```tla
---- MODULE SmartBFT ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* -- Constants -- *)
CONSTANT Nodes, N, F,
         IDLE, PREPARED, COMMITTED,
         PREPREPARE_TYPE, PREPARE_TYPE, COMMIT_TYPE,
         VIEW_CHANGE_TYPE, VIEW_DATA_TYPE, NEW_VIEW_TYPE

(* Null values for map initialization and sentinels *)
CONSTANT NULL_PROPOSAL, NULL_REQUEST, NULL_HASH, NULL_METADATA,
         NULL_PREPREPARE_MSG, NULL_PREPARE_MSG, NULL_COMMIT_MSG,
         NULL_VIEW_CHANGE_MSG, NULL_VIEW_DATA_MSG, NULL_NEW_VIEW_MSG

(* -- Variables -- *)
VARIABLES
    current_view,          (* Global current view number *)
    replica_state,         (* Map: Node -> ReplicaState *)
    messages               (* Set of messages in transit *)

(* -- Type Definitions -- *)
(* ReplicaState is a record for each replica's local state *)
ReplicaState == [
    view                  : Nat,
    next_proposal_sequence: Nat, (* Next sequence to propose/expect *)
    phase                 : [Nat -> {IDLE, PREPARED, COMMITTED}],
    prepared_proposals    : [Nat -> Proposal], (* Proposal prepared for a sequence *)
    last_decided_sequence : Int, (* Using Int to allow -1 for initial state *)
    pending_requests      : SUBSET Request, (* Requests waiting to be batched/proposed *)
    view_change_sent      : BOOLEAN,
    view_data_sent        : BOOLEAN,
    view_change_msgs_rcvd : [Nat -> [Nodes -> ViewChangeMsg]],
    view_data_msgs_rcvd   : [Nat -> [Nodes -> ViewDataMsg]],
    preprepare_msgs_rcvd  : [Nat -> [Nat -> [Nodes -> PreprepareMsg]]],
    prepare_msgs_rcvd     : [Nat -> [Nat -> [Nodes -> PrepareMsg]]],
    commit_msgs_rcvd      : [Nat -> [Nat -> [Nodes -> CommitMsg]]]
]

(* Message types *)
Message == PreprepareMsg \/ PrepareMsg \/ CommitMsg \/ ViewChangeMsg \/ ViewDataMsg \/ NewViewMsg

Proposal == [
    metadata : Metadata,
    requests : SUBSET Request,
    hash     : Hash
]

Metadata == [
    view_id        : Nat,
    latest_sequence: Int, (* Using Int to allow -1 for initial state *)
    decisions_in_view: Nat,
    blacklist      : SUBSET Nodes
]

Request == STRING (* Abstract client request *)
Hash == STRING (* Abstract hash *)

PreprepareMsg == [
    type     : {PREPREPARE_TYPE},
    view     : Nat,
    seq      : Nat,
    proposal : Proposal,
    sender   : Nodes
]

PrepareMsg == [
    type          : {PREPARE_TYPE},
    view          : Nat,
    seq           : Nat,
    proposal_hash : Hash,
    sender        : Nodes
]

CommitMsg == [
    type          : {COMMIT_TYPE},
    view          : Nat,
    seq           : Nat,
    proposal_hash : Hash,
    sender        : Nodes
]

ViewChangeMsg == [
    type              : {VIEW_CHANGE_TYPE},
    view              : Nat,
    sender            : Nodes,
    last_prepared_seq : Int, (* Using Int to allow -1 *)
    prepared_proposals: [Nat -> Proposal] (* Map of seq -> proposal for prepared sequences *)
]

ViewDataMsg == [
    type              : {VIEW_DATA_TYPE},
    view              : Nat,
    sender            : Nodes,
    last_prepared_seq : Int, (* Using Int to allow -1 *)
    prepared_proposals: [Nat -> Proposal] (* Map of seq -> proposal for prepared sequences *)
]

NewViewMsg == [
    type            : {NEW_VIEW_TYPE},
    view            : Nat,
    sender          : Nodes,
    new_proposal_seq: Nat,
    new_proposal    : Proposal
]

(* -- Helper Functions -- *)

QuorumSize == 2*F + 1

(* GetLeader assumes Nodes is a sequence of node IDs, 0-indexed *)
GetLeader(v) == Nodes[(v % N)]

GetProposalHash(p) == p.hash (* Abstract hash function *)
GetProposalMetadata(p) == p.metadata (* Abstract metadata extraction *)

(* Max on an empty set returns -1 *)
Max(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S : \A y \in S : y <= x

(* -- Null Message Definitions (for map initialization) -- *)
NULL_METADATA == [view_id |-> 0, latest_sequence |-> -1, decisions_in_view |-> 0, blacklist |-> {}]
NULL_PROPOSAL == [metadata |-> NULL_METADATA, requests |-> {}, hash |-> NULL_HASH]

NULL_PREPREPARE_MSG == [type |-> PREPREPARE_TYPE, view |-> 0, seq |-> 0, proposal |-> NULL_PROPOSAL, sender |-> Head(Nodes)]
NULL_PREPARE_MSG    == [type |-> PREPARE_TYPE, view |-> 0, seq |-> 0, proposal_hash |-> NULL_HASH, sender |-> Head(Nodes)]
NULL_COMMIT_MSG     == [type |-> COMMIT_TYPE, view |-> 0, seq |-> 0, proposal_hash |-> NULL_HASH, sender |-> Head(Nodes)]
NULL_VIEW_CHANGE_MSG == [type |-> VIEW_CHANGE_TYPE, view |-> 0, sender |-> Head(Nodes), last_prepared_seq |-> -1, prepared_proposals |-> [s \in Nat |-> NULL_PROPOSAL]]
NULL_VIEW_DATA_MSG   == [type |-> VIEW_DATA_TYPE, view |-> 0, sender |-> Head(Nodes), last_prepared_seq |-> -1, prepared_proposals |-> [s \in Nat |-> NULL_PROPOSAL]]
NULL_NEW_VIEW_MSG    == [type |-> NEW_VIEW_TYPE, view |-> 0, sender |-> Head(Nodes), new_proposal_seq |-> 0, new_proposal |-> NULL_PROPOSAL]

(* -- Initial State -- *)
Init ==
    /\ current_view = 0
    /\ replica_state = [r \in Nodes |->
                            [view                  |-> 0,
                             next_proposal_sequence|-> 0,
                             phase                 |-> [s \in Nat |-> IDLE],
                             prepared_proposals    |-> [s \in Nat |-> NULL_PROPOSAL],
                             last_decided_sequence |-> -1,
                             pending_requests      |-> {},
                             view_change_sent      |-> FALSE,
                             view_data_sent        |-> FALSE,
                             view_change_msgs_rcvd |-> [v \in Nat |-> [n \in Nodes |-> NULL_VIEW_CHANGE_MSG]],
                             view_data_msgs_rcvd   |-> [v \in Nat |-> [n \in Nodes |-> NULL_VIEW_DATA_MSG]],
                             preprepare_msgs_rcvd  |-> [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_PREPREPARE_MSG]]],
                             prepare_msgs_rcvd     |-> [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_PREPARE_MSG]]],
                             commit_msgs_rcvd      |-> [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_COMMIT_MSG]]]
                            ]
                       ]
    /\ messages = {}

(* -- Actions -- *)

(* Helper for validating messages: replica ignores messages from views older than its current view *)
ValidMessage(r, msg) ==
    msg.view >= replica_state[r].view

(* Helper for checking if a proposal is valid for a sequence *)
ValidProposal(r, proposal, view, seq) ==
    /\ proposal.metadata.view_id = view
    /\ proposal.metadata.latest_sequence = seq - 1
    (* proposal.metadata.decisions_in_view is related to leader rotation, which is excluded. *)
    /\ GetProposalHash(proposal) /= NULL_HASH
    /\ replica_state[r].last_decided_sequence < seq

(* 1. Preprepare Phase: Leader assembles a batch of client requests into a proposal and broadcasts a Preprepare message *)
Preprepare(leader, proposal_seq, proposal) ==
    /\ GetLeader(replica_state[leader].view) = leader
    /\ replica_state[leader].view = current_view
    /\ replica_state[leader].next_proposal_sequence = proposal_seq
    /\ replica_state[leader].phase[proposal_seq] = IDLE
    /\ ValidProposal(leader, proposal, current_view, proposal_seq)
    /\ replica_state[leader].pending_requests /= {} (* Leader has requests to propose *)

    /\ replica_state' = [replica_state EXCEPT ![leader] = [replica_state[leader] EXCEPT
                                    !next_proposal_sequence = proposal_seq + 1,
                                    !phase[proposal_seq] = PREPARED,
                                    !prepared_proposals[proposal_seq] = proposal,
                                    !pending_requests = replica_state[leader].pending_requests \ proposal.requests
                                ]]
    /\ messages' = messages \cup { [to |-> r, msg |-> [type |-> PREPREPARE_TYPE,
                                                     view |-> current_view,
                                                     seq |-> proposal_seq,
                                                     proposal |-> proposal,
                                                     sender |-> leader]] : r \in Nodes \ {leader} }
    /\ current_view' = current_view

(* 2. Prepare Phase: Non-leader replica receives Preprepare, validates it, and broadcasts a Prepare message *)
Prepare(r, preprepare_msg) ==
    /\ r \in Nodes \ {preprepare_msg.sender}
    /\ ValidMessage(r, preprepare_msg)
    /\ preprepare_msg.view = replica_state[r].view
    /\ preprepare_msg.seq = replica_state[r].next_proposal_sequence
    /\ replica_state[r].phase[preprepare_msg.seq] = IDLE
    /\ ValidProposal(r, preprepare_msg.proposal, preprepare_msg.view, preprepare_msg.seq)
    /\ GetLeader(preprepare_msg.view) = preprepare_msg.sender
    /\ replica_state[r].preprepare_msgs_rcvd[preprepare_msg.view][preprepare_msg.seq][preprepare_msg.sender] = preprepare_msg (* Preprepare message must have been received *)

    /\ replica_state' = [replica_state EXCEPT ![r] = [replica_state[r] EXCEPT
                                    !next_proposal_sequence = preprepare_msg.seq + 1,
                                    !phase[preprepare_msg.seq] = PREPARED,
                                    !prepared_proposals[preprepare_msg.seq] = preprepare_msg.proposal
                                ]]
    /\ messages' = messages \cup { [to |-> n, msg |-> [type |-> PREPARE_TYPE,
                                                      view |-> preprepare_msg.view,
                                                      seq |-> preprepare_msg.seq,
                                                      proposal_hash |-> GetProposalHash(preprepare_msg.proposal),
                                                      sender |-> r]] : n \in Nodes \ {r} }
    /\ current_view' = current_view

(* 3. Commit Phase: If a replica collects a quorum of Prepare messages (2f+1), then it broadcasts a Commit message *)
Commit(r, seq_num, proposal_hash) ==
    /\ replica_state[r].view = current_view
    /\ replica_state[r].phase[seq_num] = PREPARED
    /\ replica_state[r].prepared_proposals[seq_num] /= NULL_PROPOSAL
    /\ GetProposalHash(replica_state[r].prepared_proposals[seq_num]) = proposal_hash

    (* Collect Prepare messages for this sequence and view *)
    /\ LET received_prepares = {sender_node \in DOMAIN replica_state[r].prepare_msgs_rcvd[current_view][seq_num] :
                                replica_state[r].prepare_msgs_rcvd[current_view][seq_num][sender_node] /= NULL_PREPARE_MSG}
        matching_prepares = {sender_node \in received_prepares :
                             replica_state[r].prepare_msgs_rcvd[current_view][seq_num][sender_node].proposal_hash = proposal_hash}
    IN Cardinality(matching_prepares \cup {r}) >= QuorumSize (* Include self if self sent a prepare *)

    /\ replica_state' = [replica_state EXCEPT ![r] = [replica_state[r] EXCEPT
                                    !phase[seq_num] = COMMITTED
                                ]]
    /\ messages' = messages \cup { [to |-> n, msg |-> [type |-> COMMIT_TYPE,
                                                      view |-> current_view,
                                                      seq |-> seq_num,
                                                      proposal_hash |-> proposal_hash,
                                                      sender |-> r]] : n \in Nodes \ {r} }
    /\ current_view' = current_view

(* 4. Decision: If a replica collects a quorum of Commit messages (2f+1), it delivers the decided proposal to the application *)
Decide(r, seq_num, proposal_hash) ==
    /\ replica_state[r].view = current_view
    /\ replica_state[r].phase[seq_num] = COMMITTED
    /\ replica_state[r].last_decided_sequence < seq_num
    /\ replica_state[r].prepared_proposals[seq_num] /= NULL_PROPOSAL
    /\ GetProposalHash(replica_state[r].prepared_proposals[seq_num]) = proposal_hash

    (* Collect Commit messages for this sequence and view *)
    /\ LET received_commits = {sender_node \in DOMAIN replica_state[r].commit_msgs_rcvd[current_view][seq_num] :
                               replica_state[r].commit_msgs_rcvd[current_view][seq_num][sender_node] /= NULL_COMMIT_MSG}
        matching_commits = {sender_node \in received_commits :
                            replica_state[r].commit_msgs_rcvd[current_view][seq_num][sender_node].proposal_hash = proposal_hash}
    IN Cardinality(matching_commits \cup {r}) >= QuorumSize (* Include self if self sent a commit *)

    /\ replica_state' = [replica_state EXCEPT ![r] = [replica_state[r] EXCEPT
                                    !last_decided_sequence = seq_num
                                ]]
    /\ UNCHANGED messages (* No messages sent/received in this action *)
    /\ current_view' = current_view

(* 5. ViewChange: A replica suspects the current leader and sends a ViewChange message to all nodes *)
ViewChange(r) ==
    /\ replica_state[r].view = current_view
    /\ ~replica_state[r].view_change_sent
    (* Trigger condition (e.g., heartbeat timeout, equivocation) is abstracted as non-deterministic choice. *)

    /\ LET next_view = current_view + 1
        prepared_proposals_to_send = [s \in Nat |->
                                        IF replica_state[r].phase[s] \in {PREPARED, COMMITTED}
                                        THEN replica_state[r].prepared_proposals[s]
                                        ELSE NULL_PROPOSAL
                                      ]
        last_prepared_seq = Max({s \in DOMAIN prepared_proposals_to_send : prepared_proposals_to_send[s] /= NULL_PROPOSAL} \cup {-1})
    IN
        /\ replica_state' = [replica_state EXCEPT ![r] = [replica_state[r] EXCEPT
                                        !view_change_sent = TRUE,
                                        !view = next_view (* Replica immediately moves to the next view locally *)
                                    ]]
        /\ messages' = messages \cup { [to |-> n, msg |-> [type |-> VIEW_CHANGE_TYPE,
                                                         view |-> current_view + 1, (* ViewChange is for the *next* view *)
                                                         sender |-> r,
                                                         last_prepared_seq |-> last_prepared_seq,
                                                         prepared_proposals |-> prepared_proposals_to_send
                                                        ]] : n \in Nodes \ {r} }
        /\ current_view' = current_view (* Global view only changes after NewView *)

(* 6. ViewData: After collecting 2f+1 ViewChange messages, a replica sends a signed ViewData message to the next-view leader *)
ViewData(r, new_view_num) ==
    /\ replica_state[r].view = new_view_num (* Replica must be in the new view *)
    /\ ~replica_state[r].view_data_sent
    /\ new_view_num = current_view + 1 (* ViewData is for the next view *)

    (* Collect ViewChange messages for this new_view_num *)
    /\ LET received_view_changes = {sender_node \in DOMAIN replica_state[r].view_change_msgs_rcvd[new_view_num] :
                                    replica_state[r].view_change_msgs_rcvd[new_view_num][sender_node] /= NULL_VIEW_CHANGE_MSG}
        matching_view_changes = {sender_node \in received_view_changes :
                                 replica_state[r].view_change_msgs_rcvd[new_view_num][sender_node].view = new_view_num}
    IN Cardinality(matching_view_changes) >= QuorumSize

    /\ LET prepared_proposals_to_send = [s \in Nat |->
                                            IF replica_state[r].phase[s] \in {PREPARED, COMMITTED}
                                            THEN replica_state[r].prepared_proposals[s]
                                            ELSE NULL_PROPOSAL
                                          ]
        last_prepared_seq = Max({s \in DOMAIN prepared_proposals_to_send : prepared_proposals_to_send[s] /= NULL_PROPOSAL} \cup {-1})
    IN
        /\ replica_state' = [replica_state EXCEPT ![r] = [replica_state[r] EXCEPT
                                        !view_data_sent = TRUE
                                    ]]
        /\ messages' = messages \cup { [to |-> GetLeader(new_view_num), msg |-> [type |-> VIEW_DATA_TYPE,
                                                                                view |-> new_view_num,
                                                                                sender |-> r,
                                                                                last_prepared_seq |-> last_prepared_seq,
                                                                                prepared_proposals |-> prepared_proposals_to_send
                                                                               ]] }
        /\ current_view' = current_view

(* Helper for checking if a proposal is consistent with collected ViewData messages *)
ConsistentWithViewData(new_leader, new_view_num, new_proposal_seq, new_proposal) ==
    LET collected_view_data_senders = {sender_node \in DOMAIN replica_state[new_leader].view_data_msgs_rcvd[new_view_num] :
                                replica_state[new_leader].view_data_msgs_rcvd[new_view_num][sender_node] /= NULL_VIEW_DATA_MSG}
        view_data_quorum_msgs = {replica_state[new_leader].view_data_msgs_rcvd[new_view_num][sender_node] : sender_node \in collected_view_data_senders}
        
        (* Find the highest prepared sequence among the quorum *)
        max_prepared_seq_in_quorum = Max({m.last_prepared_seq : m \in view_data_quorum_msgs})
        
    IN
        /\ Cardinality(collected_view_data_senders) >= QuorumSize
        /\ new_proposal.metadata.view_id = new_view_num
        /\ new_proposal.metadata.blacklist = {} (* Simplified, blacklist handling is excluded *)
        /\ new_proposal.hash /= NULL_HASH (* Must be a valid proposal, not a null one *)
        /\ new_proposal_seq = max_prepared_seq_in_quorum + 1
        /\ new_proposal.metadata.latest_sequence = max_prepared_seq_in_quorum
        (* The new_proposal itself is a fresh proposal, not necessarily one from the previous view.
           Its metadata is what links it to the previous state. *)

(* 7. NewView: If the new leader collects 2f+1 ViewData messages, then it broadcasts a NewView message to resume consensus *)
NewView(new_leader, new_view_num, new_proposal_seq, new_proposal) ==
    /\ GetLeader(new_view_num) = new_leader
    /\ replica_state[new_leader].view = new_view_num
    /\ new_view_num = current_view + 1 (* NewView is for the next view *)
    /\ ConsistentWithViewData(new_leader, new_view_num, new_proposal_seq, new_proposal)

    (* Update global view and leader's state *)
    /\ current_view' = new_view_num
    /\ replica_state' = [replica_state EXCEPT ![new_leader] = [replica_state[new_leader] EXCEPT
                                !next_proposal_sequence = new_proposal_seq,
                                !phase = [s \in Nat |-> IDLE], (* Reset phases for new view *)
                                !prepared_proposals = [s \in Nat |-> NULL_PROPOSAL],
                                !view_change_sent = FALSE,
                                !view_data_sent = FALSE,
                                !view_change_msgs_rcvd = [v \in Nat |-> [n \in Nodes |-> NULL_VIEW_CHANGE_MSG]],
                                !view_data_msgs_rcvd = [v \in Nat |-> [n \in Nodes |-> NULL_VIEW_DATA_MSG]],
                                !preprepare_msgs_rcvd = [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_PREPREPARE_MSG]]],
                                !prepare_msgs_rcvd = [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_PREPARE_MSG]]],
                                !commit_msgs_rcvd = [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_COMMIT_MSG]]]
                               ]]
    /\ messages' = messages \cup { [to |-> n, msg |-> [type |-> NEW_VIEW_TYPE,
                                                     view |-> new_view_num,
                                                     sender |-> new_leader,
                                                     new_proposal_seq |-> new_proposal_seq,
                                                     new_proposal |-> new_proposal
                                                    ]] : n \in Nodes \ {new_leader} }

(* -- Message Processing Actions (Internal) -- *)

(* Replica r receives a message from the network *)
Receive(r, msg) ==
    /\ [to |-> r, msg |-> msg] \in messages
    /\ messages' = messages \ { [to |-> r, msg |-> msg] }
    /\ current_view' = current_view
    /\ replica_state' =
        [replica_state EXCEPT ![r] =
            CASE msg.type = PREPREPARE_TYPE ->
                [replica_state[r] EXCEPT !preprepare_msgs_rcvd[msg.view][msg.seq][msg.sender] = msg]
            OF msg.type = PREPARE_TYPE ->
                [replica_state[r] EXCEPT !prepare_msgs_rcvd[msg.view][msg.seq][msg.sender] = msg]
            OF msg.type = COMMIT_TYPE ->
                [replica_state[r] EXCEPT !commit_msgs_rcvd[msg.view][msg.seq][msg.sender] = msg]
            OF msg.type = VIEW_CHANGE_TYPE ->
                [replica_state[r] EXCEPT !view_change_msgs_rcvd[msg.view][msg.sender] = msg]
            OF msg.type = VIEW_DATA_TYPE ->
                [replica_state[r] EXCEPT !view_data_msgs_rcvd[msg.view][msg.sender] = msg]
            OF msg.type = NEW_VIEW_TYPE ->
                (* When a replica receives a NewView message, it updates its local view and resets state *)
                IF msg.view > replica_state[r].view
                THEN [replica_state[r] EXCEPT
                        !view = msg.view,
                        !next_proposal_sequence = msg.new_proposal_seq,
                        !phase = [s \in Nat |-> IDLE],
                        !prepared_proposals = [s \in Nat |-> NULL_PROPOSAL],
                        !view_change_sent = FALSE,
                        !view_data_sent = FALSE,
                        !view_change_msgs_rcvd = [v \in Nat |-> [n \in Nodes |-> NULL_VIEW_CHANGE_MSG]],
                        !view_data_msgs_rcvd = [v \in Nat |-> [n \in Nodes |-> NULL_VIEW_DATA_MSG]],
                        !preprepare_msgs_rcvd = [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_PREPREPARE_MSG]]],
                        !prepare_msgs_rcvd = [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_PREPARE_MSG]]],
                        !commit_msgs_rcvd = [v \in Nat |-> [s \in Nat |-> [n \in Nodes |-> NULL_COMMIT_MSG]]]
                      ]
                ELSE replica_state[r]
            OF OTHER -> replica_state[r] (* Ignore unknown message types *)
        ]

(* Client submits a request to a replica *)
ClientSubmitRequest(r, req) ==
    /\ req \notin replica_state[r].pending_requests
    /\ replica_state' = [replica_state EXCEPT ![r].pending_requests = replica_state[r].pending_requests \cup {req}]
    /\ UNCHANGED current_view
    /\ UNCHANGED messages

(* -- Next State -- *)
Next ==
    \/ \E leader, proposal_seq, proposal : Preprepare(leader, proposal_seq, proposal)
    \/ \E r, preprepare_msg :
        /\ preprepare_msg.type = PREPREPARE_TYPE
        /\ Prepare(r, preprepare_msg)
    \/ \E r, seq_num, proposal_hash : Commit(r, seq_num, proposal_hash)
    \/ \E r, seq_num, proposal_hash : Decide(r, seq_num, proposal_hash)
    \/ \E r : ViewChange(r)
    \/ \E r, new_view_num : ViewData(r, new_view_num)
    \/ \E new_leader, new_view_num, new_proposal_seq, new_proposal : NewView(new_leader, new_view_num, new_proposal_seq, new_proposal)
    \/ \E r, msg : Receive(r, msg)
    \/ \E r, req : ClientSubmitRequest(r, req)

Spec == Init /\ [][Next]_vars
    (* Fairness assumptions for liveness *)
    /\ WF_vars(Next)

vars == <<current_view, replica_state, messages>>

====
```
```cfg
SPECIFICATION Spec
CONSTANTS
    N = 4
    F = 1
    Nodes = <<0, 1, 2, 3>>
    IDLE = "IDLE"
    PREPARED = "PREPARED"
    COMMITTED = "COMMITTED"
    PREPREPARE_TYPE = "PREPREPARE"
    PREPARE_TYPE = "PREPARE"
    COMMIT_TYPE = "COMMIT"
    VIEW_CHANGE_TYPE = "VIEW_CHANGE"
    VIEW_DATA_TYPE = "VIEW_DATA"
    NEW_VIEW_TYPE = "NEW_VIEW"
    NULL_REQUEST = "NULL_REQUEST"
    NULL_HASH = "NULL_HASH"
```