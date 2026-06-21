```tla
---- MODULE SmartBFT ----
EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, TLC

(* -- Constants -- *)
CONSTANT Nodes, N, F, QuorumSize
CONSTANT IDLE, PREPARED, COMMITTED
CONSTANT INITIAL_VIEW, INITIAL_SEQUENCE
CONSTANT NULL_PROPOSAL_CONTENT, NULL_VIEW_METADATA
CONSTANT RequestInfoSet (* Set of all possible request infos *)
CONSTANT PreprepareMsg, PrepareMsg, CommitMsg, ViewChangeMsg, ViewDataMsg, NewViewMsg (* Added message types *)

(* -- Variables -- *)
VARIABLES
    current_view,          (* [Node -> Nat] *)
    current_sequence,      (* [Node -> Nat] *)
    phase,                 (* [Node -> [Nat -> {IDLE, PREPARED, COMMITTED}]] *)
    proposals,             (* [Nat -> [Nat -> ProposalContent]] (view -> sequence -> proposal content) *)
    requests_in_proposal,  (* [Nat -> [Nat -> SUBSET RequestInfo]] (view -> sequence -> set of request info) *)
    messages,              (* SUBSET Message *)
    decided_proposals,     (* SUBSET [view: Nat, seq: Nat, content: ProposalContent] *)
    decided_requests,      (* SUBSET RequestInfo *)
    received_prepares,     (* [Node -> [Nat -> [Nat -> [Node -> ProposalContent]]]] (replica -> view -> seq -> sender -> proposal_content) *)
    received_commits,      (* [Node -> [Nat -> [Nat -> [Node -> ProposalContent]]]] (replica -> view -> seq -> sender -> proposal_content) *)
    received_view_changes, (* [Node -> [Nat -> [Node -> BOOLEAN]]] (replica -> view -> sender -> TRUE) *)
    received_view_data,    (* [Node -> [Nat -> [Node -> ViewMetadata]]] (replica -> view -> sender -> metadata) *)
    suspected_leader,      (* [Node -> BOOLEAN] *)
    leader_token_held,     (* [Node -> BOOLEAN] *)
    decisions_in_view      (* [Node -> Nat] *)

(* -- Type Definitions -- *)
Node == Nodes
RequestInfo == RequestInfoSet
ProposalContent == SUBSET RequestInfo
Hash == ProposalContent (* Using ProposalContent itself as its hash for simplicity *)

ViewMetadata == [
    latest_sequence: Nat,
    view_id: Nat,
    decisions_in_view: Nat
]

Message == [
    type: {PreprepareMsg, PrepareMsg, CommitMsg, ViewChangeMsg, ViewDataMsg, NewViewMsg},
    sender: Node,
    receiver: Node,
    view: Nat,
    seq: Nat,
    proposal_hash: Hash,
    proposal_content: ProposalContent,
    metadata: ViewMetadata
]

(* -- Helper Operators -- *)

(* Leader for a given view. Assumes Nodes are 1-indexed. *)
GetLeader(v) == (v % N) + 1

IsLeader(n, v) == n = GetLeader(v)

(* Quorum check *)
IsQuorum(S) == Cardinality(S) >= QuorumSize

(* Initial values for mappings *)
InitialPhase == [v \in Nat |-> IDLE]
InitialProposals == [v \in Nat |-> NULL_PROPOSAL_CONTENT]
InitialRequestsInProposal == [v \in Nat |-> {}]
InitialReceivedPrepares == [v \in Nat |-> [s \in Nat |-> [s' \in Nodes |-> NULL_PROPOSAL_CONTENT]]]
InitialReceivedCommits == [v \in Nat |-> [s \in Nat |-> [s' \in Nodes |-> NULL_PROPOSAL_CONTENT]]]
InitialReceivedViewChanges == [v \in Nat |-> [s' \in Nodes |-> FALSE]]
InitialReceivedViewData == [v \in Nat |-> [s' \in Nodes |-> NULL_VIEW_METADATA]]

(* -- Init State -- *)
Init ==
    /\ N = Cardinality(Nodes)
    /\ F = (N - 1) \div 3
    /\ QuorumSize = 2*F + 1
    /\ current_view = [n \in Nodes |-> INITIAL_VIEW]
    /\ current_sequence = [n \in Nodes |-> INITIAL_SEQUENCE]
    /\ phase = [n \in Nodes |-> InitialPhase]
    /\ proposals = [v \in Nat |-> InitialProposals]
    /\ requests_in_proposal = [v \in Nat |-> InitialRequestsInProposal]
    /\ messages = {}
    /\ decided_proposals = {}
    /\ decided_requests = {}
    /\ received_prepares = [n \in Nodes |-> InitialReceivedPrepares]
    /\ received_commits = [n \in Nodes |-> InitialReceivedCommits]
    /\ received_view_changes = [n \in Nodes |-> InitialReceivedViewChanges]
    /\ received_view_data = [n \in Nodes |-> InitialReceivedViewData]
    /\ suspected_leader = [n \in Nodes |-> FALSE]
    /\ leader_token_held = [n \in Nodes |-> FALSE]
    /\ decisions_in_view = [n \in Nodes |-> 0]
    /\ NULL_PROPOSAL_CONTENT = CHOOSE p : p \notin ProposalContent
    /\ NULL_VIEW_METADATA = [latest_sequence |-> 0, view_id |-> 0, decisions_in_view |-> 0]
    /\ RequestInfoSet = {1, 2, 3, 4, 5} (* Example set of request infos *)

(* -- Message Sending/Receiving -- *)
SendMessage(msg) ==
    messages' = messages \cup {msg}

ReceiveMessage(msg) ==
    messages' = messages \ {msg}

(* -- Actions -- *)

(* 1. Preprepare Phase *)
Preprepare(leader, new_proposal_content, new_requests_info) ==
    /\ IsLeader(leader, current_view[leader])
    /\ leader_token_held[leader]
    /\ new_proposal_content \in ProposalContent
    /\ new_requests_info \subseteq RequestInfoSet
    /\ new_proposal_content /= NULL_PROPOSAL_CONTENT
    /\ LET
        new_seq == current_sequence[leader] + 1
        preprepare_msg(n) == [
            type |-> PreprepareMsg,
            sender |-> leader,
            receiver |-> n,
            view |-> current_view[leader],
            seq |-> new_seq,
            proposal_hash |-> new_proposal_content, (* Using content as hash *)
            proposal_content |-> new_proposal_content,
            metadata |-> NULL_VIEW_METADATA
        ]
    IN
        /\ current_sequence' = [current_sequence EXCEPT ![leader] = new_seq]
        /\ proposals' = [proposals EXCEPT
            ![current_view[leader]][new_seq] = new_proposal_content
        ]
        /\ requests_in_proposal' = [requests_in_proposal EXCEPT
            ![current_view[leader]][new_seq] = new_requests_info
        ]
        /\ phase' = [phase EXCEPT
            ![leader][new_seq] = PREPARED
        ]
        /\ messages' = messages \cup {preprepare_msg(n) : n \in Nodes \ {leader}}
        /\ leader_token_held' = [leader_token_held EXCEPT ![leader] = FALSE]
        /\ UNCHANGED <<current_view, decided_proposals, decided_requests,
                       received_prepares, received_commits, received_view_changes,
                       received_view_data, suspected_leader, decisions_in_view>>

(* 2. Prepare Phase *)
Prepare(replica, msg) ==
    /\ msg \in messages
    /\ msg.type = PreprepareMsg
    /\ msg.receiver = replica
    /\ msg.sender = GetLeader(msg.view)
    /\ msg.view = current_view[replica]
    /\ msg.seq = current_sequence[replica] + 1
    /\ phase[replica][msg.seq] = IDLE
    /\ proposals[msg.view][msg.seq] = NULL_PROPOSAL_CONTENT (* Ensure no other proposal for this seq *)
    /\ LET
        prepare_msg(n) == [
            type |-> PrepareMsg,
            sender |-> replica,
            receiver |-> n,
            view |-> msg.view,
            seq |-> msg.seq,
            proposal_hash |-> msg.proposal_content, (* Using content as hash *)
            proposal_content |-> msg.proposal_content,
            metadata |-> NULL_VIEW_METADATA
        ]
    IN
        /\ current_sequence' = [current_sequence EXCEPT ![replica] = msg.seq]
        /\ phase' = [phase EXCEPT ![replica][msg.seq] = PREPARED]
        /\ proposals' = [proposals EXCEPT ![msg.view][msg.seq] = msg.proposal_content]
        /\ requests_in_proposal' = [requests_in_proposal EXCEPT ![msg.view][msg.seq] = msg.proposal_content] (* Assuming proposal_content is the requests *)
        /\ messages' = (messages \ {msg}) \cup {prepare_msg(n) : n \in Nodes \ {replica}}
        /\ received_prepares' = [received_prepares EXCEPT
            ![replica][msg.view][msg.seq][replica] = msg.proposal_content
        ]
        /\ UNCHANGED <<current_view, decided_proposals, decided_requests,
                       received_commits, received_view_changes, received_view_data,
                       suspected_leader, leader_token_held, decisions_in_view>>

(* 3. Commit Phase *)
Commit(replica, msg) ==
    /\ msg \in messages
    /\ msg.type = PrepareMsg
    /\ msg.receiver = replica
    /\ msg.view = current_view[replica]
    /\ msg.seq = current_sequence[replica]
    /\ phase[replica][msg.seq] = PREPARED
    /\ received_prepares' = [received_prepares EXCEPT
        ![replica][msg.view][msg.seq][msg.sender] = msg.proposal_content
    ]
    /\ LET
        (* Collect prepares for the same proposal content *)
        matching_prepares == {s \in Nodes : received_prepares'[replica][msg.view][msg.seq][s] = msg.proposal_content}
        commit_msg(n) == [
            type |-> CommitMsg,
            sender |-> replica,
            receiver |-> n,
            view |-> msg.view,
            seq |-> msg.seq,
            proposal_hash |-> msg.proposal_content, (* Using content as hash *)
            proposal_content |-> msg.proposal_content,
            metadata |-> NULL_VIEW_METADATA
        ]
    IN
        /\ IsQuorum(matching_prepares)
        /\ phase' = [phase EXCEPT ![replica][msg.seq] = COMMITTED]
        /\ messages' = (messages \ {msg}) \cup {commit_msg(n) : n \in Nodes \ {replica}}
        /\ UNCHANGED <<current_view, current_sequence, proposals, requests_in_proposal,
                       decided_proposals, decided_requests, received_commits,
                       received_view_changes, received_view_data, suspected_leader,
                       leader_token_held, decisions_in_view>>

(* 4. Decision *)
Decide(replica, msg) ==
    /\ msg \in messages
    /\ msg.type = CommitMsg
    /\ msg.receiver = replica
    /\ msg.view = current_view[replica]
    /\ msg.seq = current_sequence[replica]
    /\ phase[replica][msg.seq] = COMMITTED
    /\ received_commits' = [received_commits EXCEPT
        ![replica][msg.view][msg.seq][msg.sender] = msg.proposal_content
    ]
    /\ LET
        (* Collect commits for the same proposal content *)
        matching_commits == {s \in Nodes : received_commits'[replica][msg.view][msg.seq][s] = msg.proposal_content}
        decided_prop == [
            view |-> msg.view,
            seq |-> msg.seq,
            content |-> proposals[msg.view][msg.seq]
        ]
        decided_reqs == requests_in_proposal[msg.view][msg.seq]
    IN
        /\ IsQuorum(matching_commits)
        /\ decided_proposals' = decided_proposals \cup {decided_prop}
        /\ decided_requests' = decided_requests \cup decided_reqs
        /\ decisions_in_view' = [decisions_in_view EXCEPT ![replica] = decisions_in_view[replica] + 1]
        /\ messages' = messages \ {msg}
        /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                       received_prepares, received_commits, received_view_changes,
                       received_view_data, suspected_leader, leader_token_held>>

(* 5. ViewChange *)
ViewChange(replica) ==
    /\ suspected_leader[replica]
    /\ LET
        new_view_num == current_view[replica] + 1
        view_change_msg(n) == [
            type |-> ViewChangeMsg,
            sender |-> replica,
            receiver |-> n,
            view |-> new_view_num,
            seq |-> 0, (* Not applicable for ViewChange *)
            proposal_hash |-> NULL_PROPOSAL_CONTENT,
            proposal_content |-> NULL_PROPOSAL_CONTENT,
            metadata |-> NULL_VIEW_METADATA
        ]
    IN
        /\ current_view' = [current_view EXCEPT ![replica] = new_view_num]
        /\ current_sequence' = [current_sequence EXCEPT ![replica] = INITIAL_SEQUENCE]
        /\ phase' = [phase EXCEPT ![replica] = InitialPhase] (* Reset all phases for this replica *)
        /\ decisions_in_view' = [decisions_in_view EXCEPT ![replica] = 0]
        /\ suspected_leader' = [suspected_leader EXCEPT ![replica] = FALSE]
        /\ leader_token_held' = [leader_token_held EXCEPT ![replica] = FALSE] (* Relinquish token *)
        /\ messages' = messages \cup {view_change_msg(n) : n \in Nodes \ {replica}}
        /\ received_view_changes' = [received_view_changes EXCEPT ![replica] = InitialReceivedViewChanges] (* Clear pending view changes for this replica *)
        /\ received_view_data' = [received_view_data EXCEPT ![replica] = InitialReceivedViewData] (* Clear pending view data for this replica *)
        /\ UNCHANGED <<proposals, requests_in_proposal, decided_proposals, decided_requests,
                       received_prepares, received_commits>>

(* 6. ViewData *)
ViewData(replica, msg) ==
    /\ msg \in messages
    /\ msg.type = ViewChangeMsg
    /\ msg.receiver = replica
    /\ msg.view > current_view[replica] (* Only process for a future view *)
    /\ received_view_changes' = [received_view_changes EXCEPT
        ![replica][msg.view][msg.sender] = TRUE
    ]
    /\ LET
        (* Collect view changes for the same view *)
        view_change_senders == {s \in Nodes : received_view_changes'[replica][msg.view][s]}
        new_leader_for_view == GetLeader(msg.view)
        (* Replica's metadata to send in ViewData. Simplified. *)
        replica_metadata == [
            latest_sequence |-> current_sequence[replica],
            view_id |-> current_view[replica],
            decisions_in_view |-> 0 (* Decisions in view reset on view change *)
        ]
        view_data_msg == [
            type |-> ViewDataMsg,
            sender |-> replica,
            receiver |-> new_leader_for_view,
            view |-> msg.view,
            seq |-> 0,
            proposal_hash |-> NULL_PROPOSAL_CONTENT,
            proposal_content |-> NULL_PROPOSAL_CONTENT,
            metadata |-> replica_metadata
        ]
    IN
        /\ IsQuorum(view_change_senders)
        /\ current_view' = [current_view EXCEPT ![replica] = msg.view] (* Advance replica's view *)
        /\ messages' = (messages \ {msg}) \cup {view_data_msg}
        /\ UNCHANGED <<current_sequence, phase, proposals, requests_in_proposal,
                       decided_proposals, decided_requests, received_prepares,
                       received_commits, received_view_data, suspected_leader,
                       leader_token_held, decisions_in_view>>

(* 7. NewView *)
NewView(new_leader, msg) ==
    /\ msg \in messages
    /\ msg.type = ViewDataMsg
    /\ msg.receiver = new_leader
    /\ IsLeader(new_leader, msg.view)
    /\ msg.view = current_view[new_leader]
    /\ received_view_data' = [received_view_data EXCEPT
        ![new_leader][msg.view][msg.sender] = msg.metadata
    ]
    /\ LET
        (* Collect view data for the same view *)
        view_data_senders == {s \in Nodes : received_view_data'[new_leader][msg.view][s] /= NULL_VIEW_METADATA}
        (* Determine new proposal sequence from collected metadata *)
        all_metadata == {received_view_data'[new_leader][msg.view][s] : s \in view_data_senders}
        max_seq_from_metadata == Max({m.latest_sequence : m \in all_metadata})
        new_proposal_sequence == max_seq_from_metadata + 1
        new_view_msg(n) == [
            type |-> NewViewMsg,
            sender |-> new_leader,
            receiver |-> n,
            view |-> msg.view,
            seq |-> new_proposal_sequence,
            proposal_hash |-> NULL_PROPOSAL_CONTENT,
            proposal_content |-> NULL_PROPOSAL_CONTENT,
            metadata |-> [
                latest_sequence |-> new_proposal_sequence,
                view_id |-> msg.view,
                decisions_in_view |-> 0 (* Decisions in view reset on new view *)
            ]
        ]
    IN
        /\ IsQuorum(view_data_senders)
        /\ current_sequence' = [current_sequence EXCEPT ![new_leader] = new_proposal_sequence]
        /\ decisions_in_view' = [decisions_in_view EXCEPT ![new_leader] = 0] (* SmartBFT resets decisions in view to 0 on new view *)
        /\ phase' = [phase EXCEPT ![new_leader] = InitialPhase] (* Reset all phases for new leader *)
        /\ leader_token_held' = [leader_token_held EXCEPT ![new_leader] = TRUE] (* New leader can propose *)
        /\ messages' = (messages \ {msg}) \cup {new_view_msg(n) : n \in Nodes \ {new_leader}}
        /\ UNCHANGED <<current_view, proposals, requests_in_proposal, decided_proposals,
                       decided_requests, received_prepares, received_commits,
                       received_view_changes, suspected_leader>>

(* -- Other Actions (Non-mandatory, but necessary for completeness) -- *)

(* A replica can spontaneously suspect the leader *)
SuspectLeader(replica) ==
    /\ ~suspected_leader[replica]
    /\ suspected_leader' = [suspected_leader EXCEPT ![replica] = TRUE]
    /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                   messages, decided_proposals, decided_requests, received_prepares,
                   received_commits, received_view_changes, received_view_data,
                   leader_token_held, decisions_in_view>>

(* A replica can acquire the leader token if it's the leader and doesn't hold it *)
AcquireLeaderToken(leader) ==
    /\ IsLeader(leader, current_view[leader])
    /\ ~leader_token_held[leader]
    /\ leader_token_held' = [leader_token_held EXCEPT ![leader] = TRUE]
    /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                   messages, decided_proposals, decided_requests, received_prepares,
                   received_commits, received_view_changes, received_view_data,
                   suspected_leader, decisions_in_view>>

(* A replica processes a NewView message *)
ProcessNewView(replica, msg) ==
    /\ msg \in messages
    /\ msg.type = NewViewMsg
    /\ msg.receiver = replica
    /\ msg.view > current_view[replica]
    /\ LET
        new_view_num == msg.view
        new_proposal_seq == msg.metadata.latest_sequence
        new_decisions_in_view == msg.metadata.decisions_in_view
    IN
        /\ current_view' = [current_view EXCEPT ![replica] = new_view_num]
        /\ current_sequence' = [current_sequence EXCEPT ![replica] = new_proposal_seq]
        /\ decisions_in_view' = [decisions_in_view EXCEPT ![replica] = new_decisions_in_view]
        /\ phase' = [phase EXCEPT ![replica] = InitialPhase]
        /\ leader_token_held' = [leader_token_held EXCEPT ![replica] = IsLeader(replica, new_view_num)]
        /\ messages' = messages \ {msg}
        /\ UNCHANGED <<proposals, requests_in_proposal, decided_proposals, decided_requests,
                       received_prepares, received_commits, received_view_changes,
                       received_view_data, suspected_leader>>

(* A replica can ignore an old message *)
IgnoreOldMessage(replica, msg) ==
    /\ msg \in messages
    /\ msg.receiver = replica
    /\ msg.view < current_view[replica]
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                   decided_proposals, decided_requests, received_prepares,
                   received_commits, received_view_changes, received_view_data,
                   suspected_leader, leader_token_held, decisions_in_view>>

(* A replica can ignore a message for a future view if it's not a ViewChange/ViewData/NewView message *)
IgnoreFutureConsensusMessage(replica, msg) ==
    /\ msg \in messages
    /\ msg.receiver = replica
    /\ msg.view > current_view[replica]
    /\ msg.type \notin {ViewChangeMsg, ViewDataMsg, NewViewMsg}
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                   decided_proposals, decided_requests, received_prepares,
                   received_commits, received_view_changes, received_view_data,
                   suspected_leader, leader_token_held, decisions_in_view>>

(* A replica can ignore a Preprepare message if it's not the leader *)
IgnorePreprepareIfNotLeader(replica, msg) ==
    /\ msg \in messages
    /\ msg.type = PreprepareMsg
    /\ msg.receiver = replica
    /\ ~IsLeader(replica, msg.view)
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                   decided_proposals, decided_requests, received_prepares,
                   received_commits, received_view_changes, received_view_data,
                   suspected_leader, leader_token_held, decisions_in_view>>

(* A replica can ignore a message if it's for a sequence number it has already processed *)
IgnoreStaleSequenceMessage(replica, msg) ==
    /\ msg \in messages
    /\ msg.receiver = replica
    /\ msg.view = current_view[replica]
    /\ msg.seq <= current_sequence[replica]
    /\ msg.type \in {PreprepareMsg, PrepareMsg, CommitMsg}
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                   decided_proposals, decided_requests, received_prepares,
                   received_commits, received_view_changes, received_view_data,
                   suspected_leader, leader_token_held, decisions_in_view>>

(* A replica can ignore a message if it's not from the expected leader *)
IgnoreMessageFromWrongLeader(replica, msg) ==
    /\ msg \in messages
    /\ msg.receiver = replica
    /\ msg.view = current_view[replica]
    /\ msg.type \in {PreprepareMsg, PrepareMsg, CommitMsg}
    /\ msg.sender /= GetLeader(msg.view)
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                   decided_proposals, decided_requests, received_prepares,
                   received_commits, received_view_changes, received_view_data,
                   suspected_leader, leader_token_held, decisions_in_view>>

(* A replica can ignore a message if it's for a sequence number that is too far ahead *)
IgnoreFutureSequenceMessage(replica, msg) ==
    /\ msg \in messages
    /\ msg.receiver = replica
    /\ msg.view = current_view[replica]
    /\ msg.seq > current_sequence[replica] + 1
    /\ msg.type \in {PreprepareMsg, PrepareMsg, CommitMsg}
    /\ messages' = messages \ {msg}
    /\ UNCHANGED <<current_view, current_sequence, phase, proposals, requests_in_proposal,
                   decided_proposals, decided_requests, received_prepares,
                   received_commits, received_view_changes, received_view_data,
                   suspected_leader, leader_token_held, decisions_in_view>>

(* -- Next State -- *)
Next ==
    \/ \E leader \in Nodes, new_proposal_content \in ProposalContent, new_requests_info \subseteq RequestInfoSet :
        Preprepare(leader, new_proposal_content, new_requests_info)
    \/ \E replica \in Nodes, msg \in messages :
        Prepare(replica, msg)
    \/ \E replica \in Nodes, msg \in messages :
        Commit(replica, msg)
    \/ \E replica \in Nodes, msg \in messages :
        Decide(replica, msg)
    \/ \E replica \in Nodes :
        ViewChange(replica)
    \/ \E replica \in Nodes, msg \in messages :
        ViewData(replica, msg)
    \/ \E new_leader \in Nodes, msg \in messages :
        NewView(new_leader, msg)
    \/ \E replica \in Nodes :
        SuspectLeader(replica)
    \/ \E leader \in Nodes :
        AcquireLeaderToken(leader)
    \/ \E replica \in Nodes, msg \in messages :
        ProcessNewView(replica, msg)
    \/ \E replica \in Nodes, msg \in messages :
        IgnoreOldMessage(replica, msg)
    \/ \E replica \in Nodes, msg \in messages :
        IgnoreFutureConsensusMessage(replica, msg)
    \/ \E replica \in Nodes, msg \in messages :
        IgnorePreprepareIfNotLeader(replica, msg)
    \/ \E replica \in Nodes, msg \in messages :
        IgnoreStaleSequenceMessage(replica, msg)
    \/ \E replica \in Nodes, msg \in messages :
        IgnoreMessageFromWrongLeader(replica, msg)
    \/ \E replica \in Nodes, msg \in messages :
        IgnoreFutureSequenceMessage(replica, msg)

(* -- Specification -- *)
Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(Preprepare(_,_,_))
    /\ WF_vars(Prepare(_,_))
    /\ WF_vars(Commit(_,_))
    /\ WF_vars(Decide(_,_))
    /\ SF_vars(ViewChange(_))
    /\ WF_vars(ViewData(_,_))
    /\ WF_vars(NewView(_,_))
    /\ WF_vars(SuspectLeader(_))
    /\ WF_vars(AcquireLeaderToken(_))
    /\ WF_vars(ProcessNewView(_,_))

vars == <<current_view, current_sequence, phase, proposals, requests_in_proposal,
           messages, decided_proposals, decided_requests, received_prepares,
           received_commits, received_view_changes, received_view_data,
           suspected_leader, leader_token_held, decisions_in_view>>

====
```
```cfg
SPECIFICATION Spec
CONSTANTS
    Nodes = {1, 2, 3, 4}
    N = 4
    F = 1
    QuorumSize = 3
    IDLE = "IDLE"
    PREPARED = "PREPARED"
    COMMITTED = "COMMITTED"
    INITIAL_VIEW = 0
    INITIAL_SEQUENCE = 0
    NULL_PROPOSAL_CONTENT = "NULL_PROPOSAL_CONTENT"
    NULL_VIEW_METADATA = [latest_sequence |-> 0, view_id |-> 0, decisions_in_view |-> 0]
    RequestInfoSet = {1, 2, 3, 4, 5}
    PreprepareMsg = "PreprepareMsg"
    PrepareMsg = "PrepareMsg"
    CommitMsg = "CommitMsg"
    ViewChangeMsg = "ViewChangeMsg"
    ViewDataMsg = "ViewDataMsg"
    NewViewMsg = "NewViewMsg"
```