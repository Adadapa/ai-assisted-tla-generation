```tla
---- MODULE SmartBFT ----
EXTENDS TLC, Integers, Sequences, FiniteSets, Naturals

(* -- Constants -- *)
CONSTANT N, F, Nodes, Nil, MaxSeq, MaxView, MaxRequestsPerBatch

ASSUME N \in Nat /\ N >= 1
ASSUME F \in Nat /\ F >= 0
ASSUME N = 3*F + 1
ASSUME Nodes = 1..N
ASSUME Nil \notin Nodes
ASSUME MaxSeq \in Nat /\ MaxSeq >= 0
ASSUME MaxView \in Nat /\ MaxView >= 1
ASSUME MaxRequestsPerBatch \in Nat /\ MaxRequestsPerBatch >= 1

(* -- Types -- *)
Request == Nat (* Changed Request from STRING to Nat for simpler generation *)

ActualViewNumber == 1..MaxView
ActualSequenceNumber == 0..MaxSeq

ActualProposal == [
    view: ActualViewNumber,
    seq: ActualSequenceNumber,
    requests: Set(Request),
    metadata: STRING (* Opaque metadata, e.g., for view change info *)
]

ViewNumber == ActualViewNumber
SequenceNumber == ActualSequenceNumber \cup {Nil}
Proposal == ActualProposal \cup {Nil}

PhaseType == {"IDLE", "PREPREPARED", "PREPARED", "COMMITTED"}

MsgType == {"Preprepare", "Prepare", "Commit", "ViewChange", "ViewData", "NewView", "ClientRequest"}

ViewChangeInfo ==
    [ last_prepared_seq: ActualSequenceNumber \cup {Nil},
      last_prepared_proposal: ActualProposal \cup {Nil}
    ]

ViewDataInfo ==
    [ collected_vc_msgs: Set(MESSAGE), (* The ViewChange MESSAGEs collected by sender *)
      prepared_proposal: ActualProposal \cup {Nil} (* The highest prepared proposal from collected_vc_msgs *)
    ]

MESSAGE ==
    [ type: MsgType,
      sender: Nodes,
      dest: Nodes \cup {Nil}, (* Nil for broadcast *)
      view: ViewNumber,
      seq: SequenceNumber,
      proposal: Proposal,     (* For Preprepare, Commit, NewView, ViewData (highest prepared) *)
      signatures: Set(Nodes), (* For Prepare, Commit, NewView (nodes that signed) *)
      requests: Set(Request), (* For Preprepare (batch of requests) *)
      vc_info: ViewChangeInfo, (* For ViewChange messages *)
      vd_info: ViewDataInfo,   (* For ViewData messages *)
      collected_vd_proposals: Set(Proposal) (* For NewView (proposals from ViewData messages) *)
    ]

(* -- State Variables -- *)
VARIABLES
    currentView,          (* Map: Node -> ActualViewNumber. The view a node believes it is in. *)
    currentSeq,           (* Map: Node -> ActualSequenceNumber. The highest sequence number a node has processed/committed. *)
    currentDecisionsInView, (* Map: Node -> Nat. Number of decisions made in currentView. *)
    phase,                (* Map: Node -> Map: ActualSequenceNumber -> PhaseType. Phase for a (node, sequence) pair. *)
    prepared_proposal,    (* Map: Node -> Map: ActualSequenceNumber -> ActualProposal \cup {Nil}. Proposal prepared by a node for a sequence. *)
    committed_proposal,   (* Map: Node -> Map: ActualSequenceNumber -> ActualProposal \cup {Nil}. Proposal committed by a node for a sequence. *)
    messages,             (* Set of messages in transit. *)
    requests_pool,        (* Map: Node -> Set of Request. Client requests available at each node. *)
    view_change_messages, (* Map: Node -> Map: ActualViewNumber -> Set of MESSAGE. Stores collected ViewChange messages. *)
    view_data_messages,   (* Map: Node -> Map: ActualViewNumber -> Set of MESSAGE. Stores collected ViewData messages. *)
    next_request_id       (* Used to generate unique requests *)

(* -- Helper Functions and Predicates -- *)

Quorum(S) == CARDINALITY(S) >= 2*F + 1

Leader(v) == ( (v-1) % N ) + 1

IsLeader(i, v) == i = Leader(v)

IsCurrentLeader(i) == IsLeader(i, currentView[i])

(* Helper to create a message *)
MakeMsg(m_type, m_sender, m_dest, m_view, m_seq, m_proposal, m_sigs, m_reqs, m_vc_info, m_vd_info, m_collected_vd_props) ==
    [ type |-> m_type,
      sender |-> m_sender,
      dest |-> m_dest,
      view |-> m_view,
      seq |-> m_seq,
      proposal |-> m_proposal,
      signatures |-> m_sigs,
      requests |-> m_reqs,
      vc_info |-> m_vc_info,
      vd_info |-> m_vd_info,
      collected_vd_proposals |-> m_collected_vd_props
    ]

DefaultViewChangeInfo == [last_prepared_seq |-> Nil, last_prepared_proposal |-> Nil]
DefaultViewDataInfo == [collected_vc_msgs |-> {}, prepared_proposal |-> Nil]

(* -- Initial State -- *)
Init ==
    currentView = [i \in Nodes |-> 1]
    /\ currentSeq = [i \in Nodes |-> 0]
    /\ currentDecisionsInView = [i \in Nodes |-> 0]
    /\ phase = [i \in Nodes |-> [s \in ActualSequenceNumber |-> "IDLE"]]
    /\ prepared_proposal = [i \in Nodes |-> [s \in ActualSequenceNumber |-> Nil]]
    /\ committed_proposal = [i \in Nodes |-> [s \in ActualSequenceNumber |-> Nil]]
    /\ messages = {}
    /\ requests_pool = [i \in Nodes |-> {}]
    /\ view_change_messages = [i \in Nodes |-> [v \in ActualViewNumber |-> {}]]
    /\ view_data_messages = [i \in Nodes |-> [v \in ActualViewNumber |-> {}]]
    /\ next_request_id = 0

(* -- Actions -- *)

(* Helper action for receiving a message *)
Receive(i, m) ==
    m \in messages
    /\ (m.dest = i \/ m.dest = Nil) (* Message is for me or broadcast *)
    /\ messages' = messages \ {m}

(* Helper action for broadcasting a message *)
Broadcast(m_type, m_sender, m_view, m_seq, m_proposal, m_sigs, m_reqs, m_vc_info, m_vd_info, m_collected_vd_props) ==
    messages' = messages \cup {MakeMsg(m_type, m_sender, Nil, m_view, m_seq, m_proposal, m_sigs, m_reqs, m_vc_info, m_vd_info, m_collected_vd_props)}

(* Helper action for sending a message to a specific destination *)
SendTo(m_dest, m_type, m_sender, m_view, m_seq, m_proposal, m_sigs, m_reqs, m_vc_info, m_vd_info, m_collected_vd_props) ==
    messages' = messages \cup {MakeMsg(m_type, m_sender, m_dest, m_view, m_seq, m_proposal, m_sigs, m_reqs, m_vc_info, m_vd_info, m_collected_vd_props)}

(* Client submits a request to a specific node *)
SubmitClientRequest(i) ==
    LET new_req == next_request_id (* Changed from "req_" \o ToString(next_request_id) *)
    IN
        requests_pool' = [requests_pool EXCEPT ![i] = requests_pool[i] \cup {new_req}]
        /\ next_request_id' = next_request_id + 1
        /\ UNCHANGED <<currentView, currentSeq, currentDecisionsInView, phase, prepared_proposal, committed_proposal, messages, view_change_messages, view_data_messages>>

(* 1. Preprepare Phase: Leader assembles a batch of client requests into a proposal and broadcasts a Preprepare message *)
Preprepare(i) ==
    IsCurrentLeader(i)
    /\ currentView[i] < MaxView
    /\ currentSeq[i] < MaxSeq
    /\ phase[i][currentSeq[i]+1] = "IDLE"
    /\ requests_pool[i] /= {}
    /\ LET
        v == currentView[i]
        s == currentSeq[i] + 1
        batch_requests == CHOOSE S \in SUBSET requests_pool[i] : CARDINALITY(S) = Min({CARDINALITY(requests_pool[i]), MaxRequestsPerBatch})
        p == [view |-> v, seq |-> s, requests |-> batch_requests, metadata |-> ""]
    IN
        currentSeq' = [currentSeq EXCEPT ![i] = s]
        /\ phase' = [phase EXCEPT ![i][s] = "PREPREPARED"]
        /\ prepared_proposal' = [prepared_proposal EXCEPT ![i][s] = p]
        /\ requests_pool' = [requests_pool EXCEPT ![i] = requests_pool[i] \ batch_requests]
        /\ Broadcast("Preprepare", i, v, s, p, {}, batch_requests, DefaultViewChangeInfo, DefaultViewDataInfo, {})
        /\ UNCHANGED <<currentView, currentDecisionsInView, committed_proposal, view_change_messages, view_data_messages, next_request_id>>

(* 2. Prepare Phase: Non-leader replica receives the Preprepare, validates it, makes sure it is in the right view, and broadcasts a Prepare message *)
Prepare(i, m) ==
    Receive(i, m)
    /\ m.type = "Preprepare"
    /\ m.sender = Leader(m.view)
    /\ m.view = currentView[i]
    /\ m.seq = currentSeq[i] + 1
    /\ phase[i][m.seq] = "IDLE"
    /\ m.proposal.view = m.view
    /\ m.proposal.seq = m.seq
    /\ ~IsCurrentLeader(i) (* Only non-leaders send Prepare *)
    /\ currentSeq' = [currentSeq EXCEPT ![i] = m.seq]
    /\ phase' = [phase EXCEPT ![i][m.seq] = "PREPREPARED"]
    /\ prepared_proposal' = [prepared_proposal EXCEPT ![i][m.seq] = m.proposal]
    /\ Broadcast("Prepare", i, m.view, m.seq, m.proposal, {i}, {}, DefaultViewChangeInfo, DefaultViewDataInfo, {})
    /\ UNCHANGED <<currentView, currentDecisionsInView, committed_proposal, requests_pool, view_change_messages, view_data_messages, next_request_id>>

(* 3. Commit Phase: If a replica collects a quorum of Prepare messages (2f+1), then it broadcasts a Commit message *)
Commit(i, s, p) == (* Changed arguments from m_preprepare to s, p *)
    s \in ActualSequenceNumber
    /\ p \in ActualProposal
    /\ p.view = currentView[i]
    /\ p.seq = s
    /\ phase[i][s] = "PREPREPARED"
    /\ prepared_proposal[i][s] = p
    /\ LET
        prepares_for_seq == {m \in messages :
            m.type = "Prepare"
            /\ m.view = p.view
            /\ m.seq = p.seq
            /\ m.proposal = p
        }
        all_prepares_senders == {Leader(p.view)} \cup {m.sender : m \in prepares_for_seq}
    IN
        Quorum(all_prepares_senders)
        /\ phase' = [phase EXCEPT ![i][s] = "COMMITTED"]
        /\ committed_proposal' = [committed_proposal EXCEPT ![i][s] = p]
        /\ Broadcast("Commit", i, p.view, p.seq, p, {i}, {}, DefaultViewChangeInfo, DefaultViewDataInfo, {})
        /\ UNCHANGED <<currentView, currentSeq, currentDecisionsInView, requests_pool, view_change_messages, view_data_messages, next_request_id>>

(* 4. Decision: If a replica collects a quorum of Commit messages (2f+1), it delivers the decided proposal to the application *)
Decide(i, s, p) == (* Changed arguments from m_preprepare to s, p *)
    s \in ActualSequenceNumber
    /\ p \in ActualProposal
    /\ p.view = currentView[i]
    /\ p.seq = s
    /\ phase[i][s] = "COMMITTED"
    /\ committed_proposal[i][s] = p
    /\ LET
        commits_for_seq == {m \in messages :
            m.type = "Commit"
            /\ m.view = p.view
            /\ m.seq = p.seq
            /\ m.proposal = p
        }
        all_commits_senders == {m.sender : m \in commits_for_seq} (* FIX: Removed Leader(p.view) from quorum calculation *)
    IN
        Quorum(all_commits_senders)
        /\ currentDecisionsInView' = [currentDecisionsInView EXCEPT ![i] = currentDecisionsInView[i] + 1]
        /\ requests_pool' = [requests_pool EXCEPT ![i] = requests_pool[i] \ p.requests]
        (* The phase remains COMMITTED, as it's a terminal state for the sequence.
           No leader rotation based on decisions, as per exclusion. *)
        /\ UNCHANGED <<currentView, currentSeq, phase, prepared_proposal, committed_proposal, messages, view_change_messages, view_data_messages, next_request_id>>

(* 5. ViewChange: A replica suspects the current leader (heartbeat timeout or equivocation) and sends a ViewChange message to all nodes *)
ViewChange(i) ==
    currentView[i] < MaxView
    /\ LET
        old_v == currentView[i]
        new_v == old_v + 1
        last_prepared_s == currentSeq[i]
        last_prepared_p == prepared_proposal[i][last_prepared_s]
    IN
        currentView' = [currentView EXCEPT ![i] = new_v]
        /\ currentSeq' = [currentSeq EXCEPT ![i] = 0] (* Reset sequence for new view *)
        /\ currentDecisionsInView' = [currentDecisionsInView EXCEPT ![i] = 0]
        /\ phase' = [phase EXCEPT ![i] = [s \in ActualSequenceNumber |-> "IDLE"]] (* Reset all phases *)
        /\ view_change_messages' = [view_change_messages EXCEPT ![i] = [v \in ActualViewNumber |-> {}]] (* Clear collected VCs *)
        /\ view_data_messages' = [view_data_messages EXCEPT ![i] = [v \in ActualViewNumber |-> {}]] (* Clear collected VDs *)
        /\ Broadcast("ViewChange", i, old_v, Nil, Nil, {}, {}, [last_prepared_seq |-> last_prepared_s, last_prepared_proposal |-> last_prepared_p], DefaultViewDataInfo, {})
        /\ UNCHANGED <<prepared_proposal, committed_proposal, messages, requests_pool, next_request_id>>

(* 6. ViewData: After collecting 2f+1 ViewChange messages, a replica sends a signed ViewData message to the next-view leader *)
ViewData(i, m_vc) ==
    Receive(i, m_vc)
    /\ m_vc.type = "ViewChange"
    /\ m_vc.view + 1 = currentView[i] (* Only process VCs for the *next* view *)
    /\ LET
        new_v == currentView[i]
        updated_vc_state == view_change_messages[i][new_v] \cup {m_vc}
    IN
        view_change_messages' = [view_change_messages EXCEPT ![i][new_v] = updated_vc_state]
        /\ IF Quorum( {vc.sender : vc \in updated_vc_state} )
           THEN
               LET
                   (* Find the highest prepared proposal among the collected ViewChange messages *)
                   all_prepared_proposals == {vc.vc_info.last_prepared_proposal : vc \in updated_vc_state \land vc.vc_info.last_prepared_proposal /= Nil}
                   max_seq_prop == IF all_prepared_proposals = {}
                                   THEN Nil
                                   ELSE CHOOSE p_val \in all_prepared_proposals :
                                            \A p_other \in all_prepared_proposals : p_val.seq >= p_other.seq
               IN
                   SendTo(Leader(new_v), "ViewData", i, new_v, Nil, max_seq_prop, {i}, DefaultViewChangeInfo, [collected_vc_msgs |-> updated_vc_state, prepared_proposal |-> max_seq_prop], {})
                   /\ UNCHANGED <<currentView, currentSeq, currentDecisionsInView, phase, prepared_proposal, committed_proposal, requests_pool, view_data_messages, next_request_id>> (* FIX: Removed messages from UNCHANGED as SendTo modifies it *)
           ELSE
               UNCHANGED <<currentView, currentSeq, currentDecisionsInView, phase, prepared_proposal, committed_proposal, requests_pool, messages, view_data_messages, next_request_id>>

(* 7. NewView: If the new leader collects 2f+1 ViewData messages, then it broadcasts a NewView message to resume consensus *)
NewView(i, m_vd) ==
    Receive(i, m_vd)
    /\ m_vd.type = "ViewData"
    /\ m_vd.view = currentView[i]
    /\ IsCurrentLeader(i)
    /\ LET
        new_v == currentView[i]
        updated_vd_state == view_data_messages[i][new_v] \cup {m_vd}
    IN
        view_data_messages' = [view_data_messages EXCEPT ![i][new_v] = updated_vd_state]
        /\ IF Quorum( {vd.sender : vd \in updated_vd_state} )
           THEN
               LET
                   (* Determine the new proposal for the new view *)
                   all_vd_proposals == {vd.vd_info.prepared_proposal : vd \in updated_vd_state \land vd.vd_info.prepared_proposal /= Nil}
                   new_proposal_seq == IF all_vd_proposals = {} THEN 0 ELSE
                                       CHOOSE s_val \in {p_val.seq : p_val \in all_vd_proposals} :
                                            \A s_other \in {p_other.seq : p_other \in all_vd_proposals} : s_val >= s_other
                   new_proposal_content_requests == IF all_vd_proposals = {} THEN {} ELSE
                                           (CHOOSE p_val \in all_vd_proposals : p_val.seq = new_proposal_seq).requests
                   new_s == new_proposal_seq + 1
                   new_p == [view |-> new_v, seq |-> new_s, requests |-> new_proposal_content_requests, metadata |-> "NewView"]
               IN
                   currentSeq' = [currentSeq EXCEPT ![i] = new_s]
                   /\ phase' = [phase EXCEPT ![i][new_s] = "PREPREPARED"]
                   /\ prepared_proposal' = [prepared_proposal EXCEPT ![i][new_s] = new_p]
                   /\ Broadcast("NewView", i, new_v, new_s, new_p, {i}, {}, DefaultViewChangeInfo, DefaultViewDataInfo, {vd.vd_info.prepared_proposal : vd \in updated_vd_state \land vd.vd_info.prepared_proposal /= Nil})
                   /\ UNCHANGED <<currentView, currentDecisionsInView, committed_proposal, requests_pool, view_change_messages, next_request_id>> (* FIX: Removed messages from UNCHANGED as Broadcast modifies it *)
           ELSE
               UNCHANGED <<currentView, currentSeq, currentDecisionsInView, phase, prepared_proposal, committed_proposal, requests_pool, messages, view_change_messages, next_request_id>>

(* Advance a node's view if it receives a message from a higher view *)
AdvanceView(i, m) ==
    Receive(i, m)
    /\ m.view > currentView[i]
    /\ currentView' = [currentView EXCEPT ![i] = m.view]
    /\ currentSeq' = [currentSeq EXCEPT ![i] = 0] (* Reset sequence for new view *)
    /\ currentDecisionsInView' = [currentDecisionsInView EXCEPT ![i] = 0]
    /\ phase' = [phase EXCEPT ![i] = [s \in ActualSequenceNumber |-> "IDLE"]] (* Reset all phases *)
    /\ view_change_messages' = [view_change_messages EXCEPT ![i] = [v \in ActualViewNumber |-> {}]] (* Clear collected VCs *)
    /\ view_data_messages' = [view_data_messages EXCEPT ![i] = [v \in ActualViewNumber |-> {}]] (* Clear collected VDs *)
    /\ UNCHANGED <<prepared_proposal, committed_proposal, requests_pool, next_request_id>> (* FIX: Removed messages from UNCHANGED as Receive modifies it *)

(* Non-deterministic message loss *)
MessageLoss ==
    messages /= {}
    /\ messages' = CHOOSE S \in SUBSET messages : S /= messages
    /\ UNCHANGED <<currentView, currentSeq, currentDecisionsInView, phase, prepared_proposal, committed_proposal, requests_pool, view_change_messages, view_data_messages, next_request_id>>

Next ==
    \/ \E i \in Nodes : SubmitClientRequest(i)
    \/ \E i \in Nodes, m \in messages :
        (m.dest = i \/ m.dest = Nil) /\ m.view > currentView[i] /\ AdvanceView(i, m)
    \/ \E i \in Nodes : Preprepare(i)
    \/ \E i \in Nodes, m \in messages :
        (m.dest = i \/ m.dest = Nil) /\ m.type = "Preprepare" /\ m.view = currentView[i] /\ Prepare(i, m)
    \/ \E i \in Nodes, s \in ActualSequenceNumber, p \in ActualProposal : (* Changed for Commit *)
        Commit(i, s, p)
    \/ \E i \in Nodes, s \in ActualSequenceNumber, p \in ActualProposal : (* Changed for Decide *)
        Decide(i, s, p)
    \/ \E i \in Nodes : ViewChange(i)
    \/ \E i \in Nodes, m_vc \in messages :
        (m_vc.dest = i \/ m_vc.dest = Nil) /\ m_vc.type = "ViewChange" /\ m_vc.view + 1 = currentView[i] /\ ViewData(i, m_vc)
    \/ \E i \in Nodes, m_vd \in messages :
        (m_vd.dest = i \/ m_vd.dest = Nil) /\ m_vd.type = "ViewData" /\ m_vd.view = currentView[i] /\ NewView(i, m_vd)
    \/ MessageLoss

(* Fairness for liveness properties *)
Spec == Init /\ WF_vars(Next)

====
```
```cfg
SPECIFICATION Spec
CONSTANTS
    N = 4
    F = 1
    Nodes = 1..4
    Nil = "Nil"
    MaxSeq = 10
    MaxView = 5
    MaxRequestsPerBatch = 1
```