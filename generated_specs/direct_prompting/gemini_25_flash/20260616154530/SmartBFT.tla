```tla
---- MODULE SmartBFT ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N, F, Nodes, Nil (* Nil for sentinel values *)
CONSTANT RequestContent (* Abstract content for requests *)

(* PHASES: IDLE, PREPREPARED, PREPARED, COMMITTED *)
PHASES == {"IDLE", "PREPREPARED", "PREPARED", "COMMITTED"}

(* MSG_TYPES: Preprepare, Prepare, Commit, ViewChange, ViewData, NewView, ClientRequest *)
MSG_TYPES == {"Preprepare", "Prepare", "Commit", "ViewChange", "ViewData", "NewView", "ClientRequest"}

(* RequestType is the set of abstract request identifiers *)
RequestType == RequestContent

(* ProposalType is a record structure *)
ProposalType == [view |-> Nat, seq |-> Nat, requests |-> Set(RequestType)]

VARIABLES
    current_view,          (* [node \in Nodes |-> Nat] *)
    current_sequence,      (* [node \in Nodes |-> Nat] *)
    phase,                 (* [node \in Nodes |-> [view \in Nat |-> [seq \in Nat |-> PHASES]]] *)
    prepared_proposal,     (* [node \in Nodes |-> [view \in Nat |-> [seq \in Nat |-> ProposalType \cup {Nil}]]] *)
    decided_proposals,     (* [node \in Nodes |-> Set(ProposalType)] *)
    messages,              (* Set(Record) - set of all messages in transit *)
    node_requests_in_pool, (* [node \in Nodes |-> Set(RequestType)] *)
    last_prepared_meta,    (* [node \in Nodes |-> [view_val |-> Nat, seq_val |-> Nat, prop_val |-> ProposalType \cup {Nil}]] *)
    view_change_messages,  (* [node \in Nodes |-> [view \in Nat |-> Set(Record)]] *)
    view_data_messages,    (* [node \in Nodes |-> [view \in Nat |-> Set(Record)]] *)
    leader_monitor_complained (* [node \in Nodes |-> BOOLEAN] *)

vars == <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, messages, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* Helper Definitions *)
quorum_size == 2*F + 1

IsQuorum(S) == Cardinality(S) >= quorum_size

Leader(v) == CHOOSE n \in Nodes : n = (v % Cardinality(Nodes)) + 1
IsLeader(i, v) == Leader(v) = i

(* Message types *)
PreprepareMsg(sender, receiver, view, seq, proposal, requests) ==
    [type |-> "Preprepare", sender |-> sender, receiver |-> receiver,
     view |-> view, seq |-> seq, proposal |-> proposal, requests |-> requests]

PrepareMsg(sender, receiver, view, seq, proposal) ==
    [type |-> "Prepare", sender |-> sender, receiver |-> receiver,
     view |-> view, seq |-> seq, proposal |-> proposal]

CommitMsg(sender, receiver, view, seq, proposal) ==
    [type |-> "Commit", sender |-> sender, receiver |-> receiver,
     view |-> view, seq |-> seq, proposal |-> proposal]

ViewChangeMsg(sender, receiver, view, last_prepared_v, last_prepared_s, last_prepared_p) ==
    [type |-> "ViewChange", sender |-> sender, receiver |-> receiver,
     view |-> view,
     last_prepared_view |-> last_prepared_v,
     last_prepared_seq |-> last_prepared_s,
     last_prepared_proposal |-> last_prepared_p]

ViewDataMsg(sender, receiver, view, last_prepared_v, last_prepared_s, last_prepared_p) ==
    [type |-> "ViewData", sender |-> sender, receiver |-> receiver,
     view |-> view,
     last_prepared_view |-> last_prepared_v,
     last_prepared_seq |-> last_prepared_s,
     last_prepared_proposal |-> last_prepared_p]

NewViewMsg(sender, receiver, view, new_proposal_seq, new_proposal) ==
    [type |-> "NewView", sender |-> sender, receiver |-> receiver,
     view |-> view,
     new_proposal_seq |-> new_proposal_seq,
     new_proposal |-> new_proposal]

ClientRequestMsg(sender, receiver, request) ==
    [type |-> "ClientRequest", sender |-> sender, receiver |-> receiver, request |-> request]

(* Proposal constructor *)
Proposal(v, s, reqs) == [view |-> v, seq |-> s, requests |-> reqs]

(* Helper for last_prepared_meta initialization *)
InitialLastPreparedMeta == [view_val |-> 0, seq_val |-> 0, prop_val |-> Nil]

(* Helper for view change logic: determines the highest prepared proposal from a set of ViewChange/ViewData messages *)
MaxPrepared(vc_vd_msgs) ==
    LET prepared_records == { [view_val |-> m.last_prepared_view, seq_val |-> m.last_prepared_seq, prop_val |-> m.last_prepared_proposal]
                              : m \in vc_vd_msgs : m.last_prepared_proposal /= Nil }
        max_seq_record == IF prepared_records = {}
                          THEN InitialLastPreparedMeta
                          ELSE CHOOSE r \in prepared_records :
                                 \A r2 \in prepared_records :
                                   (r.seq_val > r2.seq_val) \/ (r.seq_val = r2.seq_val /\ r.view_val >= r2.view_val)
    IN max_seq_record

(* Initial State *)
Init ==
    current_view = [n \in Nodes |-> 1]
    /\ current_sequence = [n \in Nodes |-> 1]
    /\ phase = [n \in Nodes |-> [v \in Nat |-> [s \in Nat |-> "IDLE"]]]
    /\ prepared_proposal = [n \in Nodes |-> [v \in Nat |-> [s \in Nat |-> Nil]]]
    /\ decided_proposals = [n \in Nodes |-> {}]
    /\ messages = {}
    /\ node_requests_in_pool = [n \in Nodes |-> {}]
    /\ last_prepared_meta = [n \in Nodes |-> InitialLastPreparedMeta]
    /\ view_change_messages = [n \in Nodes |-> [v \in Nat |-> {}]]
    /\ view_data_messages = [n \in Nodes |-> [v \in Nat |-> {}]]
    /\ leader_monitor_complained = [n \in Nodes |-> FALSE]

(* Core SmartBFT Actions *)

(* 1. Preprepare Phase: Leader assembles a batch of client requests into a proposal and broadcasts a Preprepare message *)
Preprepare(i, v, s, p_requests) ==
    /\ IsLeader(i, v)
    /\ current_view[i] = v
    /\ current_sequence[i] = s
    /\ phase[i][v][s] = "IDLE"
    /\ p_requests \subseteq node_requests_in_pool[i]
    /\ p_requests /= {} (* Must propose something *)
    /\ LET p == Proposal(v, s, p_requests) IN
        /\ messages' = messages \cup {PreprepareMsg(i, j, v, s, p, p_requests) : j \in Nodes \setminus {i}}
        /\ current_sequence' = [current_sequence EXCEPT ![i] = s + 1]
        /\ phase' = [phase EXCEPT ![i][v][s] = "PREPREPARED"]
        /\ prepared_proposal' = [prepared_proposal EXCEPT ![i][v][s] = p]
        /\ node_requests_in_pool' = [node_requests_in_pool EXCEPT ![i] = node_requests_in_pool[i] \setminus p_requests]
        /\ UNCHANGED <<current_view, decided_proposals, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* 2. Prepare Phase: Non-leader replica receives Preprepare, validates it, and broadcasts a Prepare message *)
Prepare(i, v, s, p) ==
    \E m \in messages :
        /\ m.type = "Preprepare"
        /\ m.receiver = i
        /\ m.view = v
        /\ m.seq = s
        /\ m.proposal = p
        /\ m.sender = Leader(v)
        /\ ~IsLeader(i, v)
        /\ current_view[i] = v
        /\ phase[i][v][s] = "IDLE"
        /\ LET new_last_prepared_meta ==
                IF v > last_prepared_meta[i].view_val \/ (v = last_prepared_meta[i].view_val /\ s > last_prepared_meta[i].seq_val)
                THEN [view_val |-> v, seq_val |-> s, prop_val |-> p]
                ELSE last_prepared_meta[i]
           IN
            /\ messages' = (messages \setminus {m}) \cup {PrepareMsg(i, j, v, s, p) : j \in Nodes \setminus {i}}
            /\ phase' = [phase EXCEPT ![i][v][s] = "PREPARED"]
            /\ prepared_proposal' = [prepared_proposal EXCEPT ![i][v][s] = p]
            /\ last_prepared_meta' = [last_prepared_meta EXCEPT ![i] = new_last_prepared_meta]
            /\ UNCHANGED <<current_view, current_sequence, decided_proposals, node_requests_in_pool, view_change_messages, view_data_messages, leader_monitor_complained>>

(* 3. Commit Phase: If a replica collects a quorum of Prepare messages, then it broadcasts a Commit message *)
Commit(i, v, s, p) ==
    /\ current_view[i] = v
    /\ phase[i][v][s] = "PREPARED"
    /\ prepared_proposal[i][v][s] = p
    /\ LET prepare_msgs_for_p == {m \in messages : m.type = "Prepare" /\ m.view = v /\ m.seq = s /\ m.proposal = p} IN
        /\ IsQuorum({m.sender : m \in prepare_msgs_for_p})
        /\ messages' = messages \cup {CommitMsg(i, j, v, s, p) : j \in Nodes \setminus {i}}
        /\ phase' = [phase EXCEPT ![i][v][s] = "COMMITTED"]
        /\ UNCHANGED <<current_view, current_sequence, prepared_proposal, decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* 4. Decision: If a replica collects a quorum of Commit messages, it delivers the decided proposal to the application *)
Decide(i, v, s, p) ==
    /\ current_view[i] = v
    /\ phase[i][v][s] = "COMMITTED"
    /\ prepared_proposal[i][v][s] = p
    /\ p \notin decided_proposals[i] (* Not already decided *)
    /\ LET commit_msgs_for_p == {m \in messages : m.type = "Commit" /\ m.view = v /\ m.seq = s /\ m.proposal = p} IN
        /\ IsQuorum({m.sender : m \in commit_msgs_for_p})
        /\ decided_proposals' = [decided_proposals EXCEPT ![i] = decided_proposals[i] \cup {p}]
        /\ node_requests_in_pool' = [node_requests_in_pool EXCEPT ![i] = node_requests_in_pool[i] \setminus p.requests]
        /\ IF current_sequence[i] = s THEN (* If this was the sequence we were expecting to decide *)
            current_sequence' = [current_sequence EXCEPT ![i] = s + 1]
           ELSE
            UNCHANGED current_sequence
        /\ UNCHANGED <<current_view, phase, prepared_proposal, messages, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* 5. ViewChange: A replica suspects the current leader and sends a ViewChange message *)
ViewChange(i, old_v) ==
    /\ current_view[i] = old_v
    /\ leader_monitor_complained[i] (* Trigger for view change *)
    /\ LET new_v == old_v + 1 IN
        /\ messages' = messages \cup {ViewChangeMsg(i, j, new_v, last_prepared_meta[i].view_val, last_prepared_meta[i].seq_val, last_prepared_meta[i].prop_val) : j \in Nodes}
        /\ current_view' = [current_view EXCEPT ![i] = new_v]
        /\ leader_monitor_complained' = [leader_monitor_complained EXCEPT ![i] = FALSE] (* Reset complaint *)
        /\ UNCHANGED <<current_sequence, phase, prepared_proposal, decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages>>

(* 6. ViewData: After collecting 2f+1 ViewChange messages, a replica sends a signed ViewData message to the next-view leader *)
ViewData(i, new_v) ==
    /\ current_view[i] = new_v
    /\ ~IsLeader(i, new_v) (* Only non-leaders send ViewData to the new leader *)
    /\ LET vc_msgs_for_new_v_stored_by_i == view_change_messages[i][new_v] IN
        /\ IsQuorum({m.sender : m \in vc_msgs_for_new_v_stored_by_i})
        /\ messages' = messages \cup {ViewDataMsg(i, Leader(new_v), new_v, last_prepared_meta[i].view_val, last_prepared_meta[i].seq_val, last_prepared_meta[i].prop_val)}
        /\ UNCHANGED <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* 7. NewView: If the new leader collects 2f+1 ViewData messages, then it broadcasts a NewView message *)
NewView(i, new_v) ==
    /\ IsLeader(i, new_v)
    /\ current_view[i] = new_v
    /\ LET vd_msgs_for_new_v_stored_by_i == view_data_messages[i][new_v] IN
        /\ IsQuorum({m.sender : m \in vd_msgs_for_new_v_stored_by_i})
        /\ LET max_prepared_info == MaxPrepared({m \in vd_msgs_for_new_v_stored_by_i : TRUE})
               new_s == max_prepared_info.seq_val + 1
               new_p == IF max_prepared_info.prop_val /= Nil
                        THEN Proposal(new_v, max_prepared_info.seq_val + 1, max_prepared_info.prop_val.requests)
                        ELSE Proposal(new_v, max_prepared_info.seq_val + 1, {})
           IN
            /\ messages' = messages \cup {NewViewMsg(i, j, new_v, new_s, new_p) : j \in Nodes \setminus {i}}
            /\ current_sequence' = [current_sequence EXCEPT ![i] = new_s]
            /\ prepared_proposal' = [prepared_proposal EXCEPT ![i][new_v][new_s] = new_p]
            /\ phase' = [phase EXCEPT ![i][new_v][new_s] = "PREPREPARED"]
            /\ UNCHANGED <<current_view, decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* Auxiliary actions for message handling and client requests *)

(* Receive a Preprepare message. Node must be in the same view. *)
ReceivePreprepare(i, m) ==
    /\ m.type = "Preprepare"
    /\ m.receiver = i
    /\ m.view = current_view[i]
    /\ messages' = messages \setminus {m}
    /\ UNCHANGED <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* Receive a Prepare message. Node must be in the same view. *)
ReceivePrepare(i, m) ==
    /\ m.type = "Prepare"
    /\ m.receiver = i
    /\ m.view = current_view[i]
    /\ messages' = messages \setminus {m}
    /\ UNCHANGED <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* Receive a Commit message. Node must be in the same view. *)
ReceiveCommit(i, m) ==
    /\ m.type = "Commit"
    /\ m.receiver = i
    /\ m.view = current_view[i]
    /\ messages' = messages \setminus {m}
    /\ UNCHANGED <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* Receive a ViewChange message. Can be for a future view. *)
ReceiveViewChange(i, m) ==
    /\ m.type = "ViewChange"
    /\ m.receiver = i
    /\ m.view >= current_view[i]
    /\ messages' = messages \setminus {m}
    /\ view_change_messages' = [view_change_messages EXCEPT ![i][m.view] = view_change_messages[i][m.view] \cup {m}]
    /\ UNCHANGED <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, node_requests_in_pool, last_prepared_meta, view_data_messages, leader_monitor_complained>>

(* Receive a ViewData message. Can be for a future view. *)
ReceiveViewData(i, m) ==
    /\ m.type = "ViewData"
    /\ m.receiver = i
    /\ m.view >= current_view[i]
    /\ messages' = messages \setminus {m}
    /\ view_data_messages' = [view_data_messages EXCEPT ![i][m.view] = view_data_messages[i][m.view] \cup {m}]
    /\ UNCHANGED <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, leader_monitor_complained>>

(* Receive a NewView message. Must be for a strictly higher view to trigger a view change. *)
ReceiveNewView(i, m) ==
    /\ m.type = "NewView"
    /\ m.receiver = i
    /\ m.view > current_view[i]
    /\ messages' = messages \setminus {m}
    /\ current_view' = [current_view EXCEPT ![i] = m.view]
    /\ current_sequence' = [current_sequence EXCEPT ![i] = m.new_proposal_seq]
    /\ phase' = [phase EXCEPT ![i][m.view][m.new_proposal_seq] = "PREPREPARED"]
    /\ prepared_proposal' = [prepared_proposal EXCEPT ![i][m.view][m.new_proposal_seq] = m.new_proposal]
    /\ UNCHANGED <<decided_proposals, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* A node complains about the leader, triggering a potential view change *)
Complain(i) ==
    /\ ~leader_monitor_complained[i]
    /\ leader_monitor_complained' = [leader_monitor_complained EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, messages, node_requests_in_pool, last_prepared_meta, view_change_messages, view_data_messages>>

(* A client submits a request to a node's request pool *)
ClientSubmitRequest(req) ==
    \E i \in Nodes :
        node_requests_in_pool' = [node_requests_in_pool EXCEPT ![i] = node_requests_in_pool[i] \cup {req}]
        /\ UNCHANGED <<current_view, current_sequence, phase, prepared_proposal, decided_proposals, messages, last_prepared_meta, view_change_messages, view_data_messages, leader_monitor_complained>>

(* No operation: allows the system to idle *)
NoOp == UNCHANGED vars

Next ==
    \/ \E i \in Nodes, v \in Nat, s \in Nat, p_reqs \in SUBSET RequestType : Preprepare(i, v, s, p_reqs)
    \/ \E i \in Nodes, v \in Nat, s \in Nat, p \in ProposalType : Prepare(i, v, s, p)
    \/ \E i \in Nodes, v \in Nat, s \in Nat, p \in ProposalType : Commit(i, v, s, p)
    \/ \E i \in Nodes, v \in Nat, s \in Nat, p \in ProposalType : Decide(i, v, s, p)
    \/ \E i \in Nodes, old_v \in Nat : ViewChange(i, old_v)
    \/ \E i \in Nodes, new_v \in Nat : ViewData(i, new_v)
    \/ \E i \in Nodes, new_v \in Nat : NewView(i, new_v)
    \/ \E i \in Nodes, m \in messages : ReceivePreprepare(i, m)
    \/ \E i \in Nodes, m \in messages : ReceivePrepare(i, m)
    \/ \E i \in Nodes, m \in messages : ReceiveCommit(i, m)
    \/ \E i \in Nodes, m \in messages : ReceiveViewChange(i, m)
    \/ \E i \in Nodes, m \in messages : ReceiveViewData(i, m)
    \/ \E i \in Nodes, m \in messages : ReceiveNewView(i, m)
    \/ \E i \in Nodes : Complain(i)
    \/ \E req \in RequestType : ClientSubmitRequest(req)
    \/ NoOp

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
```
```cfg
SPECIFICATION Spec
CONSTANTS
    N = 4
    F = 1
    Nodes = {1, 2, 3, 4}
    Nil = "NULL"
    RequestContent = {"req1", "req2", "req3"}
```