```tla
---- MODULE SmartBFT ----
EXTENDS TLC, Integers, Sequences, FiniteSets, Naturals

CONSTANT N, F, Nodes, Nil, RequestID, MaxRequestsPerBatch

ASSUME N = 3*F + 1
ASSUME Nodes = 1..N
ASSUME Nil \notin Nodes /\ Nil \notin RequestID
ASSUME Cardinality(RequestID) >= 1

QuorumSize == 2*F + 1

IsQuorum(S) == Cardinality(S) >= QuorumSize

Leader(v) == (v-1) % N + 1

ALL_NODES == CHOOSE n : n \notin Nodes

Min2(a, b) == IF a <= b THEN a ELSE b
Max2(a, b) == IF a >= b THEN a ELSE b

MinSet(S) == CHOOSE x \in S : \A y \in S : x <= y
MaxSet(S) == CHOOSE x \in S : \A y \in S : x >= y

Phase = {IDLE, PREPARED, COMMITTED}

Proposal == [view: Nat, seq: Nat, requests: SUBSET RequestID]

VCInfo == [
    lastCommittedSeq: Nat,
    lastCommittedProposal: Proposal \cup {Nil},
    preparedProposals: SUBSET [seq: Nat, proposal: Proposal]
]

VDInfo == [
    vc_sender: Nodes,
    vc_view: Nat,
    vc_info: VCInfo
]

MsgType = {"PREPREPARE", "PREPARE", "COMMIT", "VIEW_CHANGE", "VIEW_DATA", "NEW_VIEW"}

Msg == [
    type: MsgType,
    sender: Nodes,
    receiver: Nodes \cup {ALL_NODES},
    content:
        [type: "PREPREPARE", view: Nat, seq: Nat, proposal: Proposal] \cup
        [type: "PREPARE", view: Nat, seq: Nat, proposal: Proposal] \cup
        [type: "COMMIT", view: Nat, seq: Nat, proposal: Proposal] \cup
        [type: "VIEW_CHANGE", newView: Nat, vcInfo: VCInfo] \cup
        [type: "VIEW_DATA", newView: Nat, vdInfo: VDInfo] \cup
        [type: "NEW_VIEW", newView: Nat, newProposal: Proposal, viewDataQuorum: SUBSET VDInfo]
]

VARIABLES
    currentView,
    currentSequence,
    currentDecisionsInView,
    phase,
    preparedProposal,
    committedProposal,
    requests,
    messages

Init ==
    /\ currentView = [i \in Nodes |-> 1]
    /\ currentSequence = [i \in Nodes |-> 0]
    /\ currentDecisionsInView = [i \in Nodes |-> 0]
    /\ phase = [i \in Nodes |-> [v \in Nat |-> [s \in Nat |-> IDLE]]]
    /\ preparedProposal = [i \in Nodes |-> [v \in Nat |-> [s \in Nat |-> Nil]]]
    /\ committedProposal = [i \in Nodes |-> [v \in Nat |-> [s \in Nat |-> Nil]]]
    /\ requests = [i \in Nodes |-> {}]
    /\ messages = {}

Receive(i) ==
    \E m \in messages :
        /\ m.receiver = i \/ m.receiver = ALL_NODES
        /\ messages' = messages \setminus {m}
        /\ UNCHANGED <<currentView, currentSequence, currentDecisionsInView, phase,
                       preparedProposal, committedProposal, requests>>

ClientSubmitRequest(r) ==
    \E i \in Nodes :
        /\ r \in RequestID
        /\ r \notin requests[i]
        /\ requests' = [requests EXCEPT ![i] = requests[i] \cup {r}]
        /\ UNCHANGED <<currentView, currentSequence, currentDecisionsInView, phase,
                       preparedProposal, committedProposal, messages>>

Preprepare(i) ==
    /\ i = Leader(currentView[i])
    /\ phase[i][currentView[i]][currentSequence[i]+1] = IDLE
    /\ Cardinality(requests[i]) > 0
    LET
        v == currentView[i]
        s == currentSequence[i] + 1
        prop_requests == CHOOSE S \subseteq requests[i] : Cardinality(S) > 0 /\ Cardinality(S) <= MaxRequestsPerBatch
        p == [view |-> v, seq |-> s, requests |-> prop_requests]
        preprepare_msg_content == [type |-> "PREPREPARE", view |-> v, seq |-> s, proposal |-> p]
        preprepare_msg(j) == [type |-> "PREPREPARE", sender |-> i, receiver |-> j, content |-> preprepare_msg_content]
    IN
        /\ messages' = messages \cup {preprepare_msg(j) : j \in Nodes \setminus {i}}
        /\ phase' = [phase EXCEPT ![i][v][s] = PREPARED]
        /\ preparedProposal' = [preparedProposal EXCEPT ![i][v][s] = p]
        /\ currentSequence' = [currentSequence EXCEPT ![i] = s]
        /\ requests' = [requests EXCEPT ![i] = requests[i] \setminus prop_requests]
        /\ UNCHANGED <<currentView, currentDecisionsInView, committedProposal>>

Prepare(i) ==
    \E m \in messages :
        /\ m.receiver = i
        /\ m.type = "PREPREPARE"
        /\ m.content.view = currentView[i]
        /\ m.content.seq = currentSequence[i] + 1
        /\ phase[i][m.content.view][m.content.seq] = IDLE
        /\ m.content.proposal.view = m.content.view
        /\ m.content.proposal.seq = m.content.seq
        LET
            v == m.content.view
            s == m.content.seq
            p == m.content.proposal
            prepare_msg_content == [type |-> "PREPARE", view |-> v, seq |-> s, proposal |-> p]
            prepare_msg(j) == [type |-> "PREPARE", sender |-> i, receiver |-> j, content |-> prepare_msg_content]
        IN
            /\ messages' = (messages \setminus {m}) \cup {prepare_msg(j) : j \in Nodes \setminus {i}}
            /\ phase' = [phase EXCEPT ![i][v][s] = PREPARED]
            /\ preparedProposal' = [preparedProposal EXCEPT ![i][v][s] = p]
            /\ UNCHANGED <<currentView, currentSequence, currentDecisionsInView, committedProposal, requests>>

Commit(i) ==
    \E v, s, p :
        /\ phase[i][v][s] = PREPARED
        /\ preparedProposal[i][v][s] = p
        /\ v = currentView[i]
        /\ s > currentSequence[i]
        /\ LET prepare_msgs_for_p_v_s == {m_prep \in messages :
                                            m_prep.type = "PREPARE" /\ m_prep.content.view = v /\ m_prep.content.seq = s /\ m_prep.content.proposal = p}
           IN IsQuorum({m_prep.sender : m_prep \in prepare_msgs_for_p_v_s})
        LET
            commit_msg_content == [type |-> "COMMIT", view |-> v, seq |-> s, proposal |-> p]
            commit_msg(j) == [type |-> "COMMIT", sender |-> i, receiver |-> j, content |-> commit_msg_content]
        IN
            /\ messages' = messages \cup {commit_msg(j) : j \in Nodes \setminus {i}}
            /\ phase' = [phase EXCEPT ![i][v][s] = COMMITTED]
            /\ committedProposal' = [committedProposal EXCEPT ![i][v][s] = p]
            /\ UNCHANGED <<currentView, currentSequence, currentDecisionsInView, preparedProposal, requests>>

Decide(i) ==
    \E v, s, p :
        /\ phase[i][v][s] = COMMITTED
        /\ committedProposal[i][v][s] = p
        /\ v = currentView[i]
        /\ s = currentSequence[i] + 1
        /\ LET commit_msgs_for_p_v_s == {m_comm \in messages :
                                            m_comm.type = "COMMIT" /\ m_comm.content.view = v /\ m_comm.content.seq = s /\ m_comm.content.proposal = p}
           IN IsQuorum({m_comm.sender : m_comm \in commit_msgs_for_p_v_s})
        IN
            /\ currentSequence' = [currentSequence EXCEPT ![i] = s]
            /\ currentDecisionsInView' = [currentDecisionsInView EXCEPT ![i] = currentDecisionsInView[i] + 1]
            /\ requests' = [requests EXCEPT ![i] = requests[i] \setminus p.requests]
            /\ UNCHANGED <<currentView, phase, preparedProposal, committedProposal, messages>>

ViewChange(i) ==
    \E v_old \in Nat :
        /\ v_old = currentView[i]
        /\ i # Leader(v_old)
        /\ TRUE  (* A replica suspects the current leader *)
    LET
        new_view == v_old + 1
        last_committed_seq_i == currentSequence[i]
        last_committed_prop_i == committedProposal[i][v_old][last_committed_seq_i]
        prepared_props_i == { [seq |-> s, proposal |-> preparedProposal[i][v_old][s]] :
                                s \in DOMAIN phase[i][v_old],
                                phase[i][v_old][s] = PREPARED /\ preparedProposal[i][v_old][s] # Nil }
        vc_info_i == [
            lastCommittedSeq |-> last_committed_seq_i,
            lastCommittedProposal |-> last_committed_prop_i,
            preparedProposals |-> prepared_props_i
        ]
        vc_msg_content == [type |-> "VIEW_CHANGE", newView |-> new_view, vcInfo |-> vc_info_i]
        vc_msg(j) == [type |-> "VIEW_CHANGE", sender |-> i, receiver |-> j, content |-> vc_msg_content]
    IN
        /\ messages' = messages \cup {vc_msg(j) : j \in Nodes \setminus {i}}
        /\ currentView' = [currentView EXCEPT ![i] = new_view]
        /\ currentDecisionsInView' = [currentDecisionsInView EXCEPT ![i] = 0]
        /\ UNCHANGED <<currentSequence, phase, preparedProposal, committedProposal, requests>>

ViewData(i) ==
    \E m_vc \in messages :
        /\ m_vc.receiver = i
        /\ m_vc.type = "VIEW_CHANGE"
        /\ m_vc.content.newView = currentView[i]
        /\ i # Leader(m_vc.content.newView) (* Only non-leaders send ViewData to the new leader *)
        /\ LET vc_msgs_for_new_view == {m \in messages :
                                            m.type = "VIEW_CHANGE" /\ m.content.newView = m_vc.content.newView}
           IN IsQuorum({m.sender : m \in vc_msgs_for_new_view})
        LET
            new_view == m_vc.content.newView
            vd_info_i == [
                vc_sender |-> i,
                vc_view |-> new_view,
                vc_info |-> m_vc.content.vcInfo
            ]
            vd_msg_content == [type |-> "VIEW_DATA", newView |-> new_view, vdInfo |-> vd_info_i]
            vd_msg == [type |-> "VIEW_DATA", sender |-> i, receiver |-> Leader(new_view), content |-> vd_msg_content]
        IN
            /\ messages' = (messages \setminus {m_vc}) \cup {vd_msg}
            /\ UNCHANGED <<currentView, currentSequence, currentDecisionsInView, phase,
                           preparedProposal, committedProposal, requests>>

NewView(i) ==
    \E new_view \in Nat :
        /\ i = Leader(new_view)
        /\ currentView[i] = new_view
        /\ currentDecisionsInView[i] = 0
        /\ LET vd_msgs_for_new_view == {m \in messages :
                                            m.type = "VIEW_DATA" /\ m.content.newView = new_view}
           IN IsQuorum({m.sender : m \in vd_msgs_for_new_view})
        LET
            vd_quorum_contents == {m.content.vdInfo : m \in vd_msgs_for_new_view}
            committed_seqs == {vd.vc_info.lastCommittedSeq : vd \in vd_quorum_contents}
            max_committed_seq == IF committed_seqs = {} THEN 0 ELSE MaxSet(committed_seqs)
            committed_prop_at_max_seq == CHOOSE p \in Proposal \cup {Nil} :
                                            \E vd \in vd_quorum_contents :
                                                vd.vc_info.lastCommittedSeq = max_committed_seq /\ vd.vc_info.lastCommittedProposal = p
            all_prepared_entries == UNION {vd.vc_info.preparedProposals : vd \in vd_quorum_contents}
            relevant_prepared_entries == {entry \in all_prepared_entries : entry.seq > max_committed_seq}
            prepared_seqs == {entry.seq : entry \in relevant_prepared_entries}
            max_prepared_seq == IF prepared_seqs = {} THEN 0 ELSE MaxSet(prepared_seqs)
            prepared_prop_at_max_seq == IF max_prepared_seq = 0 THEN Nil ELSE
                                        CHOOSE p_val \in Proposal :
                                            \E entry \in relevant_prepared_entries :
                                                entry.seq = max_prepared_seq /\ entry.proposal = p_val

            new_proposal_for_view ==
                IF prepared_prop_at_max_seq # Nil THEN prepared_prop_at_max_seq
                ELSE IF committed_prop_at_max_seq # Nil THEN committed_prop_at_max_seq
                ELSE [view |-> new_view, seq |-> max_committed_seq + 1, requests |-> {}]

            new_view_msg_content == [type |-> "NEW_VIEW", newView |-> new_view, newProposal |-> new_proposal_for_view, viewDataQuorum |-> vd_quorum_contents]
            new_view_msg(j) == [type |-> "NEW_VIEW", sender |-> i, receiver |-> j, content |-> new_view_msg_content]
        IN
            /\ messages' = (messages \setminus vd_msgs_for_new_view) \cup {new_view_msg(j) : j \in Nodes \setminus {i}}
            /\ currentSequence' = [currentSequence EXCEPT ![i] = new_proposal_for_view.seq]
            /\ phase' = [phase EXCEPT ![i][new_view][new_proposal_for_view.seq] = PREPARED]
            /\ preparedProposal' = [preparedProposal EXCEPT ![i][new_view][new_proposal_for_view.seq] = new_proposal_for_view]
            /\ UNCHANGED <<currentView, currentDecisionsInView, committedProposal, requests>>

Next ==
    \/ \E i \in Nodes : Preprepare(i)
    \/ \E i \in Nodes : Prepare(i)
    \/ \E i \in Nodes : Commit(i)
    \/ \E i \in Nodes : Decide(i)
    \/ \E i \in Nodes : ViewChange(i)
    \/ \E i \in Nodes : ViewData(i)
    \/ \E i \in Nodes : NewView(i)
    \/ \E i \in Nodes : Receive(i)
    \/ \E r \in RequestID : ClientSubmitRequest(r)

Spec ==
    Init /\ [][Next]_vars
    /\ \A i \in Nodes : WF_vars(Preprepare(i))
    /\ \A i \in Nodes : WF_vars(Prepare(i))
    /\ \A i \in Nodes : WF_vars(Commit(i))
    /\ \A i \in Nodes : WF_vars(Decide(i))
    /\ \A i \in Nodes : WF_vars(ViewChange(i))
    /\ \A i \in Nodes : WF_vars(ViewData(i))
    /\ \A i \in Nodes : WF_vars(NewView(i))
    /\ \A i \in Nodes : WF_vars(Receive(i))
    /\ \A r \in RequestID : WF_vars(ClientSubmitRequest(r))

vars == <<currentView, currentSequence, currentDecisionsInView, phase,
          preparedProposal, committedProposal, requests, messages>>

====
```
```cfg
SPECIFICATION Spec
CONSTANTS
  N = 4
  F = 1
  Nodes = {1, 2, 3, 4}
  Nil = "NilValue"
  RequestID = {r1, r2, r3, r4, r5}
  MaxRequestsPerBatch = 2
```