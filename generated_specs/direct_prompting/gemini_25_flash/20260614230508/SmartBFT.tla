```tla
---- MODULE SmartBFT ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* -- Constants -- *)
CONSTANT Nodes, N, f, NULL_PROPOSAL, NULL_DIGEST, NULL_INFO,
         MAX_SEQ, MAX_VIEW,
         Requests

(* -- Variables -- *)
VARIABLES replica_view, replica_seq, replica_phase,
          replica_prepared_proposal, replica_committed_proposal,
          replica_last_prepared_info, replica_last_committed_info,
          msgs, proposals_by_leader, decided_proposals,
          requests_available

(* -- Definitions -- *)
Phase == {"IDLE", "PREPARED", "COMMITTED"}
MessageTypes == {"Preprepare", "Prepare", "Commit", "ViewChange", "ViewData", "NewView"}

quorumSize == 2*f + 1

(* Leader election: simplified to (view % N), assuming Nodes are 0 to N-1 *)
Leader(v) == CHOOSE n \in Nodes : n = (v % N)

IsLeader(r, v) == r = Leader(v)

IsNewerView(r, v) == v > replica_view[r]
IsCurrentView(r, v) == v = replica_view[r]
IsNextSeq(r, s) == s = replica_seq[r] + 1

IsIdle(r, v, s) == replica_phase[r][v][s] = "IDLE"
IsPrepared(r, v, s) == replica_phase[r][v][s] = "PREPARED"
IsCommitted(r, v, s) == replica_phase[r][v][s] = "COMMITTED"

(* Digest function: simplified to the proposal itself for uniqueness *)
Digest(P) == P

(* AnyValue for flexible payload types *)
AnyValue == CHOOSE v : TRUE

(* Message structure *)
Message == [
    sender: Nodes,
    receiver: Nodes,
    type: MessageTypes,
    view: Nat,
    seq: Nat,
    payload: AnyValue
]

(* Message constructors *)
PreprepareMsg(sender, receiver, v, s, proposal, digest) ==
    [sender |-> sender, receiver |-> receiver, type |-> "Preprepare", view |-> v, seq |-> s,
     payload |-> [proposal |-> proposal, digest |-> digest]]

PrepareMsg(sender, receiver, v, s, digest) ==
    [sender |-> sender, receiver |-> receiver, type |-> "Prepare", view |-> v, seq |-> s,
     payload |-> [digest |-> digest]]

CommitMsg(sender, receiver, v, s, digest) ==
    [sender |-> sender, receiver |-> receiver, type |-> "Commit", view |-> v, seq |-> s,
     payload |-> [digest |-> digest]]

ViewChangeMsg(sender, receiver, v, s, last_prepared_info, last_committed_info) ==
    [sender |-> sender, receiver |-> receiver, type |-> "ViewChange", view |-> v, seq |-> s,
     payload |-> [last_prepared_info |-> last_prepared_info, last_committed_info |-> last_committed_info]]

ViewDataMsg(sender, receiver, v, s, vc_messages) ==
    [sender |-> sender, receiver |-> receiver, type |-> "ViewData", view |-> v, seq |-> s,
     payload |-> [vc_messages |-> vc_messages]]

NewViewMsg(sender, receiver, v, s, proposal, digest, vc_messages) ==
    [sender |-> sender, receiver |-> receiver, type |-> "NewView", view |-> v, seq |-> s,
     payload |-> [proposal |-> proposal, digest |-> digest, vc_messages |-> vc_messages]]

(* Helper for message collection *)
GetMessages(msg_type, v, s, d, target_receiver) ==
    {m \in msgs :
        m.type = msg_type /\ m.view = v /\ m.seq = s /\
        m.payload.digest = d /\ m.receiver = target_receiver}

GetViewChangeMessages(v, target_receiver) ==
    {m \in msgs :
        m.type = "ViewChange" /\ m.view = v /\ m.receiver = target_receiver}

GetViewDataMessages(v, target_receiver) ==
    {m \in msgs :
        m.type = "ViewData" /\ m.view = v /\ m.receiver = target_receiver}

HasQuorum(msg_type, v, s, d, target_receiver) ==
    Cardinality({m \in GetMessages(msg_type, v, s, d, target_receiver) : TRUE}) >= quorumSize

HasViewChangeQuorum(v, target_receiver) ==
    Cardinality({m \in GetViewChangeMessages(v, target_receiver) : TRUE}) >= quorumSize

HasViewDataQuorum(v, target_receiver) ==
    Cardinality({m \in GetViewDataMessages(v, target_receiver) : TRUE}) >= quorumSize

(* Initial state *)
Init ==
    /\ replica_view = [r \in Nodes |-> 0]
    /\ replica_seq = [r \in Nodes |-> 0]
    /\ replica_phase = [r \in Nodes |-> [v \in 0..MAX_VIEW |-> [s \in 0..MAX_SEQ |-> "IDLE"]]]
    /\ replica_prepared_proposal = [r \in Nodes |-> [v \in 0..MAX_VIEW |-> [s \in 0..MAX_SEQ |-> NULL_PROPOSAL]]]
    /\ replica_committed_proposal = [r \in Nodes |-> [v \in 0..MAX_VIEW |-> [s \in 0..MAX_SEQ |-> NULL_PROPOSAL]]]
    /\ replica_last_prepared_info = [r \in Nodes |-> NULL_INFO]
    /\ replica_last_committed_info = [r \in Nodes |-> NULL_INFO]
    /\ msgs = {}
    /\ proposals_by_leader = [v \in 0..MAX_VIEW |-> [s \in 0..MAX_SEQ |-> NULL_PROPOSAL]]
    /\ decided_proposals = {}
    /\ requests_available = Requests

(* Actions *)

(* Generic message delivery *)
Deliver(r) ==
    \E m \in msgs :
        /\ m.receiver = r
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED <<replica_view, replica_seq, replica_phase,
                       replica_prepared_proposal, replica_committed_proposal,
                       replica_last_prepared_info, replica_last_committed_info,
                       proposals_by_leader, decided_proposals, requests_available>>

(* 1. Preprepare Phase *)
Preprepare(leader, v, s, P) ==
    /\ IsLeader(leader, v)
    /\ IsCurrentView(leader, v)
    /\ IsNextSeq(leader, s)
    /\ IsIdle(leader, v, s)
    /\ P \in requests_available
    /\ P /= NULL_PROPOSAL
    /\ s < MAX_SEQ
    /\ v < MAX_VIEW

    /\ replica_view' = replica_view
    /\ replica_seq' = [replica_seq EXCEPT ![leader] = s]
    /\ replica_phase' = [replica_phase EXCEPT ![leader][v][s] = "PREPARED"] (* Leader implicitly prepares its own proposal *)
    /\ replica_prepared_proposal' = [replica_prepared_proposal EXCEPT ![leader][v][s] = P]
    /\ replica_committed_proposal' = replica_committed_proposal
    /\ replica_last_prepared_info' = [replica_last_prepared_info EXCEPT ![leader] = [view |-> v, seq |-> s, digest |-> Digest(P)]]
    /\ replica_last_committed_info' = replica_last_committed_info
    /\ msgs' = msgs \cup {PreprepareMsg(leader, r, v, s, P, Digest(P)) : r \in Nodes \ {leader}}
    /\ proposals_by_leader' = [proposals_by_leader EXCEPT ![v][s] = P]
    /\ decided_proposals' = decided_proposals
    /\ requests_available' = requests_available

(* 2. Prepare Phase *)
Prepare(replica, v, s, P_digest, P) ==
    /\ replica \in Nodes \ {Leader(v)}
    /\ IsCurrentView(replica, v)
    /\ IsNextSeq(replica, s)
    /\ IsIdle(replica, v, s)
    /\ s < MAX_SEQ
    /\ v < MAX_VIEW

    /\ \E m \in msgs : (* Replica receives Preprepare message *)
        /\ m.type = "Preprepare"
        /\ m.sender = Leader(v)
        /\ m.receiver = replica
        /\ m.view = v
        /\ m.seq = s
        /\ m.payload.digest = P_digest
        /\ m.payload.proposal = P
        /\ P_digest = Digest(P)

    /\ replica_view' = replica_view
    /\ replica_seq' = [replica_seq EXCEPT ![replica] = s]
    /\ replica_phase' = [replica_phase EXCEPT ![replica][v][s] = "PREPARED"]
    /\ replica_prepared_proposal' = [replica_prepared_proposal EXCEPT ![replica][v][s] = P]
    /\ replica_committed_proposal' = replica_committed_proposal
    /\ replica_last_prepared_info' = [replica_last_prepared_info EXCEPT ![replica] = [view |-> v, seq |-> s, digest |-> P_digest]]
    /\ replica_last_committed_info' = replica_last_committed_info
    /\ msgs' = (msgs \ {m}) \cup {PrepareMsg(replica, r, v, s, P_digest) : r \in Nodes \ {replica}}
    /\ proposals_by_leader' = [proposals_by_leader EXCEPT ![v][s] = P] (* Store proposal if not already there *)
    /\ decided_proposals' = decided_proposals
    /\ requests_available' = requests_available

(* 3. Commit Phase *)
Commit(replica, v, s, P_digest) ==
    /\ replica \in Nodes
    /\ IsCurrentView(replica, v)
    /\ IsPrepared(replica, v, s)
    /\ s < MAX_SEQ
    /\ v < MAX_VIEW

    /\ HasQuorum("Prepare", v, s, P_digest, replica)
    /\ replica_prepared_proposal[replica][v][s] /= NULL_PROPOSAL
    /\ P_digest = Digest(replica_prepared_proposal[replica][v][s])

    /\ replica_view' = replica_view
    /\ replica_seq' = replica_seq
    /\ replica_phase' = [replica_phase EXCEPT ![replica][v][s] = "COMMITTED"]
    /\ replica_prepared_proposal' = replica_prepared_proposal
    /\ replica_committed_proposal' = [replica_committed_proposal EXCEPT ![replica][v][s] = replica_prepared_proposal[replica][v][s]]
    /\ replica_last_prepared_info' = replica_last_prepared_info
    /\ replica_last_committed_info' = [replica_last_committed_info EXCEPT ![replica] = [view |-> v, seq |-> s, digest |-> P_digest]]
    /\ msgs' = msgs \cup {CommitMsg(replica, r, v, s, P_digest) : r \in Nodes \ {replica}}
    /\ proposals_by_leader' = proposals_by_leader
    /\ decided_proposals' = decided_proposals
    /\ requests_available' = requests_available

(* 4. Decision *)
Decide(replica, v, s, P) ==
    /\ replica \in Nodes
    /\ IsCurrentView(replica, v)
    /\ IsCommitted(replica, v, s)
    /\ P = replica_committed_proposal[replica][v][s]
    /\ P /= NULL_PROPOSAL
    /\ [view |-> v, seq |-> s, proposal |-> P] \notin decided_proposals
    /\ s < MAX_SEQ
    /\ v < MAX_VIEW

    /\ HasQuorum("Commit", v, s, Digest(P), replica)

    /\ replica_view' = replica_view
    /\ replica_seq' = replica_seq
    /\ replica_phase' = replica_phase
    /\ replica_prepared_proposal' = replica_prepared_proposal
    /\ replica_committed_proposal' = replica_committed_proposal
    /\ replica_last_prepared_info' = replica_last_prepared_info
    /\ replica_last_committed_info' = replica_last_committed_info
    /\ msgs' = msgs
    /\ proposals_by_leader' = proposals_by_leader
    /\ decided_proposals' = decided_proposals \cup {[view |-> v, seq |-> s, proposal |-> P]}
    /\ requests_available' = requests_available \ {P} (* Abstracted: remove requests from decided proposal *)

(* 5. ViewChange *)
ViewChange(replica, old_view) ==
    /\ replica \in Nodes
    /\ IsCurrentView(replica, old_view)
    /\ old_view < MAX_VIEW

    /\ replica_view' = [replica_view EXCEPT ![replica] = old_view + 1]
    /\ replica_seq' = replica_seq (* Do not reset sequence here; it's part of last_prepared_info *)
    /\ replica_phase' = [replica_phase EXCEPT ![replica][old_view+1] = [s \in 0..MAX_SEQ |-> "IDLE"]]
    /\ replica_prepared_proposal' = replica_prepared_proposal
    /\ replica_committed_proposal' = replica_committed_proposal
    /\ replica_last_prepared_info' = replica_last_prepared_info
    /\ replica_last_committed_info' = replica_last_committed_info
    /\ msgs' = msgs \cup {ViewChangeMsg(replica, r, old_view + 1, replica_seq[replica], replica_last_prepared_info[replica], replica_last_committed_info[replica]) : r \in Nodes \ {replica}}
    /\ proposals_by_leader' = proposals_by_leader
    /\ decided_proposals' = decided_proposals
    /\ requests_available' = requests_available

(* 6. ViewData *)
ViewData(replica, new_view) ==
    /\ replica \in Nodes
    /\ IsCurrentView(replica, new_view)
    /\ new_view > 0
    /\ new_view < MAX_VIEW

    /\ HasViewChangeQuorum(new_view, replica)
    /\ LET vc_msgs == GetViewChangeMessages(new_view, replica) IN
        /\ replica_view' = replica_view
        /\ replica_seq' = replica_seq
        /\ replica_phase' = replica_phase
        /\ replica_prepared_proposal' = replica_prepared_proposal
        /\ replica_committed_proposal' = replica_committed_proposal
        /\ replica_last_prepared_info' = replica_last_prepared_info
        /\ replica_last_committed_info' = replica_last_committed_info
        /\ msgs' = msgs \cup {ViewDataMsg(replica, Leader(new_view), new_view, 0, vc_msgs)} (* seq 0 for ViewData is fine as it's not proposal-specific *)
        /\ proposals_by_leader' = proposals_by_leader
        /\ decided_proposals' = decided_proposals
        /\ requests_available' = requests_available

(* 7. NewView *)
NewView(new_leader, new_view) ==
    /\ IsLeader(new_leader, new_view)
    /\ IsCurrentView(new_leader, new_view)
    /\ new_view > 0
    /\ new_view < MAX_VIEW

    /\ HasViewDataQuorum(new_view, new_leader)
    /\ LET vd_msgs == GetViewDataMessages(new_view, new_leader)
           vc_msgs_from_vd == UNION {m.payload.vc_messages : m \in vd_msgs}
           (* Determine new_seq and P_new based on collected ViewChange messages *)
           all_prepared_infos == {vc.payload.last_prepared_info : vc \in vc_msgs_from_vd}
           (* all_prepared_infos will contain at least NULL_INFO if any VC message was sent,
              which is guaranteed if HasViewDataQuorum is true. *)
           max_seq_info == CHOOSE info \in all_prepared_infos :
                             \A other_info \in all_prepared_infos : info.seq >= other_info.seq
           new_seq == max_seq_info.seq
           P_new == IF new_seq = 0 THEN NULL_PROPOSAL ELSE proposals_by_leader[max_seq_info.view][new_seq]
           P_new_digest == Digest(P_new)
        IN
        /\ replica_view' = replica_view
        /\ replica_seq' = [replica_seq EXCEPT ![new_leader] = new_seq] (* Leader's sequence is set to the highest prepared sequence from previous view *)
        /\ replica_phase' = [replica_phase EXCEPT ![new_leader][new_view][new_seq] = "PREPARED"] (* Leader implicitly prepares P_new in the new view *)
        /\ replica_prepared_proposal' = [replica_prepared_proposal EXCEPT ![new_leader][new_view][new_seq] = P_new]
        /\ replica_committed_proposal' = replica_committed_proposal
        /\ replica_last_prepared_info' = [replica_last_prepared_info EXCEPT ![new_leader] = [view |-> new_view, seq |-> new_seq, digest |-> P_new_digest]]
        /\ replica_last_committed_info' = replica_last_committed_info
        /\ msgs' = msgs \cup {NewViewMsg(new_leader, r, new_view, new_seq, P_new, P_new_digest, vc_msgs_from_vd) : r \in Nodes \ {new_leader}}
        /\ proposals_by_leader' = [proposals_by_leader EXCEPT ![new_view][new_seq] = P_new]
        /\ decided_proposals' = decided_proposals
        /\ requests_available' = requests_available

(* CatchUp action (abstracted sync mechanism) *)
CatchUp(r) ==
    /\ r \in Nodes
    /\ \E v_dec, s_dec, P_dec :
        /\ [view |-> v_dec, seq |-> s_dec, proposal |-> P_dec] \in decided_proposals
        /\ (v_dec > replica_view[r] \/ (v_dec = replica_view[r] /\ s_dec > replica_seq[r]))
        /\ v_dec < MAX_VIEW
        /\ s_dec < MAX_SEQ

    /\ LET new_view == v_dec
           new_seq == s_dec
           new_digest == Digest(P_dec)
        IN
        /\ replica_view' = [replica_view EXCEPT ![r] = new_view]
        /\ replica_seq' = [replica_seq EXCEPT ![r] = new_seq]
        /\ replica_phase' = [replica_phase EXCEPT ![r][new_view][new_seq] = "COMMITTED"]
        /\ replica_prepared_proposal' = [replica_prepared_proposal EXCEPT ![r][new_view][new_seq] = P_dec]
        /\ replica_committed_proposal' = [replica_committed_proposal EXCEPT ![r][new_view][new_seq] = P_dec]
        /\ replica_last_prepared_info' = [replica_last_prepared_info EXCEPT ![r] = [view |-> new_view, seq |-> new_seq, digest |-> new_digest]]
        /\ replica_last_committed_info' = [replica_last_committed_info EXCEPT ![r] = [view |-> new_view, seq |-> new_seq, digest |-> new_digest]]
        /\ msgs' = msgs
        /\ proposals_by_leader' = [proposals_by_leader EXCEPT ![new_view][new_seq] = P_dec]
        /\ decided_proposals' = decided_proposals
        /\ requests_available' = requests_available \ {P_dec} (* Remove requests from decided proposal if not already removed *)

(* Top-level action operators for fairness and trace validation *)
Action_Deliver == \E r \in Nodes : Deliver(r)
Action_Preprepare == \E leader \in Nodes, v \in Nat, s \in Nat, P \in Requests : Preprepare(leader, v, s, P)
Action_Prepare == \E replica \in Nodes, v \in Nat, s \in Nat, P_digest \in STRING, P \in Requests : Prepare(replica, v, s, P_digest, P)
Action_Commit == \E replica \in Nodes, v \in Nat, s \in Nat, P_digest \in STRING : Commit(replica, v, s, P_digest)
Action_Decide == \E replica \in Nodes, v \in Nat, s \in Nat, P \in Requests : Decide(replica, v, s, P)
Action_ViewChange == \E replica \in Nodes, old_view \in Nat : ViewChange(replica, old_view)
Action_ViewData == \E replica \in Nodes, new_view \in Nat : ViewData(replica, new_view)
Action_NewView == \E new_leader \in Nodes, new_view \in Nat : NewView(new_leader, new_view)
Action_CatchUp == \E r \in Nodes : CatchUp(r)

Next ==
    Action_Deliver \/
    Action_Preprepare \/
    Action_Prepare \/
    Action_Commit \/
    Action_Decide \/
    Action_ViewChange \/
    Action_ViewData \/
    Action_NewView \/
    Action_CatchUp

vars == <<replica_view, replica_seq, replica_phase,
           replica_prepared_proposal, replica_committed_proposal,
           replica_last_prepared_info, replica_last_committed_info,
           msgs, proposals_by_leader, decided_proposals, requests_available>>

(* Specification with fairness for action operations *)
Fairness ==
    /\ WF_vars(Action_Deliver)
    /\ WF_vars(Action_Preprepare)
    /\ WF_vars(Action_Prepare)
    /\ WF_vars(Action_Commit)
    /\ WF_vars(Action_Decide)
    /\ WF_vars(Action_ViewChange)
    /\ WF_vars(Action_ViewData)
    /\ WF_vars(Action_NewView)
    /\ WF_vars(Action_CatchUp)

Spec == Init /\ [][Next]_vars /\ Fairness

====
```
```cfg
SPECIFICATION Spec
CONSTANTS
    N = 4
    f = 1
    Nodes = {0, 1, 2, 3}
    NULL_PROPOSAL = "NULL_PROPOSAL"
    NULL_DIGEST = "NULL_DIGEST"
    NULL_INFO = [view |-> 0, seq |-> 0, digest |-> "NULL_DIGEST"]
    MAX_SEQ = 2
    MAX_VIEW = 2
    Requests = {"Req1", "Req2"}
```