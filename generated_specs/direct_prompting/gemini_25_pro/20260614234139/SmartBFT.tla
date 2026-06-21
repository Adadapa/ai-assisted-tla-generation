```tla
---- MODULE SmartBFT ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Nodes,      \* The set of replicas, e.g., 0..3
    Requests,   \* The set of possible client requests, e.g., {"r1", "r2"}
    F,          \* The maximum number of Byzantine faults
    MaxSeq,     \* The maximum sequence number to model
    MaxView,    \* The maximum view number to model
    NULL        \* A sentinel for empty proposals

ASSUME F \in Nat /\ F > 0
ASSUME Cardinality(Nodes) = 3*F + 1
ASSUME IsFiniteSet(Requests) /\ Requests /= {}

QuorumSize == 2*F + 1
N == Cardinality(Nodes)

VARIABLES
    view,       \* [i \in Nodes |-> current view number]
    phase,      \* [i \in Nodes |-> [s \in 0..MaxSeq |-> phase]]
    proposal,   \* [i \in Nodes |-> [s \in 0..MaxSeq |-> proposal]]
    log,        \* [i \in Nodes |-> sequence of decided values]
    vcStatus,   \* [i \in Nodes |-> "normal", "vc_sent", "vd_sent"]
    network     \* The set of messages in transit

vars == <<view, phase, proposal, log, vcStatus, network>>

TypeOK ==
    /\ view \in [Nodes -> 0..MaxView]
    /\ phase \in [Nodes -> [0..MaxSeq -> {"idle", "pre-prepared", "prepared", "committed"}]]
    /\ proposal \in [Nodes -> [0..MaxSeq -> Requests \cup {NULL}]]
    /\ log \in [Nodes -> Seq({[seq |-> s, val |-> r] : s \in 0..MaxSeq, r \in Requests \cup {NULL}})]
    /\ vcStatus \in [Nodes -> {"normal", "vc_sent", "vd_sent"}]
    /\ network \subseteq
        UNION {
            [type |-> {"PREPREPARE"}, view |-> 0..MaxView, seq |-> 0..MaxSeq, req |-> Requests, sender |-> Nodes],
            [type |-> {"PREPARE"}, view |-> 0..MaxView, seq |-> 0..MaxSeq, req |-> Requests, sender |-> Nodes],
            [type |-> {"COMMIT"}, view |-> 0..MaxView, seq |-> 0..MaxSeq, req |-> Requests, sender |-> Nodes],
            [type |-> {"VIEWCHANGE"}, view |-> 1..MaxView, sender |-> Nodes],
            [type |-> {"VIEWDATA"}, view |-> 1..MaxView, sender |-> Nodes,
                prepared |-> SUBSET({[seq |-> s, val |-> r] : s \in 0..MaxSeq, r \in Requests \cup {NULL}}),
                target |-> Nodes],
            [type |-> {"NEWVIEW"}, view |-> 1..MaxView, sender |-> Nodes]
        }

Init ==
    /\ view = [i \in Nodes |-> 0]
    /\ phase = [i \in Nodes |-> [s \in 0..MaxSeq |-> "idle"]]
    /\ proposal = [i \in Nodes |-> [s \in 0..MaxSeq |-> NULL]]
    /\ log = [i \in Nodes |-> <<>>]
    /\ vcStatus = [i \in Nodes |-> "normal"]
    /\ network = {}

Leader(v) == v % N

(***************************************************************************)
(*                             Normal Case Actions                         *)
(***************************************************************************)

Preprepare(s, req) ==
    \E l \in Nodes:
        /\ l = Leader(view[l])
        /\ vcStatus[l] = "normal"
        /\ s \in 0..MaxSeq
        /\ proposal[l][s] = NULL
        /\ req \in Requests
        /\ phase' = [phase EXCEPT ![l][s] = "pre-prepared"]
        /\ proposal' = [proposal EXCEPT ![l][s] = req]
        /\ network' = network \cup { [ type |-> "PREPREPARE", view |-> view[l], seq |-> s, req |-> req, sender |-> l ] }
        /\ UNCHANGED <<view, log, vcStatus>>

Prepare(i, msg) ==
    /\ msg \in network
    /\ msg.type = "PREPREPARE"
    /\ i \in Nodes
    /\ i /= msg.sender
    /\ msg.view = view[i]
    /\ msg.sender = Leader(view[i])
    /\ phase[i][msg.seq] = "idle"
    /\ vcStatus[i] = "normal"
    /\ phase' = [phase EXCEPT ![i][msg.seq] = "pre-prepared"]
    /\ proposal' = [proposal EXCEPT ![i][msg.seq] = msg.req]
    /\ network' = network \cup { [ type |-> "PREPARE", view |-> msg.view, seq |-> msg.seq, req |-> msg.req, sender |-> i ] }
    /\ UNCHANGED <<view, log, vcStatus>>

Commit(i, s) ==
    /\ i \in Nodes
    /\ s \in 0..MaxSeq
    /\ phase[i][s] = "pre-prepared"
    /\ LET p_req == proposal[i][s]
           p_view == view[i]
           prepare_proof == {m.sender | m \in network :
                                m.type = "PREPARE" /\ m.view = p_view /\ m.seq = s /\ m.req = p_req} \cup {i}
    /\ Cardinality(prepare_proof) >= QuorumSize
    /\ phase' = [phase EXCEPT ![i][s] = "prepared"]
    /\ network' = network \cup { [ type |-> "COMMIT", view |-> p_view, seq |-> s, req |-> p_req, sender |-> i ] }
    /\ UNCHANGED <<view, proposal, log, vcStatus>>

Decide(i, s) ==
    /\ i \in Nodes
    /\ s \in 0..MaxSeq
    /\ phase[i][s] = "prepared"
    /\ \A decided \in log[i] : s /= decided.seq
    /\ LET c_req == proposal[i][s]
           c_view == view[i]
           commit_proof == {m.sender | m \in network :
                                m.type = "COMMIT" /\ m.view = c_view /\ m.seq = s /\ m.req = c_req} \cup {i}
    /\ Cardinality(commit_proof) >= QuorumSize
    /\ phase' = [phase EXCEPT ![i][s] = "committed"]
    /\ log' = [log EXCEPT ![i] = Append(@, [seq |-> s, val |-> c_req])]
    /\ UNCHANGED <<view, proposal, network, vcStatus>>

(***************************************************************************)
(*                             View Change Actions                         *)
(***************************************************************************)

ViewChange(i) ==
    /\ i \in Nodes
    /\ vcStatus[i] = "normal"
    /\ view[i] < MaxView
    /\ LET new_view = view[i] + 1
    /\ view' = [view EXCEPT ![i] = new_view]
    /\ vcStatus' = [vcStatus EXCEPT ![i] = "vc_sent"]
    /\ network' = network \cup { [ type |-> "VIEWCHANGE", view |-> new_view, sender |-> i ] }
    /\ UNCHANGED <<phase, proposal, log>>

ViewData(i, v) ==
    /\ i \in Nodes
    /\ v \in 1..MaxView
    /\ view[i] = v
    /\ vcStatus[i] = "vc_sent"
    /\ LET vc_proof = {m.sender | m \in network : m.type = "VIEWCHANGE" /\ m.view = v} \cup {i}
    /\ Cardinality(vc_proof) >= QuorumSize
    /\ LET prepared_set = {[seq |-> s, val |-> proposal[i][s]] | s \in 0..MaxSeq :
                              phase[i][s] \in {"pre-prepared", "prepared"} /\ proposal[i][s] /= NULL}
    /\ network' = network \cup { [ type |-> "VIEWDATA", view |-> v, sender |-> i, prepared |-> prepared_set, target |-> Leader(v) ] }
    /\ vcStatus' = [vcStatus EXCEPT ![i] = "vd_sent"]
    /\ UNCHANGED <<view, phase, proposal, log>>

NewView(l, v) ==
    /\ l \in Nodes
    /\ v \in 1..MaxView
    /\ l = Leader(v)
    /\ view[l] = v
    /\ vcStatus[l] = "vd_sent"
    /\ LET vd_proof = {m | m \in network : m.type = "VIEWDATA" /\ m.view = v}
    /\ Cardinality({m.sender : m \in vd_proof}) >= QuorumSize
    /\ LET
        HighestSeq(prep_set) == IF prep_set = {} THEN -1
                                ELSE CHOOSE s \in {p.seq : p \in prep_set} :
                                         \A s2 \in {p.seq : p \in prep_set} : s >= s2
        BestPreparedSet ==
            CHOOSE p_set \in {m.prepared : m \in vd_proof} :
                \A p_set2 \in {m.prepared : m \in vd_proof} :
                    HighestSeq(p_set) >= HighestSeq(p_set2)
        NewProposals == BestPreparedSet
    /\ view' = [i \in Nodes |-> v]
    /\ vcStatus' = [i \in Nodes |-> "normal"]
    /\ phase' = [i \in Nodes |-> [s \in 0..MaxSeq |->
                    IF \E p \in NewProposals : p.seq = s
                    THEN "pre-prepared"
                    ELSE "idle"]]
    /\ proposal' = [i \in Nodes |-> [s \in 0..MaxSeq |->
                    LET val_set = {p.val | p \in NewProposals : p.seq = s}
                    IN IF val_set = {} THEN NULL ELSE CHOOSE val \in val_set : TRUE]]
    /\ UNCHANGED <<network, log>>

Next ==
    \/ (\E s \in 0..MaxSeq, req \in Requests : Preprepare(s, req))
    \/ (\E i \in Nodes, msg \in network : Prepare(i, msg))
    \/ (\E i \in Nodes, s \in 0..MaxSeq : Commit(i, s))
    \/ (\E i \in Nodes, s \in 0..MaxSeq : Decide(i, s))
    \/ (\E i \in Nodes : ViewChange(i))
    \/ (\E i \in Nodes, v \in 1..MaxView : ViewData(i, v))
    \/ (\E l \in Nodes, v \in 1..MaxView : NewView(l, v))

Spec == Init /\ [][Next]_vars /\ WF_vars

====
```

```cfg
SPECIFICATION Spec

CONSTANTS
    Nodes = 0..3
    F = 1
    Requests = { "r1", "r2" }
    MaxSeq = 1
    MaxView = 2
    NULL = "null_proposal"
```