```tla
---- MODULE SmartBFT ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Nodes,      \* The set of replicas, e.g., 0..3
    N,          \* The total number of replicas
    F,          \* The number of Byzantine replicas tolerated
    QuorumSize, \* The size of a quorum
    Requests,   \* The set of possible client requests
    NULL,       \* A special value for empty/null proposals
    MaxSeq,     \* A bound on sequence numbers for model checking
    MaxView     \* A bound on view numbers for model checking

ASSUME
    /\ N = 3 * F + 1
    /\ QuorumSize = 2 * F + 1
    /\ IsFiniteSet(Nodes)
    /\ Cardinality(Nodes) = N
    /\ NULL \notin Requests

VARIABLES
    view,            \* view[i]: current view number of node i
    phase,           \* phase[i][n]: consensus phase of node i for sequence n
    preparedValue,   \* preparedValue[i][n]: the value node i has prepared for sequence n
    decidedLog,      \* decidedLog[i]: the sequence of decided values for node i
    network          \* The set of messages in flight

vars == <<view, phase, preparedValue, decidedLog, network>>

\* Helper to determine the leader for a given view.
Leader(v) == v % N

\* Initial state of the system.
Init ==
    /\ view = [i \in Nodes |-> 0]
    /\ phase = [i \in Nodes |-> [n \in 0..MaxSeq |-> "IDLE"]]
    /\ preparedValue = [i \in Nodes |-> [n \in 0..MaxSeq |-> NULL]]
    /\ decidedLog = [i \in Nodes |-> <<>>]
    /\ network = {}

\* Message constructors for clarity
PreprepareMsg(v, n, r, s) == [type |-> "Preprepare", view |-> v, seq |-> n, req |-> r, sender |-> s]
PrepareMsg(v, n, r, s) == [type |-> "Prepare", view |-> v, seq |-> n, req |-> r, sender |-> s]
CommitMsg(v, n, r, s) == [type |-> "Commit", view |-> v, seq |-> n, req |-> r, sender |-> s]
ViewChangeMsg(v, s) == [type |-> "ViewChange", view |-> v, sender |-> s]
ViewDataMsg(v, p, s) == [type |-> "ViewData", view |-> v, prepared |-> p, sender |-> s]
NewViewMsg(v, p, s) == [type |-> "NewView", view |-> v, proposals |-> p, sender |-> s]

\*-----------------------------------------------------------------------------
\* Actions
\*-----------------------------------------------------------------------------

Preprepare(self, n, r) ==
    /\ self = Leader(view[self])
    /\ n \in 0..MaxSeq
    /\ r \in Requests
    /\ phase[self][n] = "IDLE"
    /\ LET v == view[self] IN
        /\ network' = network \cup {PreprepareMsg(v, n, r, self)}
        /\ phase' = [phase EXCEPT ![self][n] = "PREPREPARED"]
        /\ preparedValue' = [preparedValue EXCEPT ![self][n] = r]
    /\ UNCHANGED <<view, decidedLog>>

Prepare(self, v, n, r) ==
    /\ v >= view[self]
    /\ n \in 0..MaxSeq
    /\ r \in Requests
    /\ phase[self][n] = "IDLE"
    /\ \/ (\E l \in Nodes:
            /\ l = Leader(v)
            /\ PreprepareMsg(v, n, r, l) \in network)
       \/ (\E msg \in network:
            /\ msg.type = "NewView"
            /\ msg.view = v
            /\ msg.sender = Leader(v)
            /\ <<n, r>> \in msg.proposals)
    /\ network' = network \cup {PrepareMsg(v, n, r, self)}
    /\ view' = [view EXCEPT ![self] = v]
    /\ phase' = [phase EXCEPT ![self][n] = "PREPREPARED"]
    /\ preparedValue' = [preparedValue EXCEPT ![self][n] = r]
    /\ UNCHANGED <<decidedLog>>

Commit(self, n) ==
    /\ n \in 0..MaxSeq
    /\ phase[self][n] = "PREPREPARED"
    /\ LET v == view[self] IN
       LET r == preparedValue[self][n] IN
         /\ r # NULL
         /\ LET prepares == {m.sender : m \in network,
                                m.type = "Prepare" /\ m.view = v /\ m.seq = n /\ m.req = r} \cup {self}
         IN Cardinality(prepares) >= QuorumSize
    /\ LET v == view[self] IN
       LET r == preparedValue[self][n] IN
         /\ network' = network \cup {CommitMsg(v, n, r, self)}
         /\ phase' = [phase EXCEPT ![self][n] = "PREPARED"]
    /\ UNCHANGED <<view, preparedValue, decidedLog>>

Decide(self, n) ==
    /\ n \in 0..MaxSeq
    /\ phase[self][n] = "PREPARED"
    /\ LET v == view[self] IN
       LET r == preparedValue[self][n] IN
         /\ r # NULL
         /\ LET commits == {m.sender : m \in network,
                                m.type = "Commit" /\ m.view = v /\ m.seq = n /\ m.req = r} \cup {self}
         IN Cardinality(commits) >= QuorumSize
    /\ LET r == preparedValue[self][n] IN
        /\ phase' = [phase EXCEPT ![self][n] = "COMMITTED"]
        /\ decidedLog' = [decidedLog EXCEPT ![self] = Append(@, [seq |-> n, req |-> r])]
    /\ UNCHANGED <<view, preparedValue, network>>

ViewChange(self) ==
    /\ LET new_v == view[self] + 1 IN
        /\ new_v <= MaxView
        /\ network' = network \cup {ViewChangeMsg(new_v, self)}
        /\ view' = [view EXCEPT ![self] = new_v]
    /\ UNCHANGED <<phase, preparedValue, decidedLog>>

ViewData(self, v) ==
    /\ v > view[self]
    /\ v <= MaxView
    /\ LET vcs == {m.sender : m \in network, m.type = "ViewChange" /\ m.view = v}
    IN Cardinality(vcs) >= QuorumSize
    /\ LET prepared_set == {<<s, preparedValue[self][s]>> : s \in 0..MaxSeq, preparedValue[self][s] # NULL}
    IN network' = network \cup {ViewDataMsg(v, prepared_set, self)}
    /\ view' = [view EXCEPT ![self] = v]
    /\ UNCHANGED <<phase, preparedValue, decidedLog>>

NewView(self, v) ==
    /\ self = Leader(v)
    /\ v >= view[self]
    /\ v <= MaxView
    /\ LET vds == {m : m \in network, m.type = "ViewData" /\ m.view = v}
    IN Cardinality({m.sender : m \in vds}) >= QuorumSize
    /\ LET all_prepared = UNION {m.prepared : m \in vds}
    /\ LET new_proposals == all_prepared
    /\ network' = network \cup {NewViewMsg(v, new_proposals, self)}
    /\ view' = [view EXCEPT ![self] = v]
    /\ LET new_prepared_self = [s \in 0..MaxSeq |->
            LET val_set = {p[2] : p \in new_proposals, p[1] = s} IN
            IF val_set = {} THEN preparedValue[self][s] ELSE CHOOSE val \in val_set: TRUE]
    /\ LET new_phase_self = [s \in 0..MaxSeq |->
            IF \E p \in new_proposals: p[1] = s
            THEN "PREPREPARED"
            ELSE phase[self][s]]
    /\ preparedValue' = [preparedValue EXCEPT ![self] = new_prepared_self]
    /\ phase' = [phase EXCEPT ![self] = new_phase_self]
    /\ UNCHANGED <<decidedLog>>

\*-----------------------------------------------------------------------------
\* Next State Relation
\*-----------------------------------------------------------------------------

Next ==
    \/ \E self \in Nodes, n \in 0..MaxSeq, r \in Requests: Preprepare(self, n, r)
    \/ \E self \in Nodes, v \in 0..MaxView, n \in 0..MaxSeq, r \in Requests: Prepare(self, v, n, r)
    \/ \E self \in Nodes, n \in 0..MaxSeq: Commit(self, n)
    \/ \E self \in Nodes, n \in 0..MaxSeq: Decide(self, n)
    \/ \E self \in Nodes: ViewChange(self)
    \/ \E self \in Nodes, v \in 0..MaxView: ViewData(self, v)
    \/ \E self \in Nodes, v \in 0..MaxView: NewView(self, v)

\*-----------------------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------------------

Fairness ==
    /\ \A self \in Nodes: WF_vars(ViewChange(self))
    /\ \A self \in Nodes, v \in 0..MaxView: WF_vars(ViewData(self, v))
    /\ \A self \in Nodes, v \in 0..MaxView: WF_vars(NewView(self, v))
    /\ \A self \in Nodes, n \in 0..MaxSeq, r \in Requests: WF_vars(Preprepare(self, n, r))
    /\ \A self \in Nodes, v \in 0..MaxView, n \in 0..MaxSeq, r \in Requests: WF_vars(Prepare(self, v, n, r))
    /\ \A self \in Nodes, n \in 0..MaxSeq: WF_vars(Commit(self, n))
    /\ \A self \in Nodes, n \in 0..MaxSeq: WF_vars(Decide(self, n))

Spec == Init /\ [][Next]_vars /\ Fairness

====
```

```cfg
SPECIFICATION Spec

CONSTANTS
    N = 4
    F = 1
    Nodes = 0..3
    QuorumSize = 3
    Requests = {"r1", "r2"}
    NULL = "null"
    MaxSeq = 1
    MaxView = 2
```