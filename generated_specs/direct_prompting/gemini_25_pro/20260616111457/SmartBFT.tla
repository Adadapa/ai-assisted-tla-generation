```tla
---- MODULE SmartBFT ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS N, F, Data, NULL

ASSUME N = 3*F + 1

Nodes == 0..(N-1)
QuorumSize == 2*F + 1
MaxSeq == 1  \* A bound for model checking
Sequences == 0..MaxSeq

Phases == {"idle", "pre-prepared", "prepared", "committed"}

VARIABLES view, phase, proposal, messages

vars == <<view, phase, proposal, messages>>

Leader(v) == v % N

Init ==
    /\ view = [n \in Nodes |-> 0]
    /\ phase = [n \in Nodes |-> [s \in Sequences |-> "idle"]]
    /\ proposal = [n \in Nodes |-> [s \in Sequences |-> NULL]]
    /\ messages = {}

\* Action: The leader of the current view proposes a new value for a sequence.
Preprepare(l, s, d) ==
    /\ l = Leader(view[l])
    /\ s \in Sequences
    /\ phase[l][s] = "idle"
    /\ d \in Data
    /\ messages' = messages \cup
        {[type |-> "pp", view |-> view[l], seq |-> s, val |-> d, sender |-> l]}
    /\ phase' = [phase EXCEPT ![l][s] = "pre-prepared"]
    /\ proposal' = [proposal EXCEPT ![l][s] = d]
    /\ UNCHANGED <<view>>

\* Action: A replica receives a valid Preprepare message and broadcasts a Prepare.
Prepare(i, m) ==
    /\ i \in Nodes
    /\ m \in messages
    /\ m.type = "pp"
    /\ m.sender = Leader(m.view)
    /\ view[i] = m.view
    /\ phase[i][m.seq] = "idle"
    /\ messages' = messages \cup
        {[type |-> "p", view |-> m.view, seq |-> m.seq, val |-> m.val, sender |-> i]}
    /\ phase' = [phase EXCEPT ![i][m.seq] = "pre-prepared"]
    /\ proposal' = [proposal EXCEPT ![i][m.seq] = m.val]
    /\ UNCHANGED <<view>>

\* Action: A replica has received a quorum of Prepare messages and broadcasts a Commit.
Commit(i, s) ==
    /\ i \in Nodes
    /\ s \in Sequences
    /\ phase[i][s] = "pre-prepared"
    /\ proposal[i][s] /= NULL
    /\ LET v == view[i]
           prepares == {msg \in messages : msg.type = "p" /\ msg.view = v /\ msg.seq = s /\ msg.val = proposal[i][s]}
       IN Cardinality({msg.sender : msg \in prepares} \cup {i}) >= QuorumSize
    /\ messages' = messages \cup
        {[type |-> "c", view |-> view[i], seq |-> s, val |-> proposal[i][s], sender |-> i]}
    /\ phase' = [phase EXCEPT ![i][s] = "prepared"]
    /\ UNCHANGED <<view, proposal>>

\* Action: A replica has received a quorum of Commit messages and decides on the value.
Decide(i, s) ==
    /\ i \in Nodes
    /\ s \in Sequences
    /\ phase[i][s] = "prepared"
    /\ proposal[i][s] /= NULL
    /\ LET v == view[i]
           commits == {msg \in messages : msg.type = "c" /\ msg.view = v /\ msg.seq = s /\ msg.val = proposal[i][s]}
       IN Cardinality({msg.sender : msg \in commits} \cup {i}) >= QuorumSize
    /\ phase' = [phase EXCEPT ![i][s] = "committed"]
    /\ UNCHANGED <<view, proposal, messages>>

\* Action: A replica suspects the leader and initiates a view change.
ViewChange(i) ==
    /\ i \in Nodes
    /\ LET new_v == view[i] + 1
       IN /\ messages' = messages \cup {[type |-> "vc", view |-> new_v, sender |-> i]}
          /\ view' = [view EXCEPT ![i] = new_v]
          /\ UNCHANGED <<phase, proposal>>

\* Action: A replica has a quorum of ViewChange messages and sends its state to the new leader.
ViewData(i) ==
    /\ i \in Nodes
    /\ LET v == view[i]
           vcs == {msg \in messages : msg.type = "vc" /\ msg.view = v}
           pSet == {<<s, proposal[i][s]>> : s \in Sequences | phase[i][s] \in {"prepared", "committed"}}
       IN /\ Cardinality({msg.sender : msg \in vcs}) >= QuorumSize
          /\ messages' = messages \cup {[type |-> "vd", view |-> v, pSet |-> pSet, sender |-> i]}
    /\ UNCHANGED <<view, phase, proposal>>

\* Helper to determine the re-proposal for a NewView.
\* It finds the prepared proposal with the highest sequence number.
HighestPrepared(vds) ==
  LET AllPreparedPairs == UNION {m.pSet : m \in vds}
  IN IF AllPreparedPairs = {} THEN
       [seq |-> -1, val |-> NULL]
     ELSE
       LET PreparedSeqs == {p[1] : p \in AllPreparedPairs}
       IN LET MaxS == CHOOSE s \in PreparedSeqs : \A s_prime \in PreparedSeqs : s >= s_prime
       IN LET ValForMaxS == CHOOSE v \in {p[2] : p \in AllPreparedPairs | p[1] = MaxS} : TRUE
       IN [seq |-> MaxS, val |-> ValForMaxS]

\* Action: A node sends or processes a NewView message.
NewView(p, v) ==
    \* Case 1: p is the leader of v and sends the NewView message
    \/ /\ p = Leader(v)
       /\ view[p] = v
       /\ LET vds == {msg \in messages : msg.type = "vd" /\ msg.view = v}
             re_proposal == HighestPrepared(vds)
          IN /\ Cardinality({msg.sender : msg \in vds}) >= QuorumSize
             /\ messages' = messages \cup {[type |-> "nv", view |-> v, seq |-> re_proposal.seq, val |-> re_proposal.val, sender |-> p]}
             /\ UNCHANGED <<view, phase, proposal>>
    \* Case 2: p is a replica processing a NewView message for v
    \/ /\ \E m \in {msg \in messages : msg.type = "nv" /\ msg.view = v} :
            /\ view[p] < v
            /\ m.sender = Leader(v)
            /\ view' = [view EXCEPT ![p] = v]
            /\ phase' = IF m.val = NULL THEN phase
                                       ELSE [phase EXCEPT ![p][m.seq] = "pre-prepared"]
            /\ proposal' = IF m.val = NULL THEN proposal
                                          ELSE [proposal EXCEPT ![p][m.seq] = m.val]
            /\ UNCHANGED <<messages>>

Next ==
    \/ \E l \in Nodes, s \in Sequences, d \in Data : Preprepare(l, s, d)
    \/ \E i \in Nodes, m \in messages : Prepare(i, m)
    \/ \E i \in Nodes, s \in Sequences : Commit(i, s)
    \/ \E i \in Nodes, s \in Sequences : Decide(i, s)
    \/ \E i \in Nodes : ViewChange(i)
    \/ \E i \in Nodes : ViewData(i)
    \/ \E p \in Nodes, v \in 0..(MaxSeq + N) : NewView(p, v) \* Bound view for TLC

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
```

```cfg
SPECIFICATION Spec

CONSTANTS
    N = 4
    F = 1
    Data = { "d1", "d2" }
    NULL = "null_val"
```