```tla
---- MODULE SmartBFT ----
EXTENDS FiniteSets, FiniteSetsExt, Sequences, Naturals, TLC

CONSTANTS
    Nodes,      \* The set of replicas, e.g., 1..4
    Proposals,  \* The set of potential client proposals, e.g., {101, 102}
    F,          \* The maximum number of Byzantine faulty nodes
    NULL        \* A sentinel for an empty proposal slot

ASSUME F \in Nat /\ F > 0
ASSUME Cardinality(Nodes) = 3*F + 1
ASSUME NULL \notin Proposals
ASSUME \A n \in Nodes: n \in Int
ASSUME IsFiniteSet(Proposals) /\ \A p \in Proposals: p \in Int

\*
--
\* Computed Constants
--
N == Cardinality(Nodes)
Quorum == 2*F + 1

\* A deterministic leader election function. Assumes Nodes is a set of integers.
Leader(v) ==
    LET sortedNodes == CHOOSE S \in Seqs(Nodes) : IsPermutation(S, Nodes) /\ \A i \in 1..(N-1) : S[i] < S[i+1]
    IN sortedNodes[((v-1) % N) + 1]

\*
--
\* State Variables
--
VARIABLES
    view,       \* [n \in Nodes |-> Nat]
    phase,      \* [n \in Nodes |-> [s \in Nat |-> {"idle", "pre-prepared", "prepared", "committed"}]]
    proposal,   \* [n \in Nodes |-> [s \in Nat |-> Proposals \cup {NULL}]]
    log,        \* [n \in Nodes |-> Seq(Proposals)]
    messages    \* A set of messages in the network

vars == <<view, phase, proposal, log, messages>>

\*
--
\* Message Definitions
--
\* Note: To simplify, we use the full proposal instead of a digest.
PrePrepareMsg(v, s, p, l) == [type |-> "pre-prepare", view |-> v, seq |-> s, proposal |-> p, sender |-> l]
PrepareMsg(v, s, p, r) == [type |-> "prepare", view |-> v, seq |-> s, proposal |-> p, sender |-> r]
CommitMsg(v, s, p, r) == [type |-> "commit", view |-> v, seq |-> s, proposal |-> p, sender |-> r]
ViewChangeMsg(v, r) == [type |-> "view-change", view |-> v, sender |-> r]
ViewDataMsg(v, r, pSet) == [type |-> "view-data", view |-> v, sender |-> r, pSet |-> pSet]
NewViewMsg(v, l) == [type |-> "new-view", view |-> v, sender |-> l]

\*
--
\* Initial State
--
Init ==
    /\ view = [n \in Nodes |-> 1]
    /\ phase = [n \in Nodes |-> [s \in 0..0 |-> "idle"]]
    /\ proposal = [n \in Nodes |-> [s \in 0..0 |-> NULL]]
    /\ log = [n \in Nodes |-> <<>>]
    /\ messages = {}

\*
--
\* Actions
--

\* A leader proposes a new value for a sequence number.
Preprepare(leader, s, p) ==
    /\ leader = Leader(view[leader])
    /\ \/ s \notin DOMAIN phase[leader]
       \/ phase[leader][s] = "idle"
    /\ p \in Proposals
    /\ LET v == view[leader]
           msg == PrePrepareMsg(v, s, p, leader)
       IN /\ messages' = messages \cup {msg}
          /\ phase' = [phase EXCEPT ![leader][s] = "pre-prepared"]
          /\ proposal' = [proposal EXCEPT ![leader][s] = p]
          /\ UNCHANGED <<view, log>>

\* A replica receives a valid PrePrepare and broadcasts a Prepare.
Prepare(replica, m) ==
    /\ m.type = "pre-prepare"
    /\ LET v == m.view
           s == m.seq
           p == m.proposal
           l == m.sender
       IN /\ v = view[replica]
          /\ l = Leader(v)
          /\ \/ s \notin DOMAIN phase[replica]
             \/ phase[replica][s] = "idle"
          /\ LET msg == PrepareMsg(v, s, p, replica)
             IN /\ messages' = messages \cup {msg}
                /\ phase' = [phase EXCEPT ![replica][s] = "pre-prepared"]
                /\ proposal' = [proposal EXCEPT ![replica][s] = p]
                /\ UNCHANGED <<view, log>>

\* A replica has a valid PrePrepare and a quorum of matching Prepares, so it broadcasts a Commit.
Commit(replica, s) ==
    /\ LET v == view[replica]
           p == proposal[replica][s]
       IN /\ phase[replica][s] = "pre-prepared"
          /\ p # NULL
          /\ LET PrepareVotes == {m.sender : m \in messages |
                                   /\ m.type = "prepare"
                                   /\ m.view = v
                                   /\ m.seq = s
                                   /\ m.proposal = p}
             IN Cardinality(PrepareVotes \cup {replica}) >= Quorum
          /\ LET msg == CommitMsg(v, s, p, replica)
             IN /\ messages' = messages \cup {msg}
                /\ phase' = [phase EXCEPT ![replica][s] = "prepared"]
                /\ UNCHANGED <<view, proposal, log>>

\* A replica has a quorum of Commits and decides on the proposal.
Decide(replica, s) ==
    /\ LET v == view[replica]
           p == proposal[replica][s]
       IN /\ phase[replica][s] = "prepared"
          /\ p # NULL
          /\ LET CommitVotes == {m.sender : m \in messages |
                                  /\ m.type = "commit"
                                  /\ m.view = v
                                  /\ m.seq = s
                                  /\ m.proposal = p}
             IN Cardinality(CommitVotes \cup {replica}) >= Quorum
          /\ phase' = [phase EXCEPT ![replica][s] = "committed"]
          /\ log' = [log EXCEPT ![replica] = Append(@, p)]
          /\ UNCHANGED <<view, proposal, messages>>

\* A replica suspects the leader and initiates a view change.
ViewChange(replica) ==
    /\ LET v == view[replica]
           newView == v + 1
           msg == ViewChangeMsg(newView, replica)
       IN /\ view' = [view EXCEPT ![replica] = newView]
          /\ messages' = messages \cup {msg}
          /\ UNCHANGED <<phase, proposal, log>>

\* After seeing a quorum of ViewChange messages, a replica sends its state to the new leader.
ViewData(replica, newView) ==
    /\ view[replica] = newView
    /\ LET VCVotes == {m.sender : m \in messages |
                           /\ m.type = "view-change"
                           /\ m.view = newView}
       IN Cardinality(VCVotes) >= Quorum
    /\ LET pSet == { [seq |-> s, proposal |-> proposal[replica][s]] :
                       s \in (DOMAIN phase[replica]) | phase[replica][s] \in {"pre-prepared", "prepared"} }
           msg == ViewDataMsg(newView, replica, pSet)
       IN /\ messages' = messages \cup {msg}
          /\ UNCHANGED <<view, phase, proposal, log>>

\* Helper for NewView: computes the map of proposals to be re-proposed.
NewProposalsMap(VDVotes) ==
    LET AllPSets == UNION {m.pSet : m \in VDVotes}
        SeqNumbers == {p.seq : p \in AllPSets}
        Reproposals(s) == {p.proposal : p \in AllPSets | p.seq = s}
    IN [s \in {s_ \in SeqNumbers | Reproposals(s_) /= {}} |-> Min(Reproposals(s_))]

\* The new leader receives a quorum of ViewData, sends a NewView, and re-proposes pending requests.
\* This action models all correct nodes advancing to the new view in a single step.
NewView(newLeader, newView) ==
    /\ newLeader = Leader(newView)
    /\ LET VDVotes == {m \in messages | m.type = "view-data" /\ m.view = newView}
           Senders == {m.sender : m \in VDVotes}
       IN /\ Cardinality(Senders) >= Quorum
          /\ LET
             \* PBFT view change safety logic: determine which proposals to re-propose.
             NewProposals == NewProposalsMap(VDVotes)
             msg == NewViewMsg(newView, newLeader)
             \* Re-broadcast PrePrepares for the new view.
             reproposalMsgs == { PrePrepareMsg(newView, s, NewProposals[s], newLeader) : s \in DOMAIN NewProposals }
             IN /\ messages' = (messages \cup {msg}) \cup reproposalMsgs
                /\ view' = [n \in Nodes |-> IF view[n] < newView THEN newView ELSE view[n]]
                /\ phase' = [n \in Nodes |-> IF view[n] < newView
                                           THEN phase[n] \oplus [s \in DOMAIN NewProposals |-> "pre-prepared"]
                                           ELSE phase[n]]
                /\ proposal' = [n \in Nodes |-> IF view[n] < newView
                                              THEN proposal[n] \oplus NewProposals
                                              ELSE proposal[n]]
                /\ UNCHANGED <<log>>

\*
--
-- Next State Relation
--
Next ==
    \/ \E leader \in Nodes, s \in Nat, p \in Proposals : Preprepare(leader, s, p)
    \/ \E replica \in Nodes, m \in messages : Prepare(replica, m)
    \/ \E replica \in Nodes, s \in Nat : Commit(replica, s)
    \/ \E replica \in Nodes, s \in Nat : Decide(replica, s)
    \/ \E replica \in Nodes : ViewChange(replica)
    \/ \E replica \in Nodes, newView \in Nat : ViewData(replica, newView)
    \/ \E newLeader \in Nodes, newView \in Nat : NewView(newLeader, newView)

\*
--
-- Specification
--
Fairness ==
    /\ \A n \in Nodes, s \in Nat, p \in Proposals : WF_vars(Preprepare(n, s, p))
    /\ \A n \in Nodes, m \in messages : WF_vars(Prepare(n, m))
    /\ \A n \in Nodes, s \in Nat : WF_vars(Commit(n, s))
    /\ \A n \in Nodes, s \in Nat : WF_vars(Decide(n, s))
    /\ \A n \in Nodes : WF_vars(ViewChange(n))
    /\ \A n \in Nodes, v \in Nat : WF_vars(ViewData(n, v))
    /\ \A n \in Nodes, v \in Nat : WF_vars(NewView(n, v))

Spec == Init /\ [][Next]_vars /\ Fairness

====
```

```cfg
SPECIFICATION Spec

CONSTANTS
    F = 1
    Nodes = 1..4
    Proposals = {101, 102}
    NULL = 0
```