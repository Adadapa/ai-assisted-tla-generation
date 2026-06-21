```tla
---- MODULE SmartBFT ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    \* @type: Set(Int);
    Nodes,
    \* @type: Int;
    F,
    \* @type: Int;
    QuorumSize,
    \* @type: Set(Str);
    Requests,
    \* @type: Str;
    NULL,
    \* @type: Int;
    MaxSeq,
    \* @type: Int;
    MaxView,
    \* @type: Seq(Int);
    NodeList

IsPermutation(seq, set) ==
    /\ Len(seq) = Cardinality(set)
    /\ {seq[i] : i \in 1..Len(seq)} = set

ASSUME QuorumSize = 2 * F + 1
ASSUME Cardinality(Nodes) = 3 * F + 1
ASSUME NULL \notin Requests
ASSUME IsPermutation(NodeList, Nodes)

VARIABLES
    \* @type: [node: Int -> Int];
    view,
    \* @type: [node: Int -> [seq: Int -> Str]];
    phase,
    \* @type: [node: Int -> [seq: Int -> Str]];
    proposal,
    \* @type: [node: Int -> Seq([seq: Int, req: Str])];
    log,
    \* @type: Set([type: Str, view: Int, seq: Int, req: Str, sender: Int, pSet: Set([seq: Int, p: Str]), proposals: Set([seq: Int, p: Str])]);
    messages

vars == << view, phase, proposal, log, messages >>

Phases == {"IDLE", "PREPREPARED", "PREPARED", "COMMITTED"}

\* The leader for a given view.
Leader(v) ==
    LET N == Cardinality(Nodes)
    IN NodeList[(v % N) + 1]

\* The latest sequence number committed by a node.
LatestCommittedSeq(n) ==
    IF Len(log[n]) = 0 THEN 0 ELSE log[n][Len(log[n])].seq

\* Initial state of the system.
Init ==
    /\ view = [n \in Nodes |-> 0]
    /\ phase = [n \in Nodes |-> [s \in 1..MaxSeq |-> "IDLE"]]
    /\ proposal = [n \in Nodes |-> [s \in 1..MaxSeq |-> NULL]]
    /\ log = [n \in Nodes |-> << >>]
    /\ messages = {}

\* The leader proposes a new request.
Preprepare(leader, v, seq, req) ==
    /\ leader = Leader(v)
    /\ view[leader] = v
    /\ seq = LatestCommittedSeq(leader) + 1
    /\ seq \in 1..MaxSeq
    /\ req \in Requests
    /\ phase[leader][seq] = "IDLE"
    /\ messages' = messages \cup
        { [ type      |-> "Preprepare",
            view      |-> v,
            seq       |-> seq,
            req       |-> req,
            sender    |-> leader ] }
    /\ UNCHANGED << view, phase, proposal, log >>

\* A replica receives a Preprepare and broadcasts a Prepare.
Prepare(n, v, seq, req, l) ==
    /\ n # l
    /\ l = Leader(v)
    /\ view[n] = v
    /\ phase[n][seq] = "IDLE"
    /\ \E m \in messages:
        /\ m.type = "Preprepare"
        /\ m.view = v
        /\ m.seq = seq
        /\ m.req = req
        /\ m.sender = l
    /\ phase' = [phase EXCEPT ![n][seq] = "PREPREPARED"]
    /\ proposal' = [proposal EXCEPT ![n][seq] = req]
    /\ messages' = messages \cup
        { [ type      |-> "Prepare",
            view      |-> v,
            seq       |-> seq,
            req       |-> req,
            sender    |-> n ] }
    /\ UNCHANGED << view, log >>

\* A replica receives a quorum of Prepare messages and broadcasts a Commit.
Commit(n, v, seq, req) ==
    /\ view[n] = v
    /\ phase[n][seq] = "PREPREPARED"
    /\ proposal[n][seq] = req
    /\ LET PrepareQuorum == {m.sender : m \in messages |
                                /\ m.type = "Prepare"
                                /\ m.view = v
                                /\ m.seq = seq
                                /\ m.req = req }
       IN Cardinality(PrepareQuorum) >= QuorumSize
    /\ phase' = [phase EXCEPT ![n][seq] = "PREPARED"]
    /\ messages' = messages \cup
        { [ type      |-> "Commit",
            view      |-> v,
            seq       |-> seq,
            req       |-> req,
            sender    |-> n ] }
    /\ UNCHANGED << view, proposal, log >>

\* A replica receives a quorum of Commit messages and decides on the proposal.
Decide(n, v, seq, req) ==
    /\ view[n] = v
    /\ phase[n][seq] # "COMMITTED"
    /\ proposal[n][seq] = req
    /\ LET CommitQuorum == {m.sender : m \in messages |
                                /\ m.type = "Commit"
                                /\ m.view = v
                                /\ m.seq = seq
                                /\ m.req = req }
       IN Cardinality(CommitQuorum) >= QuorumSize
    /\ phase' = [phase EXCEPT ![n][seq] = "COMMITTED"]
    /\ log' = [log EXCEPT ![n] = Append(log[n], [seq |-> seq, req |-> req])]
    /\ UNCHANGED << view, proposal, messages >>

\* A replica suspects the leader and initiates a view change.
ViewChange(n) ==
    LET new_v == view[n] + 1
        pSet == { [s |-> s, p |-> proposal[n][s]] : s \in 1..MaxSeq | phase[n][s] \in {"PREPARED", "COMMITTED"} }
    IN
        /\ new_v \in 1..MaxView
        /\ view' = [view EXCEPT ![n] = new_v]
        /\ messages' = messages \cup
             { [ type      |-> "ViewChange",
                 view      |-> new_v,
                 sender    |-> n,
                 pSet      |-> pSet ] }
        /\ UNCHANGED << phase, proposal, log >>

\* After seeing a quorum of ViewChange messages, a replica sends its state to the new leader.
ViewData(n, v) ==
    LET pSet == { [s |-> s, p |-> proposal[n][s]] : s \in 1..MaxSeq | phase[n][s] \in {"PREPARED", "COMMITTED"} }
    IN
        /\ view[n] = v
        /\ Cardinality({m.sender : m \in messages |
                            /\ m.type = "ViewChange"
                            /\ m.view = v }) >= QuorumSize
        /\ \lnot (\E m \in messages: m.type = "ViewData" /\ m.view = v /\ m.sender = n)
        /\ messages' = messages \cup
            { [ type      |-> "ViewData",
                view      |-> v,
                sender    |-> n,
                pSet      |-> pSet ] }
        /\ UNCHANGED << view, phase, proposal, log >>

\* The new leader receives a quorum of ViewData messages and broadcasts a NewView.
NewView(l, v) ==
    LET VDQuorumSet == {m \in messages : m.type = "ViewData" /\ m.view = v}
        allProposals == UNION {m.pSet : m \in VDQuorumSet}
        newProposals == {p \in allProposals : \A p2 \in allProposals : (p2.s = p.s) => (p2.p = p.p)}
    IN
        /\ l = Leader(v)
        /\ view[l] = v
        /\ Cardinality({m.sender : m \in VDQuorumSet}) >= QuorumSize
        /\ \lnot (\E m \in messages: m.type = "NewView" /\ m.view = v)
        /\ messages' = messages \cup
            { [ type      |-> "NewView",
                view      |-> v,
                sender    |-> l,
                proposals |-> newProposals ] }
        /\ view' = [n \in Nodes |-> IF view[n] < v THEN v ELSE view[n]]
        /\ phase' = [n \in Nodes |-> [s \in 1..MaxSeq |->
                        LET matching_p = {p \in newProposals : p.s = s}
                        IN IF view[n] < v /\ matching_p # {}
                           THEN "PREPREPARED"
                           ELSE phase[n][s] ]]
        /\ proposal' = [n \in Nodes |-> [s \in 1..MaxSeq |->
                        LET matching_p = {p \in newProposals : p.s = s}
                        IN IF view[n] < v /\ matching_p # {}
                           THEN (CHOOSE p \in matching_p: TRUE).p
                           ELSE proposal[n][s] ]]
        /\ UNCHANGED << log >>

Next ==
    \/ (\E leader \in Nodes, v \in 0..MaxView, seq \in 1..MaxSeq, req \in Requests:
        Preprepare(leader, v, seq, req))
    \/ (\E n \in Nodes, l \in Nodes, v \in 0..MaxView, seq \in 1..MaxSeq, req \in Requests:
        Prepare(n, v, seq, req, l))
    \/ (\E n \in Nodes, v \in 0..MaxView, seq \in 1..MaxSeq, req \in Requests:
        Commit(n, v, seq, req))
    \/ (\E n \in Nodes, v \in 0..MaxView, seq \in 1..MaxSeq, req \in Requests:
        Decide(n, v, seq, req))
    \/ (\E n \in Nodes:
        ViewChange(n))
    \/ (\E n \in Nodes, v \in 1..MaxView:
        ViewData(n, v))
    \/ (\E l \in Nodes, v \in 1..MaxView:
        NewView(l, v))

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
```

```cfg
SPECIFICATION Spec

CONSTANTS
    N = 4
    Nodes = 1..N
    F = 1
    QuorumSize = 3
    Requests = {"req1"}
    NULL = "null_req"
    MaxSeq = 2
    MaxView = 2
    NodeList = <<1, 2, 3, 4>>
```