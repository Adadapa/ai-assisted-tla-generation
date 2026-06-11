---- MODULE MC_TTrace_1781181873 ----
EXTENDS Sequences, TLCExt, MC, Toolbox, Naturals, TLC, MC_TEConstants

_expression ==
    LET MC_TEExpression == INSTANCE MC_TEExpression
    IN MC_TEExpression!expression
----

_trace ==
    LET MC_TETrace == INSTANCE MC_TETrace
    IN MC_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        phase = ((s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted))
        /\
        leader = ((s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1))
        /\
        proposalSeq = ((s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1))
        /\
        stopped = ((s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE))
        /\
        wal = ((s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>))
        /\
        checkpointVal = ((s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil)))
        /\
        inFlightPrepared = ((s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE))
        /\
        blacklist = ((s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}))
        /\
        delivered = ((s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}))
        /\
        inFlight = ((s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil))
        /\
        syncResult = ((s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil))
        /\
        selectedInFlight = ((s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil))
        /\
        viewDecisions = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0))
        /\
        checkpointSeq = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0))
        /\
        deliveredVal = ((s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil)))
        /\
        viewData = ((s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}))
        /\
        viewNum = ((s1 :> 1 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0))
        /\
        restoredPhase = ((s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted))
        /\
        constraintCounters = ([clientProposal |-> 0, sync |-> 0, viewChange |-> 0, viewData |-> 0, crash |-> 0, lose |-> 0])
        /\
        crashed = ((s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE))
        /\
        syncLockHolder = (Nil)
        /\
        messages = ({})
        /\
        decisionsInView = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0))
    )
----

_init ==
    /\ decisionsInView = _TETrace[1].decisionsInView
    /\ leader = _TETrace[1].leader
    /\ wal = _TETrace[1].wal
    /\ proposalSeq = _TETrace[1].proposalSeq
    /\ inFlightPrepared = _TETrace[1].inFlightPrepared
    /\ constraintCounters = _TETrace[1].constraintCounters
    /\ selectedInFlight = _TETrace[1].selectedInFlight
    /\ viewData = _TETrace[1].viewData
    /\ checkpointVal = _TETrace[1].checkpointVal
    /\ viewNum = _TETrace[1].viewNum
    /\ viewDecisions = _TETrace[1].viewDecisions
    /\ delivered = _TETrace[1].delivered
    /\ phase = _TETrace[1].phase
    /\ restoredPhase = _TETrace[1].restoredPhase
    /\ crashed = _TETrace[1].crashed
    /\ syncLockHolder = _TETrace[1].syncLockHolder
    /\ blacklist = _TETrace[1].blacklist
    /\ checkpointSeq = _TETrace[1].checkpointSeq
    /\ stopped = _TETrace[1].stopped
    /\ syncResult = _TETrace[1].syncResult
    /\ deliveredVal = _TETrace[1].deliveredVal
    /\ inFlight = _TETrace[1].inFlight
    /\ messages = _TETrace[1].messages
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ decisionsInView  = _TETrace[i].decisionsInView
        /\ decisionsInView' = _TETrace[j].decisionsInView
        /\ leader  = _TETrace[i].leader
        /\ leader' = _TETrace[j].leader
        /\ wal  = _TETrace[i].wal
        /\ wal' = _TETrace[j].wal
        /\ proposalSeq  = _TETrace[i].proposalSeq
        /\ proposalSeq' = _TETrace[j].proposalSeq
        /\ inFlightPrepared  = _TETrace[i].inFlightPrepared
        /\ inFlightPrepared' = _TETrace[j].inFlightPrepared
        /\ constraintCounters  = _TETrace[i].constraintCounters
        /\ constraintCounters' = _TETrace[j].constraintCounters
        /\ selectedInFlight  = _TETrace[i].selectedInFlight
        /\ selectedInFlight' = _TETrace[j].selectedInFlight
        /\ viewData  = _TETrace[i].viewData
        /\ viewData' = _TETrace[j].viewData
        /\ checkpointVal  = _TETrace[i].checkpointVal
        /\ checkpointVal' = _TETrace[j].checkpointVal
        /\ viewNum  = _TETrace[i].viewNum
        /\ viewNum' = _TETrace[j].viewNum
        /\ viewDecisions  = _TETrace[i].viewDecisions
        /\ viewDecisions' = _TETrace[j].viewDecisions
        /\ delivered  = _TETrace[i].delivered
        /\ delivered' = _TETrace[j].delivered
        /\ phase  = _TETrace[i].phase
        /\ phase' = _TETrace[j].phase
        /\ restoredPhase  = _TETrace[i].restoredPhase
        /\ restoredPhase' = _TETrace[j].restoredPhase
        /\ crashed  = _TETrace[i].crashed
        /\ crashed' = _TETrace[j].crashed
        /\ syncLockHolder  = _TETrace[i].syncLockHolder
        /\ syncLockHolder' = _TETrace[j].syncLockHolder
        /\ blacklist  = _TETrace[i].blacklist
        /\ blacklist' = _TETrace[j].blacklist
        /\ checkpointSeq  = _TETrace[i].checkpointSeq
        /\ checkpointSeq' = _TETrace[j].checkpointSeq
        /\ stopped  = _TETrace[i].stopped
        /\ stopped' = _TETrace[j].stopped
        /\ syncResult  = _TETrace[i].syncResult
        /\ syncResult' = _TETrace[j].syncResult
        /\ deliveredVal  = _TETrace[i].deliveredVal
        /\ deliveredVal' = _TETrace[j].deliveredVal
        /\ inFlight  = _TETrace[i].inFlight
        /\ inFlight' = _TETrace[j].inFlight
        /\ messages  = _TETrace[i].messages
        /\ messages' = _TETrace[j].messages

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("MC_TTrace_1781181873.json", _TETrace)

=============================================================================

 Note that you can extract this module `MC_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `MC_TEExpression.tla` file takes precedence 
  over the module `MC_TEExpression` below).

---- MODULE MC_TEExpression ----
EXTENDS Sequences, TLCExt, MC, Toolbox, Naturals, TLC, MC_TEConstants

expression == 
    [
        \* To hide variables of the `MC` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        decisionsInView |-> decisionsInView
        ,leader |-> leader
        ,wal |-> wal
        ,proposalSeq |-> proposalSeq
        ,inFlightPrepared |-> inFlightPrepared
        ,constraintCounters |-> constraintCounters
        ,selectedInFlight |-> selectedInFlight
        ,viewData |-> viewData
        ,checkpointVal |-> checkpointVal
        ,viewNum |-> viewNum
        ,viewDecisions |-> viewDecisions
        ,delivered |-> delivered
        ,phase |-> phase
        ,restoredPhase |-> restoredPhase
        ,crashed |-> crashed
        ,syncLockHolder |-> syncLockHolder
        ,blacklist |-> blacklist
        ,checkpointSeq |-> checkpointSeq
        ,stopped |-> stopped
        ,syncResult |-> syncResult
        ,deliveredVal |-> deliveredVal
        ,inFlight |-> inFlight
        ,messages |-> messages
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_decisionsInViewUnchanged |-> decisionsInView = decisionsInView'
        
        \* Format the `decisionsInView` variable as Json value.
        \* ,_decisionsInViewJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(decisionsInView)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_decisionsInViewModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].decisionsInView # _TETrace[s-1].decisionsInView
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE MC_TETrace ----
\*EXTENDS IOUtils, MC, TLC, MC_TEConstants
\*
\*trace == IODeserialize("MC_TTrace_1781181873.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE MC_TETrace ----
EXTENDS MC, TLC, MC_TEConstants

trace == 
    <<
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),constraintCounters |-> [clientProposal |-> 0, sync |-> 0, viewChange |-> 0, viewData |-> 0, crash |-> 0, lose |-> 0],crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> Nil,messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 1 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),constraintCounters |-> [clientProposal |-> 0, sync |-> 0, viewChange |-> 0, viewData |-> 0, crash |-> 0, lose |-> 0],crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> Nil,messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)])
    >>
----


=============================================================================

---- MODULE MC_TEConstants ----
EXTENDS MC

CONSTANTS s1, s2, s3, s4, v1, v2

=============================================================================

---- CONFIG MC_TTrace_1781181873 ----
CONSTANTS
    s1 = s1
    s2 = s2
    s3 = s3
    s4 = s4
    v1 = v1
    v2 = v2
    Nil = Nil
    Genesis = Genesis
    MsgPrePrepare = MsgPrePrepare
    MsgPrepare = MsgPrepare
    MsgCommit = MsgCommit
    MsgViewChange = MsgViewChange
    MsgViewData = MsgViewData
    MsgNewView = MsgNewView
    MsgStateTransferRequest = MsgStateTransferRequest
    MsgStateTransferResponse = MsgStateTransferResponse
    PhaseCommitted = PhaseCommitted
    PhaseProposed = PhaseProposed
    PhasePrepared = PhasePrepared
    PhaseAbort = PhaseAbort
    WalProposed = WalProposed
    WalCommit = WalCommit
    WalViewChange = WalViewChange
    WalNewView = WalNewView
    Server = { s1 , s2 , s3 , s4 }
    Values = { v1 , v2 }
    MaxSeq = 3
    MaxView = 3
    MaxWalLen = 4
    MaxDecisionsPerLeader = 2
    Quorum = 3
    MaxClientProposalLimit = 2
    MaxSyncLimit = 2
    MaxViewChangeLimit = 2
    MaxViewDataLimit = 4
    MaxCrashLimit = 1
    MaxLoseLimit = 2
    MaxMsgBufferLimit = 8
    MsgStateTransferResponse = MsgStateTransferResponse
    s1 = s1
    MsgNewView = MsgNewView
    MsgStateTransferRequest = MsgStateTransferRequest
    PhaseCommitted = PhaseCommitted
    s2 = s2
    MsgViewData = MsgViewData
    PhasePrepared = PhasePrepared
    PhaseProposed = PhaseProposed
    s3 = s3
    MsgViewChange = MsgViewChange
    v2 = v2
    MsgPrePrepare = MsgPrePrepare
    WalViewChange = WalViewChange
    WalNewView = WalNewView
    WalCommit = WalCommit
    Nil = Nil
    Genesis = Genesis
    PhaseAbort = PhaseAbort
    v1 = v1
    MsgPrepare = MsgPrepare
    s4 = s4
    MsgCommit = MsgCommit
    WalProposed = WalProposed

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Thu Jun 11 14:44:47 CEST 2026