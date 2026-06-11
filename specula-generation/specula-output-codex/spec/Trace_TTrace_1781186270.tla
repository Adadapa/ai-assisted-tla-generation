---- MODULE Trace_TTrace_1781186270 ----
EXTENDS Trace, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET Trace_TEExpression == INSTANCE Trace_TEExpression
    IN Trace_TEExpression!expression
----

_trace ==
    LET Trace_TETrace == INSTANCE Trace_TETrace
    IN Trace_TETrace!trace
----

_prop ==
    ~<>[](
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
        checkpointVal = ((s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)))
        /\
        inFlightPrepared = ((s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE))
        /\
        blacklist = ((s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}))
        /\
        delivered = ((s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}))
        /\
        inFlight = ((s1 :> [value |-> v1, valid |-> TRUE, metadata |-> [seq |-> 1, view |-> 0, decisions |-> 0, blacklist |-> {}]] @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil))
        /\
        syncResult = ((s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis]))
        /\
        l = (18)
        /\
        selectedInFlight = ((s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil))
        /\
        viewDecisions = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0))
        /\
        checkpointSeq = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0))
        /\
        deliveredVal = ((s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)))
        /\
        viewData = ((s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}))
        /\
        viewNum = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0))
        /\
        restoredPhase = ((s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted))
        /\
        crashed = ((s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE))
        /\
        syncLockHolder = ({})
        /\
        messages = ({[seq |-> 1, view |-> 0, from |-> s1, to |-> s1, type |-> MsgPrePrepare, proposal |-> [value |-> v1, valid |-> TRUE, metadata |-> [seq |-> 1, view |-> 0, decisions |-> 0, blacklist |-> {}]]]})
        /\
        decisionsInView = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0))
    )
----

_init ==
    /\ decisionsInView = _TETrace[1].decisionsInView
    /\ leader = _TETrace[1].leader
    /\ l = _TETrace[1].l
    /\ wal = _TETrace[1].wal
    /\ proposalSeq = _TETrace[1].proposalSeq
    /\ inFlightPrepared = _TETrace[1].inFlightPrepared
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
        /\ l  = _TETrace[i].l
        /\ l' = _TETrace[j].l
        /\ wal  = _TETrace[i].wal
        /\ wal' = _TETrace[j].wal
        /\ proposalSeq  = _TETrace[i].proposalSeq
        /\ proposalSeq' = _TETrace[j].proposalSeq
        /\ inFlightPrepared  = _TETrace[i].inFlightPrepared
        /\ inFlightPrepared' = _TETrace[j].inFlightPrepared
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
    \*         IN J!JsonSerialize("Trace_TTrace_1781186270.json", _TETrace)

=============================================================================

 Note that you can extract this module `Trace_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `Trace_TEExpression.tla` file takes precedence 
  over the module `Trace_TEExpression` below).

---- MODULE Trace_TEExpression ----
EXTENDS Trace, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `Trace` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        decisionsInView |-> decisionsInView
        ,leader |-> leader
        ,l |-> l
        ,wal |-> wal
        ,proposalSeq |-> proposalSeq
        ,inFlightPrepared |-> inFlightPrepared
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
\*---- MODULE Trace_TETrace ----
\*EXTENDS Trace, IOUtils, TLC
\*
\*trace == IODeserialize("Trace_TTrace_1781186270.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Trace_TETrace ----
EXTENDS Trace, TLC

trace == 
    <<
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),l |-> 1,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),l |-> 2,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {s1},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),l |-> 3,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),l |-> 4,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),l |-> 5,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),l |-> 6,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {s2},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> Nil @@ s4 :> Nil),l |-> 7,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> Nil @@ s4 :> Nil),l |-> 8,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> Nil @@ s4 :> Nil),l |-> 9,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> Nil @@ s4 :> Nil),l |-> 10,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {s3},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> Nil),l |-> 11,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> Nil),l |-> 12,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> Nil),l |-> 13,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> Nil),l |-> 14,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {s4},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis]),l |-> 15,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis]),l |-> 16,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis]),l |-> 17,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)]),
    ([phase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),leader |-> (s1 :> s1 @@ s2 :> s1 @@ s3 :> s1 @@ s4 :> s1),proposalSeq |-> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1 @@ s4 :> 1),stopped |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),wal |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>> @@ s4 :> <<>>),checkpointVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),inFlightPrepared |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),blacklist |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),delivered |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),inFlight |-> (s1 :> [value |-> v1, valid |-> TRUE, metadata |-> [seq |-> 1, view |-> 0, decisions |-> 0, blacklist |-> {}]] @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),syncResult |-> (s1 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s2 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s3 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis] @@ s4 :> [seq |-> 0, view |-> 0, decisions |-> 0, value |-> Genesis]),l |-> 18,selectedInFlight |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil @@ s4 :> Nil),viewDecisions |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),checkpointSeq |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),deliveredVal |-> (s1 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s2 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s3 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil) @@ s4 :> (0 :> Genesis @@ 1 :> Nil @@ 2 :> Nil @@ 3 :> Nil @@ 4 :> Nil @@ 5 :> Nil @@ 6 :> Nil @@ 7 :> Nil @@ 8 :> Nil @@ 9 :> Nil @@ 10 :> Nil)),viewData |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {} @@ s4 :> {}),viewNum |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0),restoredPhase |-> (s1 :> PhaseCommitted @@ s2 :> PhaseCommitted @@ s3 :> PhaseCommitted @@ s4 :> PhaseCommitted),crashed |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE @@ s4 :> FALSE),syncLockHolder |-> {},messages |-> {[seq |-> 1, view |-> 0, from |-> s1, to |-> s1, type |-> MsgPrePrepare, proposal |-> [value |-> v1, valid |-> TRUE, metadata |-> [seq |-> 1, view |-> 0, decisions |-> 0, blacklist |-> {}]]]},decisionsInView |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0 @@ s4 :> 0)])
    >>
----


=============================================================================

---- CONFIG Trace_TTrace_1781186270 ----
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
    MaxSeq = 10
    MaxView = 10
    MaxWalLen = 32
    MaxDecisionsPerLeader = 3
    Quorum = 3
    WalNewView = WalNewView
    Genesis = Genesis
    MsgStateTransferResponse = MsgStateTransferResponse
    s3 = s3
    MsgCommit = MsgCommit
    PhasePrepared = PhasePrepared
    v2 = v2
    MsgNewView = MsgNewView
    WalCommit = WalCommit
    v1 = v1
    MsgViewData = MsgViewData
    WalProposed = WalProposed
    s4 = s4
    MsgViewChange = MsgViewChange
    PhaseAbort = PhaseAbort
    Nil = Nil
    MsgStateTransferRequest = MsgStateTransferRequest
    WalViewChange = WalViewChange
    s2 = s2
    MsgPrepare = MsgPrepare
    PhaseProposed = PhaseProposed
    s1 = s1
    MsgPrePrepare = MsgPrePrepare
    PhaseCommitted = PhaseCommitted

PROPERTY
    _prop

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
\* Generated on Thu Jun 11 15:57:56 CEST 2026