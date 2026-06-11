---------------------------- MODULE Trace ----------------------------
(*
 * Trace validation wrapper for SmartBFT base.tla.
 *
 * Trace events are expected under ../traces/smartbft.ndjson by default.
 * The harness should emit one event per spec action, matching the event
 * names and state fields in instrumentation-spec.md.
 *)

EXTENDS base, Json, IOUtils

B == INSTANCE base

CONSTANTS s1, s2, s3, s4, v1, v2

VARIABLE l

JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON
    ELSE "../traces/smartbft.ndjson"

RawTrace == ndJsonDeserialize(JsonFile)
TraceLog == [k \in 1..Len(RawTrace) |-> RawTrace[k]]

traceVars == <<vars, l>>

LogLine == TraceLog[l]

Field(e, name, default) ==
    IF name \in DOMAIN e THEN e[name] ELSE default

StateField(e, name, default) ==
    IF "state" \in DOMAIN e /\ name \in DOMAIN e["state"]
    THEN e["state"][name]
    ELSE default

SeqToSet(seq) ==
    {seq[k] : k \in 1..Len(seq)}

DecodeNode(raw) ==
    IF raw = "s1" THEN s1
    ELSE IF raw = "s2" THEN s2
    ELSE IF raw = "s3" THEN s3
    ELSE IF raw = "s4" THEN s4
    ELSE IF raw = "Nil" THEN Nil
    ELSE raw

DecodeValue(raw) ==
    IF raw = "v1" THEN v1
    ELSE IF raw = "v2" THEN v2
    ELSE IF raw = "Genesis" THEN Genesis
    ELSE IF raw = "Nil" THEN Nil
    ELSE raw

DecodePhase(raw) ==
    IF raw = "PhaseCommitted" THEN PhaseCommitted
    ELSE IF raw = "PhaseProposed" THEN PhaseProposed
    ELSE IF raw = "PhasePrepared" THEN PhasePrepared
    ELSE IF raw = "PhaseAbort" THEN PhaseAbort
    ELSE raw

IsEvent(name) ==
    /\ l <= Len(TraceLog)
    /\ Field(LogLine, "event", "") = name

EventNode ==
    DecodeNode(Field(LogLine, "node", CHOOSE i \in Server : TRUE))

EventValue ==
    DecodeValue(Field(LogLine, "value", CHOOSE v \in Values : TRUE))

EventSender ==
    DecodeNode(Field(LogLine, "sender", CHOOSE i \in Server : TRUE))

ValidateControllerState(i) ==
    /\ StateField(LogLine, "view", viewNum[i]) = viewNum'[i]
    /\ StateField(LogLine, "proposal_seq", proposalSeq[i]) = proposalSeq'[i]
    /\ StateField(LogLine, "decisions_in_view", decisionsInView[i]) =
          decisionsInView'[i]
    /\ StateField(LogLine, "checkpoint_seq", checkpointSeq[i]) =
          checkpointSeq'[i]
    /\ DecodePhase(StateField(LogLine, "phase", phase[i])) = phase'[i]

ValidateDeliveryState(i) ==
    /\ StateField(LogLine, "checkpoint_seq", checkpointSeq[i]) =
          checkpointSeq'[i]
    /\ SeqToSet(StateField(LogLine, "delivered", <<>>)) = delivered'[i]

ValidateWalState(i) ==
    /\ StateField(LogLine, "wal_len", Len(wal[i])) = Len(wal'[i])
    /\ DecodePhase(StateField(LogLine, "phase", phase[i])) = phase'[i]

Advance ==
    l' = l + 1

\* Event: controller_start_view
\* Sources: SmartBFT/internal/bft/controller.go:384-405.
TraceControllerStartView ==
    /\ IsEvent("controller_start_view")
    /\ LET i == EventNode
           observedView == StateField(LogLine, "view", viewNum[i]) IN
       /\ B!ControllerStartView(i, observedView)
       /\ ValidateControllerState(i)
    /\ Advance

\* Event: view_propose
\* Sources: SmartBFT/internal/bft/view.go:951-978.
TraceViewPropose ==
    /\ IsEvent("view_propose")
    /\ LET i == EventNode
           val == EventValue IN
       /\ B!ViewPropose(i, val)
       /\ ValidateControllerState(i)
    /\ Advance

\* Event: view_process_preprepare
\* Sources: SmartBFT/internal/bft/view.go:302-427, 554-604.
TraceViewProcessPrePrepare ==
    /\ IsEvent("view_process_preprepare")
    /\ LET i == EventNode
           val == EventValue
           p == Proposal(viewNum[i], proposalSeq[i], viewDecisions[i],
                         val, blacklist[i], TRUE) IN
       /\ inFlight' = [inFlight EXCEPT ![i] = p]
       /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] = FALSE]
       /\ AppendWal(i, [type |-> WalProposed, proposal |-> p])
       /\ phase' = [phase EXCEPT ![i] = PhaseProposed]
       /\ messages' = messages \cup
            {Message(MsgPrepare, i, j, p, proposalSeq[i], viewNum[i]) :
                 j \in Server \ {i}}
       /\ UNCHANGED <<viewNum, proposalSeq, decisionsInView, viewDecisions,
                       stopped, leader, blacklist, decisionVars,
                       viewData, selectedInFlight, crashed, restoredPhase,
                       syncLockHolder, syncResult>>
       /\ ValidateWalState(i)
    /\ Advance

\* Event: view_process_prepares
\* Sources: SmartBFT/internal/bft/view.go:442-518.
TraceViewProcessPrepares ==
    /\ IsEvent("view_process_prepares")
    /\ LET i == EventNode IN
       /\ B!ViewProcessPrepares(i)
       /\ ValidateWalState(i)
    /\ Advance

\* Event: controller_decide
\* Sources: SmartBFT/internal/bft/controller.go:537-567.
TraceControllerDecide ==
    /\ IsEvent("controller_decide")
    /\ LET i == EventNode IN
       /\ (B!ControllerDecide(i)
           \/ /\ inFlight[i] /= Nil
              /\ ProposalSeqOf(inFlight[i]) \in delivered[i]
              /\ decisionsInView' = [decisionsInView EXCEPT ![i] = @ + 1]
              /\ phase' = [phase EXCEPT ![i] = PhaseCommitted]
              /\ inFlight' = [inFlight EXCEPT ![i] = Nil]
              /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] = FALSE]
              /\ UNCHANGED <<viewNum, proposalSeq, viewDecisions, stopped,
                              leader, blacklist, decisionVars, viewData,
                              selectedInFlight, walVars, messages,
                              syncLockHolder, syncResult>>
           \/ /\ checkpointSeq[i] \in delivered[i]
              /\ decisionsInView' = [decisionsInView EXCEPT ![i] = @ + 1]
              /\ phase' = [phase EXCEPT ![i] = PhaseCommitted]
              /\ inFlight' = [inFlight EXCEPT ![i] = Nil]
              /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] = FALSE]
              /\ UNCHANGED <<viewNum, proposalSeq, viewDecisions, stopped,
                              leader, blacklist, decisionVars, viewData,
                              selectedInFlight, walVars, messages,
                              syncLockHolder, syncResult>>)
       /\ ValidateDeliveryState(i)
    /\ Advance

\* Event: controller_change_view
\* Sources: SmartBFT/internal/bft/controller.go:407-435.
TraceControllerChangeView ==
    /\ IsEvent("controller_change_view")
    /\ LET i == EventNode
           nv == StateField(LogLine, "view", viewNum[i])
           ns == StateField(LogLine, "proposal_seq", proposalSeq[i])
           nd == StateField(LogLine, "decisions_in_view", decisionsInView[i]) IN
       /\ (B!ControllerChangeView(i, nv, ns, nd)
           \/ B!ControllerChangeViewNoop(i, nv, ns, nd))
       /\ ValidateControllerState(i)
    /\ Advance

\* Event: controller_sync_begin
\* Sources: SmartBFT/internal/bft/controller.go:585-596.
TraceControllerSyncBegin ==
    /\ IsEvent("controller_sync_begin")
    /\ LET i == EventNode IN
       /\ B!ControllerSyncBegin(i)
       /\ i \in syncLockHolder'
    /\ Advance

\* Event: controller_sync_apply
\* Sources: SmartBFT/internal/bft/controller.go:596-690.
TraceControllerSyncApply ==
    /\ IsEvent("controller_sync_apply")
    /\ LET i == EventNode
           r == [view |-> Field(LogLine, "sync_view", viewNum[i]),
                 seq |-> Field(LogLine, "sync_seq", checkpointSeq[i]),
                 decisions |-> Field(LogLine, "sync_decisions", decisionsInView[i]),
                 value |-> DecodeValue(Field(LogLine, "sync_value", Genesis))] IN
       /\ B!ControllerSyncApply(i, r)
       /\ ValidateControllerState(i)
       /\ i \notin syncLockHolder'
    /\ Advance

\* Event: mutually_exclusive_deliver
\* Sources: SmartBFT/internal/bft/controller.go:944-976.
TraceMutuallyExclusiveDeliver ==
    /\ IsEvent("mutually_exclusive_deliver")
    /\ LET i == EventNode IN
       /\ B!MutuallyExclusiveDeliver(i)
       /\ ValidateDeliveryState(i)
    /\ Advance

\* Event: viewchanger_process_viewchange
\* Sources: SmartBFT/internal/bft/viewchanger.go:393-430.
TraceViewChangerProcessViewChange ==
    /\ IsEvent("viewchanger_process_viewchange")
    /\ LET i == EventNode
           nv == StateField(LogLine, "view", viewNum[i] + 1) IN
       /\ B!ViewChangerProcessViewChange(i, nv)
       /\ ValidateWalState(i)
    /\ Advance

\* Event: viewchanger_accept_viewdata
\* Sources: SmartBFT/internal/bft/viewchanger.go:501-665.
TraceViewChangerAcceptViewData ==
    /\ IsEvent("viewchanger_accept_viewdata")
    /\ LET i == EventNode
           sender == EventSender
           prepared == Field(LogLine, "prepared", FALSE)
           prop == IF Field(LogLine, "has_inflight", FALSE)
                   THEN Proposal(viewNum[i] - 1, checkpointSeq[i] + 1,
                                 decisionsInView[i], EventValue,
                                 blacklist[i], Field(LogLine, "proposal_valid", TRUE))
                   ELSE Nil IN
       /\ B!ViewChangerAcceptViewData(i, sender, prop, prepared)
       /\ StateField(LogLine, "viewdata_count", Cardinality(viewData[i])) =
             Cardinality(viewData'[i])
    /\ Advance

\* Event: viewchanger_check_inflight
\* Sources: SmartBFT/internal/bft/viewchanger.go:747-908.
TraceViewChangerCheckInFlight ==
    /\ IsEvent("viewchanger_check_inflight")
    /\ LET i == EventNode IN
       /\ B!ViewChangerCheckInFlight(i)
       /\ StateField(LogLine, "selected_inflight_seq", ProposalSeqOf(selectedInFlight'[i])) =
             ProposalSeqOf(selectedInFlight'[i])
    /\ Advance

\* Event: viewchanger_commit_inflight
\* Sources: SmartBFT/internal/bft/viewchanger.go:1186-1305.
TraceViewChangerCommitInFlight ==
    /\ IsEvent("viewchanger_commit_inflight")
    /\ LET i == EventNode IN
       /\ B!ViewChangerCommitInFlight(i)
       /\ ValidateControllerState(i)
    /\ Advance

\* Event: viewchanger_process_newview
\* Sources: SmartBFT/internal/bft/viewchanger.go:1110-1165.
TraceViewChangerProcessNewView ==
    /\ IsEvent("viewchanger_process_newview")
    /\ LET i == EventNode IN
       /\ B!ViewChangerProcessNewView(i)
       /\ ValidateControllerState(i)
    /\ Advance

\* Event: crash
\* Sources: SmartBFT/internal/bft/state.go:38-59.
TraceCrash ==
    /\ IsEvent("crash")
    /\ LET i == EventNode IN
       /\ B!Crash(i)
       /\ StateField(LogLine, "crashed", TRUE) = crashed'[i]
    /\ Advance

\* Event: recover
\* Sources: SmartBFT/internal/bft/state.go:115-247,
\*          SmartBFT/pkg/consensus/consensus.go:460-499.
TraceRecover ==
    /\ IsEvent("recover")
    /\ LET i == EventNode IN
       /\ B!Recover(i)
       /\ ValidateControllerState(i)
       /\ StateField(LogLine, "crashed", FALSE) = crashed'[i]
    /\ Advance

TraceInit ==
    /\ Init
    /\ l = 1

TraceNext ==
    \/ TraceControllerStartView
    \/ TraceViewPropose
    \/ TraceViewProcessPrePrepare
    \/ TraceViewProcessPrepares
    \/ TraceControllerDecide
    \/ TraceControllerChangeView
    \/ TraceControllerSyncBegin
    \/ TraceControllerSyncApply
    \/ TraceMutuallyExclusiveDeliver
    \/ TraceViewChangerProcessViewChange
    \/ TraceViewChangerAcceptViewData
    \/ TraceViewChangerCheckInFlight
    \/ TraceViewChangerCommitInFlight
    \/ TraceViewChangerProcessNewView
    \/ TraceCrash
    \/ TraceRecover
    \/ /\ l > Len(TraceLog)
       /\ UNCHANGED traceVars

TraceMatched == <>(l > Len(TraceLog))

=============================================================================
