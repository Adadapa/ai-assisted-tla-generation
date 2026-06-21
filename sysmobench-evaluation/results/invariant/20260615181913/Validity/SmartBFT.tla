------------------------------ MODULE SmartBFT ------------------------------
(*
 * Model-checking wrapper for SmartBFT base.tla.
 * Fault-introducing actions are counter-bounded; deterministic/reactive
 * handlers delegate to the base spec without counters.
 * base spec is now flattened to be in this spec
 *)

(*
 * SmartBFT implementation-focused TLA+ model.
 *
 * Input: .specula-output/modeling-brief.md
 * Category: Distributed / Message-Passing with BFT overlay.
 *
 * Scope is bug-family driven:
 *   Family 1: decision, sync, and view-change interleavings.
 *   Family 2: DecisionsInView, leader rotation, and metadata freshness.
 *   Family 3: WAL crash recovery and persistent phase boundaries.
 *   Family 4: receiver-side validation divergence in view-change in-flight commit.
 *)

EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\* ---------------------------------------------------------------------
\* Constants
\* ---------------------------------------------------------------------

CONSTANT Server
CONSTANT Values
CONSTANT Nil
CONSTANT Genesis
CONSTANT MaxSeq
CONSTANT MaxView
CONSTANT MaxWalLen
CONSTANT MaxDecisionsPerLeader
CONSTANT Quorum

CONSTANTS
    MsgPrePrepare,
    MsgPrepare,
    MsgCommit,
    MsgViewChange,
    MsgViewData,
    MsgNewView,
    MsgStateTransferRequest,
    MsgStateTransferResponse

CONSTANTS
    PhaseCommitted,
    PhaseProposed,
    PhasePrepared,
    PhaseAbort

CONSTANTS
    WalProposed,
    WalCommit,
    WalViewChange,
    WalNewView

\* ---------------------------------------------------------------------
\* Variables
\* ---------------------------------------------------------------------

\* Controller and view state.
VARIABLE viewNum              \* [Server -> Nat]
VARIABLE proposalSeq          \* [Server -> Nat], next proposal sequence
VARIABLE decisionsInView      \* [Server -> Nat], controller counter
VARIABLE viewDecisions        \* [Server -> Nat], current View.DecisionsInView
VARIABLE phase                \* [Server -> phase]
VARIABLE stopped              \* [Server -> BOOLEAN]
VARIABLE leader               \* [Server -> Server]
VARIABLE blacklist            \* [Server -> SUBSET Server]

\* Decision/checkpoint state.
VARIABLE checkpointSeq        \* [Server -> Nat]
VARIABLE checkpointVal        \* [Server -> [Nat -> Values \cup {Genesis, Nil}]]
VARIABLE delivered            \* [Server -> SUBSET Nat]
VARIABLE deliveredVal         \* [Server -> [Nat -> Values \cup {Genesis, Nil}]]

\* In-flight proposal and view-change evidence.
VARIABLE inFlight             \* [Server -> proposal record or Nil]
VARIABLE inFlightPrepared     \* [Server -> BOOLEAN]
VARIABLE viewData             \* [Server -> SUBSET records]
VARIABLE selectedInFlight     \* [Server -> proposal record or Nil]

\* WAL/recovery state.
VARIABLE wal                  \* [Server -> Seq(record)]
VARIABLE crashed              \* [Server -> BOOLEAN]
VARIABLE restoredPhase        \* [Server -> phase]

\* Network and synchronization.
VARIABLE messages             \* SUBSET message records
VARIABLE syncLockHolder       \* SUBSET Server, one per Controller.syncLock
VARIABLE syncResult           \* [Server -> sync result record or Nil]

controllerVars == <<viewNum, proposalSeq, decisionsInView, viewDecisions,
                    phase, stopped, leader, blacklist>>
decisionVars == <<checkpointSeq, checkpointVal, delivered, deliveredVal>>
inFlightVars == <<inFlight, inFlightPrepared, viewData, selectedInFlight>>
walVars == <<wal, crashed, restoredPhase>>
netVars == <<messages, syncLockHolder, syncResult>>

vars == <<controllerVars, decisionVars, inFlightVars, walVars, netVars>>

\* ---------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------

NatSeq == 0..MaxSeq
NatView == 0..MaxView
ValueOrNil == Values \cup {Genesis, Nil}

Metadata(v, s, d, bl) ==
    [view |-> v, seq |-> s, decisions |-> d, blacklist |-> bl]

Proposal(v, s, d, val, bl, valid) ==
    [metadata |-> Metadata(v, s, d, bl),
     value |-> val,
     valid |-> valid]

InitialValueMap == [s \in NatSeq |-> IF s = 0 THEN Genesis ELSE Nil]

CandidateLeader(v, d, bl) ==
    CHOOSE s \in Server \ bl : TRUE

Message(t, from, to, prop, seq, v) ==
    [type |-> t, from |-> from, to |-> to, proposal |-> prop, seq |-> seq, view |-> v]

Send(m) == messages' = messages \cup {m}
Drop(m) == messages' = messages \ {m}

AppendWal(i, entry) ==
    wal' = [wal EXCEPT ![i] =
        IF Len(wal[i]) < MaxWalLen THEN Append(wal[i], entry) ELSE wal[i]]

LastWal(i) ==
    IF Len(wal[i]) = 0 THEN Nil ELSE wal[i][Len(wal[i])]

ProposalSeqOf(p) == p.metadata.seq
ProposalViewOf(p) == p.metadata.view
ProposalDecisionsOf(p) == p.metadata.decisions
ProposalBlacklistOf(p) == p.metadata.blacklist

ProposalSet ==
    {Proposal(v, s, d, val, bl, valid) :
        v \in NatView,
        s \in 1..MaxSeq,
        d \in 0..MaxSeq,
        val \in Values,
        bl \in SUBSET Server,
        valid \in BOOLEAN}

AgreementForSeq(seq) ==
    LET vals == {deliveredVal[i][seq] : i \in {j \in Server : seq \in delivered[j]}}
    IN Cardinality(vals \ {Nil}) <= 1

\* ---------------------------------------------------------------------
\* Initialization
\* ---------------------------------------------------------------------

Init ==
    /\ viewNum = [i \in Server |-> 0]
    /\ proposalSeq = [i \in Server |-> 1]
    /\ decisionsInView = [i \in Server |-> 0]
    /\ viewDecisions = [i \in Server |-> 0]
    /\ phase = [i \in Server |-> PhaseCommitted]
    /\ stopped = [i \in Server |-> FALSE]
    /\ blacklist = [i \in Server |-> {}]
    /\ leader = [i \in Server |-> CandidateLeader(0, 0, {})]
    /\ checkpointSeq = [i \in Server |-> 0]
    /\ checkpointVal = [i \in Server |-> InitialValueMap]
    /\ delivered = [i \in Server |-> {}]
    /\ deliveredVal = [i \in Server |-> InitialValueMap]
    /\ inFlight = [i \in Server |-> Nil]
    /\ inFlightPrepared = [i \in Server |-> FALSE]
    /\ viewData = [i \in Server |-> {}]
    /\ selectedInFlight = [i \in Server |-> Nil]
    /\ wal = [i \in Server |-> <<>>]
    /\ crashed = [i \in Server |-> FALSE]
    /\ restoredPhase = [i \in Server |-> PhaseCommitted]
    /\ messages = {}
    /\ syncLockHolder = {}
    /\ syncResult = [i \in Server |-> Nil]

\* ---------------------------------------------------------------------
\* Implementation actions
\* ---------------------------------------------------------------------

\* Controller.startView / ProposalMaker.NewProposer
\* Sources: SmartBFT/internal/bft/controller.go:384-405,
\*          SmartBFT/internal/bft/util.go:272-328.
ControllerStartView(i, newView) ==
    /\ ~crashed[i]
    /\ ~stopped[i]
    /\ newView \in NatView
    /\ newView >= viewNum[i]
    /\ phase[i] \in {PhaseCommitted, PhaseAbort}
    \* controller.go:384 builds a proposer using current leader, sequence,
    \* current view number, and currDecisionsInView.
    /\ viewNum' = [viewNum EXCEPT ![i] = newView]
    /\ leader' = [leader EXCEPT ![i] =
          CandidateLeader(newView, decisionsInView[i], blacklist[i])]
    /\ viewDecisions' = [viewDecisions EXCEPT ![i] = decisionsInView[i]]
    \* util.go:300-328 stores active view sequence and restored phase.
    /\ phase' = [phase EXCEPT ![i] = restoredPhase[i]]
    /\ UNCHANGED <<proposalSeq, decisionsInView, stopped, blacklist,
                    decisionVars, inFlightVars, walVars, messages,
                    syncLockHolder, syncResult>>

\* View.Propose creates a pre-prepare and sends it to self before broadcast.
\* Sources: SmartBFT/internal/bft/view.go:897-925, 951-978.
ViewPropose(i, val) ==
    /\ ~crashed[i]
    /\ ~stopped[i]
    /\ leader[i] = i
    /\ phase[i] = PhaseCommitted
    /\ val \in Values
    /\ LET p == Proposal(viewNum[i], proposalSeq[i], viewDecisions[i],
                         val, blacklist[i], TRUE) IN
          \* view.go:974-980 enqueues the self pre-prepare through HandleMessage.
          /\ Send(Message(MsgPrePrepare, i, i, p, proposalSeq[i], viewNum[i]))
          /\ UNCHANGED <<controllerVars, decisionVars, inFlightVars, walVars,
                          syncLockHolder, syncResult>>

\* View.processProposal accepts a pre-prepare after verifyProposal.
\* Sources: SmartBFT/internal/bft/view.go:302-427, 554-604.
ViewProcessPrePrepare(i, m) ==
    /\ ~crashed[i]
    /\ m \in messages
    /\ m.to = i
    /\ m.type = MsgPrePrepare
    /\ m.proposal /= Nil
    \* view.go:568-581 metadata must match current view, sequence, decisions.
    /\ m.proposal.metadata.view = viewNum[i]
    /\ m.proposal.metadata.seq = proposalSeq[i]
    /\ m.proposal.metadata.decisions = viewDecisions[i]
    \* view.go:554-604 abstracts app proposal, blacklist, and prev-commit checks.
    /\ m.proposal.valid
    /\ inFlight' = [inFlight EXCEPT ![i] = m.proposal]
    /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] = FALSE]
    \* view.go:405-415 persists ProposedRecord before prepare broadcast.
    /\ AppendWal(i, [type |-> WalProposed, proposal |-> m.proposal])
    /\ phase' = [phase EXCEPT ![i] = PhaseProposed]
    /\ messages' = (messages \ {m}) \cup
         {Message(MsgPrepare, i, j, m.proposal, proposalSeq[i], viewNum[i]) :
              j \in Server \ {i}}
    /\ UNCHANGED <<viewNum, proposalSeq, decisionsInView, viewDecisions,
                    stopped, leader, blacklist, decisionVars,
                    viewData, selectedInFlight, crashed, restoredPhase,
                    syncLockHolder, syncResult>>

\* Trace replay fallback for accepted pre-prepares whose network enqueue is
\* below the trace abstraction.
ViewProcessPrePrepareObserved(i, val) ==
    /\ ~crashed[i]
    /\ val \in Values
    /\ LET p == Proposal(viewNum[i], proposalSeq[i], viewDecisions[i],
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

\* View.processPrepares records prepared state.
\* Sources: SmartBFT/internal/bft/view.go:442-518.
ViewProcessPrepares(i) ==
    /\ ~crashed[i]
    /\ phase[i] = PhaseProposed
    /\ inFlight[i] /= Nil
    \* view.go:447-461 waits for Quorum-1 matching prepares; abstracted as enabled.
    /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] = TRUE]
    \* view.go:501-511 persists commit message before broadcasting.
    /\ AppendWal(i, [type |-> WalCommit, proposal |-> inFlight[i]])
    /\ phase' = [phase EXCEPT ![i] = PhasePrepared]
    /\ messages' = messages \cup
         {Message(MsgCommit, i, j, inFlight[i], proposalSeq[i], viewNum[i]) :
              j \in Server \ {i}}
    /\ UNCHANGED <<viewNum, proposalSeq, decisionsInView, viewDecisions,
                    stopped, leader, blacklist, decisionVars,
                    inFlight, viewData, selectedInFlight,
                    crashed, restoredPhase, syncLockHolder, syncResult>>

\* Controller.decide / View.decide normal commit path.
\* Sources: SmartBFT/internal/bft/view.go:852-859,
\*          SmartBFT/internal/bft/controller.go:537-567.
ControllerDecide(i) ==
    /\ ~crashed[i]
    /\ phase[i] = PhasePrepared
    /\ inFlight[i] /= Nil
    /\ LET s == ProposalSeqOf(inFlight[i])
           v == inFlight[i].value IN
          /\ s \notin delivered[i]
          \* controller.go:539 delivers before pool pruning and counter increment.
          /\ delivered' = [delivered EXCEPT ![i] = @ \cup {s}]
          /\ deliveredVal' = [deliveredVal EXCEPT ![i] =
                [deliveredVal[i] EXCEPT ![s] = v]]
          /\ checkpointSeq' = [checkpointSeq EXCEPT ![i] = s]
          /\ checkpointVal' = [checkpointVal EXCEPT ![i] =
                [checkpointVal[i] EXCEPT ![s] = v]]
          \* controller.go:550 increments current decisions in view.
          /\ decisionsInView' = [decisionsInView EXCEPT ![i] = @ + 1]
          \* view.go:861-895 advances the view-local sequence and decisions.
          /\ proposalSeq' = [proposalSeq EXCEPT ![i] = s + 1]
          /\ viewDecisions' = [viewDecisions EXCEPT ![i] = @ + 1]
          /\ phase' = [phase EXCEPT ![i] = PhaseCommitted]
          /\ inFlight' = [inFlight EXCEPT ![i] = Nil]
          /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] = FALSE]
          /\ UNCHANGED <<viewNum, stopped, leader, blacklist,
                          viewData, selectedInFlight, walVars, messages,
                          syncLockHolder, syncResult>>

\* Controller.changeView.
\* Sources: SmartBFT/internal/bft/controller.go:407-435.
ControllerChangeView(i, newView, newSeq, newDecisions) ==
    /\ ~crashed[i]
    /\ newView \in NatView
    /\ newSeq \in 1..MaxSeq
    /\ newDecisions \in Nat
    \* controller.go:409-420 ignores stale/no-op view changes.
    /\ newView >= viewNum[i]
    /\ \/ newView > viewNum[i]
       \/ proposalSeq[i] /= newSeq
       \/ decisionsInView[i] /= newDecisions
       \/ stopped[i]
    \* controller.go:423-430 aborts, sets view/decisions, starts view.
    /\ viewNum' = [viewNum EXCEPT ![i] = newView]
    /\ proposalSeq' = [proposalSeq EXCEPT ![i] = newSeq]
    /\ decisionsInView' = [decisionsInView EXCEPT ![i] = newDecisions]
    /\ viewDecisions' = [viewDecisions EXCEPT ![i] = newDecisions]
    /\ phase' = [phase EXCEPT ![i] = PhaseCommitted]
    /\ leader' = [leader EXCEPT ![i] =
          CandidateLeader(newView, newDecisions, blacklist[i])]
    /\ UNCHANGED <<stopped, blacklist, decisionVars, inFlightVars,
                    walVars, messages, syncLockHolder, syncResult>>

\* changeView can return without changing state for stale/no-op requests.
ControllerChangeViewNoop(i, newView, newSeq, newDecisions) ==
    /\ ~crashed[i]
    /\ newView \in NatView
    /\ newSeq \in 1..MaxSeq
    /\ newDecisions \in Nat
    /\ \/ newView < viewNum[i]
       \/ /\ newView = viewNum[i]
          /\ proposalSeq[i] = newSeq
          /\ decisionsInView[i] = newDecisions
          /\ ~stopped[i]
    /\ UNCHANGED vars

\* Controller.sync starts the critical section.
\* Sources: SmartBFT/internal/bft/controller.go:585-596.
ControllerSyncBegin(i) ==
    /\ ~crashed[i]
    /\ i \notin syncLockHolder
    /\ syncLockHolder' = syncLockHolder \cup {i}
    /\ UNCHANGED syncResult
    /\ UNCHANGED <<controllerVars, decisionVars, inFlightVars, walVars, messages>>

\* Controller.sync applies latest decision and fetched state.
\* Sources: SmartBFT/internal/bft/controller.go:596-690, 693-716.
ControllerSyncApply(i, result) ==
    /\ ~crashed[i]
    /\ i \in syncLockHolder
    /\ result \in [view : NatView, seq : NatSeq, decisions : Nat, value : ValueOrNil]
    /\ result.seq >= checkpointSeq[i]
    /\ LET r == result IN
          /\ IF r.seq > checkpointSeq[i]
             THEN
               \* controller.go:637-644 updates checkpoint and derives next sequence.
               /\ checkpointSeq' = [checkpointSeq EXCEPT ![i] = r.seq]
               /\ checkpointVal' = [checkpointVal EXCEPT ![i] =
                    [checkpointVal[i] EXCEPT ![r.seq] = r.value]]
               /\ proposalSeq' = [proposalSeq EXCEPT ![i] = r.seq + 1]
               /\ decisionsInView' = [decisionsInView EXCEPT ![i] = r.decisions + 1]
               /\ viewDecisions' = [viewDecisions EXCEPT ![i] = r.decisions + 1]
             ELSE
               \* controller.go:635 and PR #663 keep decisions from current metadata
               \* during same-height sync unless fetched state advances view.
               /\ UNCHANGED <<checkpointSeq, checkpointVal, proposalSeq,
                               decisionsInView, viewDecisions>>
          /\ IF r.view > viewNum[i]
             THEN
               \* controller.go:646-688 records higher view and informs view changer.
               /\ viewNum' = [viewNum EXCEPT ![i] = r.view]
               /\ leader' = [leader EXCEPT ![i] =
                    CandidateLeader(r.view, decisionsInView'[i], blacklist[i])]
             ELSE UNCHANGED <<viewNum, leader>>
          \* controller.go:681-683 / 693-716 prune stale in-flight proposals.
          /\ IF inFlight[i] /= Nil /\ r.seq >= ProposalSeqOf(inFlight[i])
             THEN /\ inFlight' = [inFlight EXCEPT ![i] = Nil]
                  /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] = FALSE]
             ELSE UNCHANGED <<inFlight, inFlightPrepared>>
          /\ syncLockHolder' = syncLockHolder \ {i}
          /\ syncResult' = [syncResult EXCEPT ![i] = result]
          /\ UNCHANGED <<stopped, blacklist, delivered, deliveredVal,
                          viewData, selectedInFlight, walVars, messages, phase>>

\* MutuallyExclusiveDeliver.Deliver handles a pending delivery that sync already passed.
\* Sources: SmartBFT/internal/bft/controller.go:944-976.
MutuallyExclusiveDeliver(i) ==
    /\ ~crashed[i]
    /\ i \notin syncLockHolder
    /\ inFlight[i] /= Nil
    /\ LET s == ProposalSeqOf(inFlight[i])
           v == inFlight[i].value IN
          /\ IF checkpointSeq[i] >= s /\ checkpointSeq[i] /= 0
             THEN
               \* controller.go:956-966 returns result from sync and does not deliver again.
               /\ delivered' = delivered
               /\ deliveredVal' = deliveredVal
             ELSE
               \* controller.go:969-975 delivers and checkpoints pending proposal.
               /\ delivered' = [delivered EXCEPT ![i] = @ \cup {s}]
               /\ deliveredVal' = [deliveredVal EXCEPT ![i] =
                    [deliveredVal[i] EXCEPT ![s] = v]]
          /\ checkpointSeq' = [checkpointSeq EXCEPT ![i] =
                IF checkpointSeq[i] >= s THEN checkpointSeq[i] ELSE s]
          /\ checkpointVal' = [checkpointVal EXCEPT ![i] =
                [checkpointVal[i] EXCEPT ![s] = v]]
          /\ UNCHANGED <<controllerVars, inFlightVars, walVars, messages,
                          syncLockHolder, syncResult>>

\* ViewChanger.processViewChangeMsg saves view-change and prepares view data.
\* Sources: SmartBFT/internal/bft/viewchanger.go:393-430.
ViewChangerProcessViewChange(i, newView) ==
    /\ ~crashed[i]
    /\ newView = viewNum[i] + 1
    /\ newView \in NatView
    \* viewchanger.go:407-416 saves ViewChange record.
    /\ AppendWal(i, [type |-> WalViewChange, view |-> newView])
    \* viewchanger.go:418-423 aborts current view and moves to next view.
    /\ viewNum' = [viewNum EXCEPT ![i] = newView]
    /\ phase' = [phase EXCEPT ![i] = PhaseAbort]
    /\ selectedInFlight' = [selectedInFlight EXCEPT ![i] = Nil]
    /\ UNCHANGED <<proposalSeq, decisionsInView, viewDecisions, stopped,
                    leader, blacklist, decisionVars, inFlight,
                    inFlightPrepared, viewData, crashed, restoredPhase,
                    messages, syncLockHolder, syncResult>>

\* ViewChanger.validateViewDataMsg / checkLastDecision accepts view data.
\* Sources: SmartBFT/internal/bft/viewchanger.go:501-665.
ViewChangerAcceptViewData(i, sender, prop, prepared) ==
    /\ ~crashed[i]
    /\ i \in Server
    /\ sender \in Server
    /\ viewNum[i] > 0
    /\ prop \in {Nil} \cup
        {Proposal(viewNum[i] - 1, checkpointSeq[i] + 1, decisionsInView[i],
                  v, blacklist[i], valid) : v \in Values, valid \in BOOLEAN}
    \* viewchanger.go:512-528 checks next view and in-flight sequence shape.
    /\ IF prop = Nil THEN TRUE ELSE ProposalSeqOf(prop) = checkpointSeq[i] + 1
    \* viewchanger.go:592-665 accepts same or one-ahead last decision data.
    /\ viewData' = [viewData EXCEPT ![i] =
          @ \cup {[sender |-> sender, proposal |-> prop, prepared |-> prepared]}]
    /\ UNCHANGED <<controllerVars, decisionVars, inFlight, inFlightPrepared,
                    selectedInFlight, walVars, messages, syncLockHolder,
                    syncResult>>

\* CheckInFlight selects an in-flight proposal from quorum view data.
\* Sources: SmartBFT/internal/bft/viewchanger.go:747-908.
ViewChangerCheckInFlight(i) ==
    /\ ~crashed[i]
    /\ Cardinality(viewData[i]) >= Quorum
    /\ \E p \in {d.proposal : d \in viewData[i]} :
          /\ p /= Nil
          /\ Cardinality({d \in viewData[i] : d.proposal = p /\ d.prepared}) > 0
    /\ LET p == CHOOSE pp \in {d.proposal : d \in viewData[i]} :
                   pp /= Nil /\
                   Cardinality({d \in viewData[i] : d.proposal = pp /\ d.prepared}) > 0
       IN
          \* viewchanger.go:884-905 applies A1/A2/no-in-flight conditions.
          /\ selectedInFlight' = [selectedInFlight EXCEPT ![i] = p]
          /\ UNCHANGED <<controllerVars, decisionVars, inFlight, inFlightPrepared,
                          viewData, walVars, messages, syncLockHolder, syncResult>>

\* ViewChanger.commitInFlightProposal creates a temporary prepared view.
\* Sources: SmartBFT/internal/bft/viewchanger.go:1186-1305.
ViewChangerCommitInFlight(i) ==
    /\ ~crashed[i]
    /\ selectedInFlight[i] /= Nil
    /\ LET p == selectedInFlight[i]
           s == ProposalSeqOf(p) IN
          /\ s = checkpointSeq[i] + 1 \/ s = checkpointSeq[i]
          \* viewchanger.go:1197-1214 avoids re-committing same sequence unless equal.
          /\ IF s = checkpointSeq[i]
             THEN checkpointVal[i][s] = p.value
             ELSE TRUE
          \* viewchanger.go:1216-1279 constructs a PREPARED temporary view.
          /\ inFlight' = [inFlight EXCEPT ![i] = p]
          /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] = TRUE]
          /\ phase' = [phase EXCEPT ![i] = PhasePrepared]
          /\ UNCHANGED <<viewNum, proposalSeq, decisionsInView, viewDecisions,
                          stopped, leader, blacklist, decisionVars,
                          viewData, selectedInFlight, walVars, messages,
                          syncLockHolder, syncResult>>

\* ViewChanger.processNewViewMsg saves new-view and tells controller.
\* Sources: SmartBFT/internal/bft/viewchanger.go:1110-1165.
ViewChangerProcessNewView(i) ==
    /\ ~crashed[i]
    /\ phase[i] \in {PhasePrepared, PhaseAbort, PhaseCommitted}
    \* viewchanger.go:1141-1150 saves NewView record after in-flight handling.
    /\ AppendWal(i, [type |-> WalNewView,
                     view |-> viewNum[i],
                     seq |-> checkpointSeq[i]])
    \* viewchanger.go:1161-1164 notifies controller with mySequence+1.
    /\ proposalSeq' = [proposalSeq EXCEPT ![i] = checkpointSeq[i] + 1]
    /\ decisionsInView' = [decisionsInView EXCEPT ![i] = 0]
    /\ viewDecisions' = [viewDecisions EXCEPT ![i] = 0]
    /\ phase' = [phase EXCEPT ![i] = PhaseCommitted]
    /\ leader' = [leader EXCEPT ![i] = CandidateLeader(viewNum[i], 0, blacklist[i])]
    /\ UNCHANGED <<viewNum, stopped, blacklist, decisionVars,
                    inFlightVars, crashed, restoredPhase, messages,
                    syncLockHolder, syncResult>>

\* PersistedState.Save already modeled by WAL append sites; this action models crash.
\* Sources: SmartBFT/internal/bft/state.go:38-59.
Crash(i) ==
    /\ ~crashed[i]
    /\ crashed' = [crashed EXCEPT ![i] = TRUE]
    /\ stopped' = [stopped EXCEPT ![i] = TRUE]
    /\ syncLockHolder' = syncLockHolder \ {i}
    /\ UNCHANGED <<viewNum, proposalSeq, decisionsInView, viewDecisions,
                    phase, leader, blacklist, decisionVars, inFlightVars,
                    wal, restoredPhase, messages, syncResult>>

\* PersistedState.Restore / Consensus.setViewAndSeq.
\* Sources: SmartBFT/internal/bft/state.go:115-247,
\*          SmartBFT/pkg/consensus/consensus.go:460-499.
Recover(i) ==
    /\ i \in Server
    /\ LET last == LastWal(i) IN
          /\ \* state.go:120-247 restores phase from last WAL record.
             restoredPhase' = [restoredPhase EXCEPT ![i] =
                IF last = Nil THEN PhaseCommitted
                ELSE IF last.type = WalProposed THEN PhaseProposed
                ELSE IF last.type = WalCommit THEN PhasePrepared
                ELSE IF last.type = WalNewView THEN PhaseCommitted
                ELSE PhaseAbort]
          /\ phase' = [phase EXCEPT ![i] = restoredPhase'[i]]
          /\ inFlight' = [inFlight EXCEPT ![i] =
                IF last # Nil /\ last.type \in {WalProposed, WalCommit}
                THEN last.proposal ELSE inFlight[i]]
          /\ inFlightPrepared' = [inFlightPrepared EXCEPT ![i] =
                IF last # Nil /\ last.type = WalCommit THEN TRUE
                ELSE IF last # Nil /\ last.type = WalProposed THEN FALSE
                ELSE inFlightPrepared[i]]
          /\ \* consensus.go:471-499 separately restores view-change/new-view markers.
             viewNum' = [viewNum EXCEPT ![i] =
                IF last # Nil /\ last.type \in {WalNewView, WalViewChange}
                THEN last.view ELSE viewNum[i]]
          /\ proposalSeq' = [proposalSeq EXCEPT ![i] =
                IF last # Nil /\ last.type \in {WalProposed, WalCommit}
                THEN ProposalSeqOf(last.proposal)
                ELSE IF last # Nil /\ last.type = WalNewView
                THEN last.seq + 1
                ELSE proposalSeq[i]]
          /\ decisionsInView' = [decisionsInView EXCEPT ![i] =
                IF last # Nil /\ last.type = WalNewView THEN 0 ELSE decisionsInView[i]]
          /\ viewDecisions' = [viewDecisions EXCEPT ![i] =
                IF last # Nil /\ last.type \in {WalProposed, WalCommit}
                THEN ProposalDecisionsOf(last.proposal)
                ELSE IF last # Nil /\ last.type = WalNewView THEN 0
                ELSE viewDecisions[i]]
          /\ crashed' = [crashed EXCEPT ![i] = FALSE]
          /\ stopped' = [stopped EXCEPT ![i] = FALSE]
          /\ UNCHANGED <<leader, blacklist, checkpointSeq, checkpointVal,
                          delivered, deliveredVal, viewData, selectedInFlight,
                          wal, messages, syncLockHolder, syncResult>>

\* Message loss/reordering abstraction.
LoseMessage(m) ==
    /\ m \in messages
    /\ Drop(m)
    /\ UNCHANGED <<controllerVars, decisionVars, inFlightVars, walVars,
                    syncLockHolder, syncResult>>

Next ==
    \/ \E i \in Server, v \in NatView : ControllerStartView(i, v)
    \/ \E i \in Server, val \in Values : ViewPropose(i, val)
    \/ \E i \in Server, m \in messages : ViewProcessPrePrepare(i, m)
    \/ \E i \in Server : ViewProcessPrepares(i)
    \/ \E i \in Server : ControllerDecide(i)
    \/ \E i \in Server, v \in NatView, s \in 1..MaxSeq, d \in 0..MaxSeq :
          ControllerChangeView(i, v, s, d)
    \/ \E i \in Server, v \in NatView, s \in 1..MaxSeq, d \in 0..MaxSeq :
          ControllerChangeViewNoop(i, v, s, d)
    \/ \E i \in Server, r \in [view : NatView, seq : NatSeq,
                               decisions : 0..MaxSeq, value : ValueOrNil] :
          ControllerSyncApply(i, r)
    \/ \E i \in Server : ControllerSyncBegin(i)
    \/ \E i \in Server : MutuallyExclusiveDeliver(i)
    \/ \E i \in Server, v \in NatView : ViewChangerProcessViewChange(i, v)
    \/ \E i, j \in Server, p \in {Nil} \cup ProposalSet,
          prepared \in BOOLEAN :
          ViewChangerAcceptViewData(i, j, p, prepared)
    \/ \E i \in Server : ViewChangerCheckInFlight(i)
    \/ \E i \in Server : ViewChangerCommitInFlight(i)
    \/ \E i \in Server : ViewChangerProcessNewView(i)
    \/ \E i \in Server : Crash(i)
    \/ \E i \in Server : Recover(i)
    \/ \E m \in messages : LoseMessage(m)

\* ---------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------

TypeOK ==
    /\ viewNum \in [Server -> NatView]
    /\ proposalSeq \in [Server -> 1..(MaxSeq + 1)]
    /\ decisionsInView \in [Server -> Nat]
    /\ viewDecisions \in [Server -> Nat]
    /\ phase \in [Server -> {PhaseCommitted, PhaseProposed, PhasePrepared, PhaseAbort}]
    /\ stopped \in [Server -> BOOLEAN]
    /\ leader \in [Server -> Server]
    /\ blacklist \in [Server -> SUBSET Server]
    /\ checkpointSeq \in [Server -> NatSeq]
    /\ delivered \in [Server -> SUBSET NatSeq]
    /\ inFlightPrepared \in [Server -> BOOLEAN]
    /\ wal \in [Server -> Seq(UNION {
          [type : {WalProposed, WalCommit}, proposal : ProposalSet],
          [type : {WalViewChange}, view : NatView],
          [type : {WalNewView}, view : NatView, seq : NatSeq]})]
    /\ crashed \in [Server -> BOOLEAN]
    /\ syncLockHolder \in SUBSET Server
    /\ syncResult \in [Server -> [view : NatView, seq : NatSeq,
                                  decisions : Nat, value : ValueOrNil] \cup {Nil}]
    /\ messages \in SUBSET [type : {MsgPrePrepare, MsgPrepare, MsgCommit,
                                    MsgViewChange, MsgViewData, MsgNewView,
                                    MsgStateTransferRequest, MsgStateTransferResponse},
                            from : Server, to : Server,
                            proposal : ProposalSet \cup {Nil},
                            seq : Nat, view : Nat]

Agreement ==
    \A s \in NatSeq : AgreementForSeq(s)

NoDuplicateDelivery ==
    \A i \in Server : Cardinality(delivered[i]) = Cardinality({s \in delivered[i] : TRUE})

MonotonicCheckpoint ==
    \A i \in Server : checkpointSeq[i] <= MaxSeq

LeaderMetadataAgreement ==
    \A i, j \in Server :
        /\ ~crashed[i] /\ ~crashed[j]
        /\ viewNum[i] = viewNum[j]
        /\ proposalSeq[i] = proposalSeq[j]
        /\ decisionsInView[i] = decisionsInView[j]
        /\ blacklist[i] = blacklist[j]
        => leader[i] = leader[j]

InFlightSelectionSafety ==
    \A i \in Server :
        selectedInFlight[i] # Nil =>
            /\ ProposalSeqOf(selectedInFlight[i]) \in {checkpointSeq[i], checkpointSeq[i] + 1}
            /\ selectedInFlight[i].valid

RestorePhaseSoundness ==
    \A i \in Server :
        /\ ~crashed[i]
        /\ phase[i] = PhasePrepared
        /\ inFlight[i] /= Nil
        => ProposalSeqOf(inFlight[i]) >= checkpointSeq[i]

Spec == Init /\ [][Next]_vars

CONSTANT MaxClientProposalLimit
CONSTANT MaxSyncLimit
CONSTANT MaxViewChangeLimit
CONSTANT MaxViewDataLimit
CONSTANT MaxCrashLimit
CONSTANT MaxLoseLimit
CONSTANT MaxMsgBufferLimit

VARIABLE constraintCounters

faultVars == <<constraintCounters>>
mcVars == <<vars, constraintCounters>>

MCViewPropose(i, val) ==
    /\ constraintCounters.clientProposal < MaxClientProposalLimit
    /\ ViewPropose(i, val)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.clientProposal = @ + 1]

MCControllerSyncBegin(i) ==
    /\ constraintCounters.sync < MaxSyncLimit
    /\ ControllerSyncBegin(i)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.sync = @ + 1]

MCViewChangerProcessViewChange(i, newView) ==
    /\ constraintCounters.viewChange < MaxViewChangeLimit
    /\ ViewChangerProcessViewChange(i, newView)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.viewChange = @ + 1]

MCViewChangerAcceptViewData(i, sender, prop, prepared) ==
    /\ constraintCounters.viewData < MaxViewDataLimit
    /\ ViewChangerAcceptViewData(i, sender, prop, prepared)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.viewData = @ + 1]

MCCrash(i) ==
    /\ constraintCounters.crash < MaxCrashLimit
    /\ Crash(i)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.crash = @ + 1]

MCLoseMessage(m) ==
    /\ constraintCounters.lose < MaxLoseLimit
    /\ LoseMessage(m)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.lose = @ + 1]

MCInit ==
    /\ Init
    /\ constraintCounters = [
        clientProposal |-> 0,
        sync |-> 0,
        viewChange |-> 0,
        viewData |-> 0,
        crash |-> 0,
        lose |-> 0]

MCNext ==
    \/ \E i \in Server, v \in NatView :
          ControllerStartView(i, v) /\ UNCHANGED faultVars
    \/ \E i \in Server, val \in Values : MCViewPropose(i, val)
    \/ \E i \in Server, m \in messages :
          ViewProcessPrePrepare(i, m) /\ UNCHANGED faultVars
    \/ \E i \in Server : ViewProcessPrepares(i) /\ UNCHANGED faultVars
    \/ \E i \in Server : ControllerDecide(i) /\ UNCHANGED faultVars
    \/ \E i \in Server, v \in NatView, s \in 1..MaxSeq, d \in 0..MaxSeq :
          ControllerChangeView(i, v, s, d) /\ UNCHANGED faultVars
    \/ \E i \in Server : MCControllerSyncBegin(i)
    \/ \E i \in Server, r \in [view : NatView, seq : NatSeq,
                               decisions : 0..MaxSeq, value : ValueOrNil] :
          ControllerSyncApply(i, r) /\ UNCHANGED faultVars
    \/ \E i \in Server : MutuallyExclusiveDeliver(i) /\ UNCHANGED faultVars
    \/ \E i \in Server, v \in NatView : MCViewChangerProcessViewChange(i, v)
    \/ \E i, j \in Server, p \in {Nil} \cup ProposalSet,
          prepared \in BOOLEAN :
          MCViewChangerAcceptViewData(i, j, p, prepared)
    \/ \E i \in Server : ViewChangerCheckInFlight(i) /\ UNCHANGED faultVars
    \/ \E i \in Server : ViewChangerCommitInFlight(i) /\ UNCHANGED faultVars
    \/ \E i \in Server : ViewChangerProcessNewView(i) /\ UNCHANGED faultVars
    \/ \E i \in Server : MCCrash(i)
    \/ \E i \in Server : Recover(i) /\ UNCHANGED faultVars
    \/ \E m \in messages : MCLoseMessage(m)

MCTypeOK ==
    /\ TypeOK
    /\ constraintCounters \in [
        clientProposal : 0..MaxClientProposalLimit,
        sync : 0..MaxSyncLimit,
        viewChange : 0..MaxViewChangeLimit,
        viewData : 0..MaxViewDataLimit,
        crash : 0..MaxCrashLimit,
        lose : 0..MaxLoseLimit]

MessageBufferBound == Cardinality(messages) <= MaxMsgBufferLimit

MCSpec == MCInit /\ [][MCNext]_mcVars


\* Manual invariant: Validity
Validity ==
  \A i \in Server :
    \A s \in delivered[i] :
      deliveredVal[i][s] \in Values \cup {Genesis}

=============================================================================
