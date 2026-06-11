------------------------------ MODULE MC ------------------------------
(*
 * Model-checking wrapper for SmartBFT base.tla.
 * Fault-introducing actions are counter-bounded; deterministic/reactive
 * handlers delegate to the base spec without counters.
 *)

EXTENDS base

B == INSTANCE base

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
    /\ B!ViewPropose(i, val)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.clientProposal = @ + 1]

MCControllerSyncBegin(i) ==
    /\ constraintCounters.sync < MaxSyncLimit
    /\ B!ControllerSyncBegin(i)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.sync = @ + 1]

MCViewChangerProcessViewChange(i, newView) ==
    /\ constraintCounters.viewChange < MaxViewChangeLimit
    /\ B!ViewChangerProcessViewChange(i, newView)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.viewChange = @ + 1]

MCViewChangerAcceptViewData(i, sender, prop, prepared) ==
    /\ constraintCounters.viewData < MaxViewDataLimit
    /\ B!ViewChangerAcceptViewData(i, sender, prop, prepared)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.viewData = @ + 1]

MCCrash(i) ==
    /\ constraintCounters.crash < MaxCrashLimit
    /\ B!Crash(i)
    /\ constraintCounters' =
        [constraintCounters EXCEPT !.crash = @ + 1]

MCLoseMessage(m) ==
    /\ constraintCounters.lose < MaxLoseLimit
    /\ B!LoseMessage(m)
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
          B!ControllerStartView(i, v) /\ UNCHANGED faultVars
    \/ \E i \in Server, val \in Values : MCViewPropose(i, val)
    \/ \E i \in Server, m \in messages :
          B!ViewProcessPrePrepare(i, m) /\ UNCHANGED faultVars
    \/ \E i \in Server : B!ViewProcessPrepares(i) /\ UNCHANGED faultVars
    \/ \E i \in Server : B!ControllerDecide(i) /\ UNCHANGED faultVars
    \/ \E i \in Server, v \in NatView, s \in 1..MaxSeq, d \in 0..MaxSeq :
          B!ControllerChangeView(i, v, s, d) /\ UNCHANGED faultVars
    \/ \E i \in Server : MCControllerSyncBegin(i)
    \/ \E i \in Server, r \in [view : NatView, seq : NatSeq,
                               decisions : 0..MaxSeq, value : ValueOrNil] :
          B!ControllerSyncApply(i, r) /\ UNCHANGED faultVars
    \/ \E i \in Server : B!MutuallyExclusiveDeliver(i) /\ UNCHANGED faultVars
    \/ \E i \in Server, v \in NatView : MCViewChangerProcessViewChange(i, v)
    \/ \E i, j \in Server, p \in {Nil} \cup ProposalSet,
          prepared \in BOOLEAN :
          MCViewChangerAcceptViewData(i, j, p, prepared)
    \/ \E i \in Server : B!ViewChangerCheckInFlight(i) /\ UNCHANGED faultVars
    \/ \E i \in Server : B!ViewChangerCommitInFlight(i) /\ UNCHANGED faultVars
    \/ \E i \in Server : B!ViewChangerProcessNewView(i) /\ UNCHANGED faultVars
    \/ \E i \in Server : MCCrash(i)
    \/ \E i \in Server : B!Recover(i) /\ UNCHANGED faultVars
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

=============================================================================
