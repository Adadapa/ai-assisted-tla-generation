---- MODULE MC ----
\* Model checking wrapper for SmartBFT base spec.
\* Adds counter-bounded fault-injection actions and symmetry reduction.
EXTENDS base, Integers

\* ─── Fault counters ───────────────────────────────────────────────────────────
\* One record to hold all fault-injection counters.
VARIABLE faultCounts

faultVars == <<faultCounts>>

\* ─── Counter bounds (tuned per hunting config via CONSTANTS override) ─────────
CONSTANTS
    MaxCrashes,          \* Crash/recovery cycles
    MaxByzMsgs,          \* Byzantine VIEW_DATA injections (Families 2,4)
    MaxVCDrops,          \* StartViewChange drops (Family 5)
    MaxViewChanges,      \* Total view-change rounds
    MaxInformDrops       \* InformNewView drops (Family 4)

\* ─── MCInit ───────────────────────────────────────────────────────────────────

MCInit ==
    /\ Init
    /\ faultCounts = [crashes      |-> 0,
                       byz_msgs    |-> 0,
                       vc_drops    |-> 0,
                       view_changes|-> 0,
                       inform_drops|-> 0]

\* ─── Bounded fault-injection wrappers ────────────────────────────────────────

\* Bounded crash: controller.go / viewchanger.go — volatile state reset on crash.
MCCrash(s) ==
    /\ faultCounts.crashes < MaxCrashes
    /\ Crash(s)
    /\ faultCounts' = [faultCounts EXCEPT !.crashes = @ + 1]

\* Bounded Byzantine VIEW_DATA injection: Family 2 fault.
\* Byzantine node sends ViewData with valid inner + invalid outer signature.
\* viewchanger.go:686-703 outer signature check.
MCByzantineViewData(byz, dest) ==
    /\ faultCounts.byz_msgs < MaxByzMsgs
    /\ ByzantineViewData(byz, dest)
    /\ faultCounts' = [faultCounts EXCEPT !.byz_msgs = @ + 1]

\* Bounded Byzantine VIEW_DATA to follower injection: Family 4 fault.
\* viewchanger.go:1081-1126 validateNewViewMsg seq+1 branch.
MCByzantineViewDataToFollower(byz, dest) ==
    /\ faultCounts.byz_msgs < MaxByzMsgs
    /\ ByzantineViewDataToFollower(byz, dest)
    /\ faultCounts' = [faultCounts EXCEPT !.byz_msgs = @ + 1]

\* Bounded StartViewChange drop: Family 5 fault.
\* viewchanger.go:356-371 capacity-2 startChangeChan.
MCMaybeStartViewChange(s) ==
    /\ MaybeStartViewChange(s)
    /\ IF vc_start_dropped'[s] THEN
           \* Only count actual drops against the bound
           /\ faultCounts.vc_drops < MaxVCDrops
           /\ faultCounts' = [faultCounts EXCEPT !.vc_drops = @ + 1]
       ELSE
           UNCHANGED faultCounts

\* Bounded InformNewView drop: Family 4 fault.
\* viewchanger.go:328-332 informChan buffer size 1.
MCInformNewView(s, newView) ==
    /\ InformNewView(s, newView)
    /\ IF vc_inform_dropped'[s] THEN
           /\ faultCounts.inform_drops < MaxInformDrops
           /\ faultCounts' = [faultCounts EXCEPT !.inform_drops = @ + 1]
       ELSE
           UNCHANGED faultCounts

\* Bounded view changes: prevents unbounded view-change churn.
MCHandleViewChange(s) ==
    /\ faultCounts.view_changes < MaxViewChanges
    /\ HandleViewChange(s)
    /\ faultCounts' = [faultCounts EXCEPT !.view_changes = @ + 1]

\* ─── Pass-through wrappers (deterministic/reactive actions — not bounded) ─────

MCPropose(s)                          == Propose(s)                          /\ UNCHANGED faultVars
MCHBLeaderTick(s)                     == HBLeaderTick(s)                     /\ UNCHANGED faultVars
MCHBFollowerTick(s)                   == HBFollowerTick(s)                   /\ UNCHANGED faultVars
MCInjectArtificialHeartbeat(s)        == InjectArtificialHeartbeat(s)        /\ UNCHANGED faultVars
MCHandleArtificialHeartbeat(s)        == HandleArtificialHeartbeat(s)        /\ UNCHANGED faultVars
MCHandleHeartbeat(s, from)            == HandleHeartbeat(s, from)            /\ UNCHANGED faultVars
MCOnHeartbeatTimeout(s)               == OnHeartbeatTimeout(s)               /\ UNCHANGED faultVars
MCHandlePrePrepare(s)                 == HandlePrePrepare(s)                 /\ UNCHANGED faultVars
MCHandlePrepare(s, from)              == HandlePrepare(s, from)              /\ UNCHANGED faultVars
MCDecide(s, from)                     == Decide(s, from)                     /\ UNCHANGED faultVars
MCProcessViewDataDeliver(s, from)     == ProcessViewDataDeliver(s, from)     /\ UNCHANGED faultVars
MCProcessViewDataValidate(s, from)    == ProcessViewDataValidate(s, from)    /\ UNCHANGED faultVars
MCProcessViewDataSameSeq(s, from)     == ProcessViewDataSameSeq(s, from)     /\ UNCHANGED faultVars
MCBuildNewView(s)                     == BuildNewView(s)                     /\ UNCHANGED faultVars
MCEnterNewView(s)                     == EnterNewView(s)                     /\ UNCHANGED faultVars
MCProcessNewViewDeliverLoop(s)        == ProcessNewViewDeliverLoop(s)        /\ UNCHANGED faultVars
MCChangeViewUpdateView(s)             == ChangeViewUpdateView(s)             /\ UNCHANGED faultVars
MCChangeViewUpdateDecisions(s, d)     == ChangeViewUpdateDecisions(s, d)     /\ UNCHANGED faultVars
MCReadLeaderID(s)                     == ReadLeaderID(s)                     /\ UNCHANGED faultVars
MCRecover(s)                          == Recover(s)                          /\ UNCHANGED faultVars
MCSendChangeRole(s)                   == SendChangeRole(s)                   /\ UNCHANGED faultVars
MCProcessChangeRole(s)                == ProcessChangeRole(s)                /\ UNCHANGED faultVars

\* ─── MCNext ───────────────────────────────────────────────────────────────────

MCNext ==
    \* Normal path
    \/ \E s \in Server           : MCPropose(s)
    \/ \E s \in Server           : MCHBLeaderTick(s)
    \/ \E s \in Server           : MCHBFollowerTick(s)
    \/ \E s \in Server           : MCInjectArtificialHeartbeat(s)
    \/ \E s \in Server           : MCHandleArtificialHeartbeat(s)
    \/ \E s, from \in Server     : MCHandleHeartbeat(s, from)
    \/ \E s \in Server           : MCOnHeartbeatTimeout(s)
    \/ \E s \in Server           : MCHandlePrePrepare(s)
    \/ \E s, from \in Server     : MCHandlePrepare(s, from)
    \/ \E s, from \in Server     : MCDecide(s, from)
    \* View change path
    \/ \E s \in Server           : MCMaybeStartViewChange(s)
    \/ \E s \in Server           : MCHandleViewChange(s)
    \/ \E s, from \in Server     : MCProcessViewDataDeliver(s, from)
    \/ \E s, from \in Server     : MCProcessViewDataValidate(s, from)
    \/ \E s, from \in Server     : MCProcessViewDataSameSeq(s, from)
    \/ \E s \in Server           : MCBuildNewView(s)
    \/ \E s \in Server           : MCEnterNewView(s)
    \/ \E s \in Server           : MCProcessNewViewDeliverLoop(s)
    \/ \E s \in Server : \E v \in 0..MaxView : MCInformNewView(s, v)
    \* Non-atomic update (Family 3)
    \/ \E s \in Server           : MCChangeViewUpdateView(s)
    \/ \E s \in Server : \E d \in 0..MaxSeq : MCChangeViewUpdateDecisions(s, d)
    \/ \E s \in Server           : MCReadLeaderID(s)
    \* HBM goroutine
    \/ \E s \in Server           : MCSendChangeRole(s)
    \/ \E s \in Server           : MCProcessChangeRole(s)
    \* Fault injection (bounded)
    \/ \E s \in Correct          : MCCrash(s)
    \/ \E s \in Correct          : MCRecover(s)
    \/ \E byz \in Byzantine, dest \in Server : MCByzantineViewData(byz, dest)
    \/ \E byz \in Byzantine, dest \in Server : MCByzantineViewDataToFollower(byz, dest)

MCSpec == MCInit /\ [][MCNext]_<<vars, faultVars>>

\* ─── Symmetry and view ────────────────────────────────────────────────────────

Symmetry == Permutations(Server)

\* Exclude fault counters from symmetry view (they are scalar, not per-server)
MCView == <<vars>>

\* ─── Message buffer constraint ────────────────────────────────────────────────

\* Bound total messages in flight to prune state space.
MsgBufConstraint == Cardinality(msgs) <= 12

\* ─── MCTypeOK ─────────────────────────────────────────────────────────────────

MCTypeOK ==
    /\ TypeOK
    /\ faultCounts \in [crashes: Nat, byz_msgs: Nat, vc_drops: Nat, view_changes: Nat, inform_drops: Nat]

====
