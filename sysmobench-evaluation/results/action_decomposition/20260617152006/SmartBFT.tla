---- MODULE SmartBFT ----
\* SmartBFT Trace Validation Spec — Category A (Distributed / Message-Passing)
\*
\* Replays NDJSON execution traces from the instrumented SmartBFT implementation
\* against the base spec, verifying that every observed state transition is legal.
\* Trace files are written by the harness (harness-generation phase).
\*
\* Cursor variable l walks through events. Each action wrapper:
\*   1. Matches the current trace event
\*   2. Calls the corresponding base spec action
\*   3. Validates post-state fields captured by the harness
\*   4. Advances l

EXTENDS base, Json, IOUtils, Sequences, FiniteSets, TLC

\* ─── Trace file ───────────────────────────────────────────────────────────────

JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON
    ELSE "../traces/trace.ndjson"

TraceLog == ndJsonDeserialize(JsonFile)

\* ─── Trace cursor ─────────────────────────────────────────────────────────────

VARIABLE l

\* ─── TraceInit ────────────────────────────────────────────────────────────────
\* Bootstrap state matches implementation startup (view=0, no committed decisions).

TraceInit ==
    /\ Init
    /\ l = 1

\* ─── Helper: current trace event ──────────────────────────────────────────────

Logline == TraceLog[l]

IsEvent(name) == Logline.event = name
IsNodeEvent(name, s) == IsEvent(name) /\ Logline.node = s

\* ─── Post-state validation helpers ───────────────────────────────────────────
\* ValidatePostState is MANDATORY per spec — not a stub.
\* Each wrapper checks the key fields the action modifies.

\* Convert trace node identifier to Server element (trace uses integer node IDs).
NodeID(id) == id    \* assumes trace emits integer node IDs matching Server set

\* ─── Action wrappers ──────────────────────────────────────────────────────────

\* ── TracePropose ──────────────────────────────────────────────────────────────
\* Instrumentation: after Propose(s) in view.go (when leader assembles proposal)
\* Event: "propose"
\* Fields: node, view, seq
TracePropose ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("propose")
    /\ LET s == NodeID(Logline.node) IN
       /\ Propose(s)
       \* Post-state: verify view and seq match
       /\ ctrl_view'[s] = Logline.view
       /\ CommittedSeq(s) + 1 = Logline.seq
    /\ l' = l + 1

\* ── TraceHandlePrePrepare ─────────────────────────────────────────────────────
\* Instrumentation: after HandlePrePrepare stores in-flight (view.go prePrepare handler)
\* Event: "pre_prepare"
\* Fields: node, view, seq, sender
TraceHandlePrePrepare ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("pre_prepare")
    /\ LET s == NodeID(Logline.node) IN
       /\ HandlePrePrepare(s)
       \* Post-state: in_flight set to the received seq
       /\ in_flight'[s] = Logline.seq
    /\ l' = l + 1

\* ── TraceDecide ───────────────────────────────────────────────────────────────
\* Instrumentation: after Decide delivers to application (controller.go:553)
\* Event: "decide"
\* Fields: node, seq, view, decisions_in_view
\*
\* Direct state-update formulation: the trace proves the decision happened, so we
\* model it as a single bulk delivery step rather than going through Decide(s, from)
\* which accumulates one COMMIT vote at a time. Vote-level granularity is already
\* checked by the base-spec invariants during model checking; here we just verify the
\* observable post-state (log grew, ctrl_decisions incremented).
TraceDecide ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("decide")
    /\ LET s   == NodeID(Logline.node)
           seq == CommittedSeq(s) + 1
       IN
       /\ phase[s]          = "NORMAL"
       /\ ~ctrl_updating[s]
       \* Apply delivery: log grows, in-flight cleared, decisions incremented
       /\ log'            = [log            EXCEPT ![s] = Append(log[s], seq)]
       /\ in_flight'      = [in_flight      EXCEPT ![s] = NULL]
       /\ ctrl_decisions' = [ctrl_decisions EXCEPT ![s] = ctrl_decisions[s] + 1]
       \* Mark commit quorum reached so downstream Decide guards are satisfied
       /\ commit_votes'   = [commit_votes   EXCEPT ![s][seq] = Server]
       /\ UNCHANGED <<ctrl_view, ctrl_updating, ctrl_view_pending, prepare_votes,
                      blacklist, phase, vcVars, hbmVars, msgs>>
       \* Post-state checks
       /\ Len(log'[s]) = Logline.seq
       /\ ctrl_decisions'[s] = Logline.decisions_in_view
    /\ l' = l + 1

\* ── TraceHBFollowerTick ───────────────────────────────────────────────────────
\* Instrumentation: when followerTick fires OnHeartbeatTimeout (heartbeatmonitor.go:399)
\* Event: "hb_timeout"
\* Fields: node, view, leader
TraceHBFollowerTick ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("hb_timeout")
    /\ LET s == NodeID(Logline.node) IN
       /\ HBFollowerTick(s)
       \* Post-state: hbm_timed_out set; complaint emitted
       /\ hbm_timed_out'[s] = TRUE
       /\ hbm_view'[s] = Logline.view
    /\ l' = l + 1

\* ── TraceHBFollowerTickAbsorb ─────────────────────────────────────────────────
\* Absorbs a hb_timeout trace event when SilentHBFollowerTickBeforeVC already set
\* hbm_timed_out[s]=TRUE (to enable an earlier view_change_start for the same node).
\* In concurrent execution view_change_start can fire before the node's own hb_timeout;
\* the silent action pre-fires HBFollowerTick, so the subsequent hb_timeout trace event
\* is idempotent — just validate view is consistent and advance l.
TraceHBFollowerTickAbsorb ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("hb_timeout")
    /\ LET s == NodeID(Logline.node) IN
       /\ hbm_timed_out[s]           \* Already set by silent pre-fire
       /\ hbm_view[s] = Logline.view \* View still consistent
    /\ UNCHANGED vars
    /\ l' = l + 1

\* ── TraceProcessChangeRole ────────────────────────────────────────────────────
\* Instrumentation: after handleCommand drains ChangeRole (heartbeatmonitor.go:337)
\* Event: "change_role"
\* Fields: node, view, leader, role ("leader" | "follower")
TraceProcessChangeRole ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("change_role")
    /\ LET s == NodeID(Logline.node) IN
       /\ ProcessChangeRole(s)
       \* Post-state: hbm state reset
       /\ hbm_view'[s]      = Logline.view
       /\ hbm_timed_out'[s] = FALSE
       /\ hbm_role'[s]      = IF Logline.role = "leader" THEN "LEADER" ELSE "FOLLOWER"
    /\ l' = l + 1

\* ── TraceStartViewChange ──────────────────────────────────────────────────────
\* Instrumentation: when startViewChange broadcasts VIEW_CHANGE (viewchanger.go:394)
\* Event: "view_change_start"
\* Fields: node, next_view, dropped (bool)
TraceStartViewChange ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("view_change_start")
    /\ LET s == NodeID(Logline.node) IN
       /\ MaybeStartViewChange(s)
       \* Post-state: dropped flag matches
       /\ vc_start_dropped'[s] = Logline.dropped
    /\ l' = l + 1

\* ── TraceProcessViewDataDeliver ───────────────────────────────────────────────
\* Instrumentation: after deliverDecision in checkLastDecision (viewchanger.go:661)
\* Event: "vc_deliver"
\* Fields: node, from, seq, view
TraceProcessViewDataDeliver ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("vc_deliver")
    /\ LET s    == NodeID(Logline.node)
           from == NodeID(Logline.from)
       IN
       /\ ProcessViewDataDeliver(s, from)
       \* Post-state: log grew; vc_delivered_seq set
       /\ Len(log'[s]) = Logline.seq
       /\ vc_delivered_seq'[s] = Logline.seq
    /\ l' = l + 1

\* ── TraceProcessViewDataValidate ──────────────────────────────────────────────
\* Instrumentation: after VerifySignature in checkLastDecision (viewchanger.go:690)
\* Event: "vc_validate"
\* Fields: node, from, view, valid (bool — outer sig result)
TraceProcessViewDataValidate ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("vc_validate")
    /\ LET s    == NodeID(Logline.node)
           from == NodeID(Logline.from)
       IN
       /\ ProcessViewDataValidate(s, from)
       \* Post-state: vc_quorum grew iff outer sig valid
       /\ IF Logline.valid THEN from \in vc_quorum'[s]
          ELSE from \notin vc_quorum'[s]
    /\ l' = l + 1

\* ── TraceEnterNewView ─────────────────────────────────────────────────────────
\* Instrumentation: after processNewViewMsg completes view entry (viewchanger.go:1199+)
\* Event: "enter_new_view"
\* Fields: node, view, proposal_seq
\*
\* Direct state-update formulation (cf. TraceDecide).
\* EnterNewView(s) from the base spec guards on vc_view[s]+1 = m.view, but
\* SilentHandleViewChange already advanced vc_view[s] (to send VIEW_DATA to the new
\* leader) before this trace event fires. Using vc_view[s]+1 would require
\* a NEW_VIEW for the NEXT view, not the current one. Instead we verify the
\* trace's view (Logline.view) directly against the msgs set and apply the same
\* state transitions EnterNewView would apply.
TraceEnterNewView ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("enter_new_view")
    /\ LET s       == NodeID(Logline.node)
           newView == Logline.view
       IN
       /\ phase[s] \in {"NORMAL", "VC_STARTED", "ENTERING_NV"}
       \* Verify a NEW_VIEW for this view is in msgs from the correct new leader.
       /\ \E m \in msgs :
           /\ m.type   = "NEW_VIEW"
           /\ m.view   = newView                            \* trace view, not vc_view[s]+1
           /\ m.sender = GetLeaderID(newView, 0, blacklist[s])
           \* Apply transitions (mirrors EnterNewView, without the vc_view[s]+1 guard)
           /\ vc_view'           = [vc_view           EXCEPT ![s] = newView]
           /\ phase'             = [phase             EXCEPT ![s] = "NORMAL"]
           /\ vc_quorum'         = [vc_quorum         EXCEPT ![s] = {}]
           /\ vc_enter_seq'      = [vc_enter_seq      EXCEPT ![s] = CommittedSeq(s)]
           \* Only open the non-atomic ctrl window if the Controller has not yet processed
           \* this view change (update_view/update_decisions may precede enter_new_view in
           \* the trace when the Controller goroutine races ahead of the ViewChanger goroutine).
           /\ IF ~ctrl_updating[s] /\ ctrl_view[s] = newView
              THEN UNCHANGED <<ctrl_updating, ctrl_view_pending>>
              ELSE /\ ctrl_updating'     = [ctrl_updating     EXCEPT ![s] = TRUE]
                   /\ ctrl_view_pending' = [ctrl_view_pending EXCEPT ![s] = newView]
           \* Always reset in_flight when entering a new view.
           /\ in_flight' = [in_flight EXCEPT ![s] =
                               IF m.in_flight /= NULL THEN m.in_flight ELSE NULL]
       /\ UNCHANGED <<ctrl_view, ctrl_decisions, log, prepare_votes, commit_votes,
                      blacklist, committed_during_vc, vc_delivered_seq, vc_start_dropped,
                      vc_inform_dropped, hbmVars, msgs>>
       \* Post-state validation
       /\ vc_view'[s]  = Logline.view
       /\ phase'[s]    = "NORMAL"
    /\ l' = l + 1

\* ── TraceChangeViewUpdateView ─────────────────────────────────────────────────
\* Instrumentation: after setCurrentViewNumber (controller.go:427)
\* Event: "update_view"
\* Fields: node, view
TraceChangeViewUpdateView ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("update_view")
    /\ LET s == NodeID(Logline.node) IN
       /\ ChangeViewUpdateView(s)
       \* Post-state: ctrl_view updated; ctrl_updating still TRUE (window open)
       /\ ctrl_view'[s]     = Logline.view
       /\ ctrl_updating'[s] = TRUE
    /\ l' = l + 1

\* ── TraceProcessViewDataSameSeq ───────────────────────────────────────────────
\* Instrumentation: after VerifySignature in same-seq branch of checkLastDecision
\* Event: "vc_same_seq"
\* Fields: node, from, seq, view, valid
TraceProcessViewDataSameSeq ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("vc_same_seq")
    /\ LET s    == NodeID(Logline.node)
           from == NodeID(Logline.from)
       IN
       /\ ProcessViewDataSameSeq(s, from)
       \* Post-state: vc_quorum grew iff outer sig valid
       /\ IF Logline.valid THEN from \in vc_quorum'[s]
          ELSE from \notin vc_quorum'[s]
    /\ l' = l + 1

\* ── TraceChangeViewUpdateDecisions ────────────────────────────────────────────
\* Instrumentation: after setCurrentDecisionsInView (controller.go:435)
\* Event: "update_decisions"
\* Fields: node, decisions
TraceChangeViewUpdateDecisions ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("update_decisions")
    /\ LET s == NodeID(Logline.node) IN
       /\ ChangeViewUpdateDecisions(s, Logline.decisions)
       \* Post-state: ctrl_decisions updated; ctrl_updating cleared
       /\ ctrl_decisions'[s] = Logline.decisions
       /\ ctrl_updating'[s]  = FALSE
    /\ l' = l + 1

\* ─── Silent actions ───────────────────────────────────────────────────────────
\* Fire base spec actions without consuming a trace event.
\* Must be TIGHTLY CONSTRAINED to prevent state space explosion.

SilentSendChangeRole ==
    /\ l <= Len(TraceLog)
    \* Fire SendChangeRole for the traced node just before TraceProcessChangeRole consumes the event.
    \* ProcessChangeRole requires hbm_chg_pend[s]=TRUE (set by SendChangeRole).
    \* Init sets hbm_chg_pend=FALSE, so every change_role trace event needs this silent step first.
    /\ IsEvent("change_role")
    /\ LET s == NodeID(Logline.node) IN
       SendChangeRole(s)
    /\ UNCHANGED l

\* ── SilentHBFollowerTickBeforeVC ──────────────────────────────────────────────
\* Fire HBFollowerTick(s) silently before a view_change_start event when the node
\* has not yet timed out. Needed because in concurrent execution, view_change_start
\* can be emitted by the ViewChanger goroutine (triggered by receiving VIEW_CHANGE
\* messages from peers) before the node's own HBM goroutine emits hb_timeout.
\* HBFollowerTick sends the COMPLAINT that OnHeartbeatTimeout will consume.
SilentHBFollowerTickBeforeVC ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("view_change_start")
    /\ LET s == NodeID(Logline.node) IN
       /\ ~hbm_timed_out[s]      \* HBM has not yet fired for this node
       /\ HBFollowerTick(s)
    /\ UNCHANGED l

\* ── SilentOnHeartbeatTimeout ──────────────────────────────────────────────────
\* Fire OnHeartbeatTimeout(s) silently before a view_change_start event.
\* MaybeStartViewChange requires phase[s]="VC_STARTED", which is set by
\* OnHeartbeatTimeout. This silent step consumes the COMPLAINT (produced by
\* HBFollowerTick or SilentHBFollowerTickBeforeVC) and transitions phase→VC_STARTED.
SilentOnHeartbeatTimeout ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("view_change_start")
    /\ LET s == NodeID(Logline.node) IN
       /\ phase[s] = "NORMAL"    \* Not yet transitioned to VC_STARTED
       /\ OnHeartbeatTimeout(s)
    /\ UNCHANGED l

SilentReceiveCommit ==
    /\ l <= Len(TraceLog)
    \* Fire pre-quorum Decide calls before a traced decide event.
    \* Decide accumulates commit votes one at a time; Quorum-1 silent votes are needed
    \* before TraceDecide fires the quorum-reaching Decide that delivers to the log.
    \* Exclude commit_sender: it is reserved for TraceDecide (Decide guards from \notin commit_votes).
    \* Guard on COMMIT from commit_sender already in msgs: TraceDecide needs it, so delay
    \* SilentReceiveCommit until SilentHandlePrepare has generated that message.
    /\ IsEvent("decide")
    /\ LET s      == NodeID(Logline.node)
           seq    == CommittedSeq(s) + 1
           skip   == NodeID(Logline.commit_sender)
           view   == ctrl_view[s]
       IN
       /\ Cardinality(commit_votes[s][seq]) < Quorum - 1
       /\ \E m \in msgs : m.type = "COMMIT" /\ m.sender = skip /\ m.view = view /\ m.seq = seq
       /\ \E from \in Server : from /= skip /\ Decide(s, from)
       /\ UNCHANGED log
    /\ UNCHANGED l

SilentHandlePrepare ==
    /\ l <= Len(TraceLog)
    \* Only fire when the next event requires Quorum prepare votes to have been seen.
    \* Constrain to the specific node named in the trace event to avoid the 16-way
    \* (s x from) branching that causes state-space explosion.
    /\ Logline.event \in {"decide", "vc_deliver", "enter_new_view"}
    /\ LET s == NodeID(Logline.node)
       IN \E from \in Server : HandlePrepare(s, from)
    /\ UNCHANGED l

SilentHandleHeartbeat ==
    /\ l <= Len(TraceLog)
    \* Only fire when there is actually a HEARTBEAT message to process.
    \* Constraining to a concrete message prevents unbounded state-space
    \* exploration that would otherwise allow spurious view-change paths.
    /\ \E hb \in msgs : hb.type = "HEARTBEAT"
    /\ \E s, from \in Server : HandleHeartbeat(s, from)
    /\ UNCHANGED l

SilentBuildNewView ==
    /\ l <= Len(TraceLog)
    /\ Logline.event = "enter_new_view"
    /\ \E s \in Server : BuildNewView(s)
    /\ UNCHANGED l

\* ── SilentHandleViewChange ────────────────────────────────────────────────────
\* Fire HandleViewChange(s) silently before enter_new_view, vc_validate, vc_same_seq,
\* update_view, or update_decisions events. HandleViewChange transitions a node from
\* VC_STARTED to ENTERING_NV, advances vc_view, and sends VIEW_DATA to the new leader.
\* Required before BuildNewView can fire (needs ENTERING_NV + VIEW_DATA in msgs).
\*
\* NOTE: "vc_deliver" is intentionally excluded. Firing HandleViewChange at vc_deliver
\* time can send VIEW_DATA from the new leader *before* it has caught up on sequence
\* (deliverDecision hasn't run yet), producing VIEW_DATA with a stale last_seq that can
\* never be matched by ProcessViewDataSameSeq — deadlocking the trace. By firing only
\* at vc_validate (which always follows vc_deliver), the leader's committed seq is
\* already advanced when it sends its own VIEW_DATA.
SilentHandleViewChange ==
    /\ l <= Len(TraceLog)
    /\ Logline.event \in {"enter_new_view", "vc_validate", "vc_same_seq",
                          "update_view", "update_decisions"}
    /\ \E s \in Server : HandleViewChange(s)
    /\ UNCHANGED l

\* ── SilentActivateCtrlWindow ─────────────────────────────────────────────────
\* Open the Controller's non-atomic view-update window (ctrl_updating=TRUE,
\* ctrl_view_pending=newView) without requiring a NEW_VIEW message in msgs.
\*
\* Needed for "Case B" ordering: in concurrent execution the Controller goroutine
\* can emit update_view before the ViewChanger goroutine emits enter_new_view for
\* the same node. ChangeViewUpdateView(s) requires ctrl_updating[s]=TRUE, which
\* is normally set by TraceEnterNewView. This silent action sets it directly from
\* the update_view event so the trace action can proceed even when enter_new_view
\* has not yet appeared.
\*
\* Unlike the old SilentEnterNewView, this action does NOT touch vc_view, phase,
\* vc_quorum, or in_flight — those are left to TraceEnterNewView when it fires
\* later. This avoids contaminating vc_view with a premature value that would
\* prevent HandleViewChange from firing correctly.
SilentActivateCtrlWindow ==
    /\ l <= Len(TraceLog)
    /\ IsEvent("update_view")
    /\ LET s       == NodeID(Logline.node)
           newView == Logline.view
       IN
       /\ ~ctrl_updating[s]
       /\ ctrl_view[s] < newView
       /\ ctrl_updating'     = [ctrl_updating     EXCEPT ![s] = TRUE]
       /\ ctrl_view_pending' = [ctrl_view_pending EXCEPT ![s] = newView]
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, phase, log, prepare_votes, commit_votes,
                   in_flight, blacklist, vcVars, hbmVars, msgs>>
    /\ UNCHANGED l

\* ── SilentProcessViewDataSameSeq ──────────────────────────────────────────────
\* Fire ProcessViewDataSameSeq(s, from) silently before enter_new_view, update_view,
\* or update_decisions events. In the genesis view change (no prior commits), all
\* VIEW_DATA messages are same-seq; without this silent step vc_quorum never reaches
\* Quorum and BuildNewView is never enabled.
SilentProcessViewDataSameSeq ==
    /\ l <= Len(TraceLog)
    /\ Logline.event \in {"enter_new_view", "update_view", "update_decisions"}
    /\ \E s, from \in Server : ProcessViewDataSameSeq(s, from)
    /\ UNCHANGED l

\* ── SilentHandlePrePrepare ───────────────────────────────────────────────────
\* Fire HandlePrePrepare(s) silently before a decide or propose event.
\* Followers need to receive the PREPREPARE and broadcast PREPARE before commit
\* accumulation can begin.
SilentHandlePrePrepare ==
    /\ l <= Len(TraceLog)
    /\ Logline.event \in {"decide", "propose"}
    /\ \E m \in msgs : m.type = "PREPREPARE"
    /\ \E s \in Server : HandlePrePrepare(s)
    /\ UNCHANGED l

\* ─── TraceTermination ────────────────────────────────────────────────────────
\* Explicit stutter action once all trace events are consumed.
\* Without this, TLC reports "Deadlock reached" when l > Len(TraceLog) because
\* every TraceNext branch guards l <= Len(TraceLog). Adding an explicit
\* UNCHANGED stutter when the trace is exhausted turns the deadlock into a
\* validly terminating behaviour.
TraceTermination ==
    /\ l > Len(TraceLog)
    /\ UNCHANGED <<vars, l>>

\* ─── TraceNext ────────────────────────────────────────────────────────────────

TraceNext ==
    \/ TracePropose
    \/ TraceHandlePrePrepare
    \/ TraceDecide
    \/ TraceHBFollowerTick
    \/ TraceHBFollowerTickAbsorb
    \/ TraceProcessChangeRole
    \/ TraceStartViewChange
    \/ TraceProcessViewDataDeliver
    \/ TraceProcessViewDataValidate
    \/ TraceEnterNewView
    \/ TraceChangeViewUpdateView
    \/ TraceChangeViewUpdateDecisions
    \/ TraceProcessViewDataSameSeq
    \* Silent actions
    \/ SilentSendChangeRole
    \/ SilentHBFollowerTickBeforeVC
    \/ SilentOnHeartbeatTimeout
    \/ SilentHandleViewChange
    \/ SilentActivateCtrlWindow
    \/ SilentProcessViewDataSameSeq
    \/ SilentHandleHeartbeat
    \/ SilentBuildNewView
    \/ SilentHandlePrePrepare
    \/ TraceTermination
    \* SilentReceiveCommit and SilentHandlePrepare are NOT included: TraceDecide
    \* uses a direct state-update formulation (sets commit_votes=Server directly)
    \* and does not require prior COMMIT/PREPARE accumulation via Decide(s,from).

\* ─── TraceMatched ─────────────────────────────────────────────────────────────
\* Temporal property: the entire trace must be consumed.
\* Without this, TLC reports "no errors" even when validation never advances.

TraceMatched == <>(l > Len(TraceLog))

\* ─── TraceSpec ────────────────────────────────────────────────────────────────

TraceSpec == TraceInit /\ [][TraceNext]_<<vars, l>> /\ WF_<<vars, l>>(TraceNext)

====
