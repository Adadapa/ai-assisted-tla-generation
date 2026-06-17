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

EXTENDS Json, IOUtils, Sequences, FiniteSets, TLC, Integers
\* base
\* SmartBFT — PBFT-family BFT consensus with rotating leader
\* hyperledger-labs/SmartBFT, internal/bft/
\*
\* Category A: Distributed / Message-Passing, BFT overlay (n >= 3f+1)
\* Bug families modeled:
\*   F1 — Heartbeat Monitor State Isolation (timedOut, artificial HB drop)
\*   F2 — Deliver-Before-Validate (blind-fold Byzantine delivery)
\*   F3 — Non-Atomic View+DecisionsInView Update (two-lock window)
\*   F4 — View Change Processing Correctness (informChan drop, deliver-loop)
\*   F5 — In-Flight Proposal Lifecycle (stale committedDuringViewChange)

\* ─── Constants ───────────────────────────────────────────────────────────────

CONSTANTS
    Server,             \* All N nodes (use {1,2,3,4} in MC)
    F,                  \* Max Byzantine faults; N >= 3F+1
    Quorum,             \* ceil((N+F+1)/2); e.g. 3 for N=4
    Byzantine,          \* SUBSET Server — nodes allowed to deviate
    NodesList,          \* Ordered sequence of Server for getLeaderID
    DecisionsPerLeader, \* Decisions before leader rotation (0 = disabled)
    LeaderRotation,     \* BOOLEAN: leader rotation enabled
    MaxView,            \* Bound on view numbers for MC
    MaxSeq,             \* Bound on sequence numbers for MC
    NULL                \* Sentinel

Correct == Server \ Byzantine

\* Ordered node list for model checking — TLC cfg files cannot contain <<>> literals.
\* Use `NodesList <- MCNodesList` in all .cfg files.
MCNodesList == <<1, 2, 3, 4>>

ASSUME Byzantine \subseteq Server
ASSUME Cardinality(Byzantine) <= F
ASSUME NodesList \in Seq(Server)
ASSUME Len(NodesList) = Cardinality(Server)
ASSUME \A i,j \in 1..Len(NodesList) : i /= j => NodesList[i] /= NodesList[j]

\* ─── Type abbreviations ───────────────────────────────────────────────────────

Phase == {"NORMAL", "VC_STARTED", "ENTERING_NV", "CRASHED"}
HBMRole == {"LEADER", "FOLLOWER"}
MsgType == {"PREPREPARE", "PREPARE", "COMMIT",
            "HEARTBEAT", "HEARTBEAT_RESP",
            "VIEW_CHANGE", "VIEW_DATA", "NEW_VIEW",
            "COMPLAINT"}

\* ─── Variables ────────────────────────────────────────────────────────────────

VARIABLES
    \* ── Controller goroutine state (controller.go) ───────────────────────────
    ctrl_view,          \* [Server -> Nat]: currViewNumber           controller.go:122
    ctrl_decisions,     \* [Server -> Nat]: currDecisionsInView      controller.go:125
    ctrl_updating,      \* [Server -> BOOLEAN]: TRUE between ChangeViewUpdateView and
                        \*   ChangeViewUpdateDecisions (non-atomic two-lock window; Family 3)
    ctrl_view_pending,  \* [Server -> Nat]: new view# being installed (during ctrl_updating)
    phase,              \* [Server -> Phase]
    log,                \* [Server -> Seq(Nat)]: committed seq numbers (Len = committed count)
    prepare_votes,      \* [Server -> [Nat -> SUBSET Server]]: prepare vote sets per seq
    commit_votes,       \* [Server -> [Nat -> SUBSET Server]]: commit vote sets per seq
    in_flight,          \* [Server -> Nat ∪ {NULL}]: prepared in-flight proposal seq
    blacklist,          \* [Server -> SUBSET Server]: from checkpoint metadata

    \* ── ViewChanger goroutine state (viewchanger.go) ─────────────────────────
    vc_view,            \* [Server -> Nat]: currView               viewchanger.go:105
    vc_quorum,          \* [Server -> SUBSET Server]: valid ViewData senders (Family 2)
    committed_during_vc,\* [Server -> Nat ∪ {NULL}]: committedDuringViewChange
                        \*   viewchanger.go:109 — NEVER reset between view changes (Family 5 bug)
    vc_delivered_seq,   \* [Server -> Nat ∪ {NULL}]: seq delivered during VC (Family 2 tracking)
    vc_start_dropped,   \* [Server -> BOOLEAN]: last StartViewChange was dropped (Family 5)
    vc_inform_dropped,  \* [Server -> BOOLEAN]: InformNewView was dropped (buffer-1) (Family 4)
    vc_enter_seq,       \* [Server -> Nat ∪ {NULL}]: proposal seq from last new view entry

    \* ── HeartbeatMonitor goroutine (heartbeatmonitor.go) — INDEPENDENT ────────
    hbm_view,           \* [Server -> Nat]: hm.view                heartbeatmonitor.go:60
    hbm_timed_out,      \* [Server -> BOOLEAN]: hm.timedOut         heartbeatmonitor.go:69
                        \*   Cleared ONLY by handleCommand (ChangeRole). Bug: once set per view,
                        \*   no further timeouts fire until ChangeRole arrives.     Family 1
    hbm_role,           \* [Server -> HBMRole]: hm.follower
    hbm_chg_pend,       \* [Server -> BOOLEAN]: ChangeRole cmd in commandChan (not yet drained)
    hbm_artif_pending,  \* [Server -> BOOLEAN]: artificialHeartbeat capacity-1 channel occupied
                        \*   heartbeatmonitor.go:95 (capacity 1); drop on full channel  Family 1

    \* ── Network ──────────────────────────────────────────────────────────────
    msgs                \* Set of message records

\* Variable groups for UNCHANGED
controllerVars == <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                    phase, log, prepare_votes, commit_votes, in_flight, blacklist>>
vcVars         == <<vc_view, vc_quorum, committed_during_vc, vc_delivered_seq,
                    vc_start_dropped, vc_inform_dropped, vc_enter_seq>>
hbmVars        == <<hbm_view, hbm_timed_out, hbm_role, hbm_chg_pend, hbm_artif_pending>>
msgVars        == <<msgs>>
vars           == <<controllerVars, vcVars, hbmVars, msgVars>>

\* ─── Helper operators ─────────────────────────────────────────────────────────

N == Len(NodesList)

\* getLeaderID: util.go:72-99
GetLeaderID(view, decisions, bl) ==
    IF ~LeaderRotation THEN
        NodesList[(view % N) + 1]
    ELSE
        LET base == view + (decisions \div DecisionsPerLeader)
        IN CHOOSE node \in Server :
            /\ node \notin bl
            /\ \E i \in 0..(N-1) :
                /\ NodesList[((base + i) % N) + 1] = node
                /\ \A j \in 0..(i-1) : NodesList[((base + j) % N) + 1] \in bl

\* Leader as seen by a node's Controller (uses its own ctrl_view, ctrl_decisions, blacklist)
CtrlLeader(s) == GetLeaderID(ctrl_view[s], ctrl_decisions[s], blacklist[s])

\* Leader as seen by HBM (uses its own hbm_view; HBM always passes decisions=0: viewchanger.go:232)
HBMLeader(s) == GetLeaderID(hbm_view[s], 0, {})

\* Leader as seen by ViewChanger (uses vc_view, decisions=0: viewchanger.go:231-232)
VCLeader(s) == GetLeaderID(vc_view[s], 0, blacklist[s])

\* Current next-to-commit sequence at node s (0-based; Len(log[s]) = number committed)
CommittedSeq(s) == Len(log[s])

\* Whether a quorum of nodes is in NORMAL phase at a view (leader is "alive" for invariant checking)
LeaderAliveInView(v) ==
    \E leader \in Correct :
        /\ GetLeaderID(v, 0, {}) = leader
        /\ phase[leader] = "NORMAL"
        /\ ctrl_view[leader] = v

\* Message send/discard helpers
Send(m)    == msgs' = msgs \cup {m}
Discard(m) == msgs' = msgs \ {m}

\* Check whether a ViewData outer signature is valid (modeled as a field in the message)
\* Byzantine nodes may send VIEW_DATA with outer_valid = FALSE to trigger Family 2 bug
OuterSigValid(m) == m.outer_valid

\* ─── TypeOK ───────────────────────────────────────────────────────────────────

TypeOK ==
    /\ ctrl_view         \in [Server -> Nat]
    /\ ctrl_decisions    \in [Server -> Nat]
    /\ ctrl_updating     \in [Server -> BOOLEAN]
    /\ ctrl_view_pending \in [Server -> Nat]
    /\ phase             \in [Server -> Phase]
    /\ log               \in [Server -> Seq(Nat)]
    /\ in_flight         \in [Server -> Nat \cup {NULL}]
    /\ blacklist         \in [Server -> SUBSET Server]
    /\ vc_view           \in [Server -> Nat]
    /\ vc_quorum         \in [Server -> SUBSET Server]
    /\ committed_during_vc \in [Server -> Nat \cup {NULL}]
    /\ vc_delivered_seq  \in [Server -> Nat \cup {NULL}]
    /\ vc_start_dropped  \in [Server -> BOOLEAN]
    /\ vc_inform_dropped \in [Server -> BOOLEAN]
    /\ vc_enter_seq      \in [Server -> Nat \cup {NULL}]
    /\ hbm_view          \in [Server -> Nat]
    /\ hbm_timed_out     \in [Server -> BOOLEAN]
    /\ hbm_role          \in [Server -> HBMRole]
    /\ hbm_chg_pend      \in [Server -> BOOLEAN]
    /\ hbm_artif_pending \in [Server -> BOOLEAN]
    /\ \A m \in msgs : m.type \in MsgType

\* ─── Init ─────────────────────────────────────────────────────────────────────

Init ==
    /\ ctrl_view          = [s \in Server |-> 0]
    /\ ctrl_decisions     = [s \in Server |-> 0]
    /\ ctrl_updating      = [s \in Server |-> FALSE]
    /\ ctrl_view_pending  = [s \in Server |-> 0]
    /\ phase              = [s \in Server |-> "NORMAL"]
    /\ log                = [s \in Server |-> <<>>]
    /\ prepare_votes      = [s \in Server |-> [seq \in 0..MaxSeq |-> {}]]
    /\ commit_votes       = [s \in Server |-> [seq \in 0..MaxSeq |-> {}]]
    /\ in_flight          = [s \in Server |-> NULL]
    /\ blacklist          = [s \in Server |-> {}]
    /\ vc_view            = [s \in Server |-> 0]
    /\ vc_quorum          = [s \in Server |-> {}]
    /\ committed_during_vc = [s \in Server |-> NULL]
    /\ vc_delivered_seq   = [s \in Server |-> NULL]
    /\ vc_start_dropped   = [s \in Server |-> FALSE]
    /\ vc_inform_dropped  = [s \in Server |-> FALSE]
    /\ vc_enter_seq       = [s \in Server |-> NULL]
    /\ hbm_view           = [s \in Server |-> 0]
    /\ hbm_timed_out      = [s \in Server |-> FALSE]
    /\ hbm_role           = [s \in Server |-> IF GetLeaderID(0, 0, {}) = s THEN "LEADER" ELSE "FOLLOWER"]
    /\ hbm_chg_pend       = [s \in Server |-> FALSE]
    /\ hbm_artif_pending  = [s \in Server |-> FALSE]
    /\ msgs               = {}

\* ─── Normal-Path Actions ──────────────────────────────────────────────────────

\* Leader proposes the next request. controller.go:498-509 propose()
Propose(s) ==
    /\ s \in Correct
    /\ phase[s] = "NORMAL"
    /\ ~ctrl_updating[s]
    /\ CtrlLeader(s) = s                          \* I am the leader: controller.go:227-230
    /\ CommittedSeq(s) < MaxSeq                   \* bound for MC
    /\ LET seq == CommittedSeq(s) + 1
       IN
       /\ Send([type    |-> "PREPREPARE",
                view    |-> ctrl_view[s],
                seq     |-> seq,
                digest  |-> seq,
                sender  |-> s])
    /\ UNCHANGED <<controllerVars, vcVars, hbmVars>>

\* Follower receives PREPREPARE, stores in-flight, broadcasts PREPARE.
\* view.go HandleMessage/pre-prepare path. controller.go:331-341 ProcessMessages().
HandlePrePrepare(s) ==
    /\ s \in Correct
    /\ phase[s] = "NORMAL"
    /\ \E m \in msgs :
        /\ m.type = "PREPREPARE"
        /\ m.view = ctrl_view[s]                  \* view.go: check view matches
        /\ m.seq  = CommittedSeq(s) + 1           \* view.go: check seq is next
        /\ m.sender = CtrlLeader(s)               \* view.go: from current leader
        /\ in_flight[s] = NULL                    \* not already prepared
        /\ in_flight' = [in_flight EXCEPT ![s] = m.seq]
        /\ Send([type   |-> "PREPARE",
                 view   |-> m.view,
                 seq    |-> m.seq,
                 digest |-> m.digest,
                 sender |-> s])
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   phase, log, prepare_votes, commit_votes, blacklist,
                   vcVars, hbmVars>>

\* Node receives PREPARE, accumulates votes; when quorum, broadcasts COMMIT.
\* view.go prepare vote accumulation.
HandlePrepare(s, from) ==
    /\ s \in Correct
    /\ phase[s] = "NORMAL"
    /\ from /= s                                  \* view.go: don't self-count
    /\ \E m \in msgs :
        /\ m.type   = "PREPARE"
        /\ m.sender = from
        /\ m.view   = ctrl_view[s]
        /\ m.seq    = CommittedSeq(s) + 1
        /\ from \notin prepare_votes[s][m.seq]   \* not already counted
        /\ prepare_votes' = [prepare_votes EXCEPT ![s][m.seq] =
                                prepare_votes[s][m.seq] \cup {from}]
        /\ IF Cardinality(prepare_votes'[s][m.seq]) >= Quorum - 1 THEN
               \* Reached prepare quorum: store in-flight, broadcast COMMIT
               /\ in_flight' = [in_flight EXCEPT ![s] = m.seq]
               /\ Send([type   |-> "COMMIT",
                        view   |-> m.view,
                        seq    |-> m.seq,
                        digest |-> m.digest,
                        sender |-> s])
           ELSE
               /\ UNCHANGED <<in_flight, msgs>>
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   phase, log, commit_votes, blacklist, vcVars, hbmVars>>

\* Node receives COMMIT, accumulates votes; when quorum, decides (commits to log).
\* view.go commit vote accumulation. controller.go:551-595 decide().
Decide(s, from) ==
    /\ s \in Correct
    /\ phase[s] = "NORMAL"
    /\ \E m \in msgs :
        /\ m.type   = "COMMIT"
        /\ m.sender = from
        /\ m.view   = ctrl_view[s]
        /\ m.seq    = CommittedSeq(s) + 1
        /\ from \notin commit_votes[s][m.seq]
        /\ commit_votes' = [commit_votes EXCEPT ![s][m.seq] =
                                commit_votes[s][m.seq] \cup {from}]
        /\ IF Cardinality(commit_votes'[s][m.seq]) >= Quorum THEN
               \* Quorum of commits: deliver to application  controller.go:553
               /\ log'            = [log EXCEPT ![s] = Append(log[s], m.seq)]
               /\ in_flight'      = [in_flight EXCEPT ![s] = NULL]          \* clear after commit
               /\ ctrl_decisions' = [ctrl_decisions EXCEPT ![s] = ctrl_decisions[s] + 1]
               \* controller.go:585-590: check rotation
               /\ LET newDecisions == ctrl_decisions[s] + 1
                  IN IF GetLeaderID(ctrl_view[s], newDecisions - 1, blacklist[s]) /=
                        GetLeaderID(ctrl_view[s], newDecisions, blacklist[s]) THEN
                         \* Leader rotation triggered  controller.go:586-589
                         /\ phase' = [phase EXCEPT ![s] = "VC_STARTED"]
                     ELSE
                         /\ UNCHANGED phase
               /\ UNCHANGED <<ctrl_view, ctrl_updating, ctrl_view_pending, prepare_votes, blacklist>>
           ELSE
               /\ UNCHANGED <<log, in_flight, ctrl_decisions,
                               ctrl_view, ctrl_updating, ctrl_view_pending,
                               phase, prepare_votes, blacklist>>
    /\ UNCHANGED <<vcVars, hbmVars, msgs>>

\* ─── HeartbeatMonitor Actions (INDEPENDENT GOROUTINE) ────────────────────────
\*
\* The HBM runs in its own goroutine. Its state (hbm_view, hbm_timed_out, hbm_role)
\* is ONLY updated when the commandChan is drained (handleCommand). This means
\* hbm_view can lag ctrl_view; hbm_timed_out is cleared ONLY on ChangeRole.
\* heartbeatmonitor.go, all actions.

\* Leader sends heartbeat.  heartbeatmonitor.go:366-390 leaderTick()
HBLeaderTick(s) ==
    /\ s \in Correct
    /\ hbm_role[s] = "LEADER"
    /\ phase[s] /= "CRASHED"
    /\ Send([type   |-> "HEARTBEAT",
             view   |-> hbm_view[s],
             seq    |-> CommittedSeq(s),
             sender |-> s])
    /\ UNCHANGED <<controllerVars, vcVars, hbmVars>>

\* Follower tick: if timedOut is already set, short-circuits (suppression bug).
\* heartbeatmonitor.go:392-413 followerTick()
\* BUG (Family 1): line 393 — returns early when timedOut=true; no second complaint possible.
HBFollowerTick(s) ==
    /\ s \in Correct
    /\ hbm_role[s] = "FOLLOWER"
    /\ phase[s] /= "CRASHED"
    \* heartbeatmonitor.go:393-395: short-circuit when timedOut
    /\ ~hbm_timed_out[s]
    \* Heartbeat timeout expired: no heartbeat from leader in current view
    /\ ~\E m \in msgs : m.type = "HEARTBEAT" /\ m.sender = HBMLeader(s) /\ m.view = hbm_view[s]
    \* heartbeatmonitor.go:399-412: fire timeout, set timedOut
    /\ hbm_timed_out' = [hbm_timed_out EXCEPT ![s] = TRUE]
    \* Fires OnHeartbeatTimeout → Controller.Complain → StartViewChange
    /\ msgs' = msgs \cup {[type   |-> "COMPLAINT",
                           sender |-> s,
                           view   |-> hbm_view[s],
                           leader |-> HBMLeader(s)]}
    /\ UNCHANGED <<controllerVars, vcVars, hbm_view, hbm_role, hbm_chg_pend, hbm_artif_pending>>

\* Follower processes a real heartbeat from the leader.
\* heartbeatmonitor.go:217-257 handleHeartBeat()
HandleHeartbeat(s, from) ==
    /\ s \in Correct
    /\ hbm_role[s] = "FOLLOWER"
    /\ phase[s] /= "CRASHED"
    /\ \E m \in msgs :
        /\ m.type   = "HEARTBEAT"
        /\ m.sender = from
        \* heartbeatmonitor.go:218-221: if hb.View < hm.view, send response and return
        /\ m.view   = hbm_view[s]               \* only process matching-view heartbeats
        /\ from = HBMLeader(s)                  \* heartbeatmonitor.go:224-226: sender must be leader
        \* heartbeatmonitor.go:229-231: if hb.View > hm.view, sync (handled separately)
        \* Heartbeat resets the timeout window (lastHeartbeat = lastTick)
        \* Modeled: remove any stale COMPLAINT since leader is alive
        /\ msgs' = (msgs \ {m}) \cup
                   {[type |-> "HEARTBEAT_RESP", view |-> hbm_view[s], sender |-> s, dest |-> from]}
    /\ UNCHANGED <<controllerVars, vcVars, hbm_view, hbm_timed_out, hbm_role, hbm_chg_pend, hbm_artif_pending>>

\* InjectArtificialHeartbeat: capacity-1 channel with default drop.
\* Called by Controller when it receives a proposal message from the leader.
\* heartbeatmonitor.go:153-161 InjectArtificialHeartbeat()
\* BUG (Family 1): if channel is full, this heartbeat is silently dropped.
\* A proposal burst causes drops → HBM misses heartbeats → spurious timeout fires.
InjectArtificialHeartbeat(s) ==
    /\ s \in Correct
    /\ phase[s] = "NORMAL"
    \* Controller received a proposal from the leader, calls InjectArtificialHeartbeat
    \* controller.go:339-341: on receiving PrePrepare/Prepare/Commit from leader
    /\ \E m \in msgs :
        /\ m.type \in {"PREPREPARE", "PREPARE", "COMMIT"}
        /\ m.sender = CtrlLeader(s)
        /\ m.view = ctrl_view[s]
    /\ IF hbm_artif_pending[s] THEN  \* heartbeatmonitor.go:158-160: default branch — drop
           UNCHANGED <<hbm_artif_pending, msgs>>
       ELSE                          \* heartbeatmonitor.go:154-157: channel slot available
           /\ hbm_artif_pending' = [hbm_artif_pending EXCEPT ![s] = TRUE]
           /\ UNCHANGED msgs
    /\ UNCHANGED <<controllerVars, vcVars, hbm_view, hbm_timed_out, hbm_role, hbm_chg_pend>>

\* HBM goroutine drains the artificial heartbeat channel.
\* heartbeatmonitor.go:134-135 — case <-hm.artificialHeartbeat
HandleArtificialHeartbeat(s) ==
    /\ s \in Correct
    /\ hbm_artif_pending[s]                     \* channel has a message
    /\ hbm_artif_pending' = [hbm_artif_pending EXCEPT ![s] = FALSE]
    \* Processing the artificial HB resets lastHeartbeat: no timeout fires this tick
    \* Modeled as: if hbm_timed_out was going to fire next, it no longer fires
    \* (Timeout is only fired by HBFollowerTick which guards ~hbm_timed_out)
    /\ UNCHANGED <<controllerVars, vcVars, hbm_view, hbm_timed_out, hbm_role, hbm_chg_pend, msgs>>

\* Controller sends ChangeRole to HBM via commandChan.
\* Happens when Controller starts a new view: controller.go:403.
\* The ChangeRole command is queued; HBM will process it asynchronously (hbm_chg_pend).
SendChangeRole(s) ==
    /\ s \in Correct
    /\ ~hbm_chg_pend[s]                         \* commandChan is unbuffered (send blocks until HBM reads)
    /\ hbm_chg_pend' = [hbm_chg_pend EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<controllerVars, vcVars, hbm_view, hbm_timed_out, hbm_role, hbm_artif_pending, msgs>>

\* HBM goroutine drains the ChangeRole command from commandChan.
\* heartbeatmonitor.go:337-350 handleCommand()
\* KEY: this is the ONLY place hbm_timed_out is cleared.
ProcessChangeRole(s) ==
    /\ s \in Correct
    /\ hbm_chg_pend[s]
    \* heartbeatmonitor.go:343-349: update view, leaderID, role; clear timedOut
    \* hbm_role is derived from the current leader calculation
    /\ LET newView == ctrl_view[s]
           newLeader == CtrlLeader(s)
       IN
       /\ hbm_view'      = [hbm_view      EXCEPT ![s] = newView]
       /\ hbm_timed_out' = [hbm_timed_out EXCEPT ![s] = FALSE]   \* line 347: timedOut = false
       /\ hbm_role'      = [hbm_role      EXCEPT ![s] = IF s = newLeader THEN "LEADER" ELSE "FOLLOWER"]
       /\ hbm_chg_pend'  = [hbm_chg_pend  EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<controllerVars, vcVars, hbm_artif_pending, msgs>>

\* ─── View Change Actions ──────────────────────────────────────────────────────

\* OnHeartbeatTimeout: Controller receives complaint from HBM.
\* controller.go:310-327. Calls FailureDetector.Complain → StartViewChange.
OnHeartbeatTimeout(s) ==
    /\ s \in Correct
    /\ phase[s] = "NORMAL"
    /\ \E m \in msgs :
        /\ m.type   = "COMPLAINT"
        /\ m.sender = s
        /\ m.view   = ctrl_view[s]              \* controller.go:320-323: ignore stale-view complaints
        /\ m.leader = CtrlLeader(s)
        /\ Discard(m)
    /\ phase' = [phase EXCEPT ![s] = "VC_STARTED"]
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   log, prepare_votes, commit_votes, in_flight, blacklist, vcVars, hbmVars>>

\* MaybeStartViewChange: capacity-2 startChangeChan; 3rd+ concurrent call is DROPPED.
\* viewchanger.go:356-371 StartViewChange() — select { case ... ; default: }
\* BUG (Family 5): multiple concurrent triggers cause drops.
MaybeStartViewChange(s) ==
    /\ s \in Correct
    /\ phase[s] = "VC_STARTED"
    \* Non-deterministic: either the VC message enters the channel or is dropped
    /\ \/ \* Channel has room: view change proceeds
           /\ vc_start_dropped' = [vc_start_dropped EXCEPT ![s] = FALSE]
           /\ Send([type      |-> "VIEW_CHANGE",
                    next_view |-> vc_view[s] + 1,
                    sender    |-> s])
       \/ \* Channel full: drop silently (select { default: })
           /\ vc_start_dropped' = [vc_start_dropped EXCEPT ![s] = TRUE]
           /\ UNCHANGED msgs
    /\ UNCHANGED <<controllerVars, vc_view, vc_quorum, committed_during_vc, vc_delivered_seq,
                   vc_inform_dropped, vc_enter_seq, hbmVars>>

\* Accumulate VIEW_CHANGE messages. viewchanger.go:403-441.
HandleViewChange(s) ==
    /\ s \in Correct
    /\ \E m \in msgs :
        /\ m.type      = "VIEW_CHANGE"
        /\ m.next_view = vc_view[s] + 1
        /\ LET senders == {m2.sender : m2 \in {msg \in msgs :
                               msg.type = "VIEW_CHANGE" /\ msg.next_view = vc_view[s] + 1}}
           \* viewchanger.go:408: proceeds when len(viewChangeMsgs) >= quorum-1 = F+1.
           IN Cardinality(senders) >= F + 1
        \* Advance to next view, broadcast VIEW_DATA
        /\ vc_view'  = [vc_view EXCEPT ![s] = vc_view[s] + 1]
        /\ phase'    = [phase  EXCEPT ![s] = "ENTERING_NV"]
        /\ Send([type          |-> "VIEW_DATA",
                 view          |-> vc_view[s] + 1,
                 last_seq      |-> CommittedSeq(s),
                 in_flight_seq |-> in_flight[s],         \* getInFlight result
                 outer_valid   |-> TRUE,                 \* correct node: valid outer sig
                 sender        |-> s,
                 dest          |-> GetLeaderID(vc_view[s] + 1, 0, blacklist[s])])
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   log, prepare_votes, commit_votes, in_flight, blacklist,
                   vc_quorum, committed_during_vc, vc_delivered_seq, vc_start_dropped,
                   vc_inform_dropped, vc_enter_seq,
                   hbmVars>>

\* Byzantine node sends a crafted VIEW_DATA: valid inner decision but invalid outer sig.
\* viewchanger.go:640-705 checkLastDecision() bug: deliverDecision at 640, VerifySignature at 660.
\* The outer_valid=FALSE models an invalid SignedViewData.Signature.
\* Family 2 fault injection.
ByzantineViewData(byz, dest) ==
    /\ byz \in Byzantine
    /\ dest \in Correct
    /\ GetLeaderID(vc_view[dest], 0, blacklist[dest]) = dest   \* dest is new leader
    /\ phase[dest] = "ENTERING_NV"
    /\ CommittedSeq(dest) > 0                                  \* non-genesis case
    /\ Send([type          |-> "VIEW_DATA",
             view          |-> vc_view[dest],
             last_seq      |-> CommittedSeq(dest),
             in_flight_seq |-> NULL,
             outer_valid   |-> FALSE,                          \* invalid outer signature
             sender        |-> byz,
             dest          |-> dest])
    /\ UNCHANGED <<controllerVars, vcVars, hbmVars>>

\* Step 1 of VIEW_DATA processing: deliver the decision (if sender is one ahead).
\* viewchanger.go:633-665 checkLastDecision() — v.deliverDecision at line 661.
\* The delivery happens BEFORE outer signature verification (Family 2 bug).
ProcessViewDataDeliver(s, from) ==
    /\ s \in Correct
    /\ phase[s] = "ENTERING_NV"
    /\ GetLeaderID(vc_view[s], 0, blacklist[s]) = s    \* I am new leader
    /\ \E m \in msgs :
        /\ m.type  = "VIEW_DATA"
        /\ m.view  = vc_view[s]
        /\ m.dest  = s
        /\ m.sender = from
        /\ from \notin vc_quorum[s]              \* not already processed
        \* viewchanger.go:593-600: sender is one sequence ahead of us
        /\ m.last_seq = CommittedSeq(s) + 1
        \* viewchanger.go:661: v.deliverDecision — advances our sequence
        /\ log'              = [log EXCEPT ![s] = Append(log[s], m.last_seq)]
        /\ vc_delivered_seq' = [vc_delivered_seq EXCEPT ![s] = m.last_seq]  \* track Family 2
        \* viewchanger.go:678: committedDuringViewChange = md (NEVER reset between VCs)
        /\ committed_during_vc' = [committed_during_vc EXCEPT ![s] = m.last_seq]
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   phase, prepare_votes, commit_votes, in_flight, blacklist,
                   vc_view, vc_quorum, vc_start_dropped, vc_inform_dropped, vc_enter_seq,
                   hbmVars, msgs>>

\* Step 2 of VIEW_DATA processing: verify outer signature, count toward quorum.
\* viewchanger.go:686-703. If outer sig invalid, returns false — ViewData does NOT count.
\* BUG (Family 2): sequence was already advanced in step 1; now ViewData doesn't count toward quorum.
ProcessViewDataValidate(s, from) ==
    /\ s \in Correct
    /\ phase[s] = "ENTERING_NV"
    /\ GetLeaderID(vc_view[s], 0, blacklist[s]) = s
    /\ \E m \in msgs :
        /\ m.type   = "VIEW_DATA"
        /\ m.view   = vc_view[s]
        /\ m.dest   = s
        /\ m.sender = from
        /\ from \notin vc_quorum[s]
        \* Check outer signature: viewchanger.go:690-702
        /\ IF OuterSigValid(m) THEN
               \* Valid: count toward quorum
               vc_quorum' = [vc_quorum EXCEPT ![s] = vc_quorum[s] \cup {from}]
           ELSE
               \* Invalid outer sig: do NOT count. Sequence already advanced in step 1.
               \* viewchanger.go:700-702: return false, 0
               UNCHANGED vc_quorum
        /\ Discard(m)
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   phase, log, prepare_votes, commit_votes, in_flight, blacklist,
                   vc_view, committed_during_vc, vc_delivered_seq, vc_start_dropped,
                   vc_inform_dropped, vc_enter_seq, hbmVars>>

\* Same-sequence case: just validates and counts (no delivery needed).
\* viewchanger.go:602-631 checkLastDecision() same-seq branch
ProcessViewDataSameSeq(s, from) ==
    /\ s \in Correct
    /\ phase[s] = "ENTERING_NV"
    /\ GetLeaderID(vc_view[s], 0, blacklist[s]) = s
    /\ \E m \in msgs :
        /\ m.type    = "VIEW_DATA"
        /\ m.view    = vc_view[s]
        /\ m.dest    = s
        /\ m.sender  = from
        /\ from \notin vc_quorum[s]
        /\ m.last_seq = CommittedSeq(s)          \* same seq: no delivery
        /\ IF OuterSigValid(m) THEN
               vc_quorum' = [vc_quorum EXCEPT ![s] = vc_quorum[s] \cup {from}]
           ELSE
               UNCHANGED vc_quorum
        /\ Discard(m)
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   phase, log, prepare_votes, commit_votes, in_flight, blacklist,
                   vc_view, committed_during_vc, vc_delivered_seq, vc_start_dropped,
                   vc_inform_dropped, vc_enter_seq, hbmVars>>

\* New leader has Quorum valid VIEW_DATAs; builds and broadcasts NEW_VIEW.
\* viewchanger.go:787-825 processViewDataMsg()
BuildNewView(s) ==
    /\ s \in Correct
    /\ phase[s] = "ENTERING_NV"
    /\ GetLeaderID(vc_view[s], 0, blacklist[s]) = s
    /\ Cardinality(vc_quorum[s]) >= Quorum
    \* Determine in-flight proposal to include: the highest in-flight seq among ViewData senders
    /\ LET inFlightSeq ==
           IF \E sender \in vc_quorum[s] :
               \E m \in msgs : m.type = "VIEW_DATA" /\ m.sender = sender /\ m.in_flight_seq /= NULL
           THEN CHOOSE seq \in {m.in_flight_seq : m \in {msg \in msgs :
                    msg.type = "VIEW_DATA" /\ msg.in_flight_seq /= NULL /\ msg.sender \in vc_quorum[s]}} :
                    \A seq2 \in {m.in_flight_seq : m \in {msg \in msgs :
                        msg.type = "VIEW_DATA" /\ msg.in_flight_seq /= NULL /\ msg.sender \in vc_quorum[s]}} :
                        seq >= seq2
           ELSE NULL
       IN
       Send([type       |-> "NEW_VIEW",
             view       |-> vc_view[s],
             in_flight  |-> inFlightSeq,
             sender     |-> s])
    /\ phase' = [phase EXCEPT ![s] = "NORMAL"]
    /\ vc_quorum' = [vc_quorum EXCEPT ![s] = {}]
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   log, prepare_votes, commit_votes, in_flight, blacklist,
                   vc_view, committed_during_vc, vc_delivered_seq, vc_start_dropped,
                   vc_inform_dropped, vc_enter_seq, hbmVars>>

\* Non-leader follower receives NEW_VIEW; enters new view.
\* viewchanger.go:1150-1215 processNewViewMsg()
EnterNewView(s) ==
    /\ s \in Correct
    /\ phase[s] \in {"NORMAL", "VC_STARTED", "ENTERING_NV"}
    /\ \E m \in msgs :
        /\ m.type   = "NEW_VIEW"
        /\ m.view   = vc_view[s] + 1
        /\ m.sender = GetLeaderID(vc_view[s] + 1, 0, blacklist[s])   \* from correct new leader
        \* viewchanger.go:1081-1126: validateNewViewMsg same deliver-then-validate pattern
        \* In the follower path, if m.in_flight /= NULL, replay the in-flight proposal
        /\ vc_view'                = [vc_view                EXCEPT ![s] = m.view]
        /\ phase'                  = [phase                  EXCEPT ![s] = "NORMAL"]
        \* Replay in-flight proposal if present
        /\ in_flight' = [in_flight EXCEPT ![s] =
                            IF m.in_flight /= NULL THEN m.in_flight ELSE NULL]
        /\ vc_enter_seq' = [vc_enter_seq EXCEPT ![s] = CommittedSeq(s)]
        \* VC state reset (but NOT committedDuringViewChange — Family 5 bug)
        /\ vc_quorum'         = [vc_quorum         EXCEPT ![s] = {}]
        /\ vc_delivered_seq'  = [vc_delivered_seq  EXCEPT ![s] = NULL]
        /\ vc_start_dropped'  = [vc_start_dropped  EXCEPT ![s] = FALSE]
        \* Notify controller of new view (InformNewView → ViewChanged → changeView)
        \* Non-atomic update: step 1 (view number) — Family 3
        /\ ctrl_updating'      = [ctrl_updating      EXCEPT ![s] = TRUE]
        /\ ctrl_view_pending'  = [ctrl_view_pending  EXCEPT ![s] = m.view]
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, log, prepare_votes, commit_votes, blacklist,
                   committed_during_vc, vc_inform_dropped, hbmVars, msgs>>

\* ─── InformNewView with buffer-1 drop (Family 4) ────────────────────────────
\*
\* viewchanger.go:121-122 informChan: buffer size 1
\*   Two consecutive InformNewView calls drop the second.
\*   Called from controller.sync() at controller.go:715 and via informChan drain.
\*   BUG: if two concurrent syncs call InformNewView, the second is silently dropped.
\*   The dropped call may contain a higher view number that would have advanced
\*   the ViewChanger past a stale state.
\*
\* Modeled as: VCInformNewView sends a notification; then process picks it up (or drops).

\* InformNewView call with buffer-1 capacity constraint.
\* viewchanger.go:327-333 InformNewView()
InformNewView(s, newView) ==
    /\ s \in Correct
    /\ \/ \* Channel has room: notification accepted
           /\ vc_inform_dropped' = [vc_inform_dropped EXCEPT ![s] = FALSE]
           \* The notification updates vc_view (handled in processInformNewView)
           /\ IF newView > vc_view[s] THEN
                  vc_view' = [vc_view EXCEPT ![s] = newView]
              ELSE
                  UNCHANGED vc_view
       \/ \* Channel full (buffer=1): second call dropped  BUG (Family 4)
           /\ vc_inform_dropped' = [vc_inform_dropped EXCEPT ![s] = TRUE]
           /\ UNCHANGED vc_view
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   phase, log, prepare_votes, commit_votes, in_flight, blacklist,
                   vc_quorum, committed_during_vc, vc_delivered_seq, vc_start_dropped,
                   vc_enter_seq, hbmVars, msgs>>

\* ─── ProcessNewViewMsg deliver-loop (Family 4) ───────────────────────────────
\*
\* viewchanger.go:1150-1155: processNewViewMsg iterates calling validateNewViewMsg
\* with `for calledDeliver { ... valid, calledSync, calledDeliver = v.validateNewViewMsg(msg) }`.
\* Each iteration can deliver one more decision (if the new view contains multiple
\* ViewData messages with different last_seqs). But only the FIRST delivery has
\* its outer signature verified within the same iteration.
\*
\* Modeled as: EnterNewView may optionally fire multiple deliveries (one per
\* VIEW_DATA message in the NEW_VIEW bundle with a seq ahead of the follower).

\* Deliver-loop: follower delivers multiple decisions from a NEW_VIEW message.
\* viewchanger.go:1152-1155: for calledDeliver loop
ProcessNewViewDeliverLoop(s) ==
    /\ s \in Correct
    /\ phase[s] \in {"NORMAL", "VC_STARTED", "ENTERING_NV"}
    \* A NEW_VIEW message is in flight
    /\ \E m \in msgs :
        /\ m.type   = "NEW_VIEW"
        /\ m.view   = vc_view[s] + 1
        /\ m.sender = GetLeaderID(vc_view[s] + 1, 0, blacklist[s])
        \* Deliver the next in-flight proposal from the new view (one sequence ahead)
        /\ m.in_flight /= NULL
        /\ m.in_flight = CommittedSeq(s) + 1
        /\ in_flight[s] = NULL
        \* In the real code, validateNewViewMsg at viewchanger.go:1107 calls deliverDecision
        \* before verifying the outer signature at line 1115 — same deliver-before-validate pattern.
        \* For the follower deliver-loop, the first decision is delivered, then processing
        \* proceeds through additional loops.
        /\ log' = [log EXCEPT ![s] = Append(log[s], m.in_flight)]
        /\ in_flight' = [in_flight EXCEPT ![s] = m.in_flight]
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   phase, prepare_votes, commit_votes, blacklist,
                   vcVars, hbmVars, msgs>>

\* ─── View Change State Machine: ViewData From Byzantine (Family 4) ───────────
\*
\* Byzantine node sends VIEW_DATA to a non-leader follower during view change.
\* If the BYZANTINE destination is a CORRECT follower (not the new leader),
\* the ViewData message can advance the follower's state incorrectly before
\* the outer signature is verified.
\* viewchanger.go:1081-1126 validateNewViewMsg() seq+1 branch.

\* Byzantine sends VIEW_DATA directly to a correct follower (not the leader).
\* This bypasses the NEW_VIEW process and can advance the follower's sequence
\* without the full quorum check.
ByzantineViewDataToFollower(byz, dest) ==
    /\ byz \in Byzantine
    /\ dest \in Correct
    /\ GetLeaderID(vc_view[dest], 0, blacklist[dest]) /= dest   \* dest is NOT the new leader
    /\ phase[dest] = "NORMAL"
    /\ CommittedSeq(dest) > 0                                   \* non-genesis case
    /\ Send([type          |-> "VIEW_DATA",
             view          |-> vc_view[dest],
             last_seq      |-> CommittedSeq(dest) + 1,
             in_flight_seq |-> NULL,
             outer_valid   |-> FALSE,                           \* invalid signature
             sender        |-> byz,
             dest          |-> dest])
    /\ UNCHANGED <<controllerVars, vcVars, hbmVars>>

\* ─── Non-Atomic View+Decisions Update (Family 3) ─────────────────────────────
\*
\* controller.go:407-449 changeView():
\*   setCurrentViewNumber(newViewNumber)      line 427 — under currViewLock
\*   setCurrentDecisionsInView(newDecisions)  line 435 — under currDecisionsInViewLock
\* Between these two calls, concurrent ProcessMessages callers invoking leaderID()
\* see the new view with OLD decisions, computing a transiently wrong leader.

\* Step 1: update ctrl_view (under currViewLock).  controller.go:427
ChangeViewUpdateView(s) ==
    /\ s \in Correct
    /\ ctrl_updating[s]
    /\ ctrl_view' = [ctrl_view EXCEPT ![s] = ctrl_view_pending[s]]
    \* ctrl_decisions still has OLD value — window begins
    /\ UNCHANGED <<ctrl_decisions, ctrl_updating, ctrl_view_pending, phase, log,
                   prepare_votes, commit_votes, in_flight, blacklist, vcVars, hbmVars, msgs>>

\* Step 2: update ctrl_decisions (under currDecisionsInViewLock).  controller.go:435
ChangeViewUpdateDecisions(s, newDecisions) ==
    /\ s \in Correct
    /\ ctrl_updating[s]
    /\ ctrl_view[s] = ctrl_view_pending[s]   \* view was already updated in step 1
    /\ ctrl_decisions' = [ctrl_decisions EXCEPT ![s] = newDecisions]
    /\ ctrl_updating'  = [ctrl_updating  EXCEPT ![s] = FALSE]
    \* Start HBM ChangeRole (controller.go:403)
    /\ hbm_chg_pend' = [hbm_chg_pend EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<ctrl_view, ctrl_view_pending, phase, log, prepare_votes, commit_votes,
                   in_flight, blacklist, vcVars, hbm_view, hbm_timed_out, hbm_role, hbm_artif_pending, msgs>>

\* A correct node reads leaderID() during the non-atomic window.
\* controller.go:233-235: leaderID() reads both currViewNumber AND currDecisionsInView.
\* BUG (Family 3): if ctrl_updating[s]=TRUE, view was updated but decisions may be old.
\* This action doesn't change state; it records the observed leader for checking LeaderIdentityConsistency.
ReadLeaderID(s) ==
    /\ s \in Correct
    /\ ctrl_updating[s]                          \* in the non-atomic window
    \* The read observes ctrl_view[s] (new) + ctrl_decisions[s] (old) — transiently wrong leader
    /\ UNCHANGED vars                            \* read-only; invariant checked on current state

\* ─── getInFlight suppression (Family 5) ──────────────────────────────────────
\*
\* viewchanger.go:468-509 getInFlight():
\*   If inFlightMetadata.LatestSequence+1 == lastDecisionMetadata.LatestSequence
\*   AND committedDuringViewChange != nil
\*   AND committedDuringViewChange.LatestSequence == lastDecisionMetadata.LatestSequence
\* → return nil (suppress in-flight report)
\*
\* BUG: committedDuringViewChange is NEVER reset between view changes.
\* On a second view change, stale value can suppress a real in-flight proposal.

GetInFlightSeq(s) ==
    \* viewchanger.go:468-509 getInFlight()
    LET ifSeq == in_flight[s]
        lastSeq == CommittedSeq(s)
    IN
    IF ifSeq = NULL THEN NULL
    ELSE IF ifSeq = lastSeq THEN NULL   \* same seq as last decision: not an actual in-flight
    ELSE IF ifSeq + 1 = lastSeq /\ committed_during_vc[s] /= NULL
             /\ committed_during_vc[s] = lastSeq THEN
             \* Suppression: committed during this VC — return nil
             \* BUG: if committed_during_vc is STALE from previous VC, this fires incorrectly
             NULL
    ELSE ifSeq

\* ─── Crash and Recovery ───────────────────────────────────────────────────────

\* Crash resets all volatile (in-memory) state. controller.go, viewchanger.go.
\* Persisted state (log, checkpoint) survives; volatile state (votes, in-flight) is lost.
Crash(s) ==
    /\ s \in Correct
    /\ phase'              = [phase              EXCEPT ![s] = "CRASHED"]
    /\ prepare_votes'      = [prepare_votes      EXCEPT ![s] = [seq \in 0..MaxSeq |-> {}]]
    /\ commit_votes'       = [commit_votes       EXCEPT ![s] = [seq \in 0..MaxSeq |-> {}]]
    /\ in_flight'          = [in_flight          EXCEPT ![s] = NULL]
    /\ ctrl_updating'      = [ctrl_updating      EXCEPT ![s] = FALSE]
    /\ ctrl_view_pending'  = [ctrl_view_pending  EXCEPT ![s] = ctrl_view[s]]
    /\ vc_quorum'          = [vc_quorum          EXCEPT ![s] = {}]
    /\ vc_delivered_seq'   = [vc_delivered_seq   EXCEPT ![s] = NULL]
    /\ vc_start_dropped'   = [vc_start_dropped   EXCEPT ![s] = FALSE]
    /\ vc_inform_dropped'  = [vc_inform_dropped  EXCEPT ![s] = FALSE]
    /\ vc_enter_seq'       = [vc_enter_seq       EXCEPT ![s] = NULL]
    \* committedDuringViewChange: in-memory (viewchanger.go:109) — reset on crash
    /\ committed_during_vc' = [committed_during_vc EXCEPT ![s] = NULL]
    /\ hbm_timed_out'      = [hbm_timed_out      EXCEPT ![s] = FALSE]
    /\ hbm_chg_pend'       = [hbm_chg_pend       EXCEPT ![s] = FALSE]
    /\ hbm_artif_pending'  = [hbm_artif_pending  EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, log, blacklist, vc_view, hbm_view, hbm_role, msgs>>

\* Recovery: restore from checkpoint, re-enter consensus at recovered view+seq.
Recover(s) ==
    /\ phase[s] = "CRASHED"
    /\ phase' = [phase EXCEPT ![s] = "NORMAL"]
    \* Restore view and decisions from persisted state (WAL/checkpoint).
    \* In simplified model, ctrl_view and ctrl_decisions are already correct (they survived crash).
    /\ vc_view' = [vc_view EXCEPT ![s] = ctrl_view[s]]
    \* HBM reset on recovery
    /\ hbm_view' = [hbm_view EXCEPT ![s] = ctrl_view[s]]
    /\ hbm_role' = [hbm_role EXCEPT ![s] = IF CtrlLeader(s) = s THEN "LEADER" ELSE "FOLLOWER"]
    /\ UNCHANGED <<ctrl_view, ctrl_decisions, ctrl_updating, ctrl_view_pending,
                   log, prepare_votes, commit_votes, in_flight, blacklist,
                   vc_quorum, committed_during_vc, vc_delivered_seq, vc_start_dropped,
                   vc_inform_dropped, vc_enter_seq,
                   hbm_timed_out, hbm_chg_pend, hbm_artif_pending, msgs>>

\* ─── Next ─────────────────────────────────────────────────────────────────────

Next ==
    \/ \E s \in Server : Propose(s)
    \/ \E s \in Server : HBLeaderTick(s)
    \/ \E s \in Server : HBFollowerTick(s)
    \/ \E s \in Server : InjectArtificialHeartbeat(s)
    \/ \E s \in Server : HandleArtificialHeartbeat(s)
    \/ \E s, from \in Server : HandleHeartbeat(s, from)
    \/ \E s \in Server : OnHeartbeatTimeout(s)
    \/ \E s \in Server : MaybeStartViewChange(s)
    \/ \E s \in Server : HandleViewChange(s)
    \/ \E byz \in Byzantine, dest \in Server : ByzantineViewData(byz, dest)
    \/ \E byz \in Byzantine, dest \in Server : ByzantineViewDataToFollower(byz, dest)
    \/ \E s, from \in Server : ProcessViewDataDeliver(s, from)
    \/ \E s, from \in Server : ProcessViewDataValidate(s, from)
    \/ \E s, from \in Server : ProcessViewDataSameSeq(s, from)
    \/ \E s \in Server : BuildNewView(s)
    \/ \E s \in Server : EnterNewView(s)
    \/ \E s \in Server : ProcessNewViewDeliverLoop(s)
    \/ \E s \in Server : \E v \in 0..MaxView : InformNewView(s, v)
    \/ \E s \in Server : ChangeViewUpdateView(s)
    \/ \E s \in Server : \E d \in 0..MaxSeq : ChangeViewUpdateDecisions(s, d)
    \/ \E s \in Server : ReadLeaderID(s)
    \/ \E s, from \in Server : HandlePrePrepare(s)
    \/ \E s, from \in Server : HandlePrepare(s, from)
    \/ \E s, from \in Server : Decide(s, from)
    \/ \E s \in Server : Crash(s)
    \/ \E s \in Server : Recover(s)
    \/ \E s \in Server : SendChangeRole(s)
    \/ \E s \in Server : ProcessChangeRole(s)

Spec == Init /\ [][Next]_vars

\* ─── Invariants ───────────────────────────────────────────────────────────────

\* Min operator (not built-in in TLA+)
Min(a, b) == IF a <= b THEN a ELSE b

\* Standard BFT safety: no two correct nodes commit different proposals at the same seq.
\* In the simplified model, proposals = sequence numbers, so we check monotonic delivery.
Agreement ==
    \A s1, s2 \in Correct :
        \A i \in 1..Min(Len(log[s1]), Len(log[s2])) :
            log[s1][i] = log[s2][i]

\* ViewChangeSafety: committed proposals survive view changes.
\* If s committed seq K, the new view leader must include seq K in its state.
ViewChangeSafety ==
    \A s \in Correct :
        phase[s] = "NORMAL" =>
            Len(log[s]) = CommittedSeq(s)

\* NoViewFork (Family 4): no two correct nodes have divergent vc_view.
\* If two correct nodes are in the same view, they agree on the current view.
\* Allows transient gap where vc_view > ctrl_view during a view change
\* (InformNewView fires before the Controller processes update_view).
NoViewFork ==
    \A s1, s2 \in Correct :
        /\ ctrl_view[s1] = ctrl_view[s2]
        => \/ vc_view[s1] = vc_view[s2]
           \/ vc_view[s1] /= ctrl_view[s1]
           \/ vc_view[s2] /= ctrl_view[s2]

\* NoFalseTimeout (Family 1): HBM should not fire timedOut against a live leader.
\* A "live leader" is one in NORMAL phase, sending heartbeats in the current view.
\* Invariant: if hbm_timed_out[s] = TRUE, the leader in hbm_view[s] is not live.
NoFalseTimeout ==
    \A s \in Correct :
        hbm_timed_out[s] =>
            ~LeaderAliveInView(hbm_view[s])

\* DeliverImpliesViewEntered (Family 2): if a node delivered seq S during view-change processing,
\* the view change must eventually complete (vc_quorum reaches Quorum) or another VC starts.
\* Safety form: if vc_delivered_seq[s] /= NULL, the view cannot stall permanently.
\* Checked as: either view change completed (phase = NORMAL) or quorum was reached.
DeliverImpliesViewEntered ==
    \A s \in Correct :
        (vc_delivered_seq[s] /= NULL /\ phase[s] = "ENTERING_NV") =>
            Cardinality(vc_quorum[s]) >= Quorum

\* LeaderIdentityConsistency (Family 3): all correct nodes agree on leader for given (view, decisions).
\* During the non-atomic update window, a node sees new view + old decisions → wrong leader.
\* Invariant: no two correct nodes should simultaneously see different leaders for the same view.
LeaderIdentityConsistency ==
    \A s1, s2 \in Correct :
        (ctrl_view[s1] = ctrl_view[s2] /\ ctrl_decisions[s1] = ctrl_decisions[s2]) =>
            CtrlLeader(s1) = CtrlLeader(s2)

\* InFlightReplay (Family 5): if a correct node reported an in-flight proposal during VC,
\* the new view must either re-propose it or it was already committed by quorum.
\* Checked as: GetInFlightSeq should only return NULL when semantically correct.
InFlightReplay ==
    \A s \in Correct :
        in_flight[s] /= NULL =>
            \* Either seq is already committed (in log), or GetInFlight correctly reports it
            \/ in_flight[s] <= CommittedSeq(s)
            \/ GetInFlightSeq(s) /= NULL

\* InformViewNotDropped (Family 4): if a ViewChanger is informed of a new view,
\* the inform should not be silently dropped (buffer-1 channel).
\* Checked as: vc_inform_dropped[s] should not be TRUE when vc_view[s] is stale.
InformViewNotDropped ==
    \A s \in Correct :
        vc_inform_dropped[s] => vc_view[s] >= ctrl_view[s]

\* Structural invariant: committed sequence numbers are monotonically increasing.
LogMonotonic ==
    \A s \in Correct :
        \A i \in 1..Len(log[s]) : log[s][i] = i

\* Combined structural check.
StructuralInv ==
    /\ TypeOK
    /\ LogMonotonic




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
