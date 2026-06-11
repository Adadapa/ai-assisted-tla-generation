# SmartBFT Instrumentation Spec

This document maps SmartBFT implementation points to `Trace.tla` events. Emit one JSON object per event to `traces/smartbft.ndjson`.

## 1. Trace Event Schema

Common event envelope:

```json
{
  "event": "controller_decide",
  "node": "s1",
  "sender": "s2",
  "value": "v1",
  "state": {
    "view": 0,
    "proposal_seq": 2,
    "decisions_in_view": 1,
    "checkpoint_seq": 1,
    "phase": "PhaseCommitted",
    "delivered": [1],
    "wal_len": 2,
    "sync_lock_holder": "Nil",
    "crashed": false,
    "viewdata_count": 0
  }
}
```

State fields captured at every event:

| Field | Implementation source | TLA variable |
|-------|-----------------------|--------------|
| `node` | consensus/controller node ID | server index |
| `view` | `Controller.getCurrentViewNumber()` / `ViewChanger.currView` | `viewNum[node]` |
| `proposal_seq` | `ViewSequences.ProposalSeq`, `View.ProposalSequence`, or metadata sequence | `proposalSeq[node]` |
| `decisions_in_view` | `Controller.getCurrentDecisionsInView()` or `View.DecisionsInView` | `decisionsInView[node]` |
| `checkpoint_seq` | decoded checkpoint `ViewMetadata.LatestSequence` | `checkpointSeq[node]` |
| `phase` | current `View.Phase` or restored phase | `phase[node]` |
| `delivered` | application test hook / shadow set of delivered sequences | `delivered[node]` |
| `wal_len` | WAL append counter / `PersistedState.Entries` length | `Len(wal[node])` |
| `sync_lock_holder` | tracer shadow around `syncLock.Lock/Unlock` | `syncLockHolder` |
| `crashed` | harness lifecycle state | `crashed[node]` |
| `viewdata_count` | `len(ViewChanger.viewDataMsgs.voted)` or tracer shadow | `Cardinality(viewData[node])` |

Message/proposal fields:

| Field | Meaning |
|-------|---------|
| `value` | abstract proposal value, mapped from proposal digest/payload to `v1`, `v2`, etc. |
| `sender` | sender node ID for received view-data/message events |
| `sync_view`, `sync_seq`, `sync_decisions`, `sync_value` | result returned by `Synchronizer.Sync()` |
| `prepared` | `ViewData.InFlightPrepared` |
| `has_inflight` | whether `ViewData.InFlightProposal != nil` |
| `proposal_valid` | result of app-level verifier predicate for abstract trace |

## 2. Action-to-Code Mapping

### `ControllerStartView`

- Code location: `SmartBFT/internal/bft/controller.go:384`
- Trigger point: after `c.startView(newProposalSequence)` assigns `currView` and calls `Start()`.
- Trace event: `controller_start_view`
- Fields: common state fields.
- Notes: Capture post-state after `LeaderMonitor.ChangeRole`, since the spec validates `leader` and view counters after start.

### `ViewPropose`

- Code location: `SmartBFT/internal/bft/view.go:951`
- Trigger point: after `v.HandleMessage(v.LeaderID, msg)` returns.
- Trace event: `view_propose`
- Fields: `value`, common state fields.
- Notes: The event represents the self pre-prepare injection, not the later network broadcast.

### `ViewProcessPrePrepare`

- Code location: `SmartBFT/internal/bft/view.go:387`
- Trigger point: after `v.State.Save(savedMsg)` succeeds and before/after `lastBroadcastSent` is set.
- Trace event: `view_process_preprepare`
- Fields: `value`, `wal_len`, `phase`, common state fields.
- Notes: Do not emit if `verifyProposal` returned an error; rejected proposals are outside this base action.

### `ViewProcessPrepares`

- Code location: `SmartBFT/internal/bft/view.go:501`
- Trigger point: after `v.State.Save(preparedProof)` succeeds.
- Trace event: `view_process_prepares`
- Fields: `wal_len`, `phase`, common state fields.
- Notes: Captures the transition to prepared after quorum prepares.

### `ControllerDecide`

- Code location: `SmartBFT/internal/bft/controller.go:537`
- Trigger point: after `c.Deliver.Deliver(...)`, request removal, and `incrementCurrentDecisionsInView()`.
- Trace event: `controller_decide`
- Fields: `delivered`, `checkpoint_seq`, `decisions_in_view`, `proposal_seq`, common state fields.
- Notes: The trace state should include the post-delivery checkpoint sequence.

### `ControllerChangeView`

- Code location: `SmartBFT/internal/bft/controller.go:407`
- Trigger point: after `c.changeView(...)` returns.
- Trace event: `controller_change_view`
- Fields: `view`, `proposal_seq`, `decisions_in_view`, common state fields.
- Notes: Emit for both view-change and sync-driven restart paths.

### `ControllerSyncBegin`

- Code location: `SmartBFT/internal/bft/controller.go:593`
- Trigger point: immediately after `c.syncLock.Lock()`.
- Trace event: `controller_sync_begin`
- Fields: `sync_view`, `sync_seq`, `sync_decisions`, `sync_value`, `sync_lock_holder`.
- Notes: If tracing cannot observe the lock directly, maintain a tracer shadow value around the lock/unlock calls.

### `ControllerSyncApply`

- Code location: `SmartBFT/internal/bft/controller.go:596`
- Trigger point: just before returning from `sync()`, after checkpoint/view/in-flight updates and before `syncLock.Unlock()` defer runs, or immediately after unlock with `sync_lock_holder = Nil`.
- Trace event: `controller_sync_apply`
- Fields: `view`, `proposal_seq`, `decisions_in_view`, `checkpoint_seq`, `sync_lock_holder`.
- Notes: This is the primary event for Family 2 same-height sync validation.

### `MutuallyExclusiveDeliver`

- Code location: `SmartBFT/internal/bft/controller.go:944`
- Trigger point: after `MutuallyExclusiveDeliver.Deliver` returns.
- Trace event: `mutually_exclusive_deliver`
- Fields: `delivered`, `checkpoint_seq`, common state fields.
- Notes: This path may not deliver if checkpoint already passed the pending proposal.

### `ViewChangerProcessViewChange`

- Code location: `SmartBFT/internal/bft/viewchanger.go:393`
- Trigger point: after `v.State.Save(msgToSave)` and after `v.currView = v.nextView`.
- Trace event: `viewchanger_process_viewchange`
- Fields: `view`, `wal_len`, `phase`, common state fields.
- Notes: Emit only when the function actually sends/prepares view data.

### `ViewChangerAcceptViewData`

- Code location: `SmartBFT/internal/bft/viewchanger.go:501`
- Trigger point: after `v.viewDataMsgs.registerVote(sender, m)`.
- Trace event: `viewchanger_accept_viewdata`
- Fields: `sender`, `prepared`, `has_inflight`, `proposal_valid`, `value`, `viewdata_count`.
- Notes: Emit only for validated view-data messages.

### `ViewChangerCheckInFlight`

- Code location: `SmartBFT/internal/bft/viewchanger.go:747`
- Trigger point: after `CheckInFlight(...)` returns `ok`.
- Trace event: `viewchanger_check_inflight`
- Fields: `selected_inflight_seq`, `viewdata_count`.
- Notes: If no in-flight proposal is selected, do not emit this action; emit `viewchanger_process_newview` instead.

### `ViewChangerCommitInFlight`

- Code location: `SmartBFT/internal/bft/viewchanger.go:1186`
- Trigger point: after the temporary in-flight view reaches `PREPARED` setup or after it reports commit success.
- Trace event: `viewchanger_commit_inflight`
- Fields: `phase`, `proposal_seq`, `checkpoint_seq`, common state fields.
- Notes: This is a key Family 4 trace point. Capture proposal digest/value and sequence.

### `ViewChangerProcessNewView`

- Code location: `SmartBFT/internal/bft/viewchanger.go:1110`
- Trigger point: after `v.State.Save(newViewToSave)` and `v.Controller.ViewChanged(...)`.
- Trace event: `viewchanger_process_newview`
- Fields: `view`, `proposal_seq`, `decisions_in_view`, `wal_len`, common state fields.
- Notes: This event resets `decisions_in_view` to 0 in the abstraction.

### `Crash`

- Code location: harness lifecycle around process/node stop; WAL code in `SmartBFT/internal/bft/state.go:38`.
- Trigger point: immediately after the node is stopped or crash is injected.
- Trace event: `crash`
- Fields: `crashed`, `wal_len`, common state fields.
- Notes: This event is harness-level; SmartBFT does not expose a crash function.

### `Recover`

- Code location: `SmartBFT/internal/bft/state.go:115`, `SmartBFT/pkg/consensus/consensus.go:460`
- Trigger point: after `PersistedState.Restore` and `Consensus.setViewAndSeq` complete.
- Trace event: `recover`
- Fields: `crashed`, `view`, `proposal_seq`, `decisions_in_view`, `phase`, `wal_len`.
- Notes: Capture the restored phase and proposal sequence before the node processes new network messages.

## 3. Special Considerations

- SmartBFT uses goroutines for controller, view, view-changer, heartbeat monitor, request-pool timers, and async commit signature verification. Use a single linear trace ordered by emission time for Category A validation; keep events at the action boundaries listed above.
- Some state is not directly exported. Add tracing helper methods under build tags or test-only wrappers to decode checkpoint metadata and inspect `ViewSequences`.
- Do not trace rejected proposal/view-data messages as successful actions. Rejected paths need separate negative tests, not base action traces.
- Proposal values should be abstracted by digest: first unique digest maps to `v1`, second to `v2`, and so on within the trace.
- The trace spec uses `IOEnv.JSON` to override the trace path. Default path is `../traces/smartbft.ndjson`.
