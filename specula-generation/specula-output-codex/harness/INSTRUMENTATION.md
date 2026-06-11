# SmartBFT Trace Harness

This harness instruments the real SmartBFT Go code to emit NDJSON traces for `.specula-output/spec/Trace.tla`.

## Files

| Path | Purpose |
|------|---------|
| `harness/src/tla_trace.go` | Go trace emission module copied to `SmartBFT/internal/bft/tla_trace.go` |
| `harness/patches/instrumentation.patch` | Patch adding emit calls to SmartBFT source |
| `harness/apply.sh` | Copies trace module and applies the patch |
| `harness/run.sh` | Applies instrumentation and runs selected Go tests with tracing enabled |
| `traces/*.ndjson` | Output traces |

## Trace Format

Each event is one top-level JSON object with `tag: "trace"`, real `ts`, `event`, `node`, `state`, and action-specific fields. Event names match `Trace.tla`, for example:

```json
{"tag":"trace","ts":123456789,"event":"controller_decide","node":"s1","value":"v1","state":{"view":0,"proposal_seq":2,"decisions_in_view":1,"checkpoint_seq":1,"phase":"PhaseCommitted","delivered":[1],"wal_len":2,"sync_lock_holder":"Nil","crashed":false,"viewdata_count":0}}
```

## Instrumented Code Points

| Event | Source location |
|-------|-----------------|
| `controller_start_view` | `internal/bft/controller.go`, end of `startView` |
| `controller_change_view` | `internal/bft/controller.go`, end of `changeView` |
| `controller_decide` | `internal/bft/controller.go`, after delivery and `DecisionsInView` increment |
| `controller_sync_begin` | `internal/bft/controller.go`, after `syncLock.Lock()` |
| `controller_sync_apply` | `internal/bft/controller.go`, deferred at end of `sync()` |
| `mutually_exclusive_deliver` | `internal/bft/controller.go`, both return paths in `MutuallyExclusiveDeliver.Deliver` |
| `view_propose` | `internal/bft/view.go`, after self `HandleMessage` in `Propose` |
| `view_process_preprepare` | `internal/bft/view.go`, after `State.Save(ProposedRecord)` |
| `view_process_prepares` | `internal/bft/view.go`, after `State.Save(Commit)` |
| `viewchanger_process_viewchange` | `internal/bft/viewchanger.go`, after view-data send/registration |
| `viewchanger_accept_viewdata` | `internal/bft/viewchanger.go`, after validated view-data registration |
| `viewchanger_check_inflight` | `internal/bft/viewchanger.go`, after successful `CheckInFlight` with an in-flight proposal |
| `viewchanger_commit_inflight` | `internal/bft/viewchanger.go`, after temporary prepared view starts |
| `viewchanger_process_newview` | `internal/bft/viewchanger.go`, after `Controller.ViewChanged` |
| `recover` | `internal/bft/state.go`, successful restore paths |

## Running

From the repository root:

```bash
cd .specula-output
bash harness/run.sh
```

The runner sets:

- `SMARTBFT_TLA_TRACE=1`
- `SMARTBFT_TLA_TRACE_FILE=<scenario trace file>`
- `TRACE_DIR=.specula-output/traces`

## Notes for Validation

- Node IDs are mapped by numeric ID: SmartBFT node `1` becomes TLA server `s1`.
- Proposal digests are mapped to `v1`, `v2`; additional values are currently collapsed to `v2` because the generated cfg uses two abstract values.
- The `crash` event is not emitted by the SmartBFT code because crash is a harness lifecycle action. Add it in an external process-control scenario if Phase 3 needs crash traces.
- `recover` is emitted from `PersistedState.Restore`; it captures restored view phase before subsequent network processing.
