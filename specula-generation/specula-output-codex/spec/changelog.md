# SmartBFT Validation Changelog

## Round 1 - Trace Validation
- [blocked] Harness trace generation: `harness/run.sh` could not run SmartBFT tests because `go` is not available on `PATH`; the only available trace is the existing empty `traces/smartbft.ndjson`.
- [check] Empty trace fixture: `Trace.tla` with `Trace.cfg` passed against the zero-line `traces/smartbft.ndjson`; output saved at `spec/output/trace_validation_empty.out`.
- [fix] Environment: installed Go with Homebrew (`go version go1.26.4 darwin/amd64`) and reran the harness.
- [fix] Harness portability: changed `harness/run.sh` to use workspace-local `GOCACHE`/`GOMODCACHE` and a shell watchdog instead of GNU `timeout`.
- [fix] Trace encoder: changed empty `delivered` slices from JSON `null` to `[]`; TLC cannot deserialize JSON null.
- [fix-spec] Synchronization model: changed `syncLockHolder` from a single global holder to a set of per-replica holders, matching SmartBFT's per-controller `syncLock`.
- [fix-spec] Startup/replay coverage: modeled startup `Recover`, observed `ControllerStartView` view numbers, no-op `ControllerChangeView`, enqueue-only `ViewPropose`, observed accepted pre-prepares, and split `MutuallyExclusiveDeliver` delivery from `ControllerDecide` bookkeeping.
- [blocked] Real trace validation: single-test trace `traces/test_basic.ndjson` replays through 31 of 32 events but still fails `TraceMatched` at the final `controller_decide` for `s3`; output saved at `spec/output/trace_test_basic.out`.

## Round 1 - Model Checking
- [partial] Standard `MC.cfg` run initialized successfully and reached BFS depth 5 with no violation reported before the bounded wrapper terminated it; output saved at `spec/output/MC_convergence_bounded.out`.
- [fix] Updated `MC.tla` for changed base action arities (`ControllerStartView`, `ControllerSyncBegin`, `ControllerSyncApply`).
- [partial] Current `MC.cfg` parses, initializes, and reaches BFS depth 5 with no violation reported before the bounded wrapper terminates it; output saved at `spec/output/MC_convergence_after_go.out`.

## Result
Validation workflow is blocked from completion by a remaining trace/spec abstraction mismatch in `test_basic.ndjson` at the final `controller_decide` event. Go is installed and the harness runs, but trace validation has not converged, so bug hunting is not complete.
