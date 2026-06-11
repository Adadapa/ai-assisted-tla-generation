# Bug Report - SmartBFT

## Summary

- Bug families tested: 0
- Bugs found: 0
- Configs run: none

Bug hunting was not started because the validation workflow did not converge. Go is now installed and the SmartBFT harness runs, but `Trace.tla` still fails to replay `traces/test_basic.ndjson` through the final `controller_decide` event.

## Not Reproduced

| Bug Family | Config | States Explored | Result |
|------------|--------|-----------------|--------|
| Family 1: decision/sync/view-change delivery interleavings | `MC_hunt_family1_delivery_sync.cfg` | Not run | Not testable until trace validation and standard model checking converge |
| Family 2: `DecisionsInView`, leader rotation, metadata freshness | `MC_hunt_family2_decisions_in_view.cfg` | Not run | Not testable until trace validation and standard model checking converge |
| Family 3: WAL crash recovery and persisted phase boundaries | `MC_hunt_family3_wal_recovery.cfg` | Not run | Not testable until trace validation and standard model checking converge |
| Family 4: normal proposal validation vs view-change in-flight validation | `MC_hunt_family4_inflight_viewchange.cfg` | Not run | Not testable until trace validation and standard model checking converge |

## Validation Notes

- Empty trace validation passed; see `spec/output/trace_validation_empty.out`.
- Harness run succeeded after Go installation and generated non-empty traces, including `traces/test_basic.ndjson`.
- `test_basic.ndjson` replay currently fails at the final `controller_decide` event; see `spec/output/trace_test_basic.out`.
- A bounded standard `MC.cfg` run with the current spec reached BFS depth 5 with no violation reported before termination; see `spec/output/MC_convergence_after_go.out`.
- The TLC build rejected the workflow guide's `-t` option, and the host does not provide a `timeout` executable, so the bounded run used a shell wrapper that killed and waited for TLC after a fixed interval.
