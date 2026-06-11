# SmartBFT Code Analysis Report

## Scope and Coverage

Target: `/Users/adaturgut/software-analysis/Specula/SmartBFT`

Method: project-local `skills/code_analysis` workflow. The system is Category A distributed/message-passing with a BFT overlay; concurrent Go goroutine boundaries were included where they affect protocol atomicity.

Coverage performed:
- Source map: `pkg/consensus`, `internal/bft`, `pkg/wal`, `pkg/types`, `pkg/api`, and integration tests.
- Core LOC count: 19,059 Go LOC under `pkg` and `internal`, including tests/mocks in those directories; core implementation hot files are `controller.go`, `view.go`, `viewchanger.go`, `requestpool.go`, `heartbeatmonitor.go`, `state.go`, and WAL.
- Git history: 658 commits touching `pkg`, `internal`, `test`, or protobufs. Reviewed core-file history and classified significant fix commits visible locally.
- GitHub issue/PR discussions: not deeply verified because `gh` is not installed in this environment (`zsh: gh: command not found`). PR numbers are taken from commit subjects and local commit messages, not from live issue-thread reading.
- Reference papers: SmartBFT paper and Castro/Liskov PBFT thesis were consulted for protocol context.

## Structural Map

`pkg/consensus/consensus.go` wires public API, configuration validation, reconfiguration, component lifecycle, node membership filtering, and component creation. Incoming consensus messages are rejected if the sender is not in `nodeMap` before dispatch to the controller.

`internal/bft/controller.go` is the central event loop. It handles client requests, leader request timeouts, heartbeat timeouts, message dispatch, view start/abort/change, sync, delivery, request pruning, and leader-token scheduling.

`internal/bft/view.go` implements normal pre-prepare/prepare/commit. It validates proposals, persists proposed/prepared phase records, collects prepares/commits, signs commits, handles previous-sequence assist messages, and triggers sync when it observes enough future commits.

`internal/bft/viewchanger.go` implements view-change, view-data validation, new-view validation, in-flight proposal selection, and temporary prepared views used to commit in-flight proposals during view change.

`internal/bft/state.go` maps protocol phase records to WAL entries and reconstructs view phase after restart.

`pkg/wal/writeaheadlog.go` implements append/read/repair/truncate mechanics with CRC-chained records and file rotation.

## Historical Bug Families

### Exactly-Once Delivery and Sync/View-Change Races

Evidence:
- `57f434c` / PR #570: "Deliver Twice Bug Fix" touched controller and viewchanger with extensive tests.
- `154c866` / PR #560: "fix two twice delivery on sync" touched controller and tests; reverted by `31f018a`, then later fixed by #570.
- `d9182ed` / PR #553: "fix committed sequence twice" changed controller, viewchanger, consensus, and integration tests.
- `30764c3` / PR #538: fixed crash when a node commits during view change while holding an in-flight proposal; root cause was second view-data message encountering now-stale in-flight state.
- `eb005ee` / PR #622: fixed simultaneous decision progression and view stopping.

Current code evidence:
- Controller event loop handles decisions, view changes, aborts, leader token, and sync in one select (`internal/bft/controller.go:498`).
- Sync and deliver are serialized by `syncLock`, but sync can still update checkpoints and cause view restarts (`internal/bft/controller.go:585`, `internal/bft/controller.go:940`).
- View-change can call application delivery while processing view data or new-view messages (`internal/bft/viewchanger.go:617`, `internal/bft/viewchanger.go:1046`).

Assessment: high priority. This is the best TLA+ target because it combines historical bug density with simple observable invariants: no duplicate delivery, monotonic checkpoint, and agreement.

### `DecisionsInView` and Leader Rotation

Evidence:
- `62e7161` / PR #663 fixed same-height sync resetting `DecisionsInView` to zero, causing later leader proposals to be rejected and repeated recovery loops.
- `e5a79af` / PR #512 added `DecisionsInView` checking during change-view.
- `134292d` / PR #599 changed when previous commit signatures are included based on leader rotation.
- `7385234` / PR #452 fixed not blacklisting the current leader.

Current code evidence:
- Leader ID is derived from view, node list, leader-rotation flag, `DecisionsInView`, decisions-per-leader, and blacklist (`internal/bft/util.go:72`).
- Controller keeps `currDecisionsInView` under its own lock, while each `View` has its own `DecisionsInView` field (`internal/bft/controller.go:124`, `internal/bft/view.go:88`).
- Normal proposal metadata must exactly match view sequence and decisions in view (`internal/bft/view.go:568`, `internal/bft/view.go:573`, `internal/bft/view.go:578`).
- Sync computes new proposal sequence and decisions from latest decision metadata and state transfer (`internal/bft/controller.go:635`, `internal/bft/controller.go:662`).

Assessment: high priority. This is safety-adjacent liveness: divergent leader computation can cause rejection loops and view changes, and with blacklist/reconfiguration it may become a safety precondition.

### View-Change In-Flight Evidence and Receiver Validation

Evidence:
- `6833de8` / PR #499 fixed fork view change.
- `420a802` added a conflicting proposals test and bug fix.
- `f2a2545` rewrote/fixed view-change logic and tests.

Current code evidence:
- Normal proposal validation includes app-level proposal verification, metadata validation, prev-commit signature verification, blacklist computation, and prev-commit digest binding (`internal/bft/view.go:554`).
- View-change `ValidateInFlight` checks only metadata presence and sequence relation to last decision (`internal/bft/viewchanger.go:729`).
- `CheckInFlight` uses A1/A2-style quorum conditions to select an in-flight proposal (`internal/bft/viewchanger.go:813`).
- `commitInFlightProposal` constructs a temporary `View` in `PREPARED` phase and attempts to commit the selected proposal (`internal/bft/viewchanger.go:1216`).

Assessment: medium priority. This may be correct by quorum intersection, but it is a receiver-validation divergence worth modeling with Byzantine equivocation and reconfiguration context.

### WAL and Crash Recovery

Evidence:
- `e5f5a42` fixed WAL repair.
- `a2d2cad` changed WAL file accumulation.
- `internal/bft/state.go:57` TODO says new-view records are not yet handled as truncation points.

Current code evidence:
- `PersistedState.Save` writes every saved message but marks truncation only for proposed records (`internal/bft/state.go:50`).
- Recovering from a commit requires the previous WAL entry to be a matching pre-prepare (`internal/bft/state.go:184`).
- `LoadViewChangeIfApplicable` and `LoadNewViewIfApplicable` inspect only the last WAL entry (`internal/bft/state.go:77`, `internal/bft/state.go:96`).
- WAL `ReadAll` clears its returned suffix at records marked `TruncateTo` (`pkg/wal/writeaheadlog.go:555`).

Assessment: medium priority. The model should treat WAL appends as durable atomic actions and explore crash points before/after delivery and checkpoint persistence.

### Reconfiguration and Membership Boundary

Evidence:
- `f8474b6` verified membership change in `view.go`.
- `399aae2` filtered unexpected nodes in `consensus.go`.
- `8cfccc9` and `fd3c35e` updated request-timeout handler/options on reconfig.
- `36cac46` fixed nil `MembershipNotifier` panic.
- `584daef` restricted use of `Comm.Nodes()` to consensus start.

Current code evidence:
- `Consensus.reconfig` stops view-changer/controller/collector before replacing configuration and restarting components (`pkg/consensus/consensus.go:186`).
- `HandleMessage` rejects senders absent from the current `nodeMap` (`pkg/consensus/consensus.go:290`).
- `View.verifyBlacklist` has special paths for verification sequence or membership changes where blacklist must remain unchanged (`internal/bft/view.go:667`, `internal/bft/view.go:677`).

Assessment: useful context for Families 1, 2, and 4, but not a standalone first model unless the spec scope explicitly includes dynamic membership.

## Developer Signals

High-signal TODOs:
- `pkg/wal/writeaheadlog.go:148`: create WAL directory/file atomically via temp dir and rename.
- `pkg/consensus/consensus.go:229`: request pool queue size is not handled on reconfiguration.
- `internal/bft/state.go:57`: new-view WAL records are not truncation points yet.
- `internal/bft/viewchanger.go:782`: self new-view message is reprocessed.
- `internal/bft/viewchanger.go:1005`: after sync due to future new-view data, code does not revalidate and rejoin immediately.

## Candidate Findings

Model-checkable:
- MC1: exactly-once delivery across sync, view-change catch-up, and normal commit.
- MC2: metadata agreement for `DecisionsInView` across same-height sync, higher-view state transfer, and reconfiguration restart.
- MC3: WAL crash/restart phase soundness after persisted commit or new-view records.
- MC4: in-flight view-change selection safety under Byzantine view data and reconfiguration.

Test-verifiable:
- Request-pool queue-size reconfiguration.
- WAL atomic creation and repair edge cases.
- Liveness around `viewchanger.go:1005` after future new-view data triggers sync.

Code-review-only:
- Whether `ValidateInFlight` intentionally omits app-level proposal validation.
- Whether reprocessing self new-view can be simplified or proven harmless.
- Whether `LoadNewViewIfApplicable` and `LoadViewChangeIfApplicable` should scan more than the last WAL entry after truncation.

## Exclusions and False Positives

Closed historical bugs are not treated as modeling targets. They are used as evidence for mechanisms only.

Excluded:
- Metrics-only changes, typo fixes, logging improvements, and refactors.
- Pure performance concerns in batching and request pool.
- Cryptographic primitive breaks; the BFT model should assume unforgeable honest signatures and Byzantine nodes signing as themselves.
- Go panics in tests/mocks unless they correspond to production protocol paths.

## Limitations

The GitHub issue/PR archaeology required by the full skill could not be completed because the `gh` CLI is unavailable. Local commit messages include PR numbers and useful summaries, but they are not a substitute for full discussion-thread verification. A complete follow-up pass should run:

```bash
gh issue list -R hyperledger-labs/SmartBFT --state all --search 'bug OR race OR panic OR correctness OR view change OR sync' --limit 100
gh pr list -R hyperledger-labs/SmartBFT --state all --search 'bug OR race OR panic OR correctness OR view change OR sync' --limit 100
gh issue view -R hyperledger-labs/SmartBFT <number> --comments
gh pr view -R hyperledger-labs/SmartBFT <number> --comments
```

## Output

Primary handoff: `.specula-output/modeling-brief.md`
