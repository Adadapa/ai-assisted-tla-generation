# SmartBFT Modeling Brief

## 1. System Overview

SmartBFT is a Go Byzantine fault-tolerant state machine replication library, approximately 19k Go LOC across consensus, view-change, request-pool, heartbeat, WAL, and tests. Category: **Category A (Distributed / Message-Passing), BFT overlay**; the implementation is a permissioned authenticated BFT-Smart/PBFT-style protocol with view change, quorums, signatures, state transfer, leader rotation, and reconfiguration. It also has important Go concurrency boundaries: controller, view, view-changer, heartbeat monitor, request-pool timers, WAL recovery, and async signature verification goroutines. The SmartBFT paper describes a Go BFT consensus library tailored for Fabric ordering, and PBFT provides the theoretical baseline for pre-prepare/prepare/commit and view-change safety.

Key implementation choices to model beyond textbook PBFT:
- `DecisionsInView` drives leader rotation and is embedded in proposal metadata.
- View-change may commit/deliver a one-ahead decision before validating all view-data signatures, because reconfiguration can change validator context.
- WAL persists pre-prepare, commit, view-change, and new-view records, but truncation currently happens only on new proposed records.
- Reconfiguration restarts controller/view-changer components while preserving checkpoint and request-pool state.

## 2. Bug Families

### Family 1: Decision, Sync, and View-Change Interleavings

**Mechanism**: Multiple independently scheduled paths can advance checkpoint/sequence or deliver a decision: normal view commit, sync result, view-data catch-up, new-view in-flight commit, and controller change-view.

**Evidence**:
- Historical: `57f434c` / PR #570 fixed double delivery; `154c866` / PR #560 and revert `31f018a` show sync double-delivery complexity; `d9182ed` / PR #553 fixed committed sequence twice; `30764c3` / PR #538 fixed committing during view change with an in-flight decision; `eb005ee` / PR #622 fixed simultaneous decision progression and view stopping.
- Code analysis: `Controller.run` multiplexes decision, view-change, abort, leader-token, and sync events (`internal/bft/controller.go:498`); `MutuallyExclusiveDeliver` serializes sync and application delivery but can replace the checkpoint from sync if the pending proposal is already committed (`internal/bft/controller.go:940`); view-change can deliver one-ahead decisions while validating view data (`internal/bft/viewchanger.go:617`, `internal/bft/viewchanger.go:1046`); in-flight commit creates a temporary prepared view (`internal/bft/viewchanger.go:1186`).

**Affected code paths**: `Controller.decide`, `Controller.sync`, `MutuallyExclusiveDeliver.Deliver`, `ViewChanger.checkLastDecision`, `ViewChanger.validateNewViewMsg`, `ViewChanger.commitInFlightProposal`.

**Suggested modeling approach**:
- Variables: `checkpointSeq`, `deliveredSeqs`, `controllerView`, `viewChangerView`, `inFlight`, `syncResult`, `stopped`.
- Actions: split normal commit, sync checkpoint update, view-data catch-up delivery, new-view in-flight delivery, and view abort/restart.
- Granularity: model delivery and checkpoint update as separate steps guarded by a mutual-exclusion token, because the implementation explicitly serializes these operations.

**Priority**: High
**Rationale**: Highest historical bug density, safety-relevant exactly-once delivery, and good TLA+ fit.

### Family 2: `DecisionsInView`, Leader Rotation, and Metadata Freshness

**Mechanism**: Leader identity depends on view, blacklist, `DecisionsInView`, and `DecisionsPerLeader`; stale or reset `DecisionsInView` causes honest nodes to reject proposals or rotate to different leaders.

**Evidence**:
- Historical: `62e7161` / PR #663 fixed `DecisionsInView` reset to zero during same-height sync; `e5a79af` / PR #512 added `DecisionsInView` checks for change-view; `134292d` / PR #599 changed when prev commit signatures are attached for leader rotation; `7385234` / PR #452 fixed blacklisting current leader.
- Code analysis: leader is computed from `getCurrentViewNumber`, `currDecisionsInView`, blacklist, and rotation config (`internal/bft/controller.go:233`); `changeView` resets `currDecisionsInView` from the caller-provided value (`internal/bft/controller.go:407`); normal proposals reject mismatched decisions (`internal/bft/view.go:578`); sync derives new decisions from latest decision metadata or state-transfer response (`internal/bft/controller.go:635`, `internal/bft/controller.go:662`); startup/reconfig uses `setViewAndSeq` to convert latest committed metadata into next proposal metadata (`pkg/consensus/consensus.go:460`).

**Affected code paths**: `getLeaderID`, `Controller.changeView`, `Controller.sync`, `Consensus.setViewAndSeq`, `View.verifyProposal`, `View.GetMetadata`.

**Suggested modeling approach**:
- Variables: `decisionsInView[node]`, `metadataDecisions[seq]`, `leader[node]`, `blacklist`, `syncMetadata`.
- Actions: normal decision increment, leader rotation, same-height sync, higher-view state transfer, new-view restore, reconfiguration restart.
- Granularity: split sync into `ReadLatestDecision`, `FetchState`, `UpdateControllerCounters`, and `StartView`.

**Priority**: High
**Rationale**: Recent production-style bug, directly affects liveness and can cascade into repeated sync/view-change loops; model can verify whether all transition paths preserve metadata agreement.

### Family 3: WAL Crash Recovery and Persistent Phase Boundaries

**Mechanism**: Crash recovery reconstructs view phase from the last persisted WAL records; missing, truncated, or stale phase records can restart nodes in a different protocol phase than the live cluster expects.

**Evidence**:
- Historical: `e5f5a42` fixed WAL repair; `a2d2cad` changed WAL file accumulation; TODO in `PersistedState.Save` notes new-view truncation is not yet handled.
- Code analysis: pre-prepare records are truncation points, while commit/new-view/view-change records are not (`internal/bft/state.go:50`); recovery from a commit expects the previous WAL entry to be the matching pre-prepare (`internal/bft/state.go:184`); `Consensus.setViewAndSeq` separately restores view-change and new-view records from only the last WAL entry (`pkg/consensus/consensus.go:471`, `pkg/consensus/consensus.go:486`); WAL read clears items at truncation markers and returns the suffix after the latest marker (`pkg/wal/writeaheadlog.go:555`).

**Affected code paths**: `PersistedState.Save`, `PersistedState.Restore`, `LoadViewChangeIfApplicable`, `LoadNewViewIfApplicable`, `WriteAheadLogFile.ReadAll`.

**Suggested modeling approach**:
- Variables: `wal`, `durablePhase`, `inMemoryPhase`, `checkpoint`, `crashed`.
- Actions: persist pre-prepare, persist commit, persist view-change, persist new-view, crash, repair/read, restore proposer.
- Granularity: each WAL append is an atomic durable action; application delivery/checkpoint update is a separate action.

**Priority**: Medium
**Rationale**: Crash/recovery is modelable and safety-relevant, but current local evidence is mostly defensive comments and historical WAL repair rather than an unfixed confirmed safety bug.

### Family 4: Receiver-Side Validation Divergence Between Normal and View-Change Paths

**Mechanism**: Normal proposals go through `VerifyProposal`, metadata, prev-commit, and blacklist checks; view-change in-flight candidates are selected from view data by quorum predicates, then committed through a temporary view.

**Evidence**:
- Historical: `420a802` added conflicting-proposals test/fix; `6833de8` fixed fork view change; `f2a2545` heavily rewrote view-change handling.
- Code analysis: normal path validates app proposal, metadata, verification sequence, prev commit signatures, and blacklist (`internal/bft/view.go:554`); `ValidateInFlight` only checks sequence relative to last decision (`internal/bft/viewchanger.go:729`); `CheckInFlight` selects proposals using A1/A2-style counts (`internal/bft/viewchanger.go:813`); `commitInFlightProposal` signs and commits the selected proposal via a prepared temporary view (`internal/bft/viewchanger.go:1216`).

**Affected code paths**: `View.verifyProposal`, `ValidateInFlight`, `CheckInFlight`, `ViewChanger.processNewViewMsg`, `ViewChanger.commitInFlightProposal`.

**Suggested modeling approach**:
- Variables: `validProposal`, `preparedEvidence`, `viewData`, `selectedInFlight`, `committed`.
- Actions: Byzantine view-data equivocation, honest view-data emission, new leader selection, in-flight commit.
- Granularity: route Byzantine view data through the same validation predicates; do not model signature forgery.

**Priority**: Medium
**Rationale**: Promising BFT receiver-validation question, but likely intentionally relies on quorum intersection rather than full revalidation. Needs model checking to confirm whether A1/A2 selection suffices under the implementation’s reconfiguration constraints.

## 3. Modeling Recommendations

### 3.1 Model

| What | Why | How |
|------|-----|-----|
| Exactly-once delivery across normal commit, sync, and view-change | Family 1 has repeated historical fixes and direct safety impact | Split delivery/checkpoint/sync/view-change actions with a mutex-like token |
| `DecisionsInView` metadata preservation | Family 2 caused recent same-height sync regression | Track per-node controller counter and proposal metadata counter |
| View-change in-flight selection | Family 4 is the central BFT safety bridge | Model view-data messages, prepared flags, and A1/A2 selection |
| Crash/restart phase reconstruction | Family 3 captures implementation-specific persistence | Model WAL suffix and restoration of `PROPOSED`/`PREPARED`/new-view states |

### 3.2 Do Not Model

| What | Why |
|------|-----|
| Cryptographic primitive breaks | SmartBFT assumes authenticated signatures; useful bugs are receiver predicate gaps, not forgery |
| Request-pool sizing and metrics bugs | Reconfig TODO around queue size is operational/test-verifiable, not core consensus safety |
| Pure Go data races already fixed in history | Use commits as evidence for concurrency hot spots; do not recreate closed races as MC targets |
| WAL filesystem atomic directory creation TODO | Important engineering hardening, but below the protocol abstraction unless crash-created partial directories are in scope |

## 4. Proposed Extensions

| Extension | Variables | Purpose | Bug Family |
|-----------|-----------|---------|------------|
| Split delivery/sync controller | `deliveredSeqs`, `checkpointSeq`, `syncLock`, `stopped` | Check no duplicate or skipped delivery under interleavings | Family 1 |
| Leader-rotation metadata | `decisionsInView`, `metadataDecisions`, `leader`, `blacklist` | Check all honest nodes compute same leader and accept next proposal | Family 2 |
| WAL recovery | `wal`, `durablePhase`, `inFlight`, `crashed` | Check restart resumes from valid phase and sequence | Family 3 |
| View-change in-flight evidence | `viewData`, `prepared`, `selectedProposal`, `validProposal` | Check selected in-flight proposal is safe to commit | Family 4 |

## 5. Proposed Invariants

| Invariant | Type | Description | Targets |
|-----------|------|-------------|---------|
| Agreement | Safety | No two honest nodes deliver different proposals for the same sequence | Families 1, 4 |
| NoDuplicateDelivery | Safety | An honest node never delivers the same sequence twice | Family 1 |
| MonotonicCheckpoint | Safety | Honest checkpoint sequence never decreases across sync, view-change, and restart | Families 1, 3 |
| LeaderMetadataAgreement | Safety/Liveness guard | Honest nodes in the same view/sequence compute the same leader from metadata | Family 2 |
| InFlightSelectionSafety | Safety | A new-view selected in-flight proposal is either already decided or has sufficient prepared evidence | Family 4 |
| RestorePhaseSoundness | Safety | Restored phase never allows a node to sign conflicting prepare/commit for a sequence | Family 3 |

## 6. Findings Pending Verification

### 6.1 Model-Checkable

| ID | Description | Expected invariant violation | Bug Family |
|----|-------------|----------------------------|------------|
| MC1 | Can a sync result and a view-change catch-up delivery interleave so an honest node delivers or checkpoints the same sequence twice despite `syncLock`? | `NoDuplicateDelivery`, `MonotonicCheckpoint` | Family 1 |
| MC2 | Can same-height sync plus higher-view state transfer leave `DecisionsInView` inconsistent between controller state and proposal metadata? | `LeaderMetadataAgreement` | Family 2 |
| MC3 | Can crash after persisted commit but before app checkpoint, followed by WAL repair/read, restart in a phase that allows conflicting signatures? | `RestorePhaseSoundness`, `Agreement` | Family 3 |
| MC4 | Under Byzantine view-data equivocation and partial reconfiguration, can `CheckInFlight` select an in-flight proposal that no honest quorum would validate on the normal path? | `InFlightSelectionSafety`, `Agreement` | Family 4 |

### 6.2 Test-Verifiable

| ID | Description | Suggested test approach |
|----|-------------|------------------------|
| TV1 | Request-pool queue size is not updated on reconfiguration | Reconfig integration test that changes `RequestPoolSize` and asserts capacity |
| TV2 | WAL partial directory/file creation handling | Fault-injection filesystem test around `wal.Create` and startup retry |
| TV3 | `gh` issue archaeology unavailable in this environment | Run `gh issue list/view` externally and append confirmed issue classifications |

### 6.3 Code-Review-Only

| ID | Description | Suggested action |
|----|-------------|------------------|
| CR1 | `PersistedState.Save` TODO says new-view records are not truncation points | Audit whether long WAL suffixes or stale phase records can survive after finalized new-view |
| CR2 | `ViewChanger.processViewDataMsg` reprocesses self new-view message | Confirm this cannot duplicate vote accounting or interact with closed `viewDataMsgs.votes` |
| CR3 | `ValidateInFlight` validates only sequence shape | Review whether all required proposal validity is guaranteed indirectly by A1/A2 quorum intersection |

## 7. Reference Pointers

- Detailed audit: `.specula-output/analysis-report.md`
- Core files: `SmartBFT/internal/bft/controller.go`, `SmartBFT/internal/bft/view.go`, `SmartBFT/internal/bft/viewchanger.go`, `SmartBFT/internal/bft/state.go`, `SmartBFT/pkg/consensus/consensus.go`, `SmartBFT/pkg/wal/writeaheadlog.go`
- Key historical commits: `62e7161`, `eb005ee`, `57f434c`, `154c866`, `d9182ed`, `30764c3`, `6833de8`, `420a802`, `39017cf`, `e5f5a42`
- Reference papers: SmartBFT paper, "A Byzantine Fault-Tolerant Consensus Library for Hyperledger Fabric"; Castro/Liskov PBFT thesis, "Practical Byzantine Fault Tolerance"
