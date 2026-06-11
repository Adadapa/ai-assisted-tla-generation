# SmartBFT Brief Coverage Audit

Input brief: `.specula-output/modeling-brief.md`

## Bug Families

| Brief family | Base actions / variables | Hunt cfg |
|--------------|--------------------------|----------|
| Family 1: Decision, Sync, and View-Change Interleavings | `ControllerDecide`, `ControllerSyncBegin`, `ControllerSyncApply`, `MutuallyExclusiveDeliver`, `ViewChangerCommitInFlight`; variables `delivered`, `checkpointSeq`, `syncLockHolder` | `MC_hunt_family1_delivery_sync.cfg` |
| Family 2: `DecisionsInView`, Leader Rotation, Metadata Freshness | `ControllerChangeView`, `ControllerSyncApply`, `ViewChangerProcessNewView`, `ControllerStartView`; variables `decisionsInView`, `viewDecisions`, `leader`, `blacklist` | `MC_hunt_family2_decisions_in_view.cfg` |
| Family 3: WAL Crash Recovery and Persistent Phase Boundaries | `ViewProcessPrePrepare`, `ViewProcessPrepares`, `ViewChangerProcessViewChange`, `ViewChangerProcessNewView`, `Crash`, `Recover`; variables `wal`, `phase`, `restoredPhase`, `crashed` | `MC_hunt_family3_wal_recovery.cfg` |
| Family 4: Receiver-Side Validation Divergence | `ViewChangerAcceptViewData`, `ViewChangerCheckInFlight`, `ViewChangerCommitInFlight`; variables `viewData`, `selectedInFlight`, `inFlightPrepared` | `MC_hunt_family4_inflight_viewchange.cfg` |

## Proposed Invariants

| Brief invariant | Defined in | Wired in `MC.tla` | Enabled in cfg |
|-----------------|------------|-------------------|----------------|
| `Agreement` | `base.tla` | base invariant under `MCNext` | `MC.cfg`, all hunt cfgs |
| `NoDuplicateDelivery` | `base.tla` | base invariant under `MCNext` | `MC.cfg`, `MC_hunt_family1_delivery_sync.cfg` |
| `MonotonicCheckpoint` | `base.tla` | base invariant under `MCNext` | `MC.cfg`, Family 1, Family 3 |
| `LeaderMetadataAgreement` | `base.tla` | base invariant under `MCNext` | `MC_hunt_family2_decisions_in_view.cfg` |
| `InFlightSelectionSafety` | `base.tla` | base invariant under `MCNext` | `MC_hunt_family4_inflight_viewchange.cfg` |
| `RestorePhaseSoundness` | `base.tla` | base invariant under `MCNext` | `MC_hunt_family3_wal_recovery.cfg` |

Note: `LeaderMetadataAgreement`, `InFlightSelectionSafety`, and `RestorePhaseSoundness` are intentionally commented out in standard `MC.cfg` and enabled in targeted hunt cfgs, per the skill guidance.

## Model-Checkable Findings

| Finding | Trigger mechanism | Expected invariant | Target cfg |
|---------|-------------------|--------------------|------------|
| MC1: sync and view-change catch-up interleaving can duplicate delivery/checkpoint | `ControllerSyncBegin/Apply`, `MutuallyExclusiveDeliver`, `ViewChangerCommitInFlight`, normal `ControllerDecide` | `NoDuplicateDelivery`, `MonotonicCheckpoint` | `MC_hunt_family1_delivery_sync.cfg` |
| MC2: same-height sync plus higher-view state transfer leaves `DecisionsInView` inconsistent | `ControllerSyncApply`, `ControllerChangeView`, `ControllerStartView` | `LeaderMetadataAgreement` | `MC_hunt_family2_decisions_in_view.cfg` |
| MC3: crash after persisted commit but before app checkpoint restarts into unsafe signing phase | `ViewProcessPrepares`, `Crash`, `Recover` | `RestorePhaseSoundness`, `Agreement` | `MC_hunt_family3_wal_recovery.cfg` |
| MC4: Byzantine view-data equivocation selects invalid in-flight proposal | `ViewChangerAcceptViewData`, `ViewChangerCheckInFlight`, `ViewChangerCommitInFlight` | `InFlightSelectionSafety`, `Agreement` | `MC_hunt_family4_inflight_viewchange.cfg` |

## Intentional Scope Limits

- The spec abstracts cryptographic validation into `proposal.valid` and does not model signature forgery.
- Reconfiguration is represented through metadata, view-change, and sync paths; full dynamic membership-set replacement is left for a later extension.
- Request-pool sizing and metrics are not modeled.
- WAL filesystem atomic directory creation is not modeled below the protocol record abstraction.
