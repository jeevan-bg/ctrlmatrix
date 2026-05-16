//!
//! conformance σ_min structural layer. The predicate has two clauses:
//!
//! - clause (a): `kind = spawn → SpawnedBy ≠ none`
//!     (a Spawn event MUST carry a cap-mint binding).
//! - clause (b): `kernelAuthored ∨ SpawnedBy = none`
//!     (only the kernel may set `SpawnedBy`; tenant-authored events
//!     with `SpawnedBy = some _` are forgery).
//!
//! ## H1 Definition — what each test asserts
//!
//! - `spawn_without_spawnedby_rejected` — falsifies clause (a). An
//!   event with `kind = Kind.spawn` and `SpawnedBy = none` MUST
//!   fail `well_formed_spawned_by`.
//! - `tenant_self_spawn_rejected` — falsifies clause (b). An event
//!   with `kernelAuthored = false` and `SpawnedBy = some _` MUST
//!   fail (tenant cannot self-claim a spawn-relationship).
//! - `kernel_spawn_well_formed_accepted` — positive arm. An event
//!   with `kernelAuthored = true` AND `SpawnedBy = some p` MUST be
//!   accepted by the predicate.
//!
//! rebuttals)
//!
//! ### Attacks against `spawn_without_spawnedby_rejected`
//!
//! 1. **Default-vacuity**: if the conformance harness implements
//!    `well_formed_spawned_by` such that `SpawnedBy = none` is the
//!    silent default for any `kind`, the predicate degenerates to
//!    `true` for spawn events. **Rebuttal:** the test explicitly
//!    asserts `!well_formed_spawned_by(&falsifier)` on a constructed
//!    `Spawn` event with `spawned_by = None` — if the predicate
//!    silently accepted this, the test would FAIL, exhibiting the
//! 2. **Off-by-one in kind enum match**: a buggy implementation might
//!    match `Kind::Other` instead of `Kind::Spawn`. **Rebuttal:** the
//!    `kernel_spawn_well_formed_accepted` positive arm exercises a
//!    well-formed `Spawn` event; if the predicate misroutes Spawn
//!    events to the Other arm, the falsifier would still be accepted
//!    (predicate returns `true`) and we would catch it via the
//!    contrasting positive arm.
//! 3. **Harness -injection of well-formed events bypassing
//!    the falsifier**: a buggy test runner might accept the event
//!    via a different code path (e.g., the M6 hash-chain
//!    `well_formed`). **Rebuttal:** this test invokes
//!    `well_formed_spawned_by` directly — no detour through M6
//!    chassis — and the predicate is the published L0 mirror name.
//!
//! ### Attacks against `tenant_self_spawn_rejected`
//!
//! 1. **`kernel_authored = true` shadow forgery**: an attacker-tenant
//!    claims `kernel_authored = true` AND `spawned_by = Some _`. At
//!    the σ_min structural layer this would be ACCEPTED — the
//!    enforcement that only-kernel-can-set-`kernel_authored` is L1+
//!    kernel-runtime TCB (a non-tenant-tamperable boolean is a
//!    cryptographic discipline, not a structural one). **Rebuttal:**
//!    the σ_min layer's `well_formed_spawned_by` predicate is
//!    explicitly STRUCTURAL — it checks the *combination* of
//!    flag-state AND constructor-state, not that the flag was set
//!    legitimately. The attack scenario is captured at the
//!    DOCUMENTED-CAVEAT below: `kernel_authored = true ∧
//!    spawned_by = Some _` would pass the σ_min structural predicate
//!    but be flagged at the L1+ kernel-runtime layer. We document
//!    naming.
//! 2. **Empty parents list with non-empty SpawnedBy**: would the
//!    predicate also enforce that `spawned_by ⇒ parents ≠ ∅`?
//!    **Rebuttal:** No — the cross-cell happens-before discipline
//!    `wellFormedSpawnedBy`'s clause. `wellFormedSpawnedBy` is
//!    intentionally narrow: clauses (a) and (b) only.
//! 3. **`Kind::Other` event with `kernel_authored = false` and
//!    `spawned_by = Some _`**: not strictly a spawn event but still
//!    forgery? **Rebuttal:** YES — clause (b)'s `kernelAuthored ∨
//!    SpawnedBy = none` applies to *any* event with
//!    `spawned_by = Some _`, regardless of kind. We exercise this
//!    breadth in `unit_tenant_other_event_with_spawnedby_rejected`
//!    below.
//!
//! ### Attacks against `kernel_spawn_well_formed_accepted`
//!
//! 1. **Vacuous accept by always-true predicate**: a buggy predicate
//!    might return `true` unconditionally. **Rebuttal:** the negative
//!    falsifiers above (which MUST return `false`) catch this — if
//!    the predicate is always-true, the negatives FAIL, exhibiting
//!    the bug.
//! 2. **Cap-mint binding shape**: does `spawned_by = Some p` with
//!    `p` not corresponding to any `CapMintRecord` in the trace
//!    pass? **Rebuttal:** at the σ_min structural layer, YES —
//!    TCB. We document this honestly.
//! 3. **Multi-parent spawn**: does the predicate care about
//!    `parents.len() > 1`? **Rebuttal:** No — `wellFormedSpawnedBy`'s
//!    two clauses do not constrain `parents.len()`; that constraint
//!    lives at the cross-cell happens-before relation layer ().
//!
//! ## DOCUMENTED-CAVEAT — L1+ TCB residual
//!
//! 1. **kernel_authored field integrity** is a cryptographic discipline
//!    (only-kernel-can-set), not a structural one. The σ_min layer
//!    treats `kernel_authored` as a free Boolean. End-to-end forgery
//!    enforcement requires kernel-runtime non-tenant-tamperable
//!    state — L1+ TCB.
//! 2. **`SpawnedBy = Some p` end-to-end cap-mint binding** to a
//!    kernel-runtime TCB. The σ_min layer only checks the local
//!    structural shape (Option<CapId>); the global referential
//!    integrity (cap-mint record existence + `mintedCapId` match) is
//!    the L1+ binding obligation.

use ctrlmatrix_conformance::generators::{
    kernel_spawn_from_seed, tenant_other_event, well_formed_spawned_by, CapId, EventId, Kind,
    KernelEvent,
};
use proptest::prelude::*;

// =====================================================================
// Falsifier shape #1 — spawn_without_spawnedby_rejected (clause (a))
// =====================================================================

/// Construct a Spawn event with `SpawnedBy = None` — the σ_min
/// falsifier for clause (a).
fn spawn_without_spawnedby() -> KernelEvent {
    KernelEvent {
        event_id: 1,
        kind: Kind::Spawn,
        kernel_authored: true,
        spawned_by: None, // <-- falsifier: spawn MUST carry a cap-mint binding.
        retract_target: None,
        parents: vec![0],
    }
}

#[test]
fn spawn_without_spawnedby_rejected() {
    let falsifier = spawn_without_spawnedby();
    assert!(
        !well_formed_spawned_by(&falsifier),
        "wellFormedSpawnedBy must reject Kind.spawn with SpawnedBy = none (clause (a))"
    );
}

// =====================================================================
// Falsifier shape #2 — tenant_self_spawn_rejected (clause (b))
// =====================================================================

/// Construct a forged spawn event: kernelAuthored = false AND
/// SpawnedBy = Some _. The σ_min falsifier for clause (b) — only the
/// kernel may set `SpawnedBy`.
fn tenant_self_spawn(seed: u32) -> KernelEvent {
    let mut cap_id: CapId = [0u8; 32];
    cap_id[0..4].copy_from_slice(&seed.to_le_bytes());
    cap_id[4..15].copy_from_slice(b"forgedcap__");
    KernelEvent {
        event_id: 2,
        kind: Kind::Spawn,
        kernel_authored: false, // <-- falsifier: tenant claims spawn.
        spawned_by: Some(cap_id),
        retract_target: None,
        parents: vec![0],
    }
}

#[test]
fn tenant_self_spawn_rejected() {
    let falsifier = tenant_self_spawn(0xDEAD_BEEF);
    assert!(
        !well_formed_spawned_by(&falsifier),
        "wellFormedSpawnedBy must reject tenant-authored event with SpawnedBy = Some _ (clause (b))"
    );
}

// =====================================================================
// Positive arm — kernel_spawn_well_formed_accepted
// =====================================================================

#[test]
fn kernel_spawn_well_formed_accepted() {
    // kernelAuthored = true AND SpawnedBy = Some _ ⇒ predicate accepts.
    let positive = kernel_spawn_from_seed(3, 0, 0xCAFE_BABE);
    assert!(matches!(positive.kind, Kind::Spawn));
    assert!(positive.kernel_authored);
    assert!(positive.spawned_by.is_some());
    assert!(
        well_formed_spawned_by(&positive),
        "wellFormedSpawnedBy must accept kernel-authored Spawn with SpawnedBy = Some _"
    );
}

// =====================================================================
// Cross-checks — the predicate's full truth table at the σ_min layer
// =====================================================================

#[test]
fn unit_other_kind_with_no_spawnedby_accepted() {
    // Vacuous case for a non-Spawn event: predicate accepts an Other
    // event with SpawnedBy = None (both clauses (a) and (b) hold:
    // (a) trivially since kind ≠ spawn; (b) since SpawnedBy = None).
    let other = tenant_other_event(10, vec![0]);
    assert!(well_formed_spawned_by(&other));
}

#[test]
fn unit_tenant_other_event_with_spawnedby_rejected() {
    // Breadth check (H2  against tenant_self_spawn): even a
    // non-Spawn-kind event with `kernel_authored = false` and
    // `spawned_by = Some _` is rejected by clause (b). The predicate
    // applies to ALL events, not just Spawn-kind events.
    let mut e = tenant_other_event(11, vec![0]);
    let mut bad_cap: CapId = [0u8; 32];
    bad_cap[0..6].copy_from_slice(b"bogus_");
    e.spawned_by = Some(bad_cap);
    assert!(
        !well_formed_spawned_by(&e),
        "wellFormedSpawnedBy clause (b) applies to all events, not just Spawn-kind"
    );
}

#[test]
fn unit_kernel_authored_other_with_spawnedby_accepted() {
    // Edge case: kernel-authored Other event with SpawnedBy = Some _.
    // Clause (a) trivially holds (kind ≠ spawn); clause (b) holds
    // (kernel_authored = true). Predicate ACCEPTS — this is the
    // honest naming residual: at the σ_min structural layer, only
    // the (kind, kernel_authored, spawned_by) triple matters; binding
    // back to a CapMintRecord is L1+ kernel-runtime TCB.
    let mut e = tenant_other_event(12, vec![0]);
    e.kernel_authored = true;
    let mut cap: CapId = [0u8; 32];
    cap[0..7].copy_from_slice(b"k_other");
    e.spawned_by = Some(cap);
    assert!(well_formed_spawned_by(&e));
}

#[test]
fn unit_spawn_with_kernel_false_and_spawnedby_some_rejected() {
    // Composite falsifier: kind = Spawn AND kernel_authored = false
    // AND SpawnedBy = Some _. This violates BOTH clause (b) (tenant
    // claims SpawnedBy) — clause (a) is satisfied. Predicate rejects.
    let mut cap: CapId = [0u8; 32];
    cap[0..6].copy_from_slice(b"forge2");
    let e = KernelEvent {
        event_id: 13,
        kind: Kind::Spawn,
        kernel_authored: false,
        spawned_by: Some(cap),
        retract_target: None,
        parents: vec![0],
    };
    assert!(!well_formed_spawned_by(&e));
}

// =====================================================================
// Property tests — randomized falsifier sweep over clause (a) and (b)
// =====================================================================

/// Strategy: generate a random EventId in [0, 100], a random parent
/// EventId in [0, 100], a random kind, kernel_authored bool, and an
/// optional spawned_by CapId; assert the predicate returns the
/// hand-computed truth value.
fn arb_kernel_event() -> impl Strategy<Value = KernelEvent> {
    (
        0u64..100,
        prop::collection::vec(0u64..100, 0..3),
        prop_oneof![Just(Kind::Other), Just(Kind::Spawn), Just(Kind::Retract)],
        any::<bool>(),
        prop::option::of(any::<u32>()),
    )
        .prop_map(|(event_id, parents, kind, kernel_authored, spawned_by_seed)| {
            let spawned_by = spawned_by_seed.map(|s| {
                let mut c: CapId = [0u8; 32];
                c[0..4].copy_from_slice(&s.to_le_bytes());
                c
            });
            KernelEvent {
                event_id,
                kind,
                kernel_authored,
                spawned_by,
                retract_target: None,
                parents,
            }
        })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 5_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 5×10³ random events: the predicate's return value matches the
    /// hand-computed truth value of (clause-a ∧ clause-b). Closes the
    /// σ_min structural sweep against `wellFormedSpawnedBy`.
    #[test]
    fn pt_well_formed_spawned_by_matches_truth_table(e in arb_kernel_event()) {
        let clause_a = !matches!(e.kind, Kind::Spawn) || e.spawned_by.is_some();
        let clause_b = e.kernel_authored || e.spawned_by.is_none();
        let expected = clause_a && clause_b;
        prop_assert_eq!(well_formed_spawned_by(&e), expected);
    }

    /// 5×10³ random spawn events with `spawned_by = None`: predicate
    /// MUST reject (clause (a) falsifier sweep).
    #[test]
    fn pt_spawn_without_spawnedby_always_rejected(
        event_id in 0u64..100,
        kernel_authored in any::<bool>(),
        parents in prop::collection::vec(0u64..100, 0..3),
    ) {
        let e = KernelEvent {
            event_id,
            kind: Kind::Spawn,
            kernel_authored,
            spawned_by: None,
            retract_target: None,
            parents,
        };
        prop_assert!(!well_formed_spawned_by(&e),
            "every Spawn event with SpawnedBy = none must be rejected");
    }

    /// 5×10³ random tenant-authored events with `spawned_by = Some _`:
    /// predicate MUST reject (clause (b) falsifier sweep).
    #[test]
    fn pt_tenant_with_spawnedby_always_rejected(
        event_id in 0u64..100,
        kind in prop_oneof![Just(Kind::Other), Just(Kind::Spawn), Just(Kind::Retract)],
        seed in any::<u32>(),
        parents in prop::collection::vec(0u64..100, 0..3),
    ) {
        let mut cap: CapId = [0u8; 32];
        cap[0..4].copy_from_slice(&seed.to_le_bytes());
        let e = KernelEvent {
            event_id,
            kind,
            kernel_authored: false, // <-- tenant
            spawned_by: Some(cap),
            retract_target: None,
            parents,
        };
        prop_assert!(!well_formed_spawned_by(&e),
            "every tenant-authored event with SpawnedBy = Some _ must be rejected");
    }
}

// =====================================================================
// Auditability: sanity-witness that all 3 PLAN.md falsifier shapes are
// covered.
// =====================================================================

#[test]
fn unit_item9_cross_cell_spawn_falsifier_coverage_3_of_3() {
    // Falsifier shape #1: spawn_without_spawnedby (clause (a)).
    let f1 = spawn_without_spawnedby();
    assert!(!well_formed_spawned_by(&f1));
    // Falsifier shape #2: tenant_self_spawn (clause (b)).
    let f2 = tenant_self_spawn(0);
    assert!(!well_formed_spawned_by(&f2));
    // Positive #3: kernel-authored spawn with SpawnedBy = Some _.
    let p3 = kernel_spawn_from_seed(0, 0, 0);
    assert!(well_formed_spawned_by(&p3));
    // 3-of-3 falsifier shapes structurally enumerated.
}

// Suppress unused-variable lints on EventId import (kept for type
// auditability of the test file's harness contract).
#[allow(dead_code)]
fn _typeof_eventid_marker() -> EventId {
    0
}
