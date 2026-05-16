//!
//! conformance σ_min structural layer. The predicate has three clauses:
//!
//! - clause (a): `kind = retract → retractTarget ≠ none`.
//! - clause (b): `retractTarget ∈ event.parents` (target is causally
//!   prior).
//! - clause (c): the event identified by `retractTarget` MUST NOT
//!   itself be a `retract` (terminal violation — `wellFormedRetraction`
//!   refuses retracting a retract event).
//!
//! ## H1 Definition — what each test asserts
//!
//! - `retract_without_target_rejected` — falsifies clause (a). A
//!   `retract` event with `retractTarget = none` MUST fail.
//! - `target_not_in_parents_rejected` — falsifies clause (b). A
//!   `retract` event with `retractTarget = Some t` where
//!   `t ∉ event.parents` MUST fail.
//! - `target_is_retract_rejected` — falsifies clause (c). A
//!   `retract` of a `retract` event (terminal violation) MUST fail.
//!
//! rebuttals)
//!
//! ### Attacks against `retract_without_target_rejected`
//!
//! 1. **Default-vacuity**: if `retractTarget = none` is silently
//!    accepted for retract-kind events, the predicate degenerates.
//!    **Rebuttal:** the test asserts `!well_formed_retraction(...)`
//!    on a constructed `Retract` event with `retract_target = None`;
//!    default-vacuity discipline).
//! 2. **Off-by-one in kind enum match (Other vs Retract)**: a buggy
//!    implementation might mis-route Retract events to the Other
//!    arm (which is vacuously true). **Rebuttal:** the positive arm
//!    `unit_kernel_retract_well_formed_accepted` would also pass
//!    when it should NOT exhibit the bug, but the negative
//!    `retract_without_target_rejected` would pass too (predicate
//!    returns `true` on a falsifier ⇒ test FAILS).
//! 3. **Empty-trace context with retract event**: would the
//!    predicate accept a retract event in an empty trace (target
//!    not in trace)? **Rebuttal:** No — clause (c) requires the
//!    target be in the trace AND not be a retract; absence of the
//!    target in trace fails clause (c). We exercise this in
//!    `unit_retract_target_not_in_trace_rejected` below.
//!
//! ### Attacks against `target_not_in_parents_rejected`
//!
//! 1. **Off-by-one EventId comparison**: a buggy `parents.contains`
//!    might match `target + 1` or `target - 1`. **Rebuttal:** the
//!    test constructs a falsifier with `target = 99` and `parents =
//!    [0, 1, 2]` — neither off-by-one matches.
//! 2. **`parents` containing the target's `event_id` but the target
//!    NOT in the trace**: vacuously parents-match. **Rebuttal:**
//!    clause (c) ALSO requires the target be in the trace context;
//!    parents-only-match is insufficient. We exercise this case to
//!    confirm clause (c) is checked even when (b) passes.
//! 3. **Multi-parent retract with target in some but not all
//!    parents**: does `parents.iter().any(target)` correctly check
//!    membership? **Rebuttal:** YES — `any` is the right primitive;
//!    we exercise multi-parent in
//!    `unit_retract_with_multi_parent_target_in_parents_accepted`.
//!
//! ### Attacks against `target_is_retract_rejected`
//!
//! 1. **Trace-not-found vs trace-target-is-retract**: do these two
//!    paths get distinguishable rejection? **Rebuttal:** at the
//!    σ_min layer both are clause (c) failures. The test exercises
//!    BOTH in `unit_retract_target_not_in_trace_rejected` and
//!    `target_is_retract_rejected`.
//! 2. **Idempotent retraction ( H2 attack 1)**: the σ_min
//!    attack 1 rebuttal). **Rebuttal:** we exercise the terminal-
//!    violation falsifier explicitly.
//! 3. **Self-retract (event retracts itself)**: an event with
//!    `event_id = e` and `retract_target = Some e` and `parents =
//!    [e]`. **Rebuttal:** if the event is itself a retract, clause
//!    (c) fails (target.kind = retract). We exercise this in
//!    `unit_retract_self_rejected`.
//!
//! ## DOCUMENTED-CAVEAT — L1+ TCB residual
//!
//! 1. **`event.parents` integrity**: at the σ_min structural layer
//!    `parents` is a free `Vec<EventId>`. The kernel-runtime
//!    obligation that `parents` reflects the actual happens-before
//!    field as the σ_min binding shape only.
//! 2. **`retract` of a non-existent EventId**: at σ_min layer this
//!    fails clause (c) (target not in trace). The L1+ kernel-runtime
//!    obligation that EventIds are kernel-assigned monotone is not
//!    structurally enforced here.

use ctrlmatrix_conformance::generators::{
    kernel_retract_from_seed, kernel_spawn_from_seed, tenant_other_event, well_formed_retraction,
    EventId, Kind, KernelEvent, Trace,
};
use proptest::prelude::*;

// =====================================================================
// Trace-context helpers
// =====================================================================

/// Build a small trace fixture: a Spawn event at id=0 (cap-mint
/// binding) and an Other-kind tenant event at id=1 (target candidate
/// for retraction).
fn fixture_trace_with_spawn_and_other() -> Trace {
    let spawn = kernel_spawn_from_seed(0, 0, 0xCAFE);
    let other = tenant_other_event(1, vec![0]);
    vec![spawn, other]
}

/// Build a trace fixture containing a retract event at id=2
/// retracting the Other event at id=1 (well-formed retraction).
fn fixture_trace_with_retract() -> Trace {
    let mut t = fixture_trace_with_spawn_and_other();
    let retract = kernel_retract_from_seed(2, 1);
    t.push(retract);
    t
}

// =====================================================================
// Falsifier shape #1 — retract_without_target_rejected (clause (a))
// =====================================================================

/// Construct a Retract event with `retract_target = None`.
fn retract_without_target() -> KernelEvent {
    KernelEvent {
        event_id: 99,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None, // <-- falsifier: clause (a) violation.
        parents: vec![1],
    }
}

#[test]
fn retract_without_target_rejected() {
    let trace = fixture_trace_with_spawn_and_other();
    let falsifier = retract_without_target();
    assert!(
        !well_formed_retraction(&falsifier, &trace),
        "wellFormedRetraction must reject Kind.retract with retractTarget = none (clause (a))"
    );
}

// =====================================================================
// Falsifier shape #2 — target_not_in_parents_rejected (clause (b))
// =====================================================================

/// Construct a Retract event whose `retract_target` is NOT in its
/// `parents` list. Clause (b) violation.
fn retract_target_not_in_parents() -> KernelEvent {
    KernelEvent {
        event_id: 99,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(1),  // target = 1...
        parents: vec![0, 50, 51], // ...but parents = {0, 50, 51}.
    }
}

#[test]
fn target_not_in_parents_rejected() {
    let trace = fixture_trace_with_spawn_and_other();
    let falsifier = retract_target_not_in_parents();
    assert!(
        !well_formed_retraction(&falsifier, &trace),
        "wellFormedRetraction must reject when retractTarget ∉ parents (clause (b))"
    );
}

// =====================================================================
// Falsifier shape #3 — target_is_retract_rejected (clause (c))
// =====================================================================

/// Construct a Retract event whose `retract_target` is itself a
/// retract event in the trace context. Clause (c) terminal violation.
fn retract_of_retract_event_id() -> EventId {
    // The fixture trace_with_retract has retract event at id=2.
    // Our new retract event will target id=2 (terminal violation).
    2
}

#[test]
fn target_is_retract_rejected() {
    let trace = fixture_trace_with_retract();
    // Construct a retract event targeting the EXISTING retract event
    // (id=2 in the fixture trace).
    let target = retract_of_retract_event_id();
    let falsifier = KernelEvent {
        event_id: 3,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(target),
        parents: vec![target],
    };
    assert!(
        !well_formed_retraction(&falsifier, &trace),
        "wellFormedRetraction must reject retract of a retract (clause (c) terminal violation)"
    );
}

// =====================================================================
// Positive arm — kernel_retract_well_formed_accepted
// =====================================================================

#[test]
fn unit_kernel_retract_well_formed_accepted() {
    let trace = fixture_trace_with_spawn_and_other();
    let positive = kernel_retract_from_seed(99, 1);
    assert!(
        well_formed_retraction(&positive, &trace),
        "wellFormedRetraction must accept retract of a non-retract event with target ∈ parents"
    );
}

// =====================================================================
// Cross-checks — clause coverage breadth
// =====================================================================

#[test]
fn unit_non_retract_event_is_vacuously_well_formed() {
    // A non-retract event vacuously satisfies wellFormedRetraction
    // (clause (a)'s antecedent is false; clauses (b) and (c) only
    // apply when kind = retract).
    let trace = fixture_trace_with_spawn_and_other();
    let other = tenant_other_event(50, vec![0]);
    assert!(well_formed_retraction(&other, &trace));
    let spawn = kernel_spawn_from_seed(51, 0, 1);
    assert!(well_formed_retraction(&spawn, &trace));
}

#[test]
fn unit_retract_target_not_in_trace_rejected() {
    // Clause (c) failure path: target is NOT in the trace at all.
    // The σ_min predicate rejects (clause (c)'s "target.kind ≠
    // retract" cannot be checked if target is missing — failure-
    // closed under the σ_min discipline).
    let trace = fixture_trace_with_spawn_and_other();
    let e = KernelEvent {
        event_id: 99,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(404), // target not in trace.
        parents: vec![404],
    };
    assert!(
        !well_formed_retraction(&e, &trace),
        "wellFormedRetraction rejects retract of a target absent from trace context"
    );
}

#[test]
fn unit_retract_with_multi_parent_target_in_parents_accepted() {
    // Multi-parent retract: parents = [0, 1, 5, 7]; target = 1;
    // target is in trace and is non-retract. Predicate accepts.
    let trace = fixture_trace_with_spawn_and_other();
    let e = KernelEvent {
        event_id: 99,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(1),
        parents: vec![0, 1, 5, 7],
    };
    assert!(well_formed_retraction(&e, &trace));
}

#[test]
fn unit_retract_self_rejected() {
    // Self-retract: an event with event_id = 7 and
    // retract_target = Some 7 in a trace where the trace's id-7
    // event is itself a retract. Clause (c) fails.
    let target = 7u64;
    let self_retract = KernelEvent {
        event_id: target,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(target),
        parents: vec![target],
    };
    let trace = vec![self_retract.clone()];
    assert!(
        !well_formed_retraction(&self_retract, &trace),
        "self-retract is rejected (target = self = retract ⇒ clause (c) violation)"
    );
}

#[test]
fn unit_retract_clause_a_passes_b_fails_c_passes() {
    // Tease apart clause failures: clause (a) holds (target
    // present), clause (b) fails (target NOT in parents), clause (c)
    // would hold (target is non-retract). Predicate rejects on (b).
    let trace = fixture_trace_with_spawn_and_other();
    let e = KernelEvent {
        event_id: 99,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(1),
        parents: vec![0], // <-- target=1 missing.
    };
    assert!(!well_formed_retraction(&e, &trace));
}

#[test]
fn unit_retract_clauses_a_b_pass_c_fails() {
    // Clauses (a) AND (b) hold; clause (c) fails (target is a
    // retract event in trace).
    let trace = fixture_trace_with_retract();
    let e = KernelEvent {
        event_id: 99,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(2), // <-- 2 is a retract in trace.
        parents: vec![2],
    };
    assert!(!well_formed_retraction(&e, &trace));
}

// =====================================================================
// Property tests — randomized 3-clause sweep
// =====================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 5_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 5×10³ random Retract events with `retractTarget = None`:
    /// predicate MUST reject (clause (a) sweep).
    #[test]
    fn pt_retract_without_target_always_rejected(
        event_id in 0u64..100,
        parents in prop::collection::vec(0u64..100, 0..3),
    ) {
        let trace = fixture_trace_with_spawn_and_other();
        let e = KernelEvent {
            event_id,
            kind: Kind::Retract,
            kernel_authored: true,
            spawned_by: None,
            retract_target: None,
            parents,
        };
        prop_assert!(!well_formed_retraction(&e, &trace));
    }

    /// 5×10³ random Retract events with target NOT in parents:
    /// predicate MUST reject (clause (b) sweep).
    #[test]
    fn pt_retract_target_not_in_parents_always_rejected(
        event_id in 100u64..200,
        target in 0u64..50,
    ) {
        // Construct parents that EXCLUDE target by mapping to a
        // disjoint range.
        let parents: Vec<EventId> = vec![target + 1000, target + 2000, target + 3000];
        let trace = fixture_trace_with_spawn_and_other();
        let e = KernelEvent {
            event_id,
            kind: Kind::Retract,
            kernel_authored: true,
            spawned_by: None,
            retract_target: Some(target),
            parents,
        };
        prop_assert!(!well_formed_retraction(&e, &trace));
    }

    /// 5×10³ random non-retract events: predicate MUST accept
    /// (vacuous arm sweep — clause (a) trivially holds).
    #[test]
    fn pt_non_retract_event_always_vacuously_accepted(
        event_id in 0u64..100,
        kernel_authored in any::<bool>(),
        parents in prop::collection::vec(0u64..100, 0..3),
        target_present in any::<bool>(),
    ) {
        let trace = fixture_trace_with_spawn_and_other();
        let retract_target = if target_present { Some(1u64) } else { None };
        let e = KernelEvent {
            event_id,
            kind: Kind::Other, // <-- non-retract.
            kernel_authored,
            spawned_by: None,
            retract_target,
            parents,
        };
        prop_assert!(well_formed_retraction(&e, &trace),
            "non-retract events vacuously satisfy wellFormedRetraction");
    }
}

// =====================================================================
// Auditability: sanity-witness that all 3 PLAN.md falsifier shapes are
// covered.
// =====================================================================

#[test]
fn unit_item9_cross_cell_retract_falsifier_coverage_3_of_3() {
    let trace_simple = fixture_trace_with_spawn_and_other();
    let trace_with_retract = fixture_trace_with_retract();
    // Falsifier shape #1: retract_without_target (clause (a)).
    let f1 = retract_without_target();
    assert!(!well_formed_retraction(&f1, &trace_simple));
    // Falsifier shape #2: target_not_in_parents (clause (b)).
    let f2 = retract_target_not_in_parents();
    assert!(!well_formed_retraction(&f2, &trace_simple));
    // Falsifier shape #3: target_is_retract (clause (c)).
    let target = retract_of_retract_event_id();
    let f3 = KernelEvent {
        event_id: 999,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(target),
        parents: vec![target],
    };
    assert!(!well_formed_retraction(&f3, &trace_with_retract));
    // 3-of-3 falsifier shapes structurally enumerated.
}
