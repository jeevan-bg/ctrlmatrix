//! extension).
//!
//! Tests `well_formed_plan_exec` mirror of Lean predicate
//! `Event.wellFormedPlanExec` (lean/AgentKernel/Replay.lean
//! L1079-1084). Trace-parameterized 2-clause predicate:
//!
//! - Clause (a): `kind = .plan ∧ linkedExecId = some eid → ∃ e' ∈ t,
//!   e'.id = eid ∧ e'.kind = .exec` — when a plan event commits to a
//!   link, the link must resolve to an exec event in the trace.
//! - Clause (b): `kind ≠ .plan → linkedExecId = none` — only plan
//!   events carry `linkedExecId` (forgery defense for non-plan kinds).
//!
//!
//! 1. Default-vacuous accept (legacy `Other`-kind, no link, mirrors
//!    `wellFormedPlanExec_default_event_holds`).
//!    L0 spec is structural per-event link, NOT longitudinal liveness;
//!    plan-without-exec is L1+ deployment policy).
//! 3. Plan with `linkedExecId = Some(eid)` resolving to an Exec event
//!    in trace ACCEPT.
//! 4. Plan with `linkedExecId = Some(eid)` where eid not in trace
//!    REJECT (clause (a) dangling-link forgery).
//! 5. Plan with `linkedExecId = Some(eid)` where eid resolves to a
//!    NON-Exec event REJECT (clause (a) wrong-target-kind).
//!    deferred to v1.7+; `e'.kind = .exec` strictly).
//! 7. Non-plan event with `linkedExecId = Some(_)` REJECT (clause (b)
//!    forgery).
//!
//! (hierarchical-planning `Kind.subPlan` deferred).

use ctrlmatrix_conformance::generators::{
    exec_event, other_event_with_link, plan_event, trace_well_formed_plan_exec,
    well_formed_plan_exec, KernelEvent, Kind, KindExt, KernelEventWithPlanExec, PlanExecTrace,
};

/// Helper: construct a baseline non-plan, non-exec wrapper event.
fn baseline_other_event(event_id: u64) -> KernelEventWithPlanExec {
    other_event_with_link(event_id, None)
}

// Scenario 1 — default-vacuous accept

#[test]
fn default_other_kind_no_link_accepted() {
    let e = baseline_other_event(0);
    let trace: PlanExecTrace = vec![e.clone()];
    assert!(
        well_formed_plan_exec(&trace, &e),
        "default Other-kind event with no link must vacuously accept \
         (mirrors Lean wellFormedPlanExec_default_event_holds)"
    );
}

// Scenario 2 — plan with `linkedExecId = None` ACCEPT
// longitudinal liveness.

#[test]
fn plan_with_none_link_accepted() {
    let e = plan_event(0, None);
    let trace: PlanExecTrace = vec![e.clone()];
    assert!(
        well_formed_plan_exec(&trace, &e),
        "plan event with linked_exec_id = None must accept \
"
    );
}

// Scenario 3 — plan with linkedExecId resolving to Exec ACCEPT

#[test]
fn plan_with_resolving_exec_link_accepted() {
    let exec = exec_event(42);
    let plan = plan_event(0, Some(42));
    let trace: PlanExecTrace = vec![plan.clone(), exec];
    assert!(
        well_formed_plan_exec(&trace, &plan),
        "plan event linking to a present Exec event must accept \
         (clause (a) resolved)"
    );
}

// Scenario 4 — plan with dangling link REJECT (clause (a) falsifier)

#[test]
fn plan_dangling_link_rejected() {
    // linked_exec_id = Some(99), but event 99 not in trace.
    let plan = plan_event(0, Some(99));
    let trace: PlanExecTrace = vec![plan.clone()];
    assert!(
        !well_formed_plan_exec(&trace, &plan),
        "plan event with dangling linked_exec_id (target not in trace) \
         MUST be rejected by clause (a)"
    );
}

// Scenario 5 — plan linking to a non-Exec event REJECT (clause (a))

#[test]
fn plan_links_to_non_exec_rejected() {
    // Event 42 exists but is Other-kind, not Exec.
    let other = other_event_with_link(42, None);
    let plan = plan_event(0, Some(42));
    let trace: PlanExecTrace = vec![plan.clone(), other];
    assert!(
        !well_formed_plan_exec(&trace, &plan),
        "plan event linking to a non-Exec target MUST be rejected by clause (a) \
         (e'.kind = .exec required strictly)"
    );
}


#[test]
fn plan_plan_loop_rejected() {
    // Plan event 0 links to plan event 1 (NOT exec).
    let plan_target = plan_event(1, None);
    let plan = plan_event(0, Some(1));
    let trace: PlanExecTrace = vec![plan.clone(), plan_target];
    assert!(
        !well_formed_plan_exec(&trace, &plan),
        "plan-plan link MUST be rejected by clause (a) \
"
    );
}

// Scenario 7 — non-plan event with linkedExecId REJECT (clause (b))

#[test]
fn non_plan_with_link_rejected() {
    // Other-kind event with linked_exec_id = Some(_) — clause (b) falsifier.
    let other = other_event_with_link(0, Some(42));
    let exec = exec_event(42);
    let trace: PlanExecTrace = vec![other.clone(), exec];
    assert!(
        !well_formed_plan_exec(&trace, &other),
        "non-plan event with linked_exec_id = Some(_) MUST be rejected by clause (b) \
         (forgery defense: only plan events carry linked_exec_id)"
    );
}

#[test]
fn exec_event_with_no_link_accepted() {
    // Exec event itself has linked_exec_id = None per constructor;
    // clause (b) consequent holds (kind_ext = Exec ≠ Plan ⇒ link = None).
    let exec = exec_event(42);
    let trace: PlanExecTrace = vec![exec.clone()];
    assert!(
        well_formed_plan_exec(&trace, &exec),
        "exec event with linked_exec_id = None must accept (clause (b) trivial)"
    );
}

// Scenario 8 — composite trace at trace lift

#[test]
fn composite_trace_well_formed_at_trace_lift() {
    // Mixed trace: 2 plan-exec pairs + a baseline event.
    // Plan 0 → Exec 1; Plan 2 → Exec 3; baseline Other event 4.
    let trace: PlanExecTrace = vec![
        plan_event(0, Some(1)),
        exec_event(1),
        plan_event(2, Some(3)),
        exec_event(3),
        baseline_other_event(4),
    ];
    assert!(
        trace_well_formed_plan_exec(&trace),
        "composite trace with resolved plan-exec pairs must accept at trace lift"
    );
}

#[test]
fn composite_trace_with_dangling_plan_rejected_at_trace_lift() {
    // Plan event 5 links to non-existent event 99.
    let trace: PlanExecTrace = vec![
        plan_event(0, Some(1)),
        exec_event(1),
        plan_event(5, Some(99)), // dangling
    ];
    assert!(
        !trace_well_formed_plan_exec(&trace),
        "trace containing a dangling-link plan event MUST be rejected at trace lift"
    );
}

// Defensive: confirm head-963 KernelEvent + Kind interop is preserved
// (the wrapper threads the inner KernelEvent through; we exercise the
// inner field flow to ensure the wrapper does NOT depend on edits to
// head-963 surface).

#[test]
fn wrapper_inner_kernel_event_preserved() {
    let inner = KernelEvent {
        event_id: 7,
        kind: Kind::Spawn,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    let wrapped = KernelEventWithPlanExec {
        event: inner.clone(),
        kind_ext: KindExt::Other,
        linked_exec_id: None,
        // `pub type` alias to the unified `KernelEventLatest`; the
        // remaining wrapper-extension fields default-construct via
        // struct-update syntax.
        ..Default::default()
    };
    assert_eq!(
        wrapped.event, inner,
        "wrapper preserves inner KernelEvent byte-equivalence"
    );
}

// =====================================================================
// =====================================================================
//
// ~6–8 NEW property tests covering `well_formed_plan_exec`'s 2-clause
// shape. Existing 8 example-based scenarios above are PRESERVED
// replacement" binding). proptest config defaults (256 cases per
// property).

use proptest::prelude::*;

/// Strategy: deterministic `KernelEvent` with `Kind::Other`,
/// kernel-authored randomized, no spawn/retract side-data.
fn strategy_inner_event() -> impl Strategy<Value = ctrlmatrix_conformance::generators::KernelEvent> {
    (0u64..1000, any::<bool>()).prop_map(|(event_id, kernel_authored)| {
        ctrlmatrix_conformance::generators::KernelEvent {
            event_id,
            kind: Kind::Other,
            kernel_authored,
            spawned_by: None,
            retract_target: None,
            parents: vec![],
        }
    })
}

/// Strategy: a unified plan-exec event with random `kind_ext` and
/// `linked_exec_id`.
fn strategy_plan_exec_event(
) -> impl Strategy<Value = KernelEventWithPlanExec> {
    let kind_ext_strategy = prop_oneof![
        Just(KindExt::Other),
        Just(KindExt::Plan),
        Just(KindExt::Exec),
        Just(KindExt::Spawn),
        Just(KindExt::Retract),
    ];
    let link_strategy = prop_oneof![Just::<Option<u64>>(None), (0u64..1000).prop_map(Some)];
    (strategy_inner_event(), kind_ext_strategy, link_strategy).prop_map(
        |(event, kind_ext, linked_exec_id)| KernelEventWithPlanExec {
            event,
            kind_ext,
            linked_exec_id,
            ..Default::default()
        },
    )
}

proptest! {
    /// Property 1 (clause (a) positive arm): plan events with a
    /// link that resolves to a present Exec event MUST be accepted.
    #[test]
    fn prop_plan_resolving_exec_accepted(
        plan_id in 0u64..500,
        exec_id in 500u64..1000,
    ) {
        let exec = exec_event(exec_id);
        let plan = plan_event(plan_id, Some(exec_id));
        let trace: PlanExecTrace = vec![plan.clone(), exec];
        prop_assert!(well_formed_plan_exec(&trace, &plan));
    }

    /// Property 2 (clause (a) inverse): plan events with a dangling
    /// link (target not in trace) MUST be rejected.
    #[test]
    fn prop_plan_dangling_link_rejected(
        plan_id in 0u64..500,
        dangle_id in 500u64..1000,
    ) {
        // Construct trace WITHOUT the dangle_id target.
        let plan = plan_event(plan_id, Some(dangle_id));
        let trace: PlanExecTrace = vec![plan.clone()];
        prop_assert!(!well_formed_plan_exec(&trace, &plan));
    }

    /// Property 3 (clause (b) positive arm): non-plan events with
    /// `linked_exec_id = None` MUST be accepted.
    #[test]
    fn prop_non_plan_no_link_accepted(event_id in 0u64..1000) {
        let other = other_event_with_link(event_id, None);
        let trace: PlanExecTrace = vec![other.clone()];
        prop_assert!(well_formed_plan_exec(&trace, &other));
    }

    /// Property 4 (clause (b) inverse): non-plan events with
    /// `linked_exec_id = Some(_)` MUST be rejected.
    #[test]
    fn prop_non_plan_with_link_rejected(
        event_id in 0u64..1000,
        link_target in 0u64..1000,
    ) {
        let other = other_event_with_link(event_id, Some(link_target));
        let trace: PlanExecTrace = vec![other.clone()];
        prop_assert!(!well_formed_plan_exec(&trace, &other));
    }

    /// Property 5 (trace-extending monotonicity): a trace of all-
    /// well-formed plan/exec/other events at the per-event predicate
    /// MUST satisfy the trace-level lift.
    #[test]
    fn prop_trace_all_well_formed_implies_trace_lift(
        events_count in 1usize..6,
    ) {
        // Build a trace of `events_count` baseline other events
        // (vacuously well-formed at per-event predicate).
        let trace: PlanExecTrace = (0..events_count as u64)
            .map(|i| other_event_with_link(i, None))
            .collect();
        prop_assert!(trace_well_formed_plan_exec(&trace));
    }

    /// linking to another plan event MUST be rejected (clause (a)
    /// requires `e'.kind_ext = Exec` strictly).
    #[test]
    fn prop_plan_links_to_plan_rejected(
        plan_a_id in 0u64..500,
        plan_b_id in 500u64..1000,
    ) {
        let plan_b = plan_event(plan_b_id, None);
        let plan_a = plan_event(plan_a_id, Some(plan_b_id));
        let trace: PlanExecTrace = vec![plan_a.clone(), plan_b];
        prop_assert!(!well_formed_plan_exec(&trace, &plan_a));
    }

    /// Property 7 (composite trace contamination): a trace containing
    /// any forgery event MUST be rejected at the trace lift.
    #[test]
    fn prop_trace_with_forgery_rejected(
        good_id in 0u64..500,
        bad_id in 500u64..900,
        link_target in 900u64..1000,
    ) {
        prop_assume!(good_id != bad_id);
        let trace: PlanExecTrace = vec![
            other_event_with_link(good_id, None),
            other_event_with_link(bad_id, Some(link_target)), // clause (b) forgery
        ];
        prop_assert!(!trace_well_formed_plan_exec(&trace));
    }

    /// Property 8 (random event predicate matches semantic
    /// expectation): for any randomly-generated plan-exec event,
    /// the predicate disposition matches a literal re-implementation
    /// of the 2-clause rule.
    #[test]
    fn prop_predicate_matches_literal_semantics(
        e in strategy_plan_exec_event(),
    ) {
        let trace: PlanExecTrace = vec![e.clone()];
        let actual = well_formed_plan_exec(&trace, &e);
        // Literal re-implementation: clause (a) is vacuous (no other
        // events in trace, so plan with Some(_) link cannot resolve);
        // clause (b) requires kind_ext != Plan → linked_exec_id == None.
        let clause_b_holds = e.kind_ext == KindExt::Plan || e.linked_exec_id.is_none();
        let clause_a_holds = match (e.kind_ext, e.linked_exec_id) {
            (KindExt::Plan, Some(_)) => false, // singleton trace → dangle
            _ => true,
        };
        let expected = clause_a_holds && clause_b_holds;
        prop_assert_eq!(actual, expected);
    }
}
