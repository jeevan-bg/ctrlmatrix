//!
//! Tests `wellFormedTenantBinding` mirror of Agent G's Lean predicate
//! `Event.wellFormedTenantBinding` (lean/AgentKernel/Replay.lean
//! L837-846). Predicate is `(a) ∧ (b)`:
//! - clause (a): tenant equality when both committed; NO
//!   `kernelAuthored` escape.
//! - clause (b): tenant equality OR `kernelAuthored`.
//!
//!
//! PLAN line 318 expected "accept cross-tenant `kernelAuthored=true`".
//! Per LITERAL Lean clause (a) (Replay.lean L839-842) there is NO
//! `kernelAuthored` escape; cross-tenant kernel-authored is REJECTED
//! by clause (a). Rust mirror matches the LITERAL predicate per
//!
//! ## Scenarios (mirrors Agent G's  H2 #1/#2/#3 + structural
//! packaging vacuity)
//!
//! 1. Same-tenant spawn ACCEPT (kernel + tenant-authored arms).
//! 3. Cross-tenant tenant-authored REJECT (forgery; both clauses fail).
//! 4. Tenant-`None` ACCEPT default-vacuous.
//! 5. Composite 5-event trace at the trace lift.
//! 6. Phantom-parent-id arm vacuous (Agent G H2 #3).
//!
//! L1+. σ_min mirror caveat: Lean uses `Event.SpawnedBy : Option
//! EventId`; σ_min surface uses existing `parents : Vec<EventId>`.

use ctrlmatrix_conformance::generators::{
    cross_tenant_kernel_authored_event, cross_tenant_tenant_authored_event,
    same_tenant_spawn_event, tenant_none_event, trace_well_formed_tenant_binding,
    well_formed_tenant_binding, wrap_with_tenant, KernelEvent, KernelEventWithTenant, Kind,
    TenantId, TenantTrace,
};

const TENANT_T1: TenantId = 1;
const TENANT_T2: TenantId = 2;

/// Construct a parent event with an explicit tenant attribution.
fn parent_event_with_tenant(
    event_id: u64,
    tenant: Option<TenantId>,
    kernel_authored: bool,
) -> KernelEventWithTenant {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    wrap_with_tenant(inner, tenant)
}

// Scenario 1 — same-tenant spawn (must accept)

#[test]
fn same_tenant_kernel_authored_accepted() {
    let parent = parent_event_with_tenant(0, Some(TENANT_T1), true);
    let child = same_tenant_spawn_event(1, 0, 0xCAFE_BABE, TENANT_T1, true);
    let trace: TenantTrace = vec![parent, child.clone()];
    assert!(
        well_formed_tenant_binding(&trace, &child),
        "same-tenant kernel-authored spawn must accept"
    );
}

#[test]
fn same_tenant_tenant_authored_accepted() {
    let parent = parent_event_with_tenant(0, Some(TENANT_T1), true);
    let child = same_tenant_spawn_event(1, 0, 0xDEAD_BEEF, TENANT_T1, false);
    let trace: TenantTrace = vec![parent, child.clone()];
    assert!(
        well_formed_tenant_binding(&trace, &child),
        "same-tenant tenant-authored spawn must accept (clause (b) left disjunct)"
    );
}

// Scenario 2 — cross-tenant kernel-authored REJECT per literal Lean

#[test]
fn cross_tenant_kernel_authored_rejected_per_literal_lean() {
    // Per literal Lean clause (a) (Replay.lean L839-842), tenant
    // equality is required when both committed; NO kernel_authored
    // escape in clause (a). Rust mirrors literal predicate.
    let parent = parent_event_with_tenant(0, Some(TENANT_T1), true);
    let child = cross_tenant_kernel_authored_event(1, 0, 0xC0FFEE_42, TENANT_T2);
    let trace: TenantTrace = vec![parent, child.clone()];
    assert!(
        !well_formed_tenant_binding(&trace, &child),
        "cross-tenant spawn must reject even with kernel_authored = true (clause (a) failure; [ref] residual)"
    );
}

// Scenario 3 — cross-tenant tenant-authored REJECT (forgery)

#[test]
fn cross_tenant_tenant_authored_rejected() {
    let parent = parent_event_with_tenant(0, Some(TENANT_T1), true);
    let child = cross_tenant_tenant_authored_event(1, 0, 0xBAD_FACE, TENANT_T2);
    let trace: TenantTrace = vec![parent, child.clone()];
    assert!(
        !well_formed_tenant_binding(&trace, &child),
        "cross-tenant tenant-authored spawn must reject (forgery; both clauses fail)"
    );
}

// Scenario 4 — tenant-None default-vacuous ACCEPT

#[test]
fn tenant_none_child_with_kernel_authored_parent_accepted() {
    let parent = parent_event_with_tenant(0, Some(TENANT_T1), true);
    let child = tenant_none_event(1, 0, 0xFEED_BEEF);
    let trace: TenantTrace = vec![parent, child.clone()];
    assert!(
        well_formed_tenant_binding(&trace, &child),
        "tenant-None child with kernel-authored parent must accept (clause (a) vacuous; clause (b) right disjunct)"
    );
}

#[test]
fn tenant_none_both_sides_accepted() {
    let parent = parent_event_with_tenant(0, None, false);
    let child = tenant_none_event(1, 0, 0xABCD_EF01);
    let trace: TenantTrace = vec![parent, child.clone()];
    assert!(
        well_formed_tenant_binding(&trace, &child),
        "tenant-None on both sides must accept (clause (b) left disjunct)"
    );
}

// Scenario 5 — composite 5-event trace

#[test]
fn composite_trace_5_events() {
    // e0: parent T1 kernel-authored; e1: same-tenant kernel-authored
    // child; e2: cross-tenant kernel-authored T2 (REJECT); e3:
    // tenant-None child; e4: same-tenant tenant-authored child.
    let e0 = parent_event_with_tenant(0, Some(TENANT_T1), true);
    let e1 = same_tenant_spawn_event(1, 0, 0x1111_AAAA, TENANT_T1, true);
    let e2 = cross_tenant_kernel_authored_event(2, 0, 0x2222_BBBB, TENANT_T2);
    let e3 = tenant_none_event(3, 0, 0x3333_CCCC);
    let e4 = same_tenant_spawn_event(4, 0, 0x4444_DDDD, TENANT_T1, false);

    let trace: TenantTrace = vec![e0.clone(), e1.clone(), e2.clone(), e3.clone(), e4.clone()];

    assert!(well_formed_tenant_binding(&trace, &e0), "e0 (no parents) vacuous");
    assert!(well_formed_tenant_binding(&trace, &e1), "e1 same-tenant kernel-authored");
    assert!(!well_formed_tenant_binding(&trace, &e2), "e2 cross-tenant kernel-authored REJECT (clause (a))");
    assert!(well_formed_tenant_binding(&trace, &e3), "e3 tenant-None default-vacuous");
    assert!(well_formed_tenant_binding(&trace, &e4), "e4 same-tenant tenant-authored");

    assert!(
        !trace_well_formed_tenant_binding(&trace),
        "trace lift must reject because e2 violates clause (a)"
    );

    let trace_clean: TenantTrace = vec![e0, e1, e3, e4];
    assert!(
        trace_well_formed_tenant_binding(&trace_clean),
        "clean subtrace (no cross-tenant violations) must accept"
    );
}

// Scenario 6 — phantom-parent vacuity (Agent G H2 #3)

#[test]
fn phantom_parent_arm_vacuous_accepted() {
    let inner = KernelEvent {
        event_id: 1,
        kind: Kind::Spawn,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents: vec![99], // <-- phantom parent: no event with id 99 in trace.
    };
    let child = wrap_with_tenant(inner, Some(TENANT_T2));
    let trace: TenantTrace = vec![child.clone()];
    assert!(
        well_formed_tenant_binding(&trace, &child),
        "phantom parent_id arm vacuous (mirrors Lean p_event ∈ t membership conjunct)"
    );
}

// Auditability witness — 4 PLAN scenarios covered structurally

#[test]
fn unit_item9_cross_tenant_binding_coverage_4_of_4_scenarios() {
    let p1 = parent_event_with_tenant(0, Some(TENANT_T1), true);
    let s1 = same_tenant_spawn_event(1, 0, 1, TENANT_T1, true);
    let s2 = cross_tenant_kernel_authored_event(2, 0, 2, TENANT_T2);
    let s3 = cross_tenant_tenant_authored_event(3, 0, 3, TENANT_T2);
    let s4 = tenant_none_event(4, 0, 4);
    let trace: TenantTrace = vec![p1.clone(), s1.clone(), s2.clone(), s3.clone(), s4.clone()];
    assert!(well_formed_tenant_binding(&trace, &s1), "scenario 1 ACCEPT");
    assert!(!well_formed_tenant_binding(&trace, &s2), "scenario 2 REJECT (literal Lean)");
    assert!(!well_formed_tenant_binding(&trace, &s3), "scenario 3 REJECT (forgery)");
    assert!(well_formed_tenant_binding(&trace, &s4), "scenario 4 ACCEPT (vacuous)");
}
