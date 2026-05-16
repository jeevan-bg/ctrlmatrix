//! σ_min v1.8  payload-promotion falsifier tests
//!
//! Tests the three NEW σ_min wrapper-layer mirrors of v1.8 + Lean
//! substantive promotions:
//!
//! 1. `well_formed_human_gate_full` — 2-clause mirror of Lean's
//!    PROMOTED `Event.wellFormedHumanGate` (Replay.lean L1950-1960;
//!    1-clause `well_formed_human_gate` which is PRESERVED VERBATIM.
//!
//! 2. `well_formed_failure_mode` — 2-clause mirror of Lean
//!    `Event.wellFormedFailureMode` (Replay.lean L2073-2087; v1.8 
//!
//! 3. `well_formed_env_binding` — 2-clause mirror of Lean
//!    `Event.wellFormedEnvBinding` (Replay.lean L2211-2225; v1.8 
//!
//! ## H2 attack scenarios
//!
//! 1. Kernel-authored full-payload human-gate ACCEPT (positive).
//! 2. Kernel-authored human-gate WITHOUT context REJECT (clause (a)
//!    v1.8 substantive layer where v1.7  1-clause vacuously
//!    accepted).
//! 3. Tenant-authored full-payload human-gate REJECT (clause (b)
//! 4. Default-vacuity ACCEPT — non-`HumanGate` kind_ext with
//!    arbitrary payload trivially accepts.
//! 5. Trace-level lift POSITIVE — all-kernel-authored full-payload
//!    + non-humanGate baseline events all satisfy.
//! 6. Trace-level lift NEGATIVE — one missing-context forgery
//!    contaminates trace.
//!
//! 7. Kernel-authored byzantine failure ACCEPT (positive; clause (a)
//!    + clause (b) both pass at σ_min).
//! 8. Tenant-authored byzantine failure REJECT (clause (a) forgery
//!    defense; failureMode is cross-kind).
//! 9. Kernel-authored transient failure ACCEPT (positive; non-
//!    byzantine variants exercise clause (a) only).
//! 10. Tenant-authored permanent failure REJECT (clause (a) forgery
//!     defense across non-byzantine variants).
//! 11. Default-vacuity ACCEPT — non-failure event satisfies.
//! 12. Trace-level lift NEGATIVE — one tenant-forged failure
//!     contaminates trace.
//!
//! 13. Kernel-authored env-binding ACCEPT (positive; cross-kind).
//! 14. Tenant-authored env-binding REJECT (clause (a) forgery defense).
//! 15. Default-vacuity ACCEPT — non-env-binding event satisfies.
//! 16. Trace-level lift NEGATIVE — one tenant-forged env-binding
//!     contaminates trace.
//!
//! ## L1+ TCB residuals
//!
//!   `KernelOrTenant` 2-element enum.
//!   collapse at σ_min; substantive independence Lean-side at
//!   collapse at σ_min; substantive independence Lean-side at
//!   3-variant `FailureMode` enum.
//!   binding "keep flat TLA+ Event record".

use ctrlmatrix_conformance::generators::{
    human_gate_event_full, human_gate_event_missing_context, kernel_env_binding_event,
    kernel_failure_event, non_env_binding_event, non_failure_event, non_human_gate_event_full,
    tenant_env_binding_event, tenant_failure_event, tenant_human_gate_event_full,
    trace_well_formed_env_binding, trace_well_formed_failure_mode,
    trace_well_formed_human_gate_full, well_formed_env_binding, well_formed_failure_mode,
    well_formed_human_gate_full, EnvBindingTrace, FailureMode, FailureModeTrace,
    HumanGateFullTrace,
};

// =====================================================================
// =====================================================================

// Scenario 1 — kernel-authored full-payload human-gate ACCEPT (positive)

#[test]
fn kernel_authored_human_gate_full_accepted() {
    let e = human_gate_event_full(0);
    assert!(
        well_formed_human_gate_full(&e),
        "kernel-authored full-payload human-gate event must satisfy \
         well_formed_human_gate_full (mirrors Lean PROMOTED \
         wellFormedHumanGate positive arm: clauses (a) field-presence \
         + (b) kernel-authorship both hold)"
    );
}

// Scenario 2 — kernel-authored human-gate WITHOUT context REJECT

#[test]
fn kernel_authored_human_gate_missing_context_rejected() {
    let e = human_gate_event_missing_context(0);
    assert!(
        !well_formed_human_gate_full(&e),
        "kernel-authored human-gate event without HumanGateRecord context \
         MUST violate well_formed_human_gate_full (clause (a) field-presence \
         is the v1.8  [ref] PROMOTION substantive arm; this scenario \
         was vacuously accepted at v1.7  1-clause but REJECTED at v1.8  \
         substantive PREDICATE-LOAD-BEARING framework)"
    );
}

// Scenario 3 — tenant-authored full-payload human-gate REJECT

#[test]
fn tenant_authored_human_gate_full_rejected() {
    let e = tenant_human_gate_event_full(0);
    assert!(
        !well_formed_human_gate_full(&e),
        "tenant-authored full-payload human-gate event MUST violate \
         well_formed_human_gate_full (mirrors Lean [ref] forgery defense; \
         clause (b) kernel-authorship preserved from v1.7  / [ref] \
         under the v1.8  [ref] PROMOTION; tenant cannot forge human-\
         assent records)"
    );
}

// Scenario 4 — default-vacuity ACCEPT (non-`HumanGate` kind_ext)

#[test]
fn non_human_gate_event_full_default_accepted() {
    // Non-HumanGate kind_ext + tenant-authored: vacuously accepted.
    let e_tenant = non_human_gate_event_full(0, false);
    assert!(
        well_formed_human_gate_full(&e_tenant),
        "non-HumanGate event with tenant-authored MUST vacuously accept \
         (mirrors Lean wellFormedHumanGate_default_event_holds; both \
         clauses' antecedents kind_ext = HumanGate fail ⇒ implications hold)"
    );
    // Non-HumanGate kind_ext + kernel-authored: vacuously accepted.
    let e_kernel = non_human_gate_event_full(1, true);
    assert!(
        well_formed_human_gate_full(&e_kernel),
        "non-HumanGate event with kernel-authored MUST vacuously accept \
         (default-vacuity holds regardless of authorship for non-HumanGate \
         kind_ext)"
    );
}

// Scenario 5 — trace-level lift POSITIVE

#[test]
fn trace_all_kernel_authored_human_gate_full_accepted() {
    let trace: HumanGateFullTrace = vec![
        human_gate_event_full(0),
        human_gate_event_full(1),
        non_human_gate_event_full(2, false),
    ];
    assert!(
        trace_well_formed_human_gate_full(&trace),
        "trace of kernel-authored full-payload human-gate events + \
         non-HumanGate baseline event MUST satisfy \
         trace_well_formed_human_gate_full (mirrors Lean \
         Trace.wellFormedHumanGate ∀-shape positive case)"
    );
}

// Scenario 6 — trace-level lift NEGATIVE (missing-context forgery
// contaminates trace)

#[test]
fn trace_one_human_gate_missing_context_rejected() {
    let trace: HumanGateFullTrace = vec![
        human_gate_event_full(0),
        human_gate_event_missing_context(1), // clause (a) violator
        human_gate_event_full(2),
    ];
    assert!(
        !trace_well_formed_human_gate_full(&trace),
        "trace containing one missing-context human-gate event MUST fail \
         trace_well_formed_human_gate_full (∀-quantifier flips on first \
         clause (a) failure; mirrors v1.8  [ref] substantive PROMOTION)"
    );
}

// =====================================================================
// =====================================================================

// Scenario 7 — kernel-authored byzantine failure ACCEPT (positive)

#[test]
fn kernel_authored_byzantine_failure_accepted() {
    let e = kernel_failure_event(0, FailureMode::Byzantine);
    assert!(
        well_formed_failure_mode(&e),
        "kernel-authored byzantine failure event must satisfy \
         well_formed_failure_mode (clause (a) forgery defense passes; \
         clause (b) byzantine kernelAuthored discriminator passes at \
         σ_min via clause-collapse per [ref]\
         collapse-σmin; substantive independence at Lean side per \
         [ref])"
    );
}

// Scenario 8 — tenant-authored byzantine failure REJECT (clause (a)
// forgery defense)

#[test]
fn tenant_authored_byzantine_failure_rejected() {
    let e = tenant_failure_event(0, FailureMode::Byzantine);
    assert!(
        !well_formed_failure_mode(&e),
        "tenant-authored byzantine failure event MUST violate \
         well_formed_failure_mode (clause (a) forgery defense; \
         tenants cannot forge kernel-attested failure records)"
    );
}

// Scenario 9 — kernel-authored transient failure ACCEPT (positive
// across non-byzantine variants)

#[test]
fn kernel_authored_transient_failure_accepted() {
    let e = kernel_failure_event(0, FailureMode::Transient);
    assert!(
        well_formed_failure_mode(&e),
        "kernel-authored transient failure event must satisfy \
         well_formed_failure_mode (clause (a) passes; clause (b) \
         vacuously holds for non-byzantine variants — antecedent \
         FailureMode = Byzantine fails)"
    );
}

// Scenario 10 — tenant-authored permanent failure REJECT (clause (a)
// forgery defense universal)

#[test]
fn tenant_authored_permanent_failure_rejected() {
    let e = tenant_failure_event(0, FailureMode::Permanent);
    assert!(
        !well_formed_failure_mode(&e),
        "tenant-authored permanent failure event MUST violate \
         well_formed_failure_mode (clause (a) forgery defense fires \
         universally across all FailureMode variants; failure \
         attestation is cross-kind kernel-only)"
    );
}

// Scenario 11 — default-vacuity ACCEPT (no failure record)

#[test]
fn non_failure_event_default_accepted() {
    // No failure record + tenant-authored: vacuously accepted.
    let e_tenant = non_failure_event(0, false);
    assert!(
        well_formed_failure_mode(&e_tenant),
        "event without failure record + tenant-authored MUST vacuously \
         accept well_formed_failure_mode (both clauses' antecedents \
         require failure_record.is_some(); they fail ⇒ implications hold)"
    );
    // No failure record + kernel-authored: also vacuously accepted.
    let e_kernel = non_failure_event(1, true);
    assert!(
        well_formed_failure_mode(&e_kernel),
        "event without failure record + kernel-authored MUST vacuously accept"
    );
}

// Scenario 12 — trace-level lift NEGATIVE (one tenant-forged failure
// contaminates trace)

#[test]
fn trace_one_tenant_forged_failure_rejected() {
    let trace: FailureModeTrace = vec![
        kernel_failure_event(0, FailureMode::Byzantine),
        tenant_failure_event(1, FailureMode::Permanent), // forgery
        non_failure_event(2, true),
    ];
    assert!(
        !trace_well_formed_failure_mode(&trace),
        "trace containing one tenant-forged failure event MUST fail \
         trace_well_formed_failure_mode (∀-quantifier flips on first \
         clause (a) failure; [ref] forgery defense at trace level)"
    );
}

// =====================================================================
// =====================================================================

// Scenario 13 — kernel-authored env-binding ACCEPT (positive)

#[test]
fn kernel_authored_env_binding_accepted() {
    let e = kernel_env_binding_event(0, 0xdeadbeef);
    assert!(
        well_formed_env_binding(&e),
        "kernel-authored env-binding event must satisfy \
         well_formed_env_binding (clause (a) forgery defense passes; \
         clause (b) universal kernelAuthored discriminator passes at \
         σ_min via clause-collapse per [ref]\
         collapse-σmin; substantive independence at Lean side per \
         [ref]Authored-substantive)"
    );
}

// Scenario 14 — tenant-authored env-binding REJECT (clause (a)
// forgery defense)

#[test]
fn tenant_authored_env_binding_rejected() {
    let e = tenant_env_binding_event(0, 0xdeadbeef);
    assert!(
        !well_formed_env_binding(&e),
        "tenant-authored env-binding event MUST violate \
         well_formed_env_binding (clause (a) forgery defense; \
         tenants cannot forge kernel-attested env-digest records; \
         absorbs v1.5  [ref] SystemEvent.tenant via substitution \
)"
    );
}

// Scenario 15 — default-vacuity ACCEPT (no env-digest record)

#[test]
fn non_env_binding_event_default_accepted() {
    let e_tenant = non_env_binding_event(0, false);
    assert!(
        well_formed_env_binding(&e_tenant),
        "event without env-digest record + tenant-authored MUST \
         vacuously accept well_formed_env_binding (both clauses' \
         antecedents require env_digest_record.is_some(); they fail \
         ⇒ implications hold)"
    );
    let e_kernel = non_env_binding_event(1, true);
    assert!(
        well_formed_env_binding(&e_kernel),
        "event without env-digest record + kernel-authored MUST vacuously accept"
    );
}

// Scenario 16 — trace-level lift NEGATIVE (one tenant-forged
// env-binding contaminates trace)

#[test]
fn trace_one_tenant_forged_env_binding_rejected() {
    let trace: EnvBindingTrace = vec![
        kernel_env_binding_event(0, 0x1111),
        tenant_env_binding_event(1, 0x2222), // forgery
        kernel_env_binding_event(2, 0x3333),
    ];
    assert!(
        !trace_well_formed_env_binding(&trace),
        "trace containing one tenant-forged env-binding event MUST fail \
         trace_well_formed_env_binding (∀-quantifier flips on first \
         clause (a) failure; [ref] env-digest forgery defense at trace level)"
    );
}

// =====================================================================
// =====================================================================
//
// ~5–6 NEW property tests covering `well_formed_human_gate_full` +
// `well_formed_env_binding` + `well_formed_failure_mode` (σ_min
// substantive 2-clause predicates. Existing 16 example-based scenarios
// above are PRESERVED.

use ctrlmatrix_conformance::generators::{
    well_formed_env_binding_substantive, well_formed_failure_mode_substantive, EnvDigestRecord,
    FailureRecord, HumanGateRecord, KernelEvent, KernelEventLatest, Kind,
};
use proptest::prelude::*;

fn strategy_failure_mode() -> impl Strategy<Value = FailureMode> {
    prop_oneof![
        Just(FailureMode::Transient),
        Just(FailureMode::Permanent),
        Just(FailureMode::Byzantine),
    ]
}

proptest! {

    /// Property 1 (HumanGateFull clause (a) — kernel-authored
    /// human-gate WITHOUT context REJECTED).
    #[test]
    fn prop_human_gate_full_missing_context_rejected(
        event_id in 0u64..1000,
    ) {
        let e = human_gate_event_missing_context(event_id);
        prop_assert!(!well_formed_human_gate_full(&e));
    }

    /// Property 2 (HumanGateFull clause (b) — tenant-authored
    /// human-gate REJECTED regardless of context).
    #[test]
    fn prop_human_gate_full_tenant_authored_rejected(
        event_id in 0u64..1000,
    ) {
        let e = tenant_human_gate_event_full(event_id);
        prop_assert!(!well_formed_human_gate_full(&e));
    }

    /// Property 3 (FailureMode σ_min — kernel-authored failure
    /// ALWAYS accepted).
    #[test]
    fn prop_failure_mode_kernel_authored_accepted(
        event_id in 0u64..1000,
        mode in strategy_failure_mode(),
    ) {
        let e = kernel_failure_event(event_id, mode);
        prop_assert!(well_formed_failure_mode(&e));
    }

    /// Property 4 (FailureMode σ_min — tenant-authored failure
    /// ALWAYS rejected).
    #[test]
    fn prop_failure_mode_tenant_authored_rejected(
        event_id in 0u64..1000,
        mode in strategy_failure_mode(),
    ) {
        let e = tenant_failure_event(event_id, mode);
        prop_assert!(!well_formed_failure_mode(&e));
    }

    /// Property 5 (EnvBinding σ_min — tenant-authored env-binding
    /// ALWAYS rejected).
    #[test]
    fn prop_env_binding_tenant_authored_rejected(
        event_id in 0u64..1000,
        digest in 1u64..1_000_000,
    ) {
        let e = tenant_env_binding_event(event_id, digest);
        prop_assert!(!well_formed_env_binding(&e));
    }

    /// Property 6 (EnvBinding σ_min — kernel-authored env-binding
    /// ALWAYS accepted).
    #[test]
    fn prop_env_binding_kernel_authored_accepted(
        event_id in 0u64..1000,
        digest in 1u64..1_000_000,
    ) {
        let e = kernel_env_binding_event(event_id, digest);
        prop_assert!(well_formed_env_binding(&e));
    }


    /// `failure_record = Some(_) ∧ kernel_authored = false`).
    #[test]
    fn prop_substantive_failure_mode_tenant_rejected(
        event_id in 0u64..1000,
        mode in strategy_failure_mode(),
    ) {
        let e = tenant_failure_event(event_id, mode);
        prop_assert!(!well_formed_failure_mode_substantive(&e));
    }

    /// `env_digest_record = Some(_) ∧ kernel_authored = false`).
    #[test]
    fn prop_substantive_env_binding_tenant_rejected(
        event_id in 0u64..1000,
        digest in 1u64..1_000_000,
    ) {
        let e = tenant_env_binding_event(event_id, digest);
        prop_assert!(!well_formed_env_binding_substantive(&e));
    }

    /// empty/zero digest even when kernel-authored).
    #[test]
    fn prop_substantive_env_binding_zero_digest_rejected(
        event_id in 0u64..1000,
    ) {
        // Construct a kernel-authored env-binding event with digest = 0
        // (the substantive clause (a) sentinel for "empty digest").
        let inner = KernelEvent {
            event_id,
            kind: Kind::Other,
            kernel_authored: true,
            spawned_by: None,
            retract_target: None,
            parents: vec![],
        };
        let e = KernelEventLatest {
            event: inner,
            env_digest_record: Some(EnvDigestRecord { digest: 0 }),
            ..Default::default()
        };
        // σ_min collapsed form ACCEPTS (only checks kernel_authored).
        prop_assert!(well_formed_env_binding(&e));
        // Substantive 2-clause REJECTS due to clause (a) zero-digest.
        prop_assert!(!well_formed_env_binding_substantive(&e));
    }

    /// is at least as strict as σ_min for `failure_mode`; never
    /// strictly weaker).
    #[test]
    fn prop_substantive_failure_at_least_as_strict_as_sigma_min(
        event_id in 0u64..1000,
        kernel_authored in any::<bool>(),
        mode in strategy_failure_mode(),
        with_record in any::<bool>(),
    ) {
        let inner = KernelEvent {
            event_id,
            kind: Kind::Other,
            kernel_authored,
            spawned_by: None,
            retract_target: None,
            parents: vec![],
        };
        let e = KernelEventLatest {
            event: inner,
            failure_record: if with_record {
                Some(FailureRecord { mode })
            } else {
                None
            },
            ..Default::default()
        };
        let sigma = well_formed_failure_mode(&e);
        let subst = well_formed_failure_mode_substantive(&e);
        // Substantive ⇒ σ_min (substantive at-least-as-strict).
        if subst {
            prop_assert!(sigma, "substantive accept must imply σ_min accept");
        }
    }

    /// is at least as strict as σ_min for `env_binding`; never
    /// strictly weaker).
    #[test]
    fn prop_substantive_env_binding_at_least_as_strict_as_sigma_min(
        event_id in 0u64..1000,
        kernel_authored in any::<bool>(),
        digest in 0u64..1_000_000,
        with_record in any::<bool>(),
    ) {
        let inner = KernelEvent {
            event_id,
            kind: Kind::Other,
            kernel_authored,
            spawned_by: None,
            retract_target: None,
            parents: vec![],
        };
        let e = KernelEventLatest {
            event: inner,
            env_digest_record: if with_record {
                Some(EnvDigestRecord { digest })
            } else {
                None
            },
            ..Default::default()
        };
        let sigma = well_formed_env_binding(&e);
        let subst = well_formed_env_binding_substantive(&e);
        if subst {
            prop_assert!(sigma, "substantive accept must imply σ_min accept");
        }
    }

    /// the canonical positive constructor outputs).
    #[test]
    fn prop_substantive_canonical_positive_accepted(
        event_id in 0u64..1000,
        mode in strategy_failure_mode(),
        digest in 1u64..1_000_000,
    ) {
        let e_failure = kernel_failure_event(event_id, mode);
        prop_assert!(well_formed_failure_mode_substantive(&e_failure));
        let e_env = kernel_env_binding_event(event_id, digest);
        prop_assert!(well_formed_env_binding_substantive(&e_env));
    }

    // (Reference HumanGateRecord here so the import is exercised
    // — keeps `rustc unused_imports` quiet.)
    /// Sanity property: HumanGateRecord default constructs with
    /// `decision_outcome = false`.
    #[test]
    fn prop_human_gate_record_default_decision_outcome_false(
        _seed in 0u64..1000,
    ) {
        let r = HumanGateRecord::default();
        prop_assert!(!r.decision_outcome);
    }
}
