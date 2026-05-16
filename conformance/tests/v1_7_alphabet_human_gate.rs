//!
//! Tests `well_formed_human_gate` mirror of Lean predicate
//! `Event.wellFormedHumanGate` (lean/AgentKernel/Replay.lean
//! L1583-1586). 1-clause predicate (Route (c) STRUCTURAL PACKAGING
//!
//! - Clause: `kind_ext = HumanGate → event.kernel_authored = true` —
//!   only the kernel may author a human-gate event. A tenant action
//!   defense).
//!
//! ## Route (c) STRUCTURAL PACKAGING — v1.7 narrowing
//!
//! the originally-planned 2-clause shape (clause (a) `humanGateContext`
//! field-presence + clause (b) kernel authorship) is reduced at v1.7
//! to clause (b) ONLY. The dedicated `humanGateContext : Option
//! HumanGateRecord := none` field + `HumanGateRecord` payload struct
//! the 1-clause shape only; the v1.8  cycle will add a second test
//! file mirroring the field-presence clause once the payload schema
//! lands.
//!
//! ## H2 attack scenarios
//!
//! 1. Kernel-authored human-gate event ACCEPT (canonical positive
//!    mirroring Lean predicate's positive arm).
//! 2. Tenant-authored human-gate event REJECT (clause forgery
//!    `wellFormedHumanGate` literal `e.author = .kernel`
//!    consequent).
//! 3. Default-vacuity ACCEPT — non-`HumanGate` kind_ext with
//!    arbitrary authorship satisfies the predicate vacuously.
//!    Mirrors Lean
//!    `Event.wellFormedHumanGate_default_event_holds`.
//! 4. Trace-level lift POSITIVE — a trace of all kernel-authored
//!    human-gate events (and a baseline non-HumanGate event) all
//!    satisfy `trace_well_formed_human_gate`.
//! 5. Trace-level lift NEGATIVE — a trace containing one tenant-
//!    forged human-gate event fails `trace_well_formed_human_gate`
//!    (∀-quantifier flips on first failure, mirroring Lean
//!    `Trace.wellFormedHumanGate` ∀-shape).
//!

use ctrlmatrix_conformance::generators::{
    human_gate_event, non_human_gate_event_with_author, tenant_human_gate_event,
    trace_well_formed_human_gate, well_formed_human_gate, HumanGateTrace,
};

// Scenario 1 — kernel-authored human-gate ACCEPT (canonical positive)

#[test]
fn kernel_authored_human_gate_accepted() {
    let e = human_gate_event(0);
    assert!(
        well_formed_human_gate(&e),
        "kernel-authored human-gate event must satisfy well_formed_human_gate \
         (mirrors Lean wellFormedHumanGate positive arm: \
         kind = humanGate ∧ author = kernel)"
    );
}

// Scenario 2 — tenant-authored human-gate REJECT (forgery defense)

#[test]
fn tenant_authored_human_gate_rejected() {
    let e = tenant_human_gate_event(0);
    assert!(
        !well_formed_human_gate(&e),
        "tenant-authored human-gate event MUST violate well_formed_human_gate \
         (mirrors Lean [ref] forgery defense — only the kernel may author \
         a human-gate event; a tenant action handler attempting to forge \
         human-assent records must be rejected by the L0 predicate)"
    );
}

// Scenario 3 — default-vacuity ACCEPT (non-`HumanGate` kind_ext)
// Mirrors Lean `Event.wellFormedHumanGate_default_event_holds`.

#[test]
fn non_human_gate_event_default_accepted() {
    // Non-`HumanGate` kind_ext + tenant-authored: vacuously accepted.
    let e_tenant = non_human_gate_event_with_author(0, false);
    assert!(
        well_formed_human_gate(&e_tenant),
        "non-HumanGate event with tenant-authored MUST vacuously accept \
         (mirrors Lean wellFormedHumanGate_default_event_holds — \
         antecedent kind_ext = HumanGate fails ⇒ implication holds)"
    );
    // Non-`HumanGate` kind_ext + kernel-authored: also vacuously accepted.
    let e_kernel = non_human_gate_event_with_author(1, true);
    assert!(
        well_formed_human_gate(&e_kernel),
        "non-HumanGate event with kernel-authored MUST vacuously accept \
         (default-vacuity holds regardless of authorship for non-HumanGate \
         kind_ext)"
    );
}

// Scenario 4 — trace-level lift POSITIVE

#[test]
fn trace_all_kernel_authored_human_gate_accepted() {
    // Trace mixes 2 kernel-authored human-gate events with 1 baseline
    // non-HumanGate event (vacuously accepted). Trace lift accepts iff
    // every event individually satisfies the per-event predicate.
    let trace: HumanGateTrace = vec![
        human_gate_event(0),
        human_gate_event(1),
        non_human_gate_event_with_author(2, false),
    ];
    assert!(
        trace_well_formed_human_gate(&trace),
        "trace of kernel-authored human-gate events + non-HumanGate \
         legacy event MUST satisfy trace_well_formed_human_gate \
         (mirrors Lean Trace.wellFormedHumanGate ∀-shape positive case)"
    );
}

// Scenario 5 — trace-level lift NEGATIVE (one forgery contaminates trace)

#[test]
fn trace_one_tenant_forged_human_gate_rejected() {
    // Trace contains one tenant-forged human-gate event sandwiched
    // between two kernel-authored ones. The ∀-quantifier on the
    // trace-level predicate flips on the first failure, so the entire
    // trace must be rejected.
    let trace: HumanGateTrace = vec![
        human_gate_event(0),
        tenant_human_gate_event(1), // forgery — clause violator
        human_gate_event(2),
    ];
    assert!(
        !trace_well_formed_human_gate(&trace),
        "trace containing one tenant-forged human-gate event MUST fail \
         trace_well_formed_human_gate (∀-quantifier flips on first \
         failure, mirroring Lean Trace.wellFormedHumanGate ∀-shape)"
    );
}

// =====================================================================
// =====================================================================
//
// ~5–6 NEW property tests covering `well_formed_human_gate` (1-clause
// kernel-authored discriminator). Existing 5 example-based scenarios
// above are PRESERVED.

use proptest::prelude::*;

proptest! {
    /// Property 1 (positive — kernel-authored human-gate ALWAYS
    /// accepted).
    #[test]
    fn prop_kernel_authored_human_gate_accepted(event_id in 0u64..1000) {
        let e = human_gate_event(event_id);
        prop_assert!(well_formed_human_gate(&e));
    }

    /// Property 2 (forgery defense — tenant-authored human-gate
    /// ALWAYS rejected).
    #[test]
    fn prop_tenant_human_gate_rejected(event_id in 0u64..1000) {
        let e = tenant_human_gate_event(event_id);
        prop_assert!(!well_formed_human_gate(&e));
    }

    /// Property 3 (default-vacuity — non-HumanGate events ALWAYS
    /// accepted regardless of authorship).
    #[test]
    fn prop_non_human_gate_default_accepted(
        event_id in 0u64..1000,
        kernel_authored in any::<bool>(),
    ) {
        let e = non_human_gate_event_with_author(event_id, kernel_authored);
        prop_assert!(well_formed_human_gate(&e));
    }

    /// Property 4 (trace lift positive — all-kernel-authored
    /// human-gate trace accepted).
    #[test]
    fn prop_trace_all_kernel_authored_accepted(
        events_count in 1usize..6,
    ) {
        let trace: HumanGateTrace = (0..events_count as u64)
            .map(human_gate_event)
            .collect();
        prop_assert!(trace_well_formed_human_gate(&trace));
    }

    /// Property 5 (trace lift contamination — any tenant-forged
    /// human-gate event fails the trace).
    #[test]
    fn prop_trace_one_tenant_forged_rejected(
        good_id in 0u64..500,
        bad_id in 500u64..1000,
    ) {
        prop_assume!(good_id != bad_id);
        let trace: HumanGateTrace = vec![
            human_gate_event(good_id),
            tenant_human_gate_event(bad_id),
        ];
        prop_assert!(!trace_well_formed_human_gate(&trace));
    }

    /// Property 6 (predicate matches literal semantics — for any
    /// human-gate-marked event, the predicate disposition equals
    /// `event.kernel_authored`).
    #[test]
    fn prop_predicate_matches_literal_semantics(
        event_id in 0u64..1000,
        kernel_authored in any::<bool>(),
    ) {
        // Construct a HumanGate-marked event with custom authorship.
        let e = if kernel_authored {
            human_gate_event(event_id)
        } else {
            tenant_human_gate_event(event_id)
        };
        prop_assert_eq!(well_formed_human_gate(&e), kernel_authored);
    }
}
