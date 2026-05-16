//! kinds cross-alphabet extension).
//!
//! Tests `well_formed_refusal` mirror of Lean predicate
//! `Event.wellFormedRefusal` (lean/AgentKernel/Replay.lean
//! L1167-1177). 4-clause predicate:
//!
//! - Clause (a): `kind = .refusal → detWitness = none ∧ mintedCapId
//!   = none ∧ retractTarget = none ∧ linkedExecId = none` —
//!   refusals are NON-ACTIONS.
//! - Clause (b): `kind = .contractViolation → violationContractId ≠
//!   none` — violation events MUST reference a contract by id.
//! - Clause (c): `kind ≠ .refusal → refusalReasonCode = none` —
//!   only refusal events carry refusalReasonCode (forgery defense).
//! - Clause (d): `kind ≠ .contractViolation → violationContractId =
//!   none` — only violation events carry violationContractId
//!   (forgery defense).
//!
//!
//! Lean ships `refusalReasonCode : Option Nat` (PLAN drift from
//! `Option String` for elaborator whnf-cost reasons; semantic
//! equivalence at L0 preserved). σ_min mirror uses `Option<u64>`;
//!
//!
//! 1. Default-vacuous accept (legacy `Other`-kind, no codes, mirrors
//!    `wellFormedRefusal_default_event_holds`).
//! 2. Well-formed refusal (no side-effects, opaque reason code) ACCEPT.
//! 3. Well-formed contractViolation (with contract id) ACCEPT.
//! 4. Refusal with side-effect (linkedExecId set) REJECT (clause (a)).
//! 5. Refusal with mintedCapId presence REJECT (clause (a)).
//! 6. ContractViolation without violation_contract_id REJECT (clause (b)).
//! 7. Non-refusal event with refusal_reason_code = Some(_) REJECT
//!    (clause (c) forgery).
//! 8. Non-violation event with violation_contract_id = Some(_) REJECT
//!    (clause (d) forgery).
//!    enforce that every actual refusal MUST be marked Kind.refusal;
//!    L1+ kernel-runtime obligation).
//!
//! (Option Nat field-type drift from PLAN's Option String).

use ctrlmatrix_conformance::generators::{
    contract_violation_event, other_kind_event_with_codes, refusal_event,
    trace_well_formed_refusal, well_formed_refusal, KindExt, KernelEventWithRefusal,
    RefusalTrace,
};

// Scenario 1 — default-vacuous accept

#[test]
fn default_other_kind_no_codes_accepted() {
    let e = other_kind_event_with_codes(0, None, None);
    assert!(
        well_formed_refusal(&e),
        "default Other-kind event with no codes must vacuously accept \
         (mirrors Lean wellFormedRefusal_default_event_holds)"
    );
}

// Scenario 2 — well-formed refusal ACCEPT

#[test]
fn well_formed_refusal_accepted() {
    let e = refusal_event(0, Some(0xDEAD_BEEF));
    assert!(
        well_formed_refusal(&e),
        "well-formed refusal (no side-effects, opaque reason code) must accept"
    );
}

#[test]
fn well_formed_refusal_with_no_reason_code_accepted() {
    // refusal with refusal_reason_code = None still satisfies all 4
    // clauses (clause (a) requires no side-effects; clause (c) is
    // not relevant here since kind_ext = Refusal so antecedent
    // `kind ≠ Refusal` fails).
    let e = refusal_event(0, None);
    assert!(
        well_formed_refusal(&e),
        "refusal event with refusal_reason_code = None must accept \
         (L0 spec does not require a reason code be present)"
    );
}

// Scenario 3 — well-formed contractViolation ACCEPT

#[test]
fn well_formed_contract_violation_accepted() {
    let e = contract_violation_event(0, 42);
    assert!(
        well_formed_refusal(&e),
        "well-formed contractViolation (with contract id) must accept"
    );
}

// Scenario 4 — refusal with linkedExecId side-effect REJECT (clause (a))

#[test]
fn refusal_with_linked_exec_id_rejected() {
    let mut e = refusal_event(0, Some(1));
    e.linked_exec_id_present = true; // <-- side-effect injection
    assert!(
        !well_formed_refusal(&e),
        "refusal event with linked_exec_id_present = true MUST be rejected by clause (a) \
         (refusals are non-actions; no exec linkage)"
    );
}

// Scenario 5 — refusal with mintedCapId presence REJECT (clause (a))

#[test]
fn refusal_with_minted_cap_id_rejected() {
    let mut e = refusal_event(0, Some(1));
    e.minted_cap_id_present = true; // <-- side-effect injection
    assert!(
        !well_formed_refusal(&e),
        "refusal event with minted_cap_id_present = true MUST be rejected by clause (a) \
         (refusals are non-actions; no cap minting)"
    );
}

#[test]
fn refusal_with_det_witness_rejected() {
    let mut e = refusal_event(0, Some(1));
    e.det_witness_present = true;
    assert!(
        !well_formed_refusal(&e),
        "refusal event with det_witness_present = true MUST be rejected by clause (a) \
         (refusals are non-actions; no deterministic witness)"
    );
}

#[test]
fn refusal_with_retract_target_rejected() {
    let mut e = refusal_event(0, Some(1));
    e.retract_target_present = true;
    assert!(
        !well_formed_refusal(&e),
        "refusal event with retract_target_present = true MUST be rejected by clause (a) \
         (refusals are non-actions; no retraction target)"
    );
}

// Scenario 6 — contractViolation without contract id REJECT (clause (b))

#[test]
fn violation_without_contract_id_rejected() {
    let mut e = contract_violation_event(0, 0);
    e.violation_contract_id = None; // <-- strip the binding
    assert!(
        !well_formed_refusal(&e),
        "contractViolation event with violation_contract_id = None \
         MUST be rejected by clause (b) (violation must reference a contract)"
    );
}

// Scenario 7 — non-refusal with refusal_reason_code REJECT (clause (c))

#[test]
fn non_refusal_with_reason_code_rejected() {
    // Other-kind event with refusal_reason_code = Some(_) is forgery.
    let e = other_kind_event_with_codes(0, Some(0xCAFE), None);
    assert!(
        !well_formed_refusal(&e),
        "non-refusal event with refusal_reason_code = Some(_) MUST be rejected by clause (c) \
         (forgery defense: only refusal events carry refusal_reason_code)"
    );
}

// Scenario 8 — non-violation with violation_contract_id REJECT (clause (d))

#[test]
fn non_violation_with_contract_id_rejected() {
    let e = other_kind_event_with_codes(0, None, Some(42));
    assert!(
        !well_formed_refusal(&e),
        "non-violation event with violation_contract_id = Some(_) MUST be rejected by clause (d) \
         (forgery defense: only violation events carry violation_contract_id)"
    );
}

// L0 spec asserts "if marked Kind.refusal, then non-action"; it does
// NOT mandate "every actual refusal MUST be marked Kind.refusal."
// The latter (always-mark) is L1+ kernel-runtime obligation.

#[test]
fn unmarked_refusal_accepted_documents_d079h_alpha_residual() {
    // An Other-kind event that semantically represents a refusal but
    // is NOT marked Kind::Refusal — the L0 predicate accepts (clause
    let e = other_kind_event_with_codes(0, None, None);
    assert!(
        well_formed_refusal(&e),
        "unmarked refusal accepted at L0"
    );
}

// Scenario 10 — composite trace at trace lift

#[test]
fn composite_refusal_trace_accepted_at_trace_lift() {
    // Trace: [Other, Refusal, ContractViolation, Other].
    // Each event is well-formed; trace-level lift accepts.
    let trace: RefusalTrace = vec![
        other_kind_event_with_codes(0, None, None),
        refusal_event(1, Some(0xBEEF)),
        contract_violation_event(2, 7),
        other_kind_event_with_codes(3, None, None),
    ];
    assert!(
        trace_well_formed_refusal(&trace),
        "composite refusal/violation/Other trace must accept at trace lift"
    );
}

#[test]
fn composite_refusal_trace_with_forgery_rejected_at_trace_lift() {
    // Trace contains a clause (c) forgery — must be rejected.
    let trace: RefusalTrace = vec![
        refusal_event(0, Some(0xBEEF)),
        other_kind_event_with_codes(1, Some(0xCAFE), None), // <-- clause (c) falsifier
        contract_violation_event(2, 7),
    ];
    assert!(
        !trace_well_formed_refusal(&trace),
        "trace containing a forged refusal_reason_code on Other-kind event \
         MUST be rejected at trace lift"
    );
}

// Defensive: confirm Refusal + ContractViolation kind_ext NON-OVERLAP
// siblings, not aliases — see clause (a) discriminating the field
// bindings."

#[test]
fn refusal_and_violation_are_disjoint_kinds() {
    let r = refusal_event(0, None);
    let v = contract_violation_event(1, 42);
    assert_ne!(
        r.kind_ext, v.kind_ext,
        "Refusal and ContractViolation are sibling kinds, not aliases"
    );
    assert_eq!(r.kind_ext, KindExt::Refusal);
    assert_eq!(v.kind_ext, KindExt::ContractViolation);
}

// Defensive type-coverage: confirm the Refusal trace alias and
// well-formedness wrapper compose cleanly with the wrapper struct.

#[test]
fn empty_refusal_trace_accepted() {
    let trace: RefusalTrace = vec![];
    assert!(
        trace_well_formed_refusal(&trace),
        "empty trace vacuously satisfies trace_well_formed_refusal"
    );
}

#[test]
fn single_well_formed_refusal_in_trace_accepted() {
    let r: KernelEventWithRefusal = refusal_event(0, Some(1));
    let trace: RefusalTrace = vec![r];
    assert!(trace_well_formed_refusal(&trace));
}

// =====================================================================
// =====================================================================
//
// ~6–8 NEW property tests covering `well_formed_refusal`'s 4-clause
// shape. Existing 14 example-based scenarios above are PRESERVED.

use proptest::prelude::*;

proptest! {
    /// Property 1 (clause (a) — refusals reject any side-effect bit).
    #[test]
    fn prop_refusal_with_any_side_effect_rejected(
        event_id in 0u64..1000,
        det in any::<bool>(),
        mint in any::<bool>(),
        retr in any::<bool>(),
        link in any::<bool>(),
    ) {
        prop_assume!(det || mint || retr || link); // at least one
        let mut e = refusal_event(event_id, Some(0xCAFE));
        e.det_witness_present = det;
        e.minted_cap_id_present = mint;
        e.retract_target_present = retr;
        e.linked_exec_id_present = link;
        prop_assert!(!well_formed_refusal(&e));
    }

    /// Property 2 (clause (a) positive arm — refusals with no
    /// side-effects accept regardless of reason code).
    #[test]
    fn prop_refusal_no_side_effects_accepted(
        event_id in 0u64..1000,
        reason in proptest::option::of(0u64..1000),
    ) {
        let e = refusal_event(event_id, reason);
        prop_assert!(well_formed_refusal(&e));
    }

    /// Property 3 (clause (b) — violations need a contract id).
    #[test]
    fn prop_violation_without_contract_id_rejected(
        event_id in 0u64..1000,
    ) {
        let mut e = contract_violation_event(event_id, 1);
        e.violation_contract_id = None;
        prop_assert!(!well_formed_refusal(&e));
    }

    /// Property 4 (clause (b) positive — violations with a contract
    /// id accept).
    #[test]
    fn prop_violation_with_contract_id_accepted(
        event_id in 0u64..1000,
        contract_id in 0u64..1000,
    ) {
        let e = contract_violation_event(event_id, contract_id);
        prop_assert!(well_formed_refusal(&e));
    }

    /// Property 5 (clause (c) — non-refusal carrying a refusal_reason
    /// _code is rejected).
    #[test]
    fn prop_non_refusal_with_reason_code_rejected(
        event_id in 0u64..1000,
        reason in 1u64..1000,
    ) {
        let e = other_kind_event_with_codes(event_id, Some(reason), None);
        prop_assert!(!well_formed_refusal(&e));
    }

    /// Property 6 (clause (d) — non-violation carrying a violation
    /// _contract_id is rejected).
    #[test]
    fn prop_non_violation_with_contract_id_rejected(
        event_id in 0u64..1000,
        contract_id in 1u64..1000,
    ) {
        let e = other_kind_event_with_codes(event_id, None, Some(contract_id));
        prop_assert!(!well_formed_refusal(&e));
    }

    /// Property 7 (default-vacuity — Other-kind without codes always
    /// accepts).
    #[test]
    fn prop_baseline_other_event_accepted(
        event_id in 0u64..1000,
    ) {
        let e = other_kind_event_with_codes(event_id, None, None);
        prop_assert!(well_formed_refusal(&e));
    }

    /// Property 8 (trace contamination — any forged event in trace
    /// fails the trace lift).
    #[test]
    fn prop_trace_with_forgery_rejected(
        good_id in 0u64..500,
        bad_id in 500u64..1000,
        bad_reason in 1u64..1000,
    ) {
        prop_assume!(good_id != bad_id);
        let trace: RefusalTrace = vec![
            refusal_event(good_id, Some(0xBEEF)),
            other_kind_event_with_codes(bad_id, Some(bad_reason), None), // clause (c) forgery
        ];
        prop_assert!(!trace_well_formed_refusal(&trace));
    }
}
