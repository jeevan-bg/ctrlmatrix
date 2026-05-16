//! σ_min partition / contract-violation / replay-divergence tests
//!
//! Covers three σ_min coverage parameters at the v1.1.1 floor:
//!
//! - Partition scenario #1: `partition_then_heal` (1 of 5 classes;
//!   classes 2–5 carry forward).
//! - Contract-violation class #1: `unsigned_contract` (1 of 5; rest
//!   carry forward).
//! - Replay divergence at parameterized N (default 10⁴; 10⁶ floor
//!   is a deployment-policy obligation per scope.md §8).

use ctrlmatrix_conformance::generators::{
    divergence_cause, operator_rooted, partition_merge, partition_then_heal, replay_equiv,
    run_replay_divergence, signed_contract_from_seed, unsigned_contract_from, DivergenceCause,
    PartitionTrace, REPLAY_DIVERGENCE_DEFAULT_N, REPLAY_DIVERGENCE_SPEC_FLOOR_N,
};
use ctrlmatrix_conformance::well_formed;
use proptest::prelude::*;

/// Local strategy lifter — proptest is a dev-dependency only.
fn arb_partition_trace() -> impl Strategy<Value = PartitionTrace> {
    (
        prop::collection::vec(prop::collection::vec(any::<u8>(), 0..8), 0..8),
        prop::collection::vec(prop::collection::vec(any::<u8>(), 0..8), 0..8),
    )
        .prop_map(|(a, b)| partition_then_heal(a, b))
}

// ---------------------------------------------------------------------
// Partition scenario #1: partition_then_heal
// ---------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 2_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 2×10³ partition_then_heal scenarios: side_a and side_b are
    /// independently well-formed; the merged trace is also
    /// well-formed by the M6 append discipline. Closes σ_min
    /// partition scenario #1 at the structural layer.
    #[test]
    fn pt_partition_then_heal(trace in arb_partition_trace()) {
        prop_assert!(well_formed(&trace.side_a, &trace.spec),
            "partition side_a must be M6-well-formed");
        prop_assert!(well_formed(&trace.side_b, &trace.spec),
            "partition side_b must be M6-well-formed");
        let merged = partition_merge(&trace);
        prop_assert!(well_formed(&merged, &trace.spec),
            "merged trace must be M6-well-formed by construction");
        prop_assert_eq!(merged.len(), trace.side_a.len() + trace.side_b.len());
    }
}

#[test]
fn unit_partition_then_heal_smoke() {
    let trace = partition_then_heal(
        vec![b"a1".to_vec(), b"a2".to_vec()],
        vec![b"b1".to_vec(), b"b2".to_vec(), b"b3".to_vec()],
    );
    assert_eq!(trace.side_a.len(), 2);
    assert_eq!(trace.side_b.len(), 3);
    assert!(well_formed(&trace.side_a, &trace.spec));
    assert!(well_formed(&trace.side_b, &trace.spec));
    let merged = partition_merge(&trace);
    assert_eq!(merged.len(), 5);
    assert!(well_formed(&merged, &trace.spec),
        "merged trace must satisfy M6 well-formedness");
}

#[test]
fn unit_partition_empty_sides_is_well_formed() {
    // Both sides empty: merged is empty, vacuously well-formed.
    let trace = partition_then_heal(vec![], vec![]);
    assert!(trace.side_a.is_empty());
    assert!(trace.side_b.is_empty());
    let merged = partition_merge(&trace);
    assert!(merged.is_empty());
    assert!(well_formed(&merged, &trace.spec));
}

// ---------------------------------------------------------------------
// Contract-violation class #1: unsigned_contract
// ---------------------------------------------------------------------

#[test]
fn unit_signed_contract_is_operator_rooted() {
    let c = signed_contract_from_seed(123);
    assert!(operator_rooted(&c),
        "signed contract must satisfy structural -rooting");
}

#[test]
fn unit_unsigned_contract_falsifies_operator_rooted() {
    let signed = signed_contract_from_seed(456);
    let unsigned = unsigned_contract_from(&signed);
    assert!(!operator_rooted(&unsigned),
        "unsigned contract must falsify operatorRooted — class #1 falsifier");
    assert!(unsigned.signature.is_none());
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 1_000,
        .. ProptestConfig::default()
    })]

    /// Every signed-from-seed contract is operator-rooted; stripping
    /// the signature falsifies -rooting universally.
    #[test]
    fn pt_unsigned_contract_class(seed in any::<u64>()) {
        let signed = signed_contract_from_seed(seed);
        prop_assert!(operator_rooted(&signed));
        let unsigned = unsigned_contract_from(&signed);
        prop_assert!(!operator_rooted(&unsigned),
            "unsigned_contract must falsify operatorRooted for every seed");
    }
}

// ---------------------------------------------------------------------
// Replay divergence at parameterized N
// ---------------------------------------------------------------------

#[test]
fn unit_replay_divergence_default_n_dichotomy() {
    // The σ_min spec dichotomy: every (baseline, mutated) pair is
    // either replayEquiv (a) or NOT replayEquiv with an identifiable
    // divergence cause (b). At the structural layer this is total
    // by construction — divergence_cause never returns Equivalent
    // for a length-different or payload-different trace.
    //
    // Run at the v1.1.1 default N = 10⁴; the 10⁶ floor is a
    // deployment-policy obligation (scope.md §8), not a CI obligation.
    let result = run_replay_divergence(REPLAY_DIVERGENCE_DEFAULT_N);
    let (diverged, equiv) = result.expect("dichotomy must hold for every seed");
    assert_eq!(
        diverged + equiv,
        REPLAY_DIVERGENCE_DEFAULT_N,
        "every round must be classified as either diverged or equivalent"
    );
    assert!(diverged > 0, "some seeds must produce divergence");
    assert!(equiv > 0, "some seeds must produce equivalence");
}

#[test]
fn unit_replay_divergence_constants() {
    // Sanity: the v1.1.1 default is 10⁴ and the spec floor is 10⁶.
    // The 100x gap is documented as a deployment-policy obligation
    // per the σ_min spec.
    assert_eq!(REPLAY_DIVERGENCE_DEFAULT_N, 10_000);
    assert_eq!(REPLAY_DIVERGENCE_SPEC_FLOOR_N, 1_000_000);
    assert!(REPLAY_DIVERGENCE_SPEC_FLOOR_N > REPLAY_DIVERGENCE_DEFAULT_N,
        "spec floor must exceed CI default");
}

#[test]
fn unit_divergence_cause_taxonomy_smoke() {
    use ctrlmatrix_conformance::{build_well_formed, Spec};
    let spec = Spec::default();
    let a = build_well_formed(vec![b"x".to_vec(), b"y".to_vec()], &spec);
    let b = build_well_formed(vec![b"x".to_vec(), b"y".to_vec()], &spec);
    let c = build_well_formed(vec![b"x".to_vec(), b"z".to_vec()], &spec);
    let d = build_well_formed(vec![b"x".to_vec()], &spec);
    assert_eq!(divergence_cause(&a, &b), DivergenceCause::Equivalent);
    assert!(replay_equiv(&a, &b));
    // a vs c: same length, payload differs at index 1.
    match divergence_cause(&a, &c) {
        DivergenceCause::PayloadDiffersAt(1) => {}
        other => panic!("expected PayloadDiffersAt(1), got {:?}", other),
    }
    assert!(!replay_equiv(&a, &c));
    // a vs d: length differs.
    assert_eq!(divergence_cause(&a, &d), DivergenceCause::LengthDiffers);
    assert!(!replay_equiv(&a, &d));
}
