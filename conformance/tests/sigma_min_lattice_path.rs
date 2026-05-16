//!
//! Tests the lattice path length 1–L_MAX generator against the σ_min
//! spec at `spec/sigma-min-coverage.md` §"Lattice path length", and
//! the adversarial `monotone_violation` label-flow class (class #1
//! of the σ_min adversarial label-flow grammar).
//!
//! Coverage shape:
//!
//! - Positive proptest: every (length, seed) yields a monotone path
//!   that satisfies `lattice_path_monotone`.
//! - Negative proptest: injecting a strict-below label produces a
//!   path that FAILS `lattice_path_monotone`.
//! - Hand-crafted unit tests at length 1 and length L_MAX = 48.

use ctrlmatrix_conformance::generators::{
    lattice_path_inject_monotone_violation, lattice_path_monotone,
    lattice_path_monotone_from_seed, LatticeLabel, LatticePath, L_MAX, SIGMA_C, SIGMA_I, SIGMA_P,
};
use proptest::prelude::*;

/// Local strategy lifter — proptest is a dev-dependency only.
fn arb_lattice_path() -> impl Strategy<Value = LatticePath> {
    (1usize..=L_MAX, any::<u64>())
        .prop_map(|(len, seed)| lattice_path_monotone_from_seed(len, seed))
}

// ---------------------------------------------------------------------
// Positive proptest
// ---------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 5_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 5×10³ generated lattice paths of lengths in [1, L_MAX]: each
    /// satisfies `lattice_path_monotone` by construction. Closes the
    /// σ_min "Lattice path length: 1–L_MAX" floor at the structural
    ///  monotone-join layer.
    #[test]
    fn pt_lattice_path_monotone(path in arb_lattice_path()) {
        prop_assert!(lattice_path_monotone(&path),
            "monotone-by-construction path must satisfy ");
        prop_assert!(!path.is_empty());
        prop_assert!(path.len() <= L_MAX);
    }

    /// Injecting a strict-below label (when feasible) MUST falsify
    /// `lattice_path_monotone`. This is the σ_min
    /// `monotone_violation` adversarial label-flow class
    /// (spec §"Adversarial label flow grammar" item 1).
    #[test]
    fn pt_neg_monotone_violation(seed in any::<u64>(), len in 2usize..=L_MAX, idx in any::<usize>()) {
        // Build a strictly-increasing path so the prior label is not
        // (0,0,0) at idx >= 1 — this maximizes the chance the
        // mutator can inject a strict-below label.
        let path = strictly_increasing_path(len);
        let i = 1 + (idx % (path.len() - 1));
        if let Some(bad) = lattice_path_inject_monotone_violation(&path, i) {
            prop_assert!(!lattice_path_monotone(&bad),
                "monotone-violation injection must falsify  — falsifier missing (seed={}, i={})", seed, i);
        }
    }
}

/// Helper: build a strictly-increasing lattice path. Step i sets
/// (c, i, p) = ((i / SIGMA_P / SIGMA_I) % SIGMA_C,
///              (i / SIGMA_P) % SIGMA_I,
///              i % SIGMA_P). For i < L_MAX this is strictly
/// non-decreasing in flat index and at least one component
/// increments at every step (within the alphabet ceiling).
fn strictly_increasing_path(len: usize) -> Vec<LatticeLabel> {
    assert!(len >= 1 && len <= L_MAX);
    (0..len).map(LatticeLabel::from_flat).collect()
}

// ---------------------------------------------------------------------
// Hand-crafted unit tests
// ---------------------------------------------------------------------

#[test]
fn unit_l_max_is_48() {
    // Reference L_MAX from spec §"Lattice path length": 4×3×4 = 48.
    assert_eq!(L_MAX, 48);
    assert_eq!(SIGMA_C * SIGMA_I * SIGMA_P, 48);
}

#[test]
fn unit_lattice_path_length_1_is_monotone() {
    // Length 1 is the σ_min single-event monotone-join () floor.
    let p = lattice_path_monotone_from_seed(1, 0);
    assert_eq!(p.len(), 1);
    assert!(lattice_path_monotone(&p));
}

#[test]
fn unit_lattice_path_length_l_max_is_monotone() {
    let p = lattice_path_monotone_from_seed(L_MAX, 0xDEADBEEF);
    assert_eq!(p.len(), L_MAX);
    assert!(lattice_path_monotone(&p));
}

#[test]
fn unit_lattice_path_full_length_sweep() {
    // Exercise EVERY length in [1, L_MAX] explicitly so the σ_min
    // floor is auditable from the test source alone.
    for len in 1..=L_MAX {
        let p = lattice_path_monotone_from_seed(len, len as u64);
        assert_eq!(p.len(), len);
        assert!(lattice_path_monotone(&p),
            "monotone violation at length {}", len);
    }
}

#[test]
fn unit_handcrafted_monotone_violation() {
    // (1,1,1) → (0,0,0) is a strict-below step on every component.
    let path = vec![
        LatticeLabel { c_idx: 1, i_idx: 1, p_idx: 1 },
        LatticeLabel { c_idx: 0, i_idx: 0, p_idx: 0 },
    ];
    assert!(!lattice_path_monotone(&path),
        "(1,1,1) → (0,0,0) must falsify  monotone-join");
}

#[test]
fn unit_handcrafted_componentwise_step_is_monotone() {
    let path = vec![
        LatticeLabel { c_idx: 0, i_idx: 0, p_idx: 0 },
        LatticeLabel { c_idx: 1, i_idx: 0, p_idx: 0 },
        LatticeLabel { c_idx: 1, i_idx: 1, p_idx: 0 },
        LatticeLabel { c_idx: 1, i_idx: 1, p_idx: 1 },
    ];
    assert!(lattice_path_monotone(&path),
        "componentwise-non-decreasing path must satisfy ");
}
