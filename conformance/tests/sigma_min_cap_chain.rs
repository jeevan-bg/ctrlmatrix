//!
//! Tests the cap-chain depth 1–16 generator against the σ_min spec
//! published at `spec/sigma-min-coverage.md` §"Cap derivation depth".
//!
//! Coverage shape (per H1 inventory in d-072/report.md):
//!
//! - Positive proptest: every (depth, seed) pair in [1, 16] × u32
//!   yields a closure-invariant-holding cap chain.
//! - Negative proptest: forging the parent at any non-root index
//!   produces a closure-invariant-FAILING chain.
//! - Cross-binding unit test: the cap-chain feeds the M6
//!   `well_formed` chassis via `cap_chain_to_log_chain`.
//! - Hand-crafted unit tests: explicit depth-1 (root mint) and
//!   depth-16 (full envelope) witnesses.

use ctrlmatrix_conformance::generators::{
    cap_chain_closure_holds, cap_chain_from_seed, cap_chain_to_log_chain, forge_cap_parent,
    CapChain, CAP_DEPTH_MAX, CAP_DEPTH_MIN,
};
use ctrlmatrix_conformance::{well_formed, Spec};
use proptest::prelude::*;

/// Local strategy lifter — proptest is a dev-dependency only, so the
/// `arb_*` shim lives in the test file rather than `generators.rs`.
fn arb_cap_chain() -> impl Strategy<Value = CapChain> {
    (CAP_DEPTH_MIN..=CAP_DEPTH_MAX, any::<u32>())
        .prop_map(|(depth, seed)| cap_chain_from_seed(depth, seed))
}

// ---------------------------------------------------------------------
// Positive proptest: every (depth, seed) is closure-invariant-holding
// ---------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 10_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 10⁴ generated cap chains in the σ_min depth range [1, 16]
    /// each satisfy `cap_chain_closure_holds`. Closes the σ_min
    /// "Cap derivation depth: 1–16" floor at the structural layer.
    #[test]
    fn pt_cap_chain_closure_holds(chain in arb_cap_chain()) {
        prop_assert!(cap_chain_closure_holds(&chain),
            "generated cap chain must satisfy closure invariant");
        prop_assert!(chain.len() >= CAP_DEPTH_MIN);
        prop_assert!(chain.len() <= CAP_DEPTH_MAX);
    }

    /// Forging the parent at any non-root index (1..len) MUST fail
    /// the closure invariant. Closes the σ_min "forged_parent"
    /// contract-violation class falsifier (class #4 of the
    /// contract-violation grammar).
    #[test]
    fn pt_neg_forge_parent(chain in arb_cap_chain(), idx in any::<usize>()) {
        prop_assume!(chain.len() >= 2);
        let i = 1 + (idx % (chain.len() - 1));
        let garbage = [0xAB; 32];
        let mutated = forge_cap_parent(&chain, i, garbage)
            .expect("idx in [1, len) must be valid");
        prop_assert!(!cap_chain_closure_holds(&mutated),
            "forged parent must falsify closure invariant — falsifier missing");
    }

    /// Cross-binding to M6: every cap chain encoded into a LogChain
    /// via the σ_min adapter is M6-well-formed by construction.
    /// This is the H2-Attack-3 counter — generators feed the existing
    /// chassis, not live in isolation.
    #[test]
    fn pt_cross_bind_cap_chain_to_log_chain(chain in arb_cap_chain()) {
        let spec = Spec::default();
        let log = cap_chain_to_log_chain(&chain);
        prop_assert!(well_formed(&log, &spec),
            "cap-chain → log-chain encoding must yield M6-well-formed chain");
        prop_assert_eq!(log.len(), chain.len());
    }
}

// ---------------------------------------------------------------------
// Hand-crafted unit tests
// ---------------------------------------------------------------------

#[test]
fn unit_cap_chain_depth_1_root_mint() {
    let c = cap_chain_from_seed(1, 0);
    assert_eq!(c.len(), 1);
    assert!(c[0].parent.is_none(), "depth-1 head must be a root mint");
    assert!(cap_chain_closure_holds(&c));
}

#[test]
fn unit_cap_chain_depth_16_full_envelope() {
    let c = cap_chain_from_seed(CAP_DEPTH_MAX, 42);
    assert_eq!(c.len(), 16);
    assert!(c[0].parent.is_none());
    for i in 1..c.len() {
        assert_eq!(c[i].parent, Some(c[i - 1].cap_id),
            "depth-{} entry must delegate from depth-{}", i + 1, i);
    }
    assert!(cap_chain_closure_holds(&c));
}

#[test]
fn unit_cap_chain_full_depth_sweep() {
    // The σ_min spec floor is "depth 1–16 MUST be exercised". This
    // unit test enumerates every depth in [1, 16] explicitly so the
    // floor is auditable from the test source alone.
    for depth in CAP_DEPTH_MIN..=CAP_DEPTH_MAX {
        let c = cap_chain_from_seed(depth, depth as u32);
        assert_eq!(c.len(), depth);
        assert!(cap_chain_closure_holds(&c),
            "closure invariant must hold at depth {}", depth);
    }
}

#[test]
fn unit_forged_parent_falsifies_closure() {
    let c = cap_chain_from_seed(5, 7);
    assert!(cap_chain_closure_holds(&c));
    let bad = forge_cap_parent(&c, 2, [0xFF; 32]).expect("idx 2 in range");
    assert!(!cap_chain_closure_holds(&bad),
        "forged parent at idx 2 must falsify closure invariant");
}

#[test]
fn unit_root_with_forged_parent_falsifies() {
    // Even forging the root's parent (manually — not via
    // forge_cap_parent which protects idx == 0) must falsify.
    let mut c = cap_chain_from_seed(3, 1);
    c[0].parent = Some([0xCD; 32]);
    assert!(!cap_chain_closure_holds(&c),
        "non-None root parent must falsify closure invariant");
}
