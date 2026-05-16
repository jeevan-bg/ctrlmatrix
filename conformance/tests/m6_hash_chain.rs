//! Conformance tests for M6 hash-chain wellFormedness.
//!
//! Three layers:
//!
//! 1. **Positive proptest** (`pt_built_chain_is_well_formed`):
//!    10⁵ generated chains built via successive `append`. Each must
//!    satisfy `well_formed`.
//!
//! 2. **Negative proptests** (`pt_neg_*`): one per mutator class.
//!    Each generates a well-formed chain, applies the mutator, and
//!    asserts `!well_formed(mutated)`. These are the falsifiability
//!    fails on one mutated input is").
//!
//! 3. **Hand-crafted unit tests** (`unit_*`): deterministic small
//!    chains demonstrating each mutator class produces
//!    `!well_formed(...)`. The unit tests are the
//!    parent-debugging surface — when proptest shrinks a failure,
//!    the unit tests are the human-readable counterexample shape.
//!
//! Lean spec mirror: see `src/lib.rs` module docstring.

use ctrlmatrix_conformance::{
    append, build_well_formed, flip_bit_in_prev, insert_spurious, mutate_payload, root,
    swap_adjacent, truncate_drop_prefix, well_formed, Entry, LogChain, Spec,
};
use proptest::prelude::*;

// ---------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------

/// A small payload (bounded length to keep the proptest budget
/// tractable; covers the L0 conformance σ_min envelope of "deep
/// chains, small payloads" rather than L1+ "wide payload" cases —
fn arb_payload() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(any::<u8>(), 0..16)
}

/// A well-formed chain of length 0..32. Built via successive
/// `append` so wellFormedness is by construction.
fn arb_well_formed_chain() -> impl Strategy<Value = (LogChain, Spec)> {
    prop::collection::vec(arb_payload(), 0..32)
        .prop_map(|payloads| {
            let spec = Spec::default();
            let chain = build_well_formed(payloads, &spec);
            (chain, spec)
        })
}

/// A well-formed chain of length ≥ 2 (for mutators that need at
/// least two entries — swap, mutate-non-last-payload).
fn arb_well_formed_chain_min2() -> impl Strategy<Value = (LogChain, Spec)> {
    prop::collection::vec(arb_payload(), 2..32)
        .prop_map(|payloads| {
            let spec = Spec::default();
            let chain = build_well_formed(payloads, &spec);
            (chain, spec)
        })
}

// ---------------------------------------------------------------------
// Positive proptest: 10⁵ cases
// ---------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 100_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 10⁵ generated chains built via `append`: every one satisfies
    /// `well_formed`. This is the kernel-emit invariant
    /// (Lean `LogChain.wellFormed_append_singleton`,
    /// `Log.lean:419-431`) executed against the SHA-256 mock.
    #[test]
    fn pt_built_chain_is_well_formed((chain, spec) in arb_well_formed_chain()) {
        prop_assert!(well_formed(&chain, &spec));
    }
}

// ---------------------------------------------------------------------
// Negative proptests — one per mutator class
// ---------------------------------------------------------------------
//
// Each is allotted 10_000 cases (10⁵ / 10) so the overall budget
// of the negative suite matches the positive suite within an order
// falsifiability — that for every mutator class, *every* chain in
// the input domain produces `!well_formed`. Higher case counts
// here are not buying additional coverage because the assertion
// is universal, not statistical.

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 10_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    #[test]
    fn pt_neg_flip_bit_in_prev(
        (chain, spec) in arb_well_formed_chain(),
        idx in any::<usize>(),
        byte in any::<usize>(),
        bit in any::<u8>(),
    ) {
        prop_assume!(!chain.is_empty());
        let i = idx % chain.len();
        let b = byte % 32;
        let mutated = flip_bit_in_prev(&chain, i, b, bit).unwrap();
        prop_assert!(!well_formed(&mutated, &spec),
            "flip_bit_in_prev produced a still-wellFormed chain — falsifier missing");
    }

    #[test]
    fn pt_neg_truncate_drop_prefix(
        (chain, spec) in arb_well_formed_chain(),
        n in any::<usize>(),
    ) {
        prop_assume!(chain.len() >= 2);
        let cut = 1 + (n % (chain.len() - 1));
        let mutated = truncate_drop_prefix(&chain, cut).unwrap();
        prop_assert!(!well_formed(&mutated, &spec),
            "truncate_drop_prefix produced a still-wellFormed chain — falsifier missing");
    }

    #[test]
    fn pt_neg_swap_adjacent(
        (chain, spec) in arb_well_formed_chain_min2(),
        i in any::<usize>(),
    ) {
        // Find a swap-pair (j, j+1) whose payloads differ. If no
        // such pair exists in this chain (e.g., all payloads
        // identical — unlikely given arb_payload's distribution
        // over Vec<u8>), reject the case.
        let n = chain.len();
        let start = i % (n - 1);
        let mut chosen: Option<usize> = None;
        for k in 0..(n - 1) {
            let j = (start + k) % (n - 1);
            if chain[j].payload != chain[j + 1].payload {
                chosen = Some(j);
                break;
            }
        }
        prop_assume!(chosen.is_some());
        let j = chosen.unwrap();
        let mutated = swap_adjacent(&chain, j).unwrap();
        prop_assert!(!well_formed(&mutated, &spec),
            "swap_adjacent on distinct-payload pair produced a still-wellFormed chain — falsifier missing");
    }

    #[test]
    fn pt_neg_insert_spurious(
        (chain, spec) in arb_well_formed_chain(),
        idx in any::<usize>(),
        payload in arb_payload(),
    ) {
        let i = idx % (chain.len() + 1);
        let mutated = insert_spurious(&chain, i, payload, &spec).unwrap();
        prop_assert!(!well_formed(&mutated, &spec),
            "insert_spurious produced a still-wellFormed chain — falsifier missing");
    }

    #[test]
    fn pt_neg_mutate_payload(
        (chain, spec) in arb_well_formed_chain_min2(),
        idx in any::<usize>(),
        xor in any::<u8>(),
    ) {
        // Choose a non-last index.
        let n = chain.len();
        let i = idx % (n - 1);
        let mutated = mutate_payload(&chain, i, xor).unwrap();
        prop_assert!(!well_formed(&mutated, &spec),
            "mutate_payload on non-last entry produced a still-wellFormed chain — falsifier missing");
    }
}

// ---------------------------------------------------------------------
// Hand-crafted unit tests (deterministic falsifier witnesses)
// ---------------------------------------------------------------------
//
// Each constructs a small chain by hand, applies one mutator, and
// criterion artifacts: literal, named, paste-into-the-report
// counterexamples that the Lean predicate is falsifiable.

fn small_chain(spec: &Spec) -> LogChain {
    let c = LogChain::new();
    let c = append(c, b"alpha".to_vec(), spec);
    let c = append(c, b"beta".to_vec(), spec);
    let c = append(c, b"gamma".to_vec(), spec);
    c
}

#[test]
fn unit_baseline_built_chain_is_well_formed() {
    let spec = Spec::default();
    let c = small_chain(&spec);
    assert_eq!(c.len(), 3);
    assert!(well_formed(&c, &spec), "baseline chain must be well-formed");
}

#[test]
fn unit_mutator_a_flip_bit_in_prev() {
    let spec = Spec::default();
    let c = small_chain(&spec);
    let bad = flip_bit_in_prev(&c, 1, 0, 0).expect("idx in range");
    assert_ne!(bad[1].prev, c[1].prev);
    assert!(!well_formed(&bad, &spec),
        "mutator (a) flip_bit_in_prev must produce !well_formed — falsifier required");
}

#[test]
fn unit_mutator_b_truncate_drop_prefix() {
    let spec = Spec::default();
    let c = small_chain(&spec);
    let bad = truncate_drop_prefix(&c, 1).expect("len >= 2");
    assert_eq!(bad.len(), 2);
    assert!(!well_formed(&bad, &spec),
        "mutator (b) truncate_drop_prefix must produce !well_formed — falsifier required");
}

#[test]
fn unit_mutator_c_swap_adjacent() {
    let spec = Spec::default();
    let c = small_chain(&spec);
    // small_chain has distinct payloads "alpha" / "beta" / "gamma";
    // swapping indices 0 and 1 breaks the binding.
    let bad = swap_adjacent(&c, 0).expect("len >= 2");
    assert_eq!(bad.len(), 3);
    assert!(!well_formed(&bad, &spec),
        "mutator (c) swap_adjacent (distinct payloads) must produce !well_formed — falsifier required");
}

#[test]
fn unit_mutator_d_insert_spurious() {
    let spec = Spec::default();
    let c = small_chain(&spec);
    let bad = insert_spurious(&c, 1, b"injected".to_vec(), &spec).expect("idx in range");
    assert_eq!(bad.len(), 4);
    assert!(!well_formed(&bad, &spec),
        "mutator (d) insert_spurious must produce !well_formed — falsifier required");
}

#[test]
fn unit_mutator_e_mutate_payload() {
    let spec = Spec::default();
    let c = small_chain(&spec);
    let bad = mutate_payload(&c, 0, 0xAA).expect("len >= 2 and idx in range");
    assert!(!well_formed(&bad, &spec),
        "mutator (e) mutate_payload on non-last entry must produce !well_formed — falsifier required");
}

#[test]
fn unit_negative_check_root_changes_under_mutation() {
    // Sanity: mutating an entry's payload changes the chain root
    // (this is what propagates the wellFormedness break to later
    // entries' prev fields). If this ever stops holding the hash
    // function has degenerated to a constant.
    let spec = Spec::default();
    let c = small_chain(&spec);
    let r0 = root(&c, &spec);
    let mut c2 = c.clone();
    c2[0].payload[0] ^= 0xFF;
    let r1 = root(&c2, &spec);
    assert_ne!(r0, r1, "root should depend on payload contents");
}

#[test]
fn unit_empty_chain_is_well_formed() {
    let spec = Spec::default();
    let c: LogChain = Vec::new();
    assert!(well_formed(&c, &spec),
        "empty chain is well-formed by Lean LogChain.wellFormed_nil");
}

#[test]
fn unit_truncating_to_prefix_preserves_well_formedness() {
    // Lean LogChain.wellFormed_dropLast: prefixes of well-formed
    // chains are well-formed. This is the dual of truncate_drop_prefix
    // (which drops a prefix and breaks wellFormedness). Both must
    // hold for the conformance crate to mirror Lean correctly.
    let spec = Spec::default();
    let c = small_chain(&spec);
    let prefix: LogChain = c[..2].to_vec();
    assert!(well_formed(&prefix, &spec),
        "dropLast prefix must remain well-formed (Lean wellFormed_dropLast)");
    let prefix1: LogChain = c[..1].to_vec();
    assert!(well_formed(&prefix1, &spec));
}

#[test]
fn unit_first_entry_prev_equals_h_of_genesis() {
    // Lean Log.lean:120: "The first entry's `prev` equals
    // `H(genesis)`." Concretely realized.
    let spec = Spec::default();
    let c = small_chain(&spec);
    let h_genesis = ctrlmatrix_conformance::initial_acc(&spec);
    assert_eq!(c[0].prev, h_genesis,
        "first entry's prev must equal H(genesis) per wellFormed definition");
}

#[test]
fn unit_explicit_handcrafted_falsifier_with_wrong_prev() {
    // Manually build a chain where the second entry's prev is
    // arbitrary garbage. No mutator involved — this is the simplest
    // possible falsifier.
    let spec = Spec::default();
    let mut c = LogChain::new();
    c = append(c, b"alpha".to_vec(), &spec);
    c.push(Entry { prev: [0xAB; 32], payload: b"beta".to_vec() });
    assert_eq!(c.len(), 2);
    assert!(!well_formed(&c, &spec),
        "hand-crafted chain with garbage prev field must be !well_formed");
}
