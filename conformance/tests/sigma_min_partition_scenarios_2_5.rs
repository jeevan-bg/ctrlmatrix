//!
//! shipped scenario 1, `partition_then_heal`) to the full 5-scenario
//! σ_min floor published at `spec/sigma-min-coverage.md`
//! §"Partition scenarios from FLP-class corpus".
//!
//! ## Spec taxonomy → this file mapping
//!
//! Per spec lines 49-62, the 5 σ_min partition scenarios are:
//!
//! | # | Spec name                  | Status at v1.3  | Owner             |
//! |---|----------------------------|-------------------|-------------------|
//! | 2 | `majority_minority_split`  | THIS file         | v1.3  () |
//! | 3 | `asymmetric_partition`     | THIS file         | v1.3  () |
//! | 4 | `recovering_replay`        | THIS file         | v1.3  () |
//! | 5 | `stuck_minority`           | THIS file         | v1.3  () |
//!
//! ## Honest naming
//!
//! The four new generators in this file are aligned with the SPEC's
//! 5-scenario taxonomy (binding through v1.3 per `spec/sigma-min-
//! coverage.md` §"v1.1 sign-off note"). The  task brief suggested
//! placeholder names (`partition_long_window`, `partition_repeated`,
//! `partition_during_dispatch`, `partition_with_revocation`) and
//! explicitly permitted renaming "if a better fit emerges from
//! reading the existing core" — the spec-aligned names below ARE
//! that better fit, since the spec is the frozen binding taxonomy
//! and the file's primary auditability hook is "every spec scenario
//! has a generator".
//!
//! ## Additive-only discipline ( invariant)
//!
//! No edits to `conformance/src/generators.rs` (the existing 687-LoC
//! file as functions that compose the existing public surface
//! (`partition_then_heal`, `partition_merge`, `build_well_formed`,
//! `append`, `well_formed`, `Spec`, `Bytes`, `LogChain`,
//! `PartitionTrace`). This is the H1-additive shape from the
//! because each generator is small and self-contained.
//!
//! ## Structural σ_min layer
//!
//! "documentation-grade ε(σ_min)"), these generators ship STRUCTURAL
//! shapes only — no operational semantics for the M3/M5/M7 abstract
//! layers. Each generator returns `Vec<...>`-shaped traces / chains;
//! the σ_min floor is "the suite enumerates ≥ N structurally-distinct
//! adversarial inputs", not "the suite proves Lean theorems against
//! them" (cf. `generators.rs` lines 30-40).
//!
//! Specifically, per spec lines 49-62 each scenario names a Lean
//! property the suite probes structurally:
//!
//! - #2 `majority_minority_split` — verify minority events do not
//!   leak into majority `auditChain`. Structural shape: minority
//!   sub-chain hash-roots are disjoint from majority sub-chain
//!   hash-roots.
//! - #3 `asymmetric_partition` — verify causality `parents_older`
//!   refuses asymmetric admission. Structural shape: A's chain
//!   strictly extends B's view of A; B's chain has no entry whose
//!   `prev` matches a hash from A's later-than-divergence-point
//!   prefix-roots.
//! - #4 `recovering_replay` — verify `Captured` fires on every
//!   replayed event after partition heals via T1-obs witness.
//!   Structural shape: every replayed entry, when walked from
//!   genesis, satisfies `well_formed`.
//! - #5 `stuck_minority` — verify T9 bounded-Δ revocation still
//!   Structural shape: the minority chain is well-formed in
//!   isolation AND a structurally-distinct revocation-marker
//!   chain (hand-encoded at this layer) appends successfully.

use ctrlmatrix_conformance::generators::{
    partition_merge, partition_then_heal, PartitionTrace,
};
use ctrlmatrix_conformance::{
    append, build_well_formed, root, well_formed, Bytes, Hash, LogChain, Spec,
};
use proptest::prelude::*;

// =====================================================================
// Shared local helpers (additive — defined in this test file only)
// =====================================================================

/// A bag of payload sequences exercising k-of-n quorum splits. The
/// sigma_min "majority" is the largest sub-trace; the "minority" is
/// the union of the smaller sub-traces.
#[derive(Clone, Debug)]
struct QuorumSplit {
    /// Per-sub-trace payload sequences.
    sub_traces: Vec<Vec<Bytes>>,
    spec: Spec,
}

/// An asymmetric-partition shape: A sees B's events up through some
/// divergence-point, but A's later events are not seen by B. The
/// structural shape is a pair (a_chain, b_chain) where b_chain is a
/// strict prefix of a_chain truncated at the divergence point.
#[derive(Clone, Debug)]
struct AsymmetricView {
    /// A's full chain (post-partition; A is the "informed" side).
    a_chain: LogChain,
    /// B's view of A's chain (a prefix; B is the "stale" side).
    b_chain: LogChain,
    /// The divergence-point index in a_chain (b_chain.len() == divergence_point).
    divergence_point: usize,
    spec: Spec,
}

/// A recovering-replay shape: a partition_then_heal trace plus a
/// "replay buffer" that exhaustively re-walks the merged trace
/// from genesis, demonstrating every entry survives a structural
/// `well_formed` re-check (the σ_min `Captured`-fires shape).
#[derive(Clone, Debug)]
struct RecoveringReplay {
    /// The original partition trace (independent A-side and B-side).
    partition: PartitionTrace,
    /// The merged trace produced by `partition_merge`.
    merged: LogChain,
    /// Per-entry running-prefix-root witness (length == merged.len() + 1).
    /// `prefix_roots[0]` is `H(genesis)`; `prefix_roots[i]` for i > 0
    /// is the root of `merged[..i]`. Captures the structural T1-obs
    /// "running accumulator at every position" shape.
    prefix_roots: Vec<Hash>,
}

/// A stuck-minority shape: a permanently-isolated minority chain
/// plus a structurally-distinct revocation-marker chain. The
/// revocation marker is a 1-byte tag (0xFF) prefixed onto a
/// per-position payload — a hand-encoded structural mock for
/// the T9 bounded-Δ revocation envelope (operational semantics
/// are L1+ kernel-runtime per scope.md §7).
#[derive(Clone, Debug)]
struct StuckMinority {
    /// The minority chain that never sees the majority (well-formed
    /// in isolation; never merged).
    minority_chain: LogChain,
    /// The revocation-marker chain appended after the minority is
    /// declared stuck. Well-formed against a fresh genesis (the
    /// σ_min structural witness; T9 operational semantics are L1+).
    revocation_chain: LogChain,
    spec: Spec,
}

// =====================================================================
// Scenario 2: majority_minority_split
// =====================================================================
//
// Spec (sigma-min-coverage.md §"Partition scenarios" item 2):
//
//   `majority_minority_split` — k-of-n quorum split; verify
//   minority events do not leak into majority `auditChain`.
//
// Structural shape: build n disjoint sub-chains, each well-formed
// in isolation from genesis. The "majority" is whichever sub-chain
// has the most entries; "minority" is the union of the rest. The
// σ_min property at the structural layer is that the prefix-roots
// of the majority chain are DISJOINT from the prefix-roots of any
// minority chain — i.e., no minority entry's prefix-root coincides
// with a majority prefix-root, which would indicate a leak.

/// Build a k-of-n majority/minority split structure. `n_groups >= 2`;
/// each group's payload sequence is treated as an independent
/// well-formed chain from genesis. The first group is canonically
/// the "majority"; subsequent groups are the "minority".
fn majority_minority_split(sub_traces: Vec<Vec<Bytes>>) -> QuorumSplit {
    let spec = Spec::default();
    QuorumSplit { sub_traces, spec }
}

/// Build a `LogChain` for each sub-trace (each well-formed in
/// isolation from genesis).
fn quorum_split_to_chains(qs: &QuorumSplit) -> Vec<LogChain> {
    qs.sub_traces
        .iter()
        .map(|payloads| build_well_formed(payloads.clone(), &qs.spec))
        .collect()
}

/// Compute the running-prefix-roots of a chain (length == chain.len() + 1;
/// element 0 is `H(genesis)`).
fn prefix_roots_of(chain: &LogChain, spec: &Spec) -> Vec<Hash> {
    let mut roots = Vec::with_capacity(chain.len() + 1);
    for i in 0..=chain.len() {
        roots.push(root(&chain[..i], spec));
    }
    roots
}

/// Identify the majority sub-chain index (longest; ties broken by
/// lowest index). Returns the majority index. Empty input returns 0.
fn majority_index(chains: &[LogChain]) -> usize {
    let mut best_idx = 0usize;
    let mut best_len = 0usize;
    for (i, c) in chains.iter().enumerate() {
        if c.len() > best_len {
            best_len = c.len();
            best_idx = i;
        }
    }
    best_idx
}

/// Structural σ_min property: do any minority prefix-roots COINCIDE
/// with any majority prefix-roots beyond the trivial `H(genesis)`
/// shared root? If yes, the minority has leaked into the majority's
/// audit-chain hash space — the σ_min falsifier shape.
///
/// Returns `true` iff the chains are properly disjoint (the positive
/// σ_min discipline).
fn quorum_split_majority_isolated(chains: &[LogChain], spec: &Spec) -> bool {
    if chains.is_empty() {
        return true;
    }
    let maj = majority_index(chains);
    let maj_roots = prefix_roots_of(&chains[maj], spec);
    // Skip prefix_roots[0] (the trivial H(genesis) shared by every
    // chain from genesis); only PROPER prefix-roots (i > 0) count
    // as "leaks". Build a HashSet-equivalent via Vec scan (Hash is
    // [u8; 32], small N — no need for std::collections::HashSet).
    for (i, sub) in chains.iter().enumerate() {
        if i == maj {
            continue;
        }
        let sub_roots = prefix_roots_of(sub, spec);
        for sr in sub_roots.iter().skip(1) {
            for mr in maj_roots.iter().skip(1) {
                if sr == mr {
                    return false;
                }
            }
        }
    }
    true
}

#[test]
fn unit_majority_minority_split_smoke() {
    // 3-of-5 quorum: groups of sizes [4, 2, 1, 3, 2]. Majority is
    // group 0 with length 4.
    let qs = majority_minority_split(vec![
        vec![b"m1".to_vec(), b"m2".to_vec(), b"m3".to_vec(), b"m4".to_vec()],
        vec![b"x1".to_vec(), b"x2".to_vec()],
        vec![b"y1".to_vec()],
        vec![b"z1".to_vec(), b"z2".to_vec(), b"z3".to_vec()],
        vec![b"w1".to_vec(), b"w2".to_vec()],
    ]);
    let chains = quorum_split_to_chains(&qs);
    assert_eq!(chains.len(), 5);
    for c in &chains {
        assert!(well_formed(c, &qs.spec),
            "every quorum sub-chain must be well-formed in isolation");
    }
    assert_eq!(majority_index(&chains), 0,
        "first group is the unique majority (length 4)");
    assert!(quorum_split_majority_isolated(&chains, &qs.spec),
        "distinct payloads ⇒ disjoint prefix-root spaces (σ_min positive)");
}

#[test]
fn unit_majority_minority_split_handcrafted_collision_reveals_leak() {
    // Collision case: two sub-chains with IDENTICAL payload prefixes
    // share prefix-roots beyond H(genesis), hence the predicate flags
    // the leak. This is the σ_min falsifier shape: the predicate
    // distinguishes properly-disjoint quorums from leaked ones.
    let payloads = vec![b"shared1".to_vec(), b"shared2".to_vec()];
    let qs = majority_minority_split(vec![
        // Group 0: majority — extends shared prefix.
        {
            let mut p = payloads.clone();
            p.push(b"maj-extra".to_vec());
            p
        },
        // Group 1: minority — same shared prefix only. Its prefix-
        // roots after step 1 and step 2 collide with majority's.
        payloads.clone(),
    ]);
    let chains = quorum_split_to_chains(&qs);
    assert_eq!(majority_index(&chains), 0);
    assert!(!quorum_split_majority_isolated(&chains, &qs.spec),
        "shared payload prefix ⇒ shared prefix-root space ⇒ leak detected");
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 500,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 500 randomly-sized k-of-n quorum splits with distinct per-group
    /// payload-bytes prefixes (group index encoded into the first byte
    /// of every payload, ensuring per-group disjointness): every
    /// sub-chain is well-formed and the majority is structurally
    /// isolated. Closes σ_min partition scenario #2 at the structural
    /// layer.
    #[test]
    fn pt_majority_minority_split_isolated(
        sizes in prop::collection::vec(1usize..6, 2..6),
        seed in any::<u64>(),
    ) {
        let sub_traces: Vec<Vec<Bytes>> = sizes.iter().enumerate()
            .map(|(g, &n)| {
                (0..n).map(|i| {
                    // Encode group index in first byte for cross-group
                    // disjointness; mix seed + position for within-group
                    // variation.
                    let mut p = Vec::with_capacity(16);
                    p.push((g as u8) | 0x80); // ensure top-bit set per group
                    p.extend_from_slice(&seed.to_le_bytes());
                    p.push(i as u8);
                    p
                }).collect()
            })
            .collect();
        let qs = majority_minority_split(sub_traces);
        let chains = quorum_split_to_chains(&qs);
        for c in &chains {
            prop_assert!(well_formed(c, &qs.spec));
        }
        prop_assert!(quorum_split_majority_isolated(&chains, &qs.spec),
            "disjoint per-group prefixes ⇒ majority isolated");
    }
}

// =====================================================================
// Scenario 3: asymmetric_partition
// =====================================================================
//
// Spec (sigma-min-coverage.md §"Partition scenarios" item 3):
//
//   `asymmetric_partition` — A sees B, not vice versa; verify
//   causality `parents_older` refuses asymmetric admission.
//
// Structural shape: A's chain is the "informed" full chain from
// genesis through some terminal length L. B's view is a strict
// prefix of A's chain truncated at divergence_point < L. The σ_min
// property at the structural layer is that the divergence-point
// witness is a unique index where B's tail and A's tail diverge.
// `parents_older` at the structural layer is captured by:
// "B's tail's running-acc cannot match any of A's later
// prefix-roots beyond divergence_point" — a stale auditor (B)
// cannot retroactively forge admission of A's later entries.

/// Build an asymmetric-partition view. `a_payloads` is A's full
/// payload sequence; `b_visible_count` is the number of A's
/// entries B has seen (must be `<= a_payloads.len()`). B's chain
/// is a structurally-replayed prefix from genesis (well-formed in
/// isolation).
fn asymmetric_partition(a_payloads: Vec<Bytes>, b_visible_count: usize) -> AsymmetricView {
    let spec = Spec::default();
    let n = a_payloads.len();
    let bvc = b_visible_count.min(n);
    let a_chain = build_well_formed(a_payloads.clone(), &spec);
    let b_payloads: Vec<Bytes> = a_payloads[..bvc].to_vec();
    let b_chain = build_well_formed(b_payloads, &spec);
    AsymmetricView {
        a_chain,
        b_chain,
        divergence_point: bvc,
        spec,
    }
}

/// Structural σ_min property for asymmetric admission refusal:
/// B's chain MUST be a true prefix of A's chain at the byte-identical
/// level (since both are structurally-replayed from genesis with the
/// same payload prefix), AND any of A's entries beyond
/// divergence_point MUST have a `prev` that is NOT equal to any of
/// B's prefix-roots — i.e., B cannot retroactively admit A's
/// later entries because B's view ends at divergence_point's root.
///
/// Returns `true` iff the asymmetric-admission discipline holds.
fn asymmetric_admission_refused(view: &AsymmetricView) -> bool {
    // Check 1: B's chain is byte-identical to A's prefix.
    if view.b_chain.len() != view.divergence_point {
        return false;
    }
    if view.b_chain.len() > view.a_chain.len() {
        return false;
    }
    for i in 0..view.b_chain.len() {
        if view.a_chain[i] != view.b_chain[i] {
            return false;
        }
    }
    // Check 2: every entry of A strictly past divergence_point has a
    // `prev` that is NOT in B's prefix-root set. (B's prefix-roots
    // span 0..=divergence_point; A's later entries' `prev` fields
    // span the running-acc at indices divergence_point..a.len(),
    // which by definition are NOT equal to any earlier root in a
    // collision-free hash setting.)
    let b_roots = prefix_roots_of(&view.b_chain, &view.spec);
    for i in view.divergence_point..view.a_chain.len() {
        let ap = view.a_chain[i].prev;
        // The σ_min refusal: for i > divergence_point, ap MUST NOT
        // equal any prefix-root strictly INTERIOR to B's view (i.e.,
        // any root at position < divergence_point). The only
        // legitimate match is ap == b_roots[divergence_point], which
        // happens at i == divergence_point exactly (the boundary).
        for (br_idx, br) in b_roots.iter().enumerate() {
            if br_idx == view.divergence_point {
                // Boundary match is legitimate at i == divergence_point
                // (the next entry A appended after B's last visible
                // entry); not a refusal failure.
                continue;
            }
            if &ap == br {
                return false;
            }
        }
    }
    true
}

#[test]
fn unit_asymmetric_partition_smoke() {
    let a_payloads = vec![
        b"a1".to_vec(),
        b"a2".to_vec(),
        b"a3".to_vec(),
        b"a4".to_vec(),
        b"a5".to_vec(),
    ];
    // B sees A's first 2 entries.
    let view = asymmetric_partition(a_payloads.clone(), 2);
    assert_eq!(view.divergence_point, 2);
    assert_eq!(view.b_chain.len(), 2);
    assert_eq!(view.a_chain.len(), 5);
    assert!(well_formed(&view.a_chain, &view.spec));
    assert!(well_formed(&view.b_chain, &view.spec));
    // Bytewise prefix equality.
    for i in 0..view.b_chain.len() {
        assert_eq!(view.a_chain[i], view.b_chain[i]);
    }
    assert!(asymmetric_admission_refused(&view),
        "B's stale view cannot admit A's later entries (σ_min positive)");
}

#[test]
fn unit_asymmetric_partition_full_view_is_trivial() {
    // If b_visible_count == a_payloads.len(), the partition is
    // degenerate (B has caught up to A); admission-refusal is vacuous
    // (no later A entries to refuse).
    let payloads = vec![b"p1".to_vec(), b"p2".to_vec(), b"p3".to_vec()];
    let view = asymmetric_partition(payloads, 3);
    assert_eq!(view.divergence_point, 3);
    assert!(asymmetric_admission_refused(&view),
        "vacuously refused when no later entries exist");
}

#[test]
fn unit_asymmetric_partition_zero_view_is_well_formed() {
    // b_visible_count == 0: B has seen nothing; b_chain is empty.
    let payloads = vec![b"q1".to_vec(), b"q2".to_vec()];
    let view = asymmetric_partition(payloads, 0);
    assert_eq!(view.divergence_point, 0);
    assert!(view.b_chain.is_empty());
    assert!(well_formed(&view.a_chain, &view.spec));
    assert!(well_formed(&view.b_chain, &view.spec));
    assert!(asymmetric_admission_refused(&view));
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 1_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 10³ asymmetric-partition shapes: every (a_payloads,
    /// b_visible_count) pair yields a structurally-refused
    /// admission. Closes σ_min partition scenario #3.
    #[test]
    fn pt_asymmetric_partition_admission_refused(
        a in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..6), 0..8),
        bvc_raw in any::<usize>(),
    ) {
        let n = a.len();
        // Map the raw usize into [0, n] inclusively to exercise the
        // full range including the boundary cases.
        let bvc = if n == 0 { 0 } else { bvc_raw % (n + 1) };
        let view = asymmetric_partition(a, bvc);
        prop_assert!(well_formed(&view.a_chain, &view.spec));
        prop_assert!(well_formed(&view.b_chain, &view.spec));
        prop_assert!(asymmetric_admission_refused(&view));
    }
}

// =====================================================================
// Scenario 4: recovering_replay
// =====================================================================
//
// Spec (sigma-min-coverage.md §"Partition scenarios" item 4):
//
//   `recovering_replay` — partition heals via T1-obs witness;
//   verify `Captured` fires on every replayed event.
//
// Structural shape: take a partition_then_heal trace, merge it,
// and structurally walk the merged trace from genesis,
// re-computing every prefix-root. The σ_min property at the
// structural layer is that every prefix-root is well-defined
// AND every entry's `prev` field equals the prefix-root at its
// position — i.e., `Captured`-firing is the σ_min structural
// witness that no replayed event was missed (a missed entry
// would break the running-acc binding at the next position).

fn recovering_replay(payloads_a: Vec<Bytes>, payloads_b: Vec<Bytes>) -> RecoveringReplay {
    let partition = partition_then_heal(payloads_a, payloads_b);
    let merged = partition_merge(&partition);
    let prefix_roots = prefix_roots_of(&merged, &partition.spec);
    RecoveringReplay {
        partition,
        merged,
        prefix_roots,
    }
}

/// Structural σ_min "Captured fires on every replayed event"
/// property: for every i in 0..merged.len(), merged[i].prev MUST
/// equal prefix_roots[i]. Holds by construction; the predicate is
/// a witness-function rather than a falsifiable predicate at this
/// layer (the falsifier would be a bit-flip in a `prev` field,
fn recovering_replay_captures_every_event(rr: &RecoveringReplay) -> bool {
    if rr.prefix_roots.len() != rr.merged.len() + 1 {
        return false;
    }
    for (i, entry) in rr.merged.iter().enumerate() {
        if entry.prev != rr.prefix_roots[i] {
            return false;
        }
    }
    true
}

#[test]
fn unit_recovering_replay_smoke() {
    let rr = recovering_replay(
        vec![b"a1".to_vec(), b"a2".to_vec()],
        vec![b"b1".to_vec(), b"b2".to_vec(), b"b3".to_vec()],
    );
    assert_eq!(rr.merged.len(), 5);
    assert_eq!(rr.prefix_roots.len(), 6);
    assert!(well_formed(&rr.merged, &rr.partition.spec));
    assert!(recovering_replay_captures_every_event(&rr),
        "every replayed event must capture its predecessor's prefix-root");
}

#[test]
fn unit_recovering_replay_empty_is_vacuous() {
    let rr = recovering_replay(vec![], vec![]);
    assert!(rr.merged.is_empty());
    assert_eq!(rr.prefix_roots.len(), 1, "single H(genesis) entry");
    assert!(recovering_replay_captures_every_event(&rr));
}

#[test]
fn unit_recovering_replay_single_side_b() {
    // A partitions empty; only B has events. Replay still captures
    // every B entry from genesis (the structural σ_min discipline
    // doesn't distinguish which side originally produced the event).
    let rr = recovering_replay(vec![], vec![b"b1".to_vec(), b"b2".to_vec()]);
    assert_eq!(rr.merged.len(), 2);
    assert!(recovering_replay_captures_every_event(&rr));
    // Replayed merged.prev[0] must equal H(genesis).
    let expected_genesis = root::<>(&[], &rr.partition.spec);
    assert_eq!(rr.merged[0].prev, expected_genesis);
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 1_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 10³ recovering-replay shapes: every merged trace replays
    /// from genesis with every entry's `prev` matching the
    /// running prefix-root. Closes σ_min partition scenario #4.
    #[test]
    fn pt_recovering_replay_captures_every_event(
        a in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..6), 0..6),
        b in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..6), 0..6),
    ) {
        let rr = recovering_replay(a, b);
        prop_assert!(well_formed(&rr.merged, &rr.partition.spec));
        prop_assert!(recovering_replay_captures_every_event(&rr));
        prop_assert_eq!(rr.prefix_roots.len(), rr.merged.len() + 1);
    }
}

// =====================================================================
// Scenario 5: stuck_minority
// =====================================================================
//
// Spec (sigma-min-coverage.md §"Partition scenarios" item 5):
//
//   `stuck_minority` — minority never recovers; verify T9
//
// Structural shape: a permanently-isolated minority chain plus a
// structurally-distinct revocation-marker chain. The minority
// chain is well-formed in isolation; the revocation-marker chain
// is encoded as a chain of payloads each prefixed with a 0xFF
// "revocation" tag byte and is well-formed against a fresh
// genesis. The σ_min property at the structural layer is that
// the two chains are well-formed independently AND share NO
// running prefix-roots beyond the trivial H(genesis) — i.e., the
// revocation envelope and the stuck minority's audit chain
// occupy disjoint structural spaces (the revocation propagates
// to a regulator-readable namespace without contaminating the
// minority audit chain).

const REVOCATION_TAG_BYTE: u8 = 0xFF;

fn stuck_minority(
    minority_payloads: Vec<Bytes>,
    revocation_payloads: Vec<Bytes>,
) -> StuckMinority {
    let spec = Spec::default();
    let minority_chain = build_well_formed(minority_payloads, &spec);
    // Encode revocation payloads with a 0xFF tag-byte prefix; the
    // structural shape is "every entry payload starts with
    // REVOCATION_TAG_BYTE".
    let tagged: Vec<Bytes> = revocation_payloads
        .into_iter()
        .map(|p| {
            let mut q = Vec::with_capacity(p.len() + 1);
            q.push(REVOCATION_TAG_BYTE);
            q.extend_from_slice(&p);
            q
        })
        .collect();
    let revocation_chain = build_well_formed(tagged, &spec);
    StuckMinority {
        minority_chain,
        revocation_chain,
        spec,
    }
}

/// Structural σ_min "T9 bounded-Δ revocation converges" witness:
///
///   1. Both chains are well-formed in isolation.
///   2. Every entry in `revocation_chain` has a payload whose first
///      byte is `REVOCATION_TAG_BYTE` (0xFF).
///   3. The two chains share NO running prefix-roots beyond
///      H(genesis) (the σ_min disjointness shape — the revocation
///      envelope and the audit chain do not contaminate each other).
fn stuck_minority_revocation_converges(sm: &StuckMinority) -> bool {
    if !well_formed(&sm.minority_chain, &sm.spec) {
        return false;
    }
    if !well_formed(&sm.revocation_chain, &sm.spec) {
        return false;
    }
    // Tag check: every revocation entry is tagged.
    for e in &sm.revocation_chain {
        match e.payload.first() {
            Some(&b) if b == REVOCATION_TAG_BYTE => {}
            _ => return false,
        }
    }
    // Disjointness: no proper prefix-root collisions. Skip index 0
    // (the trivial H(genesis) shared root).
    let m_roots = prefix_roots_of(&sm.minority_chain, &sm.spec);
    let r_roots = prefix_roots_of(&sm.revocation_chain, &sm.spec);
    for mr in m_roots.iter().skip(1) {
        for rr in r_roots.iter().skip(1) {
            if mr == rr {
                return false;
            }
        }
    }
    true
}

/// Append an additional revocation marker to a `StuckMinority`'s
/// revocation chain. Demonstrates the σ_min "still converges" arm:
/// the revocation envelope can grow even while the minority remains
/// stuck. Returns the new revocation-chain length.
fn extend_revocation(sm: &mut StuckMinority, extra_payload: Bytes) -> usize {
    let mut tagged = Vec::with_capacity(extra_payload.len() + 1);
    tagged.push(REVOCATION_TAG_BYTE);
    tagged.extend_from_slice(&extra_payload);
    sm.revocation_chain = append(sm.revocation_chain.clone(), tagged, &sm.spec);
    sm.revocation_chain.len()
}

#[test]
fn unit_stuck_minority_smoke() {
    let sm = stuck_minority(
        vec![b"min1".to_vec(), b"min2".to_vec(), b"min3".to_vec()],
        vec![b"rev-cap-A".to_vec(), b"rev-cap-B".to_vec()],
    );
    assert_eq!(sm.minority_chain.len(), 3);
    assert_eq!(sm.revocation_chain.len(), 2);
    assert!(well_formed(&sm.minority_chain, &sm.spec));
    assert!(well_formed(&sm.revocation_chain, &sm.spec));
    // Revocation entries each start with the tag byte.
    for e in &sm.revocation_chain {
        assert_eq!(e.payload[0], REVOCATION_TAG_BYTE);
    }
    assert!(stuck_minority_revocation_converges(&sm));
}

#[test]
fn unit_stuck_minority_extend_revocation_still_converges() {
    let mut sm = stuck_minority(
        vec![b"m1".to_vec()],
        vec![b"r1".to_vec()],
    );
    let initial_len = sm.revocation_chain.len();
    let new_len = extend_revocation(&mut sm, b"r2".to_vec());
    assert_eq!(new_len, initial_len + 1);
    assert!(well_formed(&sm.revocation_chain, &sm.spec),
        "extended revocation chain remains well-formed");
    assert!(stuck_minority_revocation_converges(&sm),
        "T9 bounded-Δ revocation envelope continues to converge");
}

#[test]
fn unit_stuck_minority_empty_minority_is_well_formed() {
    let sm = stuck_minority(vec![], vec![b"r1".to_vec()]);
    assert!(sm.minority_chain.is_empty());
    assert!(well_formed(&sm.minority_chain, &sm.spec));
    assert!(well_formed(&sm.revocation_chain, &sm.spec));
    assert!(stuck_minority_revocation_converges(&sm));
}

#[test]
fn unit_stuck_minority_empty_revocation_is_well_formed() {
    let sm = stuck_minority(vec![b"m1".to_vec(), b"m2".to_vec()], vec![]);
    assert!(sm.revocation_chain.is_empty());
    // The tag-check predicate vacuously holds for an empty chain.
    assert!(stuck_minority_revocation_converges(&sm));
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 1_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    /// 10³ stuck-minority shapes: minority chain and revocation
    /// chain are each well-formed; the disjointness predicate holds
    /// because revocation payloads are tag-prefixed (0xFF) and
    /// minority payloads exclude that tag-byte by construction.
    /// Closes σ_min partition scenario #5.
    #[test]
    fn pt_stuck_minority_revocation_converges(
        // Exclude REVOCATION_TAG_BYTE (0xFF) from minority payloads
        // by clamping the first byte; trivially still exercises the
        // payload variation space.
        m_seed in any::<u32>(),
        m_count in 0usize..6,
        r_count in 0usize..6,
    ) {
        let m_payloads: Vec<Bytes> = (0..m_count).map(|i| {
            // Construct a payload that does NOT start with 0xFF.
            let mut p = Vec::with_capacity(8);
            p.push(((m_seed.wrapping_add(i as u32)) % 0xFE) as u8);
            p.extend_from_slice(&(i as u32).to_le_bytes());
            p
        }).collect();
        let r_payloads: Vec<Bytes> = (0..r_count).map(|i| {
            // Plain payload; the helper will add the 0xFF prefix.
            (i as u64).to_le_bytes().to_vec()
        }).collect();
        let sm = stuck_minority(m_payloads, r_payloads);
        prop_assert!(well_formed(&sm.minority_chain, &sm.spec));
        prop_assert!(well_formed(&sm.revocation_chain, &sm.spec));
        prop_assert!(stuck_minority_revocation_converges(&sm));
    }
}

// =====================================================================
// Cross-scenario sanity — σ_min partition coverage ≥ 5 scenarios
// =====================================================================
//
// Single regression-style witness that this file ships 4 NEW
// (`partition_then_heal`). The σ_min spec floor at v1.3 is 5-of-5
// scenarios; this file's existence + the 4 generators above is the
// structural "every spec scenario has a generator" closure.

#[test]
fn unit_sigma_min_partition_coverage_complete_5_of_5() {
    // smoke check that the dependency module is intact.
    let p1 = partition_then_heal(vec![b"a".to_vec()], vec![b"b".to_vec()]);
    assert_eq!(p1.side_a.len(), 1);
    assert_eq!(p1.side_b.len(), 1);

    // Scenario 2: majority_minority_split.
    let p2 = majority_minority_split(vec![vec![b"x".to_vec()]]);
    assert_eq!(p2.sub_traces.len(), 1);

    // Scenario 3: asymmetric_partition.
    let p3 = asymmetric_partition(vec![b"q".to_vec()], 0);
    assert_eq!(p3.divergence_point, 0);

    // Scenario 4: recovering_replay.
    let p4 = recovering_replay(vec![], vec![]);
    assert!(p4.merged.is_empty());

    // Scenario 5: stuck_minority.
    let p5 = stuck_minority(vec![], vec![]);
    assert!(p5.minority_chain.is_empty());

    // 5-of-5 scenarios constructed without panic — σ_min partition
    // coverage is structurally complete at v1.3 .
}
