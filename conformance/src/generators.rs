//!
//! This module ships the post-v1.1.1 generators for the σ_min
//! coverage parameters published at `spec/sigma-min-coverage.md`
//! IMPLEMENTS the harness; deployments PARAMETERIZE the actual run
//! discipline — see scope.md §8 deployment-policy obligations).
//!
//! ## Coverage parameters and what's implemented at v1.1.1
//!
//! the full σ_min envelope):
//!
//! | Parameter                   | Implemented      | Carry-forward |
//! |-----------------------------|------------------|---------------|
//! | Cap derivation depth 1–16   | YES (full)       | —             |
//! | Lattice path length 1–L_MAX | YES (L_MAX=48)   | —             |
//! | Partition scenarios         | 1 of 5 (#1)      | scenarios 2-5 |
//! | Contract-violation classes  | 1 of 5 (#1)      | classes 2-5   |
//! | Replay divergence ≥ 10⁶     | parameterized N  | full 10⁶ floor (deployment-policy obligation per scope.md §8) |
//! | Adversarial label-flow      | 1 of 5 (#1)      | classes 2-5   |
//!
//! The v1.1.1 default replay-divergence N = 10⁴ (NOT 10⁶) — the 10⁶
//! floor is a deployment-policy obligation, not a CI obligation,
//! IMPLEMENTS the harness, deployments PARAMETERIZE the actual run"
//! discipline.
//!
//! ## Honest naming
//!
//! These generators implement **structural shapes**, not operational
//! semantics for any module. The structures here cover the
//! adversarial input grammar shapes per the spec; cross-binding
//! these shapes back to the M3/M5/M7 abstract operational semantics
//! is L1+ kernel-runtime work and is OUT-OF-SCOPE for v1.1.1.
//! Generators here intentionally ship as `Vec<...>`-shaped traces /
//! chains / paths — the σ_min floor is "the suite enumerates ≥ N
//! structurally-distinct adversarial inputs", not "the suite proves
//! Lean theorems against them".
//!
//! ## Where each generator hooks the existing M6 chassis
//!
//! Each generator is a constructive function returning a
//! deterministic structure given seed + parameters; a thin wrapper
//! lifts it to a proptest `Strategy` for use inside `proptest!` test
//! blocks. The cross-binding to the existing `well_formed` /
//! `LogChain` chassis from `lib.rs` is intentional: the
//! `cap_chain_to_log_chain` adapter shows that a σ_min cap-chain
//! generator and the M6 hash-chain mutators COMPOSE under a single
//! conformance harness (this is the H2  counter — that the
//! new generators are not bolt-ons but feed the existing M6 test
//! chassis).

use crate::{append, build_well_formed, Bytes, Hash, LogChain, Spec};

// =====================================================================
// 1. Cap derivation depth 1–16 generator
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Cap derivation depth: 1–16"):
//
//   Capability delegation chains exercised by the suite MUST cover
//   depth 1 (root mint, parent = none) through depth 16 (15 nested
//   Delegate from a root mint).
//
// Structural model: a `CapId` is a fixed-width opaque identifier
// (Bytes); a `CapChain` is a Vec<CapEntry> where each entry binds a
// `parent : Option<CapId>` to a derived `cap_id : CapId`. Depth N
// means the chain has N entries; entry 0 is the root mint
// (parent = None); entries 1..N-1 each delegate from the previous
// entry's `cap_id`.
//
// This is the cap-chain shape the M5 closure invariant guards in
// `lean/AgentKernel/Caps.lean` (Capability.parent : Option
// CapId), but we ship STRUCTURE only — the L1+ abstract operational
// semantics (`store : CapStore`) is NOT mirrored here. Per scope.md
// §7 "M5 forward bindings", L0 ships the structural type discipline;
// kernel-runtime semantics are L1+ TCB.

/// A capability identifier. Fixed 32-byte width (parallel to the M6
/// `Hash` type — both are 256-bit opaque identifiers in the
/// deployment-realistic envelope; the structural σ_min shape does
/// not depend on the width choice).
pub type CapId = [u8; 32];

/// A single entry in a capability delegation chain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapEntry {
    /// `None` ↔ root mint (depth-1 head); `Some(parent_cap_id)`
    /// otherwise. Mirrors `Capability.parent : Option CapId` from
    /// `Caps.lean`.
    pub parent: Option<CapId>,
    /// Identifier of this cap. Deterministic function of seed +
    /// position; the closure invariant requires every non-root
    /// entry's `parent` to point at some cap actually present in
    /// the chain prefix.
    pub cap_id: CapId,
}

/// A capability delegation chain. `chain[0]` is the root mint;
/// `chain[i]` for i > 0 delegates from `chain[i-1].cap_id`.
pub type CapChain = Vec<CapEntry>;

/// The σ_min cap-derivation-depth floor (per spec §"Cap derivation
/// depth: 1–16").
pub const CAP_DEPTH_MIN: usize = 1;

/// The σ_min cap-derivation-depth ceiling (per spec §"Cap derivation
/// depth: 1–16"; deployment-realistic envelope).
pub const CAP_DEPTH_MAX: usize = 16;

/// Build a well-formed `CapChain` of exact `depth` from a 32-bit seed.
/// Depth 1 ↔ a single root-mint entry; depth N ↔ root + (N-1) nested
/// delegates. Closure invariant holds by construction.
///
/// Determinism: total. The `seed` parameter selects a chain from the
/// 2^32 family; the same seed always yields the same chain.
pub fn cap_chain_from_seed(depth: usize, seed: u32) -> CapChain {
    assert!(depth >= CAP_DEPTH_MIN, "depth must be >= {}", CAP_DEPTH_MIN);
    let mut chain = CapChain::with_capacity(depth);
    for i in 0..depth {
        // Build a deterministic 32-byte cap_id from seed + position.
        let mut cap_id: CapId = [0u8; 32];
        cap_id[0..4].copy_from_slice(&seed.to_le_bytes());
        cap_id[4..8].copy_from_slice(&(i as u32).to_le_bytes());
        // Tag bytes 8..16 with a stable marker to keep the
        // identifier shape distinct from raw indices.
        cap_id[8..16].copy_from_slice(b"capid___");
        let parent = if i == 0 {
            None
        } else {
            Some(chain[i - 1].cap_id)
        };
        chain.push(CapEntry { parent, cap_id });
    }
    chain
}

/// Closure-invariant predicate on a `CapChain`. Mirrors the M5
/// closure invariant statement from `Caps.lean` at the structural
/// layer: every non-root entry's `parent` MUST equal the immediately
/// prior entry's `cap_id` (the chain is a linear-delegate ladder,
/// not a forest — the σ_min floor exercises ladders only; trees are
/// L1+).
pub fn cap_chain_closure_holds(chain: &CapChain) -> bool {
    if chain.is_empty() {
        // Empty chain is degenerate — depth 0 is below σ_min floor.
        // Treat as not-closure-holding to flag the caller.
        return false;
    }
    if chain[0].parent.is_some() {
        return false;
    }
    for i in 1..chain.len() {
        match chain[i].parent {
            Some(p) if p == chain[i - 1].cap_id => continue,
            _ => return false,
        }
    }
    true
}

/// Adversarial mutator: substitute a non-root entry's `parent` with
/// a `CapId` not present in the chain prefix. Falsifies the closure
/// invariant. Used by the σ_min "forged_parent" contract-violation
/// class (spec §"Contract violation grammar" item 4).
pub fn forge_cap_parent(chain: &CapChain, idx: usize, garbage: CapId) -> Option<CapChain> {
    if idx == 0 || idx >= chain.len() {
        return None;
    }
    let mut out = chain.clone();
    out[idx].parent = Some(garbage);
    Some(out)
}

// proptest `Strategy` lifters live in the test files
// (`tests/sigma_min_*.rs`) — the `proptest` crate is a `dev-dependency`
// only. Tests construct strategies directly via
// `(CAP_DEPTH_MIN..=CAP_DEPTH_MAX, any::<u32>()).prop_map(...)`.

// =====================================================================
// 2. Lattice path length 1–L_MAX generator
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Lattice path length: 1–L_MAX"):
//
//   L_MAX is defined as |Σ_C| × |Σ_I| × |Σ_P|. Reference sizes
//   4 × 3 × 4 = 48 ⇒ L_MAX ≤ 48.
//
// A `LatticeLabel` is a triple (c_idx, i_idx, p_idx) drawn from
// discipline). A `LatticePath` is a Vec<LatticeLabel>; the σ_min
// floor exercises lengths 1..=L_MAX.

/// Reference confidentiality alphabet size (Σ_C, scope.md §7).
pub const SIGMA_C: usize = 4;
/// Reference integrity alphabet size (Σ_I, scope.md §7).
pub const SIGMA_I: usize = 3;
/// Reference provenance alphabet size (Σ_P, scope.md §7).
pub const SIGMA_P: usize = 4;
/// L_MAX = Σ_C × Σ_I × Σ_P = 48 (reference; deployments re-derive
/// against their own product).
pub const L_MAX: usize = SIGMA_C * SIGMA_I * SIGMA_P;

/// A label drawn from the IFC lattice product Σ_C × Σ_I × Σ_P.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LatticeLabel {
    pub c_idx: u8,
    pub i_idx: u8,
    pub p_idx: u8,
}

impl LatticeLabel {
    /// Decode a flat 0..L_MAX index into the lattice triple.
    /// Non-repeating across [0, L_MAX) when used as a sweep.
    pub fn from_flat(idx: usize) -> Self {
        let idx = idx % L_MAX;
        let p = idx % SIGMA_P;
        let i = (idx / SIGMA_P) % SIGMA_I;
        let c = (idx / (SIGMA_P * SIGMA_I)) % SIGMA_C;
        LatticeLabel {
            c_idx: c as u8,
            i_idx: i as u8,
            p_idx: p as u8,
        }
    }

    /// Pointwise join of two labels (each component is a max-lattice
    /// at the structural layer; semantic lattice operations are L1+).
    /// Mirrors `wellLabeledStep`'s `outLabel >= join parents.outLabel`
    /// shape () at the structural σ_min level.
    pub fn join(&self, other: &LatticeLabel) -> LatticeLabel {
        LatticeLabel {
            c_idx: self.c_idx.max(other.c_idx),
            i_idx: self.i_idx.max(other.i_idx),
            p_idx: self.p_idx.max(other.p_idx),
        }
    }

    /// Pointwise `<=` predicate: `self <= other` iff every component
    /// is `<=` componentwise. This is the σ_min structural ordering;
    /// the L0 IFC lattice's actual semantics are owned by `IFC.lean`.
    pub fn leq(&self, other: &LatticeLabel) -> bool {
        self.c_idx <= other.c_idx
            && self.i_idx <= other.i_idx
            && self.p_idx <= other.p_idx
    }
}

/// A lattice path: an ordered sequence of labels.
pub type LatticePath = Vec<LatticeLabel>;

/// Build a non-repeating lattice path of exact `len` from a seed.
/// `len` MUST be in [1, L_MAX]. The path enumerates labels via a
/// seeded permutation of [0, L_MAX); for `len == L_MAX` the path
/// covers the full alphabet without repetition.
pub fn lattice_path_from_seed(len: usize, seed: u64) -> LatticePath {
    assert!(len >= 1 && len <= L_MAX, "len must be in [1, {}]", L_MAX);
    // Generate a deterministic permutation of [0, L_MAX) by sorting
    // indices keyed on a seed-mixed hash (small and total — no rng
    // dep; sha2 already in our deps but overkill here, use a simple
    // Wang-style mixer).
    let mut keyed: Vec<(u64, usize)> = (0..L_MAX)
        .map(|i| {
            let mut x = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15);
            x ^= (i as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
            x ^= x >> 31;
            (x, i)
        })
        .collect();
    keyed.sort_by_key(|(k, _)| *k);
    keyed
        .into_iter()
        .take(len)
        .map(|(_, idx)| LatticeLabel::from_flat(idx))
        .collect()
}

/// Predicate: does the path satisfy  monotone-join?
/// Structural shape: every prefix's running join is `<=` the next
/// label (i.e., the next label is at-or-above the running join).
/// This is the structural σ_min check for `wellLabeledStep` — the
/// abstract operational semantics live in `IFC.lean`.
pub fn lattice_path_monotone(path: &LatticePath) -> bool {
    if path.is_empty() {
        return true;
    }
    let mut acc = path[0].clone();
    for label in &path[1..] {
        // Step's outLabel is `label`; its join-of-parents under the
        // single-event monotone shape is `acc`.  requires
        // `acc <= label`.
        if !acc.leq(label) {
            return false;
        }
        acc = acc.join(label);
    }
    true
}

/// Build a monotone-by-construction path: pick `len` labels in
/// componentwise non-decreasing order. Always satisfies
/// `lattice_path_monotone`. Used as the positive σ_min lattice-path
/// generator.
pub fn lattice_path_monotone_from_seed(len: usize, seed: u64) -> LatticePath {
    assert!(len >= 1 && len <= L_MAX, "len must be in [1, {}]", L_MAX);
    let mut path = LatticePath::with_capacity(len);
    let mut c: u8 = 0;
    let mut i: u8 = 0;
    let mut p: u8 = 0;
    for step in 0..len {
        path.push(LatticeLabel {
            c_idx: c,
            i_idx: i,
            p_idx: p,
        });
        // Advance one component, prefer wrap+carry to stay monotone:
        let mix = seed.wrapping_add(step as u64);
        let pick = (mix % 3) as u8;
        match pick {
            0 if (p as usize) < SIGMA_P - 1 => p += 1,
            1 if (i as usize) < SIGMA_I - 1 => i += 1,
            _ if (c as usize) < SIGMA_C - 1 => c += 1,
            // Saturated — keep label fixed; stays monotone (`<=` reflexive).
            _ => {}
        }
    }
    path
}

/// Adversarial mutator: emit a label strictly below the running
/// join. Falsifies `lattice_path_monotone`. This is the σ_min
/// "monotone_violation" label-flow class (spec §"Adversarial label
/// flow grammar" item 1).
pub fn lattice_path_inject_monotone_violation(
    path: &LatticePath,
    idx: usize,
) -> Option<LatticePath> {
    if idx == 0 || idx >= path.len() {
        return None;
    }
    // Find a strictly-lower label than path[idx-1]; if path[idx-1]
    // is already (0,0,0) the violation is impossible — return None.
    let high = &path[idx - 1];
    if high.c_idx == 0 && high.i_idx == 0 && high.p_idx == 0 {
        return None;
    }
    let low = LatticeLabel {
        c_idx: high.c_idx.saturating_sub(1),
        i_idx: high.i_idx.saturating_sub(1),
        p_idx: high.p_idx.saturating_sub(1),
    };
    if !low.leq(high) || low == *high {
        return None;
    }
    // Confirm low is strictly-below by some component:
    if low.c_idx == high.c_idx && low.i_idx == high.i_idx && low.p_idx == high.p_idx {
        return None;
    }
    let mut out = path.clone();
    out[idx] = low;
    Some(out)
}

// See note above re: `arb_*` strategy lifters living in test files.

// =====================================================================
// 3. Partition scenario #1 — partition_then_heal
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Partition scenarios" item 1):
//
//   `partition_then_heal` — split into disjoint sub-traces; merge
//   after resolution; verify // on merged trace.
//
// v1.1.1 ships this scenario only; scenarios 2..5 (majority_minority,
// asymmetric, recovering_replay, stuck_minority) carry forward to
// post-v1.1.1  as documented in the H1 inventory.
//
// Structural model: a "trace" here is a `LogChain` (using the
// existing M6 chassis); a partition is two disjoint sub-LogChains
// each built from genesis; a merge concatenates them into a single
// trace by re-appending the second's payloads onto the first's tail.

/// A partition trace pair: two sub-traces built from the same
/// genesis but never crossing during the partition.
#[derive(Clone, Debug)]
pub struct PartitionTrace {
    pub side_a: LogChain,
    pub side_b: LogChain,
    pub spec: Spec,
}

/// Build a `partition_then_heal` scenario: side_a and side_b are
/// each well-formed independently from genesis. The merged trace
/// (returned by `partition_merge`) re-appends side_b's payloads
/// onto side_a's tail under a single running accumulator — i.e.,
/// the merged trace is well-formed by the M6 append discipline.
pub fn partition_then_heal(
    payloads_a: Vec<Bytes>,
    payloads_b: Vec<Bytes>,
) -> PartitionTrace {
    let spec = Spec::default();
    let side_a = build_well_formed(payloads_a, &spec);
    let side_b = build_well_formed(payloads_b, &spec);
    PartitionTrace {
        side_a,
        side_b,
        spec,
    }
}

/// Merge a partition by re-appending side_b's payloads onto side_a's
/// tail. The resulting LogChain is well-formed by construction
/// (single running accumulator). Verifies the σ_min "merge after
/// resolution" obligation at the structural level.
pub fn partition_merge(trace: &PartitionTrace) -> LogChain {
    let mut merged = trace.side_a.clone();
    for entry in &trace.side_b {
        merged = append(merged, entry.payload.clone(), &trace.spec);
    }
    merged
}

// See note above re: `arb_*` strategy lifters living in test files.

// =====================================================================
// 4. Contract-violation class #1 — unsigned_contract
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Contract violation grammar"
// item 1):
//
//   `unsigned_contract` — missing  signature; fails
//   `operatorRooted`.
//
// v1.1.1 ships this class only; classes 2..5 carry forward.
//
// Structural model: a `Contract` is a (registry_id, payload,
// signature : Option<Bytes>) triple. A contract is operator-rooted
// iff `signature.is_some() && verify_signature(...)`. We ship
// structure only — the kernel-runtime verify is L1+ TCB.

/// Structural contract. `signature == None` ↔ unsigned (the σ_min
/// adversarial shape).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Contract {
    pub registry_id: [u8; 32],
    pub payload: Bytes,
    pub signature: Option<Bytes>,
}

/// Predicate: structurally operator-rooted? σ_min level: signature
/// must be present AND non-empty. (Cryptographic verification of the
/// signature is L1+ TCB.)
pub fn operator_rooted(c: &Contract) -> bool {
    matches!(&c.signature, Some(sig) if !sig.is_empty())
}

/// Build a positive (well-formed, signed) contract from a seed.
pub fn signed_contract_from_seed(seed: u64) -> Contract {
    let mut registry_id = [0u8; 32];
    registry_id[0..8].copy_from_slice(&seed.to_le_bytes());
    let payload = format!("contract-payload-{}", seed).into_bytes();
    let signature = Some(format!("sig-{:016x}", seed).into_bytes());
    Contract {
        registry_id,
        payload,
        signature,
    }
}

/// Adversarial mutator: strip the signature → unsigned_contract.
/// Falsifies `operator_rooted`. This is class #1 of the σ_min
/// contract-violation grammar.
pub fn unsigned_contract_from(c: &Contract) -> Contract {
    let mut out = c.clone();
    out.signature = None;
    out
}

// =====================================================================
// 5. Replay-divergence trace generator (parameterized N)
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Replay divergence: ≥ 10⁶
// traces"):
//
//   The suite MUST exercise ≥ 10⁶ randomly-mutated traces and verify
//   either (a) replayEquiv t t' = true, or (b) replayEquiv t t' =
//   false AND a structural divergence cause is identifiable.
//   10⁶ is the floor; CI nightly typically exceeds 10⁷.
//
// v1.1.1 default N = 10⁴ (NOT 10⁶ — the 10⁶ floor is a deployment-
// policy obligation per scope.md §8, not a CI obligation; this
// documentation-grade).
//
// Structural model: a "trace" is a LogChain; replayEquiv is the
// pair of LogChains being byte-identical (the structural σ_min
// shape; semantic replay-equivalence per Replay.lean is L1+).
// "Divergence cause" is one of: kind / parents / detWitness / author
// LENGTH-DIFFERS or PAYLOAD-DIFFERS-AT-INDEX-i as the witness.

/// Default replay-divergence trace count for v1.1.1 CI runs.
/// Deployment-policy obligation per scope.md §8 raises this to 10⁶
/// (or 10⁷ nightly per spec §"Replay divergence").
pub const REPLAY_DIVERGENCE_DEFAULT_N: usize = 10_000;

/// The σ_min spec floor for replay-divergence trace count
/// (DEPLOYMENT obligation, NOT CI obligation per the discipline
/// above).
pub const REPLAY_DIVERGENCE_SPEC_FLOOR_N: usize = 1_000_000;

/// Structural divergence cause witnessable at the σ_min level. The
/// L1+ kernel-runtime; this enum is the structural floor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DivergenceCause {
    /// Traces have different lengths.
    LengthDiffers,
    /// Traces have same length but differ at the given index.
    PayloadDiffersAt(usize),
    /// Traces are byte-identical (no divergence).
    Equivalent,
}

/// Identify the divergence cause between two traces. Returns
/// `Equivalent` iff `replay_equiv(a, b) == true` at the structural
/// layer.
pub fn divergence_cause(a: &LogChain, b: &LogChain) -> DivergenceCause {
    if a.len() != b.len() {
        return DivergenceCause::LengthDiffers;
    }
    for (i, (ea, eb)) in a.iter().zip(b.iter()).enumerate() {
        if ea.payload != eb.payload || ea.prev != eb.prev {
            return DivergenceCause::PayloadDiffersAt(i);
        }
    }
    DivergenceCause::Equivalent
}

/// Structural replay-equivalence at the σ_min level: byte-identical
/// LogChains. Mirrors `replayEquiv` from Replay.lean at the
/// σ_min structural floor; semantic replay-equivalence (which
/// admits trace-rearrangements under the M3 trace-equivalence
/// quotient) is L1+ TCB.
pub fn replay_equiv(a: &LogChain, b: &LogChain) -> bool {
    matches!(divergence_cause(a, b), DivergenceCause::Equivalent)
}

/// Run N rounds of replay-divergence sampling. Each round picks a
/// seed, builds a baseline trace, applies a deterministic per-seed
/// mutation, and verifies the spec dichotomy:
///   either (a) replay_equiv(t, t') = true,
///   or     (b) replay_equiv(t, t') = false AND divergence_cause is
///              identifiable (i.e., not Equivalent).
/// Returns Ok(divergence_count, equivalent_count) on success;
/// Err(seed) on the first violation of the dichotomy.
pub fn run_replay_divergence(n: usize) -> Result<(usize, usize), u64> {
    let spec = Spec::default();
    let mut diverged = 0usize;
    let mut equiv = 0usize;
    for round in 0..n {
        let seed = (round as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        // Build baseline payloads from seed.
        let n_payloads = ((seed >> 8) as usize % 8) + 1; // 1..=8
        let payloads: Vec<Bytes> = (0..n_payloads)
            .map(|i| {
                let mix = seed.wrapping_add((i as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9));
                mix.to_le_bytes().to_vec()
            })
            .collect();
        let baseline = build_well_formed(payloads.clone(), &spec);
        // Apply a per-seed mutation choice:
        let choice = seed % 3;
        let mutated = match choice {
            0 => {
                // No mutation — should be equivalent.
                build_well_formed(payloads.clone(), &spec)
            }
            1 => {
                // Append an extra entry — length diverges.
                let mut p2 = payloads.clone();
                p2.push(b"extra".to_vec());
                build_well_formed(p2, &spec)
            }
            _ => {
                // Mutate one payload byte if there's room — payload diverges.
                let mut p2 = payloads.clone();
                if !p2.is_empty() && !p2[0].is_empty() {
                    p2[0][0] ^= 0xFF;
                } else {
                    p2.push(b"diff".to_vec());
                }
                build_well_formed(p2, &spec)
            }
        };
        let cause = divergence_cause(&baseline, &mutated);
        let equivalent = replay_equiv(&baseline, &mutated);
        // Dichotomy check:
        match (equivalent, &cause) {
            (true, DivergenceCause::Equivalent) => equiv += 1,
            (false, c) if !matches!(c, DivergenceCause::Equivalent) => diverged += 1,
            _ => return Err(seed),
        }
    }
    Ok((diverged, equiv))
}

// =====================================================================
// 6. Cross-binding adapter: cap_chain → log_chain (H2  counter)
// =====================================================================
//
// existing M6 hash-chain test" is countered by composing the σ_min
// cap-chain shape with the M6 append discipline: a CapChain's
// per-entry cap_id is fed as a payload into a fresh LogChain via
// `append`, and the resulting chain MUST be M6-well-formed by
// construction. This proves that σ_min generators feed the existing
// chassis rather than living in isolation.

/// Encode each CapEntry as an M6 payload and build a well-formed
/// LogChain. The encoding is `parent_marker || cap_id` where
/// parent_marker is one byte: 0 ↔ root, 1 ↔ delegate.
pub fn cap_chain_to_log_chain(cc: &CapChain) -> LogChain {
    let spec = Spec::default();
    let mut payloads: Vec<Bytes> = Vec::with_capacity(cc.len());
    for entry in cc {
        let mut p: Bytes = Vec::with_capacity(33);
        p.push(if entry.parent.is_some() { 1 } else { 0 });
        p.extend_from_slice(&entry.cap_id);
        payloads.push(p);
    }
    build_well_formed(payloads, &spec)
}

/// Convenience: hash of the CapChain when fed through the M6 chassis.
/// Equals `root(cap_chain_to_log_chain(cc), &Spec::default())`.
pub fn cap_chain_log_root(cc: &CapChain) -> Hash {
    let spec = Spec::default();
    crate::root(&cap_chain_to_log_chain(cc), &spec)
}

// =====================================================================
// In-module unit tests (lightweight; primary tests are in `tests/`)
// =====================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_chain_basic_depth_1_to_16() {
        for depth in CAP_DEPTH_MIN..=CAP_DEPTH_MAX {
            let chain = cap_chain_from_seed(depth, 0xCAFEBABE);
            assert_eq!(chain.len(), depth);
            assert!(chain[0].parent.is_none());
            assert!(cap_chain_closure_holds(&chain));
        }
    }

    #[test]
    fn lattice_path_l_max_is_48() {
        assert_eq!(L_MAX, 48);
    }

    #[test]
    fn lattice_path_monotone_path_is_monotone() {
        let p = lattice_path_monotone_from_seed(L_MAX, 0xDEADBEEF);
        assert_eq!(p.len(), L_MAX);
        assert!(lattice_path_monotone(&p));
    }

    #[test]
    fn divergence_cause_basic() {
        let spec = Spec::default();
        let a = build_well_formed(vec![b"x".to_vec(), b"y".to_vec()], &spec);
        let b = build_well_formed(vec![b"x".to_vec(), b"y".to_vec()], &spec);
        assert_eq!(divergence_cause(&a, &b), DivergenceCause::Equivalent);
        let c = build_well_formed(vec![b"x".to_vec()], &spec);
        assert_eq!(divergence_cause(&a, &c), DivergenceCause::LengthDiffers);
    }
}

// =====================================================================
// v1.4--Item-9 — σ_min cross-cell structural shapes (ADDITIVE-ONLY)
// =====================================================================
//
// This block extends the σ_min coverage with the v1.4 alphabet
// extension: `Kind.spawn` / `Kind.retract`, `SpawnedBy` /
// `retractTarget` side-tables, `wellFormedSpawnedBy` /
// `wellFormedRetraction` predicates, `Trace.union` / `Trace.union_opt`.
//
// `// v1.4--Item-9` markers below delimit every new public symbol.
//
// ## DOCUMENTED-CAVEAT — harness expressive power (L1+ TCB residual)
//
// The existing M6 hash-chain chassis (`Entry { prev, payload }`)
// captures the M6 Audit Log shape only — no `kind` field, no
// `kernelAuthored` flag, no `SpawnedBy` / `retractTarget` side-tables,
// no `parents` set, no `event_id`. The σ_min cross-cell predicates
// `wellFormedRetraction`) live on a richer event shape than M6's
// `Entry`.
//
// "documentation-grade ε(σ_min)"; cf. the v1.1.1 cap-chain precedent
// where `CapEntry` was shipped as a structurally-distinct shape with
// the `cap_chain_to_log_chain` adapter explicitly named as the
// L1+-TCB cross-binding), this block ships a STRUCTURAL `KernelEvent`
// shape additive to the existing M6 chassis. The cross-binding to
// the existing `LogChain` is exposed via the `kernel_event_to_payload`
// adapter (mirroring the cap-chain adapter); the sigma_min floor is
// "the suite enumerates ≥ N structurally-distinct adversarial inputs
// against `wellFormedSpawnedBy` / `wellFormedRetraction` /
// `Trace.union`", not "the suite proves Lean theorems against them".
//
// L1+ TCB residual: end-to-end binding the `KernelEvent.spawned_by`
// cross-cell capping) is L1+ kernel-runtime work — a `CapMintRecord`
// would carry the M5 closure semantics that this block does not
// mirror at the L0 σ_min layer.

/// v1.4--Item-9 — Closed-alphabet `Kind` enum mirror.
///
/// Mirrors Lean `Replay.Kind` from `lean/AgentKernel/Replay.lean`
/// constructors (`Spawn`, `Retract`) on top of the v1.3 alphabet. The
/// σ_min structural layer only DISTINGUISHES the constructors —
/// kernel-runtime semantics of each arm are L1+ TCB.
///
/// We model only the constructors needed for σ_min cross-cell
/// falsifiers (Spawn / Retract / Other); the full v1.4 14-element
/// alphabet is exhaustively enumerated in `Replay.lean` and the L0
/// Lean side, not at the conformance σ_min floor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Sentinel for "any non-spawn / non-retract event" — captures the
    /// v1.3 12-element alphabet's other arms collectively at the
    /// σ_min layer (the structure-distinguishing requirement is
    /// "Spawn / Retract / Other"; full taxonomy is L0 Lean-side).
    Other,
    Spawn,
    Retract,
}

/// v1.4--Item-9 — Event identifier (mirror of `EventId : Nat`).
///
/// Mirrors Lean's `EventId := Nat`. Concrete instantiation: `u64`
/// (deployment-realistic envelope; the structural σ_min shape does
/// not depend on the width choice).
pub type EventId = u64;

/// v1.4--Item-9 — Structural `KernelEvent` shape.
///
/// Mirrors the v1.4 extended `Replay.Event` / `Causality.Event` /
/// falsifier discrimination are captured; the full Lean shape (with
/// `obs`, `det_witness`, `out_label`, etc.) is L0 Lean-side and L1+
/// kernel-runtime.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelEvent {
    /// Identifier within a single trace. Disjointness across traces
    /// is what `Trace.union_opt`'s precondition checks.
    pub event_id: EventId,
    /// Closed-alphabet kind (Spawn / Retract / Other at σ_min layer).
    pub kind: Kind,
    /// the ONLY events permitted to set `spawned_by`; tenant-authored
    /// events with `spawned_by = Some _` are forgery (clause (b)
    /// of `wellFormedSpawnedBy`).
    pub kernel_authored: bool,
    /// the σ_min structural layer we model the `Option<CapId>` shape
    /// only; kernel-runtime cap-mint binding is L1+ TCB.
    pub spawned_by: Option<CapId>,
    /// Mirrors the `mintedCapId` shape: a retract event binds to the
    /// `EventId` of the event being retracted; `None` for non-retract
    /// events.
    pub retract_target: Option<EventId>,
    /// happens-before). At σ_min layer we use `Vec<EventId>`; a
    /// retract event's `retract_target` MUST appear in its `parents`
    /// per `wellFormedRetraction` clause (b).
    pub parents: Vec<EventId>,
}

/// v1.4--Item-9 — Structural trace mirror of `Replay.Trace`.
///
/// A `Trace` is a `Vec<KernelEvent>`. The v1.4 multi-cell composition
/// disjoint-EventId precondition is the σ_min structural floor.
pub type Trace = Vec<KernelEvent>;

///
/// Mirror of Lean predicate `wellFormedSpawnedBy : Event → Prop`:
/// - clause (a): `kind = spawn → SpawnedBy ≠ none` (a spawn event
///   MUST carry a cap-mint binding).
/// - clause (b): `kernelAuthored ∨ SpawnedBy = none` (only the kernel
///   may set `SpawnedBy` — tenant-authored events with
///   `SpawnedBy = Some _` are forgery).
///
/// Returns `true` iff BOTH clauses hold.
pub fn well_formed_spawned_by(event: &KernelEvent) -> bool {
    // Clause (a): kind = spawn → spawned_by ≠ none.
    if matches!(event.kind, Kind::Spawn) && event.spawned_by.is_none() {
        return false;
    }
    // Clause (b): kernelAuthored ∨ spawned_by = none.
    if !event.kernel_authored && event.spawned_by.is_some() {
        return false;
    }
    true
}

///
/// Mirror of Lean predicate `wellFormedRetraction : Trace → Event → Prop`.
/// The predicate is two-place because clause (b) and (c) reference the
/// trace context (`target ∈ parents` AND `target.kind ≠ retract`).
///
/// - clause (a): `kind = retract → retractTarget ≠ none`.
/// - clause (b): `retractTarget ∈ event.parents` (target is causally
///   prior).
/// - clause (c): the event identified by `retractTarget` MUST NOT
///   itself be a `retract` (terminal violation — `wellFormedRetraction`
///   refuses retracting a retract event).
///
/// Returns `true` iff ALL THREE clauses hold for the event in the
/// given trace context. For non-retract events, the predicate is
/// vacuously true (clause (a)'s antecedent is false).
pub fn well_formed_retraction(event: &KernelEvent, trace: &Trace) -> bool {
    if !matches!(event.kind, Kind::Retract) {
        // Non-retract events vacuously satisfy the predicate (clause
        // (a)'s implication is trivially true, clauses (b) and (c)
        // only apply when `kind = retract`).
        return true;
    }
    // Clause (a): retractTarget must be present.
    let target = match event.retract_target {
        Some(t) => t,
        None => return false,
    };
    // Clause (b): retractTarget ∈ parents.
    if !event.parents.iter().any(|p| *p == target) {
        return false;
    }
    // Clause (c): the targeted event in the trace context must NOT
    // itself be a retract.
    match trace.iter().find(|e| e.event_id == target) {
        Some(target_event) if !matches!(target_event.kind, Kind::Retract) => true,
        Some(_) => false, // target is a retract — terminal violation.
        None => false,    // target not in trace at all.
    }
}

/// v1.4--Item-9 — Constructor for a positive (well-formed) kernel
/// spawn event from a deterministic seed.
///
/// Returns a kernel-authored Spawn event with `spawned_by = Some
/// mint_cap_id` (deterministic from seed) and a parents list that
/// includes the parent EventId.
pub fn kernel_spawn_from_seed(event_id: EventId, parent: EventId, seed: u32) -> KernelEvent {
    let mut mint_cap_id: CapId = [0u8; 32];
    mint_cap_id[0..4].copy_from_slice(&seed.to_le_bytes());
    mint_cap_id[4..12].copy_from_slice(b"mintcap_");
    KernelEvent {
        event_id,
        kind: Kind::Spawn,
        kernel_authored: true,
        spawned_by: Some(mint_cap_id),
        retract_target: None,
        parents: vec![parent],
    }
}

/// v1.4--Item-9 — Constructor for a positive (well-formed) kernel
/// retract event from a deterministic seed.
pub fn kernel_retract_from_seed(event_id: EventId, target: EventId) -> KernelEvent {
    KernelEvent {
        event_id,
        kind: Kind::Retract,
        kernel_authored: true,
        spawned_by: None,
        retract_target: Some(target),
        parents: vec![target],
    }
}

/// v1.4--Item-9 — Constructor for a tenant-authored "Other"-kind
/// event (kernel_authored = false). Used as a baseline for the
/// `wellFormedSpawnedBy` clause (b) forgery falsifier (where a tenant
/// sets `spawned_by = Some _`).
pub fn tenant_other_event(event_id: EventId, parents: Vec<EventId>) -> KernelEvent {
    KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents,
    }
}

///
/// Returns `true` iff `t1` and `t2` share no EventId. The σ_min
/// structural precondition for `Trace.union` / `Trace.union_opt`.
pub fn disjoint_event_ids(t1: &Trace, t2: &Trace) -> bool {
    for e1 in t1 {
        for e2 in t2 {
            if e1.event_id == e2.event_id {
                return false;
            }
        }
    }
    true
}

/// composition.
///
/// Returns `Some(t1 ⊎ t2)` iff `disjointEventIds t1 t2`; otherwise
/// `None`. Mirrors Lean's `Trace.union_opt : Trace → Trace → Option
/// Trace`. Events are preserved verbatim — cross-cell happens-before
pub fn trace_union_opt(t1: &Trace, t2: &Trace) -> Option<Trace> {
    if !disjoint_event_ids(t1, t2) {
        return None;
    }
    let mut out = Trace::with_capacity(t1.len() + t2.len());
    out.extend_from_slice(t1);
    out.extend_from_slice(t2);
    Some(out)
}

/// composition with disjoint-EventId hypothesis.
///
/// HEADLINE-shape: requires `disjointEventIds` as a runtime
/// precondition (panics on overlap). Mirrors Lean's
/// `Trace.union : (h : disjointEventIds t1 t2) → t1 ⊎[h] t2 : Trace`
/// — the `[h]` notation in Lean threads the proof obligation; in Rust
/// we panic if the precondition is violated (the σ_min layer treats
/// the precondition violation as a programmer error, mirroring how
/// the Lean predicate-relay refuses non-disjoint inputs).
pub fn trace_union(t1: &Trace, t2: &Trace) -> Trace {
    trace_union_opt(t1, t2)
        .expect("Trace.union: disjointEventIds precondition violated (use trace_union_opt for the partial form)")
}

// =====================================================================
// =====================================================================
//
// V1.9-PLAN  § 1 line 268-275 binding ("drop the head-963 boundary
// workarounds (sibling structs `KernelEventWithTenant`,
// `KernelEventWithMode`, `KernelEventWithPlanExec`,
// `KernelEventWithRefusal`, `KernelEventWithHumanGate`,
// `KernelEventWithHumanGateFull`, `KernelEventWithFailureMode`,
// `KernelEventWithEnvBinding`) are unified into a single canonical
// `KernelEventLatest` struct carrying all v1.4–v1.8 alphabet additions
// (σ_min wrapper-layer abstraction was an artifact of boundary
// already showed this).
//
// **Backward-compatibility discipline (lighter touch).** Each existing
// wrapper struct is preserved as a `pub type` alias to
// `KernelEventLatest` so existing test code that names the wrapper
// chooses the lighter touch: aliases preserve test compile;
// deletions reduce surface"). The `inner` `KernelEvent` field
// `event` is preserved on `KernelEventLatest` so predicates and
// constructors that access `e.event.kernel_authored` etc. continue
// to work without rewrite.
//
// **Field unification.** `KernelEventLatest` carries the union of
// all wrapper-extension fields:
//
//   - `event: KernelEvent` (head-963 inner carrier; preserves
//     `e.event.kernel_authored` / `e.event.kind` / etc. access)
//     wrapper variants; default `KindExt::Other`. Note: at the
//     unified surface `kind_ext` is bare `KindExt` rather than
//     `Option<KindExt>` — the constructor `live_event(_, None)`
//     maps to `KindExt::Other` to preserve backward semantic equiv
//     `KernelEventWithPlanExec`)
//     full-payload promotion)
//
// **`Default` derive.** `KernelEventLatest` derives `Default` so
// generator functions can default-construct cleanly via
// `KernelEventLatest { event: ..., kind_ext: KindExt::HumanGate,
// ..Default::default() }` struct-update syntax. All wrapper-extension
// field types implement `Default` (`Option<T>` → `None`, `bool` →
// `false`, `Mode` → `Mode::Live`, `KindExt` → `KindExt::Other` —
// `Default` for `Mode` already exists at L1197; we add `Default`
// for `KindExt` here).
//
// **σ_min coverage residuals carried forward.** All v1.5/v1.6/v1.7/
// the L0 spec layer; the wrapper-layer redesign is purely structural
// (unifies the σ_min Rust surface; does NOT change the σ_min vs L0

/// `TenantId` σ_min mirror of Lean `abbrev TenantId : Type := Nat`
/// (Replay.lean L92-103). `u64` matches σ_min `EventId : u64`
/// precedent. Runtime tenant-authority enforcement is L1+ TCB
pub type TenantId = u64;

/// `Mode` σ_min mirror of Lean `inductive Mode | live | replay`
/// (Replay.lean L148-151). 2-element closed enum mirroring the
/// (mirrors Lean `mode : Mode := Mode.live` field default).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// `Mode.live` — normal kernel-authored or tenant-authored event
    /// emitted during a live (real-time) execution of the kernel.
    Live,
    /// `Mode.replay` — event re-emitted under a deterministic replay
    /// (post-crash recovery, audit replay, or test harness replay).
    Replay,
}

impl Default for Mode {
    fn default() -> Self {
        Mode::Live
    }
}

/// v1.6- — `KindExt` σ_min wrapper-layer extension of the head-963
/// `Kind` enum to cover the v1.6+ alphabet additions. At v1.9 
/// canonical unified-event-kind enum.
///
/// Mirrors the relevant subset of Lean `Replay.Kind` (Replay.lean
/// L191-212; 21 constructors at v1.7+ ; `failureMode` and
/// `envBinding` are payload discriminators not separate Kinds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KindExt {
    /// Sentinel for "any non-special event" — default for unified
    /// events lacking an explicit kind extension.
    Other,
    Spawn,
    Retract,
    Plan,
    Exec,
    Refusal,
    ContractViolation,
    /// σ_min abstraction of Lean `Kind.isKernelEmit` partition
    /// `{externalReq, externalResp, read}`.
    KernelEmit,
    /// σ_min abstraction of Lean `Kind.isObservable \ Kind.isKernelEmit`
    /// partition `{commit, attest}`.
    Observable,
    HumanGate,
    FailureMode,
    EnvBinding,
}

impl Default for KindExt {
    fn default() -> Self {
        KindExt::Other
    }
}

impl KindExt {
    /// Mirrors Lean `Kind.isKernelEmit` (Replay.lean L265-267).
    pub fn is_kernel_emit(self) -> bool {
        matches!(self, KindExt::KernelEmit)
    }

    /// Mirrors Lean `Kind.isObservable` (Replay.lean L240-242).
    pub fn is_observable(self) -> bool {
        matches!(self, KindExt::Observable)
    }
}

/// (Replay/Payload.lean L183-186). Concrete carrier discipline per
/// mirrors Lean `decisionOutcome : Bool` (L0-structural binary
/// accept/refuse outcome).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct HumanGateRecord {
    pub policy_id: u64,
    /// L0-structural binary outcome at the policy decision point.
    pub decision_outcome: bool,
}

/// closed-alphabet enum (Replay/Payload.lean L226-233).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FailureMode {
    /// Recoverable failure (retry-allowed).
    Transient,
    /// Non-recoverable failure (retry-prohibited).
    Permanent,
    /// Adversarial / corrupted-state failure (incident-trigger).
    Byzantine,
}

impl Default for FailureMode {
    fn default() -> Self {
        FailureMode::Transient
    }
}

/// (Replay/Payload.lean L256-258).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct FailureRecord {
    pub mode: FailureMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct EnvDigestRecord {
    pub digest: u64,
}

///
/// Replaces the v1.5/v1.6/v1.7/v1.8 wrapper-sibling structs
/// (`KernelEventWithTenant`, `KernelEventWithMode`,
/// `KernelEventWithPlanExec`, `KernelEventWithRefusal`,
/// `KernelEventWithHumanGate`, `KernelEventWithHumanGateFull`,
/// `KernelEventWithFailureMode`, `KernelEventWithEnvBinding`) — those
/// names are preserved as `pub type` aliases below for backward
///
/// Carries the union of all v1.4–v1.8 alphabet additions natively.
/// The inner `event: KernelEvent` carrier is preserved so that
/// existing predicates and constructors using `e.event.kernel_authored`
/// / `e.event.kind` / etc. access patterns continue to compile
/// without rewrite.
///
/// `Default` derive lets generator functions default-construct cleanly
/// via struct-update syntax `KernelEventLatest { event: inner,
/// kind_ext: KindExt::HumanGate, ..Default::default() }`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct KernelEventLatest {
    /// Head-963 inner `KernelEvent` carrier — preserves
    /// `e.event.kernel_authored` / `e.event.kind` / `e.event.event_id`
    /// access patterns used by all post-963 predicates.
    pub event: KernelEvent,
    /// default-vacuity arm.
    pub tenant: Option<TenantId>,
    pub mode: Mode,
    /// discriminator. Default `KindExt::Other` (vacuous-arm).
    pub kind_ext: KindExt,
    pub linked_exec_id: Option<EventId>,
    pub refusal_reason_code: Option<u64>,
    pub violation_contract_id: Option<u64>,
    pub det_witness_present: bool,
    pub minted_cap_id_present: bool,
    pub retract_target_present: bool,
    pub linked_exec_id_present: bool,
    pub human_gate_context: Option<HumanGateRecord>,
    pub failure_record: Option<FailureRecord>,
    pub env_digest_record: Option<EnvDigestRecord>,
}

impl Default for KernelEvent {
    fn default() -> Self {
        KernelEvent {
            event_id: 0,
            kind: Kind::Other,
            kernel_authored: false,
            spawned_by: None,
            retract_target: None,
            parents: vec![],
        }
    }
}

// =====================================================================
// =====================================================================
//
// Each pre-existing wrapper-struct name is preserved as a `pub type`
// alias to `KernelEventLatest`. Existing test files that import names
// like `KernelEventWithPlanExec` continue to compile. Field-literal
// construction in tests (e.g., test `wrapper_inner_kernel_event_
// preserved` in `tests/v1_6_alphabet_plan_exec.rs`) uses the
// `..Default::default()` struct-update syntax to fill in the unified-
// struct's other fields.

/// Now `KernelEventLatest`.
pub type KernelEventWithTenant = KernelEventLatest;

pub type KernelEventWithMode = KernelEventLatest;

pub type KernelEventWithPlanExec = KernelEventLatest;

pub type KernelEventWithRefusal = KernelEventLatest;

pub type KernelEventWithHumanGate = KernelEventLatest;

pub type KernelEventWithHumanGateFull = KernelEventLatest;

pub type KernelEventWithFailureMode = KernelEventLatest;

pub type KernelEventWithEnvBinding = KernelEventLatest;

pub type TenantTrace = Vec<KernelEventLatest>;

pub type ModeTrace = Vec<KernelEventLatest>;

pub type PlanExecTrace = Vec<KernelEventLatest>;

pub type RefusalTrace = Vec<KernelEventLatest>;

pub type HumanGateTrace = Vec<KernelEventLatest>;

pub type HumanGateFullTrace = Vec<KernelEventLatest>;

pub type FailureModeTrace = Vec<KernelEventLatest>;

pub type EnvBindingTrace = Vec<KernelEventLatest>;

// =====================================================================
// =====================================================================

///
/// 2-clause mirror of Lean `Event.wellFormedTenantBinding`
/// (Replay.lean L837-846). Returns `true` iff BOTH hold for every
/// `(p_id, p)` with `p_id ∈ e.event.parents` and `p ∈ t`:
///
/// - **Clause (a) — tenant equality when both sides commit:**
///   `e.tenant ≠ None ∧ p.tenant ≠ None → e.tenant = p.tenant`.
/// - **Clause (b) — kernel-authored escape:**
///   `e.tenant = p.tenant ∨ e.event.kernel_authored`.
///
/// Default-vacuity (empty `parents`): both clauses vacuously true.
pub fn well_formed_tenant_binding(t: &TenantTrace, e: &KernelEventLatest) -> bool {
    for &p_id in &e.event.parents {
        let p_match = t.iter().find(|p| p.event.event_id == p_id);
        let p = match p_match {
            Some(p) => p,
            None => continue,
        };
        if e.tenant.is_some() && p.tenant.is_some() && e.tenant != p.tenant {
            return false;
        }
        let clause_b_holds = e.tenant == p.tenant || e.event.kernel_authored;
        if !clause_b_holds {
            return false;
        }
    }
    true
}

pub fn trace_well_formed_tenant_binding(t: &TenantTrace) -> bool {
    t.iter().all(|e| well_formed_tenant_binding(t, e))
}

pub fn same_tenant_spawn_event(
    event_id: EventId,
    parent: EventId,
    seed: u32,
    tenant: TenantId,
    kernel_authored: bool,
) -> KernelEventLatest {
    let mut inner = kernel_spawn_from_seed(event_id, parent, seed);
    inner.kernel_authored = kernel_authored;
    KernelEventLatest {
        event: inner,
        tenant: Some(tenant),
        ..Default::default()
    }
}

pub fn cross_tenant_kernel_authored_event(
    event_id: EventId,
    parent: EventId,
    seed: u32,
    tenant: TenantId,
) -> KernelEventLatest {
    let mut inner = kernel_spawn_from_seed(event_id, parent, seed);
    inner.kernel_authored = true;
    KernelEventLatest {
        event: inner,
        tenant: Some(tenant),
        ..Default::default()
    }
}

pub fn cross_tenant_tenant_authored_event(
    event_id: EventId,
    parent: EventId,
    seed: u32,
    tenant: TenantId,
) -> KernelEventLatest {
    let mut inner = kernel_spawn_from_seed(event_id, parent, seed);
    inner.kernel_authored = false;
    KernelEventLatest {
        event: inner,
        tenant: Some(tenant),
        ..Default::default()
    }
}

pub fn tenant_none_event(
    event_id: EventId,
    parent: EventId,
    seed: u32,
) -> KernelEventLatest {
    KernelEventLatest {
        event: kernel_spawn_from_seed(event_id, parent, seed),
        tenant: None,
        ..Default::default()
    }
}

pub fn wrap_with_tenant(event: KernelEvent, tenant: Option<TenantId>) -> KernelEventLatest {
    KernelEventLatest {
        event,
        tenant,
        ..Default::default()
    }
}

// =====================================================================
// =====================================================================

/// Effective σ_min kind for the unified `KernelEventLatest`. Mirrors
/// the default `Other`, falls back to mapping the inner `event.kind`.
fn effective_kind(e: &KernelEventLatest) -> KindExt {
    if e.kind_ext != KindExt::Other {
        return e.kind_ext;
    }
    match e.event.kind {
        Kind::Other => KindExt::Other,
        Kind::Spawn => KindExt::Spawn,
        Kind::Retract => KindExt::Retract,
    }
}

///
/// 2-clause mirror of Lean `Event.wellFormedReplayMode` (Replay.lean
/// L1006-1008):
/// - **Clause (a) — kernel-emit cannot be replayed:**
///   `effective_kind.is_kernel_emit() = true → mode = Mode::Live`.
/// - **Clause (b) — replay events cannot publish observable side-
///   effects:** `mode = Mode::Replay → ¬effective_kind.is_observable()`.
pub fn well_formed_replay_mode(e: &KernelEventLatest) -> bool {
    let k = effective_kind(e);
    if k.is_kernel_emit() && e.mode != Mode::Live {
        return false;
    }
    if e.mode == Mode::Replay && k.is_observable() {
        return false;
    }
    true
}

pub fn trace_well_formed_replay_mode(t: &ModeTrace) -> bool {
    t.iter().all(well_formed_replay_mode)
}

///
/// `kind_ext_opt`: `None` maps to `KindExt::Other` (vacuous
/// "consult `event.kind`" semantics — at unified surface the default
/// `KindExt::Other` triggers the same fallback through
/// `effective_kind`); `Some(k)` sets `kind_ext = k`.
pub fn live_event(event: KernelEvent, kind_ext_opt: Option<KindExt>) -> KernelEventLatest {
    KernelEventLatest {
        event,
        mode: Mode::Live,
        kind_ext: kind_ext_opt.unwrap_or(KindExt::Other),
        ..Default::default()
    }
}

/// deliberately-set `kind_ext`.
pub fn replay_event(event: KernelEvent, kind_ext_opt: Option<KindExt>) -> KernelEventLatest {
    KernelEventLatest {
        event,
        mode: Mode::Replay,
        kind_ext: kind_ext_opt.unwrap_or(KindExt::Other),
        ..Default::default()
    }
}

/// event (must be REJECTED by clause (a)).
pub fn replay_kernel_emit_event(event_id: EventId) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    replay_event(inner, Some(KindExt::KernelEmit))
}

/// event (must be REJECTED by clause (b)).
pub fn replay_observable_event(event_id: EventId) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    replay_event(inner, Some(KindExt::Observable))
}

// =====================================================================
// =====================================================================

///
/// 2-clause mirror of Lean `Event.wellFormedPlanExec` (Replay.lean
/// L1079-1084):
/// - **Clause (a) — plan-link must resolve to an exec event:**
///   `kind_ext = Plan ∧ linked_exec_id = Some(eid) → ∃ e' ∈ t,
///   e'.event.event_id = eid ∧ e'.kind_ext = Exec`.
/// - **Clause (b) — only plan events carry `linked_exec_id`:**
///   `kind_ext ≠ Plan → linked_exec_id = None`.
pub fn well_formed_plan_exec(t: &PlanExecTrace, e: &KernelEventLatest) -> bool {
    if e.kind_ext == KindExt::Plan {
        if let Some(eid) = e.linked_exec_id {
            let resolved = t
                .iter()
                .any(|e2| e2.event.event_id == eid && e2.kind_ext == KindExt::Exec);
            if !resolved {
                return false;
            }
        }
    }
    if e.kind_ext != KindExt::Plan && e.linked_exec_id.is_some() {
        return false;
    }
    true
}

pub fn trace_well_formed_plan_exec(t: &PlanExecTrace) -> bool {
    t.iter().all(|e| well_formed_plan_exec(t, e))
}

/// exec id (or `None` for vacuous structural-only acceptance).
pub fn plan_event(
    event_id: EventId,
    linked_exec_id: Option<EventId>,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::Plan,
        linked_exec_id,
        ..Default::default()
    }
}

pub fn exec_event(event_id: EventId) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::Exec,
        linked_exec_id: None,
        ..Default::default()
    }
}

/// optional `linked_exec_id`.
pub fn other_event_with_link(
    event_id: EventId,
    linked_exec_id: Option<EventId>,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::Other,
        linked_exec_id,
        ..Default::default()
    }
}

// =====================================================================
// =====================================================================

///
/// 4-clause mirror of Lean `Event.wellFormedRefusal` (Replay.lean
/// L1167-1177).
pub fn well_formed_refusal(e: &KernelEventLatest) -> bool {
    if e.kind_ext == KindExt::Refusal {
        if e.det_witness_present
            || e.minted_cap_id_present
            || e.retract_target_present
            || e.linked_exec_id_present
        {
            return false;
        }
    }
    if e.kind_ext == KindExt::ContractViolation && e.violation_contract_id.is_none() {
        return false;
    }
    if e.kind_ext != KindExt::Refusal && e.refusal_reason_code.is_some() {
        return false;
    }
    if e.kind_ext != KindExt::ContractViolation && e.violation_contract_id.is_some() {
        return false;
    }
    true
}

pub fn trace_well_formed_refusal(t: &RefusalTrace) -> bool {
    t.iter().all(well_formed_refusal)
}

pub fn refusal_event(
    event_id: EventId,
    refusal_reason_code: Option<u64>,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::Refusal,
        refusal_reason_code,
        ..Default::default()
    }
}

pub fn contract_violation_event(
    event_id: EventId,
    violation_contract_id: u64,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::ContractViolation,
        violation_contract_id: Some(violation_contract_id),
        ..Default::default()
    }
}

/// configurable codes.
pub fn other_kind_event_with_codes(
    event_id: EventId,
    refusal_reason_code: Option<u64>,
    violation_contract_id: Option<u64>,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::Other,
        refusal_reason_code,
        violation_contract_id,
        ..Default::default()
    }
}

// =====================================================================
// + constructors
// =====================================================================

///
/// 1-clause mirror of Lean `Event.wellFormedHumanGate`
/// (Replay.lean L1583-1586). Returns `true` iff:
/// - **Clause — kernel-only authorship:** `kind_ext = HumanGate →
///   event.kernel_authored = true`.
pub fn well_formed_human_gate(e: &KernelEventLatest) -> bool {
    if e.kind_ext == KindExt::HumanGate {
        return e.event.kernel_authored;
    }
    true
}

pub fn trace_well_formed_human_gate(t: &HumanGateTrace) -> bool {
    t.iter().all(well_formed_human_gate)
}

pub fn human_gate_event(event_id: EventId) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::HumanGate,
        ..Default::default()
    }
}

/// event.
pub fn tenant_human_gate_event(event_id: EventId) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::HumanGate,
        ..Default::default()
    }
}

/// configurable `kernel_authored` flag.
pub fn non_human_gate_event_with_author(
    event_id: EventId,
    kernel_authored: bool,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::Other,
        ..Default::default()
    }
}

// =====================================================================
// mirror) + constructors
// =====================================================================

///
/// 2-clause mirror of Lean's PROMOTED `Event.wellFormedHumanGate`
/// (Replay.lean L1950-1960):
///   `kind_ext = HumanGate → human_gate_context.is_some()`.
/// - **Clause (b) — kernel-only authorship (PRESERVED from v1.7
///   event.kernel_authored = true`.
pub fn well_formed_human_gate_full(e: &KernelEventLatest) -> bool {
    if e.kind_ext == KindExt::HumanGate {
        e.human_gate_context.is_some() && e.event.kernel_authored
    } else {
        true
    }
}

pub fn trace_well_formed_human_gate_full(t: &HumanGateFullTrace) -> bool {
    t.iter().all(well_formed_human_gate_full)
}

/// human-gate event.
pub fn human_gate_event_full(event_id: EventId) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::HumanGate,
        human_gate_context: Some(HumanGateRecord {
            policy_id: 1,
            decision_outcome: true,
        }),
        ..Default::default()
    }
}

/// event WITHOUT a HumanGateRecord context (clause (a) violator).
pub fn human_gate_event_missing_context(
    event_id: EventId,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::HumanGate,
        human_gate_context: None,
        ..Default::default()
    }
}

/// human-gate event (clause (b) violator).
pub fn tenant_human_gate_event_full(
    event_id: EventId,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::HumanGate,
        human_gate_context: Some(HumanGateRecord {
            policy_id: 1,
            decision_outcome: true,
        }),
        ..Default::default()
    }
}

/// arm).
pub fn non_human_gate_event_full(
    event_id: EventId,
    kernel_authored: bool,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        kind_ext: KindExt::Other,
        human_gate_context: None,
        ..Default::default()
    }
}

// =====================================================================
// + constructors
// =====================================================================

/// (σ_min collapsed form).
///
/// At σ_min, clause (b) byzantine-only collapses onto clause (a)
/// 2-clause Rust mirror lives at `well_formed_failure_mode_substantive`
/// independent boolean axes at the Rust layer).
pub fn well_formed_failure_mode(e: &KernelEventLatest) -> bool {
    match e.failure_record {
        None => true,
        Some(_) => e.event.kernel_authored,
    }
}

pub fn trace_well_formed_failure_mode(t: &FailureModeTrace) -> bool {
    t.iter().all(well_formed_failure_mode)
}

pub fn kernel_failure_event(event_id: EventId, mode: FailureMode) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        failure_record: Some(FailureRecord { mode }),
        ..Default::default()
    }
}

/// event.
pub fn tenant_failure_event(event_id: EventId, mode: FailureMode) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        failure_record: Some(FailureRecord { mode }),
        ..Default::default()
    }
}

pub fn non_failure_event(event_id: EventId, kernel_authored: bool) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        failure_record: None,
        ..Default::default()
    }
}

// =====================================================================
// + constructors
// =====================================================================

/// (σ_min collapsed form).
///
/// At σ_min, both clauses collapse onto `kernel_authored` per
/// Rust mirror lives at `well_formed_env_binding_substantive` below
pub fn well_formed_env_binding(e: &KernelEventLatest) -> bool {
    match e.env_digest_record {
        None => true,
        Some(_) => e.event.kernel_authored,
    }
}

pub fn trace_well_formed_env_binding(t: &EnvBindingTrace) -> bool {
    t.iter().all(well_formed_env_binding)
}

pub fn kernel_env_binding_event(event_id: EventId, digest: u64) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: true,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        env_digest_record: Some(EnvDigestRecord { digest }),
        ..Default::default()
    }
}

/// event.
pub fn tenant_env_binding_event(event_id: EventId, digest: u64) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        env_digest_record: Some(EnvDigestRecord { digest }),
        ..Default::default()
    }
}

/// vacuity).
pub fn non_env_binding_event(
    event_id: EventId,
    kernel_authored: bool,
) -> KernelEventLatest {
    let inner = KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    };
    KernelEventLatest {
        event: inner,
        env_digest_record: None,
        ..Default::default()
    }
}

// =====================================================================
// =====================================================================

///
/// Clause (a) [field-presence + closed alphabet]: the event's
/// `failure_record` field, if present, is one of the closed 3-variant
/// `FailureMode` enum (already enforced at type level).
/// Clause (b) [BYZANTINE / kernel-authorship discriminator]:
/// `failure_record = Some(_) → kernel_authored = true`. Mirrors
///
/// substantive 2-clause shape.
pub fn well_formed_failure_mode_substantive(e: &KernelEventLatest) -> bool {
    // Clause (a): closed alphabet — type-enforced.
    // Clause (b): kernel-authorship discriminator.
    match &e.failure_record {
        None => true,
        Some(_) => e.event.kernel_authored,
    }
}

///
/// Clause (a) [field-presence]: the event's `env_digest_record`
/// field, if present, has a non-empty `digest` (digest != 0 sentinel
/// — the σ_min `u64` carrier uses 0 as the absent-sentinel since the
/// `Option` discriminant carries the structural presence; substantive
/// clause (a) additionally REJECTS a `Some(EnvDigestRecord{digest:
/// 0})` zero-digest as mal-formed since a kernel-computed digest
/// should be non-trivially populated).
/// Clause (b) [UNIVERSAL kernel-authorship discriminator]:
/// `env_digest_record = Some(_) → kernel_authored = true`. Mirrors
/// Lean's `kernelAuthored_substantive` UNIVERSAL independence at
///
/// substantive 2-clause shape.
pub fn well_formed_env_binding_substantive(e: &KernelEventLatest) -> bool {
    match &e.env_digest_record {
        None => true,
        Some(rec) => rec.digest != 0 && e.event.kernel_authored,
    }
}
