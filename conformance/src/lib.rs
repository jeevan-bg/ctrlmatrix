//! CTRLMATRIX L0 — Rust conformance MVP for M6 (Audit Log) hash-chain
//! wellFormedness.
//!
//! ## What this crate is (and is not)
//!
//! This crate mirrors the abstract spec from
//! T4 audit-integrity theorem; this Rust side is the *binding force*
//! that the theorem statement actually says what we mean — by
//! exhibiting falsifiers (mutated chains for which `well_formed`
//! returns `false`).
//!
//! README is not a binding force; a property test that fails on one
//! mutated input is.
//!
//! ## The Lean mirror
//!
//! Lean source (`Log.lean`):
//!
//! ```text
//! structure Entry (Bytes Hash : Type) where
//!   prev    : Hash
//!   payload : Bytes
//!
//! abbrev LogChain (Bytes Hash : Type) := List (Entry Bytes Hash)
//!
//! def LogChain.root (H genesis serialize) (c) : Hash :=
//!   List.foldl (fun acc e => H (serialize acc e.payload))
//!              (H genesis) c
//!
//! def LogChain.wellFormedAux (H serialize) :
//!     Hash → LogChain Bytes Hash → Prop
//!   | _,   []        => True
//!   | acc, e :: rest =>
//!       e.prev = acc ∧
//!       LogChain.wellFormedAux H serialize
//!         (H (serialize acc e.payload)) rest
//!
//! def LogChain.wellFormed (H genesis serialize) (c) : Prop :=
//!   LogChain.wellFormedAux H serialize (H genesis) c
//! ```
//!
//! Rust mirror (this file):
//!
//! | Lean name                              | Rust name                           |
//! |----------------------------------------|--------------------------------------|
//! | `Entry { prev, payload }`              | `Entry { prev, payload }`            |
//! | `LogChain Bytes Hash`                  | `LogChain` (= `Vec<Entry>`)          |
//! | `LogChain.root H genesis serialize c`  | `root(c, &cfg)`                      |
//! | `LogChain.wellFormedAux H serialize`   | `well_formed_aux(acc, c, &cfg)`      |
//! | `LogChain.wellFormed H genesis ser`    | `well_formed(c, &cfg)`               |
//! | `LogChain.wellFormed_append_singleton` | `append(chain, payload, &cfg)`       |
//!
//! Naming convention: the Lean source uses camelCase
//! (`wellFormed`); the Rust mirror uses snake_case (`well_formed`)
//! per Rust convention. The mirror is *structural* — Rust types are
//! monomorphic at `Bytes = Vec<u8>` and `Hash = [u8; 32]`; Lean's
//! polymorphism over `(Bytes, Hash)` collapses at the conformance
//! instantiation, exactly as the Lean-side conformance demos under
//! `lean/AgentKernel/Log/Conformance.lean` collapse it
//! SHA-256 (256-bit, deployment-realistic per scope.md §8 MTH
//! parameter) where the Lean conformance demo uses FNV-1a 64-bit
//! (mock; see scope.md §7 M6 forward bindings).
//!
//! ## Hash choice and the L0 vs L1+ boundary
//!
//! scope.md §8 names a 256-bit collision-resistant Merkle Tree Hash
//! `MTH = H ∘ serialize` as the abstract cryptographic primitive,
//! with concrete instantiation deferred to L1+/L2. The L0 Lean
//! statement is *polymorphic* over `(Bytes, Hash, H, serialize,
//! genesis)` — what the Rust conformance suite checks is the
//! *structure* of `well_formed` under any deterministic hash, not
//! cryptographic strength of a particular hash. SHA-256 is picked
//! here because (a) it is the deployment-realistic 256-bit width
//! (CT/Sigsum/Trillian cryptography); (b) the `sha2` crate is a
//! single dependency with no transitive deviations; (c) determinism
//! is total. This is an L1+ instantiation choice; the L0 spec is
//!
//! ## What this crate does NOT prove
//!
//! - It does not prove SHA-256 is collision-resistant. That is a
//!   §8 black-box assertion at L0.
//!   `well_formed` ≠ "no collisions exist."
//! - It does not bridge the Lean Bytes/Hash polymorphism back to
//!   the typed Lean theorem. That is the per-module bridge work
//!   running in parallel under `lean/AgentKernel/Bridge/M6.lean`
//! - It does not exercise TLA+ `Append` / `PublishRoot` arms
//!   directly. That is TLA+ + TLC owning operational semantics

use sha2::{Digest, Sha256};

/// over the M6 hash-chain chassis above; existing types and
/// functions are unchanged. See `generators.rs` for the inventory
/// and the `spec/sigma-min-coverage.md` mirror table.
///
/// wrapper-sibling structs (`KernelEventWithTenant`, `…WithMode`,
/// `…WithPlanExec`, `…WithRefusal`, `…WithHumanGate`,
/// `…WithHumanGateFull`, `…WithFailureMode`, `…WithEnvBinding`) are
/// unified into the canonical `KernelEventLatest` struct; their old
/// names are preserved as `pub type` aliases. See the post-963
/// region of `generators.rs` for the unified struct definition.
///
/// `well_formed_failure_mode_substantive` +
/// `well_formed_env_binding_substantive` re-exported below.
pub mod generators;

// audit α-residuals).
pub use generators::{well_formed_env_binding_substantive, well_formed_failure_mode_substantive};

/// 256-bit hash output. Mirrors Lean's polymorphic `Hash` parameter,
/// instantiated at SHA-256 (scope.md §8 MTH parameter width = 256).
pub type Hash = [u8; 32];

/// Opaque payload bytes. Mirrors Lean's polymorphic `Bytes`
/// parameter; conformance instantiates `Bytes := Vec<u8>` per the
pub type Bytes = Vec<u8>;

/// Mirrors Lean `Entry { prev, payload }` from `Log.lean:84-86`.
/// `prev` is the commitment to the chain prefix preceding this
/// entry; the `well_formed` invariant binds it to that prefix's
/// root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub prev: Hash,
    pub payload: Bytes,
}

/// Mirrors Lean `abbrev LogChain := List Entry` from `Log.lean:91`.
/// Head = earliest-appended; tail = most-recent (matches Lean
/// `List` semantics and the M1/M3 trace discipline cited in
/// Log.lean's header).
pub type LogChain = Vec<Entry>;

/// Configuration for the abstract spec parameters
/// `(H, genesis, serialize)`. Mirror of Lean's three function
/// arguments threaded through every M6 definition.
///
/// At L0 this is polymorphic; the conformance crate fixes the
/// instantiation to SHA-256 + length-prefixed concatenation.
#[derive(Clone, Debug)]
pub struct Spec {
    /// `genesis : Bytes`. Empty by convention (matches Lean
    /// conformance demo `genesis := []`).
    pub genesis: Bytes,
}

impl Default for Spec {
    fn default() -> Self {
        Self {
            genesis: Vec::new(),
        }
    }
}

/// Mirrors Lean's `H : Bytes → Hash`. Concrete instantiation:
/// SHA-256.
pub fn h(input: &[u8]) -> Hash {
    let mut hasher = Sha256::new();
    hasher.update(input);
    let out = hasher.finalize();
    let mut arr = [0u8; 32];
    arr.copy_from_slice(&out);
    arr
}

/// Mirrors Lean's `serialize : Hash → Bytes → Bytes`. Concrete
/// instantiation: 32-byte hash prefix concatenated with the
/// payload (analogous to the Lean conformance demo's "8-byte LE
/// hash prefix ++ payload bytes" but at 256-bit width).
///
/// reframes T4's collision witness into the composite step-hash
/// `H ∘ serialize`, exactly so injectivity of `serialize` is not
/// part of the cryptographic assumption).
pub fn serialize(prev: &Hash, payload: &[u8]) -> Bytes {
    let mut out = Vec::with_capacity(32 + payload.len());
    out.extend_from_slice(prev);
    out.extend_from_slice(payload);
    out
}

/// Composite step-hash `H ∘ serialize`. The Merkle Tree Hash (MTH)
/// collision-resistance §8 asserts as a black box.
fn mth(prev: &Hash, payload: &[u8]) -> Hash {
    h(&serialize(prev, payload))
}

/// Initial accumulator: `H(genesis)`. Mirrors the Lean
/// `LogChain.root`'s base case and `wellFormed`'s seed argument.
pub fn initial_acc(spec: &Spec) -> Hash {
    h(&spec.genesis)
}

/// Mirrors Lean `LogChain.root` from `Log.lean:99-104`.
///
/// Empty chain: `H(genesis)`.
/// Non-empty: foldl `(fun acc e => H(serialize acc e.payload))`
/// from `H(genesis)` over the chain.
pub fn root(chain: &[Entry], spec: &Spec) -> Hash {
    let mut acc = initial_acc(spec);
    for e in chain {
        acc = mth(&acc, &e.payload);
    }
    acc
}

/// Mirrors Lean `LogChain.wellFormedAux` from `Log.lean:108-116`.
/// Returns true iff every entry's `prev` field equals the
/// running prefix-root accumulator.
pub fn well_formed_aux(mut acc: Hash, chain: &[Entry]) -> bool {
    for e in chain {
        if e.prev != acc {
            return false;
        }
        acc = mth(&acc, &e.payload);
    }
    true
}

/// Mirrors Lean `LogChain.wellFormed` from `Log.lean:122-127`.
///
/// A chain is well-formed iff every entry's `prev` field equals
/// the root of the chain prefix preceding it. The first entry's
/// `prev` equals `H(genesis)`.
///
/// This is the predicate against which mutators are scored:
/// every mutator class in `tests/m6_hash_chain.rs` produces
/// chains for which this returns `false` after mutation.
pub fn well_formed(chain: &[Entry], spec: &Spec) -> bool {
    well_formed_aux(initial_acc(spec), chain)
}

/// The kernel-emit operation: append a single entry whose `prev`
/// is bound to the current chain's root. This is the Rust
/// counterpart of Lean's `LogChain.wellFormed_append_singleton`
/// (`Log.lean:419-431`) — a chain produced exclusively by
/// successive `append` calls is well-formed by construction.
///
/// Used by the positive proptest to generate well-formed chains;
/// each negative proptest then *mutates* such a chain to exhibit
/// a falsifier of `well_formed`.
pub fn append(mut chain: LogChain, payload: Bytes, spec: &Spec) -> LogChain {
    let prev = root(&chain, spec);
    chain.push(Entry { prev, payload });
    chain
}

/// Convenience: build a well-formed chain from a sequence of
/// payloads. The result satisfies `well_formed` by the kernel-emit
/// invariant.
pub fn build_well_formed(payloads: Vec<Bytes>, spec: &Spec) -> LogChain {
    let mut chain = LogChain::new();
    for p in payloads {
        chain = append(chain, p, spec);
    }
    chain
}

// =====================================================================
// Mutator classes
// =====================================================================
//
// Each mutator transforms a well-formed chain into one for which
// `well_formed` returns `false`. These are the *falsifiers* that
// test must fail on at least one mutated input class.
//
// The classes were chosen to cover the structural attack surface
// of the wellFormedness predicate as it appears in Log.lean:
//
// - `flip_bit_in_prev`         — point-mutation of the binding field
// - `truncate`                 — chain-truncation between PublishRoots
//                                (B- shape; closed structurally
//                                here, residual at the operational
// - `swap_two`                 — reorder two entries (breaks the
//                                running accumulator chain on at
//                                least one of the swapped entries)
// - `insert_spurious`          — splice in an entry whose `prev`
//                                does not match the running root
// - `mutate_payload`           — modify a non-last entry's payload
//                                (the next entry's `prev` no longer
//                                matches the recomputed root)
//
// Each mutator returns `Some(LogChain)` on success and `None`
// when the input chain is too short for the mutator to apply
// (the negative proptests reject such inputs via
// `prop_assume!`).
// =====================================================================

/// Mutator (a): flip a bit in the `prev` field of entry at `idx`.
/// Falsifies the binding `e.prev = running_acc`.
pub fn flip_bit_in_prev(chain: &LogChain, idx: usize, byte: usize, bit: u8) -> Option<LogChain> {
    if idx >= chain.len() || byte >= 32 {
        return None;
    }
    let mut out = chain.clone();
    out[idx].prev[byte] ^= 1u8 << (bit & 7);
    Some(out)
}

/// Mutator (b): truncate the chain to length `new_len < chain.len()`.
/// The truncated chain is itself well-formed (well-formedness is
/// hereditary on prefixes by `LogChain.wellFormed_dropLast`); to
/// produce a falsifier we instead *truncate-and-keep-the-tail*:
/// drop the first `n` entries, leaving a chain whose new head's
/// `prev` no longer equals `H(genesis)`.
///
/// This is the structural shape of B- (PublishRoot
/// withholding) at the wellFormedness layer: an auditor presented
/// with an arbitrary subsequence cannot accept it as well-formed
/// from genesis.
pub fn truncate_drop_prefix(chain: &LogChain, n: usize) -> Option<LogChain> {
    if n == 0 || n >= chain.len() {
        return None;
    }
    Some(chain[n..].to_vec())
}

/// Mutator (c): swap two adjacent entries at positions `i` and `i+1`.
/// After the swap, the entry at position `i` retains its old `prev`
/// (which equals the original prefix-root), but the entry at
/// position `i+1` has its old `prev` (which equals the original
/// running-acc *after* the entry now at position `i+1`'s pre-swap
/// position, i.e., `mth(prefix_root, old_e_i.payload)`) — which
/// only matches if both swapped entries had identical payloads
/// (caller responsibility to choose distinct payloads, enforced
/// by proptest filters).
pub fn swap_adjacent(chain: &LogChain, i: usize) -> Option<LogChain> {
    if i + 1 >= chain.len() {
        return None;
    }
    let mut out = chain.clone();
    out.swap(i, i + 1);
    Some(out)
}

/// Mutator (d): splice a spurious entry at position `idx`. The
/// new entry's `prev` is set to a deterministic value (the inverse
/// of the running accumulator at that point) so that
/// `well_formed` rejects it.
pub fn insert_spurious(chain: &LogChain, idx: usize, payload: Bytes, spec: &Spec) -> Option<LogChain> {
    if idx > chain.len() {
        return None;
    }
    // Compute what the running accumulator *would* be at idx, then
    // set the spurious entry's prev to its bitwise inverse — which
    // is unequal to the actual accumulator (no preimage of itself
    // under XOR-with-all-ones is itself for any 32-byte value).
    let mut acc = initial_acc(spec);
    for e in chain.iter().take(idx) {
        acc = mth(&acc, &e.payload);
    }
    let mut bad_prev = acc;
    for b in bad_prev.iter_mut() {
        *b ^= 0xFF;
    }
    let mut out = chain.clone();
    out.insert(idx, Entry { prev: bad_prev, payload });
    Some(out)
}

/// Mutator (e): mutate the payload of a non-last entry. The next
/// entry's `prev` no longer matches the recomputed running-acc.
/// (Mutating the *last* entry's payload does not falsify
/// well-formedness — the invariant only constrains `prev`, not
/// the trailing payload.)
///
/// The task description proposed "(e) replay-detection (duplicate
/// idx)" — but `Entry` in `Log.lean` has no `idx` field
/// (`Log.lean:84-86`: only `prev` and `payload`). This mutator
/// `mutate_payload` is the honest substitute: it tests the same
/// underlying property (the chain's "running accumulator binding"
/// is what wellFormedness enforces), without inventing a field
/// that doesn't exist in the Lean spec. See report H1 / H2 for
/// the falsifier traceability.
pub fn mutate_payload(chain: &LogChain, idx: usize, byte_xor: u8) -> Option<LogChain> {
    if chain.len() < 2 || idx + 1 >= chain.len() {
        return None;
    }
    let mut out = chain.clone();
    if out[idx].payload.is_empty() {
        out[idx].payload.push(byte_xor);
    } else {
        out[idx].payload[0] ^= byte_xor.max(1);
    }
    Some(out)
}
