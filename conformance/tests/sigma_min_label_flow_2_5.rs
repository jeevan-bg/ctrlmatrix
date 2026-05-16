//!
//! Sibling to `sigma_min_lattice_path.rs` (which covers class #1
//! `monotone_violation`). This file ships the four remaining classes
//! of the σ_min adversarial label-flow grammar published at
//! `spec/sigma-min-coverage.md` §"Adversarial label flow grammar":
//!
//! | Class | Generator name              | Spec attack vector                                    |
//! |-------|-----------------------------|-------------------------------------------------------|
//! |   2   | `declass_without_capability`| `Kind.declassify` w/o cap witness; fails            |
//! |   3   | `declass_locus_drift`       | declass cap doesn't authorize locus; fails      |
//! |   4   | `raw_input_alias`           | opaque-oracle output w/ foreign RawInputTags tag;     |
//! |       |                             | fails `taint_kind_closure`                            |
//! |   5   | `payload_compose_unjoined`  | concat labeled+unlabeled w/o joining; fails           |
//! |       |                             | `PayloadDiscipline.holds`                             |
//!
//!
//! summary", this file MUST NOT edit `conformance/src/generators.rs`
//! (the existing 687-LoC core). All structural types and helpers
//! used by the four classes below are defined INLINE in this test
//! file so the additive-only invariant is byte-trivial to verify
//! (`git diff v1.2-stable -- conformance/src/generators.rs` empty).
//!
//! ## Honest naming
//!
//! These generators implement **structural shapes** at the σ_min
//! floor; they do NOT mirror operational  /  / `taint_kind_closure`
//! / `PayloadDiscipline.holds` semantics. The Lean side
//! (`lean/AgentKernel/IFC.lean`, `Caps.lean`,
//! `PayloadDiscipline.lean`) owns those operational predicates; this
//! file SHIPS the adversarial input grammar shapes that an L1+
//! kernel-runtime conformance harness MUST reject. Per
//! `spec/sigma-min-coverage.md` line 36-39 ("Generators here
//! intentionally ship as Vec<...>-shaped traces / chains / paths"
//! — same discipline applied here for label-flow classes).

use ctrlmatrix_conformance::generators::{LatticeLabel, L_MAX, SIGMA_C, SIGMA_I, SIGMA_P};
use proptest::prelude::*;

// =====================================================================
// Inline structural types (additive — defined here, not in core)
// =====================================================================

/// Event kind for the σ_min label-flow adversarial harness. Mirrors
/// the relevant slice of `IFC.lean`'s `Kind` taxonomy at the
/// structural floor; full Kind semantics are L1+ TCB.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LabelFlowKind {
    /// Ordinary derived event (the well-labeled-step shape).
    Derived,
    /// Declassification — REQUIRES a cap witness binding to the new
    /// label and the payload locus (per  + `r4_declass_origin_integrity`).
    Declassify,
    /// Opaque oracle output — MUST carry `RawInputTags` per
    /// `taint_kind_closure`; no foreign labels admitted.
    OpaqueOracle,
    /// SDK payload composition — concat of two labeled streams MUST
    PayloadCompose,
}

/// A capability witness for a `Declassify` event. Mirrors the
/// (cap_id, target_locus, target_label) triple owned by `Caps.lean`
/// at the structural floor. `None` ↔ NO cap witness present (the
/// class-2 attack shape).
#[derive(Clone, Debug, PartialEq, Eq)]
struct DeclassCapWitness {
    /// Identifier of the declass cap (32 bytes — same shape as
    /// `generators::CapId`).
    cap_id: [u8; 32],
    /// Locus the cap authorizes the declass over. The σ_min
    /// "locus drift" (class 3) shape: cap `target_locus` does not
    /// match the event's payload locus.
    target_locus: u32,
    /// Label the cap authorizes the declass to.
    target_label: LatticeLabel,
}

/// Provenance tag carried by an event payload. Mirrors the slice of
/// `Caps.lean`'s `RawInputTags` taxonomy used by `taint_kind_closure`.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ProvenanceTag {
    /// Raw input from a trusted operator-rooted source — the only
    /// admissible tag for `OpaqueOracle` output.
    RawInputTags,
    /// Foreign tag — `OpaqueOracle` output carrying this is the
    /// class-4 `raw_input_alias` adversarial shape.
    ForeignTag,
}

/// A label-flow event under the σ_min structural shape. Carries
/// enough fields to express the four adversarial classes below
/// without depending on the L1+ operational `Event` from `M3.lean`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LabelFlowEvent {
    kind: LabelFlowKind,
    /// The event's outLabel.
    out_label: LatticeLabel,
    /// The event's payload locus (a u32 stand-in for the L1+
    /// locus-id discipline).
    payload_locus: u32,
    /// For Declassify: the cap witness, if any.
    cap_witness: Option<DeclassCapWitness>,
    /// For OpaqueOracle: the provenance tag carried by the output.
    provenance: Option<ProvenanceTag>,
    /// For PayloadCompose: the two source labels being composed
    /// (left, right). The composed `out_label` MUST equal
    /// `left.join(right)` per `PayloadDiscipline.holds`.
    compose_sources: Option<(LatticeLabel, LatticeLabel)>,
}

// =====================================================================
// Class 2 — declass_without_capability
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Adversarial label flow
// grammar" item 2):
//
//   `declass_without_capability` — `Kind.declassify` with no cap
//   witness; fails .
//
// Structural shape: a `Declassify`-kind event whose `cap_witness`
// is `None`. The σ_min predicate `declass_well_formed` REQUIRES
// `kind == Declassify ⇒ cap_witness.is_some()`. The class-2
// generator emits events that falsify this predicate.

/// Predicate: structurally well-formed declassification at the σ_min
/// floor. Mirrors  at the structural layer; the L1+ kernel-runtime
///  owns the cap-store lookup and label-arithmetic checks. The
/// σ_min floor is "every declass event carries a non-empty
/// `cap_witness`" — class 2 falsifies exactly this.
fn declass_well_formed(e: &LabelFlowEvent) -> bool {
    match e.kind {
        LabelFlowKind::Declassify => e.cap_witness.is_some(),
        _ => true,
    }
}

/// Build a positive (well-formed, cap-bearing) declassification event.
fn signed_declass_from_seed(seed: u64) -> LabelFlowEvent {
    let target_label = LatticeLabel::from_flat((seed as usize) % L_MAX);
    let mut cap_id = [0u8; 32];
    cap_id[0..8].copy_from_slice(&seed.to_le_bytes());
    cap_id[8..16].copy_from_slice(b"declasC_");
    let payload_locus = (seed.wrapping_mul(0x9E37_79B9) as u32) ^ 0xDEAD_BEEFu32;
    LabelFlowEvent {
        kind: LabelFlowKind::Declassify,
        out_label: target_label.clone(),
        payload_locus,
        cap_witness: Some(DeclassCapWitness {
            cap_id,
            target_locus: payload_locus,
            target_label,
        }),
        provenance: None,
        compose_sources: None,
    }
}

/// Adversarial mutator: strip the cap witness from a declass event.
/// Falsifies `declass_well_formed`. This is class #2 of the σ_min
/// adversarial label-flow grammar.
fn declass_without_capability(e: &LabelFlowEvent) -> LabelFlowEvent {
    let mut out = e.clone();
    out.cap_witness = None;
    out
}

// =====================================================================
// Class 3 — declass_locus_drift
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Adversarial label flow
// grammar" item 3):
//
//   `declass_locus_drift` — declass cap does not authorize payload
//   locus; fails  + `r4_declass_origin_integrity`.
//
// Structural shape: a `Declassify`-kind event whose `cap_witness` is
// `Some(_)` BUT `cap_witness.target_locus != payload_locus`. The
// σ_min predicate `declass_locus_authorized` REQUIRES the cap's
// `target_locus` to equal the event's `payload_locus` — class 3
// drifts these to falsify it.

/// Predicate: σ_min structural locus-authorization for a declass.
/// `Some(witness) ∧ witness.target_locus == payload_locus`. Mirrors
/// the structural slice of `r4_declass_origin_integrity` from
/// `lean/AgentKernel/IFC.lean` at the σ_min floor; the L1+
/// kernel-runtime owns full locus-arithmetic.
fn declass_locus_authorized(e: &LabelFlowEvent) -> bool {
    match (&e.kind, &e.cap_witness) {
        (LabelFlowKind::Declassify, Some(w)) => w.target_locus == e.payload_locus,
        (LabelFlowKind::Declassify, None) => false,
        _ => true,
    }
}

/// Adversarial mutator: drift the cap witness's `target_locus` to a
/// value distinct from the event's `payload_locus`. Falsifies
/// `declass_locus_authorized` while keeping `declass_well_formed`
/// (cap is present — only its locus is wrong). This is class #3.
fn declass_locus_drift(e: &LabelFlowEvent) -> Option<LabelFlowEvent> {
    let mut out = e.clone();
    let drifted_locus = e.payload_locus.wrapping_add(1);
    match &mut out.cap_witness {
        Some(w) => {
            // Pick a drift value that is guaranteed unequal to
            // payload_locus regardless of overflow.
            w.target_locus = if w.target_locus == drifted_locus {
                drifted_locus.wrapping_add(1)
            } else {
                drifted_locus
            };
            // Final safety: if by adversarial coincidence we landed
            // back on payload_locus, force a +2 offset.
            if w.target_locus == out.payload_locus {
                w.target_locus = out.payload_locus.wrapping_add(2);
            }
            Some(out)
        }
        None => None,
    }
}

// =====================================================================
// Class 4 — raw_input_alias
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Adversarial label flow
// grammar" item 4):
//
//   `raw_input_alias` — opaque-oracle output with foreign
//   `RawInputTags` tag; fails `taint_kind_closure`.
//
// Structural shape: an `OpaqueOracle`-kind event whose `provenance`
// is `Some(ForeignTag)` rather than `Some(RawInputTags)`. The σ_min
// predicate `taint_kind_closure_holds` REQUIRES every
// `OpaqueOracle` event to carry `provenance == Some(RawInputTags)`
// — class 4 aliases a foreign tag to falsify it.

/// Predicate: σ_min structural taint-kind closure. Mirrors the
/// structural slice of `taint_kind_closure` from
/// `lean/AgentKernel/Caps.lean` at the σ_min floor: every
/// `OpaqueOracle` output carries `RawInputTags`; foreign tags are
/// inadmissible.
fn taint_kind_closure_holds(e: &LabelFlowEvent) -> bool {
    match (&e.kind, &e.provenance) {
        (LabelFlowKind::OpaqueOracle, Some(ProvenanceTag::RawInputTags)) => true,
        (LabelFlowKind::OpaqueOracle, _) => false,
        _ => true,
    }
}

/// Build a positive (well-formed) opaque-oracle event.
fn signed_oracle_from_seed(seed: u64) -> LabelFlowEvent {
    let out_label = LatticeLabel::from_flat((seed as usize) % L_MAX);
    let payload_locus = seed as u32;
    LabelFlowEvent {
        kind: LabelFlowKind::OpaqueOracle,
        out_label,
        payload_locus,
        cap_witness: None,
        provenance: Some(ProvenanceTag::RawInputTags),
        compose_sources: None,
    }
}

/// Adversarial mutator: replace the `RawInputTags` provenance with
/// `ForeignTag`. Falsifies `taint_kind_closure_holds`. This is
/// class #4 of the σ_min adversarial label-flow grammar.
fn raw_input_alias(e: &LabelFlowEvent) -> Option<LabelFlowEvent> {
    if !matches!(e.kind, LabelFlowKind::OpaqueOracle) {
        return None;
    }
    let mut out = e.clone();
    out.provenance = Some(ProvenanceTag::ForeignTag);
    Some(out)
}

// =====================================================================
// Class 5 — payload_compose_unjoined
// =====================================================================
//
// Spec excerpt (sigma-min-coverage.md §"Adversarial label flow
// grammar" item 5):
//
//   `payload_compose_unjoined` — SDK concat of labeled + unlabeled
//
// Structural shape: a `PayloadCompose`-kind event whose `out_label`
// is NOT the join of `compose_sources.0` and `compose_sources.1`.
// The σ_min predicate `payload_discipline_holds` REQUIRES
// `out_label == left.join(right)` for every compose event — class 5
// emits events where one of the source labels is "dropped" (i.e.,
// `out_label = left` only, ignoring `right`) which falsifies the
// join when `right` has any component greater than `left`.

/// `PayloadDiscipline.holds` from
/// `lean/AgentKernel/PayloadDiscipline.lean` at the σ_min
/// floor: a compose event's `out_label` MUST equal the
/// componentwise join of its two source labels.
fn payload_discipline_holds(e: &LabelFlowEvent) -> bool {
    match (&e.kind, &e.compose_sources) {
        (LabelFlowKind::PayloadCompose, Some((l, r))) => {
            let expected = l.join(r);
            e.out_label == expected
        }
        (LabelFlowKind::PayloadCompose, None) => false,
        _ => true,
    }
}

/// Build a positive (well-formed) payload-compose event with
/// `out_label = left.join(right)`.
fn signed_compose_from_seeds(left_seed: u64, right_seed: u64) -> LabelFlowEvent {
    let left = LatticeLabel::from_flat((left_seed as usize) % L_MAX);
    let right = LatticeLabel::from_flat((right_seed as usize) % L_MAX);
    let out_label = left.join(&right);
    let payload_locus = (left_seed ^ right_seed) as u32;
    LabelFlowEvent {
        kind: LabelFlowKind::PayloadCompose,
        out_label,
        payload_locus,
        cap_witness: None,
        provenance: None,
        compose_sources: Some((left, right)),
    }
}

/// Adversarial mutator: replace `out_label` with `left` only,
/// dropping `right`. Falsifies `payload_discipline_holds` whenever
/// `right` has any component strictly greater than `left`. Returns
/// `None` when the drop would still satisfy the discipline (i.e.,
/// when `right.leq(left)` already). This is class #5 of the σ_min
/// adversarial label-flow grammar.
fn payload_compose_unjoined(e: &LabelFlowEvent) -> Option<LabelFlowEvent> {
    let (left, right) = match &e.compose_sources {
        Some((l, r)) => (l.clone(), r.clone()),
        None => return None,
    };
    if !matches!(e.kind, LabelFlowKind::PayloadCompose) {
        return None;
    }
    // The unjoined drop only falsifies the discipline when `right`
    // contributes something `left` does not. If right.leq(left) then
    // left.join(right) == left and the "drop" yields the same label
    // — no falsifier. Reject those inputs so callers can prop_assume.
    if right.leq(&left) {
        return None;
    }
    let mut out = e.clone();
    out.out_label = left;
    Some(out)
}

// =====================================================================
// Strategy lifters
// =====================================================================

fn arb_lattice_label() -> impl Strategy<Value = LatticeLabel> {
    (0u8..(SIGMA_C as u8), 0u8..(SIGMA_I as u8), 0u8..(SIGMA_P as u8))
        .prop_map(|(c, i, p)| LatticeLabel { c_idx: c, i_idx: i, p_idx: p })
}

fn arb_signed_declass() -> impl Strategy<Value = LabelFlowEvent> {
    any::<u64>().prop_map(signed_declass_from_seed)
}

fn arb_signed_oracle() -> impl Strategy<Value = LabelFlowEvent> {
    any::<u64>().prop_map(signed_oracle_from_seed)
}

fn arb_signed_compose() -> impl Strategy<Value = LabelFlowEvent> {
    (any::<u64>(), any::<u64>()).prop_map(|(l, r)| signed_compose_from_seeds(l, r))
}

/// Strategy for compose events where the class-5 mutator is
/// guaranteed to produce a falsifier — i.e., `right` has at least
/// one component strictly greater than `left`. Built by sampling a
/// `left` label and an "uplift" delta that is non-zero on at least
/// one component, then setting `right = left.join(delta)` clamped
/// to alphabet ceilings (with a final guarantee that some component
/// strictly exceeds `left`).
fn arb_falsifying_compose() -> impl Strategy<Value = LabelFlowEvent> {
    // Pick `left` from the lower 3/4 of each alphabet so there's
    // always headroom for `right` to be strictly above on some
    // component. SIGMA_C/I/P are 4/3/4; we cap left at (2, 1, 2)
    // so right can be 3/2/3 on at least one axis.
    let left_strat = (
        0u8..((SIGMA_C as u8).saturating_sub(1).max(1)),
        0u8..((SIGMA_I as u8).saturating_sub(1).max(1)),
        0u8..((SIGMA_P as u8).saturating_sub(1).max(1)),
    )
        .prop_map(|(c, i, p)| LatticeLabel { c_idx: c, i_idx: i, p_idx: p });
    // Pick which axis to bump strictly (0 = c, 1 = i, 2 = p).
    let bump_axis = 0u8..3u8;
    (left_strat, bump_axis, any::<u64>()).prop_map(|(left, axis, locus_seed)| {
        // Build right = left, then bump one axis by +1 (clamped).
        // If that axis is already at the ceiling (shouldn't happen
        // given the cap above, but be defensive), fall back to the
        // first non-saturated axis.
        let mut right = left.clone();
        let mut try_axis = axis;
        for _ in 0..3 {
            match try_axis {
                0 if (right.c_idx as usize) < SIGMA_C - 1 => {
                    right.c_idx += 1;
                    break;
                }
                1 if (right.i_idx as usize) < SIGMA_I - 1 => {
                    right.i_idx += 1;
                    break;
                }
                _ if (right.p_idx as usize) < SIGMA_P - 1 => {
                    right.p_idx += 1;
                    break;
                }
                _ => {
                    try_axis = (try_axis + 1) % 3;
                }
            }
        }
        // Guarantee: by construction, right has at least one component
        // strictly greater than left, so right.leq(left) is FALSE
        // and the class-5 mutator MUST return Some(_).
        debug_assert!(!right.leq(&left),
            "arb_falsifying_compose must yield right NOT leq left");
        let out_label = left.join(&right);
        LabelFlowEvent {
            kind: LabelFlowKind::PayloadCompose,
            out_label,
            payload_locus: locus_seed as u32,
            cap_witness: None,
            provenance: None,
            compose_sources: Some((left, right)),
        }
    })
}

// =====================================================================
// Positive + negative proptests (one pair per class)
// =====================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 5_000,
        max_shrink_iters: 1024,
        .. ProptestConfig::default()
    })]

    // --- Class 2 ---

    /// Positive: every signed declass event satisfies
    /// `declass_well_formed`. Closes class-2 σ_min positive coverage.
    #[test]
    fn pt_declass_signed_well_formed(e in arb_signed_declass()) {
        prop_assert!(declass_well_formed(&e),
            "signed declass event must satisfy declass_well_formed");
        prop_assert!(matches!(e.kind, LabelFlowKind::Declassify));
        prop_assert!(e.cap_witness.is_some());
    }

    /// Negative (class 2): stripping the cap witness MUST falsify
    /// `declass_well_formed`. This is the σ_min
    /// `declass_without_capability` adversarial label-flow class
    /// (spec §"Adversarial label flow grammar" item 2).
    #[test]
    fn pt_neg_declass_without_capability(e in arb_signed_declass()) {
        let bad = declass_without_capability(&e);
        prop_assert!(!declass_well_formed(&bad),
            "declass_without_capability mutator must falsify  — falsifier missing");
        prop_assert!(matches!(bad.kind, LabelFlowKind::Declassify));
        prop_assert!(bad.cap_witness.is_none());
    }

    // --- Class 3 ---

    /// Positive: every signed declass event satisfies
    /// `declass_locus_authorized` (cap.target_locus == payload_locus
    /// by construction in `signed_declass_from_seed`).
    #[test]
    fn pt_declass_locus_authorized(e in arb_signed_declass()) {
        prop_assert!(declass_locus_authorized(&e),
            "signed declass event must satisfy declass_locus_authorized");
    }

    /// Negative (class 3): drifting the cap's `target_locus` MUST
    /// falsify `declass_locus_authorized` while preserving
    /// `declass_well_formed`. This is the σ_min `declass_locus_drift`
    /// adversarial label-flow class (spec §"Adversarial label flow
    /// grammar" item 3).
    #[test]
    fn pt_neg_declass_locus_drift(e in arb_signed_declass()) {
        let bad = declass_locus_drift(&e).expect("signed declass has cap_witness");
        prop_assert!(!declass_locus_authorized(&bad),
            "declass_locus_drift mutator must falsify  — falsifier missing");
        // Cap is still present — only its locus is wrong.
        prop_assert!(declass_well_formed(&bad),
            "locus-drift must NOT also strip the cap (would conflate with class 2)");
    }

    // --- Class 4 ---

    /// Positive: every signed oracle event satisfies
    /// `taint_kind_closure_holds`.
    #[test]
    fn pt_oracle_taint_kind_closure(e in arb_signed_oracle()) {
        prop_assert!(taint_kind_closure_holds(&e),
            "signed oracle event must satisfy taint_kind_closure_holds");
        prop_assert!(matches!(e.provenance, Some(ProvenanceTag::RawInputTags)));
    }

    /// Negative (class 4): aliasing the provenance to `ForeignTag`
    /// MUST falsify `taint_kind_closure_holds`. This is the σ_min
    /// `raw_input_alias` adversarial label-flow class (spec
    /// §"Adversarial label flow grammar" item 4).
    #[test]
    fn pt_neg_raw_input_alias(e in arb_signed_oracle()) {
        let bad = raw_input_alias(&e).expect("signed oracle is OpaqueOracle kind");
        prop_assert!(!taint_kind_closure_holds(&bad),
            "raw_input_alias mutator must falsify taint_kind_closure — falsifier missing");
        prop_assert!(matches!(bad.provenance, Some(ProvenanceTag::ForeignTag)));
    }

    // --- Class 5 ---

    /// Positive: every signed compose event satisfies
    /// `payload_discipline_holds` (out_label == left.join(right)
    /// by construction).
    #[test]
    fn pt_compose_payload_discipline(e in arb_signed_compose()) {
        prop_assert!(payload_discipline_holds(&e),
            "signed compose event must satisfy payload_discipline_holds");
    }

    /// Negative (class 5): unjoining the compose (out_label = left,
    /// dropping right) MUST falsify `payload_discipline_holds`
    /// whenever `right` contributes something `left` does not.
    /// Uses `arb_falsifying_compose` which is engineered so the
    /// class-5 mutator ALWAYS finds a falsifier (right strictly above
    /// left on some component). This is the σ_min
    /// `payload_compose_unjoined` adversarial label-flow class (spec
    /// §"Adversarial label flow grammar" item 5).
    #[test]
    fn pt_neg_payload_compose_unjoined(e in arb_falsifying_compose()) {
        let bad = payload_compose_unjoined(&e)
            .expect("arb_falsifying_compose guarantees mutator yields a falsifier");
        prop_assert!(!payload_discipline_holds(&bad),
            "payload_compose_unjoined mutator must falsify PayloadDiscipline — falsifier missing");
    }

    /// Coverage on the broader (any-seed) compose strategy: the
    /// mutator is monotone — it either yields a falsifier or returns
    /// None. There is no third outcome (no false-negative where
    /// the mutator yields a NON-falsifier).
    #[test]
    fn pt_class5_mutator_monotone(e in arb_signed_compose()) {
        if let Some(bad) = payload_compose_unjoined(&e) {
            prop_assert!(!payload_discipline_holds(&bad),
                "if mutator yields Some(bad), bad MUST falsify discipline");
        }
    }

    // --- Cross-class non-interference ---

    /// Class 2 mutator on an `OpaqueOracle` event MUST be a no-op for
    /// `taint_kind_closure_holds` (the cap_witness field is None on
    /// oracles by construction; stripping it is a no-op).
    #[test]
    fn pt_class_independence_oracle_unaffected_by_class2(e in arb_signed_oracle()) {
        let bad = declass_without_capability(&e);
        prop_assert_eq!(taint_kind_closure_holds(&bad), taint_kind_closure_holds(&e));
    }

    /// Class 4 mutator MUST return None on a non-oracle event (it
    /// is type-narrow per the spec taxonomy).
    #[test]
    fn pt_class_independence_class4_narrow(e in arb_signed_declass()) {
        prop_assert!(raw_input_alias(&e).is_none(),
            "raw_input_alias must be type-narrow to OpaqueOracle events");
    }
}

// =====================================================================
// Hand-crafted unit tests — auditable from source alone
// =====================================================================

#[test]
fn unit_class2_handcrafted() {
    // Build a declass event by hand; strip its cap.
    let target_label = LatticeLabel { c_idx: 1, i_idx: 1, p_idx: 1 };
    let event = LabelFlowEvent {
        kind: LabelFlowKind::Declassify,
        out_label: target_label.clone(),
        payload_locus: 42,
        cap_witness: Some(DeclassCapWitness {
            cap_id: [0xAA; 32],
            target_locus: 42,
            target_label,
        }),
        provenance: None,
        compose_sources: None,
    };
    assert!(declass_well_formed(&event));
    let bad = declass_without_capability(&event);
    assert!(!declass_well_formed(&bad), "class 2 hand-crafted falsifier must fail ");
    assert!(bad.cap_witness.is_none());
}

#[test]
fn unit_class3_handcrafted() {
    // Cap authorizes locus 7; payload_locus is 8 → drift.
    let target_label = LatticeLabel { c_idx: 0, i_idx: 1, p_idx: 0 };
    let event = LabelFlowEvent {
        kind: LabelFlowKind::Declassify,
        out_label: target_label.clone(),
        payload_locus: 8,
        cap_witness: Some(DeclassCapWitness {
            cap_id: [0xBB; 32],
            target_locus: 7, // distinct from payload_locus
            target_label,
        }),
        provenance: None,
        compose_sources: None,
    };
    assert!(declass_well_formed(&event), "cap is present");
    assert!(!declass_locus_authorized(&event), "locus 7 != 8 must drift");
}

#[test]
fn unit_class3_drift_mutator_is_idempotent_on_already_drifted() {
    // Start with a signed declass; apply the mutator twice; both
    // applications still falsify locus_authorized.
    let event = signed_declass_from_seed(0xCAFE_BABE_DEAD_BEEF);
    assert!(declass_locus_authorized(&event));
    let bad1 = declass_locus_drift(&event).expect("signed declass has cap");
    assert!(!declass_locus_authorized(&bad1));
    let bad2 = declass_locus_drift(&bad1).expect("still has cap");
    assert!(!declass_locus_authorized(&bad2));
}

#[test]
fn unit_class4_handcrafted() {
    let event = LabelFlowEvent {
        kind: LabelFlowKind::OpaqueOracle,
        out_label: LatticeLabel { c_idx: 0, i_idx: 0, p_idx: 0 },
        payload_locus: 0,
        cap_witness: None,
        provenance: Some(ProvenanceTag::RawInputTags),
        compose_sources: None,
    };
    assert!(taint_kind_closure_holds(&event));
    let bad = raw_input_alias(&event).expect("oracle event");
    assert!(!taint_kind_closure_holds(&bad), "class 4 hand-crafted falsifier");
    assert!(matches!(bad.provenance, Some(ProvenanceTag::ForeignTag)));
}

#[test]
fn unit_class4_returns_none_on_non_oracle() {
    let declass = signed_declass_from_seed(1);
    assert!(raw_input_alias(&declass).is_none());
    let compose = signed_compose_from_seeds(1, 2);
    assert!(raw_input_alias(&compose).is_none());
}

#[test]
fn unit_class5_handcrafted() {
    // left = (0,0,0), right = (1,0,0) → join = (1,0,0).
    // Dropping right yields out_label = (0,0,0) which fails
    // the discipline.
    let left = LatticeLabel { c_idx: 0, i_idx: 0, p_idx: 0 };
    let right = LatticeLabel { c_idx: 1, i_idx: 0, p_idx: 0 };
    let event = LabelFlowEvent {
        kind: LabelFlowKind::PayloadCompose,
        out_label: left.join(&right),
        payload_locus: 0,
        cap_witness: None,
        provenance: None,
        compose_sources: Some((left.clone(), right.clone())),
    };
    assert!(payload_discipline_holds(&event));
    let bad = payload_compose_unjoined(&event).expect("right has c=1, left has c=0");
    assert!(!payload_discipline_holds(&bad), "class 5 hand-crafted falsifier");
    assert_eq!(bad.out_label, left, "unjoined out_label must drop to left");
}

#[test]
fn unit_class5_returns_none_when_right_leq_left() {
    // left = (1,1,1), right = (0,0,0) → join = (1,1,1) = left.
    // Dropping right gives out_label = left = join — no falsifier.
    let left = LatticeLabel { c_idx: 1, i_idx: 1, p_idx: 1 };
    let right = LatticeLabel { c_idx: 0, i_idx: 0, p_idx: 0 };
    let event = LabelFlowEvent {
        kind: LabelFlowKind::PayloadCompose,
        out_label: left.join(&right),
        payload_locus: 0,
        cap_witness: None,
        provenance: None,
        compose_sources: Some((left, right)),
    };
    assert!(payload_compose_unjoined(&event).is_none(),
        "right.leq(left) → no falsifier exists for class 5 mutator");
}

#[test]
fn unit_full_class_taxonomy_smoke() {
    // Smoke test: all four classes have at least one structurally-
    // distinct mutated event; the σ_min floor is "class enumerated"
    // and this asserts each class has a witness in the test harness.
    let signed_d = signed_declass_from_seed(1);
    let signed_o = signed_oracle_from_seed(2);
    let signed_c = signed_compose_from_seeds(3, 4);
    let _ = declass_without_capability(&signed_d);
    let _ = declass_locus_drift(&signed_d).expect("class 3 generator");
    let _ = raw_input_alias(&signed_o).expect("class 4 generator");
    // Class 5 may return None on adversarial seeds where right.leq(left);
    // pick seeds that guarantee a strict join.
    let left = LatticeLabel { c_idx: 0, i_idx: 0, p_idx: 0 };
    let right = LatticeLabel { c_idx: 1, i_idx: 1, p_idx: 1 };
    let compose = LabelFlowEvent {
        kind: LabelFlowKind::PayloadCompose,
        out_label: left.join(&right),
        payload_locus: 0,
        cap_witness: None,
        provenance: None,
        compose_sources: Some((left, right)),
    };
    assert!(payload_compose_unjoined(&compose).is_some(),
        "class 5 must have at least one witness with right strictly above left");
    let _ = signed_c; // exercise constructor
}

#[test]
fn unit_signed_constructors_stable_across_seeds() {
    // Determinism: same seed → same event.
    let a = signed_declass_from_seed(42);
    let b = signed_declass_from_seed(42);
    assert_eq!(a, b);
    let c = signed_oracle_from_seed(42);
    let d = signed_oracle_from_seed(42);
    assert_eq!(c, d);
    let e = signed_compose_from_seeds(1, 2);
    let f = signed_compose_from_seeds(1, 2);
    assert_eq!(e, f);
}
