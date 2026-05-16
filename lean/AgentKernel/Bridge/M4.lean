import AgentKernel.IFC



namespace AgentKernel.Bridge.M4

open AgentKernel.IFC
open AgentKernel.Replay (Kind)


inductive ActionLabel_M4
    (Principal Tag_C Tag_I Tag_P : Type) : Type where
  | emitNonDeclass
      (e : Event Tag_C Tag_I Tag_P) :
      ActionLabel_M4 Principal Tag_C Tag_I Tag_P
  | emitDeclass
      (e : Event Tag_C Tag_I Tag_P)
      (p : DeclassPayload Principal Tag_C Tag_I Tag_P) :
      ActionLabel_M4 Principal Tag_C Tag_I Tag_P

/-! ## Per-arm pre/post predicates

  Each `Next_M4` disjunct's pre/post, transcribed onto Lean's
  `Trace` shape. The bridge predicate does NOT mechanize the
  `inLabel = LabelJoinSet({parent.outLabel : pid ∈ parents})`
  parent-join consistency on the Lean side (treated as free here;
  M8 cross-composition is out of scope for this probe).
-/


def EmitNonDeclassStep
    (Principal : Type)
    {Tag_C Tag_I Tag_P : Type}
    (rawInputTags : Factor Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (t' : Trace Tag_C Tag_I Tag_P) : Prop :=
  let _ : Type := Principal  -- consume the param so unused-var linter is silent
  e.kind ≠ Kind.declassify ∧
  e.kind ≠ Kind.declassMint ∧
  Factor.leq
    (Factor.join e.inLabel.prov e.ctxLabel.prov)
    e.outLabel.prov ∧
  (Factor.overlaps e.outLabel.prov rawInputTags →
    e.kind.isKernelEmit = true) ∧
  t' = t ++ [e]


def EmitDeclassStep
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (p : DeclassPayload Principal Tag_C Tag_I Tag_P)
    (t' : Trace Tag_C Tag_I Tag_P) : Prop :=
  e.kind = Kind.declassify ∧
  dmap e.id = some p ∧
  authorizes p.who p.what ∧
  p.locus = e.id ∧
  p.when t' ∧
  e.outLabel.prov =
    (p.what.interp (Label.join e.inLabel e.ctxLabel)).prov ∧
  (∃ eMint ∈ t', eMint.kind = Kind.declassMint ∧ eMint.id = e.id) ∧
  (Factor.overlaps e.outLabel.prov rawInputTags →
    e.kind.isKernelEmit = true) ∧
  t' = t ++ [e]

/-! ## TLAStep_M4

  Per-arm TLA+-side stepping predicate, indexed by an
  `ActionLabel_M4`. Mechanical mirror of `Next_M4`'s two disjuncts.
-/

/-- The TLA+-side step. One arm per `ActionLabel_M4` constructor;
    each arm's body is the disjunct's pre/post transcribed. -/
def TLAStep_M4
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (a : ActionLabel_M4 Principal Tag_C Tag_I Tag_P)
    (t' : Trace Tag_C Tag_I Tag_P) : Prop :=
  match a with
  | ActionLabel_M4.emitNonDeclass e =>
      EmitNonDeclassStep Principal rawInputTags t e t'
  | ActionLabel_M4.emitDeclass e p =>
      EmitDeclassStep authorizes rawInputTags dmap t e p t'

/-! ## LeanStep_M4

  The Lean-side step. **Defined independently of `TLAStep_M4`**
  as the primitive predicate "`t'` extends `t` by one event satisfying
  `wellLabeledStep`." This is the structural-content shape M4's Lean
  side already encodes via `IFC.wellLabeledStep`.

  Independence from `TLAStep_M4` is the critical design choice that
  makes `BridgeSound_M4_nonMint` substantive (not `Iff.rfl` like M5's). The
  bridge proof must reify the `if-then-else` inside `wellLabeledStep`
  into the `emitNonDeclass`/`emitDeclass` constructors via a
  `by_cases` on `e.kind = Kind.declassify`.
-/

/-- The Lean-side step relation. Defined as "`t'` extends `t` by one
    event `e` such that `wellLabeledStep` holds for `e` in the
    extended trace `t'`."

    This is M4's primitive operational shape: a step is the act of
    appending one event that respects its -or- obligation
    relative to the post-state. -/
def LeanStep_M4
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t t' : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∃ e : Event Tag_C Tag_I Tag_P,
    t' = t ++ [e] ∧
    e.kind ≠ Kind.declassMint ∧
    wellLabeledStep authorizes mintingTrusted rawInputTags dmap t' e

/-! ## BridgeSound_M4_nonMint

  The bridge soundness theorem. Statement:
  `LeanStep_M4 t t' ↔ ∃ a, TLAStep_M4 t a t'`.

  Unlike M5's `Iff.rfl`, this proof requires reifying the
  `if-then-else` inside `wellLabeledStep` into the action-label
  constructors. The forward direction `by_cases` on
  `e.kind = Kind.declassify`; the backward direction `cases a` and
  reassembles `wellLabeledStep` via `if_pos`/`if_neg`.

  **The case-split is the substantive content** — and is the
  structural difference between this probe and the M5 outcome.
-/

/-- **BridgeSound_M4_nonMint.** The Lean-side step relation iff the
    existential closure of the TLA+-side per-arm step relation.

    The forward direction extracts the appended event from
    `LeanStep_M4`, unfolds `wellLabeledStep` (an `if-then-else`),
    and `by_cases` on `e.kind = Kind.declassify` to choose the
    appropriate `ActionLabel_M4` constructor.

    The backward direction destructures the `ActionLabel_M4` and
    reassembles `wellLabeledStep` from the per-arm payload via
    `if_pos`/`if_neg`. -/
theorem BridgeSound_M4_nonMint
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t t' : Trace Tag_C Tag_I Tag_P) :
    LeanStep_M4 authorizes mintingTrusted rawInputTags dmap t t'
      ↔ ∃ a : ActionLabel_M4 Principal Tag_C Tag_I Tag_P,
            TLAStep_M4 authorizes rawInputTags dmap t a t' := by
  constructor
  · -- Forward: from LeanStep_M4, witness an ActionLabel_M4.
    intro hLean
    obtain ⟨e, hAppend, hNotMint, hWL⟩ := hLean
    unfold wellLabeledStep at hWL
    have hClosure := hWL.1
    have hInner := hWL.2
    by_cases hk : e.kind = Kind.declassify
    · -- Declass arm: extract the dmap payload +  obligations
      -- the emitDeclass constructor.
      rw [if_pos hk] at hInner
      obtain ⟨p, hDmap, hAuth, hLocus, hWhen, hOutP, hBack⟩ := hInner
      refine ⟨ActionLabel_M4.emitDeclass e p, ?_⟩
      unfold TLAStep_M4
      exact ⟨hk, hDmap, hAuth, hLocus, hWhen, hOutP, hBack, hClosure, hAppend⟩
    · -- Non-declass-non-mint arm: extract  join-leq closure,
      -- repackage as the emitNonDeclass constructor.
      rw [if_neg hk, if_neg hNotMint] at hInner
      refine ⟨ActionLabel_M4.emitNonDeclass e, ?_⟩
      unfold TLAStep_M4
      exact ⟨hk, hNotMint, hInner, hClosure, hAppend⟩
  · -- Backward: from ∃ a, TLAStep_M4 a, recover LeanStep_M4.
    intro ⟨a, hTLA⟩
    cases a with
    | emitNonDeclass e =>
        unfold TLAStep_M4 at hTLA
        unfold EmitNonDeclassStep at hTLA
        obtain ⟨hKindNe, hKindNeMint, hLeq, hClosure, hAppend⟩ := hTLA
        refine ⟨e, hAppend, hKindNeMint, ?_⟩
        unfold wellLabeledStep
        refine ⟨hClosure, ?_⟩
        rw [if_neg hKindNe, if_neg hKindNeMint]
        exact hLeq
    | emitDeclass e p =>
        unfold TLAStep_M4 at hTLA
        obtain ⟨hKindEq, hDmap, hAuth, hLocus, hWhen, hOutP, hBack, hClosure,
                hAppend⟩ := hTLA
        -- A declass event is not a mint event.
        have hKindNeMint : e.kind ≠ Kind.declassMint := by
          rw [hKindEq]; intro hc; cases hc
        refine ⟨e, hAppend, hKindNeMint, ?_⟩
        unfold wellLabeledStep
        refine ⟨hClosure, ?_⟩
        rw [if_pos hKindEq]
        -- conjunct of 's existential body.
        exact ⟨p, hDmap, hAuth, hLocus, hWhen, hOutP, hBack⟩

/-! ## Closure preservation under each arm

  An honest probe must demonstrate the bridge is **not vacuous**:
  the Lean side's structural invariant (trace-wide `wellLabeled`) is
  preserved by every action arm provided the new event satisfies
  its per-step obligation. Mirrors M5's
  `MintStep_preserves_closed`/`DelegateStep_preserves_closed` shape.

  At M4 there is one structural subtlety: the trace-level
  `wellLabeled` predicate references `t` itself (via the `p.when t`
  trace-relative temporal predicate inside the declass arm). The
  preservation lemmas therefore must explicitly assume the new
  event's per-step obligation holds in the EXTENDED trace `t'`,
  not the pre-state `t` — that is exactly the shape `wellLabeledStep`
  takes inside `LeanStep_M4`'s definition.

  We prove four closure-preservation lemmas:
  1. `EmitNonDeclassStep_preserves_wellLabeled` — appending a
     non-declass event preserves trace-wide well-labeling, provided
     existing events' per-step well-labeling lifts from `t` to `t ++ [e]`.
  2. `EmitDeclassStep_preserves_wellLabeled` — same for declass.
  3. `LeanStep_M4_preserves_wellLabeled` — bridge-level closure:
     every step expressible as `LeanStep_M4` preserves trace-wide
     well-labeling under the same lift hypothesis.
  4. `wellLabeledStep_lifts_under_extension` — the per-step
     well-labeling lift hypothesis itself, holding when the temporal
     predicate `p.when` is monotone under trace extension. (Stated
     as an explicit hypothesis on `dmap`-bound payloads; not a
     theorem, since `p.when` is opaque.)
-/


def DmapTemporalMonotone
    {Principal Tag_C Tag_I Tag_P : Type}
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P) : Prop :=
  ∀ eid p,
    dmap eid = some p →
    p.when t →
    p.when (t ++ [e])


theorem wellLabeledStep_lifts_under_extension
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (e e₀ : Event Tag_C Tag_I Tag_P)
    (hMono : DmapTemporalMonotone dmap t e)
    (h : wellLabeledStep authorizes mintingTrusted rawInputTags
                          dmap t e₀) :
    wellLabeledStep authorizes mintingTrusted rawInputTags
                     dmap (t ++ [e]) e₀ := by
  unfold wellLabeledStep at h ⊢
  refine ⟨h.1, ?_⟩
  have hInner := h.2
  by_cases hk : e₀.kind = Kind.declassify
  · -- Declass-apply: lift the temporal predicate via hMono and lift
    -- eMint ∈ t ++ [e]).
    rw [if_pos hk] at hInner
    rw [if_pos hk]
    obtain ⟨p, hDmap, hAuth, hLocus, hWhen, hOutP, hBack⟩ := hInner
    obtain ⟨eMint, hMintIn, hMintKind, hMintId⟩ := hBack
    refine ⟨p, hDmap, hAuth, hLocus, hMono e₀.id p hDmap hWhen, hOutP, ?_⟩
    exact ⟨eMint, List.mem_append.mpr (Or.inl hMintIn), hMintKind, hMintId⟩
  · by_cases hm : e₀.kind = Kind.declassMint
    · -- Mint: structural content is trace-independent.
      rw [if_neg hk, if_pos hm] at hInner
      rw [if_neg hk, if_pos hm]
      exact hInner
    · -- Non-declass-non-mint: the predicate is trace-independent.
      rw [if_neg hk, if_neg hm] at hInner
      rw [if_neg hk, if_neg hm]
      exact hInner

/-- `wellLabeled` is preserved by `EmitNonDeclassStep`: appending a
    non-declass event whose  closure holds in `t'` preserves
    trace-wide well-labeling, provided existing events' per-step
    obligations lift under the trace extension.

    **Hypothesis on `dmap`'s temporal-predicate monotonicity is
    explicit** (no axiom; see `DmapTemporalMonotone`'s docstring). -/
theorem EmitNonDeclassStep_preserves_wellLabeled
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (t' : Trace Tag_C Tag_I Tag_P)
    (hMono : DmapTemporalMonotone dmap t e)
    (hWL_t : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hStep : EmitNonDeclassStep Principal rawInputTags t e t') :
    wellLabeled authorizes mintingTrusted rawInputTags dmap t' := by
  obtain ⟨hKindNe, hKindNeMint, hLeq, hClosure, hAppend⟩ := hStep
  intro e₀ he₀
  subst hAppend
  rcases List.mem_append.mp he₀ with hMemT | hMemSingleton
  · -- e₀ ∈ t: lift via wellLabeledStep_lifts_under_extension.
    have hOld := hWL_t e₀ hMemT
    exact wellLabeledStep_lifts_under_extension authorizes mintingTrusted
            rawInputTags dmap t e e₀ hMono hOld
  · -- e₀ ∈ [e], i.e. e₀ = e.
    have hEq : e₀ = e := List.mem_singleton.mp hMemSingleton
    subst hEq
    unfold wellLabeledStep
    refine ⟨hClosure, ?_⟩
    rw [if_neg hKindNe, if_neg hKindNeMint]
    exact hLeq

/-- `wellLabeled` is preserved by `EmitDeclassStep`: appending a
    declass event with the -attested payload preserves trace-wide
    well-labeling, provided existing events' per-step obligations
    lift under the trace extension. -/
theorem EmitDeclassStep_preserves_wellLabeled
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (p : DeclassPayload Principal Tag_C Tag_I Tag_P)
    (t' : Trace Tag_C Tag_I Tag_P)
    (hMono : DmapTemporalMonotone dmap t e)
    (hWL_t : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hStep : EmitDeclassStep authorizes rawInputTags dmap t e p t') :
    wellLabeled authorizes mintingTrusted rawInputTags dmap t' := by
  obtain ⟨hKindEq, hDmap, hAuth, hLocus, hWhen, hOutP, hBack, hClosure,
          hAppend⟩ := hStep
  intro e₀ he₀
  subst hAppend
  cases (List.mem_append.mp he₀) with
  | inl hMemT =>
      have hOld := hWL_t e₀ hMemT
      exact wellLabeledStep_lifts_under_extension authorizes mintingTrusted
              rawInputTags dmap t e e₀ hMono hOld
  | inr hMemSingleton =>
      have hEq : e₀ = e := List.mem_singleton.mp hMemSingleton
      subst hEq
      unfold wellLabeledStep
      refine ⟨hClosure, ?_⟩
      rw [if_pos hKindEq]
      exact ⟨p, hDmap, hAuth, hLocus, hWhen, hOutP, hBack⟩

/-- **Closure preservation across the bridge.** Every step
    expressible as `LeanStep_M4` (equivalently `∃ a, TLAStep_M4 .. a ..`)
    preserves trace-wide `wellLabeled`, provided the temporal-predicate
    monotonicity hypothesis holds.

    This is the structural-content lemma the bridge buys: M4's
    operational closure (`LabelFlowSanity` in `Lattice.tla`, TLC-
    checked at 16,059 reachable states per PROJECT_STATE inventory)
    is matched on the Lean side by `wellLabeled` preserved across
    every disjunct of the step relation. -/
theorem LeanStep_M4_preserves_wellLabeled
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t t' : Trace Tag_C Tag_I Tag_P)
    (hWL_t : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hStep : LeanStep_M4 authorizes mintingTrusted rawInputTags dmap t t')
    (hMono : ∀ e, t' = t ++ [e] →
      DmapTemporalMonotone dmap t e) :
    wellLabeled authorizes mintingTrusted rawInputTags dmap t' := by
  -- Recover the action label from LeanStep_M4 via BridgeSound_M4_nonMint.
  have hBridge := (BridgeSound_M4_nonMint authorizes mintingTrusted rawInputTags
                                    dmap t t').mp hStep
  obtain ⟨a, hTLA⟩ := hBridge
  cases a with
  | emitNonDeclass e =>
      unfold TLAStep_M4 at hTLA
      have hStep' : EmitNonDeclassStep Principal rawInputTags t e t' := hTLA
      have hAppend := hStep'.2.2.2.2
      exact EmitNonDeclassStep_preserves_wellLabeled authorizes
              mintingTrusted rawInputTags dmap t e t'
              (hMono e hAppend) hWL_t hStep'
  | emitDeclass e p =>
      unfold TLAStep_M4 at hTLA
      have hStep' : EmitDeclassStep authorizes rawInputTags dmap t e p t' := hTLA
      -- hAppend (the t'-extension equation) is now the 9th, so projection
      -- depth advances from .2^7 to .2^8.
      have hAppend := hStep'.2.2.2.2.2.2.2.2
      exact EmitDeclassStep_preserves_wellLabeled authorizes
              mintingTrusted rawInputTags dmap t e p t'
              (hMono e hAppend) hWL_t hStep'

end AgentKernel.Bridge.M4

-- ============================================================
-- `lake env lean MeasureAxioms.lean` or `#print axioms` in editor;
-- this file is wired into `AgentKernel.lean`'s import list and
-- referenced from `MeasureAxioms.lean`).
-- ============================================================

#print axioms AgentKernel.Bridge.M4.BridgeSound_M4_nonMint
#print axioms AgentKernel.Bridge.M4.wellLabeledStep_lifts_under_extension
#print axioms AgentKernel.Bridge.M4.EmitNonDeclassStep_preserves_wellLabeled
#print axioms AgentKernel.Bridge.M4.EmitDeclassStep_preserves_wellLabeled
#print axioms AgentKernel.Bridge.M4.LeanStep_M4_preserves_wellLabeled

-- ============================================================
-- (additive past line 679; repair-v1.4-residual-batch).
--
-- Threads `IFC.kernelEmit_compose_routed` through `Bridge/M4` per
-- (`t3_noninterference_kernel_emit_compose_routed{,_strong}`); this
-- repair adds the M4-side typed mirror so the routing witness can
-- be threaded INTO bridge step relations as a per-event predicate.
-- predicate-relay shape.
--
-- * `kernelEmit_routed_at` — PREDICATE (per-event lift of the IFC
--   trace-level predicate's per-event body).
-- * `kernelEmit_compose_routed_iff_per_event` — STRUCTURAL
--   PACKAGING (pure unfolding equivalence relating the IFC
--   trace-level predicate to the per-event lift).
-- * `EmitNonDeclassStep_implies_kernelEmit_routed_target` —
--   STRUCTURAL THREADING / EXISTENCE LEMMA (given the M4 step
--   AND the per-event routing witness, expose the t' = t ++ [e]
--   extension AND the routing witness as a conjunction usable by
--   downstream consumers).
--
-- Honest residual (binding for all three declarations below):
-- The kernel-emit axis is `Kind.isKernelEmit ∈ {externalReq,
-- externalResp, read}` (Replay.lean line 212-214). Declassify arms
-- (`Kind.declassify`, `Kind.declassMint`) have `Kind.isKernelEmit
-- = false`, so the per-event predicate `kernelEmit_routed_at e`
-- is VACUOUSLY satisfied on declass arms (the implication's
-- antecedent fails). The M4 mirror correspondingly does NOT
-- strengthen `EmitDeclassStep`; the routing witness is on the
-- arms not on the kernel-emit axis) verbatim.
--
-- Conformance witnesses for the IFC trace-level predicate remain
-- suite begins carrying kernel-emit composition witnesses"
--
-- * `kernelEmit_routed_at` — `def`, no axioms.
-- * `kernelEmit_compose_routed_iff_per_event` — Tier 1
--   axiom-free predicted (pure unfolding + the standard
--   `∀ x ∈ l, P x` ≡ `∀ x, x ∈ l → P x` Lean idiom). If
--   measurement comes back Tier 2 [propext], that's an honest
-- * `EmitNonDeclassStep_implies_kernelEmit_routed_target` —
--   Tier 2 [propext] predicted (composes with the `t' = t ++ [e]`
--   conjunct of `EmitNonDeclassStep`).
-- ============================================================

namespace AgentKernel.Bridge.M4

open AgentKernel.IFC
open AgentKernel.Replay (Kind)


def kernelEmit_routed_at
    {Tag_C Tag_I Tag_P : Type}
    (e : Event Tag_C Tag_I Tag_P) : Prop :=
  e.kind.isKernelEmit = true →
    ∃ (concat : Unit → Unit → Unit)
      (p1 p2 : LabeledPayload Unit Tag_C Tag_I Tag_P),
        p1.label = e.inLabel ∧
        p2.label = e.ctxLabel ∧
        e.outLabelPayload =
          { payload := concat p1.payload p2.payload
          , label   := Label.join p1.label p2.label }


theorem kernelEmit_compose_routed_iff_per_event
    {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P) :
    IFC.kernelEmit_compose_routed t ↔
      ∀ e ∈ t, kernelEmit_routed_at e := by
  unfold IFC.kernelEmit_compose_routed kernelEmit_routed_at
  exact Iff.rfl


theorem EmitNonDeclassStep_implies_kernelEmit_routed_target
    {Principal Tag_C Tag_I Tag_P : Type}
    (rawInputTags : Factor Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (t' : Trace Tag_C Tag_I Tag_P)
    (hStep : EmitNonDeclassStep Principal rawInputTags t e t')
    (hRouted : kernelEmit_routed_at e) :
    t' = t ++ [e] ∧ kernelEmit_routed_at e := by
  refine ⟨?_, hRouted⟩
  -- Extract the 5th conjunct (`t' = t ++ [e]`) from
  -- `EmitNonDeclassStep`'s record-tuple body. Per the
  -- definition at line 239-254, the conjuncts are:
  --   1. e.kind ≠ Kind.declassify
  --   2. e.kind ≠ Kind.declassMint
  --   3. Factor.leq (...) e.outLabel.prov
  --   4. (Factor.overlaps ... → e.kind.isKernelEmit = true)
  --   5. t' = t ++ [e]      ← projection .2.2.2.2
  exact hStep.2.2.2.2

end AgentKernel.Bridge.M4

#print axioms AgentKernel.Bridge.M4.kernelEmit_compose_routed_iff_per_event
#print axioms AgentKernel.Bridge.M4.EmitNonDeclassStep_implies_kernelEmit_routed_target
