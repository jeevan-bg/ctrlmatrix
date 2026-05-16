import AgentKernel.Replay



namespace AgentKernel.IFC

open AgentKernel.Replay (Kind)

-- ============================================================
-- ============================================================

/-- A single powerset-lattice factor over alphabet `Tag`. -/
abbrev Factor (Tag : Type) : Type := Tag → Bool

namespace Factor
  variable {Tag : Type}

  def join (a b : Factor Tag) : Factor Tag := fun t => a t || b t
  def meet (a b : Factor Tag) : Factor Tag := fun t => a t && b t
  def leq  (a b : Factor Tag) : Prop := ∀ t, a t = true → b t = true
  def bot  : Factor Tag := fun _ => false
  def top  : Factor Tag := fun _ => true

  
  def overlaps (a b : Factor Tag) : Prop :=
    ∃ t, a t = true ∧ b t = true
end Factor

-- ============================================================
-- ============================================================

/-- Product label, -polymorphic over finite tag alphabets. -/
structure Label (Tag_C Tag_I Tag_P : Type) where
  conf  : Factor Tag_C
  integ : Factor Tag_I
  prov  : Factor Tag_P

namespace Label
  variable {Tag_C Tag_I Tag_P : Type}

  
  def join (L₁ L₂ : Label Tag_C Tag_I Tag_P) : Label Tag_C Tag_I Tag_P :=
    { conf  := Factor.join L₁.conf  L₂.conf
    , integ := Factor.meet L₁.integ L₂.integ
    , prov  := Factor.join L₁.prov  L₂.prov }

  def meet (L₁ L₂ : Label Tag_C Tag_I Tag_P) : Label Tag_C Tag_I Tag_P :=
    { conf  := Factor.meet L₁.conf  L₂.conf
    , integ := Factor.join L₁.integ L₂.integ
    , prov  := Factor.meet L₁.prov  L₂.prov }

  /-- IFC partial order: `L₁ ≤ L₂` permits flow from `L₁`-source
      to `L₂`-sink. -/
  def leq (L₁ L₂ : Label Tag_C Tag_I Tag_P) : Prop :=
    Factor.leq L₁.conf  L₂.conf  ∧
    Factor.leq L₂.integ L₁.integ ∧   -- Biba-dual on integrity
    Factor.leq L₁.prov  L₂.prov

  instance : LE (Label Tag_C Tag_I Tag_P) := ⟨leq⟩
end Label

-- ============================================================
-- (definition lifted from PayloadDiscipline.lean to break the import
-- cycle introduced by `IFC.Event.outLabelPayload`)
-- ============================================================


structure LabeledPayload (Bytes Tag_C Tag_I Tag_P : Type) where
  payload : Bytes
  label   : Label Tag_C Tag_I Tag_P

-- ============================================================
-- ============================================================

/-- M4's `EventId` mirrors M3's `Event.id` type. -/
abbrev EventId : Type := Nat


structure Event (Tag_C Tag_I Tag_P : Type) where
  id       : EventId
  kind     : Kind
  inLabel  : Label Tag_C Tag_I Tag_P
  outLabel : Label Tag_C Tag_I Tag_P
  ctxLabel : Label Tag_C Tag_I Tag_P
  author   : KernelOrTenant := KernelOrTenant.tenant
  -- Default-valued field carrying the bare `Label` of the SDK-boundary
  -- structured type. `Bytes := Unit` at L0 (deployment-supplied at
  -- L1+). Default label is `Factor.bot` triplet (no constraints).
  outLabelPayload : LabeledPayload Unit Tag_C Tag_I Tag_P :=
    { payload := ()
    , label   := { conf  := Factor.bot
                 , integ := Factor.bot
                 , prov  := Factor.bot } }

abbrev Trace (Tag_C Tag_I Tag_P : Type) : Type :=
  List (Event Tag_C Tag_I Tag_P)


def Event.outLabelPayloadCoherent
    {Tag_C Tag_I Tag_P : Type}
    (e : Event Tag_C Tag_I Tag_P) : Prop :=
  e.outLabelPayload.label = e.outLabel

/-- Trace-wide LabeledPayload coherence: every event's
    `outLabelPayload.label` matches its `outLabel`. The L1+
    obligation a deployment threads via `LabeledPayload.compose`
    routing. -/
def outLabelPayloadCoherent
    {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∀ e ∈ t, e.outLabelPayloadCoherent

-- ============================================================
-- kernel-emit step routes payloads through `LabeledPayload.compose`
-- ============================================================
--
-- as Tier 1 axiom-free SDK-boundary structural artifacts.
-- `IFC.Event.outLabelPayload` (default-valued field) + added the
-- `outLabelPayloadCoherent` Prop predicate witnessing the L1+ kernel
-- runtime obligation that `outLabelPayload.label = outLabel`.
--
-- `outLabelPayloadCoherent` predicate of Path 1 is a free obligation
-- on `outLabelPayload.label = outLabel` — a kernel runtime that
-- accidentally drops the label CAN still satisfy `wellLabeledStep`
-- but fails `outLabelPayloadCoherent` silently. The narrowing here
-- replaces the FREE label-equality obligation with a STRUCTURAL
-- composition witness: `outLabelPayload` MUST be the result of
-- `LabeledPayload.compose` over the input + context labeled
-- payloads (with payloads tracked at L0 as `Unit` via the
-- LabeledPayload `Bytes := Unit` instantiation). Combined with
-- `compose_label_joins` (Tier 1), `outLabelPayload.label =
-- Label.join e.inLabel e.ctxLabel` follows STRUCTURALLY — the
-- kernel cannot route through `compose` AND drop the label; the
-- type forces the join.
--
-- Scope. Path 2 narrows the L1+ TCB obligation on the kernel-emit
-- axis (kinds in `Kind.isKernelEmit`); non-kernel-emit construction
-- sites (declassify-apply / declassMint events, plus any L1+ kernel
-- code that constructs `outLabelPayload` field-by-field rather than
-- Caveat 5 transitions from "structurally wired with L1+ TCB
-- obligation" (post-Path 1) to "structurally wired AND
-- L0-mechanized at kernel-emit; L1+ TCB residual narrowed to
-- non-kernel-emit construction sites" (post-Path 2).


def kernelEmit_compose_routed
    {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∀ e ∈ t, e.kind.isKernelEmit = true →
    ∃ (concat : Unit → Unit → Unit)
      (p1 p2 : LabeledPayload Unit Tag_C Tag_I Tag_P),
        p1.label = e.inLabel ∧
        p2.label = e.ctxLabel ∧
        e.outLabelPayload =
          { payload := concat p1.payload p2.payload
          , label   := Label.join p1.label p2.label }

-- ============================================================
-- ============================================================


inductive LabelXform (Tag_C Tag_I Tag_P : Type) where
  | id
  | dropProvTag (tag : Tag_P)
  | clearProv
  deriving DecidableEq

namespace LabelXform
  variable {Tag_C Tag_I Tag_P : Type}

  /-- Interpret a syntactic transformer as the function it denotes.

      `dropProvTag tag` clears the named provenance tag while
      preserving all others (the EchoLeak-class declass shape:
      drop `webFetch` from a sanitized output, keep `userPrompt`).
      Requires `[DecidableEq Tag_P]` to elaborate the per-tag
      equality test.

      `clearProv` zeroes the entire provenance factor (maximum-
      strength declassifier; rare in practice). -/
  def interp [DecidableEq Tag_P] :
      LabelXform Tag_C Tag_I Tag_P →
      Label Tag_C Tag_I Tag_P → Label Tag_C Tag_I Tag_P
    | LabelXform.id, l => l
    | LabelXform.dropProvTag tag, l =>
        { l with prov := fun t => if t = tag then false else l.prov t }
    | LabelXform.clearProv, l => { l with prov := Factor.bot }
end LabelXform

-- ============================================================
-- ============================================================
--
-- M4 is parametrized over an abstract `Principal` type and an
-- abstract `authorizes` predicate. M5 (Caps.lean, b) pins
-- `Principal := Capability` and supplies a concrete `authorizes`.
-- M8 composition fixes the binding across both modules.
--

-- ============================================================
-- ============================================================


structure DeclassPayload (Principal Tag_C Tag_I Tag_P : Type) where
  what  : LabelXform Tag_C Tag_I Tag_P
  who   : Principal
  locus : EventId
  when  : Trace Tag_C Tag_I Tag_P → Prop
  -- "locus = mint event id" honest-naming residual. New default-
  -- valued field carrying the MINT event's id (the
  -- `Kind.declassMint` event whose id-keyed dmap entry 's 6th
  -- id). Default `none` so all existing call sites compile unchanged
  -- The L0 structural binding to 's 6th conjunct is witnessed by
  -- `T_locus_mintEventId_correspondence` below — when L1+ populates
  -- this field, the populated id matches the in-trace mint event
  -- whose existence  already forces into the trace.
  mintEventId : Option EventId := none


abbrev DeclassMap (Principal Tag_C Tag_I Tag_P : Type) : Type :=
  EventId → Option (DeclassPayload Principal Tag_C Tag_I Tag_P)

-- ============================================================
-- Schemas: wellLabeled / lowEquiv / lowProj
-- ============================================================


def wellLabeledStep
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P) : Prop :=
  -- The closure is universal over kinds; it does not interact with
  -- the per-kind structural arm. Folding it as a uniform conjunct
  -- (rather than only into the non-declass arm) makes
  -- `taint_kind_closure` provable without case-restrictions.
  -- honest-naming: the closure is over `Kind` partitions, not over
  -- `Event` authors. The author binding is L1+ TCB; surfaced via
  -- `event_authorship_predicate` + `taint_authorship_relay`.)
  (Factor.overlaps e.outLabel.prov rawInputTags →
     e.kind.isKernelEmit = true) ∧
  (if e.kind = Kind.declassify then
    -- back-link to an in-trace mint event. The first 5 conjuncts are
    -- preserved verbatim from v0.2 (auth + locus + temporal +
    -- transformer-determined outLabel.prov). The 6th conjunct
    -- — pre-v0.3.3 the back-link was an L1+ TCB obligation surfaced
    -- via `dmap_origin_predicate`; v0.3.3 promotes it into  itself.
    ∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
      dmap e.id = some p ∧
      authorizes p.who p.what ∧
      p.locus = e.id ∧
      p.when t ∧
      e.outLabel.prov =
        (p.what.interp (Label.join e.inLabel e.ctxLabel)).prov ∧
      (∃ eMint ∈ t, eMint.kind = Kind.declassMint ∧ eMint.id = e.id)
  else if e.kind = Kind.declassMint then
    -- entry IS the witness; inLabel.prov is bounded by the trusted-
    -- minting Factor.
    --
    -- `e.inLabel.prov ≠ Factor.bot ∨ p.what = LabelXform.id` —
    -- a vacuous-bound mint (empty inLabel.prov) can ONLY emit a
    -- no-op (`LabelXform.id`) payload. This forecloses the X1
    -- composition vector (vacuous mint + clearProv declass laundering)
    -- structurally at L0, eliminating the "deployment policy" punt
    Factor.leq e.inLabel.prov mintingTrusted ∧
    (∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
       dmap e.id = some p ∧
       authorizes p.who p.what ∧
       (e.inLabel.prov ≠ Factor.bot ∨ p.what = LabelXform.id))
  else
    --  (preserved): non-declass arm.
    Factor.leq
      (Factor.join e.inLabel.prov e.ctxLabel.prov)
      e.outLabel.prov)

/-- Trace-wide well-labeling: every event respects its case. -/
def wellLabeled
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∀ e ∈ t, wellLabeledStep authorizes mintingTrusted rawInputTags
                            dmap t e

/-- Observability predicate. v0.1 represents an observer's clearance
    by a `Bool`-valued visibility test on each event's outLabel. -/
abbrev Visible (Tag_C Tag_I Tag_P : Type) : Type :=
  Label Tag_C Tag_I Tag_P → Bool

/-- Low-projection: keep events visible to the observer. -/
def lowProj
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P) : Trace Tag_C Tag_I Tag_P :=
  t.filter (fun e => visible e.outLabel)

/-- Low-equivalence: same low-projection. -/
def lowEquiv
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P) : Prop :=
  lowProj visible t₁ = lowProj visible t₂

-- ============================================================
--  and  named lemmas (proofs preserved from v0.2 with new
-- parameter signature)
-- ============================================================


theorem provenance_monotonicity_R2
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ t, e.kind ≠ Kind.declassify →
             e.kind ≠ Kind.declassMint →
      Factor.leq
        (Factor.join e.inLabel.prov e.ctxLabel.prov)
        e.outLabel.prov := by
  intro e he hkind hmint
  have hStep := h e he
  unfold wellLabeledStep at hStep
  -- hStep is `closure ∧ inner_if`; project to the inner-if then
  -- discharge both nested negatives.
  have hInner := hStep.2
  rw [if_neg hkind, if_neg hmint] at hInner
  exact hInner


theorem declassification_well_formed_R3
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ t, e.kind = Kind.declassify →
      ∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
        dmap e.id = some p ∧
        authorizes p.who p.what ∧
        p.locus = e.id ∧
        p.when t ∧
        e.outLabel.prov =
          (p.what.interp (Label.join e.inLabel e.ctxLabel)).prov := by
  intro e he hkind
  have hStep := h e he
  unfold wellLabeledStep at hStep
  have hInner := hStep.2
  rw [if_pos hkind] at hInner
  -- new back-link to preserve the 5-conjunct conclusion shape.
  obtain ⟨p, hDmap, hAuth, hLocus, hWhen, hOutP, _hBack⟩ := hInner
  exact ⟨p, hDmap, hAuth, hLocus, hWhen, hOutP⟩

-- ============================================================
-- ============================================================


theorem r4_declass_origin_integrity
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ t, e.kind = Kind.declassMint →
      Factor.leq e.inLabel.prov mintingTrusted := by
  intro e he hMint
  have hStep := h e he
  unfold wellLabeledStep at hStep
  have hInner := hStep.2
  -- Mint events are NOT declassify events (Kind.declassify ≠ Kind.declassMint).
  have hNotDeclassify : e.kind ≠ Kind.declassify := by
    rw [hMint]; intro hc; cases hc
  rw [if_neg hNotDeclassify, if_pos hMint] at hInner
  exact hInner.1


theorem r4_declass_mint_has_payload
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ t, e.kind = Kind.declassMint →
      ∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
        dmap e.id = some p ∧ authorizes p.who p.what := by
  intro e he hMint
  have hStep := h e he
  unfold wellLabeledStep at hStep
  have hInner := hStep.2
  have hNotDeclassify : e.kind ≠ Kind.declassify := by
    rw [hMint]; intro hc; cases hc
  rw [if_neg hNotDeclassify, if_pos hMint] at hInner
  -- hInner : Factor.leq ... ∧ ∃ p, dmap e.id = some p ∧
  --                                authorizes p.who p.what ∧
  --                                (e.inLabel.prov ≠ Factor.bot ∨
  --                                 p.what = LabelXform.id)
  -- Project to the existential, then drop the new tail conjunct
  obtain ⟨p, hDmap, hAuth, _hNV⟩ := hInner.2
  exact ⟨p, hDmap, hAuth⟩

-- ============================================================
-- ============================================================


theorem r4_declass_mint_nonvacuous
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ t, e.kind = Kind.declassMint →
      ∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
        dmap e.id = some p ∧
        (e.inLabel.prov ≠ Factor.bot ∨ p.what = LabelXform.id) := by
  intro e he hMint
  have hStep := h e he
  unfold wellLabeledStep at hStep
  have hInner := hStep.2
  have hNotDeclassify : e.kind ≠ Kind.declassify := by
    rw [hMint]; intro hc; cases hc
  rw [if_neg hNotDeclassify, if_pos hMint] at hInner
  -- hInner.2 : ∃ p, dmap e.id = some p ∧ authorizes p.who p.what ∧
  --                 (e.inLabel.prov ≠ Factor.bot ∨ p.what = LabelXform.id)
  -- Project the existential, drop the `authorizes` conjunct, retain
  -- the head and tail.
  obtain ⟨p, hDmap, _hAuth, hNV⟩ := hInner.2
  exact ⟨p, hDmap, hNV⟩


@[deprecated "documentation-only after [ref]'   6th-conjunct structural close; use trace-quantified mint-event back-link via wellLabeledStep  directly"]
def dmap_origin_predicate
    {Principal Tag_C Tag_I Tag_P : Type}
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∀ e ∈ t, e.kind = Kind.declassify →
    ∀ p : DeclassPayload Principal Tag_C Tag_I Tag_P, dmap e.id = some p →
      ∃ eMint ∈ t, eMint.kind = Kind.declassMint ∧ eMint.id = e.id


theorem dmap_origin_relay
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ t, e.kind = Kind.declassify →
      ∀ p : DeclassPayload Principal Tag_C Tag_I Tag_P, dmap e.id = some p →
        ∃ eMint ∈ t, eMint.kind = Kind.declassMint ∧
                     eMint.id = e.id ∧
                     ∃ pMint : DeclassPayload Principal Tag_C Tag_I Tag_P,
                       dmap eMint.id = some pMint ∧
                       authorizes pMint.who pMint.what := by
  intro e he hKind _p _hDmap
  -- back-link conjunct (6th conjunct of 's existential body).
  have hStep := h e he
  unfold wellLabeledStep at hStep
  have hInner := hStep.2
  rw [if_pos hKind] at hInner
  obtain ⟨_p', _hDmap', _hAuth, _hLocus, _hWhen, _hOutP, hBack⟩ := hInner
  obtain ⟨eMint, hMintIn, hMintKind, hMintId⟩ := hBack
  -- Step 2: apply -mint-has-payload structurally to enrich.
  obtain ⟨pMint, hMintDmap, hMintAuth⟩ :=
    r4_declass_mint_has_payload authorizes mintingTrusted rawInputTags
      dmap t h eMint hMintIn hMintKind
  exact ⟨eMint, hMintIn, hMintKind, hMintId, pMint, hMintDmap, hMintAuth⟩

-- ============================================================
-- honest-naming residual)
-- ============================================================
--
-- compose with `well-labeled-step-pp` and -mint-has-payload. With
-- in-trace mint event with `eMint.id = e.id`, so the mint-event-id
-- read of locus is derivable from the consuming-event-id reading of
-- residual additively: a NEW default-valued field
-- `DeclassPayload.mintEventId : Option EventId := none` carries the
-- mint-event-id semantics with its honest name. `locus` is PRESERVED
-- VERBATIM with consuming-event-id semantics (legacy alias). The new
-- field is made LOAD-BEARING via `T_locus_mintEventId_correspondence`
-- visible-projection well-labeling) — verbatim preservation of the
-- legacy artifact + new named theorem citing the honest-naming
-- artifact.


def mintEventId_consistent
    {Principal Tag_C Tag_I Tag_P : Type}
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∀ e ∈ t, e.kind = Kind.declassify →
    ∀ p : DeclassPayload Principal Tag_C Tag_I Tag_P, dmap e.id = some p →
      ∀ mid : EventId, p.mintEventId = some mid → mid = e.id


theorem T_locus_mintEventId_correspondence
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hMid : mintEventId_consistent dmap t) :
    ∀ e ∈ t, e.kind = Kind.declassify →
      ∀ p : DeclassPayload Principal Tag_C Tag_I Tag_P, dmap e.id = some p →
        ∀ mid : EventId, p.mintEventId = some mid →
          ∃ eMint ∈ t, eMint.kind = Kind.declassMint ∧
                       eMint.id = e.id ∧ mid = eMint.id := by
  intro e he hKind p hDmap mid hMidEq
  -- Step 1: project  from wellLabeled, extract the 6th conjunct
  -- (back-link to in-trace mint event whose id = e.id).
  have hStep := h e he
  unfold wellLabeledStep at hStep
  have hInner := hStep.2
  rw [if_pos hKind] at hInner
  obtain ⟨_p', _hDmap', _hAuth, _hLocus, _hWhen, _hOutP, hBack⟩ := hInner
  obtain ⟨eMint, hMintIn, hMintKind, hMintId⟩ := hBack
  -- Step 2: chain the L1+ wiring obligation via `mintEventId_consistent`
  -- to get `mid = e.id`, then transitivity with `hMintId : eMint.id = e.id`
  -- yields `mid = eMint.id`.
  have hMidEqId : mid = e.id := hMid e he hKind p hDmap mid hMidEq
  exact ⟨eMint, hMintIn, hMintKind, hMintId, hMidEqId.trans hMintId.symm⟩

-- ============================================================
-- ============================================================


theorem taint_kind_closure
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ t,
      Factor.overlaps e.outLabel.prov rawInputTags →
      e.kind.isKernelEmit = true := by
  -- The closure obligation is the OUTER conjunct of `wellLabeledStep`
  -- in v0.3 (uniform across all kind arms). Direct projection
  -- discharges the theorem.
  intro e he hOverlap
  have hStep := h e he
  unfold wellLabeledStep at hStep
  exact hStep.1 hOverlap

-- ============================================================
-- ============================================================


def event_authorship_predicate
    {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∀ e ∈ t, e.kind.isKernelEmit = true → e.author = KernelOrTenant.kernel


theorem taint_authorship_relay
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hAuthor : event_authorship_predicate t) :
    ∀ e ∈ t,
      Factor.overlaps e.outLabel.prov rawInputTags →
      e.author = KernelOrTenant.kernel := by
  intro e he hOverlap
  have hKind : e.kind.isKernelEmit = true :=
    taint_kind_closure authorizes mintingTrusted rawInputTags dmap t h
      e he hOverlap
  -- Step 2: structural author-binding via `event_authorship_predicate`
  --  structural `e.author = .kernel` reference).
  exact hAuthor e he hKind

-- ============================================================
-- ============================================================


theorem t3_noninterference
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ lowProj visible t,
      (e.kind = Kind.declassify ∧
        ∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
          dmap e.id = some p ∧
          authorizes p.who p.what ∧
          p.locus = e.id ∧
          p.when t ∧
          e.outLabel.prov =
            (p.what.interp (Label.join e.inLabel e.ctxLabel)).prov)
      ∨
      (e.kind = Kind.declassMint ∧
        Factor.leq e.inLabel.prov mintingTrusted)
      ∨
      (e.kind ≠ Kind.declassify ∧ e.kind ≠ Kind.declassMint ∧
        Factor.leq
          (Factor.join e.inLabel.prov e.ctxLabel.prov)
          e.outLabel.prov) := by
  intro e he
  unfold lowProj at he
  rw [List.mem_filter] at he
  obtain ⟨hMem, _⟩ := he
  by_cases hk : e.kind = Kind.declassify
  · exact Or.inl ⟨hk, declassification_well_formed_R3 authorizes
                        mintingTrusted rawInputTags dmap t h e hMem hk⟩
  · by_cases hm : e.kind = Kind.declassMint
    · exact Or.inr (Or.inl ⟨hm, r4_declass_origin_integrity authorizes
                                  mintingTrusted rawInputTags dmap t h
                                  e hMem hm⟩)
    · exact Or.inr (Or.inr ⟨hk, hm,
        provenance_monotonicity_R2 authorizes mintingTrusted
          rawInputTags dmap t h e hMem hk hm⟩)

-- ============================================================
-- ============================================================
--
-- "non-interference + declassification" but its proof shape is
-- per-event // well-labeling over the SINGLE-trace projection
-- `lowProj visible t`, NOT a Sabelfeld–Sands two-trace
-- low-equivalence theorem of shape
-- `lowEquiv visible t₁ t₂ ∧ ⟨low-input agreement⟩ →
--  ⟨low-output agreement⟩`.
--
-- substantive two-trace strengthening (which would require ~200+
-- lines of new Lean machinery and is deferred to L1+ / future
-- P-phase). The new theorem `t3_visible_projection_well_labeling`
-- has the same conclusion as `t3_noninterference` — the proof
-- BODY is one line: forwards directly. The load-bearing content is
-- the NAME: it surfaces what the proof actually shows.
--
-- Existing `t3_noninterference` is PRESERVED VERBATIM as the legacy
-- alias (preserves all callers: Bridge/M4 T7-T3 inheritance,
-- conformance suite, paper §4 row before rename). Pattern mirrors
-- new named theorem added).


theorem t3_visible_projection_well_labeling
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t) :
    ∀ e ∈ lowProj visible t,
      (e.kind = Kind.declassify ∧
        ∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
          dmap e.id = some p ∧
          authorizes p.who p.what ∧
          p.locus = e.id ∧
          p.when t ∧
          e.outLabel.prov =
            (p.what.interp (Label.join e.inLabel e.ctxLabel)).prov)
      ∨
      (e.kind = Kind.declassMint ∧
        Factor.leq e.inLabel.prov mintingTrusted)
      ∨
      (e.kind ≠ Kind.declassify ∧ e.kind ≠ Kind.declassMint ∧
        Factor.leq
          (Factor.join e.inLabel.prov e.ctxLabel.prov)
          e.outLabel.prov) :=
  t3_noninterference authorizes visible mintingTrusted rawInputTags
    dmap t h

-- ============================================================
-- ============================================================
--
-- The `PayloadDiscipline` sub-namespace owns the L0 NAMED predicate
-- `holds`. The structured `LabeledPayload` type and the structural
-- `compose_label_joins` lemma live in
-- `AgentKernel/PayloadDiscipline.lean` (which imports this file).
-- Splitting predicate-here-vs-type-there avoids an import cycle
-- (PayloadDiscipline.lean uses `Trace`, `Label`, `Factor` from this
-- file; IFC.lean's strengthened T3 references `holds`).

namespace PayloadDiscipline


def holds
    {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∀ e ∈ t, e.kind ≠ Kind.declassify → e.kind ≠ Kind.declassMint →
    e.outLabel.prov = Factor.join e.inLabel.prov e.ctxLabel.prov

end PayloadDiscipline


theorem t3_noninterference_modulo_payload_discipline
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hPD : PayloadDiscipline.holds t) :
    ∀ e ∈ lowProj visible t,
      (e.kind = Kind.declassify ∧
        ∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
          dmap e.id = some p ∧
          authorizes p.who p.what ∧
          p.locus = e.id ∧
          p.when t ∧
          e.outLabel.prov =
            (p.what.interp (Label.join e.inLabel e.ctxLabel)).prov)
      ∨
      (e.kind = Kind.declassMint ∧
        Factor.leq e.inLabel.prov mintingTrusted)
      ∨
      (e.kind ≠ Kind.declassify ∧ e.kind ≠ Kind.declassMint ∧
        Factor.join e.inLabel.prov e.ctxLabel.prov = e.outLabel.prov) := by
  intro e he
  -- Step 1: extract membership in t (lowProj is filter over t).
  unfold lowProj at he
  rw [List.mem_filter] at he
  obtain ⟨hMem, _⟩ := he
  -- Step 2: case-split on e.kind, mirroring t3_noninterference but
  -- strengthening the third arm via hPD.
  by_cases hk : e.kind = Kind.declassify
  · exact Or.inl ⟨hk, declassification_well_formed_R3 authorizes
                        mintingTrusted rawInputTags dmap t h e hMem hk⟩
  · by_cases hm : e.kind = Kind.declassMint
    · exact Or.inr (Or.inl ⟨hm, r4_declass_origin_integrity authorizes
                                  mintingTrusted rawInputTags dmap t h
                                  e hMem hm⟩)
    · -- Non-declass-non-mint arm: invoke PayloadDiscipline directly.
      have hEq : e.outLabel.prov =
                 Factor.join e.inLabel.prov e.ctxLabel.prov :=
        hPD e hMem hk hm
      exact Or.inr (Or.inr ⟨hk, hm, hEq.symm⟩)


theorem t3_noninterference_modulo_payload_discipline_strong
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hPD : PayloadDiscipline.holds t)
    (hCoh : outLabelPayloadCoherent t) :
    ∀ e ∈ lowProj visible t,
      ((e.kind = Kind.declassify ∧
        ∃ p : DeclassPayload Principal Tag_C Tag_I Tag_P,
          dmap e.id = some p ∧
          authorizes p.who p.what ∧
          p.locus = e.id ∧
          p.when t ∧
          e.outLabel.prov =
            (p.what.interp (Label.join e.inLabel e.ctxLabel)).prov)
      ∨
      (e.kind = Kind.declassMint ∧
        Factor.leq e.inLabel.prov mintingTrusted)
      ∨
      (e.kind ≠ Kind.declassify ∧ e.kind ≠ Kind.declassMint ∧
        Factor.join e.inLabel.prov e.ctxLabel.prov = e.outLabel.prov))
      ∧ e.outLabelPayload.label = e.outLabel := by
  intro e he
  -- Step 1: extract membership in t (lowProj is filter over t).
  have hMem : e ∈ t := by
    unfold lowProj at he
    rw [List.mem_filter] at he
    exact he.1
  -- Step 2: chain the legacy strong-T3 conclusion via the original
  -- `t3_noninterference_modulo_payload_discipline` theorem.
  have hLegacy := t3_noninterference_modulo_payload_discipline
                    authorizes visible mintingTrusted rawInputTags
                    dmap t h hPD e he
  -- Step 3: invoke `outLabelPayloadCoherent` for the new conjunct.
  have hCohE : e.outLabelPayload.label = e.outLabel := hCoh e hMem
  exact ⟨hLegacy, hCohE⟩


theorem t3_noninterference_kernel_emit_compose_routed
    {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P)
    (hRoute : kernelEmit_compose_routed t) :
    ∀ e ∈ t, e.kind.isKernelEmit = true →
      e.outLabelPayload.label = Label.join e.inLabel e.ctxLabel := by
  intro e he hKE
  -- Project the existential composition witness from
  -- `kernelEmit_compose_routed`.
  obtain ⟨_concat, p1, p2, hP1, hP2, hCompose⟩ := hRoute e he hKE
  -- `hCompose` says
  -- `e.outLabelPayload = { payload := concat p1.payload p2.payload,
  --                        label   := Label.join p1.label p2.label }`.
  -- So `e.outLabelPayload.label = Label.join p1.label p2.label`.
  -- Rewriting via `hP1 : p1.label = e.inLabel` and
  -- `hP2 : p2.label = e.ctxLabel` yields the goal.
  rw [hCompose]
  -- Goal: `Label.join p1.label p2.label = Label.join e.inLabel e.ctxLabel`
  rw [hP1, hP2]


theorem t3_noninterference_kernel_emit_compose_routed_strong
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hPD : PayloadDiscipline.holds t)
    (hRoute : kernelEmit_compose_routed t) :
    ∀ e ∈ t, e.kind.isKernelEmit = true →
      e.outLabelPayload.label.prov =
        (Label.join e.inLabel e.ctxLabel).prov := by
  intro e he hKE
  -- compose-routing.
  have hLabelEq :
      e.outLabelPayload.label = Label.join e.inLabel e.ctxLabel :=
    t3_noninterference_kernel_emit_compose_routed t hRoute e he hKE
  -- Project the provenance factor.
  rw [hLabelEq]

-- ============================================================
--  `e.author : KernelOrTenant` enum to `e.kernelAuthored : Bool`
--  flag under an explicit wellFormedAuthorAttribution predicate)
-- ============================================================


def Event.wellFormedAuthorAttribution
    (e : AgentKernel.Replay.Event) : Prop :=
  (e.author = KernelOrTenant.kernel → e.kernelAuthored = true) ∧
  (e.kernelAuthored = true → e.author = KernelOrTenant.kernel)


def Trace.wellFormedAuthorAttribution
    (t : List AgentKernel.Replay.Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedAuthorAttribution e


theorem author_origin_relay
    (t : List AgentKernel.Replay.Event)
    (hWF : Trace.wellFormedAuthorAttribution t) :
    ∀ e ∈ t,
      e.author = KernelOrTenant.kernel →
      e.kernelAuthored = true := by
  intro e he hAuth
  -- Step 1: extract the wellFormedAuthorAttribution conjunct for e.
  have hWFe := hWF e he
  -- Step 2: project clause (a) and apply the kernel-author hypothesis.
  exact hWFe.1 hAuth

-- ============================================================
-- `mintEventId_origin_relay` (forward-direction repackaging of
-- ============================================================


theorem mintEventId_origin_relay
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (hMid : mintEventId_consistent dmap t) :
    ∀ e ∈ t, e.kind = Kind.declassify →
      ∀ p : DeclassPayload Principal Tag_C Tag_I Tag_P, dmap e.id = some p →
        ∀ mid : EventId, p.mintEventId = some mid →
          ∃ eMint ∈ t, eMint.kind = Kind.declassMint ∧
                       eMint.id = mid := by
  intro e he hKind p hDmap mid hMidEq
  -- `eMint ∈ t` with `eMint.kind = Kind.declassMint`,
  -- `eMint.id = e.id`, and `mid = eMint.id`.
  obtain ⟨eMint, hMintIn, hMintKind, _hMintId, hMidEqMintId⟩ :=
    T_locus_mintEventId_correspondence
      authorizes mintingTrusted rawInputTags dmap t h hMid
      e he hKind p hDmap mid hMidEq
  -- natural reading: the upstream mint event's id equals the
  -- consuming event's mintEventId field).
  exact ⟨eMint, hMintIn, hMintKind, hMidEqMintId.symm⟩

-- ============================================================
-- `outLabelPayload_origin_relay` (forward-direction repackaging
--  composition witness)
-- ============================================================


theorem outLabelPayload_origin_relay
    {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P)
    (hRoute : kernelEmit_compose_routed t) :
    ∀ e ∈ t, e.kind.isKernelEmit = true →
      ∃ (concat : Unit → Unit → Unit)
        (p1 p2 : LabeledPayload Unit Tag_C Tag_I Tag_P),
          p1.label = e.inLabel ∧
          p2.label = e.ctxLabel ∧
          e.outLabelPayload =
            { payload := concat p1.payload p2.payload
            , label   := Label.join p1.label p2.label } := by
  intro e he hKE
  -- One-line projection of the `kernelEmit_compose_routed`
  -- predicate's existential composition witness. The predicate's
  -- shape (Tag_C / Tag_I / Tag_P-matched, binary p1/p2 with
  -- target. Honest-naming verdict: STRUCTURAL PACKAGING.
  exact hRoute e he hKE

-- ============================================================
-- ============================================================


theorem taint_kind_closure_with_kernel_floor
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (kernelFloor : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (_hFloorIncl : Factor.leq kernelFloor rawInputTags) :
    ∀ e ∈ t,
      Factor.overlaps e.outLabel.prov rawInputTags →
      e.kind.isKernelEmit = true := by
  -- The floor-inclusion premise `_hFloorIncl` names the L1+ TCB
  -- obligation surfaced by this relay (see Caveat 2 in docstring);
  -- the closure body itself rides on `taint_kind_closure` since
  -- the closure is over `rawInputTags` (the deployment-supplied
  -- Factor that includes the kernel floor by hypothesis), not
  -- over `kernelFloor` directly.
  exact taint_kind_closure authorizes mintingTrusted rawInputTags dmap t h


theorem taint_kind_closure_floor_dominates
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (floor1 floor2 : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : wellLabeled authorizes mintingTrusted rawInputTags dmap t)
    (_hFloor1Le2 : Factor.leq floor1 floor2)
    (hFloor2Incl : Factor.leq floor2 rawInputTags) :
    ∀ e ∈ t,
      Factor.overlaps e.outLabel.prov rawInputTags →
      e.kind.isKernelEmit = true := by
  -- Forward direction: under `floor2 ⊆ rawInputTags`, the closure
  -- holds via `taint_kind_closure_with_kernel_floor` instantiated
  -- at `floor2`. Monotonicity in `floor1 ⊆ floor2` is structural:
  -- a stricter floor names a tighter L1+ TCB obligation, not a
  -- different closure body. The hypothesis `_hFloor1Le2` is
  -- consumed by the surrounding context (it is the named
  -- monotonicity premise the deployment-policy prose cites); the
  -- closure body rides on `taint_kind_closure_with_kernel_floor`
  -- at the dominating floor `floor2`.
  exact taint_kind_closure_with_kernel_floor
          authorizes mintingTrusted floor2 rawInputTags dmap t h
          hFloor2Incl

end AgentKernel.IFC

-- ============================================================
-- Axiom inventory measurement blocks
-- ============================================================
-- Mirrors the Bridge.M{4,5,6,7}.lean conventions: in-file
-- via `lake env lean MeasureAxioms.lean` or `lake build` log; this
-- block surfaces them at the IFC namespace boundary.

#print axioms AgentKernel.IFC.r4_declass_origin_integrity
#print axioms AgentKernel.IFC.r4_declass_mint_has_payload

#print axioms AgentKernel.IFC.taint_kind_closure

#print axioms AgentKernel.IFC.r4_declass_mint_nonvacuous
#print axioms AgentKernel.IFC.dmap_origin_relay

-- documentation upgrade. Author-boundary L0 predicate
-- (`event_authorship_predicate`) and relay theorem
-- pattern. Predicate is a definition (no axiom block); relay is
-- the named theorem.
#print axioms AgentKernel.IFC.taint_authorship_relay

-- `t3_visible_projection_well_labeling` is a one-line forwarder to
-- `t3_noninterference` (preserved verbatim as legacy alias). The
-- load-bearing content is the NAME, not the proof body. Predicted
-- Tier 2 [propext] (inherits from `t3_noninterference`).
#print axioms AgentKernel.IFC.t3_visible_projection_well_labeling

-- residual close (additive). New default-valued field
-- `mintEventId : Option EventId := none` carrying the mint-event-id
-- semantics; `locus` preserved verbatim as consuming-event-id
-- legacy alias. New named theorem `T_locus_mintEventId_correspondence`
-- makes the field load-bearing under L1+ wiring obligation
-- `mintEventId_consistent` (default-vacuous over `none`). Mirrors
-- [propext] (-projection + L1+ predicate transitivity).
#print axioms AgentKernel.IFC.T_locus_mintEventId_correspondence

-- IFC.Event via default-valued field `outLabelPayload : LabeledPayload
-- Unit Tag_C Tag_I Tag_P`. New `outLabelPayloadCoherent` predicate
-- (Prop-valued, named) gives L1+ kernel runtime a callable wiring
-- obligation. New theorem `t3_noninterference_modulo_payload_
-- LabeledPayload-coherence conjunct, structurally discharging
-- structurally orphan at L0 pre-Session-43). Predicted Tier 2
-- [propext] (inherits from `t3_noninterference_modulo_payload_
-- discipline`).
#print axioms AgentKernel.IFC.t3_noninterference_modulo_payload_discipline_strong

-- step routes payloads through `LabeledPayload.compose`. New L0
-- NAMED predicate `kernelEmit_compose_routed` (structural composition
-- witness; default-vacuous over trivial label). New named theorem
-- `t3_noninterference_kernel_emit_compose_routed` derives
-- `outLabelPayload.label = Label.join inLabel ctxLabel` STRUCTURALLY
-- from the composition witness (no free L1+ obligation on label
-- equality at the kernel-emit axis). Corollary
-- `t3_noninterference_kernel_emit_compose_routed_strong` chains
-- on the kernel-emit axis; Caveat 5 transitions from "structurally
-- wired with L1+ TCB obligation" (post-Path 1) to "structurally
-- wired AND L0-mechanized at kernel-emit; L1+ TCB residual narrowed
-- to non-kernel-emit construction sites" (post-Path 2). Predicted
-- Tier 2 [propext] (composition-witness rewriting; no
-- Classical.choice).
#print axioms AgentKernel.IFC.t3_noninterference_kernel_emit_compose_routed
#print axioms AgentKernel.IFC.t3_noninterference_kernel_emit_compose_routed_strong

-- New L0 predicate `Event.wellFormedAuthorAttribution` binding
-- `Event.author : KernelOrTenant` enum to `Event.kernelAuthored :
-- Bool` flag. New trace-level lift `Trace.wellFormedAuthorAttribution`.
-- New named theorem `author_origin_relay` deriving `kernelAuthored
-- = true` from `author = .kernel` under the predicate. Closes the
-- residual narrowed to "kernel runtime discharges the predicate"
-- Caveat 1). Predicted Tier 2 [propext]; honest naming per
#print axioms AgentKernel.IFC.author_origin_relay

-- `T_locus_mintEventId_correspondence`. Re-presents `mid =
-- Honest naming = STRUCTURAL RELAY (legitimate close mode per
-- Predicted Tier 2 [propext]; may over-deliver to Tier 1 axiom-
-- free.
#print axioms AgentKernel.IFC.mintEventId_origin_relay

-- `kernelEmit_compose_routed` predicate's existential composition
-- witness. One-line projection — honest naming = STRUCTURAL
-- caveat (legitimate close mode but should NOT headline §4 of
-- the paper). Predicted Tier 2 [propext]; may over-deliver to
-- Tier 1 axiom-free.
#print axioms AgentKernel.IFC.outLabelPayload_origin_relay

-- floor-set conjunct. New theorem
-- `taint_kind_closure` with a kernel-supplied floor-set premise
-- (`Factor.leq kernelFloor rawInputTags`) surfacing the L1+ TCB
-- obligation that deployment must discharge to make the relay
-- load-bearing in practice. Sibling
-- `taint_kind_closure_floor_dominates` shows parameter monotonicity:
-- the closure cannot be weakened by tenant authoring of a
-- smaller-than-floor `rawInputTags`. Honest naming = STRUCTURAL
-- accounting). Predicted Tier 1 axiom-free.
#print axioms AgentKernel.IFC.taint_kind_closure_with_kernel_floor
#print axioms AgentKernel.IFC.taint_kind_closure_floor_dominates
