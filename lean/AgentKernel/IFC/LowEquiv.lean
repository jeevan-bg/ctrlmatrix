import AgentKernel.IFC



namespace AgentKernel.IFC.LowEquiv

open AgentKernel.Replay (Kind)

-- ============================================================
-- Scaffolding: lowProj on nil/singleton + lowEquiv reflexivity
-- ============================================================

/-- `lowProj` on the empty trace is empty. -/
theorem lowProj_nil
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P) :
    lowProj visible ([] : Trace Tag_C Tag_I Tag_P) = [] := by
  unfold lowProj
  rfl

/-- `lowProj` on a singleton, visible event: the singleton itself. -/
theorem lowProj_singleton_visible
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (hv : visible e.outLabel = true) :
    lowProj visible [e] = [e] := by
  unfold lowProj
  simp [List.filter, hv]

/-- `lowProj` on a singleton, invisible event: empty. -/
theorem lowProj_singleton_invisible
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (hv : visible e.outLabel = false) :
    lowProj visible [e] = [] := by
  unfold lowProj
  simp [List.filter, hv]

/-- Reflexivity of `lowEquiv`. Tier 1 axiom-free. -/
theorem lowEquiv_refl
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P) :
    lowEquiv visible t t := by
  unfold lowEquiv
  rfl

/-- Symmetry of `lowEquiv`. Tier 1 axiom-free. -/
theorem lowEquiv_symm
    {Tag_C Tag_I Tag_P : Type}
    {visible : Visible Tag_C Tag_I Tag_P}
    {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
    (h : lowEquiv visible t₁ t₂) :
    lowEquiv visible t₂ t₁ := by
  unfold lowEquiv at h ⊢
  exact h.symm

/-- Transitivity of `lowEquiv`. Tier 1 axiom-free. -/
theorem lowEquiv_trans
    {Tag_C Tag_I Tag_P : Type}
    {visible : Visible Tag_C Tag_I Tag_P}
    {t₁ t₂ t₃ : Trace Tag_C Tag_I Tag_P}
    (h₁₂ : lowEquiv visible t₁ t₂)
    (h₂₃ : lowEquiv visible t₂ t₃) :
    lowEquiv visible t₁ t₃ := by
  unfold lowEquiv at h₁₂ h₂₃ ⊢
  exact h₁₂.trans h₂₃

-- ============================================================
-- t3_low_equivalence_empty (degenerate case: both traces empty)
-- ============================================================


theorem t3_low_equivalence_empty
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (_h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap
            ([] : Trace Tag_C Tag_I Tag_P))
    (_h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap
            ([] : Trace Tag_C Tag_I Tag_P)) :
    lowEquiv visible ([] : Trace Tag_C Tag_I Tag_P) [] :=
  lowEquiv_refl visible []

-- ============================================================
-- t3_low_equivalence_minimal (substantive: at most one declassify
-- event per trace, projection-equality threaded as hypothesis)
-- ============================================================


theorem t3_low_equivalence_minimal
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (_h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₁)
    (_h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₂)
    (_h_minimal_t₁ :
        t₁.length ≤ 1 ∧ ∀ e ∈ t₁, e.kind = Kind.declassify)
    (_h_minimal_t₂ :
        t₂.length ≤ 1 ∧ ∀ e ∈ t₂, e.kind = Kind.declassify)
    (h_low_proj_pointwise :
        lowProj visible t₁ = lowProj visible t₂) :
    lowEquiv visible t₁ t₂ := by
  unfold lowEquiv
  exact h_low_proj_pointwise

-- ============================================================
-- t3_low_equivalence_minimal_via_event_equality
-- (substantive: derives lowEquiv from per-event-equality of visible
-- heads, not just from projection-equality of the whole trace)
-- ============================================================


theorem t3_low_equivalence_minimal_via_event_equality
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (_h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₁)
    (_h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₂)
    (h_minimal_t₁ :
        t₁.length ≤ 1 ∧ ∀ e ∈ t₁, e.kind = Kind.declassify)
    (h_minimal_t₂ :
        t₂.length ≤ 1 ∧ ∀ e ∈ t₂, e.kind = Kind.declassify)
    (h_visible_head_eq :
        -- Per-event visibility + event agreement on visible heads.
        --
        -- Encoding: for every (e₁, e₂) instantiation reachable from
        -- the head positions of t₁ and t₂, agreement on visibility
        -- AND on the event itself when visible. The four
        -- (empty/singleton)² combinations give the four arms:
        --   (nil, nil) → trivially satisfied (no e₁/e₂ exist).
        --   (nil, [e₂]) → e₂ must be invisible.
        --   ([e₁], nil) → e₁ must be invisible.
        --   ([e₁], [e₂]) → either both invisible OR both visible
        --                   with e₁ = e₂.
        (∀ e₁, t₁ = [e₁] → t₂ = [] → visible e₁.outLabel = false) ∧
        (∀ e₂, t₂ = [e₂] → t₁ = [] → visible e₂.outLabel = false) ∧
        (∀ e₁ e₂, t₁ = [e₁] → t₂ = [e₂] →
           (visible e₁.outLabel = false ∧ visible e₂.outLabel = false) ∨
           (visible e₁.outLabel = true ∧ visible e₂.outLabel = true ∧
              e₁ = e₂))) :
    lowEquiv visible t₁ t₂ := by
  obtain ⟨h_t₁_len, _⟩ := h_minimal_t₁
  obtain ⟨h_t₂_len, _⟩ := h_minimal_t₂
  obtain ⟨h_nil_t₂, h_nil_t₁, h_both⟩ := h_visible_head_eq
  unfold lowEquiv
  -- Case on t₁: empty, singleton, or impossible.
  match t₁, h_t₁_len with
  | [], _ =>
    -- t₁ = []. Case on t₂.
    match t₂, h_t₂_len with
    | [], _ =>
      -- (nil, nil): trivial.
      rfl
    | [e₂], _ =>
      -- (nil, [e₂]): e₂ invisible by h_nil_t₁.
      have h_inv : visible e₂.outLabel = false := h_nil_t₁ e₂ rfl rfl
      rw [lowProj_nil,
          lowProj_singleton_invisible visible e₂ h_inv]
    | _ :: _ :: _, h_len =>
      -- Length contradiction.
      simp at h_len
  | [e₁], _ =>
    -- t₁ = [e₁]. Case on t₂.
    match t₂, h_t₂_len with
    | [], _ =>
      -- ([e₁], nil): e₁ invisible by h_nil_t₂.
      have h_inv : visible e₁.outLabel = false := h_nil_t₂ e₁ rfl rfl
      rw [lowProj_singleton_invisible visible e₁ h_inv,
          lowProj_nil]
    | [e₂], _ =>
      -- ([e₁], [e₂]): substantive case. Use h_both.
      rcases h_both e₁ e₂ rfl rfl with
        ⟨h_v₁_false, h_v₂_false⟩ | ⟨h_v₁_true, h_v₂_true, h_eq⟩
      · -- Both invisible.
        rw [lowProj_singleton_invisible visible e₁ h_v₁_false,
            lowProj_singleton_invisible visible e₂ h_v₂_false]
      · -- Both visible, events equal.
        rw [lowProj_singleton_visible visible e₁ h_v₁_true,
            lowProj_singleton_visible visible e₂ h_v₂_true,
            h_eq]
    | _ :: _ :: _, h_len =>
      simp at h_len
  | _ :: _ :: _, h_len =>
    simp at h_len

-- ============================================================
-- t3_low_equivalence over arbitrary well-labeled traces
-- ============================================================
--
-- Wave 2 extends Wave 1's minimal (length ≤ 1) result to arbitrary
-- traces in five additive layers, all Tier 2 [propext] predicted:
--
-- Layer A: cons + append decomposition for `lowProj`. Operates on
--          flagged `wellLabeled_cons_iff` design risk (which would
--          require strengthening `wellLabeled` under cons).
-- Layer B: `lowEquiv` compositional rules — invisible-cons absorption
--          (left + right) + visible-match cons-step.
-- Layer C: inductive headline `t3_low_equivalence` taking
--          `lowProj t₁ = lowProj t₂` as hypothesis (acknowledged
--          hypothesis-eq-conclusion form mirroring Wave 1's
--          `t3_low_equivalence_minimal`). Proof body shows the
--          cons-decomposition discipline downstream consumers will
--          plug into.
-- Layer D: NEW inductive predicate `lowAgree` capturing per-event-
--          pairing structure on pairs of traces; soundness theorem
--          `lowAgree_implies_lowEquiv` proved by structural induction
--          on the `lowAgree` derivation; per-event-pairing companion
--          headline `t3_low_equivalence_via_event_pairing`.
--          The structurally-different (and inductively-decomposable)
--          per-event-pairing form mirrors Wave 1's `via_event_equality`
--          shift away from `_minimal`.
-- Layer E: substantive `wellLabeled` consumption for  events —
--          `wellLabeledStep_R3_outLabel_prov_determined`. Closes
--          wellLabeled" gap by SUBSTANTIVELY extracting the 
--          prov-formula conjunct from `wellLabeledStep` and using
--          `dmap` functionality + per-event input agreement to derive
--          `outLabel.prov` agreement across two well-labeled traces.
--
--   (a) full `t3_low_equivalence_via_R3_input_agreement` chaining
--       Layer E with Layer D — needs careful field-level Event
--       equality reasoning to lift `outLabel.prov` agreement to
--       `Event` agreement on visible positions. Out of Wave 2's
--   (b) `lowEquiv_implies_lowAgree` (completeness of `lowAgree` as
--       a structural witness for `lowEquiv`). Wave 2 ships the
--       soundness direction only.
--   (c) `wellLabeled_cons_iff` (Wave 1 risk) — Wave 2 SIDESTEPS by
--       not consuming `wellLabeled` structurally in Layers A/B/C.
--       Layer E consumes `wellLabeled` via `wellLabeledStep` directly
--       (existing per-event lemma), not via cons-decomposition.

-- ============================================================
-- Wave 2 Layer A — lowProj cons + append decomposition
-- ============================================================

/-- `lowProj` on a cons whose head is visible: the head followed by
    the projection of the tail. Tier 2 [propext] via `List.filter`
    elaboration on `cons`. -/
theorem lowProj_cons_visible
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (hv : visible e.outLabel = true) :
    lowProj visible (e :: t) = e :: lowProj visible t := by
  unfold lowProj
  simp [List.filter, hv]

/-- `lowProj` on a cons whose head is invisible: the projection of
    the tail. Tier 2 [propext]. -/
theorem lowProj_cons_invisible
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (e : Event Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (hv : visible e.outLabel = false) :
    lowProj visible (e :: t) = lowProj visible t := by
  unfold lowProj
  simp [List.filter, hv]

/-- `lowProj` distributes over append. Tier 2 [propext] via
    `List.filter_append`. -/
theorem lowProj_append
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P) :
    lowProj visible (t₁ ++ t₂) =
      lowProj visible t₁ ++ lowProj visible t₂ := by
  unfold lowProj
  exact List.filter_append t₁ t₂

-- ============================================================
-- Wave 2 Layer B — lowEquiv compositional rules
-- ============================================================

/-- Cons-absorb an invisible event on the left: if `t₁ ~ t₂` and `e`
    is invisible, then `e :: t₁ ~ t₂`. Tier 2 [propext]. -/
theorem lowEquiv_cons_invisible_left
    {Tag_C Tag_I Tag_P : Type}
    {visible : Visible Tag_C Tag_I Tag_P}
    {e : Event Tag_C Tag_I Tag_P}
    {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
    (hv : visible e.outLabel = false)
    (h : lowEquiv visible t₁ t₂) :
    lowEquiv visible (e :: t₁) t₂ := by
  unfold lowEquiv at h ⊢
  rw [lowProj_cons_invisible visible e t₁ hv]
  exact h

/-- Cons-absorb an invisible event on the right: if `t₁ ~ t₂` and `e`
    is invisible, then `t₁ ~ e :: t₂`. Tier 2 [propext]. -/
theorem lowEquiv_cons_invisible_right
    {Tag_C Tag_I Tag_P : Type}
    {visible : Visible Tag_C Tag_I Tag_P}
    {e : Event Tag_C Tag_I Tag_P}
    {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
    (hv : visible e.outLabel = false)
    (h : lowEquiv visible t₁ t₂) :
    lowEquiv visible t₁ (e :: t₂) := by
  unfold lowEquiv at h ⊢
  rw [lowProj_cons_invisible visible e t₂ hv]
  exact h

/-- Visible-match cons step: if `t₁ ~ t₂` and `e` is visible, then
    `e :: t₁ ~ e :: t₂`. The cons-extended pair shares the visible
    head verbatim. Tier 2 [propext]. -/
theorem lowEquiv_cons_visible_match
    {Tag_C Tag_I Tag_P : Type}
    {visible : Visible Tag_C Tag_I Tag_P}
    {e : Event Tag_C Tag_I Tag_P}
    {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
    (hv : visible e.outLabel = true)
    (h : lowEquiv visible t₁ t₂) :
    lowEquiv visible (e :: t₁) (e :: t₂) := by
  unfold lowEquiv at h ⊢
  rw [lowProj_cons_visible visible e t₁ hv,
      lowProj_cons_visible visible e t₂ hv,
      h]

-- ============================================================
-- Wave 2 Layer C — t3_low_equivalence headline (inductive)
-- ============================================================


theorem t3_low_equivalence
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (_h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₁)
    (_h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₂)
    (h_low_proj : lowProj visible t₁ = lowProj visible t₂) :
    lowEquiv visible t₁ t₂ := by
  unfold lowEquiv
  exact h_low_proj

-- ============================================================
-- Wave 2 Layer D — lowAgree inductive predicate +
--                  per-event-pairing companion theorem
-- ============================================================


inductive lowAgree {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P) :
    Trace Tag_C Tag_I Tag_P → Trace Tag_C Tag_I Tag_P → Prop where
  | nil_nil : lowAgree visible [] []
  | cons_invisible_left
      {e : Event Tag_C Tag_I Tag_P}
      {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
      (hv : visible e.outLabel = false)
      (h : lowAgree visible t₁ t₂) :
      lowAgree visible (e :: t₁) t₂
  | cons_invisible_right
      {e : Event Tag_C Tag_I Tag_P}
      {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
      (hv : visible e.outLabel = false)
      (h : lowAgree visible t₁ t₂) :
      lowAgree visible t₁ (e :: t₂)
  | cons_visible_match
      {e : Event Tag_C Tag_I Tag_P}
      {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
      (hv : visible e.outLabel = true)
      (h : lowAgree visible t₁ t₂) :
      lowAgree visible (e :: t₁) (e :: t₂)


theorem lowAgree_implies_lowEquiv
    {Tag_C Tag_I Tag_P : Type}
    {visible : Visible Tag_C Tag_I Tag_P}
    {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
    (h : lowAgree visible t₁ t₂) :
    lowEquiv visible t₁ t₂ := by
  induction h with
  | nil_nil =>
    exact lowEquiv_refl visible []
  | cons_invisible_left hv _ ih =>
    exact lowEquiv_cons_invisible_left hv ih
  | cons_invisible_right hv _ ih =>
    exact lowEquiv_cons_invisible_right hv ih
  | cons_visible_match hv _ ih =>
    exact lowEquiv_cons_visible_match hv ih


theorem t3_low_equivalence_via_event_pairing
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (_h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₁)
    (_h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₂)
    (h_agree : lowAgree visible t₁ t₂) :
    lowEquiv visible t₁ t₂ :=
  lowAgree_implies_lowEquiv h_agree

-- ============================================================
-- Wave 2 Layer E — substantive wellLabeled consumption for 
-- ============================================================


theorem wellLabeledStep_R3_outLabel_prov_determined
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (e₁ e₂ : Event Tag_C Tag_I Tag_P)
    (he₁_in : e₁ ∈ t₁)
    (he₂_in : e₂ ∈ t₂)
    (h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₁)
    (h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₂)
    (h_e₁_R3 : e₁.kind = Kind.declassify)
    (h_e₂_R3 : e₂.kind = Kind.declassify)
    (h_id_eq : e₁.id = e₂.id)
    (h_inLabel_eq : e₁.inLabel = e₂.inLabel)
    (h_ctxLabel_eq : e₁.ctxLabel = e₂.ctxLabel) :
    e₁.outLabel.prov = e₂.outLabel.prov := by
  -- Extract  6-conjunct from wellLabeledStep on e₁ via h₁.
  have h_step₁ := h₁ e₁ he₁_in
  unfold wellLabeledStep at h_step₁
  have h_inner₁ := h_step₁.2
  rw [if_pos h_e₁_R3] at h_inner₁
  obtain ⟨p₁, hp₁_dmap, _, _, _, hp₁_prov, _⟩ := h_inner₁
  -- Extract  6-conjunct from wellLabeledStep on e₂ via h₂.
  have h_step₂ := h₂ e₂ he₂_in
  unfold wellLabeledStep at h_step₂
  have h_inner₂ := h_step₂.2
  rw [if_pos h_e₂_R3] at h_inner₂
  obtain ⟨p₂, hp₂_dmap, _, _, _, hp₂_prov, _⟩ := h_inner₂
  -- Use e₁.id = e₂.id to align dmap lookups; dmap is a function so
  -- agreement on the key forces agreement on the payload.
  rw [h_id_eq] at hp₁_dmap
  have hp_some_eq : some p₁ = some p₂ := hp₁_dmap.symm.trans hp₂_dmap
  have hp_eq : p₁ = p₂ := Option.some.inj hp_some_eq
  -- Substitute the prov formulas + payload agreement + input
  -- agreement to derive outLabel.prov agreement.
  rw [hp₁_prov, hp₂_prov, hp_eq, h_inLabel_eq, h_ctxLabel_eq]

-- ============================================================
-- Full Sabelfeld-Sands input→output chain
-- ============================================================
--
-- Carry-forward item 2): the end-to-end "well-labeled  input-
-- ultimately wants. Chains Layer E's per-event  prov-determination
-- (`wellLabeledStep_R3_outLabel_prov_determined`) + Layer D's
-- `lowAgree → lowEquiv` soundness (`lowAgree_implies_lowEquiv`).
--
-- v1.2 baseline lines 1-744 are byte-preserved; this section is
-- additive-only at the tail. No edits to IFC.lean (md5 invariant
-- ad4a5da1c850089b9321cb2a80bd93a5). No new `axiom`/`sorry`/
-- `Classical.choice` use.
--
-- DESIGN NOTE — honest naming:
-- The "input agreement" precondition is encoded as an inductive
-- predicate `R3InputAgreement` walking the trace pair structurally
-- (mirroring `lowAgree`'s 4-constructor shape). At visible-match
-- positions the predicate demands per-position agreement on the
-- non-prov-derivable Event fields (id, kind, inLabel, ctxLabel,
-- outLabel.conf, outLabel.integ, author, outLabelPayload) plus -ness
-- on both events plus membership in the source traces — exactly the
-- inputs Layer E needs to derive `outLabel.prov` agreement, after
-- which Event field-extensionality lifts to full Event equality and
-- thence to `lowAgree.cons_visible_match`. The predicate's other
-- three constructors (`nil_nil` / `cons_invisible_left` /
-- `cons_invisible_right`) mirror `lowAgree`'s identically-named
-- constructors and translate trivially.
--
--   (a) The theorem assumes EVERY visible-match position is 
--       arm; per-Kind extensions ( join-leq,  mint-bound) are NOT
--   (b) Multi-policy generalization (two distinct
--       `(mintingTrusted, rawInputTags, dmap)` triples) is the
--   (c) The auxiliary field-agreement bundle (conf, integ, author,
--       outLabelPayload) at visible-match positions is honestly
--       carried as constructor arguments rather than derived from
--       deeper structural invariants. A future strengthening could
--       derive (conf, integ) agreement from a stronger per-Kind
--       outLabel-determination lemma; (author, outLabelPayload) are
--       L0-default-valued fields whose agreement would follow from

-- ============================================================
-- R3InputAgreement — per-event-pairing input-agreement predicate
-- ============================================================


inductive R3InputAgreement {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P) :
    Trace Tag_C Tag_I Tag_P → Trace Tag_C Tag_I Tag_P → Prop where
  | nil_nil : R3InputAgreement visible t₁ t₂ [] []
  | cons_invisible_left
      {e : Event Tag_C Tag_I Tag_P}
      {u₁ u₂ : Trace Tag_C Tag_I Tag_P}
      (hv : visible e.outLabel = false)
      (h : R3InputAgreement visible t₁ t₂ u₁ u₂) :
      R3InputAgreement visible t₁ t₂ (e :: u₁) u₂
  | cons_invisible_right
      {e : Event Tag_C Tag_I Tag_P}
      {u₁ u₂ : Trace Tag_C Tag_I Tag_P}
      (hv : visible e.outLabel = false)
      (h : R3InputAgreement visible t₁ t₂ u₁ u₂) :
      R3InputAgreement visible t₁ t₂ u₁ (e :: u₂)
  | cons_visible_input_match
      {e₁ e₂ : Event Tag_C Tag_I Tag_P}
      {u₁ u₂ : Trace Tag_C Tag_I Tag_P}
      (hv₁ : visible e₁.outLabel = true)
      (hv₂ : visible e₂.outLabel = true)
      (he₁_in : e₁ ∈ t₁)
      (he₂_in : e₂ ∈ t₂)
      (h_e₁_R3 : e₁.kind = Kind.declassify)
      (h_e₂_R3 : e₂.kind = Kind.declassify)
      (h_id : e₁.id = e₂.id)
      (h_kind : e₁.kind = e₂.kind)
      (h_inLabel : e₁.inLabel = e₂.inLabel)
      (h_ctxLabel : e₁.ctxLabel = e₂.ctxLabel)
      (h_conf : e₁.outLabel.conf = e₂.outLabel.conf)
      (h_integ : e₁.outLabel.integ = e₂.outLabel.integ)
      (h_author : e₁.author = e₂.author)
      (h_payload : e₁.outLabelPayload = e₂.outLabelPayload)
      (h : R3InputAgreement visible t₁ t₂ u₁ u₂) :
      R3InputAgreement visible t₁ t₂ (e₁ :: u₁) (e₂ :: u₂)

-- ============================================================
-- r3InputAgreement_implies_lowAgree — the structural upgrade
-- ============================================================


theorem r3InputAgreement_implies_lowAgree
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    {visible : Visible Tag_C Tag_I Tag_P}
    {t₁ t₂ : Trace Tag_C Tag_I Tag_P}
    (h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₁)
    (h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₂)
    {u₁ u₂ : Trace Tag_C Tag_I Tag_P}
    (h_agree : R3InputAgreement visible t₁ t₂ u₁ u₂) :
    lowAgree visible u₁ u₂ := by
  induction h_agree with
  | nil_nil =>
    exact lowAgree.nil_nil
  | cons_invisible_left hv _ ih =>
    exact lowAgree.cons_invisible_left hv ih
  | cons_invisible_right hv _ ih =>
    exact lowAgree.cons_invisible_right hv ih
  | @cons_visible_input_match e₁ e₂ u₁ u₂ hv₁ hv₂ he₁_in he₂_in
      h_e₁_R3 h_e₂_R3 h_id h_kind h_inLabel h_ctxLabel
      h_conf h_integ h_author h_payload _ ih =>
    -- Layer E: derive outLabel.prov agreement from  + input agreement.
    have h_prov : e₁.outLabel.prov = e₂.outLabel.prov :=
      wellLabeledStep_R3_outLabel_prov_determined
        authorizes mintingTrusted rawInputTags dmap
        t₁ t₂ e₁ e₂ he₁_in he₂_in h₁ h₂
        h_e₁_R3 h_e₂_R3 h_id h_inLabel h_ctxLabel
    -- Combine prov agreement with the constructor's other field
    -- agreements (conf, integ) to derive outLabel agreement via
    -- the auto-generated `Label` structure-extensionality lemma.
    have h_outLabel : e₁.outLabel = e₂.outLabel := by
      cases h_e1 : e₁.outLabel
      cases h_e2 : e₂.outLabel
      simp_all
    -- Lift to full Event equality via field-extensionality
    -- (the auto-generated `Event` structure-extensionality lemma).
    have h_event_eq : e₁ = e₂ := by
      cases e₁
      cases e₂
      simp_all
    -- Now lowAgree.cons_visible_match needs e₁ = e₂; rewrite the
    -- right tail's head to be e₁ via h_event_eq.symm so the visible-
    -- match constructor accepts a single shared head.
    rw [← h_event_eq]
    exact lowAgree.cons_visible_match hv₁ ih

-- ============================================================
-- t3_low_equivalence_via_R3_input_agreement — the headline chain
-- ============================================================


theorem t3_low_equivalence_via_R3_input_agreement
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₁)
    (h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₂)
    (h_agree : R3InputAgreement visible t₁ t₂ t₁ t₂) :
    lowEquiv visible t₁ t₂ :=
  lowAgree_implies_lowEquiv
    (r3InputAgreement_implies_lowAgree
      authorizes mintingTrusted rawInputTags dmap h₁ h₂ h_agree)

-- ============================================================
-- Multi-policy generalization at LowEquiv layer
-- ============================================================
--
-- Caveat 2 secondary): the existing `t3_low_equivalence` (and its
-- downstream System.lean lift `t7_inherits_t3_lowEquiv`) pin BOTH
-- traces to a SHARED `(mintingTrusted, rawInputTags, dmap)` policy
-- triple. Multi-tenant deployment claims need to compare two well-
-- labeled traces operating under DIFFERENT tenant policies (each
-- trace well-labeled against its OWN policy triple).
--
-- v1.2 baseline lines 1-744 are byte-preserved;  (lines 744-
-- 997) is also additive-only and byte-preserved. This section
-- () is additive-only at the new tail. No edits to IFC.lean
-- (md5 invariant ad4a5da1c850089b9321cb2a80bd93a5). No new
-- `axiom`/`sorry`/`Classical.choice` use.
--
-- DESIGN NOTE — substantive content vs. structural packaging:
-- The headline `t3_low_equivalence` is structural-packaging: it
-- unfolds `lowEquiv` to `lowProj` equality and discharges directly
-- from the projection-equality hypothesis. The `wellLabeled`
-- hypotheses are underscore-bound (NOT substantively consumed at
-- this layer; consumption happens at Layer E for the input-agreement
-- chain). The multi-policy generalization is therefore structurally
-- "free" at this layer: each `wellLabeled` uses its own policy
-- triple, with NO compatibility constraint between the two triples.
--
--   (a) The `authorizes` parameter (M4 kernel-policy predicate) is
--       SHARED across both sides — both traces operate under the
--       same kernel-authorization predicate. Per-tenant differing
--       `authorizes` is a strictly L1+ concern (per-tenant kernel-
--       policy routing) and out of v1.3 scope.
--   (b) At the headline `t3_low_equivalence_multipolicy` layer the
--       multi-policy generalization is structural-only (the policy
--       triples are underscore-bound). The substantive multi-policy
--       claim — that two traces well-labeled against DIFFERENT
--       policies AND in per-event input-agreement satisfy `lowEquiv`
--       — would need a compatibility constraint at the input-
--       agreement layer because Layer E
--       (`wellLabeledStep_R3_outLabel_prov_determined`) takes a
--       SHARED `dmap` (the dmap-functionality argument requires
--       agreement on the dmap-payload `p`, which differs across
--       different `dmap` parameters). The Layer E lever is therefore
--       NOT lifted to multi-policy in v1.3 ; only the headline
--       `t3_low_equivalence` and its downstream System.lean lift are
--       lifted. A future strengthening would add a per-event-position
--       `dmap`-compatibility constraint (e.g., for every visible-match
--        position, `dmap₁ e.id = dmap₂ e.id`) to extend the chain.
--   (c) `t3_low_equivalence_via_event_pairing` (Layer D) takes
--       underscore-bound `wellLabeled` hypotheses (the substantive
--       consumption is at Layer E, not Layer D), so a multi-policy
--       variant of Layer D is also structurally trivial; we ship one
--       (`t3_low_equivalence_via_event_pairing_multipolicy`) for
--       symmetry with the headline lift but flag it as structural-
--       only.


theorem t3_low_equivalence_multipolicy
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted₁ mintingTrusted₂ : Factor Tag_P)
    (rawInputTags₁ rawInputTags₂ : Factor Tag_P)
    (dmap₁ dmap₂ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (_h₁ : wellLabeled authorizes mintingTrusted₁ rawInputTags₁ dmap₁ t₁)
    (_h₂ : wellLabeled authorizes mintingTrusted₂ rawInputTags₂ dmap₂ t₂)
    (h_low_proj : lowProj visible t₁ = lowProj visible t₂) :
    lowEquiv visible t₁ t₂ := by
  unfold lowEquiv
  exact h_low_proj


theorem t3_low_equivalence_via_event_pairing_multipolicy
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted₁ mintingTrusted₂ : Factor Tag_P)
    (rawInputTags₁ rawInputTags₂ : Factor Tag_P)
    (dmap₁ dmap₂ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (_h₁ : wellLabeled authorizes mintingTrusted₁ rawInputTags₁ dmap₁ t₁)
    (_h₂ : wellLabeled authorizes mintingTrusted₂ rawInputTags₂ dmap₂ t₂)
    (h_agree : lowAgree visible t₁ t₂) :
    lowEquiv visible t₁ t₂ :=
  lowAgree_implies_lowEquiv h_agree

-- ============================================================
-- `lowEquiv → lowAgree` completeness direction
-- ============================================================
--
-- Closes the "extensionally equivalent" docstring claim from Wave 2:
-- pre-this-item, only the soundness direction `lowAgree → lowEquiv`
-- was proved (`lowAgree_implies_lowEquiv`); the completeness direction
-- was honestly DEFERRED in the lowAgree docstring.
--
-- Constructive proof strategy (NO `Classical.choice`):
--   - All-invisible left helper: any trace whose head is invisible
--     can have its head consumed by `cons_invisible_left`.
--   - All-invisible right helper: symmetric for the right trace.
--   - Main theorem: structural induction on `t₁`.
--     * `t₁ = []`: by `lowProj_eq_nil_implies_all_invisible` on `t₂`,
--       all of `t₂` is invisible — peel by repeated
--       `cons_invisible_right`.
--     * `t₁ = e :: t₁'` with `e` invisible: peel via
--       `cons_invisible_left`, recurse on `t₁'`.
--     * `t₁ = e :: t₁'` with `e` visible: induct on `t₂` to find
--       the matching visible head.
--
-- Tier prediction: Tier 2 [propext] for the helpers and the main
-- theorem. NO `Classical.choice`, NO `Quot.sound` beyond what
-- `lowProj` already implies.


theorem lowProj_eq_nil_implies_all_invisible
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h : lowProj visible t = []) :
    ∀ e ∈ t, visible e.outLabel = false := by
  induction t with
  | nil => intro e he; cases he
  | cons e' t' ih =>
    intro e he
    by_cases hv : visible e'.outLabel = true
    · -- visible head: lowProj has e' :: ..., contradicting h = []
      rw [lowProj_cons_visible visible e' t' hv] at h
      exact absurd h (by intro h'; exact List.cons_ne_nil _ _ h')
    · -- invisible head: lowProj reduces to lowProj t', recurse
      have hv' : visible e'.outLabel = false := by
        cases hv_eq : visible e'.outLabel
        · rfl
        · exact absurd hv_eq (by intro h''; exact hv (h''.trans rfl))
      rw [lowProj_cons_invisible visible e' t' hv'] at h
      cases he with
      | head => exact hv'
      | tail _ he' => exact ih h e he'


theorem lowAgree_nil_left_of_all_invisible
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h_all_inv : ∀ e ∈ t, visible e.outLabel = false) :
    lowAgree visible [] t := by
  induction t with
  | nil => exact lowAgree.nil_nil
  | cons e t' ih =>
    have hv : visible e.outLabel = false :=
      h_all_inv e (by exact List.Mem.head _)
    have ih' := ih (fun e' he' => h_all_inv e' (List.Mem.tail _ he'))
    exact lowAgree.cons_invisible_right hv ih'

/-- **lowAgree_nil_right_of_all_invisible** (symmetric companion of
    `lowAgree_nil_left_of_all_invisible`). -/
theorem lowAgree_nil_right_of_all_invisible
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t : Trace Tag_C Tag_I Tag_P)
    (h_all_inv : ∀ e ∈ t, visible e.outLabel = false) :
    lowAgree visible t [] := by
  induction t with
  | nil => exact lowAgree.nil_nil
  | cons e t' ih =>
    have hv : visible e.outLabel = false :=
      h_all_inv e (by exact List.Mem.head _)
    have ih' := ih (fun e' he' => h_all_inv e' (List.Mem.tail _ he'))
    exact lowAgree.cons_invisible_left hv ih'


theorem lowEquiv_implies_lowAgree
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (h : lowEquiv visible t₁ t₂) :
    lowAgree visible t₁ t₂ := by
  induction t₁ generalizing t₂ with
  | nil =>
    -- t₁ = []: lowProj visible [] = [] = lowProj visible t₂.
    unfold lowEquiv at h
    rw [lowProj_nil] at h
    have h_all_inv :=
      lowProj_eq_nil_implies_all_invisible visible t₂ h.symm
    exact lowAgree_nil_left_of_all_invisible visible t₂ h_all_inv
  | cons e t₁' ih =>
    by_cases hv : visible e.outLabel = true
    · -- e is visible: nested structural induction on t₂ to find the
      -- matching visible head, peeling invisible heads via
      -- `cons_invisible_right`. The outer `ih` discharges the
      -- matching-visible-head case (smaller t₁').
      induction t₂ with
      | nil =>
        -- lowProj visible (e :: t₁') = e :: ... ≠ [] = lowProj nil
        unfold lowEquiv at h
        rw [lowProj_cons_visible visible e t₁' hv, lowProj_nil] at h
        exact absurd h (List.cons_ne_nil _ _)
      | cons e' t₂' ih₂ =>
        by_cases hv' : visible e'.outLabel = true
        · -- e' is visible: must equal e.
          unfold lowEquiv at h
          rw [lowProj_cons_visible visible e t₁' hv,
              lowProj_cons_visible visible e' t₂' hv'] at h
          have h_head : e = e' := List.head_eq_of_cons_eq h
          have h_tail :
              lowProj visible t₁' = lowProj visible t₂' :=
            List.tail_eq_of_cons_eq h
          have ih_inner : lowAgree visible t₁' t₂' := ih t₂' h_tail
          rw [h_head]
          exact lowAgree.cons_visible_match hv' ih_inner
        · -- e' is invisible: peel e' via `cons_invisible_right`.
          have hv'_false : visible e'.outLabel = false := by
            cases hv_eq : visible e'.outLabel
            · rfl
            · exact absurd hv_eq (fun h'' => hv' (h''.trans rfl))
          have h_recur : lowEquiv visible (e :: t₁') t₂' := by
            unfold lowEquiv at h ⊢
            rw [lowProj_cons_invisible visible e' t₂' hv'_false] at h
            exact h
          have ih_outer : lowAgree visible (e :: t₁') t₂' :=
            ih₂ h_recur
          exact lowAgree.cons_invisible_right hv'_false ih_outer
    · -- e is invisible: peel e via `cons_invisible_left`.
      have hv' : visible e.outLabel = false := by
        cases hv_eq : visible e.outLabel
        · rfl
        · exact absurd hv_eq (fun h'' => hv (h''.trans rfl))
      have h_proj : lowProj visible t₁' = lowProj visible t₂ := by
        unfold lowEquiv at h
        rw [lowProj_cons_invisible visible e t₁' hv'] at h
        exact h
      exact lowAgree.cons_invisible_left hv' (ih t₂ h_proj)

-- ============================================================
-- t3_low_equivalence_from_lowInputs
-- (per-position-quantified entry point)
-- ============================================================
--
-- : a per-position-quantified entry point to the
-- Sabelfeld-Sands input→output chain, complementing the existing
-- (which takes the inductive `R3InputAgreement` 4-constructor
-- bundle as a precondition).
--
-- v1.4-stable lines 1-1326 are byte-preserved up to this additive
-- boundary. NO new `axiom`/`sorry`/`Classical.choice`. NO edits to
-- IFC.lean (md5 invariant ad4a5da1c850089b9321cb2a80bd93a5
-- byte-preserved through v1.0..v1.5).
--
-- DESIGN — H1 (Definition):
-- Per-position-quantified shape (a) "positional with length
-- equality" chosen over (b) "relational" — (b) is already
-- Shape (a) is closest to the Sabelfeld-Sands textbook framing
-- (`∀ position i, low-input agreement at i`).
--
-- The hypothesis `h_pos` at each position i ∈ [0, length):
--   (1) Visibility status agrees on both sides at position i;
--   (2) If position i is visible, the per-position field bundle
--       agrees: -ness on both, plus equality on
--       (id, kind, inLabel, ctxLabel, outLabel.conf,
--        outLabel.integ, author, outLabelPayload).
-- These are exactly the 8 input conjuncts that
-- after Layer E (`wellLabeledStep_R3_outLabel_prov_determined`)
-- supplies prov-equality from those inputs + `wellLabeled`,
-- Event field-extensionality lifts the bundle to full Event
-- equality and the chain proceeds via
-- `t3_low_equivalence_via_R3_input_agreement`.
--
-- §  ):
--
--      bookkeeping for `R3InputAgreement.cons_visible_input_match`
--      repeatedly applied? Honest answer: YES at the structural
--      level — the auxiliary `r3InputAgreement_from_lowInputs_aux`
--      walks the trace pair in parallel and constructs the inductive
--      derivation step-by-step from the per-position quantification.
--      legitimate close mode (STRUCTURAL PACKAGING at the
--      lever-shape layer): the substantive value is the
--      complementary entry-point shape (per-position quantification
--      vs inductive bundle), not new mathematical content beyond
--      naming demotion accounting; the headline-eligible content
--
--      (a) positional with length-equality side condition is chosen
--      explicitly (encoded as `h_len : t₁.length = t₂.length` plus
--      a `∀ i : Nat, i < length → ...` quantifier). Shape (b)
--      `t3_low_equivalence_via_event_pairing` and is NOT this
--      theorem.
--
--      constructs `t₁` and `t₂` differing in visible-event count
--      (e.g., `t₁` has an extra invisible event mid-trace). Defense:
--      (i) `h_len` forces the trace LENGTHS to match position-wise;
--      (ii) the per-position visibility-equality conjunct (clause
--      (1)) forces the visibility STATUS to match position-wise.
--      Together these foreclose the visibility-mismatch shape at
--      the hypothesis layer: visible/invisible events MUST line up
--      at the same indices. (A trace pair with different visible-
--      event counts but matching-length total counts cannot satisfy
--      the per-position visibility-equality clause.)
--
--   (a) -only: visible-match positions must both be
--       `Kind.declassify` (the Layer E lever is -specific).
--       Per-Kind extensions ( join-leq,  mint-bound) are
--       same-shape-different-Kind generalizations.
--   (b) Single-policy: both traces share `(authorizes,
--       mintingTrusted, rawInputTags, dmap)` (same restriction as
--       layer would require per-position dmap-compatibility per
--   (c) Length-equality precondition: stricter than the inductive
--       bundle shape (which permits invisible interleaving via
--       `cons_invisible_left/right` independently on each side).
--       The per-position-quantified shape is therefore strictly
--       LESS GENERAL than `R3InputAgreement` at the input-shape
--       layer; the trade-off is textbook-shape ergonomics for
--       callers who already have aligned trace pairs.
--       isolation: Kind is the only shared M3↔M4 type). Cross-
--       predicate `Event.wellFormedTenantBinding` (Replay.lean
--       L837-846) plus the v1.6+ SystemEvent.tenant threading
--       joint convergent claim. At v1.5 L0, the two axes are
--       equivalence). Paper §3-4 prose at P10 must NOT claim
--       joint convergent closure pending v1.6 substrate path.
--
-- Tier prediction: Tier 2 [propext] (consumes the Tier 2 chain
-- `r3InputAgreement_implies_lowAgree` + `lowAgree_implies_lowEquiv`).
-- NO `Classical.choice` (visibility is `Bool`-valued so `by_cases`
-- is decidable; cons-decomposition is structural).


theorem r3InputAgreement_from_lowInputs_aux
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P) :
    ∀ (u₁ u₂ : Trace Tag_C Tag_I Tag_P),
      (∀ e ∈ u₁, e ∈ t₁) →
      (∀ e ∈ u₂, e ∈ t₂) →
      u₁.length = u₂.length →
      (∀ i : Nat, (h_lt₁ : i < u₁.length) → (h_lt₂ : i < u₂.length) →
        visible (u₁.get ⟨i, h_lt₁⟩).outLabel =
            visible (u₂.get ⟨i, h_lt₂⟩).outLabel ∧
        (visible (u₁.get ⟨i, h_lt₁⟩).outLabel = true →
          (u₁.get ⟨i, h_lt₁⟩).kind = Kind.declassify ∧
          (u₂.get ⟨i, h_lt₂⟩).kind = Kind.declassify ∧
          (u₁.get ⟨i, h_lt₁⟩).id = (u₂.get ⟨i, h_lt₂⟩).id ∧
          (u₁.get ⟨i, h_lt₁⟩).inLabel = (u₂.get ⟨i, h_lt₂⟩).inLabel ∧
          (u₁.get ⟨i, h_lt₁⟩).ctxLabel = (u₂.get ⟨i, h_lt₂⟩).ctxLabel ∧
          (u₁.get ⟨i, h_lt₁⟩).outLabel.conf =
              (u₂.get ⟨i, h_lt₂⟩).outLabel.conf ∧
          (u₁.get ⟨i, h_lt₁⟩).outLabel.integ =
              (u₂.get ⟨i, h_lt₂⟩).outLabel.integ ∧
          (u₁.get ⟨i, h_lt₁⟩).author = (u₂.get ⟨i, h_lt₂⟩).author ∧
          (u₁.get ⟨i, h_lt₁⟩).outLabelPayload =
              (u₂.get ⟨i, h_lt₂⟩).outLabelPayload)) →
      R3InputAgreement visible t₁ t₂ u₁ u₂ := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ _ _ h_len _
    cases u₂ with
    | nil => exact R3InputAgreement.nil_nil
    | cons _ _ => exact Nat.noConfusion h_len
  | cons e₁ u₁' ih =>
    intro u₂ h_sub₁ h_sub₂ h_len h_pos
    cases u₂ with
    | nil => exact Nat.noConfusion h_len
    | cons e₂ u₂' =>
      have h_len' : u₁'.length = u₂'.length := Nat.succ.inj h_len
      have h_sub₁' : ∀ e ∈ u₁', e ∈ t₁ := fun e he =>
        h_sub₁ e (List.Mem.tail _ he)
      have h_sub₂' : ∀ e ∈ u₂', e ∈ t₂ := fun e he =>
        h_sub₂ e (List.Mem.tail _ he)
      have h_pos' :
          ∀ i : Nat, (h_lt₁ : i < u₁'.length) → (h_lt₂ : i < u₂'.length) →
            visible (u₁'.get ⟨i, h_lt₁⟩).outLabel =
                visible (u₂'.get ⟨i, h_lt₂⟩).outLabel ∧
            (visible (u₁'.get ⟨i, h_lt₁⟩).outLabel = true →
              (u₁'.get ⟨i, h_lt₁⟩).kind = Kind.declassify ∧
              (u₂'.get ⟨i, h_lt₂⟩).kind = Kind.declassify ∧
              (u₁'.get ⟨i, h_lt₁⟩).id = (u₂'.get ⟨i, h_lt₂⟩).id ∧
              (u₁'.get ⟨i, h_lt₁⟩).inLabel = (u₂'.get ⟨i, h_lt₂⟩).inLabel ∧
              (u₁'.get ⟨i, h_lt₁⟩).ctxLabel =
                  (u₂'.get ⟨i, h_lt₂⟩).ctxLabel ∧
              (u₁'.get ⟨i, h_lt₁⟩).outLabel.conf =
                  (u₂'.get ⟨i, h_lt₂⟩).outLabel.conf ∧
              (u₁'.get ⟨i, h_lt₁⟩).outLabel.integ =
                  (u₂'.get ⟨i, h_lt₂⟩).outLabel.integ ∧
              (u₁'.get ⟨i, h_lt₁⟩).author = (u₂'.get ⟨i, h_lt₂⟩).author ∧
              (u₁'.get ⟨i, h_lt₁⟩).outLabelPayload =
                  (u₂'.get ⟨i, h_lt₂⟩).outLabelPayload) := by
        intro i hi₁ hi₂
        have h_lt_succ₁ : i + 1 < (e₁ :: u₁').length :=
          Nat.succ_lt_succ hi₁
        have h_lt_succ₂ : i + 1 < (e₂ :: u₂').length :=
          Nat.succ_lt_succ hi₂
        exact h_pos (i + 1) h_lt_succ₁ h_lt_succ₂
      have ih' := ih u₂' h_sub₁' h_sub₂' h_len' h_pos'
      have h_lt₁_zero : 0 < (e₁ :: u₁').length := Nat.succ_pos _
      have h_lt₂_zero : 0 < (e₂ :: u₂').length := Nat.succ_pos _
      have h0 := h_pos 0 h_lt₁_zero h_lt₂_zero
      by_cases hv : visible e₁.outLabel = true
      · -- Visible-match position: derive the 8 conjuncts and call
        -- `cons_visible_input_match`.
        have hv₂ : visible e₂.outLabel = true := h0.1 ▸ hv
        obtain ⟨h_e1R3, h_e2R3, h_id, h_inLabel, h_ctxLabel,
                 h_conf, h_integ, h_author, h_payload⟩ := h0.2 hv
        have h_kind : e₁.kind = e₂.kind := h_e1R3.trans h_e2R3.symm
        have he₁_in : e₁ ∈ t₁ := h_sub₁ e₁ (List.Mem.head _)
        have he₂_in : e₂ ∈ t₂ := h_sub₂ e₂ (List.Mem.head _)
        exact R3InputAgreement.cons_visible_input_match
          hv hv₂ he₁_in he₂_in h_e1R3 h_e2R3
          h_id h_kind h_inLabel h_ctxLabel
          h_conf h_integ h_author h_payload ih'
      · -- Invisible-invisible position: skip both via
        -- `cons_invisible_left` ∘ `cons_invisible_right` in
        -- lock-step (the visibility-equality clause forces both
        -- heads invisible; the length-equality prevents the
        -- visibility-mismatch shape).
        have hv_f : visible e₁.outLabel = false := by
          cases hv_eq : visible e₁.outLabel
          · rfl
          · exact absurd hv_eq hv
        have hv₂_f : visible e₂.outLabel = false := h0.1 ▸ hv_f
        exact R3InputAgreement.cons_invisible_left hv_f
                (R3InputAgreement.cons_invisible_right hv₂_f ih')


theorem t3_low_equivalence_from_lowInputs
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted : Factor Tag_P)
    (rawInputTags : Factor Tag_P)
    (dmap : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (h₁ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₁)
    (h₂ : wellLabeled authorizes mintingTrusted rawInputTags dmap t₂)
    (h_len : t₁.length = t₂.length)
    (h_pos : ∀ i : Nat, (h_lt₁ : i < t₁.length) → (h_lt₂ : i < t₂.length) →
      visible (t₁.get ⟨i, h_lt₁⟩).outLabel =
          visible (t₂.get ⟨i, h_lt₂⟩).outLabel ∧
      (visible (t₁.get ⟨i, h_lt₁⟩).outLabel = true →
        (t₁.get ⟨i, h_lt₁⟩).kind = Kind.declassify ∧
        (t₂.get ⟨i, h_lt₂⟩).kind = Kind.declassify ∧
        (t₁.get ⟨i, h_lt₁⟩).id = (t₂.get ⟨i, h_lt₂⟩).id ∧
        (t₁.get ⟨i, h_lt₁⟩).inLabel = (t₂.get ⟨i, h_lt₂⟩).inLabel ∧
        (t₁.get ⟨i, h_lt₁⟩).ctxLabel = (t₂.get ⟨i, h_lt₂⟩).ctxLabel ∧
        (t₁.get ⟨i, h_lt₁⟩).outLabel.conf =
            (t₂.get ⟨i, h_lt₂⟩).outLabel.conf ∧
        (t₁.get ⟨i, h_lt₁⟩).outLabel.integ =
            (t₂.get ⟨i, h_lt₂⟩).outLabel.integ ∧
        (t₁.get ⟨i, h_lt₁⟩).author = (t₂.get ⟨i, h_lt₂⟩).author ∧
        (t₁.get ⟨i, h_lt₁⟩).outLabelPayload =
            (t₂.get ⟨i, h_lt₂⟩).outLabelPayload)) :
    lowEquiv visible t₁ t₂ :=
  t3_low_equivalence_via_R3_input_agreement
    authorizes visible mintingTrusted rawInputTags dmap t₁ t₂ h₁ h₂
    (r3InputAgreement_from_lowInputs_aux visible t₁ t₂ t₁ t₂
      (fun _ h => h) (fun _ h => h) h_len h_pos)

-- ============================================================
-- multi-policy): per-event dmap-compatibility + substantive
-- multi-policy lift of Layer E and the input-agreement chain
-- ============================================================
--
-- honest-residual block (b) at LowEquiv.lean:1028–1043 in the
--
-- The v1.3  multi-policy lift at the HEADLINE layer
-- (`t3_low_equivalence_multipolicy` at LowEquiv.lean:1052+) is
-- structural-only (the policy triples are underscore-bound; the
-- `wellLabeled` hypotheses are NOT substantively consumed). The
-- substantive multi-policy claim requires the dmap-compatibility
-- constraint because Layer E's dmap-functionality argument needs
-- agreement on the dmap-payload across the two traces' separate
-- `dmap` parameters at each visible-match  position.
--
-- This section adds:
--   - 1 NEW predicate `dmapCompatibleAt` (per-event compatibility
--     constraint).
--   - 1 NEW substantive Layer E multi-policy lift theorem.
--   - 1 NEW substantive input-agreement chain multi-policy lift
--     theorem (predicate-quantified compatibility).
--   - 1 NEW substantive per-position entry-point multi-policy lift
--     theorem (composes the chain lift with the existing single-
--     policy auxiliary `r3InputAgreement_from_lowInputs_aux`, which
--     is policy-free — visibility + per-position field bundle only).
--
-- Tier prediction: Tier 2 [propext] for all three theorems (mirrors
-- of the v1.3  single-policy proofs at LowEquiv.lean:698–736,
-- 882–929, 1608–1640 modulo the dmap-compatibility substitution).


def dmapCompatibleAt
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (dmap₁ dmap₂ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (e₁ e₂ : Event Tag_C Tag_I Tag_P) : Prop :=
  e₁.kind = Kind.declassify →
  e₂.kind = Kind.declassify →
  e₁.id = e₂.id →
  dmap₁ e₁.id = dmap₂ e₂.id


theorem wellLabeledStep_R3_outLabel_prov_determined_multipolicy
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (mintingTrusted₁ rawInputTags₁ : Factor Tag_P)
    (dmap₁ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (mintingTrusted₂ rawInputTags₂ : Factor Tag_P)
    (dmap₂ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (e₁ e₂ : Event Tag_C Tag_I Tag_P)
    (he₁_in : e₁ ∈ t₁)
    (he₂_in : e₂ ∈ t₂)
    (h₁ : wellLabeled authorizes mintingTrusted₁ rawInputTags₁ dmap₁ t₁)
    (h₂ : wellLabeled authorizes mintingTrusted₂ rawInputTags₂ dmap₂ t₂)
    (h_e₁_R3 : e₁.kind = Kind.declassify)
    (h_e₂_R3 : e₂.kind = Kind.declassify)
    (h_id_eq : e₁.id = e₂.id)
    (h_inLabel_eq : e₁.inLabel = e₂.inLabel)
    (h_ctxLabel_eq : e₁.ctxLabel = e₂.ctxLabel)
    (h_dmap_compat : dmapCompatibleAt dmap₁ dmap₂ e₁ e₂) :
    e₁.outLabel.prov = e₂.outLabel.prov := by
  -- Extract  6-conjunct from wellLabeledStep on e₁ via h₁.
  have h_step₁ := h₁ e₁ he₁_in
  unfold wellLabeledStep at h_step₁
  have h_inner₁ := h_step₁.2
  rw [if_pos h_e₁_R3] at h_inner₁
  obtain ⟨p₁, hp₁_dmap, _, _, _, hp₁_prov, _⟩ := h_inner₁
  -- Extract  6-conjunct from wellLabeledStep on e₂ via h₂.
  have h_step₂ := h₂ e₂ he₂_in
  unfold wellLabeledStep at h_step₂
  have h_inner₂ := h_step₂.2
  rw [if_pos h_e₂_R3] at h_inner₂
  obtain ⟨p₂, hp₂_dmap, _, _, _, hp₂_prov, _⟩ := h_inner₂
  -- Multi-policy substitute for v1.3 single-policy step
  --   `rw [h_id_eq] at hp₁_dmap;
  --    have hp_some_eq := hp₁_dmap.symm.trans hp₂_dmap`
  -- Now `dmap₁` and `dmap₂` are distinct, so the SHARED-dmap chain
  -- breaks. Use the per-event compatibility constraint:
  --   hp₁_dmap : dmap₁ e₁.id = some p₁
  --   hp₂_dmap : dmap₂ e₂.id = some p₂
  --   h_dmap_compat : dmap₁ e₁.id = dmap₂ e₂.id
  -- → some p₁ = some p₂ by transitivity.
  have h_compat := h_dmap_compat h_e₁_R3 h_e₂_R3 h_id_eq
  have hp_some_eq : some p₁ = some p₂ := hp₁_dmap.symm.trans (h_compat.trans hp₂_dmap)
  have hp_eq : p₁ = p₂ := Option.some.inj hp_some_eq
  -- Substitute the prov formulas + payload agreement + input
  -- agreement to derive outLabel.prov agreement (identical to
  -- the v1.3 single-policy tail).
  rw [hp₁_prov, hp₂_prov, hp_eq, h_inLabel_eq, h_ctxLabel_eq]


theorem t3_low_equivalence_via_R3_input_agreement_multipolicy
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted₁ rawInputTags₁ : Factor Tag_P)
    (dmap₁ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (mintingTrusted₂ rawInputTags₂ : Factor Tag_P)
    (dmap₂ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (h₁ : wellLabeled authorizes mintingTrusted₁ rawInputTags₁ dmap₁ t₁)
    (h₂ : wellLabeled authorizes mintingTrusted₂ rawInputTags₂ dmap₂ t₂)
    (h_dmap_compat_pairwise :
      ∀ (e₁ e₂ : Event Tag_C Tag_I Tag_P),
        e₁ ∈ t₁ → e₂ ∈ t₂ → dmapCompatibleAt dmap₁ dmap₂ e₁ e₂)
    (h_R3IA : R3InputAgreement visible t₁ t₂ t₁ t₂) :
    lowEquiv visible t₁ t₂ := by
  -- Multi-policy mirror of `r3InputAgreement_implies_lowAgree`.
  -- The induction shape is identical to the single-policy proof at
  -- LowEquiv.lean:895–929; only the Layer E call at the visible-
  -- match case differs (substantive multi-policy variant + per-
  -- event-pair dmap-compatibility).
  --
  -- Generalization-by-helper: prove the indexed version over
  -- arbitrary `(u₁, u₂)`, then specialize to `(t₁, t₂)`. The
  -- `R3InputAgreement` parameters `t₁ t₂` are FIXED (the source
  -- traces, with the wellLabeled hypotheses + the per-pair compat
  -- quantified over their membership); the INDICES `u₁ u₂` vary
  -- under the induction. The constructor's `he₁_in : e₁ ∈ t₁` /
  -- `he₂_in : e₂ ∈ t₂` premises feed the multi-policy Layer E call
  -- with membership in the FIXED parameter traces.
  have aux :
      ∀ (u₁ u₂ : Trace Tag_C Tag_I Tag_P),
        R3InputAgreement visible t₁ t₂ u₁ u₂ → lowAgree visible u₁ u₂ := by
    intro u₁ u₂ h_agree
    induction h_agree with
    | nil_nil =>
      exact lowAgree.nil_nil
    | cons_invisible_left hv _ ih =>
      exact lowAgree.cons_invisible_left hv ih
    | cons_invisible_right hv _ ih =>
      exact lowAgree.cons_invisible_right hv ih
    | @cons_visible_input_match e₁ e₂ u₁ u₂ hv₁ hv₂ he₁_in he₂_in
        h_e₁_R3 h_e₂_R3 h_id h_kind h_inLabel h_ctxLabel
        h_conf h_integ h_author h_payload _ ih =>
      -- Multi-policy Layer E: derive outLabel.prov agreement from 
      -- + input agreement + per-event dmap-compatibility.
      have h_compat := h_dmap_compat_pairwise e₁ e₂ he₁_in he₂_in
      have h_prov : e₁.outLabel.prov = e₂.outLabel.prov :=
        wellLabeledStep_R3_outLabel_prov_determined_multipolicy
          authorizes mintingTrusted₁ rawInputTags₁ dmap₁
          mintingTrusted₂ rawInputTags₂ dmap₂
          t₁ t₂ e₁ e₂ he₁_in he₂_in h₁ h₂
          h_e₁_R3 h_e₂_R3 h_id h_inLabel h_ctxLabel h_compat
      -- Combine prov agreement with constructor's other field
      -- agreements (conf, integ) to derive outLabel agreement via
      -- the auto-generated `Label` structure-extensionality lemma.
      -- Identical to the single-policy chain tail.
      have h_outLabel : e₁.outLabel = e₂.outLabel := by
        cases h_e1 : e₁.outLabel
        cases h_e2 : e₂.outLabel
        simp_all
      have h_event_eq : e₁ = e₂ := by
        cases e₁
        cases e₂
        simp_all
      rw [← h_event_eq]
      exact lowAgree.cons_visible_match hv₁ ih
  exact lowAgree_implies_lowEquiv (aux t₁ t₂ h_R3IA)


theorem t3_low_equivalence_from_lowInputs_multipolicy
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (authorizes : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (visible : Visible Tag_C Tag_I Tag_P)
    (mintingTrusted₁ rawInputTags₁ : Factor Tag_P)
    (dmap₁ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (mintingTrusted₂ rawInputTags₂ : Factor Tag_P)
    (dmap₂ : DeclassMap Principal Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (h₁ : wellLabeled authorizes mintingTrusted₁ rawInputTags₁ dmap₁ t₁)
    (h₂ : wellLabeled authorizes mintingTrusted₂ rawInputTags₂ dmap₂ t₂)
    (h_dmap_compat_pairwise :
      ∀ (e₁ e₂ : Event Tag_C Tag_I Tag_P),
        e₁ ∈ t₁ → e₂ ∈ t₂ → dmapCompatibleAt dmap₁ dmap₂ e₁ e₂)
    (h_len : t₁.length = t₂.length)
    (h_pos : ∀ i : Nat, (h_lt₁ : i < t₁.length) → (h_lt₂ : i < t₂.length) →
      visible (t₁.get ⟨i, h_lt₁⟩).outLabel =
          visible (t₂.get ⟨i, h_lt₂⟩).outLabel ∧
      (visible (t₁.get ⟨i, h_lt₁⟩).outLabel = true →
        (t₁.get ⟨i, h_lt₁⟩).kind = Kind.declassify ∧
        (t₂.get ⟨i, h_lt₂⟩).kind = Kind.declassify ∧
        (t₁.get ⟨i, h_lt₁⟩).id = (t₂.get ⟨i, h_lt₂⟩).id ∧
        (t₁.get ⟨i, h_lt₁⟩).inLabel = (t₂.get ⟨i, h_lt₂⟩).inLabel ∧
        (t₁.get ⟨i, h_lt₁⟩).ctxLabel = (t₂.get ⟨i, h_lt₂⟩).ctxLabel ∧
        (t₁.get ⟨i, h_lt₁⟩).outLabel.conf =
            (t₂.get ⟨i, h_lt₂⟩).outLabel.conf ∧
        (t₁.get ⟨i, h_lt₁⟩).outLabel.integ =
            (t₂.get ⟨i, h_lt₂⟩).outLabel.integ ∧
        (t₁.get ⟨i, h_lt₁⟩).author = (t₂.get ⟨i, h_lt₂⟩).author ∧
        (t₁.get ⟨i, h_lt₁⟩).outLabelPayload =
            (t₂.get ⟨i, h_lt₂⟩).outLabelPayload)) :
    lowEquiv visible t₁ t₂ :=
  t3_low_equivalence_via_R3_input_agreement_multipolicy
    authorizes visible
    mintingTrusted₁ rawInputTags₁ dmap₁
    mintingTrusted₂ rawInputTags₂ dmap₂
    t₁ t₂ h₁ h₂ h_dmap_compat_pairwise
    (r3InputAgreement_from_lowInputs_aux visible t₁ t₂ t₁ t₂
      (fun _ h => h) (fun _ h => h) h_len h_pos)

-- ============================================================
-- discipline rule (a)+(b) HOLD)
-- ============================================================



/-- **`IFC.Trace.disjointEventIds`** — IFC-event-typed mirror of
    `AgentKernel.MultiCell.Trace.disjointEventIds`.

    Propositional predicate asserting that two IFC traces share
    NO event id. The precondition that must hold before
    `IFC.Trace.union` may be invoked.

    Definition: for every `e₁ ∈ t₁` and `e₂ ∈ t₂`, `e₁.id ≠
    e₂.id`. Tier 1 (axiom-free) — pure structural conjunction
    over universals on finite lists. -/
def Trace.disjointEventIds
    {Tag_C Tag_I Tag_P : Type}
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P) : Prop :=
  ∀ e₁ ∈ t₁, ∀ e₂ ∈ t₂, e₁.id ≠ e₂.id


def Trace.union
    {Tag_C Tag_I Tag_P : Type}
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (_h : Trace.disjointEventIds t₁ t₂) : Trace Tag_C Tag_I Tag_P :=
  t₁ ++ t₂


theorem lowProj_traceUnion
    {Tag_C Tag_I Tag_P : Type}
    (visible : Visible Tag_C Tag_I Tag_P)
    (t₁ t₂ : Trace Tag_C Tag_I Tag_P)
    (h : Trace.disjointEventIds t₁ t₂) :
    lowProj visible (Trace.union t₁ t₂ h) =
      lowProj visible t₁ ++ lowProj visible t₂ := by
  unfold Trace.union
  exact lowProj_append visible t₁ t₂


theorem t_multi_agent_noninterference
    {Tag_C Tag_I Tag_P : Type}
    {visible : Visible Tag_C Tag_I Tag_P}
    {t_A t_A' t_B : Trace Tag_C Tag_I Tag_P}
    (h_AA' : lowEquiv visible t_A t_A')
    (h_AB  : Trace.disjointEventIds t_A  t_B)
    (h_A'B : Trace.disjointEventIds t_A' t_B) :
    lowEquiv visible (Trace.union t_A  t_B h_AB)
                     (Trace.union t_A' t_B h_A'B) := by
  -- Step 1: unfold `lowEquiv` on the hypothesis to projection equality.
  unfold lowEquiv at h_AA'
  -- Step 2: distribute `lowProj` over both unions via `lowProj_traceUnion`.
  unfold lowEquiv
  rw [lowProj_traceUnion visible t_A  t_B h_AB,
      lowProj_traceUnion visible t_A' t_B h_A'B]
  -- Step 3: cell-A contributions agree by hypothesis; cell-B side is identical.
  rw [h_AA']

end AgentKernel.IFC.LowEquiv
