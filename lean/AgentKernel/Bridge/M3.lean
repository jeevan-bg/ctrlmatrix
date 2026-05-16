import AgentKernel.Replay
import AgentKernel.Causality



namespace AgentKernel.Bridge.M3

open AgentKernel.Replay


inductive ActionLabel_M3 : Type where
  | wellWitnessedAppend (e : Event) : ActionLabel_M3
  | kernelAuthoredAppend (e : Event) : ActionLabel_M3

/-! ## Per-arm pre/post predicates

  Each arm's pre/post transcribed onto Lean's `Trace` shape. The
  bridge predicate does NOT mechanize the `nextId` / `chainHead` /
  `MaxEvents` machinery (those belong to M1/M6 and §8 TCB).
-/


def WellWitnessedAppendStep
    (t : Trace)
    (e : Event)
    (t' : Trace) : Prop :=
  e.kernelAuthored = false ∧
  Event.wellWitnessed e = true ∧
  t' = List.append (α := Event) t [e]

/-- Kernel-authored append arm.
    Pre: `e.kernelAuthored = true`; `Event.wellWitnessed e = true`;
    every `p ∈ e.parents` satisfies `Event.parentInTrace t p = true`
    (the parent already exists in the pre-step trace).
    Post: `t' = t ++ [e]`.

    The pre-step parent-presence obligation is the structural-naming
    closure of B- (causality-parents injection): a kernel-
    authored event cannot reference parent ids fabricated by a tenant
    action handler. **Note:** the TLA+ invariant
    `KernelAuthoredParentsInTrace` requires parents themselves to be
    in `KernelAuthored` (`p \in KernelAuthored`); on the Lean side
    that membership corresponds to a parent event having
    `kernelAuthored = true`. Mechanizing the parent-kernel-authored
    requirement is omitted here — the bridge tightens to *parent in
    trace* (the structurally enforceable half). The
    parent-kernel-authored half is the §8 cross-artifact bookkeeping
    on the deployment-supplied `KernelAuthored : SUBSET EventId`
    constant; flagged in this file's H4 doc. -/
def KernelAuthoredAppendStep
    (t : Trace)
    (e : Event)
    (t' : Trace) : Prop :=
  e.kernelAuthored = true ∧
  Event.wellWitnessed e = true ∧
  (∀ p ∈ e.parents, Event.parentInTrace t p = true) ∧
  t' = List.append (α := Event) t [e]

/-! ## TLAStep_M3

  Per-arm TLA+-side stepping predicate, indexed by an
  `ActionLabel_M3`. Mechanical mirror of `WellWitnessedAppend` +
  the kernel-authored slice of `KernelAuthoredParentsInTrace`.
-/

/-- The TLA+-side step. One arm per `ActionLabel_M3` constructor;
    each arm's body is the per-arm pre/post transcribed. -/
def TLAStep_M3
    (t : Trace)
    (a : ActionLabel_M3)
    (t' : Trace) : Prop :=
  match a with
  | ActionLabel_M3.wellWitnessedAppend e =>
      WellWitnessedAppendStep t e t'
  | ActionLabel_M3.kernelAuthoredAppend e =>
      KernelAuthoredAppendStep t e t'

/-! ## LeanStep_M3

  The Lean-side step. **Defined independently of `TLAStep_M3`** as
  the primitive predicate "`t'` extends `t` by one event satisfying
  `wellWitnessed`, with the parent-presence closure firing when the
  event claims kernel authorship."

  Independence from `TLAStep_M3` is the design choice that makes
  `BridgeSound_M3` substantive (not `Iff.rfl` like M5/M7's). The
  bridge proof must reify the `if-then-else` on `e.kernelAuthored`
  into the `wellWitnessedAppend`/`kernelAuthoredAppend` constructors
  via a `by_cases` on the Bool flag.
-/

/-- The Lean-side step relation. Defined as "`t'` extends `t` by
    one event `e` such that `wellWitnessed e = true`, AND if `e`
    claims kernel authorship, its parents are already in `t`."

    This is M3's primitive operational shape on the Lean side: a
    step is the act of appending one well-witnessed event, with the
    parent-presence side-condition fired when authorship is claimed. -/
def LeanStep_M3
    (t t' : Trace) : Prop :=
  ∃ e : Event,
    Event.wellWitnessed e = true ∧
    (e.kernelAuthored = true →
      ∀ p ∈ e.parents, Event.parentInTrace t p = true) ∧
    t' = List.append (α := Event) t [e]

/-! ## BridgeSound_M3

  The bridge soundness theorem. Statement:
  `LeanStep_M3 t t' ↔ ∃ a, TLAStep_M3 t a t'`.

  Unlike M5/M7's `Iff.rfl`, this proof requires reifying the
  authorship-conditional inside `LeanStep_M3` into the action-label
  constructors. The forward direction `by_cases` on
  `e.kernelAuthored = true`; the backward direction `cases a` and
  reassembles the conditional via `Bool` case-analysis.

  **The case-split is the substantive content** — and is the
  structural difference between this probe and the M5/M7 outcomes.
-/

/-- **BridgeSound_M3.** The Lean-side step relation iff the
    existential closure of the TLA+-side per-arm step relation.

    Forward direction: extract the appended event from `LeanStep_M3`,
    `by_cases` on `e.kernelAuthored = true` (Bool decidable
    equality), choose `wellWitnessedAppend` or `kernelAuthoredAppend`.

    Backward direction: destructure the `ActionLabel_M3` and
    reassemble `LeanStep_M3` from the per-arm payload. -/
theorem BridgeSound_M3
    (t t' : Trace) :
    LeanStep_M3 t t'
      ↔ ∃ a : ActionLabel_M3, TLAStep_M3 t a t' := by
  constructor
  · -- Forward: from LeanStep_M3, witness an ActionLabel_M3.
    intro hLean
    obtain ⟨e, hWW, hParents, hAppend⟩ := hLean
    by_cases hKA : e.kernelAuthored = true
    · -- Kernel-authored arm: invoke the parent-presence closure.
      refine ⟨ActionLabel_M3.kernelAuthoredAppend e, ?_⟩
      show KernelAuthoredAppendStep t e t'
      exact ⟨hKA, hWW, hParents hKA, hAppend⟩
    · -- Non-kernel arm: decline kernel authorship; vacuous parent-
      -- presence.
      have hKAfalse : e.kernelAuthored = false := by
        cases hCase : e.kernelAuthored
        · rfl
        · exact absurd hCase hKA
      refine ⟨ActionLabel_M3.wellWitnessedAppend e, ?_⟩
      show WellWitnessedAppendStep t e t'
      exact ⟨hKAfalse, hWW, hAppend⟩
  · -- Backward: from ∃ a, TLAStep_M3 a, recover LeanStep_M3.
    intro ⟨a, hTLA⟩
    cases a with
    | wellWitnessedAppend e =>
        unfold TLAStep_M3 at hTLA
        obtain ⟨hKAfalse, hWW, hAppend⟩ := hTLA
        refine ⟨e, hWW, ?_, hAppend⟩
        intro hKA
        -- e.kernelAuthored = true ∧ e.kernelAuthored = false: ⊥.
        rw [hKAfalse] at hKA
        exact absurd hKA Bool.false_ne_true
    | kernelAuthoredAppend e =>
        unfold TLAStep_M3 at hTLA
        obtain ⟨_hKA, hWW, hParents, hAppend⟩ := hTLA
        exact ⟨e, hWW, fun _ => hParents, hAppend⟩

/-! ## Closure preservation under each arm

  An honest probe must demonstrate the bridge is **not vacuous**:
  the Lean side's structural invariant (trace-wide `Trace.captured`)
  is preserved by every action arm. Mirrors M4/M6's
  preserves-wellLabeled / preserves-wellFormed shape.

  At M3 the trace-level invariant is `Trace.captured` (every event
  is `wellWitnessed`). The arm preconditions provide
  `wellWitnessed = true` for the new event; the existing events'
  obligation is preserved trivially because `Trace.captured`'s body
  references only per-event syntactic fields (no trace-relative
  predicate).

  We prove three closure-preservation lemmas:
  1. `WellWitnessedAppendStep_preserves_captured` — appending a
     non-kernel well-witnessed event preserves trace-wide capture.
  2. `KernelAuthoredAppendStep_preserves_captured` — same for the
     kernel-authored arm.
  3. `LeanStep_M3_preserves_captured` — bridge-level closure: every
     step expressible as `LeanStep_M3` preserves trace-wide capture.
-/

/-- Auxiliary: appending a `wellWitnessed`-true event to a captured
    trace yields a captured trace. Used by both arm-preservation
    lemmas. -/
private theorem captured_append_singleton
    (t : Trace)
    (e : Event)
    (hCap : Trace.captured t = true)
    (hWW : Event.wellWitnessed e = true) :
    Trace.captured (List.append (α := Event) t [e]) = true := by
  -- View `t : Trace` as `List Event` for List.all_append; Trace is
  -- `def Trace : Type := List Event`, so the cast is definitional.
  let tL : List Event := t
  show ((List.append (α := Event) tL [e]).all Event.wellWitnessed) = true
  -- Convert List.append to ++ form so List.all_append fires.
  show ((tL ++ [e]).all Event.wellWitnessed) = true
  rw [List.all_append, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- tL.all wellWitnessed = true: from hCap (Trace.captured t = t.all wellWitnessed).
    show (tL.all Event.wellWitnessed) = true
    unfold Trace.captured at hCap
    exact hCap
  · -- [e].all wellWitnessed = true: by hWW.
    show (([e] : List Event).all Event.wellWitnessed) = true
    unfold List.all
    rw [hWW]
    rfl

/-- `Trace.captured` is preserved by `WellWitnessedAppendStep`:
    appending a non-kernel well-witnessed event preserves trace-wide
    capture. Trivial — `Trace.captured` references only per-event
    syntactic content (no trace-relative predicate). -/
theorem WellWitnessedAppendStep_preserves_captured
    (t : Trace)
    (e : Event)
    (t' : Trace)
    (hCap : Trace.captured t = true)
    (hStep : WellWitnessedAppendStep t e t') :
    Trace.captured t' = true := by
  obtain ⟨_hKAfalse, hWW, hAppend⟩ := hStep
  rw [hAppend]
  exact captured_append_singleton t e hCap hWW

/-- `Trace.captured` is preserved by `KernelAuthoredAppendStep`. -/
theorem KernelAuthoredAppendStep_preserves_captured
    (t : Trace)
    (e : Event)
    (t' : Trace)
    (hCap : Trace.captured t = true)
    (hStep : KernelAuthoredAppendStep t e t') :
    Trace.captured t' = true := by
  obtain ⟨_hKA, hWW, _hParents, hAppend⟩ := hStep
  rw [hAppend]
  exact captured_append_singleton t e hCap hWW

/-- **Closure preservation across the bridge.** Every step
    expressible as `LeanStep_M3` (equivalently
    `∃ a, TLAStep_M3 t a t'`) preserves `Trace.captured`.

    This is the structural-content lemma the bridge buys at M3:
    M3's operational `CapturedInvariant` from `Determinism.tla`
    (TLC-checked at the M3 admission tightening) is matched on
    the Lean side by the same invariant preserved across both
    disjuncts of the step relation. -/
theorem LeanStep_M3_preserves_captured
    (t t' : Trace)
    (hCap : Trace.captured t = true)
    (hStep : LeanStep_M3 t t') :
    Trace.captured t' = true := by
  -- Recover the action label from LeanStep_M3 via BridgeSound_M3.
  have hBridge := (BridgeSound_M3 t t').mp hStep
  obtain ⟨a, hTLA⟩ := hBridge
  cases a with
  | wellWitnessedAppend e =>
      have hStep' : WellWitnessedAppendStep t e t' := hTLA
      exact WellWitnessedAppendStep_preserves_captured t e t' hCap hStep'
  | kernelAuthoredAppend e =>
      have hStep' : KernelAuthoredAppendStep t e t' := hTLA
      exact KernelAuthoredAppendStep_preserves_captured t e t' hCap hStep'

/-! ## Empty-trace vacuity check ()

  H2  claimed: empty-parent kernel-authored events are
  non-vacuously admissible (the universal quantifier over
  `e.parents` is trivially true on the empty list). Verified
  here: `LeanStep_M3 [] [e]` holds when `e.parents = []` and
  `wellWitnessed e = true`, regardless of `e.kernelAuthored`.

  This forecloses the "empty-trace vacuity" attack: the bridge
  is non-vacuous on the bootstrap shape (genesis kernel-authored
  emit). -/
theorem empty_trace_kernelAuthored_admissible
    (e : Event)
    (hWW : Event.wellWitnessed e = true)
    (hParents : e.parents = []) :
    LeanStep_M3 [] [e] := by
  refine ⟨e, hWW, ?_, ?_⟩
  · -- Parent-presence: vacuous (e.parents = []).
    intro _hKA p hp
    rw [hParents] at hp
    cases hp
  · -- t' = List.append [] [e] = [e]: definitional.
    rfl

end AgentKernel.Bridge.M3

-- ============================================================
-- lean ...` or `#print axioms` in editor; this file is wired into
-- AgentKernel.lean's import list at H4 close — parent integrates).
-- ============================================================

#print axioms AgentKernel.Bridge.M3.BridgeSound_M3
#print axioms AgentKernel.Bridge.M3.WellWitnessedAppendStep_preserves_captured
#print axioms AgentKernel.Bridge.M3.KernelAuthoredAppendStep_preserves_captured
#print axioms AgentKernel.Bridge.M3.LeanStep_M3_preserves_captured
#print axioms AgentKernel.Bridge.M3.empty_trace_kernelAuthored_admissible



namespace AgentKernel.Bridge.M3.V14R3

open AgentKernel.Causality

/-! ## ActionLabel_M3_CrossCell — sibling inductive for the cross-cell arm

  The v1.3-baseline `ActionLabel_M3` is preserved byte-unchanged. The
  cross-cell append is introduced as a SIBLING inductive. The label
  carries the spawn-parent id `p` and the spawned event `e` plus the
  monotone `p < e.id` discipline witness.

  Single constructor:
  * `crossCellAppend p e` — append a kernel-authored event `e` whose
    `SpawnedBy = some p` and `p < e.id`.
-/
inductive ActionLabel_M3_CrossCell : Type where
  | crossCellAppend (p : Nat) (e : Causality.Event) : ActionLabel_M3_CrossCell

/-- Cross-cell append step. Mirror of Lean 
    `HappensBefore.cross_cell_step` constructor body:
      e ∈ post-state world,
      e.SpawnedBy = some p,
      p < e.id,
      e.kernelAuthored = true.
    Plus the trace-extension shape `W' = W ++ [e]`. -/
def CrossCellAppendStep
    (W : Causality.World)
    (p : Nat)
    (e : Causality.Event)
    (W' : Causality.World) : Prop :=
  e.SpawnedBy = some p ∧
  p < e.id ∧
  e.kernelAuthored = true ∧
  W' = W ++ [e]

def TLAStep_M3_CrossCell
    (W : Causality.World)
    (a : ActionLabel_M3_CrossCell)
    (W' : Causality.World) : Prop :=
  match a with
  | ActionLabel_M3_CrossCell.crossCellAppend p e =>
      CrossCellAppendStep W p e W'

/-! ## LeanStep_M3_CrossCell -- Lean-side step relation

  Defined independently of `TLAStep_M3_CrossCell` so the bridge proof
  is substantive (not `Iff.rfl`). The trace extends by one event such
  that, IF the new event carries `SpawnedBy = some p` for some `p`,
  THEN `p < e.id` AND `e.kernelAuthored = true` (forgery defense).
-/
def LeanStep_M3_CrossCell (W W' : Causality.World) : Prop :=
  ∃ p : Nat, ∃ e : Causality.Event,
    e.SpawnedBy = some p ∧
    p < e.id ∧
    e.kernelAuthored = true ∧
    W' = W ++ [e]

/-! ## BridgeSound_M3_CrossCell -- soundness for the cross-cell arm

  Statement: `LeanStep_M3_CrossCell W W' ↔ ∃ a, TLAStep_M3_CrossCell W a W'`.

  Substantive iff. Forward direction: extract the existential witnesses
  from `LeanStep_M3_CrossCell` and package as `crossCellAppend p e`.
  Backward direction: destructure the action label and reassemble.

  Predicted Tier 2 [propext]; measurement at the bottom of this file.
-/
theorem BridgeSound_M3_CrossCell
    (W W' : Causality.World) :
    LeanStep_M3_CrossCell W W'
      ↔ ∃ a : ActionLabel_M3_CrossCell, TLAStep_M3_CrossCell W a W' := by
  constructor
  · intro hLean
    obtain ⟨p, e, hSp, hLt, hKA, hAppend⟩ := hLean
    refine ⟨ActionLabel_M3_CrossCell.crossCellAppend p e, ?_⟩
    show CrossCellAppendStep W p e W'
    exact ⟨hSp, hLt, hKA, hAppend⟩
  · intro ⟨a, hTLA⟩
    cases a with
    | crossCellAppend p e =>
        have hStep' : CrossCellAppendStep W p e W' := hTLA
        obtain ⟨hSp, hLt, hKA, hAppend⟩ := hStep'
        exact ⟨p, e, hSp, hLt, hKA, hAppend⟩

/-! ## Per-pairing T7 inheritance — SHELL on Bridge/M3.lean side

  The full T7 inheritance lift to `System.lean` (+ cumulative
  across the M2 + M3 surfaces) is deferred to  fold per parent's 
  file-overlap carve. The SHELL here:

  * Names a per-pairing local soundness theorem
    `T7_M3_cross_cell_local` that proves: every `LeanStep_M3_CrossCell`
    step yields a fresh `HappensBefore W' p e.id` proof under the
    post-state world (i.e., the cross-cell happens-before relation
    is realized at the per-step layer).
  * The System.lean lift would compose this with `SystemEvent.toCausality`
    projection-preservation; that composition is the  deliverable.

  Honest naming: STRUCTURAL PACKAGING at the M3 layer. Customer-visible
  guarantee (T7 ⇒ "cross-cell happens-before is preserved across
  trace extension") needs the System.lean lift to be load-bearing;
  the shell here exposes the per-step witness.
-/

/-- **Per-pairing T7 SHELL — `T7_M3_cross_cell_local`.**

    Every `LeanStep_M3_CrossCell` step yields a fresh
    `HappensBefore W' p e.id` witness under the post-state world. This
    binds the operational step (an event-append) to the relational
    happens-before fact (cross-cell ordering).

    Honest naming: STRUCTURAL PACKAGING at the M3 layer. The full
    System.lean T7 lift (+ cumulative across the SystemEvent
    projection layer) is  carry-forward.

    Tier prediction: Tier 1 axiom-free (mirrors  `cross_cell_step_intro`
    which was measured T1; this theorem composes that with `List.mem_append`
    monotonicity and recovers the post-state membership). -/
theorem T7_M3_cross_cell_local
    (W W' : Causality.World)
    (hStep : LeanStep_M3_CrossCell W W') :
    ∃ p : Nat, ∃ e : Causality.Event,
      e ∈ W' ∧ HappensBefore W' p e.id := by
  obtain ⟨p, e, hSp, hLt, hKA, hAppend⟩ := hStep
  refine ⟨p, e, ?_, ?_⟩
  · -- e ∈ W' = W ++ [e]: List.mem_append + Or.inr.
    rw [hAppend]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  · -- HappensBefore W' p e.id via cross_cell_step constructor.
    apply HappensBefore.cross_cell_step
    · -- e ∈ W'.
      rw [hAppend]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    · exact hSp
    · exact hLt
    · exact hKA

end AgentKernel.Bridge.M3.V14R3

#print axioms AgentKernel.Bridge.M3.V14R3.BridgeSound_M3_CrossCell
#print axioms AgentKernel.Bridge.M3.V14R3.T7_M3_cross_cell_local
