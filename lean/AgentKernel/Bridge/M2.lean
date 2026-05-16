import AgentKernel.Causality



namespace AgentKernel.Bridge.M2

open AgentKernel.Causality
open AgentKernel (KernelOrTenant)

/-! ## ActionLabel_M2

  Inductive type with two constructors mirroring the kernel-vs-tenant
  authorship partition that drives `Causality.causalCompleteness`'s
  per-event guard.

  * `emitTenantEvent e` — append a tenant-authored event
    (`e.kernelAuthored = false`); no kernel-parents closure
    obligation.
  * `emitKernelEvent e` — append a kernel-authored event
    (`e.kernelAuthored = true`); carries the `kernelParents`
    closure obligation against the post-state trace.

  Each constructor carries the new `Causality.Event` directly. The
  `parents_older` field's proof obligation rides inside the `Event`
  value (constructor-side) — the bridge does not have to mechanize
  it as a separate predicate, distinguishing it from M4's
  `wellLabeledStep` arms which carry their / obligations as
  external Props.

  TLA+ side correspondence:
  * `emitTenantEvent` ↔ an `EmitNonDeclass` / `EmitDeclass` arm
    of `System.tla`'s `Next` whose `e.id ∉ KernelAuthored`
    (Determinism.tla CONSTANT).
  * `emitKernelEvent` ↔ same arms when `e.id ∈ KernelAuthored`,
    plus the `KernelAuthoredParentsInTrace` invariant body.
-/
inductive ActionLabel_M2 : Type where
  | emitTenantEvent (e : Event) : ActionLabel_M2
  | emitKernelEvent (e : Event) : ActionLabel_M2



/-- Tenant-authored emit. `kernelAuthored` flag is `false`; no
    closure obligation. The post is `W' = W ++ [e]`.

    The `parents_older` precondition rides on the `Event` value's
    constructor-side proof field; not restated here. -/
def EmitTenantEventStep
    (W : World)
    (e : Event)
    (W' : World) : Prop :=
  e.kernelAuthored = false ∧
  W' = W ++ [e]


def EmitKernelEventStep
    (W : World)
    (e : Event)
    (W' : World) : Prop :=
  e.kernelAuthored = true ∧
  kernelParents W' e ∧
  W' = W ++ [e]

/-! ## TLAStep_M2

  Per-arm TLA+-side stepping predicate, indexed by an
  `ActionLabel_M2`. Mechanical mirror of the kernel-vs-tenant
  partition that drives `KernelAuthoredParentsInTrace`'s
  conditional body in Determinism.tla v0.2.
-/


def TLAStep_M2
    (W : World)
    (a : ActionLabel_M2)
    (W' : World) : Prop :=
  match a with
  | ActionLabel_M2.emitTenantEvent e =>
      EmitTenantEventStep W e W'
  | ActionLabel_M2.emitKernelEvent e =>
      EmitKernelEventStep W e W'

/-! ## LeanStep_M2

  The Lean-side step. **Defined independently of `TLAStep_M2`** as
  the primitive predicate "`W' = W ++ [e]` for some event `e` such
  that `e.kernelAuthored = true → kernelParents W' e`." This is the
  Lean-side step relation that drives `causalCompleteness` preservation
  on append.

  Independence from `TLAStep_M2` is the critical design choice that
  makes `BridgeSound_M2` substantive (not `Iff.rfl` like M5's). The
  bridge proof must reify the implicational guard
  (`e.kernelAuthored = true → kernelParents W' e`) into the
  `emitKernelEvent`/`emitTenantEvent` constructors via a `by_cases`
  on the Bool flag.
-/


def LeanStep_M2 (W W' : World) : Prop :=
  ∃ e : Event,
    W' = W ++ [e] ∧
    (e.kernelAuthored = true → kernelParents W' e)

/-! ## BridgeSound_M2

  The bridge soundness theorem. Statement:
  `LeanStep_M2 W W' ↔ ∃ a, TLAStep_M2 W a W'`.

  Unlike M5's `Iff.rfl`, this proof requires reifying the
  implicational guard
  (`e.kernelAuthored = true → kernelParents W' e`) into the action-
  label constructors via `by_cases hKA : e.kernelAuthored = true`.

  **The case-split is the substantive content** — and is the
  structural difference between this bridge and the M5 outcome.

  Predicted axiom tier: Tier 2 `[propext]` (bridge proof transits
  `Bool.eq_iff_iff`-style reasoning when discharging the guard
  case-split; mirrors M4's `[propext]` outcome). The expected
  realisation is documented at the bottom of the file via
  `#print axioms`.
-/

/-- **BridgeSound_M2.** The Lean-side step relation iff the
    existential closure of the TLA+-side per-arm step relation.

    Forward direction: extract the appended event from `LeanStep_M2`,
    `by_cases` on `e.kernelAuthored = true`, choose
    `emitKernelEvent` (extracting `kernelParents W' e` from the
    implicational guard) or `emitTenantEvent` (witnessing
    `kernelAuthored = false` from the case discharge).

    Backward direction: destructure the `ActionLabel_M2`, recover
    the appended-event witness, reassemble the implicational guard
    per arm. -/
theorem BridgeSound_M2
    (W W' : World) :
    LeanStep_M2 W W'
      ↔ ∃ a : ActionLabel_M2, TLAStep_M2 W a W' := by
  constructor
  · -- Forward: from LeanStep_M2, witness an ActionLabel_M2.
    intro hLean
    obtain ⟨e, hAppend, hGuard⟩ := hLean
    by_cases hKA : e.kernelAuthored = true
    · -- Kernel-authored arm: discharge the implicational guard to
      -- recover `kernelParents W' e`, package as `emitKernelEvent`.
      have hKP : kernelParents W' e := hGuard hKA
      refine ⟨ActionLabel_M2.emitKernelEvent e, ?_⟩
      show EmitKernelEventStep W e W'
      exact ⟨hKA, hKP, hAppend⟩
    · -- Tenant arm: `kernelAuthored ≠ true` ⇒ `kernelAuthored = false`
      -- (Bool dichotomy). Package as `emitTenantEvent`.
      have hKA' : e.kernelAuthored = false := by
        cases hbool : e.kernelAuthored with
        | true  => exact absurd hbool hKA
        | false => rfl
      refine ⟨ActionLabel_M2.emitTenantEvent e, ?_⟩
      show EmitTenantEventStep W e W'
      exact ⟨hKA', hAppend⟩
  · -- Backward: from ∃ a, TLAStep_M2 a, recover LeanStep_M2.
    intro ⟨a, hTLA⟩
    cases a with
    | emitTenantEvent e =>
        -- TLAStep_M2 .. (emitTenantEvent e) .. ≡ EmitTenantEventStep
        have hStep' : EmitTenantEventStep W e W' := hTLA
        obtain ⟨hKA', hAppend⟩ := hStep'
        refine ⟨e, hAppend, ?_⟩
        intro hKA
        -- hKA : kernelAuthored = true; hKA' : kernelAuthored = false.
        -- Contradiction.
        rw [hKA'] at hKA
        cases hKA
    | emitKernelEvent e =>
        have hStep' : EmitKernelEventStep W e W' := hTLA
        obtain ⟨_hKA, hKP, hAppend⟩ := hStep'
        refine ⟨e, hAppend, ?_⟩
        intro _hKA'
        exact hKP

/-! ## Closure preservation under each arm

  An honest probe must demonstrate the bridge is **not vacuous**:
  the Lean side's structural invariant (trace-wide `causalCompleteness`)
  is preserved by every action arm, provided the new event satisfies
  its per-step obligation (vacuous for tenant; `kernelParents` for
  kernel).

  Mirrors M4/M5/M6's per-arm preservation pattern. The lift of
  existing events' `causalCompleteness` obligations under trace
  extension is monotone-by-cosntruction here: if `pe ∈ W` then
  `pe ∈ W ++ [e]` (List.mem_append left disjunct), so the existential
  parent witnesses transfer verbatim. **No lift hypothesis is needed**
  (distinguishing M2 from M4, where `wellLabeledStep_lifts_under_extension`
  required `DmapTemporalMonotone`).

  Three closure-preservation lemmas:
  1. `EmitTenantEventStep_preserves_causalCompleteness` — appending
     a tenant event preserves trace-wide `causalCompleteness`
     trivially: the new event has `kernelAuthored = false`, so it
     contributes no new obligation; existing events' obligations
     transfer via parent-witness monotonicity.
  2. `EmitKernelEventStep_preserves_causalCompleteness` — appending
     a kernel event preserves it provided the per-step
     `kernelParents W' e` precondition holds (which is exactly
     the arm's payload).
  3. `LeanStep_M2_preserves_causalCompleteness` — bridge-level closure:
     every step expressible as `LeanStep_M2` preserves
     `causalCompleteness`.
-/

/-- Parent-witness monotonicity under trace extension: a parent
    witness in the prefix `W` lifts to a parent witness in `W ++ [e]`
    via `List.mem_append.mpr (Or.inl _)`. Used by the per-arm
    preservation lemmas; not exposed as a public theorem because
    the lift is mechanical.

    NOT a theorem; this is an inlined helper used inside the
    closure-preservation proofs below. -/
private theorem kernelParents_lifts_under_extension
    (W : World)
    (e₀ enew : Event)
    (h : kernelParents W e₀) :
    kernelParents (W ++ [enew]) e₀ := by
  intro p hp
  obtain ⟨pe, hpeMem, hpeId, hpeKA⟩ := h p hp
  exact ⟨pe, List.mem_append.mpr (Or.inl hpeMem), hpeId, hpeKA⟩

/-- `causalCompleteness` is preserved by `EmitTenantEventStep`.

    Append a tenant-authored event: the new event has
    `kernelAuthored = false`, so its `causalCompleteness` obligation
    is vacuous. Existing events' obligations lift via parent-witness
    monotonicity under trace extension.

    **Proof shape:** for an arbitrary `e₀ ∈ W'`, case-split on
    `e₀ ∈ W` vs `e₀ = e` (List.mem_append). Existing case: lift
    `kernelParents W e₀` to `kernelParents W' e₀`. New case:
    `e.kernelAuthored = false`, so the obligation premise is false
    and the conclusion is vacuous. -/
theorem EmitTenantEventStep_preserves_causalCompleteness
    (W : World)
    (e : Event)
    (W' : World)
    (hCC : causalCompleteness W)
    (hStep : EmitTenantEventStep W e W') :
    causalCompleteness W' := by
  obtain ⟨hKA, hAppend⟩ := hStep
  intro e₀ he₀ hAuth₀
  subst hAppend
  -- e₀ ∈ W ∨ e₀ = e
  cases List.mem_append.mp he₀ with
  | inl hMemW =>
      -- Existing event: causalCompleteness W gives kernelParents W e₀;
      -- lift to kernelParents (W ++ [e]) e₀ via mem_append left.
      have hOld : kernelParents W e₀ := hCC e₀ hMemW hAuth₀
      exact kernelParents_lifts_under_extension W e₀ e hOld
  | inr hMemSingleton =>
      -- e₀ = e; e.kernelAuthored = false, so hAuth₀ : true = false ⇒ ⊥.
      have hEq : e₀ = e := List.mem_singleton.mp hMemSingleton
      subst hEq
      rw [hKA] at hAuth₀
      cases hAuth₀

/-- `causalCompleteness` is preserved by `EmitKernelEventStep`.

    Append a kernel-authored event: the new event satisfies
    `kernelParents W' e` by the arm's payload. Existing events'
    obligations lift via parent-witness monotonicity. -/
theorem EmitKernelEventStep_preserves_causalCompleteness
    (W : World)
    (e : Event)
    (W' : World)
    (hCC : causalCompleteness W)
    (hStep : EmitKernelEventStep W e W') :
    causalCompleteness W' := by
  obtain ⟨_hKA, hKP, hAppend⟩ := hStep
  intro e₀ he₀ hAuth₀
  subst hAppend
  cases List.mem_append.mp he₀ with
  | inl hMemW =>
      -- Existing event: lift via parent-witness monotonicity.
      have hOld : kernelParents W e₀ := hCC e₀ hMemW hAuth₀
      exact kernelParents_lifts_under_extension W e₀ e hOld
  | inr hMemSingleton =>
      -- e₀ = e; the kernelParents obligation is hKP.
      have hEq : e₀ = e := List.mem_singleton.mp hMemSingleton
      subst hEq
      exact hKP


theorem LeanStep_M2_preserves_causalCompleteness
    (W W' : World)
    (hCC : causalCompleteness W)
    (hStep : LeanStep_M2 W W') :
    causalCompleteness W' := by
  -- Recover the action label via BridgeSound_M2.
  have hBridge := (BridgeSound_M2 W W').mp hStep
  obtain ⟨a, hTLA⟩ := hBridge
  cases a with
  | emitTenantEvent e =>
      have hStep' : EmitTenantEventStep W e W' := hTLA
      exact EmitTenantEventStep_preserves_causalCompleteness W e W' hCC hStep'
  | emitKernelEvent e =>
      have hStep' : EmitKernelEventStep W e W' := hTLA
      exact EmitKernelEventStep_preserves_causalCompleteness W e W' hCC hStep'



/-- The initial empty world satisfies `causalCompleteness`. Vacuous:
    no events. -/
theorem init_causalCompleteness : causalCompleteness ([] : World) := by
  intro e he _
  cases he




def AuthorCoherent (W : World) : Prop :=
  ∀ e ∈ W,
    (e.author = KernelOrTenant.kernel ↔ e.kernelAuthored = true)

end AgentKernel.Bridge.M2

-- ============================================================
-- `lake env lean MeasureAxioms.lean` or `#print axioms` in editor;
-- this file is wired into the AgentKernel target via
-- AgentKernel.lean's import list at H4 lock — parent agent's task,
-- not this agent's).
-- ============================================================

#print axioms AgentKernel.Bridge.M2.BridgeSound_M2
#print axioms AgentKernel.Bridge.M2.EmitTenantEventStep_preserves_causalCompleteness
#print axioms AgentKernel.Bridge.M2.EmitKernelEventStep_preserves_causalCompleteness
#print axioms AgentKernel.Bridge.M2.LeanStep_M2_preserves_causalCompleteness



namespace AgentKernel.Bridge.M2.V14R3

open AgentKernel.Replay


inductive ActionLabel_M2_Retract : Type where
  | emitNonRetractEvent (e : Event) : ActionLabel_M2_Retract
  | emitRetractEvent    (e : Event) (tid : Nat) : ActionLabel_M2_Retract

/-! ## Per-arm pre/post predicates

  Each arm transcribes onto `Trace = List Event` (Replay-side trace
  shape). The TLA+-side `WellFormedRetraction(trace, e)` predicate is
  not asserted here as a separate conjunct — clauses (a) and (b) are
  discharged into the arm's data, and clause (c) lives at the trace-
  level wellFormedness layer.
-/

/-- Non-retract emit. `kind ≠ Kind.retract`; no retract obligation.
    The post is `t' = t ++ [e]`. -/
def EmitNonRetractEventStep
    (t : Trace)
    (e : Event)
    (t' : Trace) : Prop :=
  e.kind ≠ Kind.retract ∧
  t' = List.append (α := Event) t [e]

/-- Retract emit. `kind = Kind.retract`; carries:
    (a) `retractTarget = some tid`,
    (b) `tid ∈ e.parents`,
    (forgery defense) `kernelAuthored = true`.

    The clause (c) terminal-on-retract is enforced at the trace-level
    wellFormedness layer (Replay-side `Trace.wellFormedRetraction`)
    and is not restated as a per-arm precondition; the bridge soundness
    proves equivalence under the per-arm formulation. -/
def EmitRetractEventStep
    (t : Trace)
    (e : Event)
    (tid : Nat)
    (t' : Trace) : Prop :=
  e.kind = Kind.retract ∧
  e.payloadRetractTarget = some tid ∧
  tid ∈ e.parents ∧
  e.kernelAuthored = true ∧
  t' = List.append (α := Event) t [e]



def TLAStep_M2_Retract
    (t : Trace)
    (a : ActionLabel_M2_Retract)
    (t' : Trace) : Prop :=
  match a with
  | ActionLabel_M2_Retract.emitNonRetractEvent e =>
      EmitNonRetractEventStep t e t'
  | ActionLabel_M2_Retract.emitRetractEvent e tid =>
      EmitRetractEventStep t e tid t'

/-! ## LeanStep_M2_Retract -- Lean-side step relation, defined
       independently of `TLAStep_M2_Retract`

  The trace extends by one event such that, IF `kind = Kind.retract`,
  THEN clauses (a) + (b) + forgery-defense fire. Independent definition
  is what makes `BridgeSound_M2_Retract` substantive (mirrors M2 v0.1
  shape) rather than `Iff.rfl`. The case-split is on `decide
  (e.kind = Kind.retract)` (Lean Decidable via `Kind` enum
  decidability).
-/

def LeanStep_M2_Retract (t t' : Trace) : Prop :=
  ∃ e : Event,
    t' = List.append (α := Event) t [e] ∧
    (e.kind = Kind.retract →
      ∃ tid, e.payloadRetractTarget = some tid ∧ tid ∈ e.parents ∧
             e.kernelAuthored = true)

/-! ## BridgeSound_M2_Retract -- soundness of the bridge for the new arm

  Statement: `LeanStep_M2_Retract t t' ↔ ∃ a, TLAStep_M2_Retract t a t'`.

  Substantive iff via `by_cases hRet : e.kind = Kind.retract`.
  Forward direction: extract `t' = t ++ [e]` and the conditional
  retract obligation; case-split on whether the event is a retract
  to choose the appropriate ActionLabel constructor. Backward direction:
  destructure the action label and reassemble the conditional.

  Predicted Tier 2 [propext] (mirrors the v1.3-baseline
  `BridgeSound_M2`'s case-split shape; the by_cases on Kind decidable
  equality routes through propext via the Decidable elaborator).
-/

theorem BridgeSound_M2_Retract
    (t t' : Trace) :
    LeanStep_M2_Retract t t'
      ↔ ∃ a : ActionLabel_M2_Retract, TLAStep_M2_Retract t a t' := by
  constructor
  · -- Forward: from LeanStep_M2_Retract, witness an ActionLabel.
    intro hLean
    obtain ⟨e, hAppend, hCond⟩ := hLean
    by_cases hRet : e.kind = Kind.retract
    · -- Retract arm: discharge the conditional to recover (tid, retractTarget,
      -- parents, kernelAuthored); package as emitRetractEvent.
      obtain ⟨tid, hRT, hParents, hKA⟩ := hCond hRet
      refine ⟨ActionLabel_M2_Retract.emitRetractEvent e tid, ?_⟩
      show EmitRetractEventStep t e tid t'
      exact ⟨hRet, hRT, hParents, hKA, hAppend⟩
    · -- Non-retract arm: package as emitNonRetractEvent.
      refine ⟨ActionLabel_M2_Retract.emitNonRetractEvent e, ?_⟩
      show EmitNonRetractEventStep t e t'
      exact ⟨hRet, hAppend⟩
  · -- Backward: from ∃ a, TLAStep, recover LeanStep_M2_Retract.
    intro ⟨a, hTLA⟩
    cases a with
    | emitNonRetractEvent e =>
        have hStep' : EmitNonRetractEventStep t e t' := hTLA
        obtain ⟨hKindNotRet, hAppend⟩ := hStep'
        refine ⟨e, hAppend, ?_⟩
        intro hRet
        exact absurd hRet hKindNotRet
    | emitRetractEvent e tid =>
        have hStep' : EmitRetractEventStep t e tid t' := hTLA
        obtain ⟨hKind, hRT, hParents, hKA, hAppend⟩ := hStep'
        refine ⟨e, hAppend, ?_⟩
        intro _hRet
        exact ⟨tid, hRT, hParents, hKA⟩

/-! ## SpawnedBy dictionary entry — Lean side has the field; TLA+
    side has the  alias `SpawnedByOf(e)`. No new
    BridgeSound theorem is needed for the field-mirror dictionary
    entry; the field is structurally projected through both sides.
    The load-bearing soundness for SpawnedBy lives in  cross-cell
    HappensBefore (Bridge/M3.lean below) — the field has no
    standalone TLA+ action arm.
-/

/-! ## Per-pairing T7 inheritance — SHELL on Bridge/M2.lean side

  The full T7 inheritance lift in `System.lean` (" retract arm
  preserves the M2 invariant under SystemEvent.toReplay projection")
  is deferred to  fold per parent's  file-overlap carve. The
  SHELL here:

  * Names a per-pairing local soundness theorem `T7_M2_retract_local`
    that proves: under `Trace.wellFormedRetraction t` invariant on
    the pre-state, every `LeanStep_M2_Retract` step preserves the
    Replay-side wellFormedness.
  * The System.lean lift would compose this with `SystemEvent.toReplay`
    projection-preservation; that composition is the  deliverable.

  Honest naming: this is a STRUCTURAL PACKAGING theorem at the M2
  layer. It exposes the per-arm invariant-preservation as a citable
  named target so the  System.lean lift has a non-vacuous starting
  point. The customer-visible guarantee (T7 ⇒ "downstream replay /
  causality / disclosure consumers see retract events as causally
  ordered after their targets") is NOT closed by this theorem alone;
   fold completes the chain.
-/

/-- **Per-pairing T7 SHELL — `T7_M2_retract_local`.**

    Under `Trace.wellFormedRetraction t` (the trace-level Replay
    invariant from ), every `LeanStep_M2_Retract` step preserves
    the Replay-side wellFormedness on the new event.

    Honest naming: STRUCTURAL PACKAGING at the M2 layer. The full
    System.lean T7 lift ( retract arm threads through the M8
    composite invariant) is  carry-forward. This theorem exposes
    the per-arm soundness as a citable named target.

    Tier prediction: Tier 2 [propext] (mirrors BridgeSound_M2_Retract
    proof shape; case-split on Kind decidable equality routes through
    propext). -/
theorem T7_M2_retract_local
    (t t' : Trace)
    (hWF : Trace.wellFormedRetraction t)
    (hStep : LeanStep_M2_Retract t t') :
    -- The new event's per-event wellFormedRetraction holds under
    -- the post-state trace, conditional on the event's structural
    -- correspondence to one of the bridge's arms.
    ∃ e : Event,
      t' = List.append (α := Event) t [e] ∧
      (e.kind = Kind.retract →
        e.payloadRetractTarget ≠ none ∧
        ∀ tid, e.payloadRetractTarget = some tid → tid ∈ e.parents) := by
  obtain ⟨e, hAppend, hCond⟩ := hStep
  refine ⟨e, hAppend, ?_⟩
  intro hRet
  obtain ⟨tid, hRT, hParents, _hKA⟩ := hCond hRet
  refine ⟨?_, ?_⟩
  · -- retractTarget ≠ none from `hRT : retractTarget = some tid`
    intro hNone
    rw [hNone] at hRT
    cases hRT
  · intro tid' hRT'
    -- hRT : retractTarget = some tid; hRT' : retractTarget = some tid'
    -- ⇒ tid = tid'; substitute and use hParents.
    rw [hRT] at hRT'
    cases hRT'
    exact hParents

end AgentKernel.Bridge.M2.V14R3

#print axioms AgentKernel.Bridge.M2.V14R3.BridgeSound_M2_Retract
#print axioms AgentKernel.Bridge.M2.V14R3.T7_M2_retract_local
#print axioms AgentKernel.Bridge.M2.init_causalCompleteness












