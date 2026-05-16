import AgentKernel.Caps
import AgentKernel.System



namespace AgentKernel.Bridge.M5

open AgentKernel.Caps
open AgentKernel.IFC (LabelXform)


inductive ActionLabel_M5
    (Principal Tag_C Tag_I Tag_P : Type) : Type where
  | mintCap
      (newId : CapId)
      (g : LabelXform Tag_C Tag_I Tag_P) :
      ActionLabel_M5 Principal Tag_C Tag_I Tag_P
  | delegate
      (parentId : CapId)
      (newId : CapId)
      (g : LabelXform Tag_C Tag_I Tag_P) :
      ActionLabel_M5 Principal Tag_C Tag_I Tag_P
  | invoke
      (cid : CapId)
      (who : Principal) :
      ActionLabel_M5 Principal Tag_C Tag_I Tag_P



/-- TLA+ `MintCap` arm transcribed.
    Pre: `newId` is fresh in the store.
    Post: the store gains exactly one entry at `newId`, kernel-
    minted (parent = none), with granted = `g`.

    The post-state is asserted pointwise (`∀ cid, store' cid = ...`)
    rather than as a function-equality (`store' = fun cid => ...`)
    because pointwise rewriting in proofs sidesteps beta-reduction
    fragility when `rw`-ing through a lambda. -/
def MintStep
    {Tag_C Tag_I Tag_P : Type}
    (store : CapStore Tag_C Tag_I Tag_P)
    (newId : CapId)
    (g : LabelXform Tag_C Tag_I Tag_P)
    (store' : CapStore Tag_C Tag_I Tag_P) : Prop :=
  store newId = none ∧
  ∀ cid, store' cid =
    (if cid = newId then
      some { id := newId, granted := g, parent := none }
    else
      store cid)

/-- TLA+ `Delegate` arm transcribed.
    Pre: `parentId` resolves in the store; `newId` is fresh; the
    parent's `granted` attenuates to `g` under `atten`.
    Post: store gains exactly one entry at `newId` whose parent
    is `parentId`. Post asserted pointwise (see `MintStep`). -/
def DelegateStep
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (parentId : CapId)
    (newId : CapId)
    (g : LabelXform Tag_C Tag_I Tag_P)
    (store' : CapStore Tag_C Tag_I Tag_P) : Prop :=
  (∃ parent : Capability Tag_C Tag_I Tag_P,
      store parentId = some parent ∧
      atten parent.granted g = true) ∧
  store newId = none ∧
  ∀ cid, store' cid =
    (if cid = newId then
      some { id := newId, granted := g, parent := some parentId }
    else
      store cid)

/-- TLA+ `Invoke` arm transcribed.
    Pre: `cid` resolves in the store; the looked-up cap's
    `granted` is authorized for `who` under `auth`.
    Post: store unchanged (`UNCHANGED store` on the TLA+ side). -/
def InvokeStep
    {Principal Tag_C Tag_I Tag_P : Type}
    (auth : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (store : CapStore Tag_C Tag_I Tag_P)
    (cid : CapId)
    (who : Principal)
    (store' : CapStore Tag_C Tag_I Tag_P) : Prop :=
  (∃ cap : Capability Tag_C Tag_I Tag_P,
      store cid = some cap ∧ auth who cap.granted) ∧
  store' = store

/-! ## TLAStep_M5

  Per-arm TLA+-side stepping predicate, indexed by an
  `ActionLabel_M5`. Mechanical mirror of `Next_M5`'s disjuncts.
-/

/-- The TLA+-side step. One arm per `ActionLabel_M5` constructor;
    each arm's body is the disjunct's pre/post transcribed. -/
def TLAStep_M5
    {Principal Tag_C Tag_I Tag_P : Type}
    (auth : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (a : ActionLabel_M5 Principal Tag_C Tag_I Tag_P)
    (store' : CapStore Tag_C Tag_I Tag_P) : Prop :=
  match a with
  | ActionLabel_M5.mintCap newId g =>
      MintStep store newId g store'
  | ActionLabel_M5.delegate parentId newId g =>
      DelegateStep atten store parentId newId g store'
  | ActionLabel_M5.invoke cid who =>
      InvokeStep auth store cid who store'

/-! ## LeanStep_M5

  The Lean-side step. **Defined as the existential closure of
  `TLAStep_M5` over `ActionLabel_M5`.** This is the honest M5
  finding: at M5, the structural Lean side has no independent
  stepping content beyond its operational primitives, and those
  primitives mirror the TLA+ disjuncts directly. The iff is
  therefore `Iff.rfl`-strength.

  The probe report flags this: M5's bridge is mechanizable, but
  the mechanization's content is reduced to constructor-by-
  constructor arm-mirroring. M6 / M7 / M8 each have additional
  Lean-side structural invariants (`LogChain.wellFormed`,
  `Disclosure.consistent`, etc.) whose stepping content is *not*
  trivially the TLA+ mirror, so a per-module probe is required
  before P6 fan-out.
-/

/-- The Lean-side step relation. Defined as the existential
    closure of `TLAStep_M5`. -/
def LeanStep_M5
    {Principal Tag_C Tag_I Tag_P : Type}
    (auth : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store store' : CapStore Tag_C Tag_I Tag_P) : Prop :=
  ∃ a : ActionLabel_M5 Principal Tag_C Tag_I Tag_P,
    TLAStep_M5 auth atten store a store'

/-! ## BridgeSound_M5

  The bridge soundness theorem. Statement:
  `LeanStep_M5 s s' ↔ ∃ a, TLAStep_M5 s a s'`.

  By the definition of `LeanStep_M5`, the two sides are
  definitionally equal. The proof is `Iff.rfl`.

  **This trivial-by-construction proof is the central P1
  finding** — see the probe report. The triviality is honestly
  reported, *not* dressed up as a real refinement obligation.
-/

/-- **BridgeSound_M5.** `LeanStep_M5` is exactly the
    existential closure of `TLAStep_M5`, by definition. The iff
    holds reflexively. -/
theorem BridgeSound_M5
    {Principal Tag_C Tag_I Tag_P : Type}
    (auth : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store store' : CapStore Tag_C Tag_I Tag_P) :
    LeanStep_M5 auth atten store store'
      ↔ ∃ a : ActionLabel_M5 Principal Tag_C Tag_I Tag_P,
            TLAStep_M5 auth atten store a store' :=
  Iff.rfl

/-! ## Closure preservation under each arm

  An honest P1 probe must demonstrate that the bridge is **not
  vacuous**: the Lean side's structural invariant
  (`CapStore.closed`, the Lean form of TLA+'s `CapClosure`) is
  preserved by every action arm. This is the structural content
  the bridge would actually buy if it were promoted out of TCB.

  The lemma names follow the per-arm decomposition. Proofs are
  case-analyses on the post-state's lookup at an arbitrary `cid`.
-/

/-- `CapStore.closed` is preserved by `MintStep`. The newly
    minted capability has `parent = none`, satisfying the
    `wellFormed` left disjunct trivially; existing entries
    retain wellFormedness because the store grew monotonically
    at a fresh id. -/
theorem MintStep_preserves_closed
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (newId : CapId)
    (g : LabelXform Tag_C Tag_I Tag_P)
    (store' : CapStore Tag_C Tag_I Tag_P)
    (hClosed : CapStore.closed atten store)
    (hStep : MintStep store newId g store') :
    CapStore.closed atten store' := by
  obtain ⟨hFresh, hExt⟩ := hStep
  intro cid cap hLookup
  -- store' cid = (if cid = newId then some {minted} else store cid)
  rw [hExt cid] at hLookup
  unfold Capability.wellFormed
  by_cases hEq : cid = newId
  · -- new entry: parent = none → wellFormed by left disjunct
    rw [if_pos hEq] at hLookup
    -- hLookup : some {minted} = some cap
    have hCapEq :
        ({ id := newId, granted := g, parent := none }
          : Capability Tag_C Tag_I Tag_P) = cap :=
      Option.some.inj hLookup
    subst hCapEq
    exact Or.inl rfl
  · -- existing entry: wellFormed inherited from hClosed.
    rw [if_neg hEq] at hLookup
    have hWF : Capability.wellFormed atten store cap := hClosed cid cap hLookup
    unfold Capability.wellFormed at hWF
    -- Lift: store → store' preserves wellFormed (monotone at fresh id).
    cases hWF with
    | inl hRoot => exact Or.inl hRoot
    | inr hDel =>
        obtain ⟨pid, p, hParEq, hStoreP, hAtten⟩ := hDel
        refine Or.inr ⟨pid, p, hParEq, ?_, hAtten⟩
        -- store' pid = (if pid = newId then ... else store pid)
        rw [hExt pid]
        by_cases hPidEq : pid = newId
        · -- pid = newId ⇒ store newId = some p, contradicting hFresh.
          exfalso
          rw [hPidEq, hFresh] at hStoreP
          contradiction
        · rw [if_neg hPidEq]; exact hStoreP

/-- `CapStore.closed` is preserved by `DelegateStep`. The
    delegated capability has a `some parentId` parent which is
    by precondition present in the store with attenuating
    granted; existing entries inherit wellFormedness from the
    monotone extension at a fresh id. -/
theorem DelegateStep_preserves_closed
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (parentId : CapId)
    (newId : CapId)
    (g : LabelXform Tag_C Tag_I Tag_P)
    (store' : CapStore Tag_C Tag_I Tag_P)
    (hClosed : CapStore.closed atten store)
    (hStep : DelegateStep atten store parentId newId g store') :
    CapStore.closed atten store' := by
  obtain ⟨⟨parent, hParStore, hAttenG⟩, hFresh, hExt⟩ := hStep
  intro cid cap hLookup
  rw [hExt cid] at hLookup
  unfold Capability.wellFormed
  by_cases hEq : cid = newId
  · -- new delegated entry; wellFormed via right disjunct.
    rw [if_pos hEq] at hLookup
    have hCapEq :
        ({ id := newId, granted := g, parent := some parentId }
          : Capability Tag_C Tag_I Tag_P) = cap :=
      Option.some.inj hLookup
    subst hCapEq
    refine Or.inr ⟨parentId, parent, rfl, ?_, hAttenG⟩
    -- store' parentId = store parentId, since parentId ≠ newId
    -- (else store newId = some parent, contradicting hFresh).
    rw [hExt parentId]
    by_cases hPidEq : parentId = newId
    · exfalso
      rw [hPidEq, hFresh] at hParStore
      contradiction
    · rw [if_neg hPidEq]; exact hParStore
  · -- existing entry: lift wellFormedness from `store` to `store'`.
    rw [if_neg hEq] at hLookup
    have hWF : Capability.wellFormed atten store cap :=
      hClosed cid cap hLookup
    unfold Capability.wellFormed at hWF
    cases hWF with
    | inl hRoot => exact Or.inl hRoot
    | inr hDel =>
        obtain ⟨pid, p, hParEq, hStoreP, hAtten⟩ := hDel
        refine Or.inr ⟨pid, p, hParEq, ?_, hAtten⟩
        rw [hExt pid]
        by_cases hPidEq : pid = newId
        · exfalso
          rw [hPidEq, hFresh] at hStoreP
          contradiction
        · rw [if_neg hPidEq]; exact hStoreP

/-- `CapStore.closed` is preserved by `InvokeStep`. Trivially:
    `InvokeStep` leaves the store unchanged. -/
theorem InvokeStep_preserves_closed
    {Principal Tag_C Tag_I Tag_P : Type}
    (auth : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (cid : CapId)
    (who : Principal)
    (store' : CapStore Tag_C Tag_I Tag_P)
    (hClosed : CapStore.closed atten store)
    (hStep : InvokeStep auth store cid who store') :
    CapStore.closed atten store' := by
  obtain ⟨_hAuth, hUnchanged⟩ := hStep
  -- store' = store, so the closure of store transfers verbatim.
  subst hUnchanged
  exact hClosed

/-- **Closure preservation across the bridge.** Every step
    expressible as `LeanStep_M5` (equivalently `∃ a,
    TLAStep_M5 .. a ..`) preserves `CapStore.closed`.

    This is the structural-content lemma the bridge buys: M5's
    operational closure invariant (`CapClosure` in TLA+, TLC-
    checked at 401 states) is matched on the Lean side by the
    same invariant preserved across every disjunct of the step
    relation. -/
theorem LeanStep_M5_preserves_closed
    {Principal Tag_C Tag_I Tag_P : Type}
    (auth : Principal → LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store store' : CapStore Tag_C Tag_I Tag_P)
    (hClosed : CapStore.closed atten store)
    (hStep : LeanStep_M5 auth atten store store') :
    CapStore.closed atten store' := by
  obtain ⟨a, hStep⟩ := hStep
  cases a with
  | mintCap newId g =>
      -- TLAStep_M5 .. (mintCap newId g) .. ≡ MintStep .. by defn.
      have hStep' : MintStep store newId g store' := hStep
      exact MintStep_preserves_closed atten store newId g store'
              hClosed hStep'
  | delegate parentId newId g =>
      have hStep' :
          DelegateStep atten store parentId newId g store' := hStep
      exact DelegateStep_preserves_closed atten store parentId newId g
              store' hClosed hStep'
  | invoke cid who =>
      have hStep' : InvokeStep auth store cid who store' := hStep
      exact InvokeStep_preserves_closed auth atten store cid who store'
              hClosed hStep'

end AgentKernel.Bridge.M5

-- ============================================================
-- lean ...` or `#print axioms` in editor; this file is meant to
-- be read into the wider `lake build` of the AgentKernel target
-- if/when the  wires it into AgentKernel.lean).
-- ============================================================

#print axioms AgentKernel.Bridge.M5.BridgeSound_M5
#print axioms AgentKernel.Bridge.M5.MintStep_preserves_closed
#print axioms AgentKernel.Bridge.M5.DelegateStep_preserves_closed
#print axioms AgentKernel.Bridge.M5.InvokeStep_preserves_closed
#print axioms AgentKernel.Bridge.M5.LeanStep_M5_preserves_closed

-- ============================================================
-- routing into Bridge/M5
-- ============================================================
--
-- This block adds an EXISTENCE LEMMA / STRUCTURAL THREADING
-- `Bridge.M5.InvokeStep` to `System.KernelAuthorizationStep`.
-- by giving the M5 invoke arm a TYPED projection into the kernel
-- authorization stepping rule when a deployer can produce the
-- audit/auth witnesses. No edits before line 494; no edits to
-- forbidden files. This is additive-only past current EOF.
--
--
-- Honest residual: the runtime obligation that `auditedNow` is
-- threaded from a real audit log (non-decreasing across calls)
-- theorem below DOES NOT discharge that obligation; it ONLY
-- supplies the TYPED LINK between M5's `InvokeStep` and
-- `KernelAuthorizationStep` so that a kernel-runtime that does
-- thread audit time-stamps lands typed-into the L0 step relation.

namespace AgentKernel.Bridge.M5


def InvokeStep_admits_kernelAuthorizationStep
    {Principal Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    {auth : Principal → IFC.LabelXform Tag_C Tag_I Tag_P → Prop}
    {store store' : Caps.CapStore Tag_C Tag_I Tag_P}
    {cid : Caps.CapId}
    {whoP : Principal}
    (ctx : Caps.RequestCtx)
    (parentInStore : Bool)
    (auditedNow : Nat)
    (who : Caps.Capability Tag_C Tag_I Tag_P)
    (what : IFC.LabelXform Tag_C Tag_I Tag_P)
    (hAuth : Caps.authorizes_at ctx parentInStore who what)
    (hAudit : ctx.matchesAuditedNow auditedNow = true)
    (_hStep : InvokeStep auth store cid whoP store') :
    System.KernelAuthorizationStep Tag_C Tag_I Tag_P :=
  { ctx := ctx
  , parentInStore := parentInStore
  , who := who
  , what := what
  , auditedNow := auditedNow
  , hAuth := hAuth
  , hAudit := hAudit }

end AgentKernel.Bridge.M5

#print axioms AgentKernel.Bridge.M5.InvokeStep_admits_kernelAuthorizationStep
