import AgentKernel.Bridge.M1
import AgentKernel.Bridge.M2
import AgentKernel.Bridge.M3
import AgentKernel.Bridge.M4
import AgentKernel.Bridge.M5
import AgentKernel.Bridge.M6
import AgentKernel.Bridge.M7
import AgentKernel.Bridge.M8
import AgentKernel.Bridge.MultiCell
import AgentKernel.Bridge.Liveness



namespace AgentKernel.Bridge.Universal



/-- 10-arm module-identifier sum for the v1.10  universal lift.
    Each constructor names one of the 10 hand-curated Bridge modules
    whose individual `BridgeSound_M_i` theorem the universal lift
    quantifies over. -/
inductive ActionLabel_Universal : Type where
  | m1
  | m2
  | m3
  | m4
  | m5
  | m6
  | m7
  | m8
  | multiCell
  | liveness
  deriving DecidableEq, Repr

instance : Inhabited ActionLabel_Universal := ⟨.m1⟩

/-! ## `LeanStep_Universal` — per-arm `Prop` clause

  The body of each clause is the per-module `BridgeSound_M_i`
  statement, universally quantified over the module-specific state
  carriers and parameters. For 9 of the 10 modules, the shape is
  `∀ ..., LeanStep_M_i ↔ ∃ a, TLAStep_M_i`. The MultiCell clause is
  the direct equality `Trace.union t₁ t₂ h = t₁ ++ t₂` (honest naming
  per the file docstring's MultiCell shape note).

  Naming convention: `LeanStep_Universal` (not `BridgeSoundClause`)
  to mirror the per-module `LeanStep_M_i` pattern at the universal
  layer — this is the cite-able universal predicate that the master
  theorem discharges.
-/

/-- Per-arm `Prop` clause for the universal lift. -/
def LeanStep_Universal : ActionLabel_Universal → Prop
  | .m1 =>
      ∀ (t t' : List AgentKernel.Replay.Event),
        M1.LeanStep_M1 t t' ↔
        ∃ a : M1.ActionLabel_M1, M1.TLAStep_M1 t a t'
  | .m2 =>
      ∀ (W W' : AgentKernel.Causality.World),
        M2.LeanStep_M2 W W' ↔
        ∃ a : M2.ActionLabel_M2, M2.TLAStep_M2 W a W'
  | .m3 =>
      ∀ (t t' : AgentKernel.Replay.Trace),
        M3.LeanStep_M3 t t' ↔
        ∃ a : M3.ActionLabel_M3, M3.TLAStep_M3 t a t'
  | .m4 =>
      ∀ {Principal Tag_C Tag_I Tag_P : Type}
        [DecidableEq Tag_P]
        (authorizes : Principal →
          AgentKernel.IFC.LabelXform Tag_C Tag_I Tag_P → Prop)
        (mintingTrusted : AgentKernel.IFC.Factor Tag_P)
        (rawInputTags : AgentKernel.IFC.Factor Tag_P)
        (dmap : AgentKernel.IFC.DeclassMap Principal Tag_C Tag_I Tag_P)
        (t t' : AgentKernel.IFC.Trace Tag_C Tag_I Tag_P),
        M4.LeanStep_M4 authorizes mintingTrusted rawInputTags dmap t t' ↔
        ∃ a : M4.ActionLabel_M4 Principal Tag_C Tag_I Tag_P,
          M4.TLAStep_M4 authorizes rawInputTags dmap t a t'
  | .m5 =>
      ∀ {Principal Tag_C Tag_I Tag_P : Type}
        (auth : Principal →
          AgentKernel.IFC.LabelXform Tag_C Tag_I Tag_P → Prop)
        (atten : AgentKernel.Caps.AttenRel Tag_C Tag_I Tag_P)
        (store store' : AgentKernel.Caps.CapStore Tag_C Tag_I Tag_P),
        M5.LeanStep_M5 auth atten store store' ↔
        ∃ a : M5.ActionLabel_M5 Principal Tag_C Tag_I Tag_P,
          M5.TLAStep_M5 auth atten store a store'
  | .m6 =>
      ∀ {Bytes Hash : Type}
        (H : Bytes → Hash)
        (genesis : Bytes)
        (serialize : Hash → Bytes → Bytes)
        (chain chain' : AgentKernel.Log.LogChain Bytes Hash),
        M6.LeanStep_M6 H genesis serialize chain chain' ↔
        ∃ a : M6.ActionLabel_M6 Bytes,
          M6.TLAStep_M6 H genesis serialize chain a chain'
  | .m7 =>
      ∀ {V C P : Type}
        [AgentKernel.Disclosure.VectorCommitmentScheme V C P]
        (s s' : M7.M7State V C P),
        M7.LeanStep_M7 s s' ↔
        ∃ a : M7.ActionLabel_M7 V C P, M7.TLAStep_M7 s a s'
  | .m8 =>
      ∀ {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
        [AgentKernel.Disclosure.VectorCommitmentScheme V Cm Pf]
        (auth : AgentKernel.Caps.Principal Tag_C Tag_I Tag_P →
          AgentKernel.IFC.LabelXform Tag_C Tag_I Tag_P → Prop)
        (atten : AgentKernel.Caps.AttenRel Tag_C Tag_I Tag_P)
        (H : Bytes → Hash)
        (genesis : Bytes)
        (serialize : Hash → Bytes → Bytes)
        (s s' : M8.M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf),
        M8.LeanStep_M8 auth atten H genesis serialize s s' ↔
        ∃ a : M8.ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf,
          M8.TLAStep_M8 auth atten H genesis serialize s a s'
  | .multiCell =>
      ∀ (t₁ t₂ : List AgentKernel.Replay.Event)
        (h : AgentKernel.MultiCell.Trace.disjointEventIds t₁ t₂),
        AgentKernel.MultiCell.Trace.union t₁ t₂ h = t₁ ++ t₂
  | .liveness =>
      ∀ (s s' : Liveness.LiveState),
        Liveness.LeanStep_Liveness s s' ↔
        ∃ a : Liveness.ActionLabel_Liveness,
          Liveness.TLAStep_Liveness s a s'




theorem BridgeSound_Universal :
    ∀ m : ActionLabel_Universal, LeanStep_Universal m := by
  intro m
  cases m with
  | m1        => exact M1.BridgeSound_M1
  | m2        => exact M2.BridgeSound_M2
  | m3        => exact M3.BridgeSound_M3
  | m4        =>
      intro _ _ _ _ _ authorizes mintingTrusted rawInputTags dmap t t'
      exact M4.BridgeSound_M4_nonMint
              authorizes mintingTrusted rawInputTags dmap t t'
  | m5        =>
      intro _ _ _ _ auth atten store store'
      exact M5.BridgeSound_M5 auth atten store store'
  | m6        =>
      intro _ _ H genesis serialize chain chain'
      exact M6.BridgeSound_M6 H genesis serialize chain chain'
  | m7        =>
      intro _ _ _ _ s s'
      exact M7.BridgeSound_M7 s s'
  | m8        =>
      intro _ _ _ _ _ _ _ _ _ auth atten H genesis serialize s s'
      exact M8.BridgeSound_M8 auth atten H genesis serialize s s'
  | multiCell =>
      intro t₁ t₂ h
      exact AgentKernel.Bridge.MultiCell.V14R4.BridgeSound_MultiCell_TraceUnion
              t₁ t₂ h
  | liveness  => exact Liveness.BridgeSound_Liveness

end AgentKernel.Bridge.Universal

-- ============================================================
-- `lake env lean AgentKernel/Bridge/Universal.lean`. Expected tier
-- HARD RULE):
--   * `BridgeSound_Universal` — Tier 2 [propext] (supremum;
--     inherited from M4 `_nonMint` clause's `Kind` case-analysis).
-- Cross-referenced from `lean/MeasureAxioms.lean` for
-- ============================================================

#print axioms AgentKernel.Bridge.Universal.BridgeSound_Universal
