import AgentKernel.System



namespace AgentKernel.ConformantL1

open AgentKernel.System


def holds
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq Tag_P]
    [Disclosure.VectorCommitmentScheme V Cm Pf]
    (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  -- Conjunct 1: Replay-captured (T1-obs hypothesis).
  s.events.toReplay.captured = true
  ∧
  -- Conjunct 2: IFC wellLabeled (T3 hypothesis); pins
  IFC.wellLabeled
    (@Caps.authorizes Tag_C Tag_I Tag_P _)
    s.mintingTrusted s.rawInputTags
    s.dmap s.events.toIFC
  ∧
  -- Conjunct 3: cap-store closure (T5 hypothesis).
  Caps.CapStore.closed s.atten s.capStore
  ∧
  -- Conjunct 4: cap-map ⊆ cap-store cross-table consistency
  -- (T5 hypothesis).
  (∀ eid cap, s.capMap eid = some cap →
              ∃ cid, s.capStore cid = some cap)
  ∧
  -- causality_acyclic_strict input).
  Causality.causalCompleteness s.events.toCausality
  ∧
  -- Conjunct 6: audit-chain wellFormed (T4 hypothesis).
  Log.LogChain.wellFormed s.hashFn s.genesis s.serialize s.auditChain
  ∧
  -- Conjunct 7: pointwise disclosure consistency (T8' hypothesis,
  -- ranged over s.disclosures).
  (∀ D ∈ s.disclosures, Disclosure.Disclosure.consistent D)
  ∧
  IFC.PayloadDiscipline.holds s.events.toIFC


theorem T_L1_Lift
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq Tag_P]
    [Disclosure.VectorCommitmentScheme V Cm Pf]
    (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (h : holds s) :
    s.events.toReplay.captured = true
    ∧
    IFC.wellLabeled
      (@Caps.authorizes Tag_C Tag_I Tag_P _)
      s.mintingTrusted s.rawInputTags
      s.dmap s.events.toIFC
    ∧
    Caps.CapStore.closed s.atten s.capStore
    ∧
    (∀ eid cap, s.capMap eid = some cap →
                ∃ cid, s.capStore cid = some cap)
    ∧
    Causality.causalCompleteness s.events.toCausality
    ∧
    Log.LogChain.wellFormed s.hashFn s.genesis s.serialize s.auditChain
    ∧
    (∀ D ∈ s.disclosures, Disclosure.Disclosure.consistent D)
    ∧
    IFC.PayloadDiscipline.holds s.events.toIFC := h

end AgentKernel.ConformantL1

-- ============================================================
-- ============================================================
--
-- Measured: Tier 2 [propext]. Proof of `T_L1_Lift` is `h` itself,
-- but elaboration of the eight conjuncts of `holds` (in particular
-- `IFC.wellLabeled`, `IFC.PayloadDiscipline.holds`, and the
-- bounded-∀ over `s.disclosures`) consumes `propext` via the
-- underlying predicates' Prop-valued bodies. Same shape as the
-- T7-inheritance lemmas (`t7_inherits_t1obs`, `t7_inherits_t3`,
-- `t7_inherits_t8'`) which also land at Tier 2 [propext] via the
-- same mechanism. NO `Quot.sound`, NO `Classical.choice`, NO
-- `sorryAx`. Tier 2 is the honest target; H1's Tier 1 prediction
-- was off by one (axiom inheritance from inner predicates'
-- elaboration costs). H4 lock entry records actual Tier 2.
--
-- : confirm via the #print block in `MeasureAxioms.lean`.

#print axioms AgentKernel.ConformantL1.T_L1_Lift
