import AgentKernel.MultiCell



namespace AgentKernel.Bridge.MultiCell.V14R4

open AgentKernel.Replay (Event)
open AgentKernel.MultiCell




theorem BridgeSound_MultiCell_TraceUnion
    (t₁ t₂ : List Event)
    (h : Trace.disjointEventIds t₁ t₂) :
    Trace.union t₁ t₂ h = t₁ ++ t₂ :=
  rfl




theorem BridgeSound_MultiCell_TraceUnionOpt_disjoint
    (t₁ t₂ : List Event)
    (h : Trace.disjointEventIds t₁ t₂) :
    Trace.union_opt t₁ t₂ = some (Trace.union t₁ t₂ h) :=
  Trace.union_opt_eq_union_of_disjoint t₁ t₂ h

/-! ## §3 — Per-pairing T7 inheritance: `T7_MultiCell_traceUnion_local`

  Mirrors `Bridge/M2.V14R3.T7_M2_retract_local` and
  `Bridge/M3.V14R3.T7_M3_cross_cell_local` shape. Names the per-pairing
  Bridge-layer contribution to the System.lean T7 inheritance lift; the
  full `SystemEvent`-context T7 inheritance theorem
  (`t7_inherits_traceUnion_disjoint_preserves_wellFormed`) lives in
  `System.lean`.

  Honest naming: this is STRUCTURAL COMPOSITION of the `MultiCell.lean`
   headline preservation theorems exposed at the
  `Bridge/MultiCell` layer as a citable named target. The LOAD-BEARING
  content is in `MultiCell.lean`. -/


theorem T7_MultiCell_traceUnion_local
    (t₁ t₂ : List Event)
    (h : Trace.disjointEventIds t₁ t₂)
    (h₁ : AgentKernel.Replay.Trace.wellFormedSpawnedBy t₁)
    (h₂ : AgentKernel.Replay.Trace.wellFormedSpawnedBy t₂) :
    AgentKernel.Replay.Trace.wellFormedSpawnedBy (Trace.union t₁ t₂ h) :=
  AgentKernel.MultiCell.traceUnion_disjoint_preserves_wellFormedSpawnedBy
    t₁ t₂ h h₁ h₂


theorem T7_MultiCell_traceUnion_retraction_local
    (t₁ t₂ : List Event)
    (h : Trace.disjointEventIds t₁ t₂)
    (h₁ : ∀ e ∈ t₁,
            AgentKernel.Replay.Event.wellFormedRetraction
              (Trace.union t₁ t₂ h) e)
    (h₂ : ∀ e ∈ t₂,
            AgentKernel.Replay.Event.wellFormedRetraction
              (Trace.union t₁ t₂ h) e) :
    AgentKernel.Replay.Trace.wellFormedRetraction (Trace.union t₁ t₂ h) :=
  AgentKernel.MultiCell.traceUnion_disjoint_preserves_wellFormedRetraction
    t₁ t₂ h h₁ h₂

end AgentKernel.Bridge.MultiCell.V14R4

-- ============================================================
-- `lake env lean MeasureAxioms.lean` or `#print axioms` in editor).
-- ============================================================

#print axioms AgentKernel.Bridge.MultiCell.V14R4.BridgeSound_MultiCell_TraceUnion
#print axioms AgentKernel.Bridge.MultiCell.V14R4.BridgeSound_MultiCell_TraceUnionOpt_disjoint
#print axioms AgentKernel.Bridge.MultiCell.V14R4.T7_MultiCell_traceUnion_local
#print axioms AgentKernel.Bridge.MultiCell.V14R4.T7_MultiCell_traceUnion_retraction_local
