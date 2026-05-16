import AgentKernel.IFC



namespace AgentKernel.PayloadDiscipline

open AgentKernel.IFC
open AgentKernel.Replay (Kind)

-- ============================================================
-- holds — re-exported from IFC.lean for namespace ergonomics
-- ============================================================

/-- Re-exports `IFC.PayloadDiscipline.holds` (the L0 named predicate)
    under this module's namespace so callers can write
    `PayloadDiscipline.holds t` (rather than the qualified
    `IFC.PayloadDiscipline.holds t`). The actual definition lives in
    `IFC.lean` so that `t3_noninterference_modulo_payload_discipline`
    in IFC.lean can reference it without an import cycle.

    The L0 predicate states: for every event in the trace whose
    `kind` is neither `Kind.declassify` nor `Kind.declassMint`, the
    event's `outLabel.prov` equals the join of `inLabel.prov` and
    `ctxLabel.prov`. -/
abbrev holds {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P) : Prop :=
  IFC.PayloadDiscipline.holds t

-- ============================================================
-- LabeledPayload — the SDK-boundary structured type
-- ============================================================
--
-- structure DEFINITION moved to `IFC.lean` (right after the `Label`
-- namespace) so that `IFC.Event` can carry an `outLabelPayload :
-- LabeledPayload Unit Tag_C Tag_I Tag_P` field without an import
-- cycle. This file (`PayloadDiscipline.lean`) imports IFC.lean and
-- continues to own:
--   * `LabeledPayload.compose` (the SDK-boundary primitive)
--   * `compose_label_joins` (the structural correctness lemma)
--   * `payload_discipline_implies_label_join` (named theorem)
--   * `holds` re-export of `IFC.PayloadDiscipline.holds`
--
-- The structure type itself is now `AgentKernel.IFC.LabeledPayload`
-- (visible here unqualified via `open AgentKernel.IFC` above).
-- Mirrors the `PayloadDiscipline.holds` defined-in-IFC pattern from

namespace LabeledPayload
  variable {Bytes Tag_C Tag_I Tag_P : Type}

  
  def compose
      (concat : Bytes → Bytes → Bytes)
      (p1 p2 : LabeledPayload Bytes Tag_C Tag_I Tag_P)
      : LabeledPayload Bytes Tag_C Tag_I Tag_P :=
    { payload := concat p1.payload p2.payload
    , label   := Label.join p1.label p2.label }

end LabeledPayload

-- ============================================================
-- Named theorems
-- ============================================================


theorem payload_discipline_implies_label_join
    {Tag_C Tag_I Tag_P : Type}
    (t : Trace Tag_C Tag_I Tag_P)
    (hPD : holds t) :
    ∀ e ∈ t, e.kind ≠ Kind.declassify → e.kind ≠ Kind.declassMint →
      Factor.leq
        (Factor.join e.inLabel.prov e.ctxLabel.prov)
        e.outLabel.prov := by
  intro e he hkind hmint
  have hEq := hPD e he hkind hmint
  -- hEq : e.outLabel.prov = Factor.join e.inLabel.prov e.ctxLabel.prov
  -- Goal: Factor.leq (Factor.join ...) e.outLabel.prov
  -- Rewrite goal using hEq: Factor.leq (join) (join), which is reflexivity.
  rw [hEq]
  intro tag h
  exact h


theorem compose_label_joins
    {Bytes Tag_C Tag_I Tag_P : Type}
    (concat : Bytes → Bytes → Bytes)
    (p1 p2 : LabeledPayload Bytes Tag_C Tag_I Tag_P) :
    (LabeledPayload.compose concat p1 p2).label =
      Label.join p1.label p2.label := by
  rfl

end AgentKernel.PayloadDiscipline

-- ============================================================
-- ============================================================
-- Mirrors IFC.lean / Bridge.M{4,5,6,7}.lean conventions: in-file
-- via `lake env lean MeasureAxioms.lean` or `lake build` log; this
-- block surfaces them at the PayloadDiscipline namespace boundary.

#print axioms AgentKernel.PayloadDiscipline.payload_discipline_implies_label_join
#print axioms AgentKernel.PayloadDiscipline.compose_label_joins
