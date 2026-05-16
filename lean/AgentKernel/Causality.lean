-- AgentKernel.Causality -- M2 v0.2
-- Layer 0, Module 2 of CTRLMATRIX. T6 (causality acyclicity).

-- parent-namespace `AgentKernel.KernelOrTenant` enum into scope for
-- `Causality.Event.author : KernelOrTenant := .tenant`. The import
-- This does NOT change the build job count (18 jobs) — modules are
-- files, not import-graph nodes.
import AgentKernel.Replay



namespace AgentKernel.Causality

structure Event where
  id             : Nat
  parents        : List Nat
  parents_older  : ∀ p ∈ parents, p < id
  kernelAuthored : Bool := false
  author         : KernelOrTenant := KernelOrTenant.tenant
  -- side-table. Mirrors Replay.Event.SpawnedBy. Default `none`
  -- preserves all existing record-literal call sites byte-unchanged
  -- cross-cell happens-before constructor will read this field; the
  --  contribution is the structural availability + the
  -- wellFormedSpawnedBy_M2 predicate below.
  SpawnedBy      : Option Nat := none
  -- Mirrors Replay.Event.retractTarget. Default `none` preserves all
  -- existing record-literal call sites byte-unchanged. The L0
  -- structural binding is wellFormedRetraction (defined on
  -- Replay.Event); this mirror is for projection-preservation under
  -- toCausality.
  retractTarget  : Option Nat := none
  -- Mirrors Replay.Event.tenant + SystemEvent.tenant. Default `none`
  -- preserves all existing record-literal call sites byte-unchanged.
  -- Threaded through `SystemEvent.toCausality`; the field is the
  -- structural target of `SystemEvent.toCausality_preserves_tenant`
  -- import (line 11) makes `Replay.TenantId` directly accessible —
  -- no Nat substitution needed (cf. Replay.lean:506 import-cycle-
  -- safety precedent which applies only at the Replay.Event field
  -- declaration, not here at the Causality.Event mirror).
  tenant         : Option Replay.TenantId := none

abbrev World := List Event

def DirectParent (W : World) (a b : Nat) : Prop :=
  ∃ e ∈ W, e.id = b ∧ a ∈ e.parents


inductive HappensBefore (W : World) : Nat → Nat → Prop where
  | step  {a b   : Nat} : DirectParent W a b → HappensBefore W a b
  | trans {a b c : Nat} : HappensBefore W a b → HappensBefore W b c → HappensBefore W a c
  | cross_cell_step {p : Nat} {e : Event} :
      e ∈ W →
      e.SpawnedBy = some p →
      p < e.id →
      e.kernelAuthored = true →
      HappensBefore W p e.id

theorem happens_before_lt {W : World} {a b : Nat}
    (h : HappensBefore W a b) : a < b := by
  induction h with
  | @step x y hp =>
    have ⟨e, _, hid, hmem⟩ := hp
    have h_lt : x < e.id := e.parents_older x hmem
    omega
  | @trans x y z _ _ ih1 ih2 => omega
  | @cross_cell_step p e _ _ hLt _ => exact hLt

theorem causality_acyclic (W : World) (a : Nat) :
    ¬ HappensBefore W a a := by
  intro h
  exact Nat.lt_irrefl a (happens_before_lt h)

-- ============================================================
-- ============================================================


def kernelParents (W : World) (e : Event) : Prop :=
  ∀ p ∈ e.parents, ∃ pe ∈ W, pe.id = p ∧ pe.kernelAuthored = true


def causalCompleteness (W : World) : Prop :=
  ∀ e ∈ W, e.kernelAuthored = true → kernelParents W e


theorem causal_completeness_implies_acyclic_strict
    (W : World) (e : Event)
    (hW : causalCompleteness W)
    (he : e ∈ W)
    (hAuth : e.kernelAuthored = true) :
    ∀ p ∈ e.parents, ∃ pe ∈ W, pe.id = p ∧ pe.kernelAuthored = true := by
  -- Direct projection: `causalCompleteness W` applied to `e` yields
  -- `kernelParents W e`, which is exactly the statement.
  exact hW e he hAuth


theorem kernel_authored_parents_in_trace_implies_no_orphan_injection
    (W : World)
    (hW : causalCompleteness W)
    (e' : Event)
    (he' : e' ∈ W)
    (hAuth' : e'.kernelAuthored = true) :
    ∀ p ∈ e'.parents, ∃ pe ∈ W, pe.id = p := by
  -- Direct discharge via `causalCompleteness W e' he' hAuth'`:
  -- yields `kernelParents W e'`, which gives the existential
  -- (after dropping the `kernelAuthored` conjunct).
  intro p hp
  have hKP : ∀ p ∈ e'.parents, ∃ pe ∈ W, pe.id = p ∧ pe.kernelAuthored = true :=
    hW e' he' hAuth'
  obtain ⟨pe, hpe_mem, hpe_id, _⟩ := hKP p hp
  exact ⟨pe, hpe_mem, hpe_id⟩

-- ============================================================
-- ============================================================


def Event.wellFormedSpawnedBy_M2 (e : Event) : Prop :=
  e.kernelAuthored = true ∨ e.SpawnedBy = none

-- ============================================================
-- + sibling theorem wellFormedRetraction_implies_HappensBefore
-- (closes  H2 attack A2' — transitive causal-future ordering
-- for retract events via parents-direct-edge).
-- ============================================================


theorem cross_cell_step_intro {W : World} {p : Nat} {e : Event}
    (heW : e ∈ W)
    (hSp : e.SpawnedBy = some p)
    (hLt : p < e.id)
    (hKA : e.kernelAuthored = true) :
    HappensBefore W p e.id :=
  HappensBefore.cross_cell_step heW hSp hLt hKA


theorem cross_cell_step_transitive {W : World} {p e_id q : Nat}
    (h1 : HappensBefore W p e_id)
    (h2 : HappensBefore W e_id q) :
    HappensBefore W p q :=
  HappensBefore.trans h1 h2


theorem cross_cell_acyclic (W : World) (a : Nat) :
    ¬ HappensBefore W a a := by
  intro h
  exact Nat.lt_irrefl a (happens_before_lt h)


theorem cross_cell_well_founded {W : World} {a b : Nat}
    (h : HappensBefore W a b) : a < b :=
  happens_before_lt h


theorem cross_cell_step_kernel_authored {W : World} {p : Nat} {e : Event}
    (heW : e ∈ W)
    (hSp : e.SpawnedBy = some p)
    (hLt : p < e.id)
    (hKA : e.kernelAuthored = true) :
    HappensBefore W p e.id ∧ e.kernelAuthored = true :=
  ⟨HappensBefore.cross_cell_step heW hSp hLt hKA, hKA⟩




def Event.wellFormedRetraction_M2 (e : Event) : Prop :=
  ∀ tid, e.retractTarget = some tid → tid ∈ e.parents


theorem wellFormedRetraction_implies_HappensBefore
    (W : World) (e : Event) (tid : Nat)
    (heW : e ∈ W)
    (hwF : Event.wellFormedRetraction_M2 e)
    (hRet : e.retractTarget = some tid) :
    HappensBefore W tid e.id :=
  HappensBefore.step ⟨e, heW, rfl, hwF tid hRet⟩

-- ============================================================
-- predicate that no progress event has occurred in the last n
-- events of a trace") at L0.
--
-- Honest naming: `isStuck` not `frozen` per L0-properties row
-- citation. The substantive structural content is the predicate
-- definition's classification of which `Kind` constructors count
-- as PROGRESS markers, plus the "last n events" universal
-- quantification.
--
-- HONEST RESIDUALS filed at  close:
--     "progress" is a deployment-policy choice. The L0 spec
--     classifies `{exec, externalReq, externalResp}` as progress
--     based on cross-substrate cohesion with `Kind.isKernelEmit`
--     (kernel-emit IO endpoints + agent-action records).
--     Deployment may broaden/narrow per their threat model
--     (e.g., a deployment that treats `commit` as observable-
--     progress would supply a wrapper predicate at L1+).
--     L0 predicate quantifies over a single trace; composing
--     stuck-states across cells requires `Trace.union`-style
--     machinery which is L1+ runtime obligation OR future
--     v1.7+ structural redesign.
-- ============================================================


def kindIsProgressMarker : Replay.Kind → Bool
  | .exec | .externalReq | .externalResp => true
  | .spawn | .commit | .attest | .read | .write | .declassify | .cancel
  | .declassMint | .cap_mint | .retract
  | .plan | .refusal | .contractViolation
  | .session_bind | .contractRegister
  | .humanGate
  | .sample | .time => false


def Trace.isStuck (n : Nat) (t : Replay.Trace) : Prop :=
  ∀ e ∈ (t.drop (t.length - n)), kindIsProgressMarker e.kind = false


theorem isStuck_empty_trace (n : Nat) :
    Trace.isStuck n ([] : Replay.Trace) := by
  intro e he
  -- `([] : List Replay.Event).drop k = []` for any `k`; membership in `[]` is False.
  -- Use `List.drop_nil` rewrite to reduce `[].drop _ = []`, then case-on-False
  -- discharges the impossible membership in `[]`. This stays Tier 1 axiom-free
  -- (the `simp [Trace.isStuck]` form would route through `propext`).
  rw [List.drop_nil] at he
  cases he


theorem isStuck_monotone {n n' : Nat} {t : Replay.Trace}
    (hLe : n' ≤ n) (hStuck : Trace.isStuck n t) :
    Trace.isStuck n' t := by
  intro e he
  -- Goal: `kindIsProgressMarker e.kind = false` for `e ∈ t.drop (t.length - n')`.
  -- Strategy: show `e ∈ t.drop (t.length - n)` via `List.drop_subset_drop_left`,
  --   then discharge via `hStuck`.
  -- Key fact: `n' ≤ n → t.length - n ≤ t.length - n'` (Nat-sub anti-monotone).
  --   Hence `t.drop (t.length - n') ⊆ t.drop (t.length - n)`
  --   (since `drop_subset_drop_left l (h : i ≤ j) : l.drop j ⊆ l.drop i`,
  --    instantiated with `i := t.length - n`, `j := t.length - n'`).
  have hSubLe : t.length - n ≤ t.length - n' := Nat.sub_le_sub_left hLe t.length
  exact hStuck e (List.drop_subset_drop_left t hSubLe he)

end AgentKernel.Causality

#print axioms AgentKernel.Causality.causality_acyclic
#print axioms AgentKernel.Causality.causal_completeness_implies_acyclic_strict
#print axioms AgentKernel.Causality.kernel_authored_parents_in_trace_implies_no_orphan_injection
#print axioms AgentKernel.Causality.isStuck_empty_trace
#print axioms AgentKernel.Causality.isStuck_monotone
