-- Layer 0, multi-cell composition module of CTRLMATRIX.
--
-- multi-cell composition `Trace_⊎` reservation (named in
-- 40-41 P5) to L0 by giving it a Lean signature + structural
--
-- Imports:
--   - `AgentKernel.Replay` for `Trace = List Event`, `Event`, `Kind`,
--     `Trace.wellFormedSpawnedBy`, `Trace.wellFormedRetraction`.
--   - `AgentKernel.Causality` for cross-cell `HappensBefore`
--     (composes naturally under `Trace_⊎` because Causality.World is
--     `List Causality.Event`; the union-as-list view extends).
--
-- This module is INDEPENDENT of `Disclosure.lean`, `Caps.lean`, and
-- at  fold via either a new `Bridge/MultiCell.lean` or fold into
-- `Bridge/M8.lean`; Agent G () does NOT write the bridge file
-- (Agent H  ships TLA+ side `MultiCell.tla` in parallel; bridge
-- pairing happens at ).
import AgentKernel.Replay
import AgentKernel.Causality



namespace AgentKernel.MultiCell

open AgentKernel.Replay (Event Kind)

/-! ## §1 — `disjointEventIds` predicate + decidable instance -/

/-- **`Trace.disjointEventIds`** — propositional predicate asserting
    that two traces share NO event id. Per H2 attack #1 counter-
    discipline, this is the precondition that must hold before
    `Trace.union` may be invoked.

    Definition: for every `e₁ ∈ t₁` and `e₂ ∈ t₂`, `e₁.id ≠ e₂.id`.

    Tier 1 (axiom-free): pure structural conjunction over universals
    on finite lists; no `propext` needed at the predicate
    definition site. -/
def Trace.disjointEventIds (t₁ t₂ : List Event) : Prop :=
  ∀ e₁ ∈ t₁, ∀ e₂ ∈ t₂, e₁.id ≠ e₂.id

/-- **`Trace.disjointEventIdsBool`** — Bool decision procedure for
    `Trace.disjointEventIds`. Used by conformance generators (
     `multicell_disjoint.rs`) and by the `Option`-shaped
    `Trace_⊎_opt` below. Decidable via `List.all` + `Nat.decEq`.

    The `_iff` theorem `disjointEventIds_iff_disjointEventIdsBool`
    below exposes the propositional/Bool correspondence.

    Honest naming: this is a STRUCTURAL DECISION PROCEDURE, not a
    theorem. -/
def Trace.disjointEventIdsBool (t₁ t₂ : List Event) : Bool :=
  t₁.all (fun e₁ => t₂.all (fun e₂ => decide (e₁.id ≠ e₂.id)))

/-- **`disjointEventIds_iff_disjointEventIdsBool`** — STRUCTURAL
    UNFOLDING. Exposes the Bool decision procedure as the
    propositional predicate.

    Predicted Tier 2 [propext] (List.all_eq_true rewrite path
    routes through propext; honest residual disclosed at parent
    H4 close if the measured tier inflates). -/
theorem disjointEventIds_iff_disjointEventIdsBool (t₁ t₂ : List Event) :
    Trace.disjointEventIdsBool t₁ t₂ = true ↔ Trace.disjointEventIds t₁ t₂ := by
  unfold Trace.disjointEventIdsBool Trace.disjointEventIds
  simp

/-- `Decidable` instance for `Trace.disjointEventIds`. Routes through
    the Bool form. Useful for downstream code that wants to use
    `if h : disjointEventIds t₁ t₂ then ... else ...` -/
instance Trace.disjointEventIdsDecidable (t₁ t₂ : List Event) :
    Decidable (Trace.disjointEventIds t₁ t₂) :=
  decidable_of_iff (Trace.disjointEventIdsBool t₁ t₂ = true)
    (disjointEventIds_iff_disjointEventIdsBool t₁ t₂)

/-! ## §2 — `Trace.union` (Trace_⊎) and Option-shaped sibling -/


def Trace.union (t₁ t₂ : List Event) (_h : Trace.disjointEventIds t₁ t₂) :
    List Event :=
  t₁ ++ t₂

/-- Notation: `t₁ ⊎[h] t₂` for `Trace.union t₁ t₂ h`. The bracket
    surfaces the disjointness witness explicitly so the 
    cannot be accidentally written without the proof. -/
notation:65 t₁ " ⊎[" h "] " t₂:65 => Trace.union t₁ t₂ h

/-- **`Trace.union_opt`** — `Option`-shaped multi-cell composition.
    Per H2 attack #1 counter-discipline, this is the
    dynamically-dispatched form: returns `some (t₁ ++ t₂)` when the
    Bool decision procedure `disjointEventIdsBool` accepts;
    `none` otherwise.

    Used by code that must check disjointness at runtime (e.g.,
    conformance shrinkers, kernel-runtime composition arms). The
    type-system-discipline form `Trace.union` is preferred when the
    disjointness proof is statically available.

    Returns `Option (List Event)` per the plan's H2 attack #1 framing
    ("Trace_⊎ is undefined / `Option Trace` shape if not disjoint
    — make this explicit; honest-name accordingly"). -/
def Trace.union_opt (t₁ t₂ : List Event) : Option (List Event) :=
  if Trace.disjointEventIdsBool t₁ t₂ then some (t₁ ++ t₂) else none

/-- STRUCTURAL PACKAGING. When the disjointness witness is
    propositionally available, `union_opt` agrees with the headline
    `union` (modulo the `some` wrapper). Tier 2 [propext] (the
    `if` discriminator routes through the Bool/Prop bridge via
    `disjointEventIds_iff_disjointEventIdsBool`).

    Predicate: `union_opt t₁ t₂ = some (t₁ ⊎[h] t₂)`. -/
theorem Trace.union_opt_eq_union_of_disjoint
    (t₁ t₂ : List Event) (h : Trace.disjointEventIds t₁ t₂) :
    Trace.union_opt t₁ t₂ = some (Trace.union t₁ t₂ h) := by
  unfold Trace.union_opt Trace.union
  rw [if_pos ((disjointEventIds_iff_disjointEventIdsBool t₁ t₂).mpr h)]



/-- STRUCTURAL PACKAGING. `disjointEventIds` is symmetric. Tier 1
    (axiom-free) — direct rewrite over the universal-quantifier
    swap. -/
theorem Trace.disjointEventIds_symm (t₁ t₂ : List Event)
    (h : Trace.disjointEventIds t₁ t₂) :
    Trace.disjointEventIds t₂ t₁ := by
  intro e₂ he₂ e₁ he₁
  exact (h e₁ he₁ e₂ he₂).symm

/-- STRUCTURAL PACKAGING. The empty trace is disjoint from any
    trace. Tier 1 (axiom-free) — vacuous on the left universal. -/
theorem Trace.disjointEventIds_nil_left (t : List Event) :
    Trace.disjointEventIds [] t := by
  intro e₁ he₁
  exact absurd he₁ (List.not_mem_nil)

/-- STRUCTURAL PACKAGING. Symmetric form. Tier 1 (axiom-free). -/
theorem Trace.disjointEventIds_nil_right (t : List Event) :
    Trace.disjointEventIds t [] := by
  intro _ _ e₂ he₂
  exact absurd he₂ (List.not_mem_nil)

/-! ## §4 — Membership lemma for `Trace.union`

The structural fact that `e ∈ Trace.union t₁ t₂ h ↔ e ∈ t₁ ∨ e ∈ t₂`
is what the wellFormedness preservation theorems below all consume.
We name it explicitly. -/

/-- STRUCTURAL UNFOLDING. Membership in the union is membership in
    one of the inputs. Direct re-export of `List.mem_append` under
    the `Trace.union` definitional unfold.

    Predicted Tier 2 [propext] (the `Iff` introduction routes
    through `List.mem_append` which uses `propext`). -/
theorem Trace.mem_union_iff
    (t₁ t₂ : List Event) (h : Trace.disjointEventIds t₁ t₂) (e : Event) :
    e ∈ (Trace.union t₁ t₂ h) ↔ e ∈ t₁ ∨ e ∈ t₂ := by
  unfold Trace.union
  exact List.mem_append

/-! ## §5 — `traceUnion_disjoint_preserves_wellFormedSpawnedBy`

The HEADLINE Tier 2 theorem: well-formedness extends compositionally
across the disjoint union. -/


theorem traceUnion_disjoint_preserves_wellFormedSpawnedBy
    (t₁ t₂ : List Event) (h : Trace.disjointEventIds t₁ t₂)
    (h₁ : AgentKernel.Replay.Trace.wellFormedSpawnedBy t₁)
    (h₂ : AgentKernel.Replay.Trace.wellFormedSpawnedBy t₂) :
    AgentKernel.Replay.Trace.wellFormedSpawnedBy (Trace.union t₁ t₂ h) := by
  intro e he
  rw [Trace.mem_union_iff] at he
  cases he with
  | inl h_in_1 => exact h₁ e h_in_1
  | inr h_in_2 => exact h₂ e h_in_2

/-! ## §6 — `traceUnion_disjoint_preserves_wellFormedRetraction`

The retraction case is more subtle than `wellFormedSpawnedBy`
because 's `Event.wellFormedRetraction t e` clauses (b) and (c)
quantify over the trace argument `t` — see H2 attack #4. We state
the theorem at the **union level**: the hypothesis is that each
event was already well-formed under the union's view, not under
the per-side view. This is the natural form when the kernel emits
the union in the first place; it preserves the L0 structural
content without inheriting the cross-trace retraction obligations
that live at L1+. -/


theorem traceUnion_disjoint_preserves_wellFormedRetraction
    (t₁ t₂ : List Event) (h : Trace.disjointEventIds t₁ t₂)
    (h₁ : ∀ e ∈ t₁,
            AgentKernel.Replay.Event.wellFormedRetraction
              (Trace.union t₁ t₂ h) e)
    (h₂ : ∀ e ∈ t₂,
            AgentKernel.Replay.Event.wellFormedRetraction
              (Trace.union t₁ t₂ h) e) :
    AgentKernel.Replay.Trace.wellFormedRetraction (Trace.union t₁ t₂ h) := by
  intro e he
  rw [Trace.mem_union_iff] at he
  cases he with
  | inl h_in_1 => exact h₁ e h_in_1
  | inr h_in_2 => exact h₂ e h_in_2

/-! ## §7 — Sibling theorem connecting `Trace_⊎` with cross-cell `HappensBefore`

Per the prompt's optional sibling theorem requirement: the union
preserves cross-cell causality witnesses from .

The Causality-side world `W` is `List Causality.Event`; we work at
the Causality-Event level here (the projection
`SystemEvent.toCausality` from `System.lean` is already the
established threading path). The key structural fact: any
`HappensBefore W₁ a b` extends to `HappensBefore (W₁ ++ W₂) a b`
(adding events to the world cannot invalidate an existing
happens-before relation). -/


theorem causalityWorld_union_extends_HappensBefore
    (W₁ W₂ : AgentKernel.Causality.World) {a b : Nat}
    (h : AgentKernel.Causality.HappensBefore W₁ a b) :
    AgentKernel.Causality.HappensBefore (W₁ ++ W₂) a b := by
  induction h with
  | @step x y hp =>
    obtain ⟨e, heW₁, hid, hmem⟩ := hp
    exact AgentKernel.Causality.HappensBefore.step
            ⟨e, List.mem_append.mpr (Or.inl heW₁), hid, hmem⟩
  | @trans x y z _ _ ih1 ih2 =>
    exact AgentKernel.Causality.HappensBefore.trans ih1 ih2
  | @cross_cell_step p e heW₁ hSp hLt hKA =>
    exact AgentKernel.Causality.HappensBefore.cross_cell_step
            (List.mem_append.mpr (Or.inl heW₁)) hSp hLt hKA


theorem traceUnion_preserves_cross_cell_HappensBefore
    (W₁ W₂ : AgentKernel.Causality.World) {p : Nat}
    {e : AgentKernel.Causality.Event}
    (heW : e ∈ W₁)
    (hSp : e.SpawnedBy = some p)
    (hLt : p < e.id)
    (hKA : e.kernelAuthored = true) :
    AgentKernel.Causality.HappensBefore (W₁ ++ W₂) p e.id :=
  AgentKernel.Causality.HappensBefore.cross_cell_step
    (List.mem_append.mpr (Or.inl heW)) hSp hLt hKA

end AgentKernel.MultiCell
