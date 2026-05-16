import AgentKernel.Replay



namespace AgentKernel.Bridge.M1

open AgentKernel.Replay



/-- The single action label for M1: append an event to the trace.
    The constructor carries the event verbatim. Mirrors TLA+
    `AppendEvent(e)` in `tla/Core/Events.tla`. -/
inductive ActionLabel_M1 : Type where
  | appendEvent (e : Event) : ActionLabel_M1

/-! ## Per-arm pre/post

  `AppendEvent(e)` from `Events.tla`:
  ```
  AppendEvent(e) ==
      /\ Len(events) < MaxEvents
      /\ e.id = nextId
      /\ e.parents ⊆ 1..(nextId - 1)
      /\ e.prevHash = chainHead
      /\ events' = Append(events, e)
      /\ nextId' = nextId + 1
      /\ chainHead' = H(e)
  ```

  Lean translation:
  * `Len(events) < MaxEvents` — omitted; `Nat`-keyed list is
    unbounded on the Lean side (TLC bound is a model-checking
    artifact). Same scoping decision as M5 / M6 / M7 bridges.
  * `e.id = nextId` becomes `e.id = t.length + 1`.
  * `e.parents ⊆ 1..(nextId - 1)` becomes
    `∀ pid ∈ e.parents, pid < t.length + 1`.
  * `e.prevHash = chainHead` — omitted; `prevHash` is not in
    `Replay.Event` (M6 alphabet, not M1).
  * `events' = Append(events, e)` becomes `t' = t ++ [e]`.
  * `nextId'`, `chainHead'` UNCHANGED-style updates collapse on
    the Lean side into the list-extension `t' = t ++ [e]`.
-/

/-- The `AppendEvent(e)` arm transcribed to Lean.
    Pre: `e.id = t.length + 1`; every parent id is strictly
    less than `e.id` (so parents reference only earlier events,
    giving topological ordering by free construction — T6
    acyclicity holds at the schema level).
    Post: `t' = t ++ [e]`.

    Note on parameter type: `Replay.Trace` is `def`-defined (not
    `abbrev`), so `HAppend Trace (List Event)` does not auto-
    resolve. We type the trace arguments as `List Event` directly
    (which is *definitionally* `Trace`) to keep the list-append
    `t ++ [e]` working without manual `show`/cast acrobatics.
    Call sites pass `Trace`-typed values, which unify
    transparently. -/
def AppendEventStep
    (t : List Event)
    (e : Event)
    (t' : List Event) : Prop :=
  e.id = t.length + 1 ∧
  (∀ pid ∈ e.parents, pid < e.id) ∧
  t' = t ++ [e]

/-! ## TLAStep_M1

  TLA+-side stepping predicate, indexed by `ActionLabel_M1`.
  Mechanical mirror of `Events.tla`'s `AppendEvent`.
-/

/-- The TLA+-side step. One arm (the `appendEvent` constructor);
    the body is `AppendEventStep`. -/
def TLAStep_M1
    (t : List Event)
    (a : ActionLabel_M1)
    (t' : List Event) : Prop :=
  match a with
  | ActionLabel_M1.appendEvent e => AppendEventStep t e t'



/-- The Lean-side step relation. Defined as the existential
    closure of `TLAStep_M1`. -/
def LeanStep_M1 (t t' : List Event) : Prop :=
  ∃ a : ActionLabel_M1, TLAStep_M1 t a t'




theorem BridgeSound_M1 (t t' : List Event) :
    LeanStep_M1 t t' ↔ ∃ a : ActionLabel_M1, TLAStep_M1 t a t' :=
  Iff.rfl

/-! ## Closure preservation

  The non-vacuity check: M1's syntactic invariant `Trace.captured`
  (every event well-witnessed) is preserved across `AppendEventStep`
  whenever the appended event is itself well-witnessed.

  This is the structural-content lemma the bridge buys: the
  alphabet fragment has a meaningful invariant whose preservation
  is a one-line list-extension argument, demonstrating the bridge
  is not vacuous even at its `Iff.rfl` triviality.
-/

/-- `Trace.captured` is preserved by `AppendEventStep` when the
    new event is well-witnessed. The argument is direct list
    traversal: `(t ++ [e]).all wellWitnessed ↔ t.all wellWitnessed
    ∧ wellWitnessed e`. -/
theorem AppendEventStep_preserves_captured
    (t : List Event)
    (e : Event)
    (t' : List Event)
    (hCaptured : Trace.captured t = true)
    (hWit : Event.wellWitnessed e = true)
    (hStep : AppendEventStep t e t') :
    Trace.captured t' = true := by
  obtain ⟨_, _, hAppend⟩ := hStep
  subst hAppend
  -- Goal: (t ++ [e]).captured = true
  unfold Trace.captured at hCaptured ⊢
  -- List.all over append: (t ++ [e]).all p = t.all p && [e].all p
  rw [List.all_append]
  simp [hCaptured, hWit]

/-- **Closure preservation across the bridge.** Every step
    expressible as `LeanStep_M1` (equivalently `∃ a, TLAStep_M1
    .. a ..`) preserves `Trace.captured` under the per-event
    well-witnessedness precondition. Demonstrates non-vacuity
    of the M1 bridge. -/
theorem LeanStep_M1_preserves_captured
    (t t' : List Event)
    (hCaptured : Trace.captured t = true)
    (hStep : LeanStep_M1 t t')
    (hWit : ∀ e : Event, (∃ a : ActionLabel_M1,
              a = ActionLabel_M1.appendEvent e ∧
              TLAStep_M1 t a t') → Event.wellWitnessed e = true) :
    Trace.captured t' = true := by
  obtain ⟨a, hStep⟩ := hStep
  cases a with
  | appendEvent e =>
      have hStep' : AppendEventStep t e t' := hStep
      have hWitE : Event.wellWitnessed e = true :=
        hWit e ⟨ActionLabel_M1.appendEvent e, rfl, hStep'⟩
      exact AppendEventStep_preserves_captured t e t'
              hCaptured hWitE hStep'

end AgentKernel.Bridge.M1

-- ============================================================
-- `lake env lean AgentKernel/Bridge/M1.lean`. Expected: Tier 1
-- (axiom-free) for `BridgeSound_M1` (`Iff.rfl`) and the
-- preservation lemma (one `subst` + `simp` over `List.all_append`,
-- which is axiom-free in Lean 4 core).
-- ============================================================

#print axioms AgentKernel.Bridge.M1.BridgeSound_M1
#print axioms AgentKernel.Bridge.M1.AppendEventStep_preserves_captured
#print axioms AgentKernel.Bridge.M1.LeanStep_M1_preserves_captured
