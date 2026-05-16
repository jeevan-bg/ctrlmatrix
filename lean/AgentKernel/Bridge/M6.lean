import AgentKernel.Log



namespace AgentKernel.Bridge.M6

open AgentKernel.Log

/-! ## ActionLabel_M6

  Inductive type with constructors equal to the disjuncts of
  `Log.tla`'s `Next_M6 == \E b ∈ Bytes : AppendEntry(b) ∨ PublishRoot`.

  * `appendEntry b` — appends a fresh entry whose payload is `b`
    and whose `prev` field is pinned to the current chain root.
  * `publishRoot` — stutter on the Lean side; reserved hook for
    L1+ transparency-log abstraction.
-/
inductive ActionLabel_M6 (Bytes : Type) : Type where
  | appendEntry (b : Bytes) : ActionLabel_M6 Bytes
  | publishRoot             : ActionLabel_M6 Bytes

/-! ## Per-arm pre/post predicates

  Each `Next_M6` disjunct's pre/post transcribed onto Lean's
  `LogChain` shape.

  Cardinality bound `MaxLen`: omitted on the Lean side per the
  probe-report's deliberate scope — `List` is unbounded; the
  bound is a TLC-only model-checking artifact.
-/

/-- TLA+ `AppendEntry(b)` arm transcribed.
    Post: `chain' = chain ++ [{prev := root chain, payload := b}]`.
    The `prev` field is pinned to the current chain root by
    construction (matching `Log.tla`'s `Append(chain, [prev |->
    Root(chain), payload |-> b])`). -/
def AppendStep
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (chain : LogChain Bytes Hash)
    (b : Bytes)
    (chain' : LogChain Bytes Hash) : Prop :=
  chain' = chain ++ [{ prev := LogChain.root H genesis serialize chain,
                       payload := b }]

/-- TLA+ `PublishRoot` arm transcribed.
    Pre: none.
    Post: `chain' = chain` (UNCHANGED chain). -/
def PublishRootStep
    {Bytes Hash : Type}
    (chain chain' : LogChain Bytes Hash) : Prop :=
  chain' = chain

/-! ## TLAStep_M6

  Per-arm TLA+-side stepping predicate, indexed by an
  `ActionLabel_M6`. Mechanical mirror of `Next_M6`'s disjuncts.
-/

/-- The TLA+-side step. One arm per `ActionLabel_M6` constructor;
    each arm's body is the disjunct's pre/post transcribed. -/
def TLAStep_M6
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (chain : LogChain Bytes Hash)
    (a : ActionLabel_M6 Bytes)
    (chain' : LogChain Bytes Hash) : Prop :=
  match a with
  | ActionLabel_M6.appendEntry b => AppendStep H genesis serialize chain b chain'
  | ActionLabel_M6.publishRoot   => PublishRootStep chain chain'

/-! ## LeanStep_M6

  The Lean-side step. **Defined independently as the structural
  disjunction** (NOT as `∃ a, TLAStep_M6 ..`). This is the key
  design choice distinguishing M6 from M5.

  At M5, `LeanStep_M5` was the existential closure of `TLAStep_M5`
  by construction, so `BridgeSound_M5` was `Iff.rfl`. At M6, the
  Lean side has independent structural content
  (`LogChain.wellFormed` is a non-trivial inductive invariant
  preserved by chain extension; the chain-extension shape itself
  is the operational primitive). We mirror that here: the Lean
  step says "either the chain grew by one entry whose `prev`
  matches the current root, or the chain stayed the same."

  The bridge theorem then has two non-trivial proof obligations:
  forward (extract a label from a structural disjunct) and
  backward (extract a structural disjunct from a label). Neither
  reduces to `Iff.rfl`.
-/

/-- The Lean-side step relation. Defined structurally: either
    chain extension with hash-pinned `prev`, or stutter. -/
def LeanStep_M6
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (chain chain' : LogChain Bytes Hash) : Prop :=
  (∃ b : Bytes,
      chain' = chain ++ [{ prev := LogChain.root H genesis serialize chain,
                           payload := b }])
  ∨ chain' = chain

/-! ## BridgeSound_M6

  The bridge soundness theorem. Statement:
  `LeanStep_M6 chain chain' ↔ ∃ a, TLAStep_M6 chain a chain'`.

  By the independent definition of `LeanStep_M6`, the two sides
  are NOT definitionally equal. The proof is `Iff.intro` with
  case-analysis on each side. Forward: case-split on the
  disjunct, witness `appendEntry b` or `publishRoot`. Backward:
  case-split on the action label, derive the structural disjunct.

  **This is the substantive iff content M5 lacked.** Each
  direction unpacks/repacks the same equality, but the unpacking
  is a real (non-`rfl`) computation step.
-/

/-- **BridgeSound_M6.** The Lean-side structural step relation
    is iff-equivalent to the existential closure of the TLA+-side
    per-arm steps. Substantive iff content (NOT `Iff.rfl`); proof
    is `Iff.intro` with case-analysis on both sides. -/
theorem BridgeSound_M6
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (chain chain' : LogChain Bytes Hash) :
    LeanStep_M6 H genesis serialize chain chain'
      ↔ ∃ a : ActionLabel_M6 Bytes,
            TLAStep_M6 H genesis serialize chain a chain' := by
  constructor
  · -- Forward: structural disjunct → existential label
    intro hStep
    cases hStep with
    | inl hAppend =>
        obtain ⟨b, hEq⟩ := hAppend
        refine ⟨ActionLabel_M6.appendEntry b, ?_⟩
        -- TLAStep_M6 .. (appendEntry b) .. ≡ AppendStep .. by defn
        show AppendStep H genesis serialize chain b chain'
        unfold AppendStep
        exact hEq
    | inr hStutter =>
        refine ⟨ActionLabel_M6.publishRoot, ?_⟩
        -- TLAStep_M6 .. publishRoot .. ≡ PublishRootStep .. by defn
        show PublishRootStep chain chain'
        unfold PublishRootStep
        exact hStutter
  · -- Backward: existential label → structural disjunct
    intro hStep
    obtain ⟨a, hStep⟩ := hStep
    cases a with
    | appendEntry b =>
        have hStep' : AppendStep H genesis serialize chain b chain' := hStep
        unfold AppendStep at hStep'
        left
        exact ⟨b, hStep'⟩
    | publishRoot =>
        have hStep' : PublishRootStep chain chain' := hStep
        unfold PublishRootStep at hStep'
        right
        exact hStep'

/-! ## Closure preservation under each arm

  An honest M6 probe must demonstrate that the bridge is **not
  vacuous**: the Lean side's structural invariant
  (`LogChain.wellFormed`, the Lean form of TLA+'s
  `ChainWellFormed`) is preserved by every action arm.

  At M6 these preservation lemmas have *real* structural content:
  `AppendStep_preserves_wellFormed` consumes
  `LogChain.wellFormed_append_singleton` (the kernel-emit
  invariant from `Log.lean`, axiom-free at `[]`) which itself is
  proved by structural induction over the chain. This is the
  substantive content the bridge buys at M6 — *not* present at
  M5 because M5's invariant was monotone-by-construction at a
  fresh id rather than structurally inductive over a chain.
-/

/-- `LogChain.wellFormed` is preserved by `AppendStep`.

    The proof consumes `LogChain.wellFormed_append_singleton`
    (the kernel-emit invariant from `Log.lean`); the
    `e.prev = chain.root` precondition of that helper is
    discharged by the `AppendStep` post-state's `prev` field
    pinning. **Real structural content** — the helper itself is
    proved by induction over the chain in `Log.lean`. -/
theorem AppendStep_preserves_wellFormed
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (chain : LogChain Bytes Hash)
    (b : Bytes)
    (chain' : LogChain Bytes Hash)
    (hWF : LogChain.wellFormed H genesis serialize chain)
    (hStep : AppendStep H genesis serialize chain b chain') :
    LogChain.wellFormed H genesis serialize chain' := by
  unfold AppendStep at hStep
  rw [hStep]
  -- Goal: wellFormed (chain ++ [{prev := root chain, payload := b}])
  -- Apply LogChain.wellFormed_append_singleton with hPrev := rfl.
  exact LogChain.wellFormed_append_singleton H genesis serialize
    chain { prev := LogChain.root H genesis serialize chain, payload := b }
    hWF rfl

/-- `LogChain.wellFormed` is preserved by `PublishRootStep`.
    Trivially: `PublishRootStep` leaves the chain unchanged. -/
theorem PublishRootStep_preserves_wellFormed
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (chain chain' : LogChain Bytes Hash)
    (hWF : LogChain.wellFormed H genesis serialize chain)
    (hStep : PublishRootStep chain chain') :
    LogChain.wellFormed H genesis serialize chain' := by
  unfold PublishRootStep at hStep
  rw [hStep]
  exact hWF

/-- **Closure preservation across the bridge.** Every step
    expressible as `LeanStep_M6` (equivalently `∃ a,
    TLAStep_M6 .. a ..`) preserves `LogChain.wellFormed`.

    This is the structural-content lemma the bridge buys at M6:
    M6's operational chain-wellFormedness invariant
    (`ChainWellFormed` in TLA+, TLC-checked at 40 states
    depth 4) is matched on the Lean side by the same invariant
    preserved across every disjunct of the step relation. The
    `appendEntry` arm's preservation pulls real structural
    content via `wellFormed_append_singleton`; the `publishRoot`
    arm is trivial. -/
theorem LeanStep_M6_preserves_wellFormed
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (chain chain' : LogChain Bytes Hash)
    (hWF : LogChain.wellFormed H genesis serialize chain)
    (hStep : LeanStep_M6 H genesis serialize chain chain') :
    LogChain.wellFormed H genesis serialize chain' := by
  cases hStep with
  | inl hAppend =>
      obtain ⟨b, hEq⟩ := hAppend
      have hStep' : AppendStep H genesis serialize chain b chain' := hEq
      exact AppendStep_preserves_wellFormed H genesis serialize chain b chain'
              hWF hStep'
  | inr hStutter =>
      have hStep' : PublishRootStep chain chain' := hStutter
      exact PublishRootStep_preserves_wellFormed H genesis serialize chain chain'
              hWF hStep'

end AgentKernel.Bridge.M6

-- ============================================================
-- lean ...` or `#print axioms` in editor; this file is wired
-- into `AgentKernel.lean`'s import list at the M6 probe close).
-- ============================================================

#print axioms AgentKernel.Bridge.M6.BridgeSound_M6
#print axioms AgentKernel.Bridge.M6.AppendStep_preserves_wellFormed
#print axioms AgentKernel.Bridge.M6.PublishRootStep_preserves_wellFormed
#print axioms AgentKernel.Bridge.M6.LeanStep_M6_preserves_wellFormed
