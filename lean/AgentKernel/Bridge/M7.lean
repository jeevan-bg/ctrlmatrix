import AgentKernel.Disclosure



namespace AgentKernel.Bridge.M7

open AgentKernel.Disclosure

/-! ## M7State — Lean record analogue of TLA+'s three variables

  TLA+ M7 carries three set-valued variables:
    `committed`   : SUBSET [vec, c]
    `revealed`    : SUBSET [c, i, v, p]
    `verifiedSet` : SUBSET [c, i, v, p]

  We use `List` rather than `Finset` because no `[DecidableEq V]`
  / `[DecidableEq C]` / `[DecidableEq P]` is assumed at the bridge
  level — the typeclass `VectorCommitmentScheme` carries no
  decidable-equality requirement. The set vs list refinement is
  inherited from §8 and is a separable TCB obligation (flagged
  in the probe report; not closed here).

  Field shapes:
    `committed`   : `List (List V × C)`         — pairs (vec, c)
    `revealed`    : `List (C × Nat × V × P)`    — quadruples
    `verifiedSet` : `List (C × Nat × V × P)`    — quadruples

  The `C` field is placed first in revealed/verifiedSet to mirror
  Disclosure.tla's `[c, i, v, p]` field ordering.
-/

structure M7State (V C P : Type) : Type where
  committed   : List (List V × C)
  revealed    : List (C × Nat × V × P)
  verifiedSet : List (C × Nat × V × P)

/-- Initial M7 state: all three lists empty. Mirrors `Init`
    in `Audit/Disclosure.tla`. -/
def M7State.init (V C P : Type) : M7State V C P :=
  { committed := [], revealed := [], verifiedSet := [] }



inductive ActionLabel_M7 (V C P : Type) : Type where
  | commit
      (xs : List V)
      (c : C) :
      ActionLabel_M7 V C P
  | reveal
      (xs : List V)
      (c : C)
      (i : Nat)
      (v : V)
      (p : P) :
      ActionLabel_M7 V C P
  | verifyDisclosure
      (c : C)
      (i : Nat)
      (v : V)
      (p : P) :
      ActionLabel_M7 V C P

/-! ## Per-arm pre/post predicates

  Each `Next` disjunct's pre/post, transcribed onto Lean's
  `M7State` shape. The `[VectorCommitmentScheme V C P]` instance
  is the **load-bearing typeclass parameter** — `commit` and
  `verify` are typeclass projections, not closed-over functions.
  This is the content M5 lacked.
-/

/-- TLA+ `CommitAction` arm transcribed.
    Pre: (none beyond the witness payload)
    Post: `committed' = committed ∪ {[vec ↦ xs, c ↦ commit xs]}`,
    `revealed`/`verifiedSet` unchanged.

    The TLA+ side uses an identity mock (`Commit(xs) = xs`) at
    `Disclosure.tla`; the Lean bridge replaces this with the
    abstract typeclass call `commit xs`. The `c` payload is
    pinned to `commit xs` by the post-state equation, so the
    TLA+ identity-mock is one valid instance among many.

    The post is asserted as a list-cons (extension at head),
    not a list-equality, to keep the proof obligations local
    to the new entry. -/
def CommitStep
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (xs : List V)
    (c : C)
    (s' : M7State V C P) : Prop :=
  c = VectorCommitmentScheme.commit (V := V) (C := C) (P := P) xs ∧
  s'.committed   = (xs, c) :: s.committed ∧
  s'.revealed    = s.revealed ∧
  s'.verifiedSet = s.verifiedSet

/-- TLA+ `RevealAction` arm transcribed.
    Pre: an entry `(xs, c)` is in `committed`; `i ∈ DOMAIN xs`
    (Lean: `i < xs.length`); `v = xs[i]`; `p` is a witness
    proof carried in the constructor.
    Post: `revealed' = revealed ∪ {[c, i, v, p]}`,
    `committed`/`verifiedSet` unchanged.

    The TLA+ side constructs `p = "proof"` (a constant); the
    Lean bridge carries `p` as an existential payload (any P-typed
    witness). This is strictly more permissive than the TLA+
    mock — but the verifier-side `VerifyDisclosureAction` still
    gates on `verify c i v p = true`, so the looser reveal does
    not weaken the overall bridge soundness. -/
def RevealStep
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (xs : List V)
    (c : C)
    (i : Nat)
    (v : V)
    (p : P)
    (s' : M7State V C P) : Prop :=
  (xs, c) ∈ s.committed ∧
  (∃ h : i < xs.length, v = xs.get ⟨i, h⟩) ∧
  s'.committed   = s.committed ∧
  s'.revealed    = (c, i, v, p) :: s.revealed ∧
  s'.verifiedSet = s.verifiedSet

/-- TLA+ `VerifyDisclosureAction` arm transcribed.
    Pre: a quadruple `(c, i, v, p)` is in `revealed`; the
    typeclass `verify c i v p = true`.
    Post: `verifiedSet' = verifiedSet ∪ {(c, i, v, p)}`,
    `committed`/`revealed` unchanged.

    **The verify-true precondition is the M7-substantive part**:
    it invokes the `[VectorCommitmentScheme]` typeclass method
    on the abstract scheme. The closure-preservation lemma
    `VerifyDisclosureAction_preserves_inv` consumes this
    precondition structurally (no `decide`), which is what
    distinguishes M7's bridge content from M5's. -/
def VerifyDisclosureStep
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (c : C)
    (i : Nat)
    (v : V)
    (p : P)
    (s' : M7State V C P) : Prop :=
  (c, i, v, p) ∈ s.revealed ∧
  VectorCommitmentScheme.verify (V := V) (C := C) (P := P) c i v p = true ∧
  s'.committed   = s.committed ∧
  s'.revealed    = s.revealed ∧
  s'.verifiedSet = (c, i, v, p) :: s.verifiedSet



/-- The TLA+-side step. One arm per `ActionLabel_M7` constructor;
    each arm's body is the disjunct's pre/post transcribed.
    The `[VectorCommitmentScheme V C P]` parameter is the
    load-bearing typeclass content — the bridge holds for any
    instance. -/
def TLAStep_M7
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (a : ActionLabel_M7 V C P)
    (s' : M7State V C P) : Prop :=
  match a with
  | ActionLabel_M7.commit xs c =>
      CommitStep s xs c s'
  | ActionLabel_M7.reveal xs c i v p =>
      RevealStep s xs c i v p s'
  | ActionLabel_M7.verifyDisclosure c i v p =>
      VerifyDisclosureStep s c i v p s'

/-! ## LeanStep_M7

  Defined as the existential closure of `TLAStep_M7` over
  `ActionLabel_M7`. Mirrors the M5 pattern. The Lean side at M7
  has T8 / T8' as **structural theorems** but no independent
  Lean-side stepping content — the structural theorems quantify
  over arbitrary disclosures, not over reachable states of a
  Lean-side transition system. So at the bridge level the iff
  reduces to the M5 shape.

  The substantive M7 content lives in the closure-preservation
  lemmas below — particularly `VerifyDisclosureAction_preserves_inv`
  which structurally consumes the typeclass `verify` call.
-/

/-- The Lean-side step relation. Defined as the existential
    closure of `TLAStep_M7`. Universally quantified over the
    `[VectorCommitmentScheme V C P]` typeclass. -/
def LeanStep_M7
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s s' : M7State V C P) : Prop :=
  ∃ a : ActionLabel_M7 V C P, TLAStep_M7 s a s'



/-- **BridgeSound_M7.** `LeanStep_M7` is exactly the existential
    closure of `TLAStep_M7`, by definition. The iff holds
    reflexively. The typeclass parameter is required to *state*
    the theorem (`TLAStep_M7` invokes typeclass methods); the
    *proof* is `Iff.rfl` because of how `LeanStep_M7` is defined.

    This is the same shape as `BridgeSound_M5` — the M7-specific
    typeclass content lives in the closure-preservation lemmas
    below, not in this iff. -/
theorem BridgeSound_M7
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s s' : M7State V C P) :
    LeanStep_M7 s s'
      ↔ ∃ a : ActionLabel_M7 V C P, TLAStep_M7 s a s' :=
  Iff.rfl

/-! ## Disclosure invariant

  The Lean analogue of TLA+'s `DisclosureCorrectness` invariant
  (every verified opening verifies against the abstract scheme).
  Mirrors `AgentKernel.Disclosure.Disclosure.consistent` shape
  but lifted to the M7State's `verifiedSet` field.

  This is the structural invariant the closure-preservation
  lemmas show is preserved by every action arm.
-/

/-- The disclosure invariant: every quadruple in `verifiedSet`
    verifies under the abstract scheme. Mirrors
    `Disclosure.tla`'s `DisclosureCorrectness` invariant
    transcribed onto the bridge state. -/
def M7State.invariant
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P) : Prop :=
  ∀ q ∈ s.verifiedSet,
    VectorCommitmentScheme.verify (V := V) (C := C) (P := P)
      q.1 q.2.1 q.2.2.1 q.2.2.2 = true

/-! ## Closure preservation — `CommitAction`

  `CommitAction` updates `committed`; `verifiedSet` is unchanged.
  The invariant transfers verbatim.

  No typeclass content beyond *invoking* `commit xs` to bind the
  new commitment. The `verify` invariant is on `verifiedSet`;
  `CommitAction` does not touch `verifiedSet`. Trivial preservation.
-/

/-- `M7State.invariant` is preserved by `CommitStep`. Trivially:
    `CommitStep` leaves `verifiedSet` unchanged, so the
    invariant transfers from `s` to `s'` by rewriting
    `s'.verifiedSet = s.verifiedSet`. -/
theorem CommitAction_preserves_inv
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (xs : List V)
    (c : C)
    (s' : M7State V C P)
    (hInv : M7State.invariant s)
    (hStep : CommitStep s xs c s') :
    M7State.invariant s' := by
  obtain ⟨_hCommit, _hCommitted, _hRevealed, hVerified⟩ := hStep
  intro q hMem
  rw [hVerified] at hMem
  exact hInv q hMem

/-! ## Closure preservation — `RevealAction`

  `RevealAction` updates `revealed`; `verifiedSet` is unchanged.
  The invariant transfers verbatim.

  No typeclass content for the invariant proof (the precondition
  about `xs` having index `i` is not consumed for invariant
  preservation — `verifiedSet` is untouched).
-/

/-- `M7State.invariant` is preserved by `RevealStep`. Trivially:
    `RevealStep` leaves `verifiedSet` unchanged. -/
theorem RevealAction_preserves_inv
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (xs : List V)
    (c : C)
    (i : Nat)
    (v : V)
    (p : P)
    (s' : M7State V C P)
    (hInv : M7State.invariant s)
    (hStep : RevealStep s xs c i v p s') :
    M7State.invariant s' := by
  -- RevealStep unfolds to:
  --   (xs,c) ∈ committed ∧ (∃ h : i < xs.length, v = xs.get ⟨i,h⟩) ∧
  --   s'.committed = s.committed ∧ s'.revealed = ... ∧
  --   s'.verifiedSet = s.verifiedSet
  obtain ⟨_hCommittedMem, _hLen, _hCommittedEq, _hRevealedEq, hVerified⟩ := hStep
  intro q hMem
  rw [hVerified] at hMem
  exact hInv q hMem

/-! ## Closure preservation — `VerifyDisclosureAction`

  **The substantive lemma.** `VerifyDisclosureAction` extends
  `verifiedSet` with a new entry `(c, i, v, p)`; the new entry's
  inclusion in the invariant requires `verify c i v p = true`,
  which is exactly the action's precondition.

  This is where the M7 bridge's typeclass content appears: the
  proof structurally consumes the typeclass `verify` call in the
  precondition (without `decide`, without specializing the
  instance). The proof is universally quantified over the
  typeclass; it holds for any scheme — trivial or non-trivial.

  This is the lemma that distinguishes M7's bridge content from
  M5's. M5's preservation lemmas case-split on `if cid = newId`
  for the new entry's well-formedness; M7's preservation lemma
  for `VerifyDisclosureAction` extracts `verify ... = true`
  directly from the precondition.
-/

/-- `M7State.invariant` is preserved by `VerifyDisclosureStep`.
    The new entry `(c, i, v, p)` is added to `verifiedSet`; its
    invariant obligation (`verify c i v p = true`) is
    discharged from the action's precondition.

    The proof: case-split on whether the queried entry is the
    new one or an existing one. New: extract from precondition.
    Existing: lift from `hInv`. **The typeclass method `verify`
    is invoked structurally in the goal**, not unfolded via
    `decide`; the proof is parametric in the scheme instance. -/
theorem VerifyDisclosureAction_preserves_inv
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (c : C)
    (i : Nat)
    (v : V)
    (p : P)
    (s' : M7State V C P)
    (hInv : M7State.invariant s)
    (hStep : VerifyDisclosureStep s c i v p s') :
    M7State.invariant s' := by
  obtain ⟨_hRevMem, hVerify, _hCommittedEq, _hRevealedEq, hVerified⟩ := hStep
  intro q hMem
  rw [hVerified] at hMem
  -- hMem : q ∈ (c, i, v, p) :: s.verifiedSet
  rcases List.mem_cons.mp hMem with hHead | hTail
  · -- q is the newly verified entry; its verify-truth is hVerify.
    subst hHead
    exact hVerify
  · -- q is a pre-existing verified entry; lift from hInv.
    exact hInv q hTail

/-! ## Closure preservation across the bridge

  Every step expressible as `LeanStep_M7` (equivalently
  `∃ a, TLAStep_M7 .. a ..`) preserves `M7State.invariant`.

  This is the structural-content lemma the bridge buys: M7's
  operational disclosure-correctness invariant (`DisclosureCorrectness`
  in TLA+, TLC-checked at 160,000 distinct states / depth 27 / 12s
  wall) is matched on the Lean side by the same invariant
  preserved across every disjunct of the step relation —
  parametric in the typeclass instance.
-/

/-- **Closure preservation across the bridge.** Every
    `LeanStep_M7` preserves `M7State.invariant`. Case-split on
    the action label, dispatch to per-arm lemma. -/
theorem LeanStep_M7_preserves_inv
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s s' : M7State V C P)
    (hInv : M7State.invariant s)
    (hStep : LeanStep_M7 s s') :
    M7State.invariant s' := by
  obtain ⟨a, hStep⟩ := hStep
  cases a with
  | commit xs c =>
      have hStep' : CommitStep s xs c s' := hStep
      exact CommitAction_preserves_inv s xs c s' hInv hStep'
  | reveal xs c i v p =>
      have hStep' : RevealStep s xs c i v p s' := hStep
      exact RevealAction_preserves_inv s xs c i v p s' hInv hStep'
  | verifyDisclosure c i v p =>
      have hStep' : VerifyDisclosureStep s c i v p s' := hStep
      exact VerifyDisclosureAction_preserves_inv s c i v p s' hInv hStep'

/-! ## Typeclass-method exposure check

  A sanity property: the bridge does invoke each of the three
  `VectorCommitmentScheme` operations (`commit`, `open_`,
  `verify`) somewhere in its definition. If a stepping arm
  silently dropped a typeclass method, the bridge would be
  weaker than advertised.

  Two such checks are mechanizable here:
    * `commit_method_used` — `CommitStep` pins the post-state
      commitment to `VectorCommitmentScheme.commit xs`.
    * `verify_method_used` — `VerifyDisclosureStep`'s
      precondition is `VectorCommitmentScheme.verify c i v p =
      true`.

  `open_` is not invoked in the operational arms (TLA+'s
  `Disclosure.tla` constructs proofs as a constant `"proof"`
  rather than calling `Open(xs, i)`; the operational shape
  doesn't exercise the `open_` projection). This is honest
  reporting: M7's TLA+ side does not exercise `open_`, so
  neither does the bridge. The Lean structural side (T8 / T8')
  uses `verify` only.
-/

/-- The `commit` typeclass method is invoked by `CommitStep`. -/
theorem commit_method_used
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (xs : List V)
    (c : C)
    (s' : M7State V C P)
    (hStep : CommitStep s xs c s') :
    c = VectorCommitmentScheme.commit (V := V) (C := C) (P := P) xs :=
  hStep.1

/-- The `verify` typeclass method is invoked by
    `VerifyDisclosureStep`. -/
theorem verify_method_used
    {V C P : Type}
    [VectorCommitmentScheme V C P]
    (s : M7State V C P)
    (c : C)
    (i : Nat)
    (v : V)
    (p : P)
    (s' : M7State V C P)
    (hStep : VerifyDisclosureStep s c i v p s') :
    VectorCommitmentScheme.verify (V := V) (C := C) (P := P) c i v p = true :=
  hStep.2.1

/-! ## Initial-state invariant

  The initial state satisfies the invariant trivially:
  `verifiedSet = []` so the universal quantifier is vacuous.
-/

/-- The invariant holds at `M7State.init`. Vacuous: empty
    `verifiedSet`. -/
theorem M7State.init_invariant
    {V C P : Type}
    [VectorCommitmentScheme V C P] :
    M7State.invariant (M7State.init V C P) := by
  intro q hMem
  -- M7State.init's verifiedSet is [], so hMem : q ∈ [] is impossible.
  cases hMem

end AgentKernel.Bridge.M7

-- ============================================================
-- `lake env lean MeasureAxioms.lean` or `#print axioms` in
-- editor; this file is wired into the AgentKernel target via
-- AgentKernel.lean's import list at H3 close).
-- ============================================================

#print axioms AgentKernel.Bridge.M7.BridgeSound_M7
#print axioms AgentKernel.Bridge.M7.CommitAction_preserves_inv
#print axioms AgentKernel.Bridge.M7.RevealAction_preserves_inv
#print axioms AgentKernel.Bridge.M7.VerifyDisclosureAction_preserves_inv
#print axioms AgentKernel.Bridge.M7.LeanStep_M7_preserves_inv
#print axioms AgentKernel.Bridge.M7.commit_method_used
#print axioms AgentKernel.Bridge.M7.verify_method_used
#print axioms AgentKernel.Bridge.M7.M7State.init_invariant
