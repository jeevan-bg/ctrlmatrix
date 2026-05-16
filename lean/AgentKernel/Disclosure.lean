

namespace AgentKernel.Disclosure

/-- Abstract vector-commitment scheme.
    The three operations (`commit`, `open_`, `verify`) are the §8
    black-box surface. Position-binding is asserted at §8: no PPT
    adversary produces a sextuple `(c, i, v, v', π, π')` with
    `v ≠ v'` and both `verify c i v π = true` and
    `verify c i v' π' = true`. The structural T8 / T8' below use
    this shape as the right disjunct's witness type. -/
class VectorCommitmentScheme (V C P : Type) where
  commit : List V → C
  open_  : List V → Nat → P
  verify : C → Nat → V → P → Bool

/-- A disclosure pairs a commitment with a list of (position,
    value, proof) openings. Mirrors the [c, i, v, p] shape of
    Disclosure.tla's verifiedSet elements (one Disclosure record
    aggregates the openings under a single commitment). -/
structure Disclosure (V C P : Type) where
  commitment : C
  openings   : List (Nat × V × P)

/-- A disclosure is consistent under a scheme iff every opening
    verifies against the commitment. Mirrors Disclosure.tla's
    DisclosureCorrectness invariant on the verifiedSet. -/
def Disclosure.consistent {V C P : Type}
    [VectorCommitmentScheme V C P]
    (d : Disclosure V C P) : Prop :=
  ∀ op ∈ d.openings,
    VectorCommitmentScheme.verify d.commitment op.1 op.2.1 op.2.2 = true


theorem t8_disclosure_soundness
    {V C P : Type}
    [DecidableEq V]
    [VectorCommitmentScheme V C P]
    (c : C) (i : Nat) (v v' : V) (π π' : P) :
    VectorCommitmentScheme.verify c i v π = true →
    VectorCommitmentScheme.verify c i v' π' = true →
    v = v' ∨
      ∃ (c₀ : C) (i₀ : Nat) (a a' : V) (p p' : P),
        a ≠ a' ∧
        VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
        VectorCommitmentScheme.verify c₀ i₀ a' p' = true := by
  intro h1 h2
  by_cases hVal : v = v'
  · exact Or.inl hVal
  · exact Or.inr ⟨c, i, v, v', π, π', hVal, h1, h2⟩

/-- Helper for T8'. Search a list `l₂` of openings against a
    fixed `head` opening, all under the same commitment `c`.

    Returns: either `head` agrees with every element of `l₂` at
    any shared position, or witnesses a position-binding
    violation against the scheme.

    Proof: induction on `l₂`. At each cons, case-split on
    position equality (`[DecidableEq Nat]`); if positions match,
    case-split on value equality (`[DecidableEq V]`). Mismatched
    values yield the violation witness immediately (rewrite
    `head.1 = op₂.1` into `hHead`, pack as sextuple); matched
    values recurse on the tail. Mismatched positions skip the
    head pair and recurse. -/
private theorem findInL₂
    {V C P : Type}
    [DecidableEq V]
    [VectorCommitmentScheme V C P]
    (c : C) (head : Nat × V × P) (l₂ : List (Nat × V × P))
    (hHead : VectorCommitmentScheme.verify c head.1 head.2.1 head.2.2 = true)
    (h₂ : ∀ op ∈ l₂,
      VectorCommitmentScheme.verify c op.1 op.2.1 op.2.2 = true) :
    (∀ op₂ ∈ l₂, head.1 = op₂.1 → head.2.1 = op₂.2.1) ∨
    ∃ (c₀ : C) (i₀ : Nat) (a a' : V) (p p' : P),
        a ≠ a' ∧
        VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
        VectorCommitmentScheme.verify c₀ i₀ a' p' = true := by
  induction l₂ with
  | nil =>
    left
    intro op₂ hMem _
    cases hMem
  | cons op₂ rest ih =>
    have hOp₂ : VectorCommitmentScheme.verify c op₂.1 op₂.2.1 op₂.2.2 = true :=
      h₂ op₂ List.mem_cons_self
    have hRest : ∀ op ∈ rest,
        VectorCommitmentScheme.verify c op.1 op.2.1 op.2.2 = true :=
      fun op hMem => h₂ op (List.mem_cons_of_mem op₂ hMem)
    by_cases hPos : head.1 = op₂.1
    · by_cases hVal : head.2.1 = op₂.2.1
      · -- positions match, values match for op₂; recurse on rest
        rcases ih hRest with hAll | hViol
        · left
          intro op hMem hPosEq
          rcases List.mem_cons.mp hMem with h | h
          · subst h; exact hVal
          · exact hAll op h hPosEq
        · right; exact hViol
      · -- positions match, values differ -- violation witnessed
        right
        rw [hPos] at hHead
        exact ⟨c, op₂.1, head.2.1, op₂.2.1, head.2.2, op₂.2.2,
               hVal, hHead, hOp₂⟩
    · -- positions differ for op₂; recurse on rest
      rcases ih hRest with hAll | hViol
      · left
        intro op hMem hPosEq
        rcases List.mem_cons.mp hMem with h | h
        · subst h; exact absurd hPosEq hPos
        · exact hAll op h hPosEq
      · right; exact hViol

/-- Helper for T8'. Search `l₁ × l₂` for a position-binding
    violation, all under the same commitment `c`.

    Returns: either every pair of openings (one from each list)
    sharing a position agrees on value, or witnesses a position-
    binding violation.

    Proof: induction on `l₁`, threading `findInL₂` at each cons.
    The head of `l₁` is searched against all of `l₂` via
    `findInL₂`; the tail recurses via the IH. -/
private theorem findMismatch
    {V C P : Type}
    [DecidableEq V]
    [VectorCommitmentScheme V C P]
    (c : C) (l₁ l₂ : List (Nat × V × P))
    (h₁ : ∀ op ∈ l₁,
      VectorCommitmentScheme.verify c op.1 op.2.1 op.2.2 = true)
    (h₂ : ∀ op ∈ l₂,
      VectorCommitmentScheme.verify c op.1 op.2.1 op.2.2 = true) :
    (∀ op₁ ∈ l₁, ∀ op₂ ∈ l₂, op₁.1 = op₂.1 → op₁.2.1 = op₂.2.1) ∨
    ∃ (c₀ : C) (i₀ : Nat) (a a' : V) (p p' : P),
        a ≠ a' ∧
        VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
        VectorCommitmentScheme.verify c₀ i₀ a' p' = true := by
  induction l₁ with
  | nil =>
    left
    intro op₁ hMem
    cases hMem
  | cons head tail ih =>
    have hHead : VectorCommitmentScheme.verify c head.1 head.2.1 head.2.2 = true :=
      h₁ head List.mem_cons_self
    have hTail : ∀ op ∈ tail,
        VectorCommitmentScheme.verify c op.1 op.2.1 op.2.2 = true :=
      fun op hMem => h₁ op (List.mem_cons_of_mem head hMem)
    rcases findInL₂ c head l₂ hHead h₂ with hHeadAll | hViol
    · rcases ih hTail with hTailAll | hViol
      · left
        intro op₁ hMem op₂ hMem₂ hPos
        rcases List.mem_cons.mp hMem with h | h
        · subst h; exact hHeadAll op₂ hMem₂ hPos
        · exact hTailAll op₁ h op₂ hMem₂ hPos
      · right; exact hViol
    · right; exact hViol


theorem t8'_multi_disclosure_nonequivocation
    {V C P : Type}
    [DecidableEq V]
    [VectorCommitmentScheme V C P]
    (D₁ D₂ : Disclosure V C P) :
    D₁.commitment = D₂.commitment →
    Disclosure.consistent D₁ →
    Disclosure.consistent D₂ →
    (∀ i v₁ v₂ π₁ π₂,
        (i, v₁, π₁) ∈ D₁.openings →
        (i, v₂, π₂) ∈ D₂.openings →
        v₁ = v₂) ∨
    ∃ (c₀ : C) (i₀ : Nat) (a a' : V) (p p' : P),
        a ≠ a' ∧
        VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
        VectorCommitmentScheme.verify c₀ i₀ a' p' = true := by
  intro hC h₁ h₂
  have h₂' : ∀ op ∈ D₂.openings,
      VectorCommitmentScheme.verify D₁.commitment op.1 op.2.1 op.2.2 = true := by
    intro op hMem
    rw [hC]
    exact h₂ op hMem
  rcases findMismatch D₁.commitment D₁.openings D₂.openings h₁ h₂' with hAll | hViol
  · left
    intro i v₁ v₂ π₁ π₂ hMem₁ hMem₂
    exact hAll (i, v₁, π₁) hMem₁ (i, v₂, π₂) hMem₂ rfl
  · right
    exact hViol



/-- A hierarchical receipt at depth-1: a parent disclosure paired
    with a list of child disclosures. Defensively pessimistic
    composition: verification AND-composes parent with every child;
    never OR. The structure carries no implicit relationship between
    parent and children other than co-membership in this composition.

    This is the depth-1 form. For depth-n composition, see
    `HierarchicalReceiptTree` below. -/
structure HierarchicalReceipt (V C P : Type) where
  parent   : Disclosure V C P
  children : List (Disclosure V C P)

/-- Construct a hierarchical receipt from a parent and a list of
    children. This is the eponymous `Compose-Verify(parent, [children])`
    constructor (the `Compose` half; `Verify` is `composeVerifyAll`).
    Defensively pessimistic: the constructor commits to BOTH the parent
    AND the children list verbatim — the composition cannot strip
    information. -/
def composeReceipt {V C P : Type}
    (parent : Disclosure V C P)
    (children : List (Disclosure V C P)) : HierarchicalReceipt V C P :=
  { parent := parent, children := children }

/-- Verification predicate for a hierarchical receipt. Defensively
    pessimistic AND-composition: the receipt verifies iff the parent
    is consistent AND every child is consistent. Each consistency
    check is independent — see `composeVerifyAll_disclosure_independence`
    for the H2-A5 rebuttal. -/
def composeVerifyAll {V C P : Type}
    [VectorCommitmentScheme V C P]
    (h : HierarchicalReceipt V C P) : Prop :=
  Disclosure.consistent h.parent ∧
    ∀ c ∈ h.children, Disclosure.consistent c


theorem composeReceipt_parent_eq {V C P : Type}
    (parent : Disclosure V C P)
    (children : List (Disclosure V C P)) :
    (composeReceipt parent children).parent = parent := rfl

/-- Companion to `composeReceipt_parent_eq`. STRUCTURAL PACKAGING. -/
theorem composeReceipt_children_eq {V C P : Type}
    (parent : Disclosure V C P)
    (children : List (Disclosure V C P)) :
    (composeReceipt parent children).children = children := rfl

/-- Surface form of the `composeVerifyAll` definition: it iff-equals
    the AND of parent-consistency with universal child-consistency.
    STRUCTURAL PACKAGING (definitional unfolding); the LOAD-BEARING
    content is the defensively-pessimistic AND choice (rebuts H2-A2
    adversarial-children). -/
theorem composeVerifyAll_iff_constituents_consistent {V C P : Type}
    [VectorCommitmentScheme V C P]
    (h : HierarchicalReceipt V C P) :
    composeVerifyAll h ↔
      Disclosure.consistent h.parent ∧
        ∀ c ∈ h.children, Disclosure.consistent c :=
  Iff.rfl


theorem composeVerifyAll_trivial_iff_parent {V C P : Type}
    [VectorCommitmentScheme V C P]
    (parent : Disclosure V C P) :
    composeVerifyAll (composeReceipt parent []) ↔
      Disclosure.consistent parent := by
  unfold composeVerifyAll
  simp [composeReceipt]

/-- H2-A2 rebuttal surface theorem: a single bad child falsifies
    the entire composition. Defensively-pessimistic AND-not-OR is
    the binding safety property. -/
theorem composeVerify_falsified_by_bad_child {V C P : Type}
    [VectorCommitmentScheme V C P]
    (h : HierarchicalReceipt V C P)
    (badChild : Disclosure V C P)
    (hMem : badChild ∈ h.children)
    (hBad : ¬ Disclosure.consistent badChild) :
    ¬ composeVerifyAll h := by
  intro hVerify
  obtain ⟨_, hAll⟩ := hVerify
  exact hBad (hAll badChild hMem)

/-- H2 surface theorem (mirror of bad-child for the parent axis):
    a bad parent falsifies the entire composition. STRUCTURAL
    PACKAGING via `And.left`. -/
theorem composeVerify_falsified_by_bad_parent {V C P : Type}
    [VectorCommitmentScheme V C P]
    (h : HierarchicalReceipt V C P)
    (hBad : ¬ Disclosure.consistent h.parent) :
    ¬ composeVerifyAll h := by
  intro hVerify
  exact hBad hVerify.1


theorem composeVerifyAll_disclosure_independence {V C P : Type}
    [VectorCommitmentScheme V C P]
    (h : HierarchicalReceipt V C P)
    (hVerify : composeVerifyAll h) :
    Disclosure.consistent h.parent ∧
      (∀ c ∈ h.children, Disclosure.consistent c) :=
  hVerify


theorem composeVerify_sound {V C P : Type}
    [VectorCommitmentScheme V C P]
    (parent : Disclosure V C P)
    (children : List (Disclosure V C P)) :
    composeVerifyAll (composeReceipt parent children) ↔
      Disclosure.consistent parent ∧
        ∀ c ∈ children, Disclosure.consistent c :=
  Iff.rfl

/-- Recursive hierarchical receipt — depth-n form. A tree with a
    parent disclosure and a list of subtrees, each itself a
    `HierarchicalReceiptTree`. Lean 4's `inductive` discipline
    establishes well-foundedness via the structural recursion on
    the list-of-subtrees argument.

    Closes H2-A3 (width-vs-depth) by allowing arbitrary tree depth.
    -/
inductive HierarchicalReceiptTree (V C P : Type) where
  | node (parent : Disclosure V C P)
         (subtrees : List (HierarchicalReceiptTree V C P)) :
        HierarchicalReceiptTree V C P

namespace HierarchicalReceiptTree

/-- Extract the parent disclosure of a tree node. -/
def parent {V C P : Type} : HierarchicalReceiptTree V C P → Disclosure V C P
  | node p _ => p

/-- Extract the list of subtrees (immediate children-as-trees) of a
    tree node. -/
def subtrees {V C P : Type} :
    HierarchicalReceiptTree V C P → List (HierarchicalReceiptTree V C P)
  | node _ s => s

/-- Verification predicate for a hierarchical receipt tree. Recursive
    over the tree structure: a tree verifies iff its parent is
    consistent AND every subtree (itself a tree) verifies.

    Defined via mutual recursion over the inductive — Lean 4's
    structural-recursion discipline establishes termination via the
    sub-list shape on `subtrees`. -/
def treeVerifyAll {V C P : Type}
    [VectorCommitmentScheme V C P] :
    HierarchicalReceiptTree V C P → Prop
  | node p subtrees =>
    Disclosure.consistent p ∧
      ∀ st ∈ subtrees, treeVerifyAll st

/-- Surface unfolding lemma: `treeVerifyAll` on a constructed node
    iff the parent is consistent AND every subtree verifies.
    STRUCTURAL PACKAGING (definitional unfolding); LOAD-BEARING
    content is the explicit recursive AND-composition (mirrors
    `composeVerifyAll_iff_constituents_consistent` at the depth-n
    level). -/
theorem treeVerifyAll_node_iff {V C P : Type}
    [VectorCommitmentScheme V C P]
    (p : Disclosure V C P)
    (subtrees : List (HierarchicalReceiptTree V C P)) :
    treeVerifyAll (node p subtrees) ↔
      Disclosure.consistent p ∧
        ∀ st ∈ subtrees, treeVerifyAll st := by
  simp only [treeVerifyAll]

/-- Trivial-leaf collapse at depth-n: a node with no subtrees verifies
    iff its parent verifies. Honest-naming companion to
    `composeVerifyAll_trivial_iff_parent` at the recursive level. -/
theorem treeVerifyAll_leaf_iff_parent {V C P : Type}
    [VectorCommitmentScheme V C P]
    (p : Disclosure V C P) :
    treeVerifyAll (node p ([] : List (HierarchicalReceiptTree V C P))) ↔
      Disclosure.consistent p := by
  unfold treeVerifyAll
  simp

/-- Adversarial-subtree falsifier at depth-n: a single bad descendant
    subtree falsifies the tree. Mirrors
    `composeVerify_falsified_by_bad_child` at the recursive level. -/
theorem treeVerify_falsified_by_bad_subtree {V C P : Type}
    [VectorCommitmentScheme V C P]
    (p : Disclosure V C P)
    (subtrees : List (HierarchicalReceiptTree V C P))
    (badSubtree : HierarchicalReceiptTree V C P)
    (hMem : badSubtree ∈ subtrees)
    (hBad : ¬ treeVerifyAll badSubtree) :
    ¬ treeVerifyAll (node p subtrees) := by
  intro hVerify
  rw [treeVerifyAll_node_iff] at hVerify
  obtain ⟨_, hAll⟩ := hVerify
  exact hBad (hAll badSubtree hMem)

/-- The headline tree-level disclosure soundness theorem at depth-n.
    A `HierarchicalReceiptTree` verifies iff its parent is
    consistent AND every immediate subtree verifies (which, by
    structural recursion, means every node in the entire tree
    verifies).

    Closes H2-A3 (width-vs-depth) explicitly: the recursive
    AND-composition extends `composeVerify_sound` (depth-1) to
    arbitrary tree depth. The proof is `Iff.rfl`-shape under the
    `treeVerifyAll` definition.

    LOAD-BEARING NAMING (paper §3-4): a multi-agent-attestation tree
    of arbitrary depth (parent agent → child agents → grandchild
    agents → ...) verifies iff every node attests consistently.
    -/
theorem treeVerify_sound {V C P : Type}
    [VectorCommitmentScheme V C P]
    (p : Disclosure V C P)
    (subtrees : List (HierarchicalReceiptTree V C P)) :
    treeVerifyAll (node p subtrees) ↔
      Disclosure.consistent p ∧
        ∀ st ∈ subtrees, treeVerifyAll st :=
  treeVerifyAll_node_iff p subtrees

end HierarchicalReceiptTree



namespace AgentKernel.Disclosure


def VectorCommitmentScheme.NonTrivial
    (V C P : Type) [VectorCommitmentScheme V C P] : Prop :=
  ∃ (c : C) (i : Nat) (v : V) (π : P),
    VectorCommitmentScheme.verify (V := V) (C := C) (P := P) c i v π = false


theorem t8_disclosure_soundness_nontrivial
    {V C P : Type}
    [DecidableEq V]
    [VectorCommitmentScheme V C P]
    (_hNT : VectorCommitmentScheme.NonTrivial V C P)
    (c : C) (i : Nat) (v v' : V) (π π' : P)
    (hV : VectorCommitmentScheme.verify c i v π = true)
    (hV' : VectorCommitmentScheme.verify c i v' π' = true) :
    v = v' ∨
      ∃ (c₀ : C) (i₀ : Nat) (a a' : V) (p p' : P),
        a ≠ a' ∧
        VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
        VectorCommitmentScheme.verify c₀ i₀ a' p' = true :=
  -- its load-bearing role is the typed signature obligation, not the
  -- proof. Forward to the existing T8 (which holds without `NonTrivial`).
  t8_disclosure_soundness c i v v' π π' hV hV'

end AgentKernel.Disclosure

#print axioms AgentKernel.Disclosure.t8_disclosure_soundness
#print axioms AgentKernel.Disclosure.t8'_multi_disclosure_nonequivocation
#print axioms AgentKernel.Disclosure.t8_disclosure_soundness_nontrivial
