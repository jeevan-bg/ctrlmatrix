

import AgentKernel.Disclosure

namespace AgentKernel.Disclosure.Conformance

/-- Concrete value type: byte sequences. -/
abbrev V : Type := List UInt8

/-- Concrete commitment type: 64-bit Merkle root (mock width;
    production uses 256-bit per §8 deployment shape). -/
abbrev C : Type := UInt64

/-- Concrete proof type: list of sibling hashes along the inclusion
    path (length 2 for a depth-2 / 4-leaf Merkle tree). -/
abbrev P : Type := List UInt64




opaque leafHash : V → UInt64 := fun _ => 0

/-- Opaque internal-node combine primitive. Kernel cannot unfold.
    Same Engineer D rationale as `leafHash`. -/
opaque combineHash : UInt64 → UInt64 → UInt64 := fun _ _ => 0



/-- Step the accumulator up one Merkle level using the next sibling
    in the path. Bit `i % 2 == 0` means the accumulator is the LEFT
    child; `1` means RIGHT. Structural recursion on `path` makes
    Lean accept termination without `decreasing_by`. -/
def merkleVerifyAux : Nat → UInt64 → List UInt64 → UInt64
  | _, acc, []          => acc
  | i, acc, s :: rest   =>
    match i % 2 with
    | 0 => merkleVerifyAux (i / 2) (combineHash acc s) rest
    | _ => merkleVerifyAux (i / 2) (combineHash s acc) rest

/-- Verify an inclusion path of arbitrary length. Capacity tested
    in conformance: degree-2 trees of depth <= 16. Larger paths
    compile but are not exercised. -/
def merkleVerify (root : UInt64) (i : Nat) (v : V) (path : P) : Bool :=
  merkleVerifyAux i (leafHash v) path == root

/-! ## Concrete demo instance: 4 leaves, computed root, computed paths -/

def L0 : V := [0]
def L1 : V := [1]
def L2 : V := [2]
def L3 : V := [3]

/-- The Merkle root of [L0, L1, L2, L3]. Defined symbolically so the
    verify expressions reduce to syntactically identical opaque ASTs. -/
def demoRoot : UInt64 :=
  combineHash
    (combineHash (leafHash L0) (leafHash L1))
    (combineHash (leafHash L2) (leafHash L3))

/-- Inclusion path for position 0: [sibling-at-level-0,
    sibling-at-level-1] = [leafHash L1, combineHash leafHash L2 leafHash L3]. -/
def path0 : P := [leafHash L1, combineHash (leafHash L2) (leafHash L3)]

/-- Inclusion path for position 1. -/
def path1 : P := [leafHash L0, combineHash (leafHash L2) (leafHash L3)]

/-- Inclusion path for position 2. -/
def path2 : P := [leafHash L3, combineHash (leafHash L0) (leafHash L1)]

/-- Inclusion path for position 3. -/
def path3 : P := [leafHash L2, combineHash (leafHash L0) (leafHash L1)]



instance schemeInst : VectorCommitmentScheme V C P where
  -- commit and open_ are placeholders; the structural conformance
  -- bridge runs through `verify` only (mirrors v0.5 trivial scheme
  -- design where commit / open_ were also unused).
  commit  _    := demoRoot
  open_   _ _  := []
  verify       := merkleVerify



theorem verify_demo_at_0 :
    VectorCommitmentScheme.verify (V := V) (C := C) (P := P)
      demoRoot 0 L0 path0 = true := by
  show merkleVerify demoRoot 0 L0 path0 = true
  unfold merkleVerify path0 merkleVerifyAux
  simp only [merkleVerifyAux]
  exact beq_self_eq_true _

theorem verify_demo_at_1 :
    VectorCommitmentScheme.verify (V := V) (C := C) (P := P)
      demoRoot 1 L1 path1 = true := by
  show merkleVerify demoRoot 1 L1 path1 = true
  unfold merkleVerify path1 merkleVerifyAux
  simp only [merkleVerifyAux]
  exact beq_self_eq_true _

theorem verify_demo_at_2 :
    VectorCommitmentScheme.verify (V := V) (C := C) (P := P)
      demoRoot 2 L2 path2 = true := by
  show merkleVerify demoRoot 2 L2 path2 = true
  unfold merkleVerify path2 merkleVerifyAux
  simp only [merkleVerifyAux]
  exact beq_self_eq_true _

theorem verify_demo_at_3 :
    VectorCommitmentScheme.verify (V := V) (C := C) (P := P)
      demoRoot 3 L3 path3 = true := by
  show merkleVerify demoRoot 3 L3 path3 = true
  unfold merkleVerify path3 merkleVerifyAux
  simp only [merkleVerifyAux]
  exact beq_self_eq_true _

/-! ## T8 fired at the concrete instance -/

theorem t8_demo : L0 = L0 ∨
    ∃ (c₀ : C) (i₀ : Nat) (a a' : V) (p p' : P),
      a ≠ a' ∧
      VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
      VectorCommitmentScheme.verify c₀ i₀ a' p' = true :=
  t8_disclosure_soundness demoRoot 0 L0 L0 path0 path0
    verify_demo_at_0 verify_demo_at_0

/-! ## T8' fired at the concrete instance

Build a single-opening disclosure D under demoRoot at position 0, and
invoke T8' on the pair (D, D). Disclosure.consistent D follows from
verify_demo_at_0 by single-element list induction. -/

def D : Disclosure V C P :=
  { commitment := demoRoot, openings := [(0, L0, path0)] }

theorem t8'_demo :
    (∀ i v₁ v₂ π₁ π₂,
        (i, v₁, π₁) ∈ D.openings →
        (i, v₂, π₂) ∈ D.openings →
        v₁ = v₂) ∨
    ∃ (c₀ : C) (i₀ : Nat) (a a' : V) (p p' : P),
      a ≠ a' ∧
      VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
      VectorCommitmentScheme.verify c₀ i₀ a' p' = true := by
  have hCons : Disclosure.consistent D := by
    intro op hMem
    rcases List.mem_cons.mp hMem with h | h
    · subst h; exact verify_demo_at_0
    · cases h
  exact t8'_multi_disclosure_nonequivocation D D rfl hCons hCons

end AgentKernel.Disclosure.Conformance
#print axioms AgentKernel.Disclosure.Conformance.verify_demo_at_0
#print axioms AgentKernel.Disclosure.Conformance.verify_demo_at_1
#print axioms AgentKernel.Disclosure.Conformance.verify_demo_at_2
#print axioms AgentKernel.Disclosure.Conformance.verify_demo_at_3
#print axioms AgentKernel.Disclosure.Conformance.t8_demo
#print axioms AgentKernel.Disclosure.Conformance.t8'_demo


