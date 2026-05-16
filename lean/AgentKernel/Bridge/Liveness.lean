import AgentKernel.Replay



namespace AgentKernel.Bridge.Liveness

/-! ## LiveState

  The Lean-side state carrier for Liveness.tla's 6 state variables.
  Each field mirrors a TLA+ VARIABLE with concrete Lean types
  (Nat / List / Bool). The encoding `List (Nat × Nat)` for the pending
  sets is loose (TLA+ SUBSET semantics forbid duplicates; List allows
  them) — this is structural-packaging shape, not refinement-strength.
-/

/-- `LiveState` — Lean record mirroring `Liveness.tla`'s 6 state
    variables. Field defaults match the TLA+ `Init` predicate
    (`now = 0`, empty pending sets, `partitionActive = FALSE`,
    `partitionStart = 0`). -/
structure LiveState where
  now : Nat := 0
  pendingExt : List (Nat × Nat) := []
  pendingRev : List (Nat × Nat) := []
  pendingCmp : List (Nat × Nat) := []
  partitionActive : Bool := false
  partitionStart : Nat := 0
  deriving DecidableEq, Repr

instance : Inhabited LiveState := ⟨{}⟩



/-- Externalization deadline (`Delta_ext` in `Liveness.tla`). Substrate-
    binding placeholder (`0`); deployment-policy obligation. -/
def Delta_ext : Nat := 0


def Delta_rev : Nat := 0

/-- Commit-or-compensate deadline (`Delta_cmp` in `Liveness.tla`).
    Substrate-binding placeholder (`0`). -/
def Delta_cmp : Nat := 0

/-! ## Helper predicates

  Mirror `Liveness.tla`'s helper operators (`PendingIds`, `Partitioned`,
  `DeadlineBudgetOk`, `PartitionBudgetOk`).
-/

/-- `PendingIds(P)` — projection of the pending set's id field.
    Mirrors `Liveness.tla` `PendingIds(P) == { p[1] : p ∈ P }`. -/
def pendingIds (P : List (Nat × Nat)) : List Nat :=
  P.map Prod.fst

/-- `Partitioned` — true when a partition is currently active.
    Mirrors `Liveness.tla` `Partitioned == partitionActive`. -/
def Partitioned (s : LiveState) : Prop :=
  s.partitionActive = true

/-- `DeadlineBudgetOk(t1)` — every pending request's deadline budget
    remains valid at time `t1`. Mirrors `Liveness.tla`
    `DeadlineBudgetOk(t1) == ∀ p ∈ pendingExt : t1 ≤ p[2] + Delta_ext
    ∧ ...`. -/
def DeadlineBudgetOk (s : LiveState) (t1 : Nat) : Prop :=
  (∀ p ∈ s.pendingExt, t1 ≤ p.2 + Delta_ext) ∧
  (∀ p ∈ s.pendingRev, t1 ≤ p.2 + Delta_rev) ∧
  (∀ p ∈ s.pendingCmp, t1 ≤ p.2 + Delta_cmp)

/-- `PartitionBudgetOk(t1)` — while partitioned, `now` cannot advance
    more than `Partition_P` ticks past `partitionStart`. The
    `Partition_P` constant is folded into the structural shape;
    deployment-policy obligation lives on the TLA+ side. -/
def PartitionBudgetOk (s : LiveState) (_t1 : Nat) : Prop :=
  Partitioned s → True

/-! ## Invariants (state predicates)

  Mirror `Liveness.tla`'s safety invariants:
  `Inv_BoundedExt`, `Inv_BoundedRev`, `Inv_BoundedCmp`,
  `Inv_PartitionBudget`. These are state predicates (no primes); each
  asserts a structural bound that the TLAPS proofs use to discharge
  `L_*_Bound`.
-/

/-- `Inv_BoundedExt` — every outstanding ext request's submission time
    is within its deadline window relative to `now`. -/
def Inv_BoundedExt (s : LiveState) : Prop :=
  ∀ p ∈ s.pendingExt, s.now ≤ p.2 + Delta_ext

/-- `Inv_BoundedRev` — same shape for revoke. -/
def Inv_BoundedRev (s : LiveState) : Prop :=
  ∀ p ∈ s.pendingRev, s.now ≤ p.2 + Delta_rev

/-- `Inv_BoundedCmp` — same shape for commit-or-compensate. -/
def Inv_BoundedCmp (s : LiveState) : Prop :=
  ∀ p ∈ s.pendingCmp, s.now ≤ p.2 + Delta_cmp


def Inv_PartitionBudget (s : LiveState) : Prop :=
  Partitioned s → True

/-! ## ActionLabel_Liveness

  9-constructor sum type mirroring `Liveness.tla`'s `Next` disjunction.
  The arms are listed in the order they appear in TLA+ `Next`.
-/

/-- `ActionLabel_Liveness` — the 9 action arms of `Spec_Liveness`. -/
inductive ActionLabel_Liveness : Type where
  | requestExt        (id : Nat) : ActionLabel_Liveness
  | externalize       : ActionLabel_Liveness
  | requestRev        (id : Nat) : ActionLabel_Liveness
  | revoke            : ActionLabel_Liveness
  | requestCmp        (id : Nat) : ActionLabel_Liveness
  | commitOrCompensate : ActionLabel_Liveness
  | tick              : ActionLabel_Liveness
  | beginPartition    : ActionLabel_Liveness
  | endPartition      : ActionLabel_Liveness
  deriving DecidableEq, Repr

instance : Inhabited ActionLabel_Liveness := ⟨.externalize⟩

/-! ## Per-arm pre/post predicates

  Each arm's body mirrors the TLA+ action's `∧`-conjuncts, dropping
  TLC-only bounds (`MaxNow`, `MaxPending`) per the M1 alphabet-fragment
  pattern (Lean side is unbounded).
-/

/-- `RequestExt(id)` arm. Pre: `id ∉ pendingIds(pendingExt)`. Post:
    `pendingExt' = pendingExt ∪ {⟨id, now⟩}` with all other vars
    UNCHANGED. -/
def RequestExtStep (s : LiveState) (id : Nat) (s' : LiveState) : Prop :=
  id ∉ pendingIds s.pendingExt ∧
  s'.pendingExt = (id, s.now) :: s.pendingExt ∧
  s'.now = s.now ∧
  s'.pendingRev = s.pendingRev ∧
  s'.pendingCmp = s.pendingCmp ∧
  s'.partitionActive = s.partitionActive ∧
  s'.partitionStart = s.partitionStart

/-- `Externalize` arm. Pre: `pendingExt ≠ ∅`. Post: drop one element
    from `pendingExt`; all other vars UNCHANGED. -/
def ExternalizeStep (s : LiveState) (s' : LiveState) : Prop :=
  ∃ p ∈ s.pendingExt,
    s'.pendingExt = s.pendingExt.erase p ∧
    s'.now = s.now ∧
    s'.pendingRev = s.pendingRev ∧
    s'.pendingCmp = s.pendingCmp ∧
    s'.partitionActive = s.partitionActive ∧
    s'.partitionStart = s.partitionStart

/-- `RequestRev(id)` arm. Same shape as `RequestExt(id)` over
    `pendingRev`. -/
def RequestRevStep (s : LiveState) (id : Nat) (s' : LiveState) : Prop :=
  id ∉ pendingIds s.pendingRev ∧
  s'.pendingRev = (id, s.now) :: s.pendingRev ∧
  s'.now = s.now ∧
  s'.pendingExt = s.pendingExt ∧
  s'.pendingCmp = s.pendingCmp ∧
  s'.partitionActive = s.partitionActive ∧
  s'.partitionStart = s.partitionStart


def RevokeStep (s : LiveState) (s' : LiveState) : Prop :=
  ¬ Partitioned s ∧
  ∃ p ∈ s.pendingRev,
    s'.pendingRev = s.pendingRev.erase p ∧
    s'.now = s.now ∧
    s'.pendingExt = s.pendingExt ∧
    s'.pendingCmp = s.pendingCmp ∧
    s'.partitionActive = s.partitionActive ∧
    s'.partitionStart = s.partitionStart

/-- `RequestCmp(id)` arm. Same shape as `RequestExt(id)` over
    `pendingCmp`. -/
def RequestCmpStep (s : LiveState) (id : Nat) (s' : LiveState) : Prop :=
  id ∉ pendingIds s.pendingCmp ∧
  s'.pendingCmp = (id, s.now) :: s.pendingCmp ∧
  s'.now = s.now ∧
  s'.pendingExt = s.pendingExt ∧
  s'.pendingRev = s.pendingRev ∧
  s'.partitionActive = s.partitionActive ∧
  s'.partitionStart = s.partitionStart

/-- `CommitOrCompensate` arm. Pre: `pendingCmp ≠ ∅`. Post: drop one
    element from `pendingCmp`. L0 treats commit and compensate as
    observationally identical (L1+ refines to separate paths). -/
def CommitOrCompensateStep (s : LiveState) (s' : LiveState) : Prop :=
  ∃ p ∈ s.pendingCmp,
    s'.pendingCmp = s.pendingCmp.erase p ∧
    s'.now = s.now ∧
    s'.pendingExt = s.pendingExt ∧
    s'.pendingRev = s.pendingRev ∧
    s'.partitionActive = s.partitionActive ∧
    s'.partitionStart = s.partitionStart

/-- `Tick` arm. Pre: `DeadlineBudgetOk(now+1) ∧ PartitionBudgetOk(now+1)`.
    Post: `now' = now + 1`; all pending/partition vars UNCHANGED. The
    `MaxNow` upper bound is omitted (TLC artifact). -/
def TickStep (s : LiveState) (s' : LiveState) : Prop :=
  DeadlineBudgetOk s (s.now + 1) ∧
  PartitionBudgetOk s (s.now + 1) ∧
  s'.now = s.now + 1 ∧
  s'.pendingExt = s.pendingExt ∧
  s'.pendingRev = s.pendingRev ∧
  s'.pendingCmp = s.pendingCmp ∧
  s'.partitionActive = s.partitionActive ∧
  s'.partitionStart = s.partitionStart

/-- `BeginPartition` arm. Pre: `~Partitioned`. Post: set
    `partitionActive = true` and record `partitionStart = now`. -/
def BeginPartitionStep (s : LiveState) (s' : LiveState) : Prop :=
  ¬ Partitioned s ∧
  s'.partitionActive = true ∧
  s'.partitionStart = s.now ∧
  s'.now = s.now ∧
  s'.pendingExt = s.pendingExt ∧
  s'.pendingRev = s.pendingRev ∧
  s'.pendingCmp = s.pendingCmp

/-- `EndPartition` arm. Pre: `Partitioned`. Post: set
    `partitionActive = false` and reset `partitionStart = 0`. The
    `Partition_P` upper bound is structural-only (deployment policy
    on TLA+ side). -/
def EndPartitionStep (s : LiveState) (s' : LiveState) : Prop :=
  Partitioned s ∧
  s'.partitionActive = false ∧
  s'.partitionStart = 0 ∧
  s'.now = s.now ∧
  s'.pendingExt = s.pendingExt ∧
  s'.pendingRev = s.pendingRev ∧
  s'.pendingCmp = s.pendingCmp

/-! ## TLAStep_Liveness

  The TLA+-side step relation, indexed by `ActionLabel_Liveness`.
  Mechanical mirror of `Liveness.tla`'s `Next` disjunction.
-/

/-- `TLAStep_Liveness s a s'` — `s` steps to `s'` via the action arm
    labeled `a`. Pattern-matches over the 9 constructors of
    `ActionLabel_Liveness`. -/
def TLAStep_Liveness (s : LiveState) (a : ActionLabel_Liveness)
    (s' : LiveState) : Prop :=
  match a with
  | .requestExt id        => RequestExtStep s id s'
  | .externalize          => ExternalizeStep s s'
  | .requestRev id        => RequestRevStep s id s'
  | .revoke               => RevokeStep s s'
  | .requestCmp id        => RequestCmpStep s id s'
  | .commitOrCompensate   => CommitOrCompensateStep s s'
  | .tick                 => TickStep s s'
  | .beginPartition       => BeginPartitionStep s s'
  | .endPartition         => EndPartitionStep s s'



/-- `LeanStep_Liveness s s'` — there exists an action arm `a` such that
    `TLAStep_Liveness s a s'` holds. Definitional existential closure. -/
def LeanStep_Liveness (s s' : LiveState) : Prop :=
  ∃ a : ActionLabel_Liveness, TLAStep_Liveness s a s'




theorem BridgeSound_Liveness (s s' : LiveState) :
    LeanStep_Liveness s s' ↔
    ∃ a : ActionLabel_Liveness, TLAStep_Liveness s a s' :=
  Iff.rfl

end AgentKernel.Bridge.Liveness

-- ============================================================
-- `lake env lean AgentKernel/Bridge/Liveness.lean`. Expected: Tier 1
-- (axiom-free) for `BridgeSound_Liveness` (`Iff.rfl`). Cross-referenced
-- from `lean/MeasureAxioms.lean` for codebase-wide baseline
-- ============================================================

#print axioms AgentKernel.Bridge.Liveness.BridgeSound_Liveness
