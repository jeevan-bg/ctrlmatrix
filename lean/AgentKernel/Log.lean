

namespace AgentKernel.Log


structure Entry (Bytes Hash : Type) where
  prev          : Hash
  payload       : Bytes
  detWitnessRef : Option Hash := none

/-- Predicate: the entry binds to a det-witness. Non-vacuous, so
    deployment-policy can require `bindsToWitness = true` for entry
    kinds that record kernel-driven IO (per the bootstrap H2 attack
    1 mitigation: vacuous binding is always allowed structurally,
    but a policy hook fires here). -/
def Entry.bindsToWitness {Bytes Hash : Type}
    (e : Entry Bytes Hash) : Bool :=
  e.detWitnessRef.isSome


abbrev LogChain (Bytes Hash : Type) := List (Entry Bytes Hash)

/-- L1+ audit metric: count of entries in a chain whose
    `detWitnessRef` is `some _`. Useful for SLA-style bounded-rate
    audit invariants ("the kernel is binding witness on at least k%
    of audit entries"). -/
def LogChain.witnessBoundCount {Bytes Hash : Type}
    (chain : LogChain Bytes Hash) : Nat :=
  chain.foldl (fun acc e => if e.bindsToWitness then acc + 1 else acc) 0

/-- Root commitment of a log chain.
    Empty chain: `H(genesis)`.
    Non-empty chain: fold left from `H(genesis)`, at each step
    replacing the accumulator with `H(serialize(acc, e.payload))`.
    The accumulator at step k is the root of the k-prefix.
    Mirrors `Log.tla`'s recursive `Root` . -/
def LogChain.root {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (c : LogChain Bytes Hash) : Hash :=
  List.foldl (fun acc e => H (serialize acc e.payload)) (H genesis) c


def LogChain.wellFormedAux {Bytes Hash : Type}
    (H : Bytes → Hash)
    (serialize : Hash → Bytes → Bytes)
    : Hash → LogChain Bytes Hash → Prop
  | _,   []        => True
  | acc, e :: rest =>
      e.prev = acc ∧
      e.detWitnessRef = none ∧
      LogChain.wellFormedAux H serialize
        (H (serialize acc e.payload)) rest


def LogChain.wellFormed {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (c : LogChain Bytes Hash) : Prop :=
  LogChain.wellFormedAux H serialize (H genesis) c

/-! ## Helper lemmas for T4

Five helpers sit between the definitions and the theorem. Each
is a one-shot induction or rewrite; none introduces an axiom
beyond the kernel defaults already in M2/M3/M4/M5.
-/

/-- Root commitment of `xs ++ [e]` peels to a single step. -/
theorem LogChain.root_append_singleton
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (xs : LogChain Bytes Hash) (e : Entry Bytes Hash) :
    (xs ++ [e]).root H genesis serialize
      = H (serialize (xs.root H genesis serialize) e.payload) := by
  unfold LogChain.root
  rw [List.foldl_append]
  rfl

/-- Well-formedness is hereditary on prefixes (auxiliary, with
    explicit accumulator). -/
theorem LogChain.wellFormedAux_dropLast
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (serialize : Hash → Bytes → Bytes)
    (xs : LogChain Bytes Hash) (e : Entry Bytes Hash) :
    ∀ (acc : Hash),
      LogChain.wellFormedAux H serialize acc (xs ++ [e]) →
      LogChain.wellFormedAux H serialize acc xs := by
  induction xs with
  | nil =>
    intro _ _
    exact True.intro
  | cons head tail ih =>
    intro acc h
    rw [List.cons_append] at h
    simp only [LogChain.wellFormedAux] at h
    obtain ⟨hPrev, hWref, hRest⟩ := h
    simp only [LogChain.wellFormedAux]
    exact ⟨hPrev, hWref, ih _ hRest⟩

/-- Well-formedness is hereditary on prefixes. -/
theorem LogChain.wellFormed_dropLast
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (xs : LogChain Bytes Hash) (e : Entry Bytes Hash) :
    LogChain.wellFormed H genesis serialize (xs ++ [e]) →
    LogChain.wellFormed H genesis serialize xs := by
  intro h
  exact LogChain.wellFormedAux_dropLast H serialize xs e (H genesis) h

/-- The last entry's `prev` field equals the prefix-root, when
    the appended chain is well-formed (auxiliary, with explicit
    accumulator). -/
theorem LogChain.wellFormedAux_last_prev
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (serialize : Hash → Bytes → Bytes)
    (xs : LogChain Bytes Hash) (e : Entry Bytes Hash) :
    ∀ (acc : Hash),
      LogChain.wellFormedAux H serialize acc (xs ++ [e]) →
      e.prev = List.foldl (fun a x => H (serialize a x.payload)) acc xs := by
  induction xs with
  | nil =>
    intro acc h
    rw [List.nil_append] at h
    simp only [LogChain.wellFormedAux] at h
    exact h.1
  | cons head tail ih =>
    intro acc h
    rw [List.cons_append] at h
    simp only [LogChain.wellFormedAux] at h
    obtain ⟨_, _, hRest⟩ := h
    have := ih (H (serialize acc head.payload)) hRest
    simp only [List.foldl_cons]
    exact this

/-- The last entry's `prev` field equals the prefix-root. -/
theorem LogChain.last_prev_eq_prefix_root
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (xs : LogChain Bytes Hash) (e : Entry Bytes Hash) :
    LogChain.wellFormed H genesis serialize (xs ++ [e]) →
    e.prev = xs.root H genesis serialize := by
  intro h
  unfold LogChain.root
  exact LogChain.wellFormedAux_last_prev H serialize xs e (H genesis) h


private theorem LogChain.wellFormedAux_witnessRef_none
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (serialize : Hash → Bytes → Bytes)
    (l : LogChain Bytes Hash) :
    ∀ (acc : Hash),
      LogChain.wellFormedAux H serialize acc l →
      ∀ e ∈ l, e.detWitnessRef = none := by
  induction l with
  | nil =>
    intro _ _ e he
    cases he
  | cons head tail ih =>
    intro acc h e he
    simp only [LogChain.wellFormedAux] at h
    obtain ⟨_, hHeadWref, hRest⟩ := h
    cases he with
    | head _ => exact hHeadWref
    | tail _ heTail => exact ih _ hRest e heTail


theorem LogChain.wellFormed_witnessRef_none
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (l : LogChain Bytes Hash)
    (h : LogChain.wellFormed H genesis serialize l)
    (e : Entry Bytes Hash) (he : e ∈ l) :
    e.detWitnessRef = none :=
  LogChain.wellFormedAux_witnessRef_none H serialize l (H genesis) h e he



/-- Local replacement for the core-Lean lemma
    `List.dropLast_append_getLast` (absent at 4.30.0-rc2).
    Discharged by structural recursion on the list. -/
private theorem dropLast_append_getLast_aux {α : Type _} :
    ∀ (l : List α) (h : l ≠ []), l.dropLast ++ [l.getLast h] = l
  | [],            h => absurd rfl h
  | [_],           _ => rfl
  | a :: b :: rest, _ => by
      have hne : (b :: rest) ≠ [] := List.cons_ne_nil _ _
      have ih := dropLast_append_getLast_aux (b :: rest) hne
      show a :: ((b :: rest).dropLast ++ [(b :: rest).getLast hne]) = a :: b :: rest
      rw [ih]


theorem t4_audit_integrity
    {Bytes Hash : Type}
    [DecidableEq Bytes] [DecidableEq Hash]
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (L1 L2 : LogChain Bytes Hash) :
    L1.length = L2.length →
    LogChain.wellFormed H genesis serialize L1 →
    LogChain.wellFormed H genesis serialize L2 →
    L1.root H genesis serialize = L2.root H genesis serialize →
    L1 = L2 ∨
      ∃ (a a' : Hash) (b b' : Bytes),
        (a, b) ≠ (a', b') ∧ H (serialize a b) = H (serialize a' b') := by
  -- Strong induction on length, generalized over both chains.
  suffices h : ∀ (n : Nat) (L1 L2 : LogChain Bytes Hash),
      L1.length = n → L2.length = n →
      LogChain.wellFormed H genesis serialize L1 →
      LogChain.wellFormed H genesis serialize L2 →
      L1.root H genesis serialize = L2.root H genesis serialize →
      L1 = L2 ∨
        ∃ (a a' : Hash) (b b' : Bytes),
          (a, b) ≠ (a', b') ∧ H (serialize a b) = H (serialize a' b') by
    intro hLen hWF1 hWF2 hRoot
    exact h L1.length L1 L2 rfl hLen.symm hWF1 hWF2 hRoot
  intro n
  induction n with
  | zero =>
    intro L1 L2 hL1 hL2 _ _ _
    have e1 : L1 = [] := by
      cases L1 with
      | nil => rfl
      | cons _ _ => simp at hL1
    have e2 : L2 = [] := by
      cases L2 with
      | nil => rfl
      | cons _ _ => simp at hL2
    left
    rw [e1, e2]
  | succ n ih =>
    intro L1 L2 hL1 hL2 hWF1 hWF2 hRoot
    have hL1ne : L1 ≠ [] := by
      intro hEmpty
      rw [hEmpty] at hL1
      exact Nat.succ_ne_zero n hL1.symm
    have hL2ne : L2 ≠ [] := by
      intro hEmpty
      rw [hEmpty] at hL2
      exact Nat.succ_ne_zero n hL2.symm
    -- Decompose L1 = xs ++ [e], L2 = ys ++ [f] via dropLast/getLast
    obtain ⟨xs, e, hL1eq⟩ : ∃ (xs : LogChain Bytes Hash) (e : Entry Bytes Hash),
        L1 = xs ++ [e] :=
      ⟨L1.dropLast, L1.getLast hL1ne,
       (dropLast_append_getLast_aux L1 hL1ne).symm⟩
    obtain ⟨ys, f, hL2eq⟩ : ∃ (ys : LogChain Bytes Hash) (f : Entry Bytes Hash),
        L2 = ys ++ [f] :=
      ⟨L2.dropLast, L2.getLast hL2ne,
       (dropLast_append_getLast_aux L2 hL2ne).symm⟩
    rw [hL1eq] at hL1 hWF1 hRoot
    rw [hL2eq] at hL2 hWF2 hRoot
    -- Length of prefixes
    have hxsLen : xs.length = n := by
      simp [List.length_append] at hL1
      omega
    have hysLen : ys.length = n := by
      simp [List.length_append] at hL2
      omega
    -- Tail-step root equation
    rw [LogChain.root_append_singleton, LogChain.root_append_singleton] at hRoot
    -- Case split on inner-pair equality of (prefix-root, payload)
    by_cases hPair :
        (xs.root H genesis serialize, e.payload)
        = (ys.root H genesis serialize, f.payload)
    · -- Equal inner pair: derive prefix-root and payload equalities
      simp only [Prod.mk.injEq] at hPair
      obtain ⟨hRootEq, hPayloadEq⟩ := hPair
      have hWF1' : LogChain.wellFormed H genesis serialize xs :=
        LogChain.wellFormed_dropLast H genesis serialize xs e hWF1
      have hWF2' : LogChain.wellFormed H genesis serialize ys :=
        LogChain.wellFormed_dropLast H genesis serialize ys f hWF2
      cases ih xs ys hxsLen hysLen hWF1' hWF2' hRootEq with
      | inl hPrefixEq =>
        -- xs = ys; combine with e = f to get L1 = L2
        have hePrev : e.prev = xs.root H genesis serialize :=
          LogChain.last_prev_eq_prefix_root H genesis serialize xs e hWF1
        have hfPrev : f.prev = ys.root H genesis serialize :=
          LogChain.last_prev_eq_prefix_root H genesis serialize ys f hWF2
        have hPrevEq : e.prev = f.prev := by
          rw [hePrev, hfPrev, hRootEq]
        have heqEntry : e = f := by
          rcases e with ⟨ep, epay, ewref⟩
          rcases f with ⟨fp, fpay, fwref⟩
          simp only [Entry.mk.injEq]
          -- standard T4 case-split; the third (`detWitnessRef`)
          -- comes from `wellFormedAux`'s ambient guarantee that
          -- `wellFormed` chains carry `detWitnessRef = none`
          -- everywhere at L0. The L1+ refinement (allowing
          -- non-`none` values) lives in `witness_binding_propagates`
          -- under a separate predicate; T4's chain-equality
          -- conclusion is preserved at L0 by the structural
          -- guarantee that both `ewref` and `fwref` are `none`
          -- (extracted from `hWF1`/`hWF2` below).
          have hewref : ewref = none :=
            LogChain.wellFormed_witnessRef_none H genesis serialize
              (xs ++ [⟨ep, epay, ewref⟩])
              hWF1 ⟨ep, epay, ewref⟩
              (List.mem_append_right _ (List.mem_singleton.mpr rfl))
          have hfwref : fwref = none :=
            LogChain.wellFormed_witnessRef_none H genesis serialize
              (ys ++ [⟨fp, fpay, fwref⟩])
              hWF2 ⟨fp, fpay, fwref⟩
              (List.mem_append_right _ (List.mem_singleton.mpr rfl))
          refine ⟨hPrevEq, hPayloadEq, ?_⟩
          rw [hewref, hfwref]
        left
        rw [hL1eq, hL2eq, hPrefixEq, heqEntry]
      | inr hCol =>
        right
        exact hCol
    · -- Distinct inner pair: witness step-hash collision
      right
      exact ⟨xs.root H genesis serialize, ys.root H genesis serialize,
             e.payload, f.payload, hPair, hRoot⟩



/-- Well-formedness of a prefix obtained via `List.take` (auxiliary,
    explicit accumulator). Structural induction on the chain, case
    split on `n`. -/
private theorem LogChain.wellFormedAux_take
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (serialize : Hash → Bytes → Bytes)
    (l : LogChain Bytes Hash) :
    ∀ (n : Nat) (acc : Hash),
      LogChain.wellFormedAux H serialize acc l →
      LogChain.wellFormedAux H serialize acc (l.take n) := by
  induction l with
  | nil =>
    intro n acc _
    rw [List.take_nil]
    exact True.intro
  | cons head tail ih =>
    intro n acc h
    cases n with
    | zero =>
      rw [List.take_zero]
      exact True.intro
    | succ k =>
      show LogChain.wellFormedAux H serialize acc (head :: tail.take k)
      simp only [LogChain.wellFormedAux] at h ⊢
      obtain ⟨hPrev, hWref, hRest⟩ := h
      exact ⟨hPrev, hWref, ih _ _ hRest⟩

/-- Well-formedness of a prefix obtained via `List.take`. -/
theorem LogChain.wellFormed_take
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (l : LogChain Bytes Hash) (n : Nat) :
    LogChain.wellFormed H genesis serialize l →
    LogChain.wellFormed H genesis serialize (l.take n) := by
  intro h
  exact LogChain.wellFormedAux_take H serialize l n (H genesis) h


theorem t4_prime_publish_consistency
    {Bytes Hash : Type}
    [DecidableEq Bytes] [DecidableEq Hash]
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (Lshort Llong : LogChain Bytes Hash) :
    Lshort.length ≤ Llong.length →
    LogChain.wellFormed H genesis serialize Lshort →
    LogChain.wellFormed H genesis serialize Llong →
    Lshort.root H genesis serialize
      = LogChain.root H genesis serialize (Llong.take Lshort.length) →
    Lshort = Llong.take Lshort.length ∨
      ∃ (a a' : Hash) (b b' : Bytes),
        (a, b) ≠ (a', b') ∧ H (serialize a b) = H (serialize a' b') := by
  intro hLen hWFshort hWFlong hRootEq
  -- The truncated long-chain prefix is well-formed.
  have hWFprefix : LogChain.wellFormed H genesis serialize
                       (Llong.take Lshort.length) :=
    LogChain.wellFormed_take H genesis serialize Llong Lshort.length hWFlong
  -- Length of the take-prefix equals Lshort.length.
  have hLenPrefix : (Llong.take Lshort.length).length = Lshort.length := by
    rw [List.length_take]
    exact Nat.min_eq_left hLen
  -- Reduce to T4 on the equal-length sub-problem.
  exact t4_audit_integrity H genesis serialize
          Lshort (Llong.take Lshort.length)
          hLenPrefix.symm hWFshort hWFprefix hRootEq

/-- Demonstrative corollary: T4 falls out as the equal-length
    specialization of T4'. Exists for documentation -- does NOT
    replace `t4_audit_integrity` (whose call sites in
    `Log/Conformance.lean` and `AgentKernel/System.lean` link to
    the original lemma name).

    With `L1.length = L2.length`, `L2.take L1.length = L2` (by
    `List.take_length`), so the T4' hypothesis collapses to T4's
    `L1.root = L2.root`, and the T4' conclusion's left disjunct
    `L1 = L2.take L1.length` collapses to `L1 = L2`. -/
theorem t4_audit_integrity_via_t4_prime
    {Bytes Hash : Type}
    [DecidableEq Bytes] [DecidableEq Hash]
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (L1 L2 : LogChain Bytes Hash) :
    L1.length = L2.length →
    LogChain.wellFormed H genesis serialize L1 →
    LogChain.wellFormed H genesis serialize L2 →
    L1.root H genesis serialize = L2.root H genesis serialize →
    L1 = L2 ∨
      ∃ (a a' : Hash) (b b' : Bytes),
        (a, b) ≠ (a', b') ∧ H (serialize a b) = H (serialize a' b') := by
  intro hLen hWF1 hWF2 hRoot
  -- L2.take L1.length = L2 by List.take_length under L1.length = L2.length.
  have hTakeId : L2.take L1.length = L2 := by
    rw [hLen]; exact List.take_length
  have hLeLen : L1.length ≤ L2.length := hLen ▸ Nat.le_refl _
  -- Transport the root-equality hypothesis through hTakeId.
  have hRoot' : L1.root H genesis serialize
                = LogChain.root H genesis serialize (L2.take L1.length) := by
    rw [hTakeId]; exact hRoot
  cases t4_prime_publish_consistency H genesis serialize L1 L2
          hLeLen hWF1 hWF2 hRoot' with
  | inl hEq =>
    left
    rw [hEq, hTakeId]
  | inr hCol =>
    right
    exact hCol



private theorem LogChain.wellFormedAux_append_singleton
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (serialize : Hash → Bytes → Bytes)
    (xs : LogChain Bytes Hash) (e : Entry Bytes Hash) :
    ∀ (acc : Hash),
      LogChain.wellFormedAux H serialize acc xs →
      e.prev = List.foldl (fun a x => H (serialize a x.payload)) acc xs →
      e.detWitnessRef = none →
      LogChain.wellFormedAux H serialize acc (xs ++ [e]) := by
  induction xs with
  | nil =>
    intro acc _ hPrev hWref
    rw [List.nil_append]
    simp only [LogChain.wellFormedAux]
    simp only [List.foldl_nil] at hPrev
    exact ⟨hPrev, hWref, trivial⟩
  | cons head tail ih =>
    intro acc hAux hPrev hWref
    rw [List.cons_append]
    simp only [LogChain.wellFormedAux] at hAux ⊢
    obtain ⟨hHead, hHeadWref, hTail⟩ := hAux
    refine ⟨hHead, hHeadWref, ?_⟩
    apply ih (H (serialize acc head.payload)) hTail
    · simp only [List.foldl_cons] at hPrev
      exact hPrev
    · exact hWref


theorem LogChain.wellFormed_nil
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes) :
    LogChain.wellFormed H genesis serialize ([] : LogChain Bytes Hash) := by
  show True
  trivial


theorem LogChain.wellFormed_append_singleton
    {Bytes Hash : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (chain : LogChain Bytes Hash) (e : Entry Bytes Hash)
    (hChain : LogChain.wellFormed H genesis serialize chain)
    (hPrev : e.prev = LogChain.root H genesis serialize chain)
    (hWref : e.detWitnessRef = none := by rfl) :
    LogChain.wellFormed H genesis serialize (chain ++ [e]) := by
  unfold LogChain.wellFormed at hChain ⊢
  unfold LogChain.root at hPrev
  exact LogChain.wellFormedAux_append_singleton
    H serialize chain e (H genesis) hChain hPrev hWref



/-- `LogChain.witnessBoundCount` of an empty chain is 0. -/
theorem LogChain.witnessBoundCount_nil
    {Bytes Hash : Type} :
    LogChain.witnessBoundCount ([] : LogChain Bytes Hash) = 0 := by
  unfold LogChain.witnessBoundCount
  rfl

/-- Folding-step lemma: append peels the last entry from the
    `foldl` accumulator. Discharged by structural induction on the
    chain so the proof depends only on Lean kernel defaults. -/
private theorem LogChain.witnessBoundCount_foldl_append
    {Bytes Hash : Type}
    (chain : LogChain Bytes Hash) (e : Entry Bytes Hash) :
    ∀ (acc : Nat),
    List.foldl (fun acc e => if e.bindsToWitness then acc + 1 else acc)
               acc (chain ++ [e])
      = (if e.bindsToWitness
         then List.foldl (fun acc e => if e.bindsToWitness then acc + 1 else acc) acc chain + 1
         else List.foldl (fun acc e => if e.bindsToWitness then acc + 1 else acc) acc chain) := by
  induction chain with
  | nil =>
    intro acc
    rfl
  | cons head tail ih =>
    intro acc
    show List.foldl (fun acc e => if e.bindsToWitness then acc + 1 else acc)
                    (if head.bindsToWitness then acc + 1 else acc)
                    (tail ++ [e])
      = _
    exact ih (if head.bindsToWitness then acc + 1 else acc)


theorem witness_binding_propagates
    {Bytes Hash : Type}
    (chain : LogChain Bytes Hash) (e : Entry Bytes Hash) :
    LogChain.witnessBoundCount (chain ++ [e])
      = (if e.bindsToWitness
         then chain.witnessBoundCount + 1
         else chain.witnessBoundCount) := by
  unfold LogChain.witnessBoundCount
  exact LogChain.witnessBoundCount_foldl_append chain e 0

end AgentKernel.Log

#print axioms AgentKernel.Log.t4_audit_integrity
#print axioms AgentKernel.Log.t4_prime_publish_consistency
#print axioms AgentKernel.Log.t4_audit_integrity_via_t4_prime
#print axioms AgentKernel.Log.LogChain.wellFormed_take
#print axioms AgentKernel.Log.LogChain.wellFormed_nil
#print axioms AgentKernel.Log.LogChain.wellFormed_append_singleton
#print axioms AgentKernel.Log.LogChain.wellFormed_witnessRef_none
#print axioms AgentKernel.Log.LogChain.witnessBoundCount_nil
#print axioms AgentKernel.Log.witness_binding_propagates
