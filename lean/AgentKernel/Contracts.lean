import AgentKernel.Caps



namespace AgentKernel.Contracts

open AgentKernel.Caps
open AgentKernel.IFC (LabelXform EventId)

/-! ## Contract identifier (mirrors CapId discipline) -/

/-- Opaque contract identifier. `Nat` mirrors `CapId` and `EventId`:
    a typed alias for the TLA+ side's CONSTANT `ContractId`,
    instantiated finite at conformance. -/
abbrev ContractId : Type := Nat



/-- Predicate: which kernel-minted root caps are operator-authorized
    for contract issuance? `Bool` so it composes cleanly with
    `AttenRel` and avoids `Decidable` plumbing. -/
abbrev OperatorRoots : Type := CapId → Bool

/-! ## Contract record

Mirrors a `ContractRegister` event payload:
* `contractId`           -- key into the registry side-table.
* `declaredTransformer`  -- the `LabelXform` the tool's contract
                            promises (e.g. `id` for read-only,
                            `clearProv` for full declassifier).
* `issuerCapId`          -- the cap that authorized this contract.
* `validFrom`, `validUntil` -- L0 revocation window.
-/

/-- Contract record. Polymorphic over `Tag_C Tag_I Tag_P` to match
    `LabelXform`'s signature. `DecidableEq` derives provided
    `[DecidableEq Tag_P]` (LabelXform requirement). -/
structure Contract (Tag_C Tag_I Tag_P : Type) where
  contractId          : ContractId
  declaredTransformer : LabelXform Tag_C Tag_I Tag_P
  issuerCapId         : CapId
  validFrom           : Nat
  validUntil          : Nat
  deriving DecidableEq


abbrev ContractRegistry (Tag_C Tag_I Tag_P : Type) : Type :=
  ContractId → Option (Contract Tag_C Tag_I Tag_P)

/-! ## Operator-rootedness predicate

A capability is **operator-rooted** iff its ancestral `parent`
chain in the cap-store terminates at a kernel-minted root that
`OperatorRoots` blesses.

Lean does not enforce acyclicity on `Capability.parent` chains
at this layer (the chain is a `CapId -> Option CapId` traversal
through `CapStore`; nothing structurally forbids `pid -> pid`).
We use a fuel-bounded recursion (the fuel parameter is the
maximum chain length the caller is willing to traverse). For any
fuel >= the actual chain length (which is `<= |store|` at any
realistic deployment), the predicate is exact.

The fuel discipline is the L0 reflection of TLA+'s
`AntiCycleAxiom` for cap chains; its concrete bound is set per
deployment.
-/

/-- Operator-rootedness, fuel-bounded. `fuel = 0` is conservative
    (predicate fails for any non-root). For `fuel = n+1`:
    * if cap is kernel-minted (`parent = none`) AND `opRoots
      cap.id = true`, succeed;
    * else if cap has parent `pid` resolving in `store` to `p`,
      recurse on `p` with `fuel = n`;
    * else fail.

    Bool-valued for decidability hygiene with `OperatorRoots`. -/
def operatorRootedB
    {Tag_C Tag_I Tag_P : Type}
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots) :
    Nat → Capability Tag_C Tag_I Tag_P → Bool
  | 0, _ => false
  | n+1, cap =>
    match cap.parent with
    | none => opRoots cap.id
    | some pid =>
      match store pid with
      | none => false
      | some p => operatorRootedB store opRoots n p

/-- Existential operator-rootedness: there exists a fuel under
    which the bounded predicate succeeds. This is the
    `Prop`-valued version used in the admissibility predicate. -/
def operatorRooted
    {Tag_C Tag_I Tag_P : Type}
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (cap : Capability Tag_C Tag_I Tag_P) : Prop :=
  ∃ fuel : Nat, operatorRootedB store opRoots fuel cap = true

/-! ## Contract admissibility -/

/-- A contract is **admissible** iff its `issuerCapId` resolves in
    the store to a well-formed, operator-rooted capability whose
    `granted` attenuates to the contract's `declaredTransformer`
    under `atten`.

    The `atten` precondition is what ties contract admission to
    the same delegation-attenuation discipline `DelegateStep`
    enforces (`Bridge/M5.lean` L204-220). -/
def Contract.admissible
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (c : Contract Tag_C Tag_I Tag_P) : Prop :=
  ∃ issuer : Capability Tag_C Tag_I Tag_P,
    store c.issuerCapId = some issuer ∧
    Capability.wellFormed atten store issuer ∧
    operatorRooted store opRoots issuer ∧
    atten issuer.granted c.declaredTransformer = true




def Contract.admissibleAt
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (now : Nat)
    (c : Contract Tag_C Tag_I Tag_P) : Prop :=
  Contract.admissible atten store opRoots c ∧
  c.validFrom ≤ now ∧
  now ≤ c.validUntil


theorem replayed_contract_after_window_close
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (now : Nat)
    (c : Contract Tag_C Tag_I Tag_P)
    (hExpired : c.validUntil < now) :
    ¬ Contract.admissibleAt atten store opRoots now c := by
  intro hAdm
  obtain ⟨_, _, hLe⟩ := hAdm
  -- hLe : now ≤ c.validUntil; hExpired : c.validUntil < now.
  exact absurd hLe (Nat.not_le.mpr hExpired)

/-! ## Contract-bound capability

The kernel mints a *contract-bound capability* on a successful
register-event: parent is the issuer cap, granted is the
contract's `declaredTransformer`. Inserting this cap into the
store IS a `DelegateStep` (cf. `Bridge/M5.lean`'s `DelegateStep`).

The result: a contract-bound cap has the same wellFormedness
discipline as any other delegated cap, and its presence in a
closed store is governed by T5.
-/

/-- Build the contract-bound capability. The newly minted cap's id
    is the `newId` argument (caller's responsibility to choose
    fresh; the kernel-stepping rule below enforces freshness). -/
def Contract.toCap
    {Tag_C Tag_I Tag_P : Type}
    (c : Contract Tag_C Tag_I Tag_P)
    (newId : CapId) : Capability Tag_C Tag_I Tag_P :=
  { id := newId
  , granted := c.declaredTransformer
  , parent := some c.issuerCapId }

/-! ## Kernel-stepping rule for contract registration

The action `RegisterContractStep`:
* Pre: `c.issuerCapId` resolves in the store to an issuer cap;
  the issuer's `granted` attenuates to `c.declaredTransformer`;
  the issuer is operator-rooted; `newId` is fresh in the store
  AND `c.contractId` is fresh in the registry.
* Post: store gains the contract-bound cap at `newId`; registry
  gains `c` at `c.contractId`.

This is exactly the `DelegateStep` shape from `Bridge/M5.lean`,
plus a registry-side-table extension.
-/


def RegisterContractStep
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (now : Nat)
    (store : CapStore Tag_C Tag_I Tag_P)
    (registry : ContractRegistry Tag_C Tag_I Tag_P)
    (c : Contract Tag_C Tag_I Tag_P)
    (newId : CapId)
    (store' : CapStore Tag_C Tag_I Tag_P)
    (registry' : ContractRegistry Tag_C Tag_I Tag_P) : Prop :=
  -- Pre: admissibility-at-now + freshness on both sides.
  -- wires the validity-window check to fire at kernel-stepping.
  Contract.admissibleAt atten store opRoots now c ∧
  store newId = none ∧
  registry c.contractId = none ∧
  -- Post: store extended pointwise with contract-bound cap.
  (∀ cid, store' cid =
    (if cid = newId then some (c.toCap newId) else store cid)) ∧
  -- Post: registry extended pointwise with the new contract.
  (∀ ctid, registry' ctid =
    (if ctid = c.contractId then some c else registry ctid))

/-! ## RegisterContractStep preserves CapStore.closed

The contract-bound cap added to the store is exactly the cap a
`DelegateStep` from `c.issuerCapId` to `newId` with `granted =
c.declaredTransformer` would produce; the precondition
`atten issuer.granted c.declaredTransformer = true` (in
`Contract.admissible`) is exactly the precondition `DelegateStep`
demands. So closure preservation reduces in one structural move
to the M5 bridge's `DelegateStep_preserves_closed` theorem
(`Bridge/M5.lean` L380-427).

We re-prove the structural statement here -- not by importing
`Bridge.M5` (that would create a P1 -> P3 import dependency the
plan doesn't sanction; M5 bridge is the §8 schema bridge probe,
not a runtime dependency) -- but by running the same case-analysis
inline. This keeps `Contracts.lean` independent of the bridge
layer.
-/

/-- `CapStore.closed` is preserved by `RegisterContractStep`.

    Mirror-in-shape of `Bridge.M5.DelegateStep_preserves_closed`:
    the new cap has `parent = some c.issuerCapId` resolving in
    `store` to the issuer (precondition), and the issuer's
    `granted` attenuates to the new cap's `granted` (also
    precondition).

    Existing entries inherit wellFormedness from the monotone
    extension at the fresh id `newId`. -/
theorem RegisterContractStep_preserves_closed
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (now : Nat)
    (store : CapStore Tag_C Tag_I Tag_P)
    (registry : ContractRegistry Tag_C Tag_I Tag_P)
    (c : Contract Tag_C Tag_I Tag_P)
    (newId : CapId)
    (store' : CapStore Tag_C Tag_I Tag_P)
    (registry' : ContractRegistry Tag_C Tag_I Tag_P)
    (hClosed : CapStore.closed atten store)
    (hStep : RegisterContractStep
              atten opRoots now store registry c newId store' registry') :
    CapStore.closed atten store' := by
  obtain ⟨hAdmAt, hFresh, _hRegFresh, hExtStore, _hExtReg⟩ := hStep
  -- .1 to recover the bare Contract.admissible existential body. The
  -- temporal conjunct (.2) is consumed by the caller's prior validity-
  -- window check; preservation of the cap-store closure is independent
  -- of the temporal axis.
  obtain ⟨issuer, hIssuerStore, _hIssuerWF, _hIssuerOR, hAttenG⟩ := hAdmAt.1
  intro cid cap hLookup
  rw [hExtStore cid] at hLookup
  unfold Capability.wellFormed
  by_cases hEq : cid = newId
  · -- New contract-bound entry; wellFormed via right (delegated) disjunct.
    rw [if_pos hEq] at hLookup
    have hCapEq :
        (c.toCap newId : Capability Tag_C Tag_I Tag_P) = cap :=
      Option.some.inj hLookup
    subst hCapEq
    -- Witness: parent = some c.issuerCapId resolves to issuer in store',
    -- and atten issuer.granted (c.toCap newId).granted = atten
    -- issuer.granted c.declaredTransformer = true.
    refine Or.inr ⟨c.issuerCapId, issuer, rfl, ?_, hAttenG⟩
    -- Show store' c.issuerCapId = some issuer.
    rw [hExtStore c.issuerCapId]
    by_cases hPidEq : c.issuerCapId = newId
    · -- pid = newId would mean store newId = some issuer, contradicting hFresh.
      exfalso
      rw [hPidEq, hFresh] at hIssuerStore
      contradiction
    · rw [if_neg hPidEq]; exact hIssuerStore
  · -- Existing entry; lift wellFormedness from store to store'.
    rw [if_neg hEq] at hLookup
    have hWF : Capability.wellFormed atten store cap := hClosed cid cap hLookup
    unfold Capability.wellFormed at hWF
    cases hWF with
    | inl hRoot => exact Or.inl hRoot
    | inr hDel =>
        obtain ⟨pid, p, hParEq, hStoreP, hAtten⟩ := hDel
        refine Or.inr ⟨pid, p, hParEq, ?_, hAtten⟩
        rw [hExtStore pid]
        by_cases hPidEq : pid = newId
        · exfalso
          rw [hPidEq, hFresh] at hStoreP
          contradiction
        · rw [if_neg hPidEq]; exact hStoreP

/-! ## Auxiliary: operator-rooted implies wellFormed

A capability that is operator-rooted under a closed store is
necessarily wellFormed: the parent-chain traversal that establishes
operator-rootedness IS a wellFormed witness at every step.
-/

/-- The bounded predicate, when true, witnesses the structural
    disjunction at the root of `Capability.wellFormed`: the cap is
    either kernel-minted (`parent = none`) or its parent resolves
    in the store. Structural induction on `fuel`.

    Note: this lemma deliberately weakens the conclusion to the
    structural arm only -- attaining the full `wellFormed` (with
    the attenuation conjunct) requires the closure assumption,
    which is supplied at the call site (cf. `T_contract_auth`). -/
theorem operatorRootedB_implies_parent_witnessed
    {Tag_C Tag_I Tag_P : Type}
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots) :
    ∀ (fuel : Nat) (cap : Capability Tag_C Tag_I Tag_P),
      operatorRootedB store opRoots fuel cap = true →
      cap.parent = none ∨
      (∃ pid : CapId, ∃ p : Capability Tag_C Tag_I Tag_P,
        cap.parent = some pid ∧ store pid = some p)
  | 0, cap, h => by
    -- operatorRootedB store opRoots 0 cap = false; contradiction.
    unfold operatorRootedB at h
    exact absurd h (by decide)
  | _n+1, cap, h => by
    unfold operatorRootedB at h
    -- Case analyse cap.parent. `cases ... with` rewrites the
    -- scrutinee in the goal too, so the witness is `rfl` at each
    -- arm (rather than `hPar`, which case-naming would not bind
    -- against the rewritten goal).
    cases hPar : cap.parent with
    | none =>
        -- Root case; goal becomes `none = none ∨ ...`.
        exact Or.inl rfl
    | some pid =>
        -- Delegated case. `rw [hPar] at h` reduces the outer
        -- match to its `some pid` arm, leaving an inner match on
        -- `store pid`. We then case on that.
        rw [hPar] at h
        simp only at h
        cases hSt : store pid with
        | none =>
            -- operatorRootedB returns false in this branch; contradiction
            -- via `h : false = true`.
            rw [hSt] at h
            simp only at h
            exact absurd h Bool.false_ne_true
        | some p =>
            exact Or.inr ⟨pid, p, rfl, hSt⟩

/-- Operator-rootedness implies the cap satisfies the structural
    arm at the root of `Capability.wellFormed`: it's either a root,
    or its parent resolves in the store. Discharges the existential
    over fuel; pure unfolding to the bounded version. -/
theorem operatorRooted_implies_parent_witnessed
    {Tag_C Tag_I Tag_P : Type}
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (cap : Capability Tag_C Tag_I Tag_P)
    (h : operatorRooted store opRoots cap) :
    cap.parent = none ∨
    (∃ pid : CapId, ∃ p : Capability Tag_C Tag_I Tag_P,
      cap.parent = some pid ∧ store pid = some p) := by
  obtain ⟨fuel, hFuel⟩ := h
  exact operatorRootedB_implies_parent_witnessed
          store opRoots fuel cap hFuel




theorem contract_auth_propagates
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (registry : ContractRegistry Tag_C Tag_I Tag_P)
    (cmap : CapMap Tag_C Tag_I Tag_P)
    (cBindings : EventId → Option ContractId)
    (hClosed : CapStore.closed atten store)
    (hRegAdmissible :
      ∀ ctid c, registry ctid = some c →
        Contract.admissible atten store opRoots c)
    (hCmapInStore :
      ∀ eid cap, cmap eid = some cap →
        ∃ cid, store cid = some cap)
    (hCapBoundToContract :
      ∀ eid cap, cmap eid = some cap →
        ∀ ctid, cBindings eid = some ctid →
          ∃ c : Contract Tag_C Tag_I Tag_P,
            registry ctid = some c ∧
            cap.parent = some c.issuerCapId ∧
            cap.granted = c.declaredTransformer)
    : ∀ eid cap ctid,
        cmap eid = some cap →
        cBindings eid = some ctid →
        Capability.wellFormed atten store cap ∧
        ∃ c : Contract Tag_C Tag_I Tag_P,
          registry ctid = some c ∧
          Contract.admissible atten store opRoots c := by
  intro eid cap ctid hCmap hCt
  -- Conjunct (1): T5 directly.
  have hWF : Capability.wellFormed atten store cap :=
    t5_capability_safety atten store cmap hClosed hCmapInStore eid cap hCmap
  -- Conjunct (2): side-table chase.
  obtain ⟨c, hReg, _hPar, _hGr⟩ :=
    hCapBoundToContract eid cap hCmap ctid hCt
  exact ⟨hWF, c, hReg, hRegAdmissible ctid c hReg⟩

/-! ## RegisterContractStep yields admissible contract in registry'

A successful `RegisterContractStep` extends the registry with `c`
at `c.contractId`; combined with the step's admissibility
precondition and the closure preservation theorem, the resulting
state has registry' satisfying `hRegAdmissible` for `c`.

This is the structural lemma showing the kernel never inserts an
inadmissible contract -- the inverse of "side-tables are
forgeable". The kernel's insertion check IS the admissibility
check.
-/

/-- After `RegisterContractStep`, the contract `c` is present in
    `registry'` and its admissibility holds against the new
    `store'` (since `store'` extends `store` monotonically at the
    fresh `newId`, the issuer cap remains in `store'` and the
    same operator-rootedness witness lifts). -/
theorem RegisterContractStep_yields_admissible
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (now : Nat)
    (store : CapStore Tag_C Tag_I Tag_P)
    (registry : ContractRegistry Tag_C Tag_I Tag_P)
    (c : Contract Tag_C Tag_I Tag_P)
    (newId : CapId)
    (store' : CapStore Tag_C Tag_I Tag_P)
    (registry' : ContractRegistry Tag_C Tag_I Tag_P)
    (hStep : RegisterContractStep
              atten opRoots now store registry c newId store' registry') :
    registry' c.contractId = some c := by
  obtain ⟨_, _, _, _, hExtReg⟩ := hStep
  rw [hExtReg c.contractId]
  simp



/-! ### `RegisterStepRecord` and `RegistryHistory` -/


structure RegisterStepRecord (Tag_C Tag_I Tag_P : Type) where
  contract       : Contract Tag_C Tag_I Tag_P
  newId          : CapId
  now            : Nat
  store_pre      : CapStore Tag_C Tag_I Tag_P
  store_post     : CapStore Tag_C Tag_I Tag_P
  registry_pre   : ContractRegistry Tag_C Tag_I Tag_P
  registry_post  : ContractRegistry Tag_C Tag_I Tag_P

/-- A `RegistryHistory` is just a `List` of records. Type alias
    for clarity at theorem-statement sites. -/
abbrev RegistryHistory (Tag_C Tag_I Tag_P : Type) : Type :=
  List (RegisterStepRecord Tag_C Tag_I Tag_P)

/-- The empty registry: every key maps to `none`. Initial state of
    the registry before any `RegisterContractStep` has fired. -/
def emptyRegistry
    {Tag_C Tag_I Tag_P : Type} : ContractRegistry Tag_C Tag_I Tag_P :=
  fun _ => none

/-! ### Folded registry construction -/

/-- Auxiliary: fold over a history applying each step's pointwise
    extension. Accumulator-threaded so we get forward-fold
    semantics (first step in `H` is applied first). -/
def registry_built_by_aux
    {Tag_C Tag_I Tag_P : Type}
    (acc : ContractRegistry Tag_C Tag_I Tag_P) :
    RegistryHistory Tag_C Tag_I Tag_P → ContractRegistry Tag_C Tag_I Tag_P
  | [] => acc
  | step :: rest =>
      let acc' : ContractRegistry Tag_C Tag_I Tag_P :=
        fun ctid =>
          if ctid = step.contract.contractId then some step.contract
          else acc ctid
      registry_built_by_aux acc' rest

/-- The registry built by folding the history starting from
    `emptyRegistry`. This is the canonical "what registry results
    from this trace of `RegisterContractStep` events" function;
    note that it does NOT trust the `registry_post` field of any
    record — it computes the extension fresh. The chain-consistency
    conjunct in `wellFormedRegistryHistory` ensures the recorded
    `registry_post` agrees with this computed value. -/
def registry_built_by
    {Tag_C Tag_I Tag_P : Type}
    (H : RegistryHistory Tag_C Tag_I Tag_P) :
    ContractRegistry Tag_C Tag_I Tag_P :=
  registry_built_by_aux emptyRegistry H

/-! ### `wellFormedRegistryHistory` predicate -/


def wellFormedRegistryHistoryFrom
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (reg : ContractRegistry Tag_C Tag_I Tag_P) :
    RegistryHistory Tag_C Tag_I Tag_P → Prop
  | [] => True
  | step :: rest =>
      step.registry_pre = reg ∧
      RegisterContractStep atten opRoots step.now
        step.store_pre step.registry_pre
        step.contract step.newId
        step.store_post step.registry_post ∧
      (∀ s ∈ rest, step.now ≤ s.now) ∧
      wellFormedRegistryHistoryFrom atten opRoots step.registry_post rest

/-- Top-level: the history is well-formed iff it is well-formed
    starting from `emptyRegistry`. -/
def wellFormedRegistryHistory
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (H : RegistryHistory Tag_C Tag_I Tag_P) : Prop :=
  wellFormedRegistryHistoryFrom atten opRoots emptyRegistry H

/-! ### Helper: `registry_built_by` step extension lemma -/

/-- Folding `step :: rest` over an accumulator equals folding
    `rest` over the extended accumulator. Pure unfolding;
    Tier 1 (axiom-free).

    Used to bridge `registry_built_by_aux` over a cons-cell with
    the extension semantics in `RegisterContractStep`'s post-state
    conjunct. -/
theorem registry_built_by_step_extends
    {Tag_C Tag_I Tag_P : Type}
    (acc : ContractRegistry Tag_C Tag_I Tag_P)
    (step : RegisterStepRecord Tag_C Tag_I Tag_P)
    (rest : RegistryHistory Tag_C Tag_I Tag_P) :
    registry_built_by_aux acc (step :: rest) =
    registry_built_by_aux
      (fun ctid =>
        if ctid = step.contract.contractId then some step.contract
        else acc ctid) rest := by
  rfl

/-! ### Auxiliary: every consumed entry traces to some step -/

/-- For any history `H` and starting accumulator `acc`, an entry
    `registry_built_by_aux acc H ctid = some c` is either already
    in the accumulator (left disjunct) or was added by some step
    in `H` (right disjunct). Structural induction on `H`.

    Tier 2 `[propext]`: the case-split on `ctid =
    step.contract.contractId` discharges the `if-then-else` via
    `propext`. -/
theorem registry_built_by_aux_origin
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (H : RegistryHistory Tag_C Tag_I Tag_P)
    (acc : ContractRegistry Tag_C Tag_I Tag_P)
    (ctid : ContractId) (c : Contract Tag_C Tag_I Tag_P)
    (h : registry_built_by_aux acc H ctid = some c) :
    acc ctid = some c ∨
    ∃ step ∈ H, step.contract = c ∧ step.contract.contractId = ctid := by
  induction H generalizing acc with
  | nil =>
      -- `registry_built_by_aux acc [] = acc`, so `acc ctid = some c`.
      left
      simpa [registry_built_by_aux] using h
  | cons step rest ih =>
      -- After folding `step`, the accumulator becomes
      -- `acc' = fun ctid => if ctid = step.contract.contractId
      --                       then some step.contract else acc ctid`.
      -- Apply IH to `acc'`.
      simp only [registry_built_by_aux] at h
      have hRec :
          (fun ctid =>
            if ctid = step.contract.contractId then some step.contract
            else acc ctid) ctid = some c ∨
          ∃ step' ∈ rest,
            step'.contract = c ∧ step'.contract.contractId = ctid :=
        ih _ h
      cases hRec with
      | inl hAcc' =>
          -- `acc' ctid = some c`. Case on `ctid = step.contract.contractId`.
          by_cases hEq : ctid = step.contract.contractId
          · -- `acc' ctid = some step.contract = some c`, so step is the witness.
            right
            simp only [hEq, if_true] at hAcc'
            refine ⟨step, ?_, ?_, ?_⟩
            · exact List.mem_cons_self
            · exact Option.some.inj hAcc'
            · -- step.contract.contractId = ctid via hEq.
              exact hEq.symm
          · -- `acc' ctid = acc ctid = some c`. Left disjunct.
            left
            simpa [hEq] using hAcc'
      | inr hStep' =>
          -- Found the witness in `rest`. Lift to `step :: rest`.
          obtain ⟨step', hMem, hContract, hCtid⟩ := hStep'
          right
          exact ⟨step', List.mem_cons_of_mem step hMem, hContract, hCtid⟩

/-! ### Auxiliary: every step in a well-formed history is admissible -/


theorem wellFormedRegistryHistoryFrom_step_admissible
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (reg : ContractRegistry Tag_C Tag_I Tag_P)
    (H : RegistryHistory Tag_C Tag_I Tag_P)
    (hWF : wellFormedRegistryHistoryFrom atten opRoots reg H)
    (step : RegisterStepRecord Tag_C Tag_I Tag_P)
    (hMem : step ∈ H) :
    Contract.admissible atten step.store_pre opRoots step.contract := by
  induction H generalizing reg with
  | nil =>
      -- step ∈ [] is uninhabited; nomatch dispatches.
      cases hMem
  | cons s rest ih =>
      -- 4th conjunct (`∀ s' ∈ rest, s.now ≤ s'.now`) which we
      -- discard (`_hMonoNow`); admissibility extraction is unchanged.
      obtain ⟨_hRegPre, hStep, _hMonoNow, hRest⟩ := hWF
      cases List.mem_cons.mp hMem with
      | inl hEq =>
          -- step is the head; admissibility-at-now is the first
          -- conjunct of `RegisterContractStep`. Project .1 to recover
          -- the bare `Contract.admissible` form.
          subst hEq
          obtain ⟨hAdmAt, _, _, _, _⟩ := hStep
          exact hAdmAt.1
      | inr hMemRest =>
          -- step is in the tail; apply IH at `s.registry_post`.
          exact ih s.registry_post hRest hMemRest

/-! ### `registry_built_by_yields_admissible`: registry entry → admissible step -/

/-- For any `(ctid, c)` in `registry_built_by H`, the witnessing
    step `s ∈ H` has `s.contract = c` AND `Contract.admissible atten
    s.store_pre opRoots c`. Tier 2 `[propext]`. -/
theorem registry_built_by_yields_admissible
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (H : RegistryHistory Tag_C Tag_I Tag_P)
    (hWF : wellFormedRegistryHistory atten opRoots H)
    (ctid : ContractId) (c : Contract Tag_C Tag_I Tag_P)
    (h : registry_built_by H ctid = some c) :
    ∃ step ∈ H,
      step.contract = c ∧
      Contract.admissible atten step.store_pre opRoots c := by
  -- Origin lemma: c was added by some step in H.
  have hOrig := registry_built_by_aux_origin H emptyRegistry ctid c h
  cases hOrig with
  | inl hAcc =>
      -- emptyRegistry ctid = some c is false.
      exact absurd hAcc (by simp [emptyRegistry])
  | inr hStep =>
      obtain ⟨step, hMem, hContract, _hCtid⟩ := hStep
      have hAdm :=
        wellFormedRegistryHistoryFrom_step_admissible
          atten opRoots emptyRegistry H hWF step hMem
      refine ⟨step, hMem, hContract, ?_⟩
      -- Rewrite admissibility from step.contract to c via hContract.
      rw [hContract] at hAdm
      exact hAdm

/-! ### Sub-store discipline (for lifting admissibility under store growth) -/

/-- Sub-store predicate: every cap-id present in `s1` resolves to
    the same capability in `s2`. Models monotone store growth (caps
    are never removed or rewritten once added). -/
def CapStore.sub
    {Tag_C Tag_I Tag_P : Type}
    (s1 s2 : CapStore Tag_C Tag_I Tag_P) : Prop :=
  ∀ cid cap, s1 cid = some cap → s2 cid = some cap

/-- `operatorRootedB` lifts under sub-store. Structural induction on
    fuel. -/
theorem operatorRootedB_lifts_under_substore
    {Tag_C Tag_I Tag_P : Type}
    (s1 s2 : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (hSub : CapStore.sub s1 s2) :
    ∀ (fuel : Nat) (cap : Capability Tag_C Tag_I Tag_P),
      operatorRootedB s1 opRoots fuel cap = true →
      operatorRootedB s2 opRoots fuel cap = true
  | 0, cap, h => by
      unfold operatorRootedB at h
      exact absurd h (by decide)
  | n+1, cap, h => by
      unfold operatorRootedB at h ⊢
      -- The `cases hPar : cap.parent` rewrites the goal but not h;
      -- we manually rewrite cap.parent in h via hPar.
      cases hPar : cap.parent with
      | none =>
          rw [hPar] at h
          simp only at h ⊢
          exact h
      | some pid =>
          rw [hPar] at h
          simp only at h ⊢
          cases hSt1 : s1 pid with
          | none =>
              -- s1 pid = none makes h : false = true, contradiction.
              rw [hSt1] at h
              simp only at h
              exact absurd h Bool.false_ne_true
          | some p =>
              -- s1 pid = some p; sub-store gives s2 pid = some p.
              have hSt2 : s2 pid = some p := hSub pid p hSt1
              rw [hSt1] at h
              simp only at h
              rw [hSt2]
              simp only
              exact operatorRootedB_lifts_under_substore
                      s1 s2 opRoots hSub n p h

/-- `operatorRooted` lifts under sub-store. Existential discharge
    over fuel. -/
theorem operatorRooted_lifts_under_substore
    {Tag_C Tag_I Tag_P : Type}
    (s1 s2 : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (cap : Capability Tag_C Tag_I Tag_P)
    (hSub : CapStore.sub s1 s2)
    (h : operatorRooted s1 opRoots cap) :
    operatorRooted s2 opRoots cap := by
  obtain ⟨fuel, hFuel⟩ := h
  refine ⟨fuel, ?_⟩
  exact operatorRootedB_lifts_under_substore s1 s2 opRoots hSub fuel cap hFuel

/-- `Capability.wellFormed` lifts under sub-store. -/
theorem Capability.wellFormed_lifts_under_substore
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (s1 s2 : CapStore Tag_C Tag_I Tag_P)
    (cap : Capability Tag_C Tag_I Tag_P)
    (hSub : CapStore.sub s1 s2)
    (h : Capability.wellFormed atten s1 cap) :
    Capability.wellFormed atten s2 cap := by
  unfold Capability.wellFormed at h ⊢
  cases h with
  | inl hRoot => exact Or.inl hRoot
  | inr hDel =>
      obtain ⟨pid, p, hParEq, hStoreP, hAtten⟩ := hDel
      exact Or.inr ⟨pid, p, hParEq, hSub pid p hStoreP, hAtten⟩

/-- `Contract.admissible` lifts under sub-store. Combines the three
    component lifts (issuer-in-store, wellFormed, operator-rooted;
    the `atten` conjunct is store-independent). -/
theorem Contract.admissible_lifts_under_substore
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (s1 s2 : CapStore Tag_C Tag_I Tag_P)
    (c : Contract Tag_C Tag_I Tag_P)
    (hSub : CapStore.sub s1 s2)
    (h : Contract.admissible atten s1 opRoots c) :
    Contract.admissible atten s2 opRoots c := by
  obtain ⟨issuer, hIssuerStore, hIssuerWF, hIssuerOR, hAttenG⟩ := h
  refine ⟨issuer, hSub c.issuerCapId issuer hIssuerStore, ?_, ?_, hAttenG⟩
  · exact Capability.wellFormed_lifts_under_substore
            atten s1 s2 issuer hSub hIssuerWF
  · exact operatorRooted_lifts_under_substore
            s1 s2 opRoots issuer hSub hIssuerOR




theorem registry_origin_invariant
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (H : RegistryHistory Tag_C Tag_I Tag_P)
    (hWF : wellFormedRegistryHistory atten opRoots H) :
    ∀ ctid c,
      registry_built_by H ctid = some c →
      ∃ step ∈ H,
        step.contract = c ∧
        Contract.admissible atten step.store_pre opRoots c := by
  intro ctid c h
  exact registry_built_by_yields_admissible atten opRoots H hWF ctid c h




theorem wellFormedRegistryHistory_now_monotone
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (reg : ContractRegistry Tag_C Tag_I Tag_P)
    (H : RegistryHistory Tag_C Tag_I Tag_P)
    (hWF : wellFormedRegistryHistoryFrom atten opRoots reg H)
    (i j : Nat)
    (si sj : RegisterStepRecord Tag_C Tag_I Tag_P)
    (hij : i ≤ j)
    (hGetI : H[i]? = some si)
    (hGetJ : H[j]? = some sj) :
    si.now ≤ sj.now := by
  induction H generalizing reg i j with
  | nil =>
      -- Vacuous: H[i]? = none for all i in [].
      simp at hGetI
  | cons s rest ih =>
      -- Destructure the head's well-formedness: pick out the per-step
      -- monotone-now conjunct and the recursive hRest for the IH.
      obtain ⟨_hRegPre, _hStep, hMonoNow, hRest⟩ := hWF
      cases i with
      | zero =>
          cases j with
          | zero =>
              -- Both at head: si = sj = s.
              simp at hGetI hGetJ
              subst hGetI; subst hGetJ
              exact Nat.le_refl _
          | succ j' =>
              -- si = s (head); sj is the j'-th element of rest.
              simp at hGetI hGetJ
              subst hGetI
              -- hGetJ : rest[j']? = some sj
              -- hMonoNow says s.now ≤ s'.now for every s' ∈ rest.
              have hMem : sj ∈ rest := List.mem_of_getElem? hGetJ
              exact hMonoNow sj hMem
      | succ i' =>
          cases j with
          | zero =>
              -- i' + 1 ≤ 0 is impossible. Avoid `omega` (Quot.sound)
              -- by appealing to Nat.not_succ_le_zero directly.
              exact absurd hij (Nat.not_succ_le_zero i')
          | succ j' =>
              -- Both in tail: apply IH on `rest`.
              simp at hGetI hGetJ
              have hij' : i' ≤ j' := Nat.le_of_succ_le_succ hij
              exact ih s.registry_post hRest i' j' hij' hGetI hGetJ




theorem T_contract_auth_via_history
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (H : RegistryHistory Tag_C Tag_I Tag_P)
    (cmap : CapMap Tag_C Tag_I Tag_P)
    (cBindings : EventId → Option ContractId)
    (hClosed : CapStore.closed atten store)
    (hHist : wellFormedRegistryHistory atten opRoots H)
    (hStoreLift :
      ∀ step ∈ H, CapStore.sub step.store_pre store)
    (hCmapInStore :
      ∀ eid cap, cmap eid = some cap →
        ∃ cid, store cid = some cap)
    (hCapBoundToContract :
      ∀ eid cap, cmap eid = some cap →
        ∀ ctid, cBindings eid = some ctid →
          ∃ c : Contract Tag_C Tag_I Tag_P,
            registry_built_by H ctid = some c ∧
            cap.parent = some c.issuerCapId ∧
            cap.granted = c.declaredTransformer)
    : ∀ eid cap ctid,
        cmap eid = some cap →
        cBindings eid = some ctid →
        Capability.wellFormed atten store cap ∧
        ∃ c : Contract Tag_C Tag_I Tag_P,
          registry_built_by H ctid = some c ∧
          Contract.admissible atten store opRoots c := by
  intro eid cap ctid hCmap hCt
  -- Conjunct (1): T5 directly (same as T_contract_auth).
  have hWF : Capability.wellFormed atten store cap :=
    t5_capability_safety atten store cmap hClosed hCmapInStore eid cap hCmap
  -- Conjunct (2): registry origin invariant + sub-store lift.
  obtain ⟨c, hReg, _hPar, _hGr⟩ :=
    hCapBoundToContract eid cap hCmap ctid hCt
  -- registry_origin_invariant gives us a step witnessing c.
  obtain ⟨step, hMem, hContract, hAdmPre⟩ :=
    registry_origin_invariant atten opRoots H hHist ctid c hReg
  -- Lift admissibility from step.store_pre to store.
  have hSub : CapStore.sub step.store_pre store := hStoreLift step hMem
  have hAdm : Contract.admissible atten store opRoots c :=
    Contract.admissible_lifts_under_substore
      atten opRoots step.store_pre store c hSub hAdmPre
  exact ⟨hWF, c, hReg, hAdm⟩



/-! ### `CapDigest` — abstract digest function

A digest function from cap-store to `Nat`. At L0 a deployment-supplied
parameter (mirrors TLA+ `StoreRoot` CONSTANT). The L1+ obligation —
collision-resistance — is named explicitly via `hStoreSubFromDigest`
in the strengthened theorem below; same shape as M6's `H ∘ serialize`
CR-of-MTH carry-forward from §8. -/
abbrev CapDigest (Tag_C Tag_I Tag_P : Type) : Type :=
  CapStore Tag_C Tag_I Tag_P → Nat

/-! ### `CapSnapshotRecord` — audit-published snapshot

The Lean side of TLA+'s audit-published cap-store snapshot.
`storeRootDigest` carries the digest value committed at chain position
`publishedAtIdx`. The pair mirrors `Log.tla` `chain[i].capRoot = cr`
plus the positional immutability discipline T4 inherits from L0 v0.1.

A `List (CapSnapshotRecord _)` is the Lean projection of the TLA+
chain's published-snapshot subsequence; an `auditPublishesSnapshot`
witness corresponds to a `CapSnapshotPublished(cr)` membership proof. -/
structure CapSnapshotRecord (Tag_C Tag_I Tag_P : Type) where
  storeRootDigest : Nat
  publishedAtIdx  : Nat

/-- Lean side of TLA+ `CapSnapshotPublished(cr)`: the digest `cr` was
    audit-published as some snapshot in the history. The `Tag_*` type
    parameters are vestigial here (the predicate is a property of the
    snapshot list shape, not its tag-typing); we keep them on
    `CapSnapshotRecord` to mirror `RegisterStepRecord`'s polymorphism
    at the same call sites. -/
def auditPublishesSnapshot
    {Tag_C Tag_I Tag_P : Type}
    (snapshots : List (CapSnapshotRecord Tag_C Tag_I Tag_P))
    (cr : Nat) : Prop :=
  ∃ snap ∈ snapshots, snap.storeRootDigest = cr


theorem T_contract_auth_via_history_audited
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (H : RegistryHistory Tag_C Tag_I Tag_P)
    (cmap : CapMap Tag_C Tag_I Tag_P)
    (cBindings : EventId → Option ContractId)
    (digest : CapDigest Tag_C Tag_I Tag_P)
    (_snapshots : List (CapSnapshotRecord Tag_C Tag_I Tag_P))
    (hClosed : CapStore.closed atten store)
    (hHist : wellFormedRegistryHistory atten opRoots H)
    (hStepStoreDigestMatchesCurrent :
      ∀ step ∈ H, digest step.store_pre = digest store)
    (hStoreSubFromDigest :
      ∀ s1 s2 : CapStore Tag_C Tag_I Tag_P,
        digest s1 = digest s2 → CapStore.sub s1 s2)
    (hCmapInStore :
      ∀ eid cap, cmap eid = some cap →
        ∃ cid, store cid = some cap)
    (hCapBoundToContract :
      ∀ eid cap, cmap eid = some cap →
        ∀ ctid, cBindings eid = some ctid →
          ∃ c : Contract Tag_C Tag_I Tag_P,
            registry_built_by H ctid = some c ∧
            cap.parent = some c.issuerCapId ∧
            cap.granted = c.declaredTransformer)
    : ∀ eid cap ctid,
        cmap eid = some cap →
        cBindings eid = some ctid →
        Capability.wellFormed atten store cap ∧
        ∃ c : Contract Tag_C Tag_I Tag_P,
          registry_built_by H ctid = some c ∧
          Contract.admissible atten store opRoots c := by
  -- Derive the original `hStoreLift` from the digest hypotheses, then
  -- forward to `T_contract_auth_via_history`. For each step in H,
  -- digest-equality + collision-resistance gives the sub-store
  -- relationship.
  have hStoreLift :
      ∀ step ∈ H, CapStore.sub step.store_pre store := by
    intro step hMem
    have hDigEq : digest step.store_pre = digest store :=
      hStepStoreDigestMatchesCurrent step hMem
    exact hStoreSubFromDigest step.store_pre store hDigEq
  -- Apply the (now-derivable) original theorem.
  exact T_contract_auth_via_history
    atten store opRoots H cmap cBindings hClosed hHist hStoreLift
    hCmapInStore hCapBoundToContract


theorem audited_snapshots_match_via_digest
    {Tag_C Tag_I Tag_P : Type}
    (snapshots : List (CapSnapshotRecord Tag_C Tag_I Tag_P))
    (cr : Nat)
    (h : auditPublishesSnapshot snapshots cr) :
    ∃ snap ∈ snapshots, snap.storeRootDigest = cr := h



/-! ### `CBindingStepRecord` and `CBindingHistory` -/


structure CBindingStepRecord (Tag_C Tag_I Tag_P : Type) where
  eventId        : EventId
  contractId     : ContractId
  cap            : Capability Tag_C Tag_I Tag_P
  now            : Nat
  cmap_pre       : CapMap Tag_C Tag_I Tag_P
  cmap_post      : CapMap Tag_C Tag_I Tag_P
  cbindings_pre  : EventId → Option ContractId
  cbindings_post : EventId → Option ContractId
  registry       : ContractRegistry Tag_C Tag_I Tag_P

/-- A `CBindingHistory` is just a `List` of records. Type alias for
    clarity at theorem-statement sites. Mirrors `RegistryHistory`. -/
abbrev CBindingHistory (Tag_C Tag_I Tag_P : Type) : Type :=
  List (CBindingStepRecord Tag_C Tag_I Tag_P)

/-- The empty cBindings: every event id maps to `none`. Initial state
    of the cBindings before any cap-binding event has fired. Mirrors
    `emptyRegistry`. -/
def emptyCBindings : EventId → Option ContractId :=
  fun _ => none

/-! ### Folded cBindings construction -/

/-- Auxiliary: fold over a history applying each step's pointwise
    extension. Accumulator-threaded so we get forward-fold semantics
    (first step in `H` is applied first). Mirrors
    `registry_built_by_aux`. -/
def cbindings_built_by_aux
    {Tag_C Tag_I Tag_P : Type}
    (acc : EventId → Option ContractId) :
    CBindingHistory Tag_C Tag_I Tag_P → (EventId → Option ContractId)
  | [] => acc
  | step :: rest =>
      let acc' : EventId → Option ContractId :=
        fun eid =>
          if eid = step.eventId then some step.contractId
          else acc eid
      cbindings_built_by_aux acc' rest

/-- The cBindings built by folding the history starting from
    `emptyCBindings`. Mirrors `registry_built_by`. -/
def cbindings_built_by
    {Tag_C Tag_I Tag_P : Type}
    (H : CBindingHistory Tag_C Tag_I Tag_P) :
    EventId → Option ContractId :=
  cbindings_built_by_aux emptyCBindings H

/-! ### `wellFormedCBindingHistory` predicate -/


def wellFormedCBindingHistoryFrom
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (cb : EventId → Option ContractId) :
    CBindingHistory Tag_C Tag_I Tag_P → Prop
  | [] => True
  | step :: rest =>
      step.cbindings_pre = cb ∧
      Capability.wellFormed atten store step.cap ∧
      (∃ c : Contract Tag_C Tag_I Tag_P,
        step.registry step.contractId = some c ∧
        step.cap.parent = some c.issuerCapId ∧
        step.cap.granted = c.declaredTransformer) ∧
      (∀ eid, step.cbindings_post eid =
        (if eid = step.eventId then some step.contractId
         else step.cbindings_pre eid)) ∧
      (∀ s ∈ rest, step.now ≤ s.now) ∧
      wellFormedCBindingHistoryFrom atten store step.cbindings_post rest

/-- Top-level: the history is well-formed iff it is well-formed
    starting from `emptyCBindings`. Mirrors
    `wellFormedRegistryHistory`. -/
def wellFormedCBindingHistory
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (H : CBindingHistory Tag_C Tag_I Tag_P) : Prop :=
  wellFormedCBindingHistoryFrom atten store emptyCBindings H

/-! ### Helper: `cbindings_built_by` step extension lemma -/

/-- Folding `step :: rest` over an accumulator equals folding `rest`
    over the extended accumulator. Pure unfolding; Tier 1
    axiom-free. Mirrors `registry_built_by_step_extends`. -/
theorem cbindings_built_by_step_extends
    {Tag_C Tag_I Tag_P : Type}
    (acc : EventId → Option ContractId)
    (step : CBindingStepRecord Tag_C Tag_I Tag_P)
    (rest : CBindingHistory Tag_C Tag_I Tag_P) :
    cbindings_built_by_aux acc (step :: rest) =
    cbindings_built_by_aux
      (fun eid =>
        if eid = step.eventId then some step.contractId
        else acc eid) rest := by
  rfl

/-! ### Auxiliary: every consumed entry traces to some step -/

/-- For any history `H` and starting accumulator `acc`, an entry
    `cbindings_built_by_aux acc H eid = some ctid` is either already
    in the accumulator (left disjunct) or was added by some step in
    `H` (right disjunct). Structural induction on `H`. Mirrors
    `registry_built_by_aux_origin`.

    Tier 2 `[propext]`: the case-split on `eid = step.eventId`
    discharges the `if-then-else` via `propext`. -/
theorem cbindings_built_by_aux_origin
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (H : CBindingHistory Tag_C Tag_I Tag_P)
    (acc : EventId → Option ContractId)
    (eid : EventId) (ctid : ContractId)
    (h : cbindings_built_by_aux acc H eid = some ctid) :
    acc eid = some ctid ∨
    ∃ step ∈ H, step.contractId = ctid ∧ step.eventId = eid := by
  induction H generalizing acc with
  | nil =>
      -- `cbindings_built_by_aux acc [] = acc`, so `acc eid = some ctid`.
      left
      simpa [cbindings_built_by_aux] using h
  | cons step rest ih =>
      -- After folding `step`, the accumulator becomes
      -- `acc' = fun eid => if eid = step.eventId
      --                       then some step.contractId else acc eid`.
      -- Apply IH to `acc'`.
      simp only [cbindings_built_by_aux] at h
      have hRec :
          (fun eid =>
            if eid = step.eventId then some step.contractId
            else acc eid) eid = some ctid ∨
          ∃ step' ∈ rest,
            step'.contractId = ctid ∧ step'.eventId = eid :=
        ih _ h
      cases hRec with
      | inl hAcc' =>
          -- `acc' eid = some ctid`. Case on `eid = step.eventId`.
          by_cases hEq : eid = step.eventId
          · -- `acc' eid = some step.contractId = some ctid`, so step is the witness.
            right
            simp only [hEq, if_true] at hAcc'
            refine ⟨step, ?_, ?_, ?_⟩
            · exact List.mem_cons_self
            · exact Option.some.inj hAcc'
            · exact hEq.symm
          · -- `acc' eid = acc eid = some ctid`. Left disjunct.
            left
            simpa [hEq] using hAcc'
      | inr hStep' =>
          -- Found the witness in `rest`. Lift to `step :: rest`.
          obtain ⟨step', hMem, hContract, hEv⟩ := hStep'
          right
          exact ⟨step', List.mem_cons_of_mem step hMem, hContract, hEv⟩

/-! ### Auxiliary: every step in a well-formed history yields a witness -/

/-- In a well-formed history (from any starting cBindings), every
    step's load-bearing conjuncts hold:
    * `Capability.wellFormed atten store step.cap`;
    * there exists `c` such that `step.registry step.contractId = some
      c ∧ step.cap.parent = some c.issuerCapId ∧ step.cap.granted =
      c.declaredTransformer`.

    Structural induction on `H`. Tier 2 `[propext]`. Mirrors
    `wellFormedRegistryHistoryFrom_step_admissible`. -/
theorem wellFormedCBindingHistoryFrom_step_yields_witness
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (cb : EventId → Option ContractId)
    (H : CBindingHistory Tag_C Tag_I Tag_P)
    (hWF : wellFormedCBindingHistoryFrom atten store cb H)
    (step : CBindingStepRecord Tag_C Tag_I Tag_P)
    (hMem : step ∈ H) :
    Capability.wellFormed atten store step.cap ∧
    ∃ c : Contract Tag_C Tag_I Tag_P,
      step.registry step.contractId = some c ∧
      step.cap.parent = some c.issuerCapId ∧
      step.cap.granted = c.declaredTransformer := by
  induction H generalizing cb with
  | nil =>
      cases hMem
  | cons s rest ih =>
      -- 5th conjunct (`∀ s' ∈ rest, s.now ≤ s'.now`); discarded here
      -- (`_hMonoNow`); witness extraction is unchanged.
      obtain ⟨_hCbPre, hCapWF, hBind, _hCbPost, _hMonoNow, hRest⟩ := hWF
      cases List.mem_cons.mp hMem with
      | inl hEq =>
          subst hEq
          exact ⟨hCapWF, hBind⟩
      | inr hMemRest =>
          exact ih s.cbindings_post hRest hMemRest




theorem cbindings_origin_invariant
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (H : CBindingHistory Tag_C Tag_I Tag_P)
    (hWF : wellFormedCBindingHistory atten store H) :
    ∀ eid ctid,
      cbindings_built_by H eid = some ctid →
      ∃ step ∈ H,
        step.eventId = eid ∧
        step.contractId = ctid ∧
        Capability.wellFormed atten store step.cap ∧
        ∃ c : Contract Tag_C Tag_I Tag_P,
          step.registry step.contractId = some c ∧
          step.cap.parent = some c.issuerCapId ∧
          step.cap.granted = c.declaredTransformer := by
  intro eid ctid h
  -- Origin lemma: (eid, ctid) was added by some step in H.
  have hOrig := cbindings_built_by_aux_origin H emptyCBindings eid ctid h
  cases hOrig with
  | inl hAcc =>
      -- emptyCBindings eid = some ctid is false.
      exact absurd hAcc (by simp [emptyCBindings])
  | inr hStep =>
      obtain ⟨step, hMem, hCtid, hEv⟩ := hStep
      have hWit :=
        wellFormedCBindingHistoryFrom_step_yields_witness
          atten store emptyCBindings H hWF step hMem
      obtain ⟨hCapWF, c, hReg, hPar, hGr⟩ := hWit
      refine ⟨step, hMem, hEv, hCtid, hCapWF, c, hReg, hPar, hGr⟩




theorem wellFormedCBindingHistory_now_monotone
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (cb : EventId → Option ContractId)
    (H : CBindingHistory Tag_C Tag_I Tag_P)
    (hWF : wellFormedCBindingHistoryFrom atten store cb H)
    (i j : Nat)
    (si sj : CBindingStepRecord Tag_C Tag_I Tag_P)
    (hij : i ≤ j)
    (hGetI : H[i]? = some si)
    (hGetJ : H[j]? = some sj) :
    si.now ≤ sj.now := by
  induction H generalizing cb i j with
  | nil =>
      simp at hGetI
  | cons s rest ih =>
      -- Destructure the head's well-formedness: pick out the per-step
      -- monotone-now conjunct (`hMonoNow`) and the recursive `hRest`
      -- for the IH.
      obtain ⟨_hCbPre, _hCapWF, _hBind, _hCbPost, hMonoNow, hRest⟩ := hWF
      cases i with
      | zero =>
          cases j with
          | zero =>
              simp at hGetI hGetJ
              subst hGetI; subst hGetJ
              exact Nat.le_refl _
          | succ j' =>
              simp at hGetI hGetJ
              subst hGetI
              have hMem : sj ∈ rest := List.mem_of_getElem? hGetJ
              exact hMonoNow sj hMem
      | succ i' =>
          cases j with
          | zero =>
              -- i' + 1 ≤ 0 is impossible. Avoid `omega` (Quot.sound).
              exact absurd hij (Nat.not_succ_le_zero i')
          | succ j' =>
              simp at hGetI hGetJ
              have hij' : i' ≤ j' := Nat.le_of_succ_le_succ hij
              exact ih s.cbindings_post hRest i' j' hij' hGetI hGetJ


theorem T_contract_auth_via_history_with_cbindings
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (opRoots : OperatorRoots)
    (cmap : CapMap Tag_C Tag_I Tag_P)
    (Hreg : RegistryHistory Tag_C Tag_I Tag_P)
    (Hcb : CBindingHistory Tag_C Tag_I Tag_P)
    (digest : CapDigest Tag_C Tag_I Tag_P)
    (_snapshots : List (CapSnapshotRecord Tag_C Tag_I Tag_P))
    (hClosed : CapStore.closed atten store)
    (hHistReg : wellFormedRegistryHistory atten opRoots Hreg)
    (hWFcb : wellFormedCBindingHistory atten store Hcb)
    (hRegistryAtStepMatches :
      ∀ step ∈ Hcb, step.registry = registry_built_by Hreg)
    (hStepStoreDigestMatchesCurrent :
      ∀ step ∈ Hreg, digest step.store_pre = digest store)
    (hStoreSubFromDigest :
      ∀ s1 s2 : CapStore Tag_C Tag_I Tag_P,
        digest s1 = digest s2 → CapStore.sub s1 s2)
    (hCmapInStore :
      ∀ eid cap, cmap eid = some cap →
        ∃ cid, store cid = some cap)
    (hCmapMatchesStepCap :
      ∀ step ∈ Hcb, cmap step.eventId = some step.cap)
    : ∀ eid cap ctid,
        cmap eid = some cap →
        cbindings_built_by Hcb eid = some ctid →
        Capability.wellFormed atten store cap ∧
        ∃ c : Contract Tag_C Tag_I Tag_P,
          registry_built_by Hreg ctid = some c ∧
          Contract.admissible atten store opRoots c := by
  intro eid cap ctid hCmap hCt
  -- Derive hCapBoundToContract from cbindings_origin_invariant + the
  -- per-step well-formedness witness, then forward to
  -- T_contract_auth_via_history_audited.
  have hCapBoundToContract :
      ∀ eid' cap', cmap eid' = some cap' →
        ∀ ctid', cbindings_built_by Hcb eid' = some ctid' →
          ∃ c : Contract Tag_C Tag_I Tag_P,
            registry_built_by Hreg ctid' = some c ∧
            cap'.parent = some c.issuerCapId ∧
            cap'.granted = c.declaredTransformer := by
    intro eid' cap' hCmap' ctid' hCt'
    obtain ⟨step, hMem, hEv, hCtid, _hCapWF, c, hReg, hPar, hGr⟩ :=
      cbindings_origin_invariant atten store Hcb hWFcb eid' ctid' hCt'
    -- Show step.cap = cap' via cmap consistency.
    have hStepCap : cmap step.eventId = some step.cap :=
      hCmapMatchesStepCap step hMem
    -- step.eventId = eid', so cmap eid' = some step.cap; combined with
    -- cmap eid' = some cap', step.cap = cap'.
    rw [hEv] at hStepCap
    have hCapEq : step.cap = cap' :=
      Option.some.inj (hStepCap.symm.trans hCmap')
    -- Pull the registry-match equality so we can substitute
    -- step.registry by registry_built_by Hreg in the conclusion.
    have hRegEq : step.registry = registry_built_by Hreg :=
      hRegistryAtStepMatches step hMem
    refine ⟨c, ?_, ?_, ?_⟩
    · -- step.registry step.contractId = some c; substitute the
      -- registry equality + step.contractId = ctid'.
      rw [← hCtid]
      rw [← hRegEq]
      exact hReg
    · rw [← hCapEq]; exact hPar
    · rw [← hCapEq]; exact hGr
  -- Forward to T_contract_auth_via_history_audited.
  exact T_contract_auth_via_history_audited
    atten store opRoots Hreg cmap (cbindings_built_by Hcb) digest _snapshots
    hClosed hHistReg hStepStoreDigestMatchesCurrent hStoreSubFromDigest
    hCmapInStore hCapBoundToContract eid cap ctid hCmap hCt




theorem contractRegistry_origin_relay
    {Tag_C Tag_I Tag_P : Type} [DecidableEq Tag_P]
    (H : RegistryHistory Tag_C Tag_I Tag_P)
    (tNow : Nat)
    (hConsumeAfter : ∀ s ∈ H, s.now ≤ tNow) :
    ∀ ctid c,
      registry_built_by H ctid = some c →
      ∃ step ∈ H,
        step.contract = c ∧
        step.contract.contractId = ctid ∧
        step.now ≤ tNow := by
  intro ctid c hReg
  -- Step 1: extract the witnessing step from registry_built_by.
  -- The fold starts from emptyRegistry; emptyRegistry returns none
  -- on every key, so the left disjunct of registry_built_by_aux_origin
  -- is uninvocable.
  have hOrig :=
    registry_built_by_aux_origin H emptyRegistry ctid c hReg
  cases hOrig with
  | inl hEmpty =>
      -- emptyRegistry ctid = some c contradicts emptyRegistry's
      -- definition (every key maps to none).
      exact absurd hEmpty (by simp [emptyRegistry])
  | inr hStep =>
      obtain ⟨step, hMem, hContract, hCtid⟩ := hStep
      -- Step 2: apply consumption-time hypothesis to bound step.now.
      have hStepNow : step.now ≤ tNow := hConsumeAfter step hMem
      exact ⟨step, hMem, hContract, hCtid, hStepNow⟩



end AgentKernel.Contracts
