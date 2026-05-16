import AgentKernel.Replay.Payload




set_option maxHeartbeats 800000


namespace AgentKernel

inductive KernelOrTenant : Type
  | kernel
  | tenant
  deriving DecidableEq, Repr

end AgentKernel

namespace AgentKernel.Replay


abbrev TenantId : Type := Nat


inductive Mode : Type
  | live
  | replay
  deriving DecidableEq, Repr




inductive Kind : Type
  -- DetKinds
  | spawn
  | commit
  | attest
  | read
  | write
  | declassify
  | cancel
  | declassMint
  | cap_mint
  | retract
  | plan
  | exec
  | refusal
  | contractViolation
  | session_bind
  | contractRegister
  | humanGate
  -- NonDetKinds
  | externalReq
  | externalResp
  | sample
  | time
  deriving DecidableEq, Repr


@[irreducible]
def Kind.isDet : Kind → Bool
  | .spawn | .commit | .attest | .read | .write | .declassify | .cancel
  | .declassMint | .cap_mint | .retract
  | .plan | .exec | .refusal | .contractViolation
  | .session_bind | .contractRegister
  | .humanGate => true
  | .externalReq | .externalResp | .sample | .time => false

def Kind.isNonDet (k : Kind) : Bool := !k.isDet




@[irreducible]
def Kind.isObservable : Kind → Bool
  | .externalReq | .commit | .attest => true
  | _ => false

def Kind.isInternal (k : Kind) : Bool := !k.isObservable




@[irreducible]
def Kind.isKernelEmit : Kind → Bool
  | .externalReq | .externalResp | .read => true
  | _ => false


def Kind.allKinds : List Kind :=
  [ -- DetKinds (17)
    Kind.spawn, Kind.commit, Kind.attest, Kind.read, Kind.write,
    Kind.declassify, Kind.cancel, Kind.declassMint, Kind.cap_mint,
    Kind.retract, Kind.plan, Kind.exec, Kind.refusal,
    Kind.contractViolation, Kind.session_bind, Kind.contractRegister,
    Kind.humanGate,
    -- NonDetKinds (4)
    Kind.externalReq, Kind.externalResp, Kind.sample, Kind.time ]


theorem cap_eq_21 : List.length Kind.allKinds = 21 := by decide


theorem cap_eq_21_exhaustive : ∀ k : Kind, k ∈ Kind.allKinds := by
  intro k; cases k <;> decide

/-! ## Deterministic witness space -/


abbrev DetWitness : Type := Unit

/-! ## Event record -/


structure Event where
  id             : Nat
  kind           : Kind
  detWitness     : Option DetWitness
  parents        : List Nat
  kernelAuthored : Bool := false
  author         : KernelOrTenant := KernelOrTenant.tenant
  SpawnedBy      : Option Nat := none
  tenant         : Option TenantId := none
  mode           : Mode := Mode.live
  payload        : EventPayload := EventPayload.base



namespace Event


@[irreducible]
def payloadCapMintedId (e : Event) : Option Nat :=
  match e.payload with
  | EventPayload.cap_mint r => some r.mintedCapId
  | _                        => none

/-- Retract-target payload accessor. Preserves v1.7
    `e.payloadRetractTarget : Option Nat` for ~33 call sites (Replay 12 +
    System 8 + M2 7 + Disclosure 1; Causality.lean's 5 sites
    project on `Causality.Event` which retains its own field). -/
@[irreducible]
def payloadRetractTarget (e : Event) : Option Nat :=
  match e.payload with
  | EventPayload.retract r => some r.retractTarget
  | _                       => none

/-- Plan→exec linkage payload accessor. Preserves v1.7
    `e.payloadLinkedExecId : Option Nat` for ~15 call sites (Replay 8 +
    System 4 + M2 3). -/
@[irreducible]
def payloadLinkedExecId (e : Event) : Option Nat :=
  match e.payload with
  | EventPayload.plan r => some r.linkedExecId
  | _                    => none

/-- Refusal reason-code payload accessor. Preserves v1.7
    `e.payloadRefusalReasonCode : Option Nat` for ~5 call sites (Replay 4 +
    M2 1). -/
@[irreducible]
def payloadRefusalReasonCode (e : Event) : Option Nat :=
  match e.payload with
  | EventPayload.refusal r => some r.refusalReasonCode
  | _                       => none

/-- Contract-violation reference payload accessor. Preserves v1.7
    `e.payloadViolationContractId : Option Nat` for ~9 call sites (Replay 6
    + System 2 + M2 1). -/
@[irreducible]
def payloadViolationContractId (e : Event) : Option Nat :=
  match e.payload with
  | EventPayload.contractViolation r => some r.violationContractId
  | _                                 => none


@[irreducible]
def payloadRegisteredContractId (e : Event) : Option Nat :=
  match e.payload with
  | EventPayload.contractRegister r => some r.registeredContractId
  | _                                => none




@[irreducible]
def payloadHumanGateContext (e : Event) : Option HumanGateRecord :=
  match e.payload with
  | EventPayload.humanGate r => some r
  | _                        => none


@[irreducible]
def payloadFailureMode (e : Event) : Option FailureMode :=
  match e.payload with
  | EventPayload.failureMode r => some r.mode
  | _                          => none


theorem payloadHumanGateContext_unfold (e : Event) :
    e.payloadHumanGateContext =
      (match e.payload with
       | EventPayload.humanGate r => some r
       | _                        => none) := by
  unfold Event.payloadHumanGateContext
  rfl


theorem payloadFailureMode_unfold (e : Event) :
    e.payloadFailureMode =
      (match e.payload with
       | EventPayload.failureMode r => some r.mode
       | _                          => none) := by
  unfold Event.payloadFailureMode
  rfl


@[irreducible]
def payloadEnvBinding (e : Event) : Option Nat :=
  match e.payload with
  | EventPayload.envBinding r => some r.digest
  | _                          => none


theorem payloadEnvBinding_unfold (e : Event) :
    e.payloadEnvBinding =
      (match e.payload with
       | EventPayload.envBinding r => some r.digest
       | _                          => none) := by
  unfold Event.payloadEnvBinding
  rfl


def payloadCoherent (e : Event) : Prop :=
  match e.kind, e.payload with
  | Kind.cap_mint,          EventPayload.cap_mint _          => True
  | Kind.retract,           EventPayload.retract _           => True
  | Kind.plan,              EventPayload.plan _              => True
  | Kind.refusal,           EventPayload.refusal _           => True
  | Kind.contractViolation, EventPayload.contractViolation _ => True
  | Kind.contractRegister,  EventPayload.contractRegister _  => True
  | Kind.humanGate,         EventPayload.humanGate _         => True
  | _,                      EventPayload.failureMode _       => True
  -- authorship + explicit kernelAuthored = true discriminator are
  -- enforced separately at `Event.wellFormedEnvBinding` predicate
  -- level, NOT at this discriminator-grid coherence floor):
  | _,                      EventPayload.envBinding _        => True
  -- v1.8  backward-compat arm (default `EventPayload.base` for kinds
  -- without kind-specific state at v1.8 ; the kind-specific
  -- well-formedness predicates — wellFormedHumanGate clause (a),
  -- wellFormedFailureMode forgery defense — independently FORBID this
  -- arm for the kinds they discriminate, promoting payloadCoherent's
  -- floor to a substantive kind/payload pairing invariant at predicate
  -- level):
  | _,                      EventPayload.base                => True
  | _, _                                                     => False

end Event

/-- Trace-level coherence: every event satisfies `payloadCoherent`.
    Mirrors `Trace.captured` shape; both pointwise predicates.

    Promotes the per-event TCB obligation to the trace level for
    `Trace.wellFormed`-style aggregation in `Replay.Event.wellFormedRetraction`
    and similar predicates. -/
def Trace.payloadCoherent (t : List Event) : Prop :=
  ∀ e ∈ t, Event.payloadCoherent e


instance : Repr Event where
  reprPrec e _ := "Replay.Event⟨id := " ++ repr e.id ++ ", ..⟩"

/-- A trace is a finite list of events. Mirrors M1 `Seq(Event)`. -/
def Trace : Type := List Event

/-! ## Captured predicate -/

/--
Per-event syntactic well-witnessedness. Mirrors M1 `WellWitnessed(e)`:
deterministic events admit any (or no) witness; non-deterministic
events must carry one.
-/
def Event.wellWitnessed (e : Event) : Bool :=
  e.kind.isDet || e.detWitness.isSome

/--
Trace-level captured predicate. Decidable by direct list traversal.
Mirrors M1 `Captured(trace)`.
-/
def Trace.captured (t : Trace) : Bool :=
  t.all Event.wellWitnessed



/--
Externally-visible event. Strips internal fields (`detWitness`,
`parents`) -- those leak nothing externally and must not appear in
the simulation relation for T1-obs.

v0.1 minimal shape: `id` and `kind` only. v0.2 may add an externalized
payload field once M3 is wired through M4 / M5.
-/
structure ObservableEvent where
  id   : Nat
  kind : Kind
  deriving DecidableEq, Repr

/--
Project an event to its observable form. Internal events project to
`none`. Mirrors M1 `IsObservable` lifted through a record projection.
-/
def Event.toObservable (e : Event) : Option ObservableEvent :=
  match e.kind.isObservable with
  | true  => some { id := e.id, kind := e.kind }
  | false => none

/-- Project a trace to its observable sequence. Mirrors M1 `ObsProj`. -/
def Trace.obsProj (t : Trace) : List ObservableEvent :=
  t.filterMap Event.toObservable

/-! ## Observable equivalence -/


def Trace.equivObs (t₁ t₂ : Trace) : Prop :=
  t₁.obsProj = t₂.obsProj



/--
Per-event agreement on the four replay-relevant fields. Two events are
replay-equivalent when they carry the same `id`, `kind`, `parents`, and
`detWitness`. At v0.1 `obsProj` only inspects `id` and `kind`; the
full four-field relation future-proofs for v0.2 when `ObservableEvent`
gains a payload field determined by the witness.
-/
def Event.replayEquiv (e₁ e₂ : Event) : Prop :=
  e₁.id = e₂.id ∧ e₁.kind = e₂.kind ∧
  e₁.parents = e₂.parents ∧ e₁.detWitness = e₂.detWitness

/-- Trace-level replay equivalence: same length, pointwise `Event.replayEquiv`. -/
def Trace.replayEquiv : Trace → Trace → Prop
  | [], [] => True
  | e₁ :: t₁, e₂ :: t₂ => Event.replayEquiv e₁ e₂ ∧ Trace.replayEquiv t₁ t₂
  | _, _ => False




def Event.replayEquivStrict (e₁ e₂ : Event) : Prop :=
  e₁.id = e₂.id ∧ e₁.kind = e₂.kind ∧
  e₁.parents = e₂.parents ∧ e₁.detWitness = e₂.detWitness ∧
  e₁.kernelAuthored = e₂.kernelAuthored


def Event.parentInTrace (t : Trace) (parent_id : Nat) : Bool :=
  t.any (fun e => decide (e.id = parent_id))



/-- `toObservable` depends only on `id` and `kind` — both covered by
`replayEquiv`. Auxiliary for `t1_obs`. -/
private theorem Event.toObservable_of_replayEquiv {e₁ e₂ : Event}
    (h : Event.replayEquiv e₁ e₂) :
    e₁.toObservable = e₂.toObservable := by
  obtain ⟨hid, hkind, _, _⟩ := h
  unfold Event.toObservable
  rw [hkind, hid]


theorem t1_obs : {t₁ t₂ : Trace} → Trace.replayEquiv t₁ t₂ →
    Trace.equivObs t₁ t₂
  | [], [], _ => rfl
  | e₁ :: t₁, e₂ :: t₂, ⟨hev, htl⟩ => by
    unfold Trace.equivObs Trace.obsProj List.filterMap
    rw [Event.toObservable_of_replayEquiv hev]
    have ih := t1_obs htl
    unfold Trace.equivObs Trace.obsProj at ih
    split <;> rw [ih]




def Event.replayEquivWithMint (e₁ e₂ : Event) : Prop :=
  e₁.id = e₂.id ∧ e₁.kind = e₂.kind ∧
  e₁.parents = e₂.parents ∧ e₁.detWitness = e₂.detWitness ∧
  e₁.payloadCapMintedId = e₂.payloadCapMintedId

/-- Trace-level 5-field replay equivalence: same length, pointwise
    `Event.replayEquivWithMint`. Sibling of `Trace.replayEquiv`;
    strictly stronger. -/
def Trace.replayEquivWithMint : Trace → Trace → Prop
  | [], [] => True
  | e₁ :: t₁, e₂ :: t₂ =>
      Event.replayEquivWithMint e₁ e₂ ∧ Trace.replayEquivWithMint t₁ t₂
  | _, _ => False


theorem Event.replayEquivWithMint_implies_replayEquiv
    {e₁ e₂ : Event}
    (h : Event.replayEquivWithMint e₁ e₂) :
    Event.replayEquiv e₁ e₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩


theorem Trace.replayEquivWithMint_implies_replayEquiv :
    {t₁ t₂ : Trace} → Trace.replayEquivWithMint t₁ t₂ →
      Trace.replayEquiv t₁ t₂
  | [], [], _ => trivial
  | e₁ :: t₁, e₂ :: t₂, ⟨hev, htl⟩ =>
      ⟨Event.replayEquivWithMint_implies_replayEquiv hev,
       Trace.replayEquivWithMint_implies_replayEquiv htl⟩




def Event.replayEquivAllFields (e₁ e₂ : Event) : Prop :=
  e₁.id = e₂.id ∧ e₁.kind = e₂.kind ∧
  e₁.parents = e₂.parents ∧ e₁.detWitness = e₂.detWitness ∧
  e₁.payloadCapMintedId = e₂.payloadCapMintedId ∧
  e₁.SpawnedBy = e₂.SpawnedBy ∧
  e₁.tenant = e₂.tenant ∧
  e₁.mode = e₂.mode ∧
  e₁.payload = e₂.payload

/-- Trace-level all-fields replay equivalence: same length,
    pointwise `Event.replayEquivAllFields`. Sibling of
    `Trace.replayEquiv` and `Trace.replayEquivWithMint`; strictly
    stronger than both. -/
def Trace.replayEquivAllFields : Trace → Trace → Prop
  | [], [] => True
  | e₁ :: t₁, e₂ :: t₂ =>
      Event.replayEquivAllFields e₁ e₂ ∧ Trace.replayEquivAllFields t₁ t₂
  | _, _ => False


theorem Event.replayEquivAllFields_implies_replayEquiv
    {e₁ e₂ : Event}
    (h : Event.replayEquivAllFields e₁ e₂) :
    Event.replayEquiv e₁ e₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩


theorem Trace.replayEquivAllFields_implies_replayEquiv :
    {t₁ t₂ : Trace} → Trace.replayEquivAllFields t₁ t₂ →
      Trace.replayEquiv t₁ t₂
  | [], [], _ => trivial
  | e₁ :: t₁, e₂ :: t₂, ⟨hev, htl⟩ =>
      ⟨Event.replayEquivAllFields_implies_replayEquiv hev,
       Trace.replayEquivAllFields_implies_replayEquiv htl⟩


def Event.wellFormedSpawnedBy (e : Event) : Prop :=
  (e.kind = Kind.spawn → e.SpawnedBy ≠ none) ∧
  (e.kernelAuthored = true ∨ e.SpawnedBy = none)

/-- Trace-level lift of `Event.wellFormedSpawnedBy`. Pure
    universal-quantification over events. Stated over `List Event`
    (the `Trace` defining shape) to make `Membership` typeclass
    resolution direct; `Trace = List Event` definitionally, so
    callers can pass either. Decidable by direct list traversal
    once the per-event predicate is decidable. -/
def Trace.wellFormedSpawnedBy (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedSpawnedBy e


theorem Event.wellFormedSpawnedBy_default_event_holds
    (e : Event)
    (hKind : e.kind ≠ Kind.spawn)
    (hSpawnedBy : e.SpawnedBy = none) :
    Event.wellFormedSpawnedBy e := by
  refine ⟨?_, ?_⟩
  · intro hSpawn; exact absurd hSpawn hKind
  · exact Or.inr hSpawnedBy


def Event.wellFormedRetraction (t : List Event) (e : Event) : Prop :=
  (e.kind = Kind.retract → e.payloadRetractTarget ≠ none) ∧
  (∀ tid, e.kind = Kind.retract → e.payloadRetractTarget = some tid →
      tid ∈ e.parents) ∧
  (∀ tid, e.kind = Kind.retract → e.payloadRetractTarget = some tid →
      ∀ tgt ∈ t, tgt.id = tid → tgt.kind ≠ Kind.retract)

/-- Trace-level lift of `Event.wellFormedRetraction`. -/
def Trace.wellFormedRetraction (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedRetraction t e


def Trace.receiptValidUnderRetraction (t : List Event) (rid : Nat) : Bool :=
  !(t.any (fun e => decide (e.kind = Kind.retract) &&
                    decide (e.payloadRetractTarget = some rid)))


theorem Trace.receiptValidUnderRetraction_iff_no_retract
    (t : List Event) (rid : Nat) :
    Trace.receiptValidUnderRetraction t rid = true ↔
      ¬ (∃ e ∈ t, e.kind = Kind.retract ∧ e.payloadRetractTarget = some rid) := by
  unfold Trace.receiptValidUnderRetraction
  simp




theorem Event.replayEquiv_independent_of_SpawnedBy
    (e₁ e₂ : Event)
    (h : Event.replayEquiv e₁ e₂) :
    Event.replayEquiv e₁ e₂ := h


theorem Event.replayEquiv_independent_of_retractTarget
    (e₁ e₂ : Event)
    (h : Event.replayEquiv e₁ e₂) :
    Event.replayEquiv e₁ e₂ := h


def Event.wellFormedTenantBinding (t : List Event) (e : Event) : Prop :=
  -- clause (a): tenant equality when both sides commit to a tenant
  (∀ p_id, e.SpawnedBy = some p_id →
    ∀ p_event ∈ t, p_event.id = p_id →
      e.tenant ≠ none → p_event.tenant ≠ none →
        e.tenant = p_event.tenant) ∧
  -- clause (b): kernel-authored events may cross-tenant-spawn freely
  (∀ p_id, e.SpawnedBy = some p_id →
    ∀ p_event ∈ t, p_event.id = p_id →
      e.tenant = p_event.tenant ∨ e.kernelAuthored = true)

/-- Trace-level lift of `Event.wellFormedTenantBinding`. Pure
    universal-quantification over events. Stated over `List Event`
    (the `Trace` defining shape) to make `Membership` typeclass
    resolution direct; `Trace = List Event` definitionally, so
    callers can pass either. -/
def Trace.wellFormedTenantBinding (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedTenantBinding t e


theorem Event.wellFormedTenantBinding_no_spawn_vacuous
    (t : List Event) (e : Event)
    (hSpawn : e.SpawnedBy = none) :
    Event.wellFormedTenantBinding t e := by
  refine ⟨?_, ?_⟩
  · intro p_id hSpawnSome
    rw [hSpawn] at hSpawnSome
    cases hSpawnSome
  · intro p_id hSpawnSome
    rw [hSpawn] at hSpawnSome
    cases hSpawnSome


def Event.wellFormedReplayMode (e : Event) : Prop :=
  (e.kind.isKernelEmit = true → e.mode = Mode.live) ∧
  (e.mode = Mode.replay → e.kind.isObservable = false)

/-- Trace-level lift of `Event.wellFormedReplayMode`. Pure
    universal-quantification over events. Stated over `List Event`
    (the `Trace` defining shape) to make `Membership` typeclass
    resolution direct; `Trace = List Event` definitionally, so
    callers can pass either. -/
def Trace.wellFormedReplayMode (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedReplayMode e


theorem Event.wellFormedReplayMode_default_event_holds
    (e : Event)
    (hMode : e.mode = Mode.live) :
    Event.wellFormedReplayMode e := by
  refine ⟨?_, ?_⟩
  · intro _; exact hMode
  · intro hRep; rw [hMode] at hRep; cases hRep


def Event.wellFormedPlanExec (t : List Event) (e : Event) : Prop :=
  -- clause (a): plan-link must resolve to an exec event
  (∀ eid, e.kind = Kind.plan → e.payloadLinkedExecId = some eid →
    ∃ e' ∈ t, e'.id = eid ∧ e'.kind = Kind.exec) ∧
  -- clause (b): only plan events carry linkedExecId
  (e.kind ≠ Kind.plan → e.payloadLinkedExecId = none)

/-- Trace-level lift of `Event.wellFormedPlanExec`. -/
def Trace.wellFormedPlanExec (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedPlanExec t e


theorem Event.wellFormedPlanExec_default_event_holds
    (t : List Event) (e : Event)
    (hKind : e.kind ≠ Kind.plan)
    (hLink : e.payloadLinkedExecId = none) :
    Event.wellFormedPlanExec t e := by
  refine ⟨?_, ?_⟩
  · intro eid hPlan _; exact absurd hPlan hKind
  · intro _; exact hLink


def Event.wellFormedRefusal (e : Event) : Prop :=
  -- clause (a): refusals are non-actions
  (e.kind = Kind.refusal →
    e.detWitness = none ∧ e.payloadCapMintedId = none ∧
    e.payloadRetractTarget = none ∧ e.payloadLinkedExecId = none) ∧
  -- clause (b): violations reference a contract
  (e.kind = Kind.contractViolation → e.payloadViolationContractId ≠ none) ∧
  -- clause (c): only refusal events carry refusalReasonCode
  (e.kind ≠ Kind.refusal → e.payloadRefusalReasonCode = none) ∧
  -- clause (d): only violation events carry violationContractId
  (e.kind ≠ Kind.contractViolation → e.payloadViolationContractId = none)

/-- Trace-level lift of `Event.wellFormedRefusal`. -/
def Trace.wellFormedRefusal (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedRefusal e


theorem Event.wellFormedRefusal_default_event_holds
    (e : Event)
    (hNotRefusal : e.kind ≠ Kind.refusal)
    (hNotViolation : e.kind ≠ Kind.contractViolation)
    (hReasonNone : e.payloadRefusalReasonCode = none)
    (hVioNone : e.payloadViolationContractId = none) :
    Event.wellFormedRefusal e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hRef; exact absurd hRef hNotRefusal
  · intro hVio; exact absurd hVio hNotViolation
  · intro _; exact hReasonNone
  · intro _; exact hVioNone


def Event.wellFormedSessionBind (e : Event) : Prop :=
  -- clause (a): only kernel may author session-bind events
  (e.kind = Kind.session_bind → e.author = KernelOrTenant.kernel) ∧
  -- clause (b): kernelAuthored Bool flag agrees with author enum
  (e.kind = Kind.session_bind → e.kernelAuthored = true)

/-- Trace-level lift of `Event.wellFormedSessionBind`. Pure
    universal-quantification over events. Stated over `List Event`
    (the `Trace` defining shape) to make `Membership` typeclass
    resolution direct; `Trace = List Event` definitionally, so
    callers can pass either. Decidable by direct list traversal. -/
def Trace.wellFormedSessionBind (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedSessionBind e


theorem Event.wellFormedSessionBind_default_event_holds
    (e : Event)
    (hKind : e.kind ≠ Kind.session_bind) :
    Event.wellFormedSessionBind e := by
  refine ⟨?_, ?_⟩
  · intro hSb; exact absurd hSb hKind
  · intro hSb; exact absurd hSb hKind


def Event.wellFormedContractRegister (e : Event) : Prop :=
  -- clause (a): registry events must reference a contract by id
  -- (via dedicated `registeredContractId` field at v1.7 ; v1.6 
  -- routed via `mintedCapId` as documented honest residual)
  (e.kind = Kind.contractRegister → e.payloadRegisteredContractId ≠ none) ∧
  -- clause (b): only kernel may author a registry event
  (e.kind = Kind.contractRegister → e.author = KernelOrTenant.kernel)

/-- Trace-level lift of `Event.wellFormedContractRegister`. -/
def Trace.wellFormedContractRegister (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedContractRegister e


theorem Event.wellFormedContractRegister_default_event_holds
    (e : Event)
    (hKind : e.kind ≠ Kind.contractRegister) :
    Event.wellFormedContractRegister e := by
  refine ⟨?_, ?_⟩
  · intro hCr; exact absurd hCr hKind
  · intro hCr; exact absurd hCr hKind


def Event.wellFormedHumanGate (e : Event) : Prop :=
  -- a humanGate event must carry a HumanGateRecord payload (forbids
  -- the Kind.humanGate ∧ EventPayload.base shape that v1.8 
  -- substrate still permits at the payloadCoherent floor)
  (e.kind = Kind.humanGate →
    ∃ rec, e.payload = EventPayload.humanGate rec)
  ∧
  -- only kernel may author human-gate events (forgery defense)
  (e.kind = Kind.humanGate → e.author = KernelOrTenant.kernel)

/-- Trace-level lift of `Event.wellFormedHumanGate`. Pure
    universal-quantification over events. Stated over `List Event`
    (the `Trace` defining shape) to make `Membership` typeclass
    resolution direct; `Trace = List Event` definitionally, so
    callers can pass either. Decidable by direct list traversal. -/
def Trace.wellFormedHumanGate (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedHumanGate e


theorem Event.wellFormedHumanGate_default_event_holds
    (e : Event)
    (hKind : e.kind ≠ Kind.humanGate) :
    Event.wellFormedHumanGate e := by
  refine ⟨?_, ?_⟩
  · intro hHg; exact absurd hHg hKind
  · intro hHg; exact absurd hHg hKind


def Event.wellFormedFailureMode (e : Event) : Prop :=
  -- clause (a) forgery defense:
  -- only the kernel may author failure attestations (any failureMode
  -- payload requires kernel authorship; tenants cannot forge failure
  -- events)
  ((∃ rec, e.payload = EventPayload.failureMode rec) →
    e.author = KernelOrTenant.kernel)
  ∧
  -- clause (b) byzantine kernel-authorship discriminator:
  -- byzantine failure attestations specifically require the
  -- discipline; byzantine is the most adversarial taxonomy member)
  ((∃ rec, e.payload = EventPayload.failureMode rec ∧
      rec.mode = FailureMode.byzantine) →
    e.kernelAuthored = true)

/-- Trace-level lift of `Event.wellFormedFailureMode`. Pure
    universal-quantification over events. Stated over `List Event`
    (the `Trace` defining shape) to make `Membership` typeclass
    resolution direct; `Trace = List Event` definitionally, so
    callers can pass either. Decidable by direct list traversal. -/
def Trace.wellFormedFailureMode (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedFailureMode e


theorem Event.wellFormedFailureMode_default_event_holds
    (e : Event)
    (hPayload : ∀ rec, e.payload ≠ EventPayload.failureMode rec) :
    Event.wellFormedFailureMode e := by
  refine ⟨?_, ?_⟩
  · rintro ⟨rec, hRec⟩; exact absurd hRec (hPayload rec)
  · rintro ⟨rec, hRec, _⟩; exact absurd hRec (hPayload rec)


def Event.wellFormedEnvBinding (e : Event) : Prop :=
  -- clause (a) forgery defense:
  -- only the kernel may author env-binding events (any envBinding
  -- payload requires kernel authorship; tenants cannot forge
  -- environment-closure attestations)
  ((∃ rec, e.payload = EventPayload.envBinding rec) →
    e.author = KernelOrTenant.kernel)
  ∧
  -- clause (b) kernelAuthored discriminator:
  -- env-binding events universally require the kernelAuthored = true
  -- digest is universally kernel-computed over the closure context;
  ((∃ rec, e.payload = EventPayload.envBinding rec) →
    e.kernelAuthored = true)

/-- Trace-level lift of `Event.wellFormedEnvBinding`. Pure
    universal-quantification over events. Stated over `List Event`
    (the `Trace` defining shape) to make `Membership` typeclass
    resolution direct; `Trace = List Event` definitionally, so
    callers can pass either. Decidable by direct list traversal. -/
def Trace.wellFormedEnvBinding (t : List Event) : Prop :=
  ∀ e ∈ t, Event.wellFormedEnvBinding e


theorem Event.wellFormedEnvBinding_default_event_holds
    (e : Event)
    (hPayload : ∀ rec, e.payload ≠ EventPayload.envBinding rec) :
    Event.wellFormedEnvBinding e := by
  refine ⟨?_, ?_⟩
  · rintro ⟨rec, hRec⟩; exact absurd hRec (hPayload rec)
  · rintro ⟨rec, hRec⟩; exact absurd hRec (hPayload rec)

end AgentKernel.Replay
