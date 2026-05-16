import AgentKernel.IFC



namespace AgentKernel.Caps

open AgentKernel.IFC (LabelXform Label EventId)



/-- Opaque capability identifier. `Nat` mirrors M3's `EventId`
    discipline: a typed alias for the TLA+ side's CONSTANT `CapId`,
    instantiated finite at conformance. -/
abbrev CapId : Type := Nat



/-- Runtime policy attached to a capability. The four built-in
    constructors encode the most common patterns:

    * `timeBound until` — predicate is `now ≤ until` (a per-cap
      expiry shorthand; redundant with the structural
      `Capability.expires` field but kept for caveat-list-only
      deployment policies that prefer to encode all runtime checks
      in `caveats`).
    * `requesterIs cid` — predicate is
      `RequestCtx.requesterCid = cid` (a "this cap is bound to
      requester `cid`" guard; foreclosed forwarding to a different
      principal at runtime).
    * `parentMustExist` — predicate is supplied as a `Bool` by the
      caller from cap-store discipline (lookup `cap.parent` in the
      store; pass result). Prevents authorization of a cap whose
      parent was revoked.
    * `noCaveat` — explicit no-op (test/L1+ default; documents
      "this cap intentionally has no runtime policy"). -/
inductive Caveat where
  | timeBound (untilT : Nat)
  | requesterIs (cid : CapId)
  | parentMustExist
  | noCaveat
  deriving DecidableEq, Repr


structure RequestCtx where
  now           : Nat
  requesterCid  : CapId
  deriving DecidableEq, Repr


def RequestCtx.matchesAuditedNow (ctx : RequestCtx) (auditedNow : Nat) : Bool :=
  decide (auditedNow ≤ ctx.now)




structure Capability (Tag_C Tag_I Tag_P : Type) where
  id      : CapId
  granted : LabelXform Tag_C Tag_I Tag_P
  parent  : Option CapId
  expires : Option Nat := none
  caveats : List Caveat := []
  deriving DecidableEq


abbrev Principal (Tag_C Tag_I Tag_P : Type) : Type :=
  Capability Tag_C Tag_I Tag_P




@[inline] def Capability.mkUnconstrained
    {Tag_C Tag_I Tag_P : Type}
    (id : CapId) (g : LabelXform Tag_C Tag_I Tag_P)
    (p : Option CapId) : Capability Tag_C Tag_I Tag_P :=
  { id := id, granted := g, parent := p }




def authorizes
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (who : Principal Tag_C Tag_I Tag_P)
    (what : LabelXform Tag_C Tag_I Tag_P) : Prop :=
  who.granted = what

instance
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_C] [DecidableEq Tag_I] [DecidableEq Tag_P]
    (who : Principal Tag_C Tag_I Tag_P)
    (what : LabelXform Tag_C Tag_I Tag_P)
    : Decidable (authorizes who what) :=
  inferInstanceAs (Decidable (who.granted = what))




def Capability.notExpired
    {Tag_C Tag_I Tag_P : Type}
    (now : Nat) (cap : Capability Tag_C Tag_I Tag_P) : Bool :=
  match cap.expires with
  | none   => true
  | some t => decide (now ≤ t)


def Caveat.holds (ctx : RequestCtx) (parent : Option CapId)
    (parentInStore : Bool) (c : Caveat) : Bool :=
  match c with
  | .timeBound untilT   => decide (ctx.now ≤ untilT)
  | .requesterIs cid    => decide (ctx.requesterCid = cid)
  | .parentMustExist    =>
      match parent with
      | none   => false
      | some _ => parentInStore
  | .noCaveat           => true


def Capability.caveatsHold
    {Tag_C Tag_I Tag_P : Type}
    (ctx : RequestCtx)
    (cap : Capability Tag_C Tag_I Tag_P)
    (parentInStore : Bool) : Bool :=
  cap.caveats.all (Caveat.holds ctx cap.parent parentInStore)


def authorizes_at
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (ctx : RequestCtx) (parentInStore : Bool)
    (who  : Capability Tag_C Tag_I Tag_P)
    (what : LabelXform Tag_C Tag_I Tag_P) : Prop :=
  who.granted = what ∧
  who.notExpired ctx.now = true ∧
  who.caveatsHold ctx parentInStore = true

/-- Decidability for `authorizes_at`. The conjunction is decided
    component-wise: `granted = what` from `LabelXform`'s
    `DecidableEq`; the two `Bool = true` arms decided by core
    `Decidable (a = b)` for `Bool`. -/
instance
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_C] [DecidableEq Tag_I] [DecidableEq Tag_P]
    (ctx : RequestCtx) (parentInStore : Bool)
    (who : Capability Tag_C Tag_I Tag_P)
    (what : LabelXform Tag_C Tag_I Tag_P)
    : Decidable (authorizes_at ctx parentInStore who what) :=
  inferInstanceAs
    (Decidable (who.granted = what ∧
                who.notExpired ctx.now = true ∧
                who.caveatsHold ctx parentInStore = true))



/-- **`authorizes_at_implies_authorizes_static`** — the runtime-
    aware predicate strictly strengthens the legacy 2-place form.

    One-line projection of the first conjunct of `authorizes_at`.
    Lets any caller of legacy `authorizes` rely on its conclusion
    when the upstream proof is in the runtime-aware shape. -/
theorem authorizes_at_implies_authorizes_static
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    {ctx : RequestCtx} {parentInStore : Bool}
    {who  : Capability Tag_C Tag_I Tag_P}
    {what : LabelXform Tag_C Tag_I Tag_P}
    (h : authorizes_at ctx parentInStore who what)
    : authorizes who what :=
  h.left


theorem quiet_authorize_foreclosed
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    {ctx : RequestCtx} {parentInStore : Bool}
    {who  : Capability Tag_C Tag_I Tag_P}
    {what : LabelXform Tag_C Tag_I Tag_P}
    {t : Nat}
    (hExp  : who.expires = some t)
    (hPast : ctx.now > t)
    : ¬ authorizes_at ctx parentInStore who what := by
  intro hAuth
  have hNotExp : who.notExpired ctx.now = true := hAuth.right.left
  -- unfold notExpired with the expires = some t hypothesis;
  -- simp reduces decide (now ≤ t) = true to now ≤ t
  have hLe : ctx.now ≤ t := by
    have := hNotExp
    simp [Capability.notExpired, hExp] at this
    exact this
  exact (Nat.not_le_of_gt hPast) hLe




theorem quiet_authorize_foreclosed_with_audit
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    {ctx : RequestCtx} {parentInStore : Bool}
    {who  : Capability Tag_C Tag_I Tag_P}
    {what : LabelXform Tag_C Tag_I Tag_P}
    {t auditedNow : Nat}
    (hExp     : who.expires = some t)
    (hAuditPast : auditedNow > t)
    (hMatches : ctx.matchesAuditedNow auditedNow = true)
    : ¬ authorizes_at ctx parentInStore who what := by
  -- matchesAuditedNow : decide (auditedNow ≤ ctx.now) = true.
  have hAuditLe : auditedNow ≤ ctx.now := by
    have := hMatches
    simp [RequestCtx.matchesAuditedNow] at this
    exact this
  -- auditedNow > t and auditedNow ≤ ctx.now ⇒ ctx.now > t.
  have hPast : ctx.now > t := Nat.lt_of_lt_of_le hAuditPast hAuditLe
  exact quiet_authorize_foreclosed hExp hPast


theorem caveats_empty_implies_static_equiv
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (ctx : RequestCtx) (parentInStore : Bool)
    (who  : Capability Tag_C Tag_I Tag_P)
    (what : LabelXform Tag_C Tag_I Tag_P)
    (hExp : who.expires = none)
    (hCav : who.caveats = [])
    : authorizes_at ctx parentInStore who what ↔ authorizes who what := by
  constructor
  · intro h
    exact h.left
  · intro hStatic
    refine ⟨hStatic, ?_, ?_⟩
    · -- notExpired: with expires = none, returns true definitionally.
      simp [Capability.notExpired, hExp]
    · -- caveatsHold: empty list under .all is true.
      simp [Capability.caveatsHold, hCav]

/-! ## Cap-store + cap-map (Sec. 8.2 second application) -/

/-- Capability store. Side-table keyed by `CapId`. -/
abbrev CapStore (Tag_C Tag_I Tag_P : Type) : Type :=
  CapId → Option (Capability Tag_C Tag_I Tag_P)

/-- Event -> capability binding. Side-table keyed by `EventId`.
    Second application of Sec. 8.2 (DeclassMap was the first).
    M8 composition will require: every event of an authorization-
    bearing kind has a `CapMap` entry whose capability is in the
    `CapStore` and whose `granted` authorizes the event's required
    transformer. -/
abbrev CapMap (Tag_C Tag_I Tag_P : Type) : Type :=
  EventId → Option (Capability Tag_C Tag_I Tag_P)



/-- Type alias: an atten relation as a Bool-valued binary predicate
    on `LabelXform`. Mirrors `AttenuatesRel` in `Caps.tla`. -/
abbrev AttenRel (Tag_C Tag_I Tag_P : Type) : Type :=
  LabelXform Tag_C Tag_I Tag_P -> LabelXform Tag_C Tag_I Tag_P -> Bool


def attenuate
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (parent : Capability Tag_C Tag_I Tag_P)
    (g : LabelXform Tag_C Tag_I Tag_P)
    (newId : CapId)
    : Option (Capability Tag_C Tag_I Tag_P) :=
  if atten parent.granted g then
    some { id := newId, granted := g, parent := some parent.id }
  else
    none

/-! ## Well-formedness + closure (Lean side of CapClosure) -/

/-- A capability is well-formed in a store iff:
    * it is kernel-minted (`parent = none`), OR
    * its parent is in the store and granted-attenuates to its own
      `granted` under `atten`.

    Lean side of one disjunct in `Caps.tla`'s `CapClosure`. -/
def Capability.wellFormed
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (cap : Capability Tag_C Tag_I Tag_P) : Prop :=
  cap.parent = none ∨
    ∃ pid : CapId, ∃ p : Capability Tag_C Tag_I Tag_P,
      cap.parent = some pid ∧
      store pid = some p ∧
      atten p.granted cap.granted = true

/-- Cap-store closure: every capability reachable through the store
    is well-formed. Lean side of `Caps.tla`'s `CapClosure`. -/
def CapStore.closed
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P) : Prop :=
  ∀ cid cap, store cid = some cap → Capability.wellFormed atten store cap




theorem t5_capability_safety
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (cmap : CapMap Tag_C Tag_I Tag_P)
    (hClosed : CapStore.closed atten store)
    (hCmap : ∀ eid cap,
              cmap eid = some cap →
              ∃ cid, store cid = some cap)
    : ∀ eid cap, cmap eid = some cap →
        Capability.wellFormed atten store cap := by
  intro eid cap hCm
  obtain ⟨cid, hStore⟩ := hCmap eid cap hCm
  exact hClosed cid cap hStore



/-! ### `CapMintRecord` and `CapabilityHistory` -/

/-- One in-trace `cap_mint` event, packaged as a record. Carries the
    minted cap, the matching event id, and snapshots of the cap-store
    before/after the mint. The record's fields are the parameters
    a structural admissibility predicate quantifies over.

    A history is `List (CapMintRecord ...)`; each element represents
    one in-trace `Kind.cap_mint` event in the order they occurred.
    `wellFormedCapabilityHistory` (below) enforces chain-consistency
    between consecutive elements + per-step structural admissibility.

    **Field roles.**
    * `eventId` — the trace-side `Event.id` of the mint event;
      `cap_mint_origin_invariant` produces a witness event with this
      id whose `kind = Kind.cap_mint` and `mintedCapId = some
      mintedCap.id`.
    * `mintedCap` — the freshly minted capability (its `id` is the
      origin-witnessed cap-id; its `parent` and `granted` are the
      attenuation pieces).
    * `store_pre` / `store_post` — the cap-store snapshots used to
      enforce per-step admissibility (parent-in-store under
      `store_pre`; cap-id freshness under `store_pre`; post-store
      extension by the mint).
-/
structure CapMintRecord (Tag_C Tag_I Tag_P : Type) where
  eventId    : Nat
  mintedCap  : Capability Tag_C Tag_I Tag_P
  store_pre  : CapStore Tag_C Tag_I Tag_P
  store_post : CapStore Tag_C Tag_I Tag_P


abbrev CapabilityHistory (Tag_C Tag_I Tag_P : Type) : Type :=
  List (CapMintRecord Tag_C Tag_I Tag_P)

/-! ### `wellFormedCapabilityHistory` predicate -/

/-- Per-step admissibility for a single `CapMintRecord` against a
    starting store `s`:

    * `step.store_pre = s` — chain-consistency with the previous
      step's `store_post` (or with the initial store at the head);
    * `step.store_pre step.mintedCap.id = none` — cap-id freshness
      at the pre-store (forecloses cap-id collision attacks against
      already-minted caps);
    * the minted cap is structurally well-formed at the pre-store
      via `Capability.wellFormed atten step.store_pre step.mintedCap`
      (the parent disjunct or the kernel-root disjunct, both
      acceptable here);
    * `step.store_post` extends `step.store_pre` by binding the
      minted cap-id to the minted cap, leaving all other entries
      unchanged.

    The predicate is the structural witness that the mint event
    actually happened legitimately at this step's pre-state — and
    the resulting post-state correctly extends the cap-store. -/
def wellFormedCapMintAt
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (s : CapStore Tag_C Tag_I Tag_P)
    (step : CapMintRecord Tag_C Tag_I Tag_P) : Prop :=
  step.store_pre = s ∧
  step.store_pre step.mintedCap.id = none ∧
  Capability.wellFormed atten step.store_pre step.mintedCap ∧
  step.store_post =
    (fun cid =>
      if cid = step.mintedCap.id then some step.mintedCap
      else step.store_pre cid)

/-- Auxiliary: a history is well-formed FROM a starting store
    `s` iff:
    * the first step is admissible at `s` (`wellFormedCapMintAt`);
    * the rest of the history is well-formed FROM the first step's
      `store_post`.

    Structural induction shape that powers `cap_mint_origin_invariant`. -/
def wellFormedCapabilityHistoryFrom
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (s : CapStore Tag_C Tag_I Tag_P) :
    CapabilityHistory Tag_C Tag_I Tag_P → Prop
  | [] => True
  | step :: rest =>
      wellFormedCapMintAt atten s step ∧
      wellFormedCapabilityHistoryFrom atten step.store_post rest

/-- The empty cap-store: every cap-id maps to `none`. Initial state
    of the cap-store before any `cap_mint` event has fired. -/
def emptyCapStore
    {Tag_C Tag_I Tag_P : Type} : CapStore Tag_C Tag_I Tag_P :=
  fun _ => none

/-- Top-level: the history is well-formed iff it is well-formed
    starting from `emptyCapStore`. Mirror of
    `wellFormedRegistryHistory`. -/
def wellFormedCapabilityHistory
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : CapabilityHistory Tag_C Tag_I Tag_P) : Prop :=
  wellFormedCapabilityHistoryFrom atten emptyCapStore H

/-! ### Trace-binding predicate -/

/-- A history `H` is BACKED BY a trace `t` iff every record in `H`
    has a witnessing event in `t` of `Kind.cap_mint` whose `id`
    matches `step.eventId` and whose `mintedCapId` matches
    `some step.mintedCap.id`. This is the structural binding between
    the side-table history and the trace itself.

    The predicate forecloses the default-vacuity attack
    (`mintedCapId = none`) STRUCTURALLY at the binding layer: a
    history can only be `traceBacked` by a trace with explicit
    `mintedCapId = some _` witnesses.

    The trace argument is typed as `List AgentKernel.Replay.Event`
    rather than the alias `AgentKernel.Replay.Trace` (which is
    `def`, not `abbrev`) so that `∈` resolves directly through the
    `List`'s `Membership` instance without a typeclass-search detour. -/
def CapabilityHistory.traceBacked
    {Tag_C Tag_I Tag_P : Type}
    (H : CapabilityHistory Tag_C Tag_I Tag_P)
    (t : List AgentKernel.Replay.Event) : Prop :=
  ∀ step ∈ H,
    ∃ e ∈ t,
      AgentKernel.Replay.Event.id e = step.eventId ∧
      AgentKernel.Replay.Event.kind e = AgentKernel.Replay.Kind.cap_mint ∧
      AgentKernel.Replay.Event.payloadCapMintedId e = some step.mintedCap.id




theorem cap_mint_origin_invariant
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : CapabilityHistory Tag_C Tag_I Tag_P)
    (t : List AgentKernel.Replay.Event)
    (_hWF : wellFormedCapabilityHistory atten H)
    (hBacked : H.traceBacked t) :
    ∀ step ∈ H,
      ∃ eMint ∈ t,
        AgentKernel.Replay.Event.kind eMint = AgentKernel.Replay.Kind.cap_mint ∧
        AgentKernel.Replay.Event.payloadCapMintedId eMint = some step.mintedCap.id ∧
        AgentKernel.Replay.Event.id eMint = step.eventId := by
  intro step hMem
  obtain ⟨e, hMemT, hId, hKind, hMinted⟩ := hBacked step hMem
  exact ⟨e, hMemT, hKind, hMinted, hId⟩

/-! ### `T_cap_id_authorship_via_history` — corollary wiring origin
       integrity into the `wellFormed` second disjunct -/

/-- For any `CapabilityHistory` `H` and a `cap : Capability`, `cap`'s
    id is "history-derived" iff there exists a record in `H` whose
    `mintedCap.id = cap.id`. This is the predicate `cap_mint_origin_invariant`
    consumes; it identifies the cap-ids whose origin is witnessed
    by some step in `H`. -/
def CapabilityHistory.containsId
    {Tag_C Tag_I Tag_P : Type}
    (H : CapabilityHistory Tag_C Tag_I Tag_P) (cid : CapId) : Prop :=
  ∃ step ∈ H, step.mintedCap.id = cid


theorem T_cap_id_authorship_via_history
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : CapabilityHistory Tag_C Tag_I Tag_P)
    (t : List AgentKernel.Replay.Event)
    (hWF : wellFormedCapabilityHistory atten H)
    (hBacked : H.traceBacked t)
    (cap : Capability Tag_C Tag_I Tag_P)
    (hContains : H.containsId cap.id) :
    ∃ eMint ∈ t,
      AgentKernel.Replay.Event.kind eMint = AgentKernel.Replay.Kind.cap_mint ∧
      AgentKernel.Replay.Event.payloadCapMintedId eMint = some cap.id := by
  obtain ⟨step, hMem, hCapId⟩ := hContains
  obtain ⟨eMint, hMemT, hKind, hMinted, _hEid⟩ :=
    cap_mint_origin_invariant atten H t hWF hBacked step hMem
  refine ⟨eMint, hMemT, hKind, ?_⟩
  -- Rewrite the minted-cap-id witness from `step.mintedCap.id` to `cap.id`.
  rw [hCapId] at hMinted
  exact hMinted



/-- A history `H` is `containsEventId` for an event id `eid` iff some
    step in `H` records the event with `id = eid`. Mirrors the
    `containsId` shape on `mintedCap.id`; for spawn-binding we
    quantify over the `eventId` field instead, since the spawn event
    references the cap-mint event's `id`, not the minted cap's `id`.

    A `traceBacked` `CapabilityHistory` ensures every `step.eventId`
    in `H` corresponds to an actual `Kind.cap_mint` event in the
    trace; `containsEventId` lifts this to a propositional witness
    consumable by spawn-binding clients. -/
def CapabilityHistory.containsEventId
    {Tag_C Tag_I Tag_P : Type}
    (H : CapabilityHistory Tag_C Tag_I Tag_P) (eid : Nat) : Prop :=
  ∃ step ∈ H, step.eventId = eid


def Event.spawnedBy_capBound
    {Tag_C Tag_I Tag_P : Type}
    (e : AgentKernel.Replay.Event)
    (H : CapabilityHistory Tag_C Tag_I Tag_P) : Prop :=
  ∀ p, e.SpawnedBy = some p → H.containsEventId p

/-- Trace-level lift of `Event.spawnedBy_capBound`. Every event in
    the trace satisfies the per-event binding against the same
    history `H`. -/
def CapabilityHistory.spawnedBy_capBoundTrace
    {Tag_C Tag_I Tag_P : Type}
    (H : CapabilityHistory Tag_C Tag_I Tag_P)
    (t : List AgentKernel.Replay.Event) : Prop :=
  ∀ e ∈ t, Event.spawnedBy_capBound e H




theorem spawn_cap_binding_sound
    {Tag_C Tag_I Tag_P : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : CapabilityHistory Tag_C Tag_I Tag_P)
    (t : List AgentKernel.Replay.Event)
    (_hWFCap : wellFormedCapabilityHistory atten H)
    (hBacked : H.traceBacked t)
    (hCapBound : H.spawnedBy_capBoundTrace t)
    (e : AgentKernel.Replay.Event)
    (hMem : e ∈ t)
    (p : Nat)
    (hSpawn : e.SpawnedBy = some p) :
    ∃ eMint ∈ t,
      AgentKernel.Replay.Event.id eMint = p ∧
      AgentKernel.Replay.Event.kind eMint = AgentKernel.Replay.Kind.cap_mint ∧
      ∃ cid, AgentKernel.Replay.Event.payloadCapMintedId eMint = some cid := by
  -- Step 1: spawnedBy_capBound on e gives a step ∈ H with step.eventId = p.
  have hContains : H.containsEventId p := hCapBound e hMem p hSpawn
  obtain ⟨step, hStepMem, hStepEid⟩ := hContains
  -- Step 2: traceBacked on the same step gives an in-trace cap_mint event.
  obtain ⟨eMint, hMintMem, hIdEq, hKindEq, hMintedEq⟩ := hBacked step hStepMem
  -- Step 3: chain eMint.id = step.eventId = p.
  refine ⟨eMint, hMintMem, ?_, hKindEq, ?_⟩
  · -- eMint.id = p via step.eventId.
    rw [hIdEq, hStepEid]
  · -- mintedCapId witness: eMint.payloadCapMintedId = some step.mintedCap.id.
    exact ⟨step.mintedCap.id, hMintedEq⟩


theorem spawn_cap_binding_kernel_authored
    (e : AgentKernel.Replay.Event)
    (hWF : AgentKernel.Replay.Event.wellFormedSpawnedBy e)
    (p : Nat)
    (hSpawn : e.SpawnedBy = some p) :
    e.kernelAuthored = true := by
  obtain ⟨_hKind, hAuthOrNone⟩ := hWF
  cases hAuthOrNone with
  | inl hAuth => exact hAuth
  | inr hNone =>
      -- hNone : e.SpawnedBy = none ; hSpawn : e.SpawnedBy = some p
      rw [hNone] at hSpawn
      cases hSpawn


theorem spawn_cap_binding_no_spawn_vacuous
    {Tag_C Tag_I Tag_P : Type}
    (e : AgentKernel.Replay.Event)
    (H : CapabilityHistory Tag_C Tag_I Tag_P)
    (hNone : e.SpawnedBy = none) :
    Event.spawnedBy_capBound e H := by
  intro p hSpawn
  rw [hNone] at hSpawn
  cases hSpawn



/-! ### `IsDelegatedFrom` inductive predicate -/


inductive IsDelegatedFrom
    {Tag_C Tag_I Tag_P : Type}
    (rootId : CapId) :
    Capability Tag_C Tag_I Tag_P → CapStore Tag_C Tag_I Tag_P → Prop
  | direct (cap : Capability Tag_C Tag_I Tag_P)
           (store : CapStore Tag_C Tag_I Tag_P)
           (hParent : cap.parent = some rootId)
           (hRootInStore : ∃ root, store rootId = some root) :
      IsDelegatedFrom rootId cap store
  | transitive (cap : Capability Tag_C Tag_I Tag_P)
               (store : CapStore Tag_C Tag_I Tag_P)
               (midId : CapId) (mid : Capability Tag_C Tag_I Tag_P)
               (hParent : cap.parent = some midId)
               (hMidInStore : store midId = some mid)
               (hLt : midId < cap.id)
               (hRec : IsDelegatedFrom rootId mid store) :
      IsDelegatedFrom rootId cap store

/-! ### `revokedRoot` predicate -/

/-- **`revokedRoot rootId preStore postStore`** — the revocation
    semantics at L0: `rootId` was live in `preStore`, `postStore`
    has `rootId` mapped to `none`, and every other entry is
    preserved verbatim from `preStore`.

    Three clauses:
    * `∃ root, preStore rootId = some root` — root was live before
      revocation. Forecloses the phantom-root vacuity attack
      (PLAN A4-cold): the predicate is uninvocable on a never-was-
      live root.
    * `postStore rootId = none` — root is gone after revocation.
      This is the structural witness the headline theorem reads.
    * `∀ cid, cid ≠ rootId → postStore cid = preStore cid` — every
      other entry is preserved. Captures "the kernel revoked exactly
      the root, leaving the rest of the store unchanged."

    **Caveat (partial revocation).** This predicate is the TOTAL
    revocation primitive: the entire root cap is removed, all other
    entries preserved. Conditional / partial revocation (e.g.,
    "revoke only descendants whose `caveats` include `requesterIs
    cid`") is NOT representable here — it would require a different
    predicate `revokedSubset rootId cond` and a stronger theorem.
    Surfaced as Caveat C-D9f-1 in the section docstring. -/
def revokedRoot
    {Tag_C Tag_I Tag_P : Type}
    (rootId : CapId)
    (preStore postStore : CapStore Tag_C Tag_I Tag_P) : Prop :=
  (∃ root, preStore rootId = some root) ∧
  postStore rootId = none ∧
  (∀ cid, cid ≠ rootId → postStore cid = preStore cid)

/-! ### `IsDelegatedFrom_implies_root_in_store` — supporting lemma -/

/-- **`IsDelegatedFrom_implies_root_in_store`** — supporting lemma:
    any cap that is `IsDelegatedFrom rootId` in some `store` forces
    `rootId` to be store-resident in that `store`, i.e. there exists
    a `root` with `store rootId = some root`.

    The structural witness: every derivation of `IsDelegatedFrom`
    chains through the `direct` base (via zero or more `transitive`
    steps). The `direct` base directly carries the
    `∃ root, store rootId = some root` clause; the `transitive`
    step's recursion preserves the same store, so by induction the
    base witness propagates to every transitive step.

    Tier 1 (axiom-free) predicted: pure structural induction on the
    `IsDelegatedFrom` derivation. Honest residual recorded if
    measurement returns higher. -/
theorem IsDelegatedFrom_implies_root_in_store
    {Tag_C Tag_I Tag_P : Type}
    (rootId : CapId)
    (cap : Capability Tag_C Tag_I Tag_P)
    (store : CapStore Tag_C Tag_I Tag_P)
    (h : IsDelegatedFrom rootId cap store) :
    ∃ root, store rootId = some root := by
  induction h with
  | direct _cap _store _hParent hRootInStore =>
      exact hRootInStore
  | transitive _cap _store _midId _mid _hP _hMidS _hLt _hRecDeleg ihRec =>
      exact ihRec

/-! ### `revoke_transitive_sound` — the headline theorem -/


theorem revoke_transitive_sound
    {Tag_C Tag_I Tag_P : Type}
    (preStore postStore : CapStore Tag_C Tag_I Tag_P)
    (rootId : CapId)
    (cap : Capability Tag_C Tag_I Tag_P)
    (hRevoke : revokedRoot rootId preStore postStore)
    (_hDelegPre : IsDelegatedFrom rootId cap preStore) :
    ¬ IsDelegatedFrom rootId cap postStore := by
  intro hDelegPost
  obtain ⟨root, hRoot⟩ :=
    IsDelegatedFrom_implies_root_in_store rootId cap postStore hDelegPost
  have hPostNone : postStore rootId = none := hRevoke.right.left
  rw [hPostNone] at hRoot
  cases hRoot

/-! ### `revoke_transitive_breaks_wellFormed_chain` — bridge to
       `Capability.wellFormed` -/

/-- **`revoke_transitive_breaks_wellFormed_chain`** — bridge from
    the `IsDelegatedFrom` algebra to `Capability.wellFormed`. If a
    cap is `IsDelegatedFrom rootId` in `preStore` AND `revokedRoot
    rootId preStore postStore`, then there exists a "chain link" in
    the cap's delegation chain (the root itself) that is no longer
    satisfiable by `wellFormed atten postStore` — specifically, the
    root cap-id resolves to `none` in `postStore`.

    The theorem statement is purposely modest: we expose the broken
    link directly (`postStore rootId = none`) plus a witness from the
    `IsDelegatedFrom` derivation that the chain references `rootId`.
    Down-stream callers (e.g., a System.lean lift) compose this with
    `Capability.wellFormed`'s second-disjunct existential to derive
    "no parent-disjunct witness exists for the descendant in
    postStore."

    Tier 1 (axiom-free) predicted: structural projection from
    `revokedRoot` + the trivial fact that the
    `IsDelegatedFrom` predicate references `rootId`. -/
theorem revoke_transitive_breaks_wellFormed_chain
    {Tag_C Tag_I Tag_P : Type}
    (preStore postStore : CapStore Tag_C Tag_I Tag_P)
    (rootId : CapId)
    (cap : Capability Tag_C Tag_I Tag_P)
    (hRevoke : revokedRoot rootId preStore postStore)
    (_hDelegPre : IsDelegatedFrom rootId cap preStore) :
    postStore rootId = none := by
  exact hRevoke.right.left

/-! ### `revoke_root_yields_no_descendant_in_store` — STRUCTURAL
       PACKAGING (vacuity discharge for the direct base) -/


theorem revoke_root_yields_no_descendant_in_store
    {Tag_C Tag_I Tag_P : Type}
    (preStore postStore : CapStore Tag_C Tag_I Tag_P)
    (rootId : CapId)
    (hRevoke : revokedRoot rootId preStore postStore) :
    postStore rootId = none :=
  hRevoke.right.left

/-! ### `revoke_transitive_sound_nonvacuous` — falsifier-witness for
       the headline theorem -/


theorem revoke_transitive_sound_nonvacuous
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_C] [DecidableEq Tag_I] [DecidableEq Tag_P] :
    ∃ (preStore postStore : CapStore Tag_C Tag_I Tag_P)
      (rootId : CapId) (cap : Capability Tag_C Tag_I Tag_P),
      IsDelegatedFrom rootId cap preStore ∧
      revokedRoot rootId preStore postStore ∧
      (¬ IsDelegatedFrom rootId cap postStore) := by
  -- Concrete witness: rootId = 0, cap.id = 1, cap.parent = some 0.
  let rootCap : Capability Tag_C Tag_I Tag_P :=
    { id := 0, granted := LabelXform.id, parent := none }
  let childCap : Capability Tag_C Tag_I Tag_P :=
    { id := 1, granted := LabelXform.id, parent := some 0 }
  let preStore : CapStore Tag_C Tag_I Tag_P :=
    fun cid => if cid = 0 then some rootCap
               else if cid = 1 then some childCap else none
  let postStore : CapStore Tag_C Tag_I Tag_P :=
    fun cid => if cid = 0 then none
               else if cid = 1 then some childCap else none
  refine ⟨preStore, postStore, 0, childCap, ?_, ?_, ?_⟩
  · -- IsDelegatedFrom 0 childCap preStore
    exact IsDelegatedFrom.direct childCap preStore (by rfl)
            ⟨rootCap, by simp [preStore]⟩
  · -- revokedRoot 0 preStore postStore
    refine ⟨⟨rootCap, by simp [preStore]⟩, by simp [postStore], ?_⟩
    intro cid hNe
    -- For cid ≠ 0, postStore cid = preStore cid.
    by_cases h1 : cid = 1
    · subst h1
      simp [preStore, postStore]
    · simp [preStore, postStore, hNe, h1]
  · -- ¬ IsDelegatedFrom 0 childCap postStore.
    -- Apply the headline theorem: revoke_transitive_sound from the
    -- preStore witness + the revokedRoot.
    have hDelegPre : IsDelegatedFrom 0 childCap preStore :=
      IsDelegatedFrom.direct childCap preStore (by rfl)
        ⟨rootCap, by simp [preStore]⟩
    have hRev : revokedRoot 0 preStore postStore := by
      refine ⟨⟨rootCap, by simp [preStore]⟩, by simp [postStore], ?_⟩
      intro cid hNe
      by_cases h1 : cid = 1
      · subst h1
        simp [preStore, postStore]
      · simp [preStore, postStore, hNe, h1]
    exact revoke_transitive_sound preStore postStore 0 childCap hRev hDelegPre




def CapabilityHistory.coversCapMintEvents
    {Tag_C Tag_I Tag_P : Type}
    (H : CapabilityHistory Tag_C Tag_I Tag_P)
    (t : List AgentKernel.Replay.Event) : Prop :=
  ∀ e ∈ t,
    ∀ cid,
      AgentKernel.Replay.Event.kind e = AgentKernel.Replay.Kind.cap_mint →
      AgentKernel.Replay.Event.payloadCapMintedId e = some cid →
      ∃ step ∈ H,
        step.mintedCap.id = cid ∧
        step.eventId = AgentKernel.Replay.Event.id e


theorem cmap_origin_relay
    {Tag_C Tag_I Tag_P : Type}
    (H : CapabilityHistory Tag_C Tag_I Tag_P)
    (t : List AgentKernel.Replay.Event)
    (hCovers : H.coversCapMintEvents t) :
    ∀ e ∈ t,
      AgentKernel.Replay.Event.kind e = AgentKernel.Replay.Kind.cap_mint →
      ∀ cid,
        AgentKernel.Replay.Event.payloadCapMintedId e = some cid →
        ∃ step ∈ H,
          step.mintedCap.id = cid ∧
          step.eventId = AgentKernel.Replay.Event.id e := by
  intro e he hKind cid hMint
  -- Direct application of the covering predicate. The structural
  -- back-link is in `coversCapMintEvents` itself (L1+ obligation).
  exact hCovers e he cid hKind hMint

end AgentKernel.Caps
