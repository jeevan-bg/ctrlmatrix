import AgentKernel.Causality
import AgentKernel.Replay
import AgentKernel.IFC
import AgentKernel.IFC.LowEquiv
import AgentKernel.Caps
import AgentKernel.Log
import AgentKernel.Disclosure
import AgentKernel.MultiCell
import AgentKernel.Bridge.M2
import AgentKernel.Bridge.M3



namespace AgentKernel.System

-- ============================================================
-- ============================================================

/-- M8's unified event record. Carries the union of M2/M3/M4 Event
    fields. Projections strip down to per-module shapes. M5/M6/M7
    state lives in SystemState siblings, not here.

    The `parents_older` proof obligation is part of the record
    (M2's `Causality.Event` already carries it). Construction sites
    must discharge `forall p in parents, p < id` -- typically via
    monotone id assignment in the operational kernel (TLC bound at
    `tla/System.tla` v0.1 via `AllParentsOlder`). -/
structure SystemEvent (Tag_C Tag_I Tag_P : Type) where
  id            : Nat
  kind          : Replay.Kind
  detWitness    : Option Replay.DetWitness
  parents       : List Nat
  parents_older : ∀ p ∈ parents, p < id
  inLabel       : IFC.Label Tag_C Tag_I Tag_P
  outLabel      : IFC.Label Tag_C Tag_I Tag_P
  ctxLabel      : IFC.Label Tag_C Tag_I Tag_P
  -- Replay.Event and Causality.Event. Default `false`.
  kernelAuthored : Bool := false
  -- on Replay.Event, IFC.Event, and Causality.Event. Default
  -- `KernelOrTenant.tenant` (asymmetric closure shape; positive
  -- `kernelAuthored : Bool` flag — both name the kernel-vs-tenant
  -- author boundary at L0; the enum is the L0-structural
  -- discriminator that `IFC.taint_authorship_relay` references
  -- `event_authorship_predicate` parameter.
  author        : KernelOrTenant := KernelOrTenant.tenant
  -- side-table. Default `none` preserves all existing
  -- default-value discipline. Threaded through `toReplay` and
  -- `toCausality` projections so M3-layer / M2-layer consumers
  -- preserve the M8-layer SpawnedBy across the forgetful
  -- projection.
  SpawnedBy     : Option Nat := none
  -- Default `none` preserves byte-unchanged construction sites.
  -- Threaded through `toReplay` and `toCausality` projections.
  retractTarget : Option Nat := none
  -- Mirrors `Replay.Event.tenant : Option TenantId := none` (v1.5 
  -- `toCausality` projections; `toIFC` is structurally tenant-free
  -- (IFC discipline is tag-typed, not tenant-typed). Closes v1.5 
  tenant        : Option Replay.TenantId := none


def SystemEvent.toReplay {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) : Replay.Event :=
  { id := e.id
  , kind := e.kind
  , detWitness := e.detWitness
  , parents := e.parents
  , kernelAuthored := e.kernelAuthored
  , author := e.author
  , SpawnedBy := e.SpawnedBy
  , tenant := e.tenant
  -- SystemEvent's flat `retractTarget : Option Nat` field (the only
  -- K-class field SystemEvent currently carries; SystemEvent retains
  -- its v1.4 shape at v1.8  — only Replay.Event pivots) into the
  -- Replay.EventPayload sum: `some tid` → `EventPayload.retract ⟨tid⟩`,
  -- `none` → `EventPayload.base`. Carrier preserved per memo § 6
  -- +: when SystemEvent gains its own kind-specific fields
  -- (humanGate / failureMode / envBinding), the lift extends with
  -- new pattern arms; existing `retractTarget` arm preserved.
  , payload :=
      match e.retractTarget with
      | some tid => Replay.EventPayload.retract { retractTarget := tid }
      | none     => Replay.EventPayload.base }


def SystemEvent.toIFC {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) : IFC.Event Tag_C Tag_I Tag_P :=
  { id := e.id
  , kind := e.kind
  , inLabel := e.inLabel
  , outLabel := e.outLabel
  , ctxLabel := e.ctxLabel
  , author := e.author }


def SystemEvent.toCausality {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) : Causality.Event :=
  { id := e.id
  , parents := e.parents
  , parents_older := e.parents_older
  , kernelAuthored := e.kernelAuthored
  , author := e.author
  , SpawnedBy := e.SpawnedBy
  , retractTarget := e.retractTarget
  , tenant := e.tenant }

/-- A system trace is a list of SystemEvents. -/
abbrev SystemTrace (Tag_C Tag_I Tag_P : Type) : Type :=
  List (SystemEvent Tag_C Tag_I Tag_P)

/-- Pointwise per-event projection to a `Replay.Trace`. -/
def SystemTrace.toReplay {Tag_C Tag_I Tag_P : Type}
    (t : SystemTrace Tag_C Tag_I Tag_P) : Replay.Trace :=
  t.map SystemEvent.toReplay

/-- Pointwise per-event projection to an `IFC.Trace`. -/
def SystemTrace.toIFC {Tag_C Tag_I Tag_P : Type}
    (t : SystemTrace Tag_C Tag_I Tag_P) : IFC.Trace Tag_C Tag_I Tag_P :=
  t.map SystemEvent.toIFC

/-- Pointwise per-event projection to a `Causality.World`. -/
def SystemTrace.toCausality {Tag_C Tag_I Tag_P : Type}
    (t : SystemTrace Tag_C Tag_I Tag_P) : Causality.World :=
  t.map SystemEvent.toCausality

-- ============================================================
-- SystemState: M5/M6/M7 siblings + M4 dmap + M2/M3/M4 trace
-- ============================================================


structure SystemState
    (Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type) where
  -- M2/M3/M4 unified trace
  events      : SystemTrace Tag_C Tag_I Tag_P
  dmap        : IFC.DeclassMap
                  (Caps.Principal Tag_C Tag_I Tag_P)
                  Tag_C Tag_I Tag_P
  -- mintingTrusted bounds 's declass-mint origin Provenance;
  mintingTrusted : IFC.Factor Tag_P
  rawInputTags   : IFC.Factor Tag_P
  -- M5 capability state
  atten       : Caps.AttenRel Tag_C Tag_I Tag_P
  capStore    : Caps.CapStore Tag_C Tag_I Tag_P
  capMap      : Caps.CapMap Tag_C Tag_I Tag_P
  hashFn      : Bytes → Hash
  genesis     : Bytes
  serialize   : Hash → Bytes → Bytes
  auditChain  : Log.LogChain Bytes Hash
  -- M7 disclosure list (typeclass instance threaded externally)
  disclosures : List (Disclosure.Disclosure V Cm Pf)

-- ============================================================
-- ============================================================

/-- **T7-T1obs** -- Replay observable soundness lifted to SystemState.
    Two SystemStates whose Replay-projected traces are replay-
    equivalent are observably equivalent. Inherits from
    `Replay.t1_obs`. -/
theorem t7_inherits_t1obs
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) :
    Replay.Trace.replayEquiv s₁.events.toReplay s₂.events.toReplay →
    Replay.Trace.equivObs   s₁.events.toReplay s₂.events.toReplay := by
  intro h
  exact Replay.t1_obs h

/-- **T7-T3** -- Non-interference lifted to SystemState. Every visible
    event in a well-labeled SystemState trace satisfies its -or-
    obligation. Inherits from `IFC.t3_noninterference`, with M4's
    `Principal` pinned to `Caps.Principal` and M4's `authorizes`
    pinned to `Caps.authorizes`.

    `visible : IFC.Visible Tag_C Tag_I Tag_P` is the observer's
    clearance; passed as a parameter rather than stored in
    SystemState because multiple observers may view the same state
    differently. -/
theorem t7_inherits_t3
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq Tag_P]
    (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (visible : IFC.Visible Tag_C Tag_I Tag_P)
    (h : IFC.wellLabeled
           (@Caps.authorizes Tag_C Tag_I Tag_P _)
           s.mintingTrusted s.rawInputTags
           s.dmap s.events.toIFC) :
    ∀ e ∈ IFC.lowProj visible s.events.toIFC,
      (e.kind = Replay.Kind.declassify ∧
        ∃ p : IFC.DeclassPayload
                (Caps.Principal Tag_C Tag_I Tag_P)
                Tag_C Tag_I Tag_P,
          s.dmap e.id = some p ∧
          (@Caps.authorizes Tag_C Tag_I Tag_P _) p.who p.what ∧
          p.locus = e.id ∧
          p.when s.events.toIFC ∧
          e.outLabel.prov =
            (p.what.interp
              (IFC.Label.join e.inLabel e.ctxLabel)).prov)
      ∨
      (e.kind = Replay.Kind.declassMint ∧
        IFC.Factor.leq e.inLabel.prov s.mintingTrusted)
      ∨
      (e.kind ≠ Replay.Kind.declassify ∧
       e.kind ≠ Replay.Kind.declassMint ∧
        IFC.Factor.leq
          (IFC.Factor.join e.inLabel.prov e.ctxLabel.prov)
          e.outLabel.prov) := by
  exact IFC.t3_noninterference
    (@Caps.authorizes Tag_C Tag_I Tag_P _)
    visible s.mintingTrusted s.rawInputTags
    s.dmap s.events.toIFC h


theorem t7_inherits_t3_lowEquiv
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq Tag_P]
    (s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (visible : IFC.Visible Tag_C Tag_I Tag_P)
    (h₁ : IFC.wellLabeled
            (@Caps.authorizes Tag_C Tag_I Tag_P _)
            s₁.mintingTrusted s₁.rawInputTags
            s₁.dmap s₁.events.toIFC)
    (h₂ : IFC.wellLabeled
            (@Caps.authorizes Tag_C Tag_I Tag_P _)
            s₁.mintingTrusted s₁.rawInputTags
            s₁.dmap s₂.events.toIFC)
    (hLow : IFC.lowProj visible s₁.events.toIFC =
            IFC.lowProj visible s₂.events.toIFC) :
    IFC.lowEquiv visible s₁.events.toIFC s₂.events.toIFC := by
  exact IFC.LowEquiv.t3_low_equivalence
    (@Caps.authorizes Tag_C Tag_I Tag_P _)
    visible s₁.mintingTrusted s₁.rawInputTags s₁.dmap
    s₁.events.toIFC s₂.events.toIFC h₁ h₂ hLow


theorem t7_inherits_t4
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq Bytes] [DecidableEq Hash]
    (s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) :
    s₁.hashFn = s₂.hashFn →
    s₁.genesis = s₂.genesis →
    s₁.serialize = s₂.serialize →
    s₁.auditChain.length = s₂.auditChain.length →
    Log.LogChain.wellFormed s₁.hashFn s₁.genesis s₁.serialize
      s₁.auditChain →
    Log.LogChain.wellFormed s₂.hashFn s₂.genesis s₂.serialize
      s₂.auditChain →
    s₁.auditChain.root s₁.hashFn s₁.genesis s₁.serialize
      = s₂.auditChain.root s₂.hashFn s₂.genesis s₂.serialize →
    s₁.auditChain = s₂.auditChain ∨
      ∃ (a a' : Hash) (b b' : Bytes),
        (a, b) ≠ (a', b') ∧
        s₁.hashFn (s₁.serialize a b)
          = s₁.hashFn (s₁.serialize a' b') := by
  intro hHash hGen hSer hLen hWF1 hWF2 hRoot
  rw [← hHash, ← hGen, ← hSer] at hWF2 hRoot
  exact Log.t4_audit_integrity
    s₁.hashFn s₁.genesis s₁.serialize
    s₁.auditChain s₂.auditChain
    hLen hWF1 hWF2 hRoot

/-- **T7-T5** -- Capability safety lifted to SystemState. Every
    cap-map entry resolves to a wellFormed capability in the closed
    cap-store. Inherits from `Caps.t5_capability_safety`.

    Hypothesis `hCmap` says every event-bound capability is also
    in the cap-store (the cross-table consistency invariant);
    combined with `closed`, this forces `wellFormed`. -/
theorem t7_inherits_t5
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hClosed : Caps.CapStore.closed s.atten s.capStore)
    (hCmap : ∀ eid cap, s.capMap eid = some cap →
                        ∃ cid, s.capStore cid = some cap) :
    ∀ eid cap, s.capMap eid = some cap →
        Caps.Capability.wellFormed s.atten s.capStore cap := by
  exact Caps.t5_capability_safety
    s.atten s.capStore s.capMap hClosed hCmap

/-- **T7-T6** -- Causality acyclicity lifted to SystemState. No
    SystemEvent happens-before itself in the Causality-projected
    world. Inherits from `Causality.causality_acyclic`. -/
theorem t7_inherits_t6
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : Nat) :
    ¬ Causality.HappensBefore s.events.toCausality a a := by
  exact Causality.causality_acyclic s.events.toCausality a

/-- **T7-T8** -- Position-binding non-equivocation (single-position)
    lifted to SystemState. Two valid openings of the same position
    against the same commitment either agree on value or witness a
    position-binding violation. Inherits from
    `Disclosure.t8_disclosure_soundness`.

    The SystemState parameter `s` is part of the M8 framing but
    plays no proof-relevant role; T8's content is a fact about the
    scheme, not the state. Underscore on the binder communicates
    that intent. -/
theorem t7_inherits_t8
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq V]
    [Disclosure.VectorCommitmentScheme V Cm Pf]
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (c : Cm) (i : Nat) (v v' : V) (π π' : Pf) :
    Disclosure.VectorCommitmentScheme.verify c i v π = true →
    Disclosure.VectorCommitmentScheme.verify c i v' π' = true →
    v = v' ∨
      ∃ (c₀ : Cm) (i₀ : Nat) (a a' : V) (p p' : Pf),
        a ≠ a' ∧
        Disclosure.VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
        Disclosure.VectorCommitmentScheme.verify c₀ i₀ a' p' = true := by
  exact Disclosure.t8_disclosure_soundness c i v v' π π'

/-- **T7-T8'** -- Multi-disclosure non-equivocation (global, shape β)
    lifted to SystemState. For any two consistent disclosures in
    `s.disclosures` sharing a commitment, either they agree pointwise
    on every shared revealed position, or they witness a position-
    binding violation. Inherits from
    `Disclosure.t8'_multi_disclosure_nonequivocation`.

    The membership hypotheses (`D₁ ∈ s.disclosures`, etc.) are part
    of the M8 framing -- they assert that the disclosures live in
    the SystemState's disclosure list -- but play no proof-relevant
    role. T8''s content is a fact about the scheme, not the state. -/
theorem t7_inherits_t8'
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq V]
    [Disclosure.VectorCommitmentScheme V Cm Pf]
    (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (D₁ D₂ : Disclosure.Disclosure V Cm Pf) :
    D₁ ∈ s.disclosures →
    D₂ ∈ s.disclosures →
    D₁.commitment = D₂.commitment →
    Disclosure.Disclosure.consistent D₁ →
    Disclosure.Disclosure.consistent D₂ →
    (∀ i v₁ v₂ π₁ π₂,
        (i, v₁, π₁) ∈ D₁.openings →
        (i, v₂, π₂) ∈ D₂.openings →
        v₁ = v₂) ∨
    ∃ (c₀ : Cm) (i₀ : Nat) (a a' : V) (p p' : Pf),
        a ≠ a' ∧
        Disclosure.VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
        Disclosure.VectorCommitmentScheme.verify c₀ i₀ a' p' = true := by
  intro _ _ hC h₁ h₂
  exact Disclosure.t8'_multi_disclosure_nonequivocation D₁ D₂ hC h₁ h₂

-- ============================================================
-- ============================================================


theorem t7_compositional_refinement
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq Tag_P] [DecidableEq Bytes] [DecidableEq Hash]
    [DecidableEq V]
    [Disclosure.VectorCommitmentScheme V Cm Pf] :
    -- T1-obs lifted
    (∀ s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf,
        Replay.Trace.replayEquiv s₁.events.toReplay s₂.events.toReplay →
        Replay.Trace.equivObs s₁.events.toReplay s₂.events.toReplay)
    ∧
    (∀ (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
       (visible : IFC.Visible Tag_C Tag_I Tag_P),
        IFC.wellLabeled
          (@Caps.authorizes Tag_C Tag_I Tag_P _)
          s.mintingTrusted s.rawInputTags
          s.dmap s.events.toIFC →
        ∀ e ∈ IFC.lowProj visible s.events.toIFC,
          (e.kind = Replay.Kind.declassify ∧
            ∃ p : IFC.DeclassPayload
                    (Caps.Principal Tag_C Tag_I Tag_P)
                    Tag_C Tag_I Tag_P,
              s.dmap e.id = some p ∧
              (@Caps.authorizes Tag_C Tag_I Tag_P _) p.who p.what ∧
              p.locus = e.id ∧
              p.when s.events.toIFC ∧
              e.outLabel.prov =
                (p.what.interp
                  (IFC.Label.join e.inLabel e.ctxLabel)).prov)
          ∨
          (e.kind = Replay.Kind.declassMint ∧
            IFC.Factor.leq e.inLabel.prov s.mintingTrusted)
          ∨
          (e.kind ≠ Replay.Kind.declassify ∧
           e.kind ≠ Replay.Kind.declassMint ∧
            IFC.Factor.leq
              (IFC.Factor.join e.inLabel.prov e.ctxLabel.prov)
              e.outLabel.prov))
    ∧
    -- T4 lifted
    (∀ s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf,
        s₁.hashFn = s₂.hashFn →
        s₁.genesis = s₂.genesis →
        s₁.serialize = s₂.serialize →
        s₁.auditChain.length = s₂.auditChain.length →
        Log.LogChain.wellFormed s₁.hashFn s₁.genesis s₁.serialize
          s₁.auditChain →
        Log.LogChain.wellFormed s₂.hashFn s₂.genesis s₂.serialize
          s₂.auditChain →
        s₁.auditChain.root s₁.hashFn s₁.genesis s₁.serialize
          = s₂.auditChain.root s₂.hashFn s₂.genesis s₂.serialize →
        s₁.auditChain = s₂.auditChain ∨
          ∃ (a a' : Hash) (b b' : Bytes),
            (a, b) ≠ (a', b') ∧
            s₁.hashFn (s₁.serialize a b)
              = s₁.hashFn (s₁.serialize a' b'))
    ∧
    -- T5 lifted
    (∀ s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf,
        Caps.CapStore.closed s.atten s.capStore →
        (∀ eid cap, s.capMap eid = some cap →
                    ∃ cid, s.capStore cid = some cap) →
        ∀ eid cap, s.capMap eid = some cap →
            Caps.Capability.wellFormed s.atten s.capStore cap)
    ∧
    -- T6 lifted
    (∀ (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) (a : Nat),
        ¬ Causality.HappensBefore s.events.toCausality a a)
    ∧
    -- T8 lifted
    (∀ (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
       (c : Cm) (i : Nat) (v v' : V) (π π' : Pf),
        Disclosure.VectorCommitmentScheme.verify c i v π = true →
        Disclosure.VectorCommitmentScheme.verify c i v' π' = true →
        v = v' ∨
          ∃ (c₀ : Cm) (i₀ : Nat) (a a' : V) (p p' : Pf),
            a ≠ a' ∧
            Disclosure.VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
            Disclosure.VectorCommitmentScheme.verify c₀ i₀ a' p' = true)
    ∧
    -- T8' lifted
    (∀ (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
       (D₁ D₂ : Disclosure.Disclosure V Cm Pf),
        D₁ ∈ s.disclosures →
        D₂ ∈ s.disclosures →
        D₁.commitment = D₂.commitment →
        Disclosure.Disclosure.consistent D₁ →
        Disclosure.Disclosure.consistent D₂ →
        (∀ i v₁ v₂ π₁ π₂,
            (i, v₁, π₁) ∈ D₁.openings →
            (i, v₂, π₂) ∈ D₂.openings →
            v₁ = v₂) ∨
        ∃ (c₀ : Cm) (i₀ : Nat) (a a' : V) (p p' : Pf),
            a ≠ a' ∧
            Disclosure.VectorCommitmentScheme.verify c₀ i₀ a p = true ∧
            Disclosure.VectorCommitmentScheme.verify c₀ i₀ a' p' = true) := by
  exact ⟨t7_inherits_t1obs, t7_inherits_t3, t7_inherits_t4,
         t7_inherits_t5, t7_inherits_t6, t7_inherits_t8,
         t7_inherits_t8'⟩

-- ============================================================
-- ============================================================
--
-- "honest naming over impressive naming":
--
-- The "axiom" framing in the bootstrap is honest-naming for
-- "load-bearing structural property of SystemEvent." The proof is
-- `rfl`-trivial (the three forgetful projections `toReplay`,
-- `toIFC`, `toCausality` each construct their target Event record
-- with `id := e.id`, so projection-id equals event-id by definition
-- of the projection). What this NAMED THEOREM asserts is that no
-- one can later split SystemEvent's projections into divergent-id
-- variants without rewriting the projection definitions themselves.
-- across modules because the three projected Events share `id`.
--
-- Decision per H1 (this session): pick the SIMPLEST shape per
-- "trivial proof, load-bearing naming" pattern. We ship two
-- theorems:
--   (1) `system_event_id_coherence` -- per-event triple equality.
--   (2) `system_trace_projection_id_coherence` -- per-event-in-trace
--       corollary, threading the `e ∈ t` membership through to the
--       three projected traces. Proof: direct application of (1)
--       via projection unfolding.
-- The "shape with iff to the unique projected event" was rejected
-- per H2 attack 5 below.


theorem system_event_id_coherence
    {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) :
    e.toReplay.id = e.id ∧
    e.toIFC.id = e.id ∧
    e.toCausality.id = e.id := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl


theorem system_trace_projection_id_coherence
    {Tag_C Tag_I Tag_P : Type}
    (_t : SystemTrace Tag_C Tag_I Tag_P)
    (e : SystemEvent Tag_C Tag_I Tag_P)
    (_hMem : e ∈ _t) :
    e.toReplay.id = e.toIFC.id ∧ e.toIFC.id = e.toCausality.id := by
  have h := system_event_id_coherence e
  exact ⟨h.1.trans h.2.1.symm, h.2.1.trans h.2.2.symm⟩

-- ============================================================
-- Multi-policy System.lean lift
-- ============================================================
--
-- Mirrors the LowEquiv.lean  multi-policy generalization at
-- the System.lean inheritance lift layer. The existing
-- `t7_inherits_t3_lowEquiv` (line 379, byte-preserved) pins both
-- traces' `wellLabeled` hypotheses to `s₁`'s `(mintingTrusted,
-- rawInputTags, dmap)` triple — a deployment-policy obligation that
-- multi-tenant deployments cannot satisfy when comparing two well-
-- labeled SystemStates from different tenants. This new sibling
-- `t7_inherits_t3_lowEquiv_multipolicy` uses each SystemState's OWN
-- policy fields for its own `wellLabeled` hypothesis.
--
-- The existing `t7_inherits_t3_lowEquiv` is BYTE-PRESERVED (no
-- edits to its body); this is purely additive at the System.lean
-- " for the underlying LowEquiv-layer theorem and its honest
-- residuals (no compatibility constraint at the headline layer; Layer
-- E lift would need a per-position dmap-compatibility constraint).


theorem t7_inherits_t3_lowEquiv_multipolicy
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq Tag_P]
    (s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (visible : IFC.Visible Tag_C Tag_I Tag_P)
    (h₁ : IFC.wellLabeled
            (@Caps.authorizes Tag_C Tag_I Tag_P _)
            s₁.mintingTrusted s₁.rawInputTags
            s₁.dmap s₁.events.toIFC)
    (h₂ : IFC.wellLabeled
            (@Caps.authorizes Tag_C Tag_I Tag_P _)
            s₂.mintingTrusted s₂.rawInputTags
            s₂.dmap s₂.events.toIFC)
    (hLow : IFC.lowProj visible s₁.events.toIFC =
            IFC.lowProj visible s₂.events.toIFC) :
    IFC.lowEquiv visible s₁.events.toIFC s₂.events.toIFC := by
  exact IFC.LowEquiv.t3_low_equivalence_multipolicy
    (@Caps.authorizes Tag_C Tag_I Tag_P _)
    visible
    s₁.mintingTrusted s₂.mintingTrusted
    s₁.rawInputTags s₂.rawInputTags
    s₁.dmap s₂.dmap
    s₁.events.toIFC s₂.events.toIFC h₁ h₂ hLow

end AgentKernel.System

-- ============================================================
-- carry-forward): Stale-`now` orphan wiring
-- ============================================================
--
-- Pre-this-item, `quiet_authorize_foreclosed_with_audit` (Caps.lean
-- L515) was structurally orphan at L0: no kernel-stepping rule routed
-- through `RequestCtx.matchesAuditedNow`, leaving the audit-publication
-- gate as a documented-but-unused L0 artifact and surfacing as Caveat
--
-- This item wires a new `KernelAuthorizationStep` stepping-rule
-- predicate that REQUIRES both (a) an `authorizes_at` proof and
-- (b) a `RequestCtx.matchesAuditedNow auditedNow = true` proof.
-- The wiring theorem `kernel_step_foreclosed_unreachable` then
-- demonstrates that no `KernelAuthorizationStep` exists for a cap
-- that has expired relative to `auditedNow` — making
-- `quiet_authorize_foreclosed_with_audit` LOAD-BEARING in the
-- L0 stepping-rule discipline.
--
-- The stepping rule is additive — no edits to `Caps.authorizes_at`
-- (body byte-preserved), no edits to `RequestCtx.matchesAuditedNow`,
-- no edits to IFC.lean. The L1+ residual (kernel runtime threads

namespace AgentKernel.System


structure KernelAuthorizationStep
    (Tag_C Tag_I Tag_P : Type)
    [DecidableEq Tag_P]
    where
  ctx           : Caps.RequestCtx
  parentInStore : Bool
  who           : Caps.Capability Tag_C Tag_I Tag_P
  what          : IFC.LabelXform Tag_C Tag_I Tag_P
  auditedNow    : Nat
  hAuth         : Caps.authorizes_at ctx parentInStore who what
  hAudit        : ctx.matchesAuditedNow auditedNow = true


theorem kernel_step_foreclosed_unreachable
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (step : KernelAuthorizationStep Tag_C Tag_I Tag_P)
    {t : Nat}
    (hExp : step.who.expires = some t)
    (hAuditPast : step.auditedNow > t) :
    False := by
  exact Caps.quiet_authorize_foreclosed_with_audit
    (ctx := step.ctx)
    (parentInStore := step.parentInStore)
    (who := step.who)
    (what := step.what)
    (t := t)
    (auditedNow := step.auditedNow)
    hExp hAuditPast step.hAudit step.hAuth


theorem kernel_step_implies_static_authorization
    {Tag_C Tag_I Tag_P : Type}
    [DecidableEq Tag_P]
    (step : KernelAuthorizationStep Tag_C Tag_I Tag_P) :
    Caps.authorizes step.who step.what :=
  Caps.authorizes_at_implies_authorizes_static step.hAuth

-- ============================================================
-- theorem family (Items #1 + #2)
-- ============================================================


theorem SystemEvent.toReplay_preserves_SpawnedBy
    {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) :
    e.toReplay.SpawnedBy = e.SpawnedBy := rfl


theorem SystemEvent.toCausality_preserves_SpawnedBy
    {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) :
    e.toCausality.SpawnedBy = e.SpawnedBy := rfl


theorem SystemEvent.toReplay_preserves_retractTarget
    {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) :
    e.toReplay.payloadRetractTarget = e.retractTarget := by
  unfold Replay.Event.payloadRetractTarget SystemEvent.toReplay
  cases e.retractTarget <;> rfl


theorem SystemEvent.toCausality_preserves_retractTarget
    {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) :
    e.toCausality.retractTarget = e.retractTarget := rfl


theorem SystemEvent.toReplay_preserves_tenant
    {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) :
    e.toReplay.tenant = e.tenant := rfl


theorem SystemEvent.toCausality_preserves_tenant
    {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) :
    e.toCausality.tenant = e.tenant := rfl

end AgentKernel.System

-- ============================================================
-- ============================================================
--
-- Predicted post-discharge tiers (Tier 4 NOT expected --
-- System.lean does not touch UInt64.BEq; v0.9.2 floor is for M7
-- conformance only):
--
-- Lemma                       | Predicted             | Source
-- ----------------------------|-----------------------|-----------------------------
-- t7_inherits_t1obs           | [propext]             | inherited from Replay.t1_obs
-- t7_inherits_t3              | [propext]             | inherited from IFC.t3_noninterference
-- t7_inherits_t4              | [propext, Quot.sound] | Log.t4_audit_integrity + rw
-- t7_inherits_t5              | []                    | inherited from Caps.t5
-- t7_inherits_t6              | [propext, Quot.sound] | Causality.causality_acyclic
-- t7_inherits_t8              | []                    | inherited from Disclosure.t8
-- t7_inherits_t8'             | [propext]             | inherited from Disclosure.t8'
-- t7_compositional_refinement | [propext, Quot.sound] | T4/T6 dominate
--
-- Tier 1 expected to gain T7-T5 + T7-T8 (axiom-free).
-- Tier 2 expected to gain T7-T1obs + T7-T3 + T7-T8' ([propext]).
-- Tier 3 expected to gain T7-T4 + T7-T6 + composite ([propext, Quot.sound]).
-- Tier 4 NOT expected (System.lean is UInt64-BEq-free).
--
-- : measure actual axioms via the #print blocks below;

#print axioms AgentKernel.System.t7_inherits_t1obs
#print axioms AgentKernel.System.t7_inherits_t3
#print axioms AgentKernel.System.t7_inherits_t4
#print axioms AgentKernel.System.t7_inherits_t5
#print axioms AgentKernel.System.t7_inherits_t6
#print axioms AgentKernel.System.t7_inherits_t8
#print axioms AgentKernel.System.t7_inherits_t8'
#print axioms AgentKernel.System.t7_compositional_refinement

-- Predicted: Tier 1 (axiom-free) for both -- proof is `rfl` /
-- structural transitivity over `rfl`. Confirm at #print blocks below.
#print axioms AgentKernel.System.system_event_id_coherence
#print axioms AgentKernel.System.system_trace_projection_id_coherence

-- projection-preservation theorem family for the new
-- SpawnedBy / retractTarget side-table fields. All four are
-- `rfl`-proofs over field projections; predicted Tier 1
-- axiom-free.
#print axioms AgentKernel.System.SystemEvent.toReplay_preserves_SpawnedBy
#print axioms AgentKernel.System.SystemEvent.toCausality_preserves_SpawnedBy
#print axioms AgentKernel.System.SystemEvent.toReplay_preserves_retractTarget
#print axioms AgentKernel.System.SystemEvent.toCausality_preserves_retractTarget
-- theorem family for the new SystemEvent.tenant / Causality.Event.tenant
-- mirrors. Both are pure `rfl`-proofs over field projections; predicted
-- Tier 1 axiom-free.
#print axioms AgentKernel.System.SystemEvent.toReplay_preserves_tenant
#print axioms AgentKernel.System.SystemEvent.toCausality_preserves_tenant

-- ============================================================
-- lifts for the cumulative .. named theorem set
-- ============================================================
--
-- **Additive at file tail.** All v1.3-baseline content above is byte-
-- coverage commitment + Agent G's  deferral note ( file-overlap
-- carve isolated System.lean from the  cycle), this block delivers
-- the SystemEvent-context T7 inheritance lifts for:
--
--   *   — `Disclosure.composeVerify_sound`
--   *   — `Caps.spawn_cap_binding_sound`
--   *   — `Caps.revoke_transitive_sound`
--   *   — `MultiCell.traceUnion_disjoint_preserves_*`
--   *   (M2 mirror) — `Bridge.M2.V14R3.T7_M2_retract_local`
--   *   (M3 mirror) — `Bridge.M3.V14R3.T7_M3_cross_cell_local`
--
--
-- Several lifts are STRUCTURAL PACKAGING / `rfl`-trivial because the
-- underlying / theorem already operates on the projected types
-- (`Replay.Event` / `Replay.Trace` / `Capability` / etc.) and the
-- SystemState's projection (`s.events.toReplay`, `s.capStore`) is
-- byte-for-byte transparent to the predicate. This is named as
-- STRUCTURAL PACKAGING in each docstring, NOT as a load-bearing
-- is too weak — name structural packaging accordingly." The
-- LOAD-BEARING content remains in the underlying / theorems
-- (Caps.lean, Disclosure.lean, MultiCell.lean, Bridge/M2.lean,
-- Bridge/M3.lean); the System.lean lifts give downstream paper §4 +
-- conformance + audit consumers a citable named target at the M8
-- composition layer.

namespace AgentKernel.System

/-! ## §1 — T7-inherits-composeVerify-sound (  lift) -/


theorem t7_inherits_hierarchical_receipt_compose_verify
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [Disclosure.VectorCommitmentScheme V Cm Pf]
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (parent : Disclosure.Disclosure V Cm Pf)
    (children : List (Disclosure.Disclosure V Cm Pf)) :
    Disclosure.composeVerifyAll
        (Disclosure.composeReceipt parent children) ↔
      Disclosure.Disclosure.consistent parent ∧
        ∀ c ∈ children, Disclosure.Disclosure.consistent c :=
  Disclosure.composeVerify_sound parent children

/-! ## §2 — T7-inherits-spawn-cap-binding-sound (  lift) -/


theorem t7_inherits_spawn_cap_binding_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (H : Caps.CapabilityHistory Tag_C Tag_I Tag_P)
    (hWFCap : Caps.wellFormedCapabilityHistory s.atten H)
    (t : List Replay.Event)
    (hProj : t = s.events.toReplay)
    (hBacked : H.traceBacked t)
    (hCapBound : H.spawnedBy_capBoundTrace t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (p : Nat)
    (hSpawn : e.SpawnedBy = some p) :
    ∃ eMint ∈ t,
      Replay.Event.id eMint = p ∧
      Replay.Event.kind eMint = Replay.Kind.cap_mint ∧
      ∃ cid, Replay.Event.payloadCapMintedId eMint = some cid := by
  -- The L0 underlying theorem operates on `t : List Replay.Event`. The
  -- M8-context lift introduces an explicit `t` binder + projection
  -- equality `hProj : t = s.events.toReplay` to discharge the
  -- Membership-typeclass mismatch (`Replay.Trace = List Event` is a
  -- `def` not an `abbrev`, so `Membership` does not unfold across the
  -- type alias automatically; the explicit `List Event` binder
  -- bypasses the unfolding). The M8 framing is preserved via `hProj`.
  exact Caps.spawn_cap_binding_sound s.atten H t
    hWFCap hBacked hCapBound e hMem p hSpawn

/-! ## §3 — T7-inherits-revoke-transitive-sound (  lift) -/


theorem t7_inherits_revoke_transitive_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (rootId : Caps.CapId)
    (cap : Caps.Capability Tag_C Tag_I Tag_P)
    (hRevoke : Caps.revokedRoot rootId s₁.capStore s₂.capStore)
    (hDelegPre : Caps.IsDelegatedFrom rootId cap s₁.capStore) :
    ¬ Caps.IsDelegatedFrom rootId cap s₂.capStore :=
  Caps.revoke_transitive_sound s₁.capStore s₂.capStore rootId cap
    hRevoke hDelegPre

/-! ## §4 — T7-inherits-traceUnion-disjoint-preserves-wellFormed
    (  lift) -/


theorem t7_inherits_traceUnion_disjoint_preserves_wellFormed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t₁ t₂ : List Replay.Event)
    (hProj₁ : t₁ = s₁.events.toReplay)
    (hProj₂ : t₂ = s₂.events.toReplay)
    (h : MultiCell.Trace.disjointEventIds t₁ t₂)
    (h₁ : Replay.Trace.wellFormedSpawnedBy t₁)
    (h₂ : Replay.Trace.wellFormedSpawnedBy t₂) :
    Replay.Trace.wellFormedSpawnedBy
      (MultiCell.Trace.union t₁ t₂ h) := by
  -- M8-context lift: explicit `t₁`, `t₂ : List Replay.Event` binders
  -- + projection equalities `hProj₁`, `hProj₂` thread the SystemState
  -- framing while sidestepping the `Replay.Trace`-vs-`List Event`
  -- Membership-typeclass mismatch (cf. comment on
  -- `t7_inherits_spawn_cap_binding_sound`).
  exact MultiCell.traceUnion_disjoint_preserves_wellFormedSpawnedBy
    t₁ t₂ h h₁ h₂


theorem t7_inherits_traceUnion_disjoint_preserves_wellFormedRetraction
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s₁ s₂ : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t₁ t₂ : List Replay.Event)
    (hProj₁ : t₁ = s₁.events.toReplay)
    (hProj₂ : t₂ = s₂.events.toReplay)
    (h : MultiCell.Trace.disjointEventIds t₁ t₂)
    (h₁ : ∀ e ∈ t₁,
            Replay.Event.wellFormedRetraction
              (MultiCell.Trace.union t₁ t₂ h) e)
    (h₂ : ∀ e ∈ t₂,
            Replay.Event.wellFormedRetraction
              (MultiCell.Trace.union t₁ t₂ h) e) :
    Replay.Trace.wellFormedRetraction
      (MultiCell.Trace.union t₁ t₂ h) := by
  -- M8-context lift: explicit `t₁`, `t₂ : List Replay.Event` binders
  -- + projection equalities discharge the Membership-typeclass mismatch
  -- (cf. `t7_inherits_spawn_cap_binding_sound` for the same shape).
  exact MultiCell.traceUnion_disjoint_preserves_wellFormedRetraction
    t₁ t₂ h h₁ h₂

/-! ## §5 — T7-inherits-M2-retract (  / Bridge/M2 lift) -/


theorem t7_inherits_M2_retract
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t t' : Replay.Trace)
    (hWF : Replay.Trace.wellFormedRetraction t)
    (hStep : AgentKernel.Bridge.M2.V14R3.LeanStep_M2_Retract t t') :
    ∃ e : Replay.Event,
      t' = List.append (α := Replay.Event) t [e] ∧
      (e.kind = Replay.Kind.retract →
        e.payloadRetractTarget ≠ none ∧
        ∀ tid, e.payloadRetractTarget = some tid → tid ∈ e.parents) :=
  AgentKernel.Bridge.M2.V14R3.T7_M2_retract_local t t' hWF hStep

/-! ## §6 — T7-inherits-M3-cross-cell (  / Bridge/M3 lift) -/


theorem t7_inherits_M3_cross_cell
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (W W' : Causality.World)
    (hStep : AgentKernel.Bridge.M3.V14R3.LeanStep_M3_CrossCell W W') :
    ∃ p : Nat, ∃ e : Causality.Event,
      e ∈ W' ∧ Causality.HappensBefore W' p e.id :=
  AgentKernel.Bridge.M3.V14R3.T7_M3_cross_cell_local W W' hStep




theorem tenant_binding_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedTenantBinding t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (p_id : Nat)
    (hSpawn : e.SpawnedBy = some p_id)
    (p_event : Replay.Event)
    (hPMem : p_event ∈ t)
    (hPId : p_event.id = p_id) :
    e.tenant = p_event.tenant ∨ e.kernelAuthored = true := by
  -- hWF e hMem : Event.wellFormedTenantBinding t e
  -- The second projection is clause (b): the disjunction itself.
  exact (hWF e hMem).2 p_id hSpawn p_event hPMem hPId

/-! ## §7 — T7-inherits-tenant-binding-sound (  lift) -/


theorem t7_inherits_tenant_binding_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedTenantBinding t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (p_id : Nat)
    (hSpawn : e.SpawnedBy = some p_id)
    (p_event : Replay.Event)
    (hPMem : p_event ∈ t)
    (hPId : p_event.id = p_id) :
    e.tenant = p_event.tenant ∨ e.kernelAuthored = true :=
  tenant_binding_sound t hWF e hMem p_id hSpawn p_event hPMem hPId


theorem replay_mode_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedReplayMode t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hKernelEmit : e.kind.isKernelEmit = true) :
    e.mode = Replay.Mode.live :=
  (hWF e hMem).1 hKernelEmit



/-! ## §7.D079f — T7-inherits-replay-mode-sound (  lift) -/


theorem t7_inherits_replay_mode_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedReplayMode t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hKernelEmit : e.kind.isKernelEmit = true) :
    e.mode = Replay.Mode.live :=
  replay_mode_sound t hWF e hMem hKernelEmit


theorem plan_exec_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedPlanExec t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (eid : Nat)
    (hPlan : e.kind = Replay.Kind.plan)
    (hLink : e.payloadLinkedExecId = some eid) :
    ∃ e' ∈ t, e'.id = eid ∧ e'.kind = Replay.Kind.exec :=
  (hWF e hMem).1 eid hPlan hLink


theorem t7_inherits_plan_exec_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedPlanExec t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (eid : Nat)
    (hPlan : e.kind = Replay.Kind.plan)
    (hLink : e.payloadLinkedExecId = some eid) :
    ∃ e' ∈ t, e'.id = eid ∧ e'.kind = Replay.Kind.exec :=
  plan_exec_sound t hWF e hMem eid hPlan hLink


theorem refusal_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedRefusal t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hRef : e.kind = Replay.Kind.refusal) :
    e.detWitness = none ∧ e.payloadCapMintedId = none ∧
    e.payloadRetractTarget = none ∧ e.payloadLinkedExecId = none :=
  (hWF e hMem).1 hRef

theorem contractViolation_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedRefusal t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hVio : e.kind = Replay.Kind.contractViolation) :
    e.payloadViolationContractId ≠ none :=
  (hWF e hMem).2.1 hVio


theorem t7_inherits_refusal_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedRefusal t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hRef : e.kind = Replay.Kind.refusal) :
    e.detWitness = none ∧ e.payloadCapMintedId = none ∧
    e.payloadRetractTarget = none ∧ e.payloadLinkedExecId = none :=
  refusal_sound t hWF e hMem hRef


theorem t7_inherits_contractViolation_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedRefusal t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hVio : e.kind = Replay.Kind.contractViolation) :
    e.payloadViolationContractId ≠ none :=
  contractViolation_sound t hWF e hMem hVio


theorem session_bind_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedSessionBind t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hSb : e.kind = Replay.Kind.session_bind) :
    e.author = KernelOrTenant.kernel :=
  (hWF e hMem).1 hSb




theorem t7_inherits_session_bind_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedSessionBind t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hSb : e.kind = Replay.Kind.session_bind) :
    e.author = KernelOrTenant.kernel :=
  session_bind_sound t hWF e hMem hSb


theorem contract_register_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedContractRegister t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hCr : e.kind = Replay.Kind.contractRegister) :
    e.payloadRegisteredContractId ≠ none :=
  (hWF e hMem).1 hCr


theorem t7_inherits_contract_register_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedContractRegister t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hCr : e.kind = Replay.Kind.contractRegister) :
    e.payloadRegisteredContractId ≠ none :=
  contract_register_sound t hWF e hMem hCr


theorem human_gate_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedHumanGate t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hHg : e.kind = Replay.Kind.humanGate) :
    e.author = KernelOrTenant.kernel :=
  (hWF e hMem).2 hHg


theorem human_gate_field_presence_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedHumanGate t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hHg : e.kind = Replay.Kind.humanGate) :
    ∃ rec, e.payload = Replay.EventPayload.humanGate rec :=
  (hWF e hMem).1 hHg


theorem failure_mode_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedFailureMode t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (rec : Replay.FailureRecord)
    (hFm : e.payload = Replay.EventPayload.failureMode rec) :
    e.author = KernelOrTenant.kernel :=
  (hWF e hMem).1 ⟨rec, hFm⟩


theorem failure_mode_byzantine_kernel_authored_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedFailureMode t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (rec : Replay.FailureRecord)
    (hFm : e.payload = Replay.EventPayload.failureMode rec)
    (hByz : rec.mode = Replay.FailureMode.byzantine) :
    e.kernelAuthored = true :=
  (hWF e hMem).2 ⟨rec, hFm, hByz⟩




theorem t7_inherits_human_gate_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedHumanGate t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hHg : e.kind = Replay.Kind.humanGate) :
    e.author = KernelOrTenant.kernel :=
  human_gate_sound t hWF e hMem hHg


theorem t7_inherits_human_gate_field_presence_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedHumanGate t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (hHg : e.kind = Replay.Kind.humanGate) :
    ∃ rec, e.payload = Replay.EventPayload.humanGate rec :=
  human_gate_field_presence_sound t hWF e hMem hHg


theorem t7_inherits_failure_mode_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedFailureMode t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (rec : Replay.FailureRecord)
    (hFm : e.payload = Replay.EventPayload.failureMode rec) :
    e.author = KernelOrTenant.kernel :=
  failure_mode_sound t hWF e hMem rec hFm


theorem t7_inherits_failure_mode_byzantine_kernel_authored_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedFailureMode t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (rec : Replay.FailureRecord)
    (hFm : e.payload = Replay.EventPayload.failureMode rec)
    (hByz : rec.mode = Replay.FailureMode.byzantine) :
    e.kernelAuthored = true :=
  failure_mode_byzantine_kernel_authored_sound t hWF e hMem rec hFm hByz


theorem env_binding_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedEnvBinding t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (rec : Replay.EnvDigestRecord)
    (hEb : e.payload = Replay.EventPayload.envBinding rec) :
    e.author = KernelOrTenant.kernel :=
  (hWF e hMem).1 ⟨rec, hEb⟩


theorem env_binding_kernel_authored_sound
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedEnvBinding t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (rec : Replay.EnvDigestRecord)
    (hEb : e.payload = Replay.EventPayload.envBinding rec) :
    e.kernelAuthored = true :=
  (hWF e hMem).2 ⟨rec, hEb⟩


theorem t7_inherits_env_binding_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedEnvBinding t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (rec : Replay.EnvDigestRecord)
    (hEb : e.payload = Replay.EventPayload.envBinding rec) :
    e.author = KernelOrTenant.kernel :=
  env_binding_sound t hWF e hMem rec hEb


theorem t7_inherits_env_binding_kernel_authored_sound
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (_s : SystemState Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (t : List Replay.Event)
    (hWF : Replay.Trace.wellFormedEnvBinding t)
    (e : Replay.Event)
    (hMem : e ∈ t)
    (rec : Replay.EnvDigestRecord)
    (hEb : e.payload = Replay.EventPayload.envBinding rec) :
    e.kernelAuthored = true :=
  env_binding_kernel_authored_sound t hWF e hMem rec hEb

end AgentKernel.System

-- ============================================================
-- ============================================================
--
-- Predicted post-discharge tiers (Tier 4 NOT expected — System.lean
-- does not touch UInt64.BEq):
--
-- Lemma                                                       | Predicted             | Source
-- ------------------------------------------------------------|-----------------------|------------------------
-- t7_inherits_hierarchical_receipt_compose_verify             | []                    | composeVerify_sound (Iff.rfl)
-- t7_inherits_spawn_cap_binding_sound                         | []                    | Caps.spawn_cap_binding_sound
-- t7_inherits_revoke_transitive_sound                         | []                    | Caps.revoke_transitive_sound
-- t7_inherits_traceUnion_disjoint_preserves_wellFormed        | [propext]             | MultiCell.traceUnion_disjoint_preserves_wellFormedSpawnedBy
-- t7_inherits_traceUnion_disjoint_preserves_wellFormedRetraction | [propext]          | MultiCell.traceUnion_disjoint_preserves_wellFormedRetraction
-- t7_inherits_M2_retract                                      | []                    | Bridge.M2.V14R3.T7_M2_retract_local
-- t7_inherits_M3_cross_cell                                   | [propext]             | Bridge.M3.V14R3.T7_M3_cross_cell_local
--
-- Tier 4 NOT expected (no UInt64-BEq path). All within v1.3-baseline
-- tier set.
--
-- block is STRUCTURAL THREADING (direct apply of the underlying /
-- theorem with the SystemState projection passed through). The
-- LOAD-BEARING content lives in the underlying / theorems
-- (Caps.lean, Disclosure.lean, MultiCell.lean, Bridge/M2.lean,
-- Bridge/M3.lean); these lifts give downstream M8-composition
-- consumers a citable named target.

#print axioms AgentKernel.System.t7_inherits_hierarchical_receipt_compose_verify
#print axioms AgentKernel.System.t7_inherits_spawn_cap_binding_sound
#print axioms AgentKernel.System.t7_inherits_revoke_transitive_sound
#print axioms AgentKernel.System.t7_inherits_traceUnion_disjoint_preserves_wellFormed
#print axioms AgentKernel.System.t7_inherits_traceUnion_disjoint_preserves_wellFormedRetraction
#print axioms AgentKernel.System.t7_inherits_M2_retract
#print axioms AgentKernel.System.t7_inherits_M3_cross_cell
#print axioms AgentKernel.System.tenant_binding_sound
#print axioms AgentKernel.System.t7_inherits_tenant_binding_sound
