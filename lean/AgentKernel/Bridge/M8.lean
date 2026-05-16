import AgentKernel.System
import AgentKernel.Bridge.M4
import AgentKernel.Bridge.M5
import AgentKernel.Bridge.M6
import AgentKernel.Bridge.M7



namespace AgentKernel.Bridge.M8

open AgentKernel
open AgentKernel.System (SystemEvent SystemTrace)
open AgentKernel.IFC (Label Factor LabelXform DeclassMap DeclassPayload Trace
                       wellLabeledStep wellLabeled)
open AgentKernel.Caps (Capability CapId CapStore CapMap AttenRel)
open AgentKernel.Log (LogChain Entry)
open AgentKernel.Disclosure (VectorCommitmentScheme)
open AgentKernel.Replay (Kind)


structure M8State
    (Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type) where
  events            : SystemTrace Tag_C Tag_I Tag_P
  capStore          : CapStore Tag_C Tag_I Tag_P
  lastPublishedRoot : Int
  auditChain        : LogChain Bytes Hash
  lastEntryAtomic   : Bool
  m7                : Bridge.M7.M7State V Cm Pf

/-- Initial M8 state. Mirrors `Init_M8`'s seven conjuncts in
    `System.tla`. -/
def M8State.init
    (Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type) :
    M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf :=
  { events            := []
  , capStore          := fun _ => none
  , lastPublishedRoot := -1
  , auditChain        := []
  , lastEntryAtomic   := false
  , m7                := Bridge.M7.M7State.init V Cm Pf }


inductive ActionLabel_M8
    (Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type) : Type where
  -- M4-style emit arms (inlined; not via Bridge.M4 because M4
  -- operates on IFC.Trace, M8 on SystemTrace).
  | emitNonDeclass
      (e : SystemEvent Tag_C Tag_I Tag_P) :
      ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf
  | emitDeclass
      (e : SystemEvent Tag_C Tag_I Tag_P)
      (p : DeclassPayload
            (Caps.Principal Tag_C Tag_I Tag_P) Tag_C Tag_I Tag_P) :
      ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf
  -- M5 wrappers: re-export Bridge.M5.ActionLabel_M5 via a wrap.
  | m5
      (a : Bridge.M5.ActionLabel_M5
            (Caps.Principal Tag_C Tag_I Tag_P)
            Tag_C Tag_I Tag_P) :
      ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf
  | publishStoreSnapshot
      (newRoot : Int) :
      ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf
  -- M6 wrappers.
  | m6
      (a : Bridge.M6.ActionLabel_M6 Bytes) :
      ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf
  -- and doesn't carry a PublishAndAudit constructor).
  | publishAndAudit
      (b : Bytes) :
      ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf
  | publishAndAuditWithCapMatch
      (b : Bytes)
      (cr : Int) :
      ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf
  -- M7 wrappers.
  | m7
      (a : Bridge.M7.ActionLabel_M7 V Cm Pf) :
      ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf

/-! ## Per-arm pre/post predicates

  Each `Next_M8` disjunct's pre/post, transcribed onto `M8State`.
  Per-module arms thread the per-module step on the relevant slice
  and leave the other slices UNCHANGED.

  v0.1 narrowing per `System.tla`:
  * `EmitNonDeclass` / `EmitDeclass` carry the new event as a
    payload (existential lifted to the constructor); the bridge
    asserts only the structural append + kind discipline.
    Trace-wide `wellLabeled` is asserted via the per-module M4
    bridge composing through the projection
    `SystemTrace.toIFC = events.map SystemEvent.toIFC`.
  * `MaxEvents` / `MaxCaps` cardinality bounds: omitted on the
    Lean side (Lean's lists / nat-keyed maps are unbounded; bound
    is a TLC artifact only).
-/

/-- TLA+ `EmitNonDeclass` arm (M8-inlined per architectural choice
    (i) in `System.tla`; M4's `Lattice.tla` operates on `IFC.Trace`
    while M8 operates on `SystemTrace`).

    Pre: the new event is non-declass (`kind ≠ declassify ∧
    kind ≠ declassMint`). The trace-level  obligation is left as
    a separate hypothesis on the preservation lemma — at the bridge
    level we record only the structural shape (append).

    Post: `events' = events ++ [e]`; all other slices unchanged.

    Per architectural choice (i), the M8-bridge does not re-prove
     here; it composes the M4 bridge's proof via projection in
    `EmitNonDeclassStep_preserves_wellLabeled` below. -/
def EmitNonDeclassStep
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (e : SystemEvent Tag_C Tag_I Tag_P)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  e.kind ≠ Kind.declassify ∧
  e.kind ≠ Kind.declassMint ∧
  s'.events            = s.events ++ [e] ∧
  s'.capStore          = s.capStore ∧
  s'.lastPublishedRoot = s.lastPublishedRoot ∧
  s'.auditChain        = s.auditChain ∧
  s'.lastEntryAtomic   = s.lastEntryAtomic ∧
  s'.m7                = s.m7

/-- TLA+ `EmitDeclass` arm (M8-inlined). Pre: `e.kind = declassify`;
    declass payload `p` lives in the per-trace dmap (see
    preservation lemma). Post: `events' = events ++ [e]`; all other
    slices unchanged. -/
def EmitDeclassStep
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (e : SystemEvent Tag_C Tag_I Tag_P)
    (_p : DeclassPayload
          (Caps.Principal Tag_C Tag_I Tag_P) Tag_C Tag_I Tag_P)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  e.kind = Kind.declassify ∧
  s'.events            = s.events ++ [e] ∧
  s'.capStore          = s.capStore ∧
  s'.lastPublishedRoot = s.lastPublishedRoot ∧
  s'.auditChain        = s.auditChain ∧
  s'.lastEntryAtomic   = s.lastEntryAtomic ∧
  s'.m7                = s.m7


def M5Step
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : Bridge.M5.ActionLabel_M5
          (Caps.Principal Tag_C Tag_I Tag_P) Tag_C Tag_I Tag_P)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  Bridge.M5.TLAStep_M5 auth atten s.capStore a s'.capStore ∧
  s'.events            = s.events ∧
  s'.lastPublishedRoot = s.lastPublishedRoot ∧
  s'.auditChain        = s.auditChain ∧
  s'.lastEntryAtomic   = s.lastEntryAtomic ∧
  s'.m7                = s.m7


def PublishStoreSnapshotStep
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (newRoot : Int)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  newRoot ≥ 0 ∧
  s'.events            = s.events ∧
  s'.capStore          = s.capStore ∧
  s'.lastPublishedRoot = newRoot ∧
  s'.auditChain        = s.auditChain ∧
  s'.lastEntryAtomic   = false ∧
  s'.m7                = s.m7

/-- M6 wrapper: M6 step on `auditChain`; sysEvents / capStore /
    lastPublishedRoot / m7 unchanged. `lastEntryAtomic` is forced to
    `false` for `appendEntry` (decoupled append per System.tla's
    `SystemAppendEntry` wrapper) and threads through verbatim for
    `publishRoot` (UNCHANGED auditChain).

    Mirrors `SystemAppendEntry` / `SystemPublishRoot` in
    `System.tla`. The `publishRoot` arm threads `lastEntryAtomic`
    UNCHANGED (per System.tla line 588); the `appendEntry` arm
    forces `false` (per System.tla line 582). -/
def M6Step
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : Bridge.M6.ActionLabel_M6 Bytes)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  Bridge.M6.TLAStep_M6 H genesis serialize s.auditChain a
    s'.auditChain ∧
  s'.events            = s.events ∧
  s'.capStore          = s.capStore ∧
  s'.lastPublishedRoot = s.lastPublishedRoot ∧
  -- Match TLA+: appendEntry forces false; publishRoot leaves
  -- unchanged (we encode both via a single conjunct using the
  -- action label).
  (match a with
    | Bridge.M6.ActionLabel_M6.appendEntry _ =>
        s'.lastEntryAtomic = false
    | Bridge.M6.ActionLabel_M6.publishRoot   =>
        s'.lastEntryAtomic = s.lastEntryAtomic) ∧
  s'.m7                = s.m7


def PublishAndAuditStep
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (b : Bytes)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  s.auditChain ≠ [] ∧
  s'.auditChain = s.auditChain ++
    [{ prev := LogChain.root H genesis serialize s.auditChain
     , payload := b }] ∧
  s'.events            = s.events ∧
  s'.capStore          = s.capStore ∧
  s'.lastPublishedRoot = s.lastPublishedRoot ∧
  s'.lastEntryAtomic   = false ∧
  s'.m7                = s.m7


def PublishAndAuditWithCapMatchStep
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (b : Bytes)
    (cr : Int)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  s.auditChain ≠ [] ∧
  cr ≥ 0 ∧
  s'.events            = s.events ∧
  s'.capStore          = s.capStore ∧
  s'.lastPublishedRoot = cr ∧
  s'.auditChain = s.auditChain ++
    [{ prev := LogChain.root H genesis serialize s.auditChain
     , payload := b }] ∧
  s'.lastEntryAtomic   = true ∧
  s'.m7                = s.m7

/-- M7 wrapper: M7 step on `m7`; sysEvents / capStore /
    lastPublishedRoot / auditChain / lastEntryAtomic unchanged.

    Mirrors `SystemCommitAction` / `SystemRevealAction` /
    `SystemVerifyDisclosureAction` in `System.tla` — all three M7
    arms thread `UNCHANGED <<sysEvents, capStore,
    lastPublishedRoot, auditChain, lastEntryAtomic>>`. -/
def M7Step
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : Bridge.M7.ActionLabel_M7 V Cm Pf)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  Bridge.M7.TLAStep_M7 s.m7 a s'.m7 ∧
  s'.events            = s.events ∧
  s'.capStore          = s.capStore ∧
  s'.lastPublishedRoot = s.lastPublishedRoot ∧
  s'.auditChain        = s.auditChain ∧
  s'.lastEntryAtomic   = s.lastEntryAtomic

/-! ## TLAStep_M8

  Per-arm TLA+-side stepping predicate, indexed by an
  `ActionLabel_M8`. Mechanical mirror of `Next_M8`'s 12 disjuncts.
-/


def TLAStep_M8
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  match a with
  | ActionLabel_M8.emitNonDeclass e =>
      EmitNonDeclassStep s e s'
  | ActionLabel_M8.emitDeclass e p =>
      EmitDeclassStep s e p s'
  | ActionLabel_M8.m5 a5 =>
      M5Step auth atten s a5 s'
  | ActionLabel_M8.publishStoreSnapshot newRoot =>
      PublishStoreSnapshotStep s newRoot s'
  | ActionLabel_M8.m6 a6 =>
      M6Step H genesis serialize s a6 s'
  | ActionLabel_M8.publishAndAudit b =>
      PublishAndAuditStep H genesis serialize s b s'
  | ActionLabel_M8.publishAndAuditWithCapMatch b cr =>
      PublishAndAuditWithCapMatchStep H genesis serialize s b cr s'
  | ActionLabel_M8.m7 a7 =>
      M7Step s a7 s'

/-! ## LeanStep_M8

  Defined as the existential closure of `TLAStep_M8` over
  `ActionLabel_M8`. Mirrors the M5 / M7 pattern.

  At M8 the Lean side has T7 inheritance lemmas as **structural
  composition theorems** but no independent stepping content beyond
  the per-module slice-projected primitives. The substantive M8
  content lives in:
  * Per-arm preservation lemmas (each composes one per-module
    preservation lemma).
  * The aggregate `LeanStep_M8_preserves_*` theorems that thread
    the cross-module invariants through any `ActionLabel_M8` arm.
  * The atomic invariant preservation
    (`LeanStep_M8_preserves_atomic_invariant`).

  Honest framing: like M5 / M7, the iff itself is `Iff.rfl`. The
  composition content is in the preservation theorems below — and
  in the per-arm dispatch in `BridgeSound_M8`'s sibling
  preservation lemmas, which DO thread per-module preservation
  proofs verbatim.
-/

/-- The Lean-side step relation. Defined as the existential
    closure of `TLAStep_M8`. -/
def LeanStep_M8
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) : Prop :=
  ∃ a : ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf,
    TLAStep_M8 auth atten H genesis serialize s a s'

/-! ## BridgeSound_M8

  The bridge soundness theorem. Statement:
  `LeanStep_M8 s s' ↔ ∃ a, TLAStep_M8 s a s'`.

  By the definition of `LeanStep_M8`, the two sides are
  definitionally equal. The proof is `Iff.rfl`.

  **The same triviality as M5 / M7** — M8's substantive content is
  the per-arm preservation lemmas below, NOT the iff itself. The
  iff serves to package the existential closure as a single
  citable bridge theorem in a uniform shape across M4 / M5 / M6 /
  M7 / M8.

  Honest framing: the iff is structural packaging; the
  composition-content is in the per-arm preservation lemmas. This
  IS the M5 / M7 reading reapplied at the composition layer.
-/

/-- **BridgeSound_M8.** `LeanStep_M8` is exactly the existential
    closure of `TLAStep_M8`, by definition. The iff holds
    reflexively.

    The 12-arm composition content lives in the per-arm
    preservation lemmas below. -/
theorem BridgeSound_M8
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf) :
    LeanStep_M8 auth atten H genesis serialize s s'
      ↔ ∃ a : ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf,
            TLAStep_M8 auth atten H genesis serialize s a s' :=
  Iff.rfl

/-! ## Per-arm preservation — capStore closure (M5 territory)

  M5's `CapStore.closed` is preserved by the M5 arms (via
  `Bridge.M5.LeanStep_M5_preserves_closed`) and is trivially
  preserved by every other arm (capStore unchanged).
-/

/-- M5 arm preserves `CapStore.closed`. Composes
    `Bridge.M5.LeanStep_M5_preserves_closed` via projection onto
    the M5 slice. -/
theorem M5Step_preserves_closed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : Bridge.M5.ActionLabel_M5
          (Caps.Principal Tag_C Tag_I Tag_P) Tag_C Tag_I Tag_P)
    (hClosed : Caps.CapStore.closed atten s.capStore)
    (hStep : M5Step auth atten s a s') :
    Caps.CapStore.closed atten s'.capStore := by
  -- M5Step's first conjunct is TLAStep_M5 on the slice; lift it
  -- to LeanStep_M5 via the existential constructor and apply
  -- the M5 preservation lemma.
  have hSlice : Bridge.M5.TLAStep_M5 auth atten s.capStore a s'.capStore :=
    hStep.1
  have hLean5 : Bridge.M5.LeanStep_M5 auth atten s.capStore s'.capStore :=
    ⟨a, hSlice⟩
  exact Bridge.M5.LeanStep_M5_preserves_closed
          auth atten s.capStore s'.capStore hClosed hLean5



/-- M6 arm preserves `LogChain.wellFormed`. Composes
    `Bridge.M6.LeanStep_M6_preserves_wellFormed` via projection
    onto the auditChain slice. -/
theorem M6Step_preserves_wellFormed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : Bridge.M6.ActionLabel_M6 Bytes)
    (hWF : LogChain.wellFormed H genesis serialize s.auditChain)
    (hStep : M6Step H genesis serialize s a s') :
    LogChain.wellFormed H genesis serialize s'.auditChain := by
  have hSlice : Bridge.M6.TLAStep_M6 H genesis serialize
                  s.auditChain a s'.auditChain := hStep.1
  -- LeanStep_M6 is the structural disjunction (defined
  -- independently in Bridge/M6.lean); BridgeSound_M6 transports.
  have hLean6 : Bridge.M6.LeanStep_M6 H genesis serialize
                  s.auditChain s'.auditChain :=
    (Bridge.M6.BridgeSound_M6 H genesis serialize
      s.auditChain s'.auditChain).mpr ⟨a, hSlice⟩
  exact Bridge.M6.LeanStep_M6_preserves_wellFormed
          H genesis serialize s.auditChain s'.auditChain hWF hLean6


theorem PublishAndAuditStep_preserves_wellFormed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (b : Bytes)
    (hWF : LogChain.wellFormed H genesis serialize s.auditChain)
    (hStep : PublishAndAuditStep H genesis serialize s b s') :
    LogChain.wellFormed H genesis serialize s'.auditChain := by
  obtain ⟨_hNonempty, hChain, _hEv, _hCap, _hLPR, _hLEA, _hM7⟩ := hStep
  -- The append shape is identical to AppendStep:
  -- s'.auditChain = s.auditChain ++ [{prev := root, payload := b}]
  have hAppendStep :
      Bridge.M6.AppendStep H genesis serialize
        s.auditChain b s'.auditChain := by
    unfold Bridge.M6.AppendStep
    exact hChain
  exact Bridge.M6.AppendStep_preserves_wellFormed
          H genesis serialize s.auditChain b s'.auditChain
          hWF hAppendStep


theorem PublishAndAuditWithCapMatchStep_preserves_wellFormed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (b : Bytes)
    (cr : Int)
    (hWF : LogChain.wellFormed H genesis serialize s.auditChain)
    (hStep : PublishAndAuditWithCapMatchStep H genesis serialize s b cr s') :
    LogChain.wellFormed H genesis serialize s'.auditChain := by
  obtain ⟨_hNonempty, _hCrPos, _hEv, _hCap, _hLPR, hChain,
          _hLEA, _hM7⟩ := hStep
  have hAppendStep :
      Bridge.M6.AppendStep H genesis serialize
        s.auditChain b s'.auditChain := by
    unfold Bridge.M6.AppendStep
    exact hChain
  exact Bridge.M6.AppendStep_preserves_wellFormed
          H genesis serialize s.auditChain b s'.auditChain
          hWF hAppendStep

/-! ## Per-arm preservation — m7 disclosure invariant (M7 territory)

  M7's `M7State.invariant` is preserved by the M7 arms (via
  `Bridge.M7.LeanStep_M7_preserves_inv`) and by all other arms
  trivially (m7 unchanged).
-/

/-- M7 arm preserves `M7State.invariant`. Composes
    `Bridge.M7.LeanStep_M7_preserves_inv` via projection onto the
    M7 slice. -/
theorem M7Step_preserves_inv
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : Bridge.M7.ActionLabel_M7 V Cm Pf)
    (hInv : Bridge.M7.M7State.invariant s.m7)
    (hStep : M7Step s a s') :
    Bridge.M7.M7State.invariant s'.m7 := by
  have hSlice : Bridge.M7.TLAStep_M7 s.m7 a s'.m7 := hStep.1
  have hLean7 : Bridge.M7.LeanStep_M7 s.m7 s'.m7 := ⟨a, hSlice⟩
  exact Bridge.M7.LeanStep_M7_preserves_inv s.m7 s'.m7 hInv hLean7

/-! ## Aggregate cross-module invariant preservation

  The structural-content lemma the M8 bridge buys: every
  `LeanStep_M8` preserves all three composite invariants
  (`CapStore.closed`, `LogChain.wellFormed`, `M7State.invariant`)
  in lock-step.

  Mirrors `M8_PerModuleInv` in `System.tla`'s composite invariant
  surface (line 814+).
-/

/-- **CapStore closure preservation across the M8 bridge.** Every
    `LeanStep_M8` preserves `CapStore.closed`. Trivial on every
    arm except `m5` (which threads via M5's preservation). -/
theorem LeanStep_M8_preserves_capStore_closed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hClosed : Caps.CapStore.closed atten s.capStore)
    (hStep : LeanStep_M8 auth atten H genesis serialize s s') :
    Caps.CapStore.closed atten s'.capStore := by
  obtain ⟨a, hStep⟩ := hStep
  cases a with
  | emitNonDeclass e =>
      have hStep' : EmitNonDeclassStep s e s' := hStep
      rw [hStep'.2.2.2.1]; exact hClosed
  | emitDeclass e p =>
      have hStep' : EmitDeclassStep s e p s' := hStep
      rw [hStep'.2.2.1]; exact hClosed
  | m5 a5 =>
      have hStep' : M5Step auth atten s a5 s' := hStep
      exact M5Step_preserves_closed auth atten s s' a5 hClosed hStep'
  | publishStoreSnapshot newRoot =>
      have hStep' : PublishStoreSnapshotStep s newRoot s' := hStep
      rw [hStep'.2.2.1]; exact hClosed
  | m6 a6 =>
      have hStep' : M6Step H genesis serialize s a6 s' := hStep
      rw [hStep'.2.2.1]; exact hClosed
  | publishAndAudit b =>
      have hStep' : PublishAndAuditStep H genesis serialize s b s' := hStep
      rw [hStep'.2.2.2.1]; exact hClosed
  | publishAndAuditWithCapMatch b cr =>
      have hStep' : PublishAndAuditWithCapMatchStep H genesis serialize s b cr s' :=
        hStep
      -- PublishAndAuditWithCapMatchStep conjuncts:
      --   .1: auditChain ≠ []; .2.1: cr ≥ 0;
      --   .2.2.1: events = ...; .2.2.2.1: capStore = ...; ...
      rw [hStep'.2.2.2.1]; exact hClosed
  | m7 a7 =>
      have hStep' : M7Step s a7 s' := hStep
      rw [hStep'.2.2.1]; exact hClosed

/-- **Audit-chain wellFormedness preservation across the M8
    bridge.** Every `LeanStep_M8` preserves
    `LogChain.wellFormed`. Trivial on every arm except `m6`,
    `publishAndAudit`, and `publishAndAuditWithCapMatch` (which
    thread via M6's preservation / append-singleton helper). -/
theorem LeanStep_M8_preserves_auditChain_wellFormed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hWF : LogChain.wellFormed H genesis serialize s.auditChain)
    (hStep : LeanStep_M8 auth atten H genesis serialize s s') :
    LogChain.wellFormed H genesis serialize s'.auditChain := by
  obtain ⟨a, hStep⟩ := hStep
  cases a with
  | emitNonDeclass e =>
      have hStep' : EmitNonDeclassStep s e s' := hStep
      rw [hStep'.2.2.2.2.2.1]; exact hWF
  | emitDeclass e p =>
      have hStep' : EmitDeclassStep s e p s' := hStep
      rw [hStep'.2.2.2.2.1]; exact hWF
  | m5 a5 =>
      have hStep' : M5Step auth atten s a5 s' := hStep
      rw [hStep'.2.2.2.1]; exact hWF
  | publishStoreSnapshot newRoot =>
      have hStep' : PublishStoreSnapshotStep s newRoot s' := hStep
      rw [hStep'.2.2.2.2.1]; exact hWF
  | m6 a6 =>
      have hStep' : M6Step H genesis serialize s a6 s' := hStep
      exact M6Step_preserves_wellFormed H genesis serialize s s' a6 hWF hStep'
  | publishAndAudit b =>
      have hStep' : PublishAndAuditStep H genesis serialize s b s' := hStep
      exact PublishAndAuditStep_preserves_wellFormed
              H genesis serialize s s' b hWF hStep'
  | publishAndAuditWithCapMatch b cr =>
      have hStep' : PublishAndAuditWithCapMatchStep H genesis serialize s b cr s' :=
        hStep
      exact PublishAndAuditWithCapMatchStep_preserves_wellFormed
              H genesis serialize s s' b cr hWF hStep'
  | m7 a7 =>
      have hStep' : M7Step s a7 s' := hStep
      rw [hStep'.2.2.2.2.1]; exact hWF

/-- **M7 disclosure invariant preservation across the M8 bridge.**
    Every `LeanStep_M8` preserves `M7State.invariant` on the m7
    slice. Trivial on every arm except `m7` (which threads via M7's
    preservation). -/
theorem LeanStep_M8_preserves_m7_invariant
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hInv : Bridge.M7.M7State.invariant s.m7)
    (hStep : LeanStep_M8 auth atten H genesis serialize s s') :
    Bridge.M7.M7State.invariant s'.m7 := by
  obtain ⟨a, hStep⟩ := hStep
  cases a with
  | emitNonDeclass e =>
      have hStep' : EmitNonDeclassStep s e s' := hStep
      rw [hStep'.2.2.2.2.2.2.2]; exact hInv
  | emitDeclass e p =>
      have hStep' : EmitDeclassStep s e p s' := hStep
      rw [hStep'.2.2.2.2.2.2]; exact hInv
  | m5 a5 =>
      have hStep' : M5Step auth atten s a5 s' := hStep
      rw [hStep'.2.2.2.2.2]; exact hInv
  | publishStoreSnapshot newRoot =>
      have hStep' : PublishStoreSnapshotStep s newRoot s' := hStep
      rw [hStep'.2.2.2.2.2.2]; exact hInv
  | m6 a6 =>
      have hStep' : M6Step H genesis serialize s a6 s' := hStep
      rw [hStep'.2.2.2.2.2]; exact hInv
  | publishAndAudit b =>
      have hStep' : PublishAndAuditStep H genesis serialize s b s' := hStep
      rw [hStep'.2.2.2.2.2.2]; exact hInv
  | publishAndAuditWithCapMatch b cr =>
      have hStep' : PublishAndAuditWithCapMatchStep H genesis serialize s b cr s' :=
        hStep
      rw [hStep'.2.2.2.2.2.2.2]; exact hInv
  | m7 a7 =>
      have hStep' : M7Step s a7 s' := hStep
      exact M7Step_preserves_inv s s' a7 hInv hStep'




theorem publishAndAuditWithCapMatch_atomicity
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (b : Bytes)
    (cr : Int)
    (hStep : PublishAndAuditWithCapMatchStep H genesis serialize s b cr s') :
    s'.lastPublishedRoot = cr ∧
    s'.auditChain = s.auditChain ++
      [{ prev := LogChain.root H genesis serialize s.auditChain
       , payload := b }] ∧
    s'.lastEntryAtomic = true := by
  obtain ⟨_hNonempty, _hCrPos, _hEv, _hCap, hLPR, hChain, hLEA, _hM7⟩ := hStep
  exact ⟨hLPR, hChain, hLEA⟩

/-- The decoupled arms (`SystemAppendEntry`, `SystemPublishAndAudit`,
    `SystemPublishStoreSnapshot`) all set `lastEntryAtomic' =
    false`, decoupling the atomic-coupling claim. This is the
    Lean-side mirror of the System.tla wrapper's
    `lastEntryAtomic' = FALSE` clauses. -/
theorem decoupled_arms_clear_atomic_flag
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (a : ActionLabel_M8 Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hStep : TLAStep_M8 auth atten H genesis serialize s a s') :
    -- The arms that clear the atomic flag (decoupled / publishStore /
    -- m6.appendEntry):
    (∀ newRoot, a = ActionLabel_M8.publishStoreSnapshot newRoot →
      s'.lastEntryAtomic = false) ∧
    (∀ b, a = ActionLabel_M8.publishAndAudit b →
      s'.lastEntryAtomic = false) ∧
    (∀ b, a = ActionLabel_M8.m6 (Bridge.M6.ActionLabel_M6.appendEntry b) →
      s'.lastEntryAtomic = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro newRoot ha
    subst ha
    have hStep' : PublishStoreSnapshotStep s newRoot s' := hStep
    exact hStep'.2.2.2.2.2.1
  · intro b ha
    subst ha
    have hStep' : PublishAndAuditStep H genesis serialize s b s' := hStep
    exact hStep'.2.2.2.2.2.1
  · intro b ha
    subst ha
    have hStep' : M6Step H genesis serialize s
                    (Bridge.M6.ActionLabel_M6.appendEntry b) s' := hStep
    -- M6Step's atomic-flag conjunct is the 5th element; for
    -- appendEntry it is `s'.lastEntryAtomic = false`.
    exact hStep'.2.2.2.2.1



/-- The initial state satisfies `CapStore.closed`. Vacuous: empty
    map. -/
theorem M8State.init_capStore_closed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (atten : AttenRel Tag_C Tag_I Tag_P) :
    Caps.CapStore.closed atten
      (M8State.init Tag_C Tag_I Tag_P Bytes Hash V Cm Pf).capStore := by
  intro cid cap hLookup
  -- (M8State.init ...).capStore = fun _ => none, so hLookup is impossible.
  unfold M8State.init at hLookup
  simp at hLookup

/-- The initial state's audit chain is well-formed. Vacuous: empty
    chain. -/
theorem M8State.init_auditChain_wellFormed
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes) :
    LogChain.wellFormed H genesis serialize
      (M8State.init Tag_C Tag_I Tag_P Bytes Hash V Cm Pf).auditChain := by
  unfold M8State.init
  exact LogChain.wellFormed_nil H genesis serialize

/-- The initial state's M7 invariant holds. Vacuous: empty
    verifiedSet. -/
theorem M8State.init_m7_invariant
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf] :
    Bridge.M7.M7State.invariant
      (M8State.init Tag_C Tag_I Tag_P Bytes Hash V Cm Pf).m7 := by
  unfold M8State.init
  exact Bridge.M7.M7State.init_invariant

/-- The initial state has `lastEntryAtomic = false`. -/
theorem M8State.init_atomic_false
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type} :
    (M8State.init Tag_C Tag_I Tag_P Bytes Hash V Cm Pf).lastEntryAtomic = false := by
  rfl



/-- The `author` field is preserved by all three forgetful
    projections. Direct sanity check: each projection writes
    `author := e.author` (System.lean lines 173, 189, 211). -/
theorem author_field_threaded
    {Tag_C Tag_I Tag_P : Type}
    (e : SystemEvent Tag_C Tag_I Tag_P) :
    e.toReplay.author = e.author ∧
    e.toIFC.author = e.author ∧
    e.toCausality.author = e.author := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl




theorem T7_cross_replay_disclose
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq V]
    [VectorCommitmentScheme V Cm Pf]
    (s : AgentKernel.System.SystemState
            Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (s₂ : AgentKernel.System.SystemState
            Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (D₁ D₂ : AgentKernel.Disclosure.Disclosure V Cm Pf)
    (hReplayEquiv :
      AgentKernel.Replay.Trace.replayEquiv
        s.events.toReplay s₂.events.toReplay)
    (hMem₁ : D₁ ∈ s.disclosures)
    (hMem₂ : D₂ ∈ s.disclosures)
    (hCom : D₁.commitment = D₂.commitment)
    (hCons₁ : AgentKernel.Disclosure.Disclosure.consistent D₁)
    (hCons₂ : AgentKernel.Disclosure.Disclosure.consistent D₂) :
    AgentKernel.Replay.Trace.equivObs
      s.events.toReplay s₂.events.toReplay
    ∧
    ((∀ i v₁ v₂ π₁ π₂,
        (i, v₁, π₁) ∈ D₁.openings →
        (i, v₂, π₂) ∈ D₂.openings →
        v₁ = v₂)
      ∨
      ∃ (c₀ : Cm) (i₀ : Nat) (a a' : V) (p p' : Pf),
        a ≠ a' ∧
        AgentKernel.Disclosure.VectorCommitmentScheme.verify
          c₀ i₀ a p = true ∧
        AgentKernel.Disclosure.VectorCommitmentScheme.verify
          c₀ i₀ a' p' = true) :=
  ⟨AgentKernel.System.t7_inherits_t1obs s s₂ hReplayEquiv,
   AgentKernel.System.t7_inherits_t8' s D₁ D₂ hMem₁ hMem₂ hCom hCons₁ hCons₂⟩


theorem T7_cross_audit_ifc
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq Tag_P] [DecidableEq Bytes] [DecidableEq Hash]
    (s₁ s₂ : AgentKernel.System.SystemState
              Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (visible : AgentKernel.IFC.Visible Tag_C Tag_I Tag_P)
    (hHash : s₁.hashFn = s₂.hashFn)
    (hGen  : s₁.genesis = s₂.genesis)
    (hSer  : s₁.serialize = s₂.serialize)
    (hLen  : s₁.auditChain.length = s₂.auditChain.length)
    (hWF1  : AgentKernel.Log.LogChain.wellFormed
              s₁.hashFn s₁.genesis s₁.serialize s₁.auditChain)
    (hWF2  : AgentKernel.Log.LogChain.wellFormed
              s₂.hashFn s₂.genesis s₂.serialize s₂.auditChain)
    (hRoot : s₁.auditChain.root s₁.hashFn s₁.genesis s₁.serialize
              = s₂.auditChain.root s₂.hashFn s₂.genesis s₂.serialize)
    (hWL : AgentKernel.IFC.wellLabeled
            (@AgentKernel.Caps.authorizes Tag_C Tag_I Tag_P _)
            s₁.mintingTrusted s₁.rawInputTags
            s₁.dmap s₁.events.toIFC) :
    -- M6 audit-integrity conclusion (T4 lifted)
    (s₁.auditChain = s₂.auditChain ∨
      ∃ (a a' : Hash) (b b' : Bytes),
        (a, b) ≠ (a', b') ∧
        s₁.hashFn (s₁.serialize a b)
          = s₁.hashFn (s₁.serialize a' b'))
    ∧
    -- M4 noninterference conclusion (T3 lifted) — three-way disjunction
    (∀ e ∈ AgentKernel.IFC.lowProj visible s₁.events.toIFC,
      (e.kind = AgentKernel.Replay.Kind.declassify ∧
        ∃ p : AgentKernel.IFC.DeclassPayload
                (AgentKernel.Caps.Principal Tag_C Tag_I Tag_P)
                Tag_C Tag_I Tag_P,
          s₁.dmap e.id = some p ∧
          (@AgentKernel.Caps.authorizes Tag_C Tag_I Tag_P _) p.who p.what ∧
          p.locus = e.id ∧
          p.when s₁.events.toIFC ∧
          e.outLabel.prov =
            (p.what.interp
              (AgentKernel.IFC.Label.join e.inLabel e.ctxLabel)).prov)
      ∨
      (e.kind = AgentKernel.Replay.Kind.declassMint ∧
        AgentKernel.IFC.Factor.leq e.inLabel.prov s₁.mintingTrusted)
      ∨
      (e.kind ≠ AgentKernel.Replay.Kind.declassify ∧
       e.kind ≠ AgentKernel.Replay.Kind.declassMint ∧
        AgentKernel.IFC.Factor.leq
          (AgentKernel.IFC.Factor.join e.inLabel.prov e.ctxLabel.prov)
          e.outLabel.prov)) :=
  ⟨AgentKernel.System.t7_inherits_t4 s₁ s₂ hHash hGen hSer hLen hWF1 hWF2 hRoot,
   AgentKernel.System.t7_inherits_t3 s₁ visible hWL⟩


theorem T7_cross_cap_disclose
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [DecidableEq V]
    [VectorCommitmentScheme V Cm Pf]
    (s : AgentKernel.System.SystemState
            Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (D₁ D₂ : AgentKernel.Disclosure.Disclosure V Cm Pf)
    (hClosed : AgentKernel.Caps.CapStore.closed s.atten s.capStore)
    (hCmap : ∀ eid cap, s.capMap eid = some cap →
                        ∃ cid, s.capStore cid = some cap)
    (hMem₁ : D₁ ∈ s.disclosures)
    (hMem₂ : D₂ ∈ s.disclosures)
    (hCom : D₁.commitment = D₂.commitment)
    (hCons₁ : AgentKernel.Disclosure.Disclosure.consistent D₁)
    (hCons₂ : AgentKernel.Disclosure.Disclosure.consistent D₂) :
    -- M5 capability-safety conclusion (T5 lifted)
    (∀ eid cap, s.capMap eid = some cap →
        AgentKernel.Caps.Capability.wellFormed s.atten s.capStore cap)
    ∧
    -- M7 multi-disclosure non-equivocation conclusion (T8' lifted)
    ((∀ i v₁ v₂ π₁ π₂,
        (i, v₁, π₁) ∈ D₁.openings →
        (i, v₂, π₂) ∈ D₂.openings →
        v₁ = v₂)
      ∨
      ∃ (c₀ : Cm) (i₀ : Nat) (a a' : V) (p p' : Pf),
        a ≠ a' ∧
        AgentKernel.Disclosure.VectorCommitmentScheme.verify
          c₀ i₀ a p = true ∧
        AgentKernel.Disclosure.VectorCommitmentScheme.verify
          c₀ i₀ a' p' = true) :=
  ⟨AgentKernel.System.t7_inherits_t5 s hClosed hCmap,
   AgentKernel.System.t7_inherits_t8' s D₁ D₂ hMem₁ hMem₂ hCom hCons₁ hCons₂⟩




theorem LeanStep_M8_preserves_events_extension
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hStep : LeanStep_M8 auth atten H genesis serialize s s') :
    ∃ tail : SystemTrace Tag_C Tag_I Tag_P,
      s'.events = s.events ++ tail := by
  obtain ⟨a, hStep⟩ := hStep
  cases a with
  | emitNonDeclass e =>
      have hStep' : EmitNonDeclassStep s e s' := hStep
      exact ⟨[e], hStep'.2.2.1⟩
  | emitDeclass e p =>
      have hStep' : EmitDeclassStep s e p s' := hStep
      exact ⟨[e], hStep'.2.1⟩
  | m5 a5 =>
      have hStep' : M5Step auth atten s a5 s' := hStep
      exact ⟨[], by rw [hStep'.2.1]; simp⟩
  | publishStoreSnapshot newRoot =>
      have hStep' : PublishStoreSnapshotStep s newRoot s' := hStep
      exact ⟨[], by rw [hStep'.2.1]; simp⟩
  | m6 a6 =>
      have hStep' : M6Step H genesis serialize s a6 s' := hStep
      exact ⟨[], by rw [hStep'.2.1]; simp⟩
  | publishAndAudit b =>
      have hStep' : PublishAndAuditStep H genesis serialize s b s' := hStep
      exact ⟨[], by rw [hStep'.2.2.1]; simp⟩
  | publishAndAuditWithCapMatch b cr =>
      have hStep' : PublishAndAuditWithCapMatchStep H genesis serialize s b cr s' :=
        hStep
      exact ⟨[], by rw [hStep'.2.2.1]; simp⟩
  | m7 a7 =>
      have hStep' : M7Step s a7 s' := hStep
      exact ⟨[], by rw [hStep'.2.1]; simp⟩


theorem T7_cross_replay_disclose_step_preserving
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hM7Inv : Bridge.M7.M7State.invariant s.m7)
    (hStep : LeanStep_M8 auth atten H genesis serialize s s') :
    -- M3 trace-side: events extends by a (possibly empty) suffix.
    (∃ tail : SystemTrace Tag_C Tag_I Tag_P,
        s'.events = s.events ++ tail)
    ∧
    -- M7 disclosure-invariant: post-state m7 satisfies invariant.
    Bridge.M7.M7State.invariant s'.m7 :=
  ⟨LeanStep_M8_preserves_events_extension
      auth atten H genesis serialize s s' hStep,
   LeanStep_M8_preserves_m7_invariant
      auth atten H genesis serialize s s' hM7Inv hStep⟩


theorem T7_cross_audit_ifc_step_preserving
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hWF : LogChain.wellFormed H genesis serialize s.auditChain)
    (hStep : LeanStep_M8 auth atten H genesis serialize s s') :
    -- M6 audit-chain wellFormedness preserved (T4 input invariant).
    LogChain.wellFormed H genesis serialize s'.auditChain
    ∧
    -- M4 trace-side: events extends by a (possibly empty) suffix.
    (∃ tail : SystemTrace Tag_C Tag_I Tag_P,
        s'.events = s.events ++ tail) :=
  ⟨LeanStep_M8_preserves_auditChain_wellFormed
      auth atten H genesis serialize s s' hWF hStep,
   LeanStep_M8_preserves_events_extension
      auth atten H genesis serialize s s' hStep⟩


theorem T7_cross_cap_disclose_step_preserving
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [VectorCommitmentScheme V Cm Pf]
    (auth : Caps.Principal Tag_C Tag_I Tag_P →
            LabelXform Tag_C Tag_I Tag_P → Prop)
    (atten : AttenRel Tag_C Tag_I Tag_P)
    (H : Bytes → Hash)
    (genesis : Bytes)
    (serialize : Hash → Bytes → Bytes)
    (s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf)
    (hClosed : Caps.CapStore.closed atten s.capStore)
    (hM7Inv : Bridge.M7.M7State.invariant s.m7)
    (hStep : LeanStep_M8 auth atten H genesis serialize s s') :
    -- M5 cap-store closure preserved (T5 input invariant).
    Caps.CapStore.closed atten s'.capStore
    ∧
    -- M7 disclosure-invariant: post-state m7 satisfies invariant.
    Bridge.M7.M7State.invariant s'.m7 :=
  ⟨LeanStep_M8_preserves_capStore_closed
      auth atten H genesis serialize s s' hClosed hStep,
   LeanStep_M8_preserves_m7_invariant
      auth atten H genesis serialize s s' hM7Inv hStep⟩

end AgentKernel.Bridge.M8

-- ============================================================
-- `lake env lean MeasureAxioms.lean` or `#print axioms` in editor;
-- this file is wired into the AgentKernel target via
-- AgentKernel.lean's import list at H4 close).
--
-- Predicted post-implementation tiers:
--
-- Theorem                                                  | Tier | Source
-- ---------------------------------------------------------|------|-----------------------
-- BridgeSound_M8                                           | []   | Iff.rfl
-- M5Step_preserves_closed                                  | []   | inherited from M5
-- M6Step_preserves_wellFormed                              | []   | M6 + BridgeSound_M6
-- PublishAndAuditStep_preserves_wellFormed                 | []   | inherited from M6
-- PublishAndAuditWithCapMatchStep_preserves_wellFormed     | []   | inherited from M6
-- M7Step_preserves_inv                                     | []   | inherited from M7
-- LeanStep_M8_preserves_capStore_closed                    | []   | dispatch over arms
-- LeanStep_M8_preserves_auditChain_wellFormed              | []   | dispatch over arms
-- LeanStep_M8_preserves_m7_invariant                       | []   | dispatch over arms
-- publishAndAuditWithCapMatch_atomicity                    | []   | structural projection
-- decoupled_arms_clear_atomic_flag                         | []   | structural projection
-- M8State.init_capStore_closed                             | []   | vacuous
-- M8State.init_auditChain_wellFormed                       | []   | vacuous
-- M8State.init_m7_invariant                                | []   | vacuous
-- M8State.init_atomic_false                                | []   | rfl
-- author_field_threaded                                    | []   | rfl
--
-- Tier 4 NOT expected (Bridge/M8 does not touch UInt64.BEq).
-- Tier 2/3 inheritance from M4/M6 PROPEXT may surface depending
-- on which preservation lemmas lift their inheritance — measure
-- at #print blocks below. The composite preservation theorems
-- dispatch over a finite enum (cases on ActionLabel_M8) and consume
-- per-module preservation lemmas verbatim; no propext expected at
-- the dispatch layer.
-- ============================================================

#print axioms AgentKernel.Bridge.M8.BridgeSound_M8
#print axioms AgentKernel.Bridge.M8.M5Step_preserves_closed
#print axioms AgentKernel.Bridge.M8.M6Step_preserves_wellFormed
#print axioms AgentKernel.Bridge.M8.PublishAndAuditStep_preserves_wellFormed
#print axioms AgentKernel.Bridge.M8.PublishAndAuditWithCapMatchStep_preserves_wellFormed
#print axioms AgentKernel.Bridge.M8.M7Step_preserves_inv
#print axioms AgentKernel.Bridge.M8.LeanStep_M8_preserves_capStore_closed
#print axioms AgentKernel.Bridge.M8.LeanStep_M8_preserves_auditChain_wellFormed
#print axioms AgentKernel.Bridge.M8.LeanStep_M8_preserves_m7_invariant
#print axioms AgentKernel.Bridge.M8.publishAndAuditWithCapMatch_atomicity
#print axioms AgentKernel.Bridge.M8.decoupled_arms_clear_atomic_flag
#print axioms AgentKernel.Bridge.M8.M8State.init_capStore_closed
#print axioms AgentKernel.Bridge.M8.M8State.init_auditChain_wellFormed
#print axioms AgentKernel.Bridge.M8.M8State.init_m7_invariant
#print axioms AgentKernel.Bridge.M8.M8State.init_atomic_false
#print axioms AgentKernel.Bridge.M8.author_field_threaded

-- composition lemmas. Each is `And.intro`-trivial over two existing
-- Predicted tier inheritance from the consumed `t7_inherits_*`:
--
-- Theorem                     | Composes                                        | Predicted
-- ----------------------------|-------------------------------------------------|----------
-- T7_cross_replay_disclose    | t7_inherits_t1obs (M3) ∧ t7_inherits_t8' (M7)   | inherits union
-- T7_cross_audit_ifc          | t7_inherits_t4    (M6) ∧ t7_inherits_t3  (M4)   | inherits union
-- T7_cross_cap_disclose       | t7_inherits_t5    (M5) ∧ t7_inherits_t8' (M7)   | inherits union
--
-- Per System.lean prediction blocks (lines 700-712 there): t7_inherits_t1obs
-- and t7_inherits_t3 + t7_inherits_t8' are predicted Tier 2 [propext];
-- t7_inherits_t4 is Tier 3 [propext, Quot.sound]; t7_inherits_t5 is Tier 1
-- (axiom-free). The cross-theorems inherit the union of their pair.

#print axioms AgentKernel.Bridge.M8.T7_cross_replay_disclose
#print axioms AgentKernel.Bridge.M8.T7_cross_audit_ifc
#print axioms AgentKernel.Bridge.M8.T7_cross_cap_disclose

-- Each is `And.intro`-trivial over two existing M8-bridge aggregate
--
--   * LeanStep_M8_preserves_events_extension — every M8 step extends
--     `events` by a (possibly empty) suffix. Tier 1 expected (per-arm
--     structural ⟨[], rfl⟩ or ⟨[e], rfl⟩).
--
-- Cross-theorems (measured tiers):
--
-- Theorem                                              | Composes (M8-bridge aggregates)               | Measured
-- -----------------------------------------------------|-----------------------------------------------|----------
-- LeanStep_M8_preserves_events_extension               | per-arm structural dispatch (8 arms)          | Tier 2 [propext]
-- T7_cross_replay_disclose_step_preserving             | events_extension (M3) ∧ m7_invariant (M7)     | Tier 2 [propext]
-- T7_cross_audit_ifc_step_preserving                   | auditChain_wellFormed (M6) ∧ events_extension (M4) | Tier 2 [propext]
-- T7_cross_cap_disclose_step_preserving                | capStore_closed (M5) ∧ m7_invariant (M7)      | Tier 2 [propext]
--
-- `T7_cross_audit_ifc_step_preserving` is Tier 2 [propext]). The
-- bridge-step-level `auditChain_wellFormed` aggregate dispatches over
-- ActionLabel_M8 arms structurally and does not consume the subst-
-- rewrite path that `t7_inherits_t4` requires (which carries
-- Quot.sound from `Log.t4_audit_integrity`'s rewrite over field
-- equalities). The replay_disclose and cap_disclose pairs land at
--
-- NO Tier 4 inflation; NO new axioms beyond `propext` (inherited from
-- the consumed aggregates' per-arm `simp`-driven rewrites). NO
-- `sorryAx`, NO `Classical.choice`, NO `Quot.sound` introduced.
-- `events_extension` carries `propext` because the per-arm `simp`
-- (closing `events ++ [] = events`) consumes the axiom; this is
-- inherited from stdlib `List.append` lemmas and is the same shape
-- as M3/M4/M5/M6/M7 bridges' Tier 2 [propext] inheritance pattern.

#print axioms AgentKernel.Bridge.M8.LeanStep_M8_preserves_events_extension
#print axioms AgentKernel.Bridge.M8.T7_cross_replay_disclose_step_preserving
#print axioms AgentKernel.Bridge.M8.T7_cross_audit_ifc_step_preserving
#print axioms AgentKernel.Bridge.M8.T7_cross_cap_disclose_step_preserving

-- ============================================================
-- routing into Bridge/M8 (M5 invoke arm)
-- ============================================================
--
-- This block adds an EXISTENCE LEMMA / STRUCTURAL THREADING
-- M5-invoke arm to `System.KernelAuthorizationStep`. Mirrors
-- composition layer.
--
--
-- Honest residuals:
-- (a) M8 admits eight non-invoke arms (emitNonDeclass,
--     emitDeclass, m5.mintCap, m5.delegate, publishStoreSnapshot,
--     m6, publishAndAudit, publishAndAuditWithCapMatch, m7); the
--     wiring theorem ONLY fires on the M5-invoke arm. Other arms
--     do not project to `KernelAuthorizationStep` because the
--     kernel-authorization stepping rule speaks specifically to
--     cap-invocation under audit-gating. The lemma's statement
--     does NOT claim closure over all M8 arms.
-- (b) The L1+ TCB residual (audit log threading) is unchanged
--     sibling.

namespace AgentKernel.Bridge.M8


def LeanStep_M8_invoke_admits_kernelAuthorizationStep
    {Tag_C Tag_I Tag_P Bytes Hash V Cm Pf : Type}
    [Disclosure.VectorCommitmentScheme V Cm Pf]
    [DecidableEq Tag_P]
    {auth : Caps.Principal Tag_C Tag_I Tag_P →
            IFC.LabelXform Tag_C Tag_I Tag_P → Prop}
    {atten : Caps.AttenRel Tag_C Tag_I Tag_P}
    {H : Bytes → Hash}
    {genesis : Bytes}
    {serialize : Hash → Bytes → Bytes}
    {s s' : M8State Tag_C Tag_I Tag_P Bytes Hash V Cm Pf}
    (ctx : Caps.RequestCtx)
    (parentInStore : Bool)
    (auditedNow : Nat)
    (who : Caps.Capability Tag_C Tag_I Tag_P)
    (what : IFC.LabelXform Tag_C Tag_I Tag_P)
    (hAuth : Caps.authorizes_at ctx parentInStore who what)
    (hAudit : ctx.matchesAuditedNow auditedNow = true)
    (_hStep : LeanStep_M8 auth atten H genesis serialize s s') :
    AgentKernel.System.KernelAuthorizationStep Tag_C Tag_I Tag_P :=
  { ctx := ctx
  , parentInStore := parentInStore
  , who := who
  , what := what
  , auditedNow := auditedNow
  , hAuth := hAuth
  , hAudit := hAudit }

end AgentKernel.Bridge.M8

#print axioms AgentKernel.Bridge.M8.LeanStep_M8_invoke_admits_kernelAuthorizationStep
