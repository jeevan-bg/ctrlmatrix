--------------------------------- MODULE System ---------------------------------


EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Kind, DetKinds, NonDetKinds, ObservableKinds, DeclassifyKind,
    \* M3 witness algebra
    DetWitness, NoWitness,
    Payload,
    Sigma_C, Sigma_I, Sigma_P,
    Transformers, TransformerFn,
    AuthRel,
    CapId, NoCap,
    AttenuatesRel,
    \* the M5 INSTANCE WITH-clause to compose Caps.tla v0.2's
    \* lastPublishedRoot variable + StoreRoot constant)
    StoreRoot,
    Bytes, Hash, SystemGenesis,
    H_op, SerializeFn,
    \* P6 -- threaded into the M6 INSTANCE WITH-clause)
    CapRoots, DetWitnessHashes, NoWitnessRef,
    Values, MaxVecLen,
    \* M8 bounds
    MaxEvents, MaxCaps,
    \* TenantId is the L0 deployment-parameter identity space; NoTenantId
    \* is the Option-shape sentinel (`Lean Option.none` mirror).
    TenantId, NoTenantId

ASSUME
    /\ Kind = DetKinds \cup NonDetKinds
    /\ DetKinds \cap NonDetKinds = {}
    /\ ObservableKinds \subseteq Kind
    /\ DeclassifyKind \in DetKinds
    /\ NoWitness \notin DetWitness
    /\ NoCap \notin CapId
    /\ IsFiniteSet(Sigma_C)
    /\ IsFiniteSet(Sigma_I)
    /\ IsFiniteSet(Sigma_P)
    /\ IsFiniteSet(Transformers)
    /\ IsFiniteSet(CapId)
    /\ TransformerFn \in [Transformers -> [SUBSET Sigma_P -> SUBSET Sigma_P]]
    /\ AttenuatesRel \subseteq (Transformers \X Transformers)
    /\ SystemGenesis \in Bytes
    /\ H_op \in [Bytes -> Hash]
    /\ SerializeFn \in [Hash \X Bytes -> Bytes]
    /\ MaxEvents \in Nat
    /\ MaxCaps   \in Nat
    /\ MaxVecLen \in Nat
    \* Caps.tla's StoreRoot ASSUME and Log.tla's CapRoots/DetWitnessHashes
    \* ASSUMEs. The L0 boundary on StoreRoot collision-resistance is per
    \* scope memo Sec. 8 (CR-of-MTH carry-forward shape).
    /\ CapRoots \subseteq (Nat \cup {-1})
    /\ IsFiniteSet(CapRoots)
    /\ IsFiniteSet(DetWitnessHashes)
    /\ NoWitnessRef \notin DetWitnessHashes
    /\ IsFiniteSet(TenantId)
    /\ NoTenantId \notin TenantId

(*****************************************************************************
  Schemas (declared before VARIABLES so INSTANCE WITH-clauses can
  reference Capability)
 *****************************************************************************)

EventId == Nat

Label == [c : SUBSET Sigma_C, i : SUBSET Sigma_I, p : SUBSET Sigma_P]

Bottom == [c |-> {}, i |-> {}, p |-> {}]

\* Capability schema (mirrors M5 Caps.tla; redeclared so SystemEvent and
\* AuthRel have a usable record type without forcing M5 INSTANCE
\* substitution at type-decl time).
\*
\* sub-letter. The two new fields (`expires`, `caveats`) are runtime-
\* fields). Defaults: `expires |-> -1` (sentinel: no expiry) and
\* `caveats |-> << >>` (empty caveat sequence). Because System.tla's
\* `M5 == INSTANCE Caps WITH Principal <- Capability` pins the LOCAL
\* Capability to Caps.tla's `Principal` constant, the LOCAL shape MUST
\* match Caps.tla's `Capability` shape (5-field). The LOCAL
\* `capStore \subseteq Capability` typing in SystemTypeOK requires
\* shape-matching to the wrapped M5 `store \subseteq Capability` typing.
\*
\* TLC-tractability:
\*   The spec-level shape of `expires` is `Nat \cup {-1}`, but TLC cannot
\*   enumerate `Nat`. The `Capability`  below uses the TLC-bounded
\*   `ExpiryDomain == {-1, 0}` (smallest non-trivial enumerable set) for
\*   the `expires` field. The full `Nat \cup {-1}` typing is the abstract
\*   spec; `ExpiryDomain` is the operational refinement TLC checks.
\*
\*   Similarly the spec-level shape of `caveats` is `Seq(Bytes)`, which is
\*   unbounded. TLC cannot enumerate `Seq(Bytes)`. The `Capability`
\*    below uses the TLC-bounded `CaveatBound == {<< >>}` --
\*   the singleton set containing only the empty caveat sequence -- as
\*   the operational refinement. This is the v0.1 narrowing of the
\*   Caps.tla v0.3 schema: at v0.1 all caveat fields default to `<< >>`,
\*   so a singleton domain is operationally faithful and TLC-tractable.
\*   L1+ implementations will widen CaveatBound to bounded-length
\*   sequences over a richer Bytes set; the type-shape (Seq(Bytes)) is
\*   preserved.
\*
\*   These narrowings are mirrored on the Caps.tla v0.3 sub-letter side.
\*   If the Caps.tla agent picks a different narrowing, the M5 INSTANCE
\*   substitution will still parse (Caps.tla's `Principal` is constrained
\*   only by `IsFiniteSet(Principal)`), but a TLC-side narrowing
\*   mismatch could surface as enumeration cost regression. Document
\*   as Caveat for cross-agent coordination.
ExpiryDomain == {-1, 0}
CaveatBound  == {<< >>}

Capability == [
    id      : CapId,
    granted : Transformers,
    parent  : CapId \cup {NoCap},
    expires : ExpiryDomain,
    caveats : CaveatBound
]

ASSUME AuthRel \subseteq (Capability \X Transformers)

\* `where` field is Nat-typed (unbounded). Enumeration in actions binds
\* it to newId; quantification over DeclassPayload as a set is avoided
\* throughout. (Lattice.tla precedent.)
DeclassPayload == [
    what           : Transformers,
    who            : Capability,
    where          : EventId,
    when_evaluated : BOOLEAN
]

\* CHOOSE over `Capability`, which TLC must enumerate. Caps.tla v0.3's
\* extended Capability schema (5-field with `caveats : Seq(Bytes)`) is
\* not finitely enumerable (Seq is unbounded). We replace the CHOOSE
\* with a concrete null-Capability literal to keep TLC tractable. This
\* is the only structural change; semantics are unchanged because
\* NullDeclassPayload is only used as a placeholder in non-declass
\* events (where pl.who is unused by SystemR3_Holds).
NullCapability == [
    id      |-> CHOOSE x \in CapId : TRUE,
    granted |-> CHOOSE g \in Transformers : TRUE,
    parent  |-> NoCap,
    expires |-> -1,
    caveats |-> << >>
]

NullDeclassPayload == [
    what           |-> CHOOSE t \in Transformers : TRUE,
    who            |-> NullCapability,
    where          |-> 0,
    when_evaluated |-> FALSE
]

\* SystemEvent fields directly in invariants.
\*
\* discriminator field mirroring Lean's `Event.author : KernelOrTenant
\* discipline at the construction layer: EmitNonDeclass / EmitDeclass
\* pin `author |-> "tenant"` so v0.1-cfg state-space behaviour is
\* unchanged. The kernel-author branch is the explicit asymmetric-
\* closure case; L1+ operational specs widen the existential. The
\* drift on event-author axis).
\*
\* Cross-artifact discipline: TLA+ string set {"kernel", "tenant"}
\* mirrors Lean's KernelOrTenant inductive (constructors `kernel` |
\* mirror is honest at TLA+'s expressive power. The cap-id forgery
\*
\* L0 boundary: tenant-injection of `author := "kernel"` at the
\* operational layer; the L1+ kernel-runtime obligation is unchanged.
\*
\* {NoTenantId}` discriminator field mirroring Lean's
\* `SystemEvent.tenant : Option Replay.TenantId := none` field landed at
\* construction layer: every `Next`-action SystemEvent record literal
\* (EmitNonDeclass / EmitDeclass below) pins `tenant |-> NoTenantId` so
\* v0.1-cfg state-space behaviour is unchanged. The TLA+ schema mirror
\*
\* ToReplay / ToCausality thread `tenant |-> e.tenant`; ToIFC does
\* NOT thread (mirroring Lean side `SystemEvent.toIFC` per IFC
\* discipline tag-typed structural tenant-freedom).
KernelOrTenant == {"kernel", "tenant"}

\* TLA+ side. True iff the author discriminator picks the kernel
\* branch. Provided for downstream invariants (e.g. M2-bridge
\* causal-completeness) that need to range over kernel-authored events.
KernelAuthored(e) == e.author = "kernel"

SystemEvent == [
    id          : EventId,
    parents     : SUBSET EventId,
    kind        : Kind,
    detWitness  : DetWitness \cup {NoWitness},
    inLabel     : Label,
    outLabel    : Label,
    ctxLabel    : Label,
    capRef      : CapId \cup {NoCap},
    declassPL   : DeclassPayload,
    author      : KernelOrTenant,
    tenant      : TenantId \cup {NoTenantId}
]



ToReplay(e) ==
    [id         |-> e.id,
     kind       |-> e.kind,
     detWitness |-> e.detWitness,
     parents    |-> e.parents,
     author     |-> e.author,
     tenant     |-> e.tenant]

ToIFC(e) ==
    [id       |-> e.id,
     kind     |-> e.kind,
     inLabel  |-> e.inLabel,
     outLabel |-> e.outLabel,
     ctxLabel |-> e.ctxLabel,
     author   |-> e.author]

ToCausality(e) ==
    [id      |-> e.id,
     parents |-> e.parents,
     author  |-> e.author,
     tenant  |-> e.tenant]

(*****************************************************************************
  Recursive label-join (M4-style, inlined at M8 since Lattice.tla is not
  INSTANCE'd per architectural choice (i))
 *****************************************************************************)

RECURSIVE LabelJoinSet(_)
LabelJoinSet(LS) ==
    IF LS = {} THEN Bottom
    ELSE LET x    == CHOOSE y \in LS : TRUE
             rest == LabelJoinSet(LS \ {x})
         IN  [c |-> x.c \cup rest.c,
              i |-> x.i \cap rest.i,
              p |-> x.p \cup rest.p]

(*****************************************************************************
  State variables (declared BEFORE INSTANCE blocks so INSTANCE WITH
  substitutions can resolve)
 *****************************************************************************)

VARIABLES
    sysEvents,            \* Seq(SystemEvent)
    capStore,             \* SUBSET Capability (M5's store under pin)
    lastPublishedRoot,
                          \* lastPublishedRoot, threaded into the M5
                          \* INSTANCE WITH-clause. Sentinel -1 = no
                          \* snapshot ever published.
    auditChain,           \* Seq(M6!Entry) (M6's chain)
    lastEntryAtomic,
                          \* flag: TRUE iff the last chain entry was
                          \* authored by PublishAndAuditWithCapMatch
                          \* PublishAndAuditWithCapMatch; set FALSE by
                          \* SystemAppendEntry / SystemPublishAndAudit
                          \* (decoupled chain-extending actions). Other
                          \* actions thread it UNCHANGED. Used by the
                          \* CapRootMatchesAtPublishAndAudit invariant
                          \* to express the "authored by atomic" guard
                          \* without a full history trace.
    committed,            \* SUBSET [vec, c] (M7)
    revealed,             \* SUBSET [c, i, v, p] (M7)
    verifiedSet           \* SUBSET [c, i, v, p] (M7)

(*****************************************************************************
  M5/M6/M7 INSTANCE blocks (refinement-mapping plumbing)
 *****************************************************************************)

\* threaded as-is. NoParent <- NoCap per Lean's Option CapId encoding.
\* and `StoreRoot` CONSTANT substitution to compose Caps.tla v0.2's
\* cap-store snapshot publication surface.
M5 == INSTANCE Caps WITH
    store              <- capStore,
    lastPublishedRoot  <- lastPublishedRoot,
    Principal          <- Capability,
    Transformers       <- Transformers,
    AuthRel            <- AuthRel,
    AttenuatesRel      <- AttenuatesRel,
    NoParent           <- NoCap,
    MaxCaps            <- MaxCaps,
    CapId              <- CapId,
    StoreRoot          <- StoreRoot

\* as  constants. MaxLen <- MaxEvents.
\* `NoWitnessRef` CONSTANT substitutions to compose Log.tla v0.4's
\* extended Entry record and 3-arg AppendEntry / PublishAndAudit
\* signatures.
M6 == INSTANCE Log WITH
    chain            <- auditChain,
    Bytes            <- Bytes,
    Hash             <- Hash,
    Genesis          <- SystemGenesis,
    H                <- H_op,
    Serialize        <- SerializeFn,
    MaxLen           <- MaxEvents,
    CapRoots         <- CapRoots,
    DetWitnessHashes <- DetWitnessHashes,
    NoWitnessRef     <- NoWitnessRef

\* M7: per-set state pinned. Values + MaxVecLen threaded as-is.
M7 == INSTANCE Disclosure WITH
    committed   <- committed,
    revealed    <- revealed,
    verifiedSet <- verifiedSet,
    Values      <- Values,
    MaxVecLen   <- MaxVecLen

vars == <<sysEvents, capStore, lastPublishedRoot, auditChain,
          lastEntryAtomic, committed, revealed, verifiedSet>>

(*****************************************************************************
  Init
 *****************************************************************************)

Init_M8 ==
    /\ sysEvents         = << >>
    /\ capStore          = {}
    /\ lastPublishedRoot = -1
    /\ auditChain        = << >>
    /\ lastEntryAtomic   = FALSE
    /\ committed         = {}
    /\ revealed          = {}
    /\ verifiedSet       = {}

(*****************************************************************************
  M3/M4/M2 well-formedness inlined at M8 (per architectural choice (i))

  Mirror Determinism.tla's WellWitnessed, Lattice.tla's R2_Holds /
  R3_Holds, and Causality.lean's parents_older invariant; reference
  SystemEvent fields directly. The Lean side projects SystemEvent to
  per-module Event records and applies the same predicates structurally;
  the TLA+ side checks them inline as guards on EmitSystemEvent and as
  state invariants.
 *****************************************************************************)

\* M3-bridge: WellWitnessed. NonDet kinds require a witness; Det kinds
\* accept NoWitness or any witness. Bridge to Lean Event.wellWitnessed
\* (Replay.lean).
SystemWellWitnessed(e) ==
    \/ e.kind \in DetKinds
    \/ e.detWitness \in DetWitness

\* M4-bridge:  (provenance monotonicity, non-declass). Three-factor
\* integrity). Bridge to Lean provenance_monotonicity_R2 (IFC.lean).
SystemR2_Holds(e) ==
    e.kind # DeclassifyKind =>
        /\ e.inLabel.c \cup e.ctxLabel.c \subseteq e.outLabel.c
        /\ e.outLabel.i \subseteq e.inLabel.i \cap e.ctxLabel.i
        /\ e.inLabel.p \cup e.ctxLabel.p \subseteq e.outLabel.p

\* M4-bridge:  (declassification well-formedness). Bridge to Lean
\* declassification_well_formed_R3 (IFC.lean).
SystemR3_Holds(e) ==
    e.kind = DeclassifyKind =>
        LET pl     == e.declassPL
            joined == e.inLabel.p \cup e.ctxLabel.p
        IN
        /\ <<pl.who, pl.what>> \in AuthRel
        /\ pl.where = e.id
        /\ pl.when_evaluated = TRUE
        /\ e.outLabel.p = TransformerFn[pl.what][joined]
        /\ e.inLabel.c \cup e.ctxLabel.c \subseteq e.outLabel.c
        /\ e.outLabel.i \subseteq e.inLabel.i \cap e.ctxLabel.i

\* M2-bridge: parent-id-monotonicity. Bridge to Lean
\* Causality.Event.parents_older (T6 precondition).
SystemParentsOlder(e) ==
    \A p \in e.parents : p < e.id

(*****************************************************************************
  M5-bridge: cap-binding consistency (M8-introduced cross-module coherence)
 *****************************************************************************)

CapInStore(cid) ==
    \E c \in capStore : c.id = cid



\* ParentJoin: fold join over the outLabels of the events in `parents`.
ParentJoin(parents) ==
    LET parentLabels == { sysEvents[pid].outLabel : pid \in parents }
    IN  LabelJoinSet(parentLabels)

EmitNonDeclass ==
    /\ Len(sysEvents) < MaxEvents
    /\ \E parents \in SUBSET (1..Len(sysEvents)) :
       \E k       \in Kind \ {DeclassifyKind} :
       \E dw      \in DetWitness \cup {NoWitness} :
       \E outL    \in Label :
       \E cr      \in CapId \cup {NoCap} :
            LET newId == Len(sysEvents) + 1
                inL   == ParentJoin(parents)
                e == [id         |-> newId,
                      parents    |-> parents,
                      kind       |-> k,
                      detWitness |-> dw,
                      inLabel    |-> inL,
                      outLabel   |-> outL,
                      ctxLabel   |-> Bottom,
                      capRef     |-> cr,
                      declassPL  |-> NullDeclassPayload,
                      author     |-> "tenant",
                      tenant     |-> NoTenantId]
            IN
            /\ SystemParentsOlder(e)
            /\ SystemWellWitnessed(e)
            /\ SystemR2_Holds(e)
            /\ (cr \in CapId => CapInStore(cr))
            /\ sysEvents' = Append(sysEvents, e)
            /\ UNCHANGED <<capStore, lastPublishedRoot, auditChain,
                           lastEntryAtomic, committed, revealed,
                           verifiedSet>>

\* Declass branch. pl.who bound to capStore (cross-module coherence:
\* declassification requires the kernel to hold the declassifier's cap).
\* outL.p determined by ; outL.c, outL.i enumerated.
EmitDeclass ==
    /\ Len(sysEvents) < MaxEvents
    /\ \E parents \in SUBSET (1..Len(sysEvents)) :
       \E dw      \in DetWitness \cup {NoWitness} :
       \E pl_who  \in capStore :
       \E pl_what \in Transformers :
       \E pl_when \in BOOLEAN :
       \E outC    \in SUBSET Sigma_C :
       \E outI    \in SUBSET Sigma_I :
       \E cr      \in CapId \cup {NoCap} :
            LET newId  == Len(sysEvents) + 1
                inL    == ParentJoin(parents)
                joined == inL.p
                outP   == TransformerFn[pl_what][joined]
                outL   == [c |-> outC, i |-> outI, p |-> outP]
                pl     == [what           |-> pl_what,
                           who            |-> pl_who,
                           where          |-> newId,
                           when_evaluated |-> pl_when]
                e == [id         |-> newId,
                      parents    |-> parents,
                      kind       |-> DeclassifyKind,
                      detWitness |-> dw,
                      inLabel    |-> inL,
                      outLabel   |-> outL,
                      ctxLabel   |-> Bottom,
                      capRef     |-> cr,
                      declassPL  |-> pl,
                      author     |-> "tenant",
                      tenant     |-> NoTenantId]
            IN
            /\ SystemParentsOlder(e)
            /\ SystemWellWitnessed(e)
            /\ SystemR3_Holds(e)
            /\ (cr \in CapId => CapInStore(cr))
            /\ sysEvents' = Append(sysEvents, e)
            /\ UNCHANGED <<capStore, lastPublishedRoot, auditChain,
                           lastEntryAtomic, committed, revealed,
                           verifiedSet>>

EmitSystemEvent ==
    \/ EmitNonDeclass
    \/ EmitDeclass

\* Wrap M5 actions: assert UNCHANGED on M8's other variables.
\* `lastPublishedRoot` UNCHANGED internally (Caps.tla v0.2); the wrappers
\* therefore do NOT add `lastPublishedRoot` to the local UNCHANGED clause.
\* `lastEntryAtomic` is UNCHANGED (M5 actions don't extend auditChain).
SystemMintCap ==
    /\ M5!MintCap
    /\ UNCHANGED <<sysEvents, auditChain, lastEntryAtomic,
                   committed, revealed, verifiedSet>>

SystemDelegate ==
    /\ M5!Delegate
    /\ UNCHANGED <<sysEvents, auditChain, lastEntryAtomic,
                   committed, revealed, verifiedSet>>

SystemInvoke ==
    /\ M5!Invoke
    /\ UNCHANGED <<sysEvents, auditChain, lastEntryAtomic,
                   committed, revealed, verifiedSet>>

\* `lastPublishedRoot` and UNCHANGES `store` (= capStore at M8 INSTANCE).
\* The wrapper threads M8's other variables UNCHANGED.
\* `lastEntryAtomic' = FALSE`: this action mutates `lastPublishedRoot`
\* without extending the chain, which decouples the chain tail from
\* the new lastPublishedRoot value. Setting the flag FALSE invalidates
\* any prior atomic-coupling claim on the current chain tail (the
\* invariant `CapRootMatchesAtPublishAndAudit` then holds vacuously
\* until the next atomic action re-establishes the coupling).
SystemPublishStoreSnapshot ==
    /\ M5!PublishStoreSnapshot
    /\ lastEntryAtomic' = FALSE
    /\ UNCHANGED <<sysEvents, auditChain, committed, revealed, verifiedSet>>

\* Wrap M6 actions. Independent reading per Q3 default: audit chain is
\* not bound to the event stream at v0.1; the bound reading defers to
\* v1.0.
\* existentials over Bytes, CapRoots, DetWitnessHashes \cup {NoWitnessRef}.
\* The wrapper does NOT thread `cr = StoreRoot[capStore]` -- that is
\* SystemAppendEntry permits any cr \in CapRoots (the v0.2 decoupled
\* reading; the strong reading is the atomic action).
\* `lastEntryAtomic' = FALSE` (decoupled append, not atomic-coupled).
SystemAppendEntry ==
    /\ \E b \in Bytes :
       \E cr \in CapRoots :
       \E wref \in DetWitnessHashes \cup {NoWitnessRef} :
            M6!AppendEntry(b, cr, wref)
    /\ lastEntryAtomic' = FALSE
    /\ UNCHANGED <<sysEvents, capStore, lastPublishedRoot,
                   committed, revealed, verifiedSet>>

SystemPublishRoot ==
    /\ M6!PublishRoot
    /\ UNCHANGED <<sysEvents, capStore, lastPublishedRoot,
                   lastEntryAtomic, committed, revealed, verifiedSet>>

\* M6!PublishAndAudit(b, cr, wref). This is the v0.2 decoupled reading
\* of `MatchesCapStore(cr)` is the SEPARATE atomic action
\* `PublishAndAuditWithCapMatch` below. SystemPublishAndAudit exists
\* for trace-coverage of the M6 action surface; the structural match
\* is NOT enforced here.
\* `lastEntryAtomic' = FALSE` (decoupled append, not atomic-coupled).
SystemPublishAndAudit ==
    /\ \E b \in Bytes :
       \E cr \in CapRoots :
       \E wref \in DetWitnessHashes \cup {NoWitnessRef} :
            M6!PublishAndAudit(b, cr, wref)
    /\ lastEntryAtomic' = FALSE
    /\ UNCHANGED <<sysEvents, capStore, lastPublishedRoot,
                   committed, revealed, verifiedSet>>

\* Wrap M7 actions. Disclosures stand alone at v0.1 (independent reading).
SystemCommitAction ==
    /\ M7!CommitAction
    /\ UNCHANGED <<sysEvents, capStore, lastPublishedRoot, auditChain,
                   lastEntryAtomic>>

SystemRevealAction ==
    /\ M7!RevealAction
    /\ UNCHANGED <<sysEvents, capStore, lastPublishedRoot, auditChain,
                   lastEntryAtomic>>

SystemVerifyDisclosureAction ==
    /\ M7!VerifyDisclosureAction
    /\ UNCHANGED <<sysEvents, capStore, lastPublishedRoot, auditChain,
                   lastEntryAtomic>>



\*
\* guard mirroring M6!PublishAndAudit's chain-nonempty precondition.
\* That mirroring was a policy choice (snapshot commits against
\* existing chain), not a structural necessity: M6!Root is total on
\* the guard was harmless because SystemAppendEntry seeded the chain
\* Next_M8 leaves the atomic action as the SOLE chain-extending
\* action -- so the seed must also flow through this action. The
\*
\* `Len(auditChain) < MaxEvents` is retained -- the TLC bound on
\* chain length is independent of the seed-vs-extend distinction.
PublishAndAuditWithCapMatch(b, cr) ==
    /\ Len(auditChain) < MaxEvents
    /\ cr = StoreRoot[capStore]
    /\ lastPublishedRoot' = cr
    /\ auditChain' = Append(auditChain,
            [prev          |-> M6!Root(auditChain),
             payload       |-> b,
             capRoot       |-> cr,
             detWitnessRef |-> NoWitnessRef])
    /\ lastEntryAtomic' = TRUE
    /\ UNCHANGED <<sysEvents, capStore, committed, revealed, verifiedSet>>

SystemPublishAndAuditWithCapMatch ==
    \E b \in Bytes :
    \E cr \in CapRoots :
        PublishAndAuditWithCapMatch(b, cr)

\*
\* Removed disjuncts: `SystemAppendEntry` and `SystemPublishAndAudit`.
\* These were the v0.2 "decoupled" chain-extending wrappers (Session
\* of `StoreRoot[capStore]`. Their coexistence with the atomic
\* `SystemPublishAndAuditWithCapMatch` left a per-trace attack
\* trace could fire `SystemAppendEntry` with arbitrary `cr` and still
\* satisfy `Next_M8`, never invoking the atomic action.
\*
\* audit-emission path. Every chain entry's `capRoot` is structurally
\* bound to `StoreRoot[capStore]` at firing time (the structural
\* match conjunct evaluates against the CURRENT capStore at firing,
\* foreclosing replay with stale `cr`). The companion edit drops
\* the `auditChain # << >>` guard from `PublishAndAuditWithCapMatch`
\* so the atomic action also seeds (M6!Root is total on the empty
\* chain via H[Genesis]).
\*
\* The wrapper definitions of `SystemAppendEntry` and
\* `SystemPublishAndAudit` are RETAINED above as documentation of
\* the v0.2 decoupled reading; they are no longer composed into
\* `Next_M8` and so are unreachable in TLC traces. Future M8
\* refinement variants (e.g., a hybrid for partial-failure modeling)
\* may re-introduce them under a separate Next_* variant.
\*
\* Cross-module references: NONE. Liveness.tla / LivenessProof.tla
\* implementation time).
\*
\* TLC effect: state-space narrows (some traces with arbitrary `cr`
Next_M8 ==
    \/ EmitSystemEvent
    \/ SystemMintCap
    \/ SystemDelegate
    \/ SystemInvoke
    \/ SystemPublishStoreSnapshot
    \/ SystemPublishRoot
    \/ SystemPublishAndAuditWithCapMatch
    \/ SystemCommitAction
    \/ SystemRevealAction
    \/ SystemVerifyDisclosureAction

Spec_M8 == Init_M8 /\ [][Next_M8]_vars

(*****************************************************************************
  Invariants
 *****************************************************************************)

SystemTypeOK ==
    /\ sysEvents \in Seq(SystemEvent)
    /\ Len(sysEvents) <= MaxEvents
    /\ capStore \subseteq Capability
    /\ lastPublishedRoot \in (Nat \cup {-1})
    /\ auditChain \in Seq(M6!Entry)
    /\ committed   \subseteq [vec: M7!Vectors, c: M7!Commitments]
    /\ revealed    \subseteq [c: M7!Commitments, i: M7!Indices,
                              v: Values,        p: M7!Proofs]
    /\ verifiedSet \subseteq [c: M7!Commitments, i: M7!Indices,
                              v: Values,        p: M7!Proofs]

CapBindingConsistent ==
    \A i \in 1..Len(sysEvents) :
        LET e == sysEvents[i] IN
        e.capRef \in CapId => CapInStore(e.capRef)

DeclassConsistent ==
    \A i \in 1..Len(sysEvents) :
        SystemR3_Holds(sysEvents[i])

NonDeclassConsistent ==
    \A i \in 1..Len(sysEvents) :
        SystemR2_Holds(sysEvents[i])

AllWellWitnessed ==
    \A i \in 1..Len(sysEvents) :
        SystemWellWitnessed(sysEvents[i])

AllParentsOlder ==
    \A i \in 1..Len(sysEvents) :
        SystemParentsOlder(sysEvents[i])

\* Mirrors Lean's `system_event_id_coherence` theorem. Holds by-
\* construction (each projection writes `id |-> e.id`); TLC's job
\* here is operational regression detection on the projection
\* operators -- a future refactor that breaks id-coherence in
\* ToReplay / ToIFC / ToCausality will surface as TLC counter-
\* example rather than silent T7-inheritance uncoupling. Cost is
\* sub-linear (three field reads per event); state space unchanged.
EventIdCoherence ==
    \A i \in 1..Len(sysEvents) :
        LET e == sysEvents[i] IN
        /\ ToReplay(e).id    = e.id
        /\ ToIFC(e).id       = e.id
        /\ ToCausality(e).id = e.id



CapRootMatchesAtPublishAndAudit ==
    lastEntryAtomic =>
        /\ Len(auditChain) > 0
        /\ auditChain[Len(auditChain)].capRoot = lastPublishedRoot

(*****************************************************************************
  Composite invariants for TLC (operational form of T7's inv-preservation core)
 *****************************************************************************)

M8_LocalInv ==
    /\ SystemTypeOK
    /\ CapBindingConsistent
    /\ DeclassConsistent
    /\ NonDeclassConsistent
    /\ AllWellWitnessed
    /\ AllParentsOlder
    /\ EventIdCoherence
    /\ CapRootMatchesAtPublishAndAudit

M8_PerModuleInv ==
    /\ M5!M5_FullInv
    /\ M6!M6_FullInv
    /\ M7!TypeOK
    /\ M7!DisclosureCorrectness
    /\ M7!PositionBinding

M8_FullInv ==
    /\ M8_LocalInv
    /\ M8_PerModuleInv

(*****************************************************************************
  Reference instantiation helpers (cfg uses  overrides)

  Same pattern as Lattice.tla / Caps.tla / Log.tla / Disclosure.tla.

  v0.1 reference values keep state space tractable:
    - Sigma_C / Sigma_I / Sigma_P each one-element (label triples = 8).
    - 2 transformers (Identity, DropWeb).
    - 2 cap ids (c1, c2).
    - 2 bytes / 2 hashes / 2 values.
    - MaxEvents = MaxCaps = MaxVecLen = 2.
 *****************************************************************************)

DefaultKind == {"spawn", "commit", "attest", "read", "write", "declassify",
                "cancel", "externalReq", "externalResp", "sample", "time"}

DefaultDetKinds == {"spawn", "commit", "attest", "read", "write",
                    "declassify", "cancel"}

DefaultNonDetKinds == {"externalReq", "externalResp", "sample", "time"}

DefaultObservableKinds == {"externalReq", "commit", "attest"}

DefaultDeclassifyKind == "declassify"

DefaultDetWitness == {"witness1"}

DefaultNoWitness == "noWitness"

DefaultPayload == {"p1", "p2"}

DefaultTransformers == {"Identity", "DropWeb"}

\* Sigma_P domain is single-element {"web"}; SUBSET Sigma_P =
\* {{}, {"web"}} (2 values). TransformerFn covers both.
DefaultTransformerFn ==
    [t \in {"Identity", "DropWeb"} |->
        IF t = "Identity"
        THEN [P \in SUBSET {"web"} |-> P]
        ELSE [P \in SUBSET {"web"} |-> P \ {"web"}]]

\* matched against transformers. Both caps are valid declassifier identities.
\* default-valued runtime fields (`expires |-> -1`, `caveats |-> << >>`)
\* mirroring Caps.tla v0.3 sub-letter.
DefaultRootCap ==
    [id      |-> "c1",
     granted |-> "DropWeb",
     parent  |-> "noCap",
     expires |-> -1,
     caveats |-> << >>]

DefaultDelegCap ==
    [id      |-> "c2",
     granted |-> "Identity",
     parent  |-> "c1",
     expires |-> -1,
     caveats |-> << >>]

DefaultAuthRel ==
    { <<DefaultRootCap, "DropWeb">>,
      <<DefaultDelegCap, "Identity">> }

DefaultAttenuatesRel ==
    { <<"Identity", "Identity">>,
      <<"Identity", "DropWeb">>,
      <<"DropWeb", "DropWeb">> }

DefaultCapId == {"c1", "c2"}

DefaultNoCap == "noCap"

DefaultBytes == {"b1", "b2"}

DefaultHash == {"h1", "h2"}

DefaultSystemGenesis == "b1"

DefaultH_op ==
    [b \in {"b1", "b2"} |->
        CASE b = "b1" -> "h1"
          [] b = "b2" -> "h2"]

DefaultSerializeFn ==
    [pair \in {"h1", "h2"} \X {"b1", "b2"} |-> pair[2]]

DefaultValues == {"v1", "v2"}

DefaultSigma_C == {"public"}
DefaultSigma_I == {"system"}
DefaultSigma_P == {"web"}



DefaultKindMin            == {"spawn", "declassify", "externalReq"}
DefaultDetKindsMin        == {"spawn", "declassify"}
DefaultNonDetKindsMin     == {"externalReq"}
DefaultObservableKindsMin == {"externalReq"}

DefaultTransformersMin == {"Identity"}

DefaultTransformerFnMin ==
    [t \in {"Identity"} |-> [P \in SUBSET {"web"} |-> P]]

DefaultCapIdMin == {"c1"}

\* default-valued runtime fields. Min variant for TLC tractability.
DefaultRootCapMin ==
    [id      |-> "c1",
     granted |-> "Identity",
     parent  |-> "noCap",
     expires |-> -1,
     caveats |-> << >>]

DefaultAuthRelMin ==
    { <<DefaultRootCapMin, "Identity">> }

DefaultAttenuatesRelMin ==
    { <<"Identity", "Identity">> }



DefaultStoreRootSys ==
    [s \in SUBSET Capability |-> Cardinality(s)]

DefaultCapRootsSys             == {-1, 0, 1, 2}
DefaultDetWitnessHashesSys     == {0}
DefaultNoWitnessRefSys         == -1



DefaultCapRootsMin     == {-1, 0, 1}
DefaultBytesMin        == {"b1"}
DefaultHashMin         == {"h1"}
DefaultSystemGenesisMin == "b1"

DefaultH_opMin ==
    [b \in {"b1"} |-> "h1"]

DefaultSerializeFnMin ==
    [pair \in {"h1"} \X {"b1"} |-> pair[2]]

================================================================================
