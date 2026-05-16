-------------------------------- MODULE Events --------------------------------
(***************************************************************************)
(* CTRLMATRIX L0 / M1 -- Event algebra (v0.4)                              *)
(*                                                                         *)

(*   - Added KernelOrTenant author-discriminator set                       *)
(*     {"kernel", "tenant"} mirroring the Lean-side                        *)

(*   - Extended `Event` record schema with `author : KernelOrTenant`       *)
(*     field. Default-valued discipline at the construction layer:         *)
(*     existing call sites (`Next`, AppendEvent constructions) extend      *)
(*     with `author |-> "tenant"` so that v0.1-cfg state-space behaviour   *)
(*     is unchanged; the kernel-author branch is the explicit case.        *)
(*   - Added `KernelAuthored(e)`  -- true iff `e.author =          *)

(*     `kernelAuthored : Bool` flag at the TLA+ side (no Bool field on     *)
(*     Events.tla; Determinism.tla v0.2 owns the Bool flag separately).    *)



(*                                                                         *)
(* v0.3 changes vs v0.2:                                                   *)

(*     {ExternalReq, Commit, Attest} are externally visible per I1; all    *)
(*     other kinds are internal. Partition is fixed at L0, not a           *)
(*     deployment parameter.                                               *)
(*   - Added IsObservable, ObsProj, and ObservabilitySanity. Schema        *)
(*     unchanged; AppendEvent / Next / Init / Spec untouched. M2           *)
(*     unaffected. Required by M3 (T1-obs).                                *)

(*     polymorphism). Adding a kind requires a scope-memo amendment.       *)
(*                                                                         *)
(* v0.2 changes vs v0.1:                                                   *)
(*   - chainHead' is deterministic: chainHead' = H(e) where H(e) = e.id.   *)
(*     Hash is now a defined set (1..MaxEvents), not a CONSTANT, and the   *)
(*     non-deterministic '\E h \in Hash' choice is gone. M6 will refine    *)
(*     H to a concrete collision-resistant hash.                           *)
(*   - Next builds events via component existentials, pre-constraining     *)
(*     id, prevHash, and parents instead of generating-then-filtering.     *)
(*     Cuts TLC successor count by ~40x at the smoke-test scale.           *)
(*                                                                         *)
(* Schema-only module. Defines the typed event record, the kind alphabet,  *)

(* and a single AppendEvent action that grows a finite trace of well-typed *)
(* events. Behavioural invariants live in later modules:                   *)
(*                                                                         *)
(*   M2  causality acyclicity (T6)                                         *)
(*   M3  determinism / replay (T1-obs, T1-bit, T2)                         *)
(*   M4  IFC + non-interference +  monotonicity (T3)                     *)
(*   M5  capability safety (T5)                                            *)
(*   M6  audit-log integrity / hash-chain semantics (T4)                   *)
(*                                                                         *)
(* M1 commits to the data shape every later module refines:                *)
(*                                                                         *)
(*   - the Event record schema                                             *)
(*   - the Kind enum (split DetKinds / NonDetKinds)                        *)
(*   - the IFC Label algebra (componentwise lattice ops)                   *)
(*   - the parent / hash linkage                                           *)
(*   - the Captured() syntactic predicate skeleton for I2                  *)
(*                                                                         *)
(* What this module does NOT do:                                           *)
(*   - constrain causality (M2)                                            *)
(*   - constrain IFC flow (M4)                                             *)
(*   - constrain capability authority (M5)                                 *)
(*   - define the actual hash function or its collision resistance (M6)    *)
(*                                                                         *)
(* AppendEvent is therefore deliberately permissive: any well-typed event  *)
(* whose id matches nextId, whose parents reference only earlier events,   *)
(* and whose prevHash matches chainHead, is admissible. Tightening lives   *)
(* in M2+.                                                                 *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* CONSTANTS                                                               *)
(*                                                                         *)
(* Tag alphabets are deployment parameters ( -- alphabet extensibility). *)
(* All theorems below are proved polymorphically over any finite           *)
(* (ConfTags, IntegTags, ProvTags). Cap, Payload, DetWitness are opaque    *)
(* finite sets at L0 / M1; they are refined by M5 (Cap), M6+ (Payload),    *)
(* and M3 (DetWitness).                                                    *)
(***************************************************************************)
CONSTANTS
    ConfTags,    \* secrecy alphabet (e.g. {public, user_pii, customer_data})
    IntegTags,   \* integrity alphabet, Biba-dual
    ProvTags,    \* provenance alphabet (e.g. {webFetch, userPrompt})
    Cap,         \* opaque capability-reference space
    Payload,     \* opaque event-payload space
    DetWitness,  \* opaque deterministic-witness space
    NoWitness,   \* sentinel: deterministic event has no detWitness
    TenantId,
    NoTenantId,
    MaxEvents    \* TLC bound on trace length

ASSUME
    /\ IsFiniteSet(ConfTags)
    /\ IsFiniteSet(IntegTags)
    /\ IsFiniteSet(ProvTags)
    /\ IsFiniteSet(Cap)
    /\ IsFiniteSet(Payload)
    /\ IsFiniteSet(DetWitness)
    /\ IsFiniteSet(TenantId)
    /\ NoWitness  \notin DetWitness
    /\ NoTenantId \notin TenantId
    /\ MaxEvents \in Nat \ {0}

(***************************************************************************)
(* Event ids and abstract hash space                                       *)
(*                                                                         *)
(* M1 models the hash space as 1..MaxEvents and the hash function as the   *)
(* identity on event ids: H(e) == e.id. This is enough to express the      *)
(* chain-link shape (prevHash of e_{n+1} equals H(e_n)) without modelling  *)
(* hash collisions. M6 refines Hash to an opaque CRH-output space and H    *)
(* to a concrete hash function with a stated collision-resistance          *)
(* assumption.                                                             *)
(***************************************************************************)
EventId == 1..MaxEvents
Hash    == EventId
NoHash  == 0                            \* sentinel: not in Hash

\* TLA+ has no Option type, so the Lean-side `Option Nat` shape is
\* mirrored via `EventId \cup {NoEventId}` set construction. NoEventId
\* is 0, disjoint from EventId (which starts at 1). Mirrors the
\* existing `NoHash == 0` and `NoWitness` sentinel discipline.
NoEventId == 0                          \* sentinel: not in EventId

\* Mirrors Lean `Replay.Event.tenant : Option TenantId := none` shape
\* TLA+ has no Option type, so the Lean-side `Option TenantId` shape
\* is mirrored via `TenantId \cup {NoTenantId}` set construction.
\* TenantId is opaque at L0 (deployment parameter, like `Cap` and
\* `Payload`); the kernel runtime binds tenant identity at event-
\* Caveat 1). Per the TLC budget (PLAN  line 184), model values for
\* TenantId restricted to {T1, T2} (cardinality 2; total set
\* `TenantId \cup {NoTenantId}` cardinality 3). Distinct sentinel name
\* (NoTenantId vs NoEventId) preserves alphabet hygiene; `NoTenantId
\* \notin TenantId` is enforced by the ASSUME above and by model-value
\* distinctness in the TLC cfg files (precedent: `NoWitness` /
\* `DetWitness` discipline at line 91-92 / 100). NoTenantId is a
\* CONSTANT (deployment-supplied opaque model value) rather than a
\* defined `==` constant, because TenantId model values are arbitrary
\* strings/symbols and a fixed Nat-style sentinel like `0` would not
\* be alphabet-clean — same precedent as NoWitness vs NoEventId
\* (NoWitness is a CONSTANT model value; NoEventId is a Nat literal
\* `0` because EventId is a Nat range starting at 1).

\* Mirror Lean `Replay.Event.refusalReasonCode : Option Nat := none`
\* types — the deployment-supplied codes are opaque at L0 but typed as
\* Nat; this matches the `EventId` Nat-range discipline). Sentinels are
\* defined as Nat literal `0` so no new CONSTANTS are needed (TLC and
\* TLAPS consumers see the literals directly; same shape as the
\* existing `NoEventId == 0` and `NoHash == 0` defined-`==` discipline).
\* Distinct sentinel names (NoReasonCode vs NoContractId vs NoEventId)
\* preserve alphabet hygiene per the NoTenantId vs NoEventId rationale
\* above — `refusalReasonCode` is a deployment-supplied opaque reason
\* code (NOT an event id, NOT a contract id), `violationContractId` is
\* a contract id (NOT an event id), so reusing `NoEventId` would
\* conflate semantics across three independent axes.
NoReasonCode   == 0                     \* sentinel: not a refusal reason code
NoContractId   == 0                     \* sentinel: not a contract id

(***************************************************************************)
(* Kind alphabet                                                           *)
(*                                                                         *)
(* DetKinds    -- deterministic kernel actions (no detWitness needed)      *)
(* NonDetKinds -- require detWitness in DetWitness for Captured() to hold  *)
(*                                                                         *)
(* Captured() is the syntactic gate for I2 (deterministic replay).         *)
(* M3 will lift Captured(T) into the replay-soundness theorem statements.  *)
(***************************************************************************)
\* "Retract" events; the new structural well-formedness predicate
\* `WellFormedRetraction` (defined below) enforces target binding.
\*
\* sequence (mirroring Lean  closed-alphabet expansion 14 → 18):
\* All four are DetKinds (matching Lean `Kind.isDet = true`), non-
\* Observable (NOT in `ObservableKinds`), non-KernelEmit (NOT in the
\* `{"ExternalReq", "ExternalResp", "Read"}` kernel-emit set used by
\* the TLA+  mirror follows the same discipline (no `"Replay"` Kind).
\*
\* sequence (mirroring Lean  Route (c) closed-alphabet expansion 20 → 21):
\* through v1.7-stable). HumanGate is a DetKind (matching Lean
\* `Kind.isDet = true`), non-Observable (NOT in `ObservableKinds`),
\* non-KernelEmit (NOT in the kernel-emit set used by
\* `WellFormedReplayMode` clause (a)).
\*
\*  — the originally-planned `humanGateContext : Option HumanGateRecord`
\* prerequisite. The TLA+ schema therefore extends ONLY by adding the new
\* DetKind constructor + the `WellFormedHumanGate`  below. The
\* default `Next` constructor (Events.tla L759-783) is therefore UNCHANGED
\* at v1.7  — no new default-valued field entry is needed because no
\* new field exists.
DetKinds    == {"Spawn", "Retract", "Commit", "Attest", "Read", "Write",
                "Declassify", "Cancel",
                "Plan", "Exec",
                "Refusal", "ContractViolation",
                "HumanGate"}
NonDetKinds == {"ExternalReq", "ExternalResp", "Sample", "Time"}
Kind        == DetKinds \cup NonDetKinds

(***************************************************************************)

(*                                                                         *)
(* Independent of the Det/NonDet split. Per scope memo §2 / I1, exactly   *)
(* three kinds are externally visible: requests issued to the outside     *)
(* world, commits of durable state, and attestations. All other kinds are *)
(* internal -- they are recorded in the trace but produce no external     *)
(* effect.                                                                 *)
(*                                                                         *)

(* a closed set is also closed). It binds T1-obs (M3): replay must        *)
(* reproduce ObsProj(trace).                                               *)
(***************************************************************************)
ObservableKinds == {"ExternalReq", "Commit", "Attest"}
InternalKinds   == Kind \ ObservableKinds

IsObservable(e) == e.kind \in ObservableKinds

(***************************************************************************)

(*                                                                         *)

(* 42). Closed two-element string set; the cross-artifact discipline is    *)
(* "Lean enum <-> TLA+ string set" -- same precedent as the Kind           *)


(*                                                                         *)
(* The `author` field on `Event` (added below) carries the discriminator   *)
(* at the schema level; default-valued discipline at the construction      *)
(* layer means existing call sites extend with `author |-> "tenant"` so    *)
(* that v0.1-cfg state-space behaviour is unchanged. The kernel-author     *)

(* default-valued .tenant discipline on the Lean side).                    *)
(*                                                                         *)
(* L0 boundary: at L0 the kernel runtime is responsible for setting        *)
(* `author := "kernel"` only on events the kernel itself authored.         *)
(* Tenant-injection of `author := "kernel"` at the runtime layer is L1+    *)

(* mirror surfaces the discriminator at the operational layer; the L1+    *)
(* kernel-runtime obligation is unchanged.                                 *)
(*                                                                         *)



(***************************************************************************)
KernelOrTenant == {"kernel", "tenant"}

\* TLA+ side. True iff the author discriminator picks the kernel branch.
\* (`kernelAuthored : Bool := false`); the TLA+ side does NOT introduce a
\* parallel Bool field on `Event` -- the enum-mirror set is sufficient,
KernelAuthored(e) == e.author = "kernel"

(***************************************************************************)

(*                                                                         *)
(* TLA+ schema mirror of Lean's `Mode` enum                                *)

(* Replay.lean L148-151). Closed two-element string set; cross-substrate   *)


(*                                                                         *)
(* The `mode` field on `Event` (added below) carries the discriminator at  *)
(* the schema level. Default-valued discipline at the construction layer:  *)
(* existing `Next` call site extends with `mode |-> "Live"` so that v0.1-  *)
(* cfg state-space behaviour is unchanged at MaxEvents=2 (mirrors v0.4     *)

(*                                                                         *)
(* L0 boundary: at L0 the schema mirror surfaces the discriminator only.   *)
(* The L1+ kernel-runtime obligation is to set `mode := "Replay"` only     *)
(* during legitimate replay sessions (e.g., post-crash recovery, audit     *)
(* replay, or test harness replay) and to ensure replay-mode events do     *)
(* not slip past kernel-emit-only event classes. This is L1+ TCB and       *)


(* entries (Bridge/M2.lean) can cite both substrates.                      *)
(*                                                                         *)
(* Capitalisation rationale: Lean lower-case constructor (`Mode.live`,     *)
(* `Mode.replay`) → TLA+ Capitalised string (`"Live"`, `"Replay"`)         *)
(* mirrors the Kind-side convention (Lean `Kind.spawn` → TLA+ `"Spawn"`).  *)
(***************************************************************************)
Mode == {"Live", "Replay"}

(***************************************************************************)
(* ObsProj -- externally-visible projection of a trace.                    *)
(*                                                                         *)
(* TLA+ side keeps full Event records (filtered). Lean side (M3) defines  *)
(* a tighter ObservableEvent type stripping internal fields (label,       *)
(* capRef, detWitness, parents, prevHash) -- those leak nothing externally *)
(* and must not appear in the simulation relation for T1-obs.             *)
(***************************************************************************)
ObsProj(trace) == SelectSeq(trace, IsObservable)

(***************************************************************************)

(*                                                                         *)
(*   Label = Confidentiality x Integrity x Provenance                      *)
(*                                                                         *)
(* Each factor is a powerset lattice over its tag alphabet. Lattice ops    *)
(* are componentwise.  (Provenance monotonicity) is proved by M4 against *)
(* this algebra.                                                           *)
(***************************************************************************)
Label  == [conf  : SUBSET ConfTags,
           integ : SUBSET IntegTags,
           prov  : SUBSET ProvTags]

Bottom == [conf |-> {},        integ |-> {},        prov |-> {}]
Top    == [conf |-> ConfTags,  integ |-> IntegTags, prov |-> ProvTags]

LabelJoin(a, b) ==                                  \* a \sqcup b
    [conf  |-> a.conf  \cup b.conf,
     integ |-> a.integ \cup b.integ,
     prov  |-> a.prov  \cup b.prov]

LabelMeet(a, b) ==                                  \* a \sqcap b
    [conf  |-> a.conf  \cap b.conf,
     integ |-> a.integ \cap b.integ,
     prov  |-> a.prov  \cap b.prov]

LabelLeq(a, b) ==                                   \* a \sqsubseteq b
    /\ a.conf  \subseteq b.conf
    /\ a.integ \subseteq b.integ
    /\ a.prov  \subseteq b.prov

(***************************************************************************)
(* Event record                                                            *)
(*                                                                         *)
(*   id         -- 1..MaxEvents identity                                   *)
(*   kind       -- element of Kind                                         *)
(*   payload    -- opaque data                                             *)
(*   label      -- IFC label                                               *)
(*   capRef     -- capability under which this event executed              *)
(*   detWitness -- DetWitness for NonDetKinds, NoWitness for DetKinds      *)
(*   parents    -- set of predecessor event ids                            *)
(*   prevHash   -- hash of preceding event in chain (NoHash for origin)    *)

(*                 mirrors Lean's `Event.author : KernelOrTenant := .tenant*)

(***************************************************************************)
\* fields mirroring Lean :
\* Each field's type is `EventId \cup {NoEventId}` (Option-Nat mirror
\* via sentinel set construction). Default-valued discipline at the
\* construction layer: `Next` pins both to NoEventId so v0.1-cfg
\* state-space behaviour is unchanged at MaxEvents=2 (mirrors the
\* v0.4 `author |-> "tenant"` discipline).  aliases
\* `SpawnedByOf(e)` / `RetractTargetOf(e)` exposed below for
\* call-site ergonomics; the schema field is the load-bearing form.
\*
\* field mirroring Lean  Agent G:
\*     binding). Type `TenantId \cup {NoTenantId}` (Option-TenantId
\*     mirror via sentinel set construction; same shape as the v1.4
\*     discipline: `Next` pins `tenant |-> NoTenantId` so v0.1-cfg
\*     state-space behaviour is unchanged at MaxEvents=2 (mirrors the
\*     `spawnedBy |-> NoEventId` disciplines).  alias
\*     `TenantOf(e)` exposed below for call-site ergonomics.
\*
\* FOUR additive fields mirroring Lean  (Replay.lean L426-429):
\* Each field's type mirrors the Lean field shape:
\*   - mode                : Mode  (closed 2-element non-Option enum;
\*                                  Lean uses `Mode := Mode.live` not
\*                                  `Option Mode`, so no sentinel needed)
\*   - linkedExecId        : EventId \cup {NoEventId}  (Option-Nat ↔ EventId
\*                                                      since the link is to
\*                                                      an event id)
\*   - refusalReasonCode   : Nat \cup {NoReasonCode}   (Option-Nat ↔ opaque
\*                                                      deployment-supplied
\*                                                      reason code; distinct
\*                                                      sentinel preserves
\*                                                      alphabet hygiene)
\*   - violationContractId : Nat \cup {NoContractId}   (Option-Nat ↔ contract
\*                                                      id; distinct sentinel)
\* Default-valued discipline at `Next` (Events.tla L502+):
\*   - mode                |-> "Live"          (mirrors Lean Mode.live default)
\*   - linkedExecId        |-> NoEventId       (mirrors Lean none default)
\*   - refusalReasonCode   |-> NoReasonCode    (mirrors Lean none default)
\*   - violationContractId |-> NoContractId    (mirrors Lean none default)
\* All four defaults preserve v0.1-cfg state-space behaviour unchanged at
\* MaxEvents=2.  aliases `ModeOf(e)`, `LinkedExecIdOf(e)`,
\* `RefusalReasonCodeOf(e)`, `ViolationContractIdOf(e)` exposed below for
\* call-site ergonomics (mirror `TenantOf(e)` / `SpawnedByOf(e)` /
\* `RetractTargetOf(e)` v1.4-v1.5 precedent).
Event == [
    id                  : EventId,
    kind                : Kind,
    payload             : Payload,
    label               : Label,
    capRef              : Cap,
    detWitness          : DetWitness \cup {NoWitness},
    parents             : SUBSET EventId,
    prevHash            : Hash \cup {NoHash},
    author              : KernelOrTenant,
    spawnedBy           : EventId \cup {NoEventId},
    retractTarget       : EventId \cup {NoEventId},
    tenant              : TenantId \cup {NoTenantId},
    mode                : Mode,
    linkedExecId        : EventId \cup {NoEventId},
    refusalReasonCode   : Nat \cup {NoReasonCode},
    violationContractId : Nat \cup {NoContractId}
]

\* Mirrors the Lean side's accessor shape (`e.SpawnedBy`,
\* `e.retractTarget`). The aliases are the " shape" sibling of
\* the schema field; either form is acceptable to consume in downstream
\* operators / TLAPS proofs. KernelAuthored(e) is the v0.4 precedent.
SpawnedByOf(e)     == e.spawnedBy
RetractTargetOf(e) == e.retractTarget

\* Mirrors the Lean side's accessor shape (`e.tenant`). Same -
\* alias discipline as SpawnedByOf / RetractTargetOf above.
TenantOf(e) == e.tenant

\* the four new fields. Mirror the Lean side accessor shape (`e.mode`,
\* `e.linkedExecId`, `e.refusalReasonCode`, `e.violationContractId`).
\* Same -alias discipline as TenantOf / SpawnedByOf / RetractTargetOf
\* (v1.4-v1.5 precedent).
ModeOf(e)                == e.mode
LinkedExecIdOf(e)        == e.linkedExecId
RefusalReasonCodeOf(e)   == e.refusalReasonCode
ViolationContractIdOf(e) == e.violationContractId

\* TLA+ mirror of Lean  `Event.wellFormedSpawnedBy` (Replay.lean L579)
\* and `Event.wellFormedRetraction` (Replay.lean L650). Per-event
\* predicates over the schema; no state-action change. The Lean side
\* carries the load-bearing proofs; the TLA+ side names the structural
\* cite the  name.
\*
\* WellFormedSpawnedBy(e) — two clauses (mirror Replay.lean L579-581):
\*   (a) e.kind = "Spawn" => e.spawnedBy /= NoEventId
\*       — a spawn event must NAME its origin (forecloses
\*         default-vacuity attack).
\*   (b) KernelAuthored(e) \/ e.spawnedBy = NoEventId
\*       — only kernel-authored events mint spawn relationships
\*         (forecloses tenant-forgery attack).
WellFormedSpawnedBy(e) ==
    /\ (e.kind = "Spawn" => e.spawnedBy /= NoEventId)
    /\ (KernelAuthored(e) \/ e.spawnedBy = NoEventId)

\* WellFormedRetraction(trace, e) — three clauses (mirror Replay.lean
\* L650-655):
\*   (a) e.kind = "Retract" => e.retractTarget /= NoEventId
\*       — a retract event must NAME its target.
\*   (b) e.kind = "Retract" /\ e.retractTarget = tid =>
\*         tid \in e.parents
\*       — the target must appear in the retract event's parents
\*         (combined with parents-older M2 invariant gives
\*         retract-event-id strictly post-dates target-id).
\*   (c) e.kind = "Retract" /\ e.retractTarget = tid =>
\*         \A i \in DOMAIN trace : trace[i].id = tid =>
\*           trace[i].kind /= "Retract"
\*       — terminal: retract-of-retract is structurally forbidden.
\* Trace-parameterized predicate signature for clause (c).
WellFormedRetraction(trace, e) ==
    /\ (e.kind = "Retract" => e.retractTarget /= NoEventId)
    /\ (\A tid \in EventId :
          e.kind = "Retract" /\ e.retractTarget = tid
            => tid \in e.parents)
    /\ (\A tid \in EventId :
          e.kind = "Retract" /\ e.retractTarget = tid
            => \A i \in DOMAIN trace :
                 trace[i].id = tid => trace[i].kind /= "Retract")

\* `Event.wellFormedTenantBinding` (Replay.lean L837 — Agent G ).
\* Trace-parameterized predicate (mirrors WellFormedRetraction shape
\* — needs the trace because both clauses look up the parent event
\* `p_event` in `trace` whose id matches the spawn edge target).
\* The Lean-side carries the load-bearing soundness theorems
\* (`tenant_binding_sound` + `t7_inherits_tenant_binding_sound` in
\* System.lean ); the TLA+ side carries the structural mirror so
\* a TLA+ schema mirror for downstream TLC checking) is satisfied.
\*
\* WellFormedTenantBinding(trace, e) — two clauses (mirror Replay.lean
\* L837-846 verbatim):
\*   (a) e.spawnedBy /= NoEventId =>
\*         (\A i \in DOMAIN trace :
\*            trace[i].id = e.spawnedBy =>
\*              (e.tenant /= NoTenantId /\ trace[i].tenant /= NoTenantId
\*                => e.tenant = trace[i].tenant))
\*       — when an event spawns from a parent, and BOTH sides commit
\*         a tenant, the tenants must agree. Default-`NoTenantId`
\*         events pass clause (a) vacuously (premise false on either
\*         side). Forecloses cross-tenant injection.
\*   (b) e.spawnedBy /= NoEventId =>
\*         (\A i \in DOMAIN trace :
\*            trace[i].id = e.spawnedBy =>
\*              (e.tenant = trace[i].tenant \/ KernelAuthored(e)))
\*       — when an event spawns from a parent, EITHER tenant equality
\*         is preserved across the spawn edge OR the spawning event
\*         is kernel-authored. Mirrors WellFormedSpawnedBy clause (b)
\*         shape exactly.
\*
\* Phantom-tenant arm foreclosed structurally by the `\A i \in DOMAIN
\* trace : trace[i].id = e.spawnedBy` quantification — a parent event
\* referenced by id but absent from the trace cannot violate either
\* clause (the implication antecedent is universally vacuous). This
\* matches Agent G's Lean-side H2 Attack #3 disposition.
WellFormedTenantBinding(trace, e) ==
    /\ (e.spawnedBy /= NoEventId =>
          \A i \in DOMAIN trace :
            trace[i].id = e.spawnedBy =>
              (e.tenant /= NoTenantId /\ trace[i].tenant /= NoTenantId
                => e.tenant = trace[i].tenant))
    /\ (e.spawnedBy /= NoEventId =>
          \A i \in DOMAIN trace :
            trace[i].id = e.spawnedBy =>
              (e.tenant = trace[i].tenant \/ KernelAuthored(e)))

\* Per-event predicate (no trace parameter); 2-clause:
\*
\* WellFormedReplayMode(e) — mirror Lean Replay.lean L1006-1008:
\*   (a) e.kind \in {"ExternalReq", "ExternalResp", "Read"}
\*         => e.mode = "Live"
\*       — kernel-emit events cannot be replays. Mirrors Lean
\*         `e.kind.isKernelEmit = true → e.mode = Mode.live`. The
\*         literal kernel-emit set is enumerated inline (no shadow
\*          KernelEmitKinds at v1.6 ; see honest residual
\*   (b) e.mode = "Replay" => e.kind \notin ObservableKinds
\*       — replay events cannot publish observable side-effects.
\*         Mirrors Lean `e.mode = Mode.replay → e.kind.isObservable = false`.
\*         {"ExternalReq", "Commit", "Attest"}).
\*
\* Default-vacuity (Lean H2 Attack #1, Replay.lean L1018-1027 mirror):
\* an event with `mode = "Live"` (constructor default) trivially passes
\* both clauses regardless of kind. Clause (a) consequent is satisfied
\* directly; clause (b) antecedent is false (`"Live" /= "Replay"`).
\* The substantive content is that any event committing to `Replay`
\* mode cannot be a kernel-emit kind and cannot publish observable
\* side-effects.
\*
\*      MUST skip kernel-emit events during replay) — L1+ TCB.
\*      is local; multi-event mode coherence is L1+).
WellFormedReplayMode(e) ==
    /\ (e.kind \in {"ExternalReq", "ExternalResp", "Read"}
          => e.mode = "Live")
    /\ (e.mode = "Replay" => e.kind \notin ObservableKinds)

\* Trace-parameterized predicate (mirrors WellFormedRetraction shape —
\* clause (a) looks up the linked exec event by id in trace). 2-clause:
\*
\* WellFormedPlanExec(trace, e) — mirror Lean Replay.lean L1079-1084:
\*   (a) \A eid \in EventId :
\*         e.kind = "Plan" /\ e.linkedExecId = eid
\*           => \E i \in DOMAIN trace :
\*                trace[i].id = eid /\ trace[i].kind = "Exec"
\*       — when a plan event commits to a link (linkedExecId /= NoEventId
\*         and ranges over EventId), the link must resolve to an Exec
\*         event in the trace. Mirrors Lean
\*         `e.kind = .plan ∧ e.linkedExecId = some eid →
\*           ∃ e' ∈ t, e'.id = eid ∧ e'.kind = .exec`.
\*         Quantifier-shape note: Lean's `e.linkedExecId = some eid`
\*         existential is mirrored via `\A eid \in EventId :
\*         e.linkedExecId = eid` because TLA+ has no Option binder; the
\*         `eid \in EventId` quantifier excludes the NoEventId sentinel
\*         (which is 0, not in EventId = 1..MaxEvents), so the implication
\*         is vacuously discharged when linkedExecId = NoEventId. This is
\*         WellFormedRetraction's parents-quantifier structure.
\*   (b) e.kind /= "Plan" => e.linkedExecId = NoEventId
\*       — only plan events carry linkedExecId. Tenants cannot forge
\*         linkage under non-plan kinds. Mirrors Lean clause (b).
\*
\* Default-vacuity (Lean H2 Attack #1, Replay.lean L1090-1099 mirror):
\* a non-Plan event with `linkedExecId = NoEventId` (constructor default)
\* trivially passes: clause (a) antecedent is false (kind /= "Plan"),
\* clause (b) consequent is satisfied directly.
\*
\* Phantom-Exec target (TLA+ H2 Attack #7): a Plan event with
\* `linkedExecId = eid` for some `eid \in EventId` that is absent from
\* trace fails clause (a) — the existential `\E i ... trace[i].id = eid`
\* has no witness, so the implication fails. This means the predicate
\* FAILS for phantom-link Plan events. The L0 spec demands link
\* resolution; the L1+ obligation (kernel runtime resolves phantom-link
\*
\*      L0 spec is per-event structural, not longitudinal liveness).
\*      "Exec" requirement; hierarchical-planning Kind.subPlan deferred
\*      to v1.7+.
WellFormedPlanExec(trace, e) ==
    /\ (\A eid \in EventId :
          e.kind = "Plan" /\ e.linkedExecId = eid
            => \E i \in DOMAIN trace :
                 trace[i].id = eid /\ trace[i].kind = "Exec")
    /\ (e.kind /= "Plan" => e.linkedExecId = NoEventId)

\* Per-event predicate (no trace parameter); 4-clause:
\*
\* WellFormedRefusal(e) — mirror Lean Replay.lean L1167-1177:
\*   (a) e.kind = "Refusal"
\*         => /\ e.detWitness    = NoWitness
\*            /\ e.retractTarget = NoEventId
\*            /\ e.linkedExecId  = NoEventId
\*       — refusal events are NON-ACTIONS: no witness, no retraction
\*         target, no exec linkage. Mirror of Lean clause (a) at the
\*         3-conjunct subset; HONEST UNDER-MIRROR by ONE conjunct
\*         `e.mintedCapId = none`, but the TLA+ Event schema does not
\*         carry a `mintedCapId : Option Nat` field at v1.5.1-stable
\*         the TLA+ mirror via `cap_mint`/Cap_mint Kind does not surface
\*         a parallel mintedCapId field — Cap is opaque via `capRef : Cap`
\*         at L312, not via a separate Option-Nat side-table). Closing
\*         this under-mirror would require either a v1.7+ schema
\*         extension OR a separate WellFormedCapMint ; both
\*   (b) e.kind = "ContractViolation" => e.violationContractId /= NoContractId
\*       — violation events MUST reference a contract by id. Mirrors
\*         Lean `e.kind = .contractViolation → e.violationContractId ≠ none`.
\*   (c) e.kind /= "Refusal" => e.refusalReasonCode = NoReasonCode
\*       — only refusal events carry refusalReasonCode (forgery defense).
\*         Mirrors Lean clause (c).
\*   (d) e.kind /= "ContractViolation" => e.violationContractId = NoContractId
\*       — only violation events carry violationContractId (forgery
\*         defense). Mirrors Lean clause (d).
\*
\* Default-vacuity (Lean H2 Attack mirror, Replay.lean L1183-1191): a
\* legacy event whose kind is neither "Refusal" nor "ContractViolation",
\* and whose new optional fields are at sentinel defaults, trivially
\* passes all four clauses.
\*
\*      non-action"; always-mark obligation is L1+).
\*      structurally permitted at L0; per-contract uniqueness L1+).
\*      — TLA+ clause (a) is the 3-conjunct subset of Lean's 4-conjunct
\*      clause (a). STRUCTURAL HONEST-DISCLOSURE; defer to v1.7+ schema
\*      extension or separate WellFormedCapMint .
WellFormedRefusal(e) ==
    /\ (e.kind = "Refusal"
          => /\ e.detWitness    = NoWitness
             /\ e.retractTarget = NoEventId
             /\ e.linkedExecId  = NoEventId)
    /\ (e.kind = "ContractViolation" => e.violationContractId /= NoContractId)
    /\ (e.kind /= "Refusal"           => e.refusalReasonCode   = NoReasonCode)
    /\ (e.kind /= "ContractViolation" => e.violationContractId = NoContractId)

\* `Event.wellFormedHumanGate` (Replay.lean L1583-1586 —  Route (c) /
\*
\* WellFormedHumanGate(e) — mirror Lean Replay.lean L1583-1586:
\*   e.kind = "HumanGate" => KernelAuthored(e)
\*       — only the kernel may author a human-gate event. This is the
\*         L0-structural arm of the "kernel-mediated human-assent"
\*         requirement: at L0 the kernel-authorship discriminator
\*         terminus; the IdP-cap-chain anchor pairing is L1+ kernel-
\*         cannot forge a human-gate event under this clause (the
\*         forgery defense). Mirrors Lean
\*         `e.kind = Kind.humanGate → e.author = KernelOrTenant.kernel`.
\*
\* Default-vacuity (Lean H2 Attack mirror, Replay.lean L1609-1613): a
\* legacy event whose kind is NOT "HumanGate" trivially passes the
\* single clause: the implication antecedent `e.kind = "HumanGate"` is
\* false for every non-HumanGate event, so the clause holds vacuously.
\* The substantive content is that any event committing to "HumanGate"
\* must be kernel-authored.
\*
\*      "kernel-authored human-gate"; it does NOT mandate a pairing
\*      with an IdP-cap-chain anchor at L0 — that anchor schema is
\*      framework).
\*      event human-gate-sequence semantics are L1+ kernel-runtime).
\*      field tags humanGate events with their tenant scope; structural
\*      additive coverage for cross-tenant binding is forward-compat to
\*      v1.8+).
\*      HumanGateRecord := none` field + `HumanGateRecord` payload
\*      predicate NAME + theorem NAMES are PRESERVED across the v1.8
\*      promotion (forward-compatible at NAME and STRUCTURE levels).
\*      The TLA+ mirror at v1.7  mirrors only the v1.7  1-clause
\*      shape; the v1.8  close will extend this  with the
\*      additional clause(s) once `humanGateContext` lands on the
\*      head+tail-factored Event schema.
\*
\* under-mirror (1-conjunct vs 1-conjunct); the full residual is
\* under v1.6  the under-mirror was structural (TLA+ Event lacked
\* `mintedCapId`); at v1.7  the parity is honest at the current
\* (1-clause) shape. The structural disclosure is the v1.8 deferral
\* itself, not a current-cycle under-mirror.
WellFormedHumanGate(e) ==
    e.kind = "HumanGate" => KernelAuthored(e)

(***************************************************************************)
(* Abstract hash function                                                  *)
(*                                                                         *)
(* M1 uses H(e) == e.id. Deterministic, single-valued. M6 refines.         *)
(***************************************************************************)
H(e) == e.id

(***************************************************************************)
(* WellWitnessed / Captured                                                *)
(*                                                                         *)
(* M1 defines these but does NOT enforce Captured() as an invariant.       *)
(* AppendEvent admits NonDet events with NoWitness. M3 will tighten the    *)
(* admission rule to require WellWitnessed and lift Captured into T1-obs / *)
(* T1-bit theorem hypotheses.                                              *)
(***************************************************************************)
WellWitnessed(e) ==
    \/ e.kind \in DetKinds
    \/ /\ e.kind \in NonDetKinds
       /\ e.detWitness \in DetWitness

Captured(trace) ==
    \A i \in DOMAIN trace : WellWitnessed(trace[i])

(***************************************************************************)
(* State                                                                   *)
(***************************************************************************)
VARIABLES
    events,     \* Seq(Event) -- append-only trace
    nextId,     \* next id to assign
    chainHead   \* hash of last event, NoHash iff trace is empty

vars == <<events, nextId, chainHead>>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ events    \in Seq(Event)
    /\ Len(events) <= MaxEvents
    /\ nextId    \in 1..(MaxEvents + 1)
    /\ chainHead \in Hash \cup {NoHash}
    /\ \A i \in DOMAIN events : events[i].id = i
    /\ \A i \in DOMAIN events : events[i].parents \subseteq 1..(i - 1)
    /\ (Len(events) = 0) <=> (chainHead = NoHash)
    /\ nextId = Len(events) + 1

(***************************************************************************)
(* Actions                                                                 *)
(*                                                                         *)
(* AppendEvent(e) -- the only state-changing action at M1. Admits any      *)
(* well-typed Event whose id matches nextId, whose parents reference only  *)
(* earlier events (giving topological order, hence acyclicity, by free     *)
(* construction -- T6 is essentially trivial at the schema level), and     *)
(* whose prevHash matches the current chainHead. The new chainHead is      *)
(* H(e). M6 refines H to a concrete hash function.                         *)
(***************************************************************************)
AppendEvent(e) ==
    /\ Len(events) < MaxEvents
    /\ e.id = nextId
    /\ e.parents \subseteq 1..(nextId - 1)
    /\ e.prevHash = chainHead
    /\ events'    = Append(events, e)
    /\ nextId'    = nextId + 1
    /\ chainHead' = H(e)

(***************************************************************************)
(* Next builds events via component existentials. id, prevHash, and the    *)
(* parents-domain are pre-constrained to the only legal values, so TLC     *)
(* does not generate-then-filter. This is the v0.2 fix for state-space     *)
(* blowup.                                                                 *)
(*                                                                         *)

(* (default-valued discipline). The v0.1 cfg therefore does not exercise   *)
(* the kernel-author branch -- state-space growth at v0.1 is zero. L1+     *)
(* operational specs widen the existential to range over KernelOrTenant    *)
(* if kernel-author transitions need TLC coverage.                         *)
(***************************************************************************)
Next ==
    \E kind    \in Kind,
       payload \in Payload,
       label   \in Label,
       capRef  \in Cap,
       dw      \in DetWitness \cup {NoWitness},
       parents \in SUBSET (1..(nextId - 1)) :
       AppendEvent([
           id                  |-> nextId,
           kind                |-> kind,
           payload             |-> payload,
           label               |-> label,
           capRef              |-> capRef,
           detWitness          |-> dw,
           parents             |-> parents,
           prevHash            |-> chainHead,
           author              |-> "tenant",
           spawnedBy           |-> NoEventId,
           retractTarget       |-> NoEventId,
           tenant              |-> NoTenantId,
           mode                |-> "Live",
           linkedExecId        |-> NoEventId,
           refusalReasonCode   |-> NoReasonCode,
           violationContractId |-> NoContractId
       ])

(***************************************************************************)
(* Initialisation                                                          *)
(***************************************************************************)
Init ==
    /\ events    = <<>>
    /\ nextId    = 1
    /\ chainHead = NoHash

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Sanity properties (M1 smoke tests for TLC)                              *)
(***************************************************************************)

\* Lattice sanity: bottom and top behave as expected; join is an upper
\* bound; meet is a lower bound.
LatticeSanity ==
    /\ LabelLeq(Bottom, Top)
    /\ \A a \in Label : LabelLeq(Bottom, a) /\ LabelLeq(a, Top)
    /\ \A a, b \in Label :
         /\ LabelLeq(a, LabelJoin(a, b))
         /\ LabelLeq(LabelMeet(a, b), a)

\* Chain-link shape: events empty iff chainHead = NoHash.
ChainLinkSanity ==
    \/ /\ events    = <<>>
       /\ chainHead = NoHash
    \/ /\ events   /= <<>>
       /\ chainHead \in Hash

\* Observability partition is well-formed: disjoint cover of Kind.
ObservabilitySanity ==
    /\ ObservableKinds \cup InternalKinds = Kind
    /\ ObservableKinds \cap InternalKinds = {}

================================================================================
