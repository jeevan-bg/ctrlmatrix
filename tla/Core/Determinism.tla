----------------------------- MODULE Determinism -----------------------------
(***************************************************************************)
(* CTRLMATRIX L0 / M3 -- Determinism & replay (v0.2)                       *)
(*                                                                         *)

(*                                                                         *)
(*   - TLA+ owns the operational semantics + TLC bounded sanity check.    *)
(*   - Lean owns T1-obs (structural simulation theorem), the simulation   *)
(*     relation `R`, the observable projection `obs`, and the detWitness  *)
(*     algebra. See `lean/AgentKernel/Replay.lean` v0.1.           *)
(*                                                                         *)
(* This module:                                                            *)
(*                                                                         *)
(*   - States `DeterministicKernelAssumption` -- the unproved assumption  *)

(*   - Hoists M1's `Captured()` predicate as a state invariant            *)
(*     `CapturedInvariant`. M1's AppendEvent admits NonDet events with    *)
(*     NoWitness; M3 tightens via `WellWitnessedAppend`.                  *)
(*   - Defines `Spec_M3` = `Init /\ [][Next_M3]_vars`. Next_M3 differs   *)
(*     from M1's Next only in admitting NonDet events solely when their   *)
(*     detWitness is in DetWitness (i.e., WellWitnessed holds).           *)
(*                                                                         *)

(*   - Adds `KernelAuthoredEventIds : SUBSET EventId` CONSTANT representing*)
(*     the kernel-authored event-id set. Mirrors the new                   *)
(*     `kernelAuthored : Bool` field on `Replay.Event` and                 *)
(*     `Causality.Event` in Lean. The L0 SPEC names the set; the          *)
(*     L1+ TCB obligation (kernel runtime sets the membership only for    *)
(*     events the kernel itself authored) is documented as Caveat 1 of    *)


(*      (which gets EXTENDed in below); pre-existing v1.4-stable  *)

(*   - Adds `KernelAuthoredParentsInTrace` invariant: for every event     *)
(*     `e \in events` whose `e.id \in KernelAuthoredEventIds`, every      *)
(*     parent id `p \in e.parents` is itself in `KernelAuthoredEventIds`  *)
(*     AND realised as some event `pe \in events` with `pe.id = p`. The   *)
(*     TLA+ analog of Lean's `causalCompleteness` invariant (M2 / M3      *)
(*     coupling). Closes B- (causality-parents injection,         *)

(*                                                                         *)


(* `Causality.Event` are the mechanized side. TLAPS proof of              *)
(* `KernelAuthoredParentsInTrace` deferred (TLC bounded check only;       *)
(* same discipline as P4's Liveness theorem statements).                   *)
(*                                                                         *)
(* TLC bounded check at MaxEvents = 2 should report:                       *)
(*   - all M1 invariants hold under tightened admission;                   *)
(*   - CapturedInvariant holds at every reachable state;                   *)
(*   - KernelAuthoredParentsInTrace holds at every reachable state.       *)
(***************************************************************************)

EXTENDS Events

(***************************************************************************)

(*                                                                         *)
(* The kernel-authored set names which event ids were authored by the      *)
(* kernel runtime (vs claimed by tenant action handlers). At the L0         *)
(* abstract level we model this as a deployment CONSTANT subset of         *)
(* EventId; the kernel runtime at L1+ TCB is responsible for binding       *)
(* membership to actual kernel authorship at event-emission time.           *)
(*                                                                         *)
(* Mirrors `kernelAuthored : Bool` field on `Replay.Event` and             *)

(*                                                                         *)
(* No ASSUME constrains `KernelAuthoredEventIds` membership beyond        *)
(* `\subseteq EventId`; the deployment supplies which ids are kernel-     *)
(* authored. A permissive deployment may set                               *)
(* `KernelAuthoredEventIds = EventId` (every event claims kernel          *)
(* authorship -- vacuous L0 close, deployment-policy surface). A          *)
(* restrictive deployment sets `KernelAuthoredEventIds = {}` (no event    *)
(* claims kernel authorship -- vacuous on the                             *)
(* `KernelAuthoredParentsInTrace` invariant since the universal-          *)
(* quantifier premise is empty). The non-trivial deployment populates    *)
(* `KernelAuthoredEventIds` to reflect actual kernel-runtime authorship;  *)
(* that binding is L1+ TCB.                                                *)
(***************************************************************************)
CONSTANT
    KernelAuthoredEventIds  \* SUBSET EventId; deployment-supplied (L1+ TCB)

ASSUME KernelAuthoredEventIds \subseteq EventId

(***************************************************************************)

(*                                                                         *)
(* The unproved assumption that lifts T1-obs to T1-bit. Stated, not        *)
(* proved. Implementations claiming the bit-replay profile separately      *)
(* certify it (per scope memo \u00a78).                                       *)
(*                                                                         *)
(* Informal statement: every NonDet event's detWitness, when supplied to   *)
(* the kernel's per-kind replay function, deterministically reproduces    *)
(* the original event's payload, label, capRef, and external observable    *)
(* (when applicable) up to bit identity.                                   *)
(*                                                                         *)
(* M3 v0.1 states this as a named TLA+ definition that downstream proofs   *)
(* may reference as a hypothesis. The Lean side (Replay.lean) names the    *)
(* same assumption via the schema bridge in TCB \u00a78.                       *)
(*                                                                         *)
(* No state-level encoding: this is a property of the per-kind replay      *)
(* functions, which live outside the abstract spec. The conformance suite  *)
(* (Artifact C) will instantiate concrete replay functions and certify     *)
(* their bit-reproducibility.                                              *)
(***************************************************************************)
DeterministicKernelAssumption ==
    \* Placeholder: stated, not constrained at the abstract level.
    \* Concrete content lives in the Lean simulation relation
    TRUE

(***************************************************************************)
(* Captured as state invariant                                             *)
(*                                                                         *)
(* M1 defines `Captured(trace)` as a syntactic predicate but does NOT     *)
(* enforce it. M3 lifts it to a state-level invariant that must hold at   *)
(* every reachable state. Discharged by tightening AppendEvent (below).   *)
(***************************************************************************)
CapturedInvariant == Captured(events)

(***************************************************************************)
(* Tightened admission: WellWitnessedAppend                                *)
(*                                                                         *)
(* M3 refines M1's permissive AppendEvent. NonDet events are admitted     *)
(* only when their detWitness is in DetWitness (NoWitness rejected for    *)
(* NonDet kinds). Det events accept NoWitness, matching M1.               *)
(*                                                                         *)
(* The body mirrors M1's AppendEvent at the schema level; only the        *)
(* WellWitnessed conjunct differs.                                        *)
(***************************************************************************)
\* C-D9h-4): the newEvent record below mirrors the v1.6 Events.tla
\* `Next` constructor (lines 759-783) by binding all v1.4-v1.6 fields
\* to their default-valued sentinels. Pre-v1.4-stable, the partial
\* record was field-disjoint from v1.4 / v1.5 / v1.6 alphabet
\* additions (`author`, `spawnedBy`, `retractTarget`, `tenant`, `mode`,
\* `linkedExecId`, `refusalReasonCode`, `violationContractId`); SANY
\* tolerated this because the M3-side bridge does not exercise the
\* flagged this as latent drift; the rename here brings WellWitnessed
\* Append into structural symmetry with `Next` so future invariants
\* added to either side stay byte-equivalent at the L0 alphabet layer.
WellWitnessedAppend ==
    /\ Len(events) < MaxEvents
    /\ \E k       \in Kind,
          p       \in Payload,
          lab     \in Label,
          c       \in Cap,
          dw      \in DetWitness \cup {NoWitness},
          parents \in SUBSET (1..Len(events)) :
        LET newId      == nextId
            prev       == IF Len(events) = 0 THEN NoHash ELSE chainHead
            newEvent   == [id                  |-> newId,
                           kind                |-> k,
                           payload             |-> p,
                           label               |-> lab,
                           capRef              |-> c,
                           detWitness          |-> dw,
                           parents             |-> parents,
                           prevHash            |-> prev,
                           author              |-> "tenant",
                           spawnedBy           |-> NoEventId,
                           retractTarget       |-> NoEventId,
                           tenant              |-> NoTenantId,
                           mode                |-> "Live",
                           linkedExecId        |-> NoEventId,
                           refusalReasonCode   |-> NoReasonCode,
                           violationContractId |-> NoContractId]
        IN  /\ WellWitnessed(newEvent)
            /\ events'    = Append(events, newEvent)
            /\ nextId'    = nextId + 1
            /\ chainHead' = H(newEvent)

Next_M3 == WellWitnessedAppend

Spec_M3 == Init /\ [][Next_M3]_vars

(***************************************************************************)

(*                                                                         *)
(* `Captured` traces extend: at any reachable state below the MaxEvents    *)
(* bound, Next_M3 admits some successor. Failure means the schema is       *)
(* over-constrained and a Captured trace can be wedged into a dead end.    *)
(* This is the bounded-model statement of T2; the unbounded extension is   *)

(***************************************************************************)
CapturedReplayability ==
    Len(events) < MaxEvents => ENABLED Next_M3

(***************************************************************************)

(*                                                                         *)
(* For every event `e \in events` whose `e.id \in                           *)
(* KernelAuthoredEventIds`, every parent id `p \in e.parents` satisfies     *)
(* BOTH:                                                                    *)
(*   (a) `p \in KernelAuthoredEventIds` -- parent is itself kernel-auth'd  *)
(*   (b) \E pe \in events : pe.id = p   -- parent is in trace              *)
(*                                                                         *)
(* This is the TLA+ analog of Lean's `causalCompleteness W` invariant      *)

(*                                                                         *)
(*   `causalCompleteness W` :=                                              *)
(*     \A e \in W : e.kernelAuthored = true ->                              *)
(*       \A p \in e.parents : \E pe \in W :                                 *)
(*         pe.id = p /\ pe.kernelAuthored = true                            *)
(*                                                                         *)
(* Closes B- (causality-parents injection) at the                   *)
(* structural-naming layer:                                                 *)
(*   - An event whose parents reference event-ids absent from the trace    *)
(*     CANNOT be a member of `KernelAuthoredEventIds` under this           *)
(*     invariant; the attacker's synthesized event must either decline    *)
(*     kernel authorship or violate `KernelAuthoredParentsInTrace`.       *)
(*                                                                         *)
(* The invariant is intentionally vacuous on events whose `id \notin       *)

(* vacuity --                                                              *)
(* non-kernel-authored events have no obligation under                     *)
(* `causalCompleteness`; intentional and documented).                      *)
(*                                                                         *)
(* Empty-trace vacuity: when `events = <<>>`, the universal quantifier     *)

(* and documented; standard for universal-quantifier invariants).          *)
(*                                                                         *)
(* TLC verification: TLA+ owns operational state-space verification;       *)
(* TLAPS proof of `KernelAuthoredParentsInTrace` deferred to P6. The Lean  *)
(* mechanized side (Causality.lean's                                        *)
(* `kernel_authored_parents_in_trace_implies_no_orphan_injection`) is      *)

(***************************************************************************)
KernelAuthoredParentsInTrace ==
    \A i \in DOMAIN events :
        LET e == events[i]
        IN  e.id \in KernelAuthoredEventIds =>
              \A p \in e.parents :
                /\ p \in KernelAuthoredEventIds
                /\ \E j \in DOMAIN events : events[j].id = p

(***************************************************************************)
(* Sanity invariants for TLC                                                *)
(***************************************************************************)
M3_Inv ==
    /\ TypeOK
    /\ LatticeSanity
    /\ ChainLinkSanity
    /\ ObservabilitySanity
    /\ CapturedInvariant
    /\ CapturedReplayability
    /\ KernelAuthoredParentsInTrace

(***************************************************************************)

(*                                                                          *)

(* (lean/AgentKernel/Causality.lean L132-137). Surfaces the           *)

(* `Bridge/M3.lean` can cite the  name; the load-bearing inductive   *)
(* + transitivity / acyclicity / well-foundedness lemmas live on the Lean    *)
(* side ( deliverable, 5 named theorems).                                  *)
(*                                                                          *)
(* IntraCellHappensBefore(trace, a, b)                                       *)
(*   --- direct-parent on the existing M2-side `parents` field. NAMES the   *)
(*       existing relation so cross-cell reads cleanly.                     *)
(*                                                                          *)
(* CrossCellHappensBefore(trace, p, e)                                       *)
(*   --- one-step cross-cell happens-before. Mirrors Lean inductive:         *)
(*         HappensBefore.cross_cell_step {p : Nat} {e : Event} :              *)
(*           e ∈ W →                                                         *)
(*           e.SpawnedBy = some p →                                          *)
(*           p < e.id →                                                      *)
(*           e.kernelAuthored = true →                                       *)
(*           HappensBefore W p e.id                                          *)
(*       Premised on the Replay-side wellFormedSpawnedBy (clauses (a) +      *)
(*       (b)); the kernel-authorship guard forecloses the                    *)
(*       B-redteam-N2-carryover forgery attack.                              *)
(*                                                                          *)
(* HappensBeforeAny(trace, a, b)                                             *)
(*   --- single-step disjunction. Transitive closure stays L1+ TCB at the    *)
(*       TLA+ side (recursion + TLC hits performance walls); the Lean side   *)
(*       carries the inductive `trans` constructor and the `Trans`-typeclass *)
(*       composition ( cross_cell_step_transitive theorem).                *)
(*                                                                          *)
(* CrossCellAcyclicSchema -- structural acyclicity at the schema level:      *)
(*   no event satisfies `CrossCellHappensBefore(trace, e.id, e)`. Mirror     *)
(*   of Lean  cross_cell_acyclic (Causality.lean L324). Provable from      *)
(*   `e.spawnedBy < e.id` discipline (the `p < e.id` constructor clause).    *)
(*   Stated as INVARIANT for TLC; structural validity is by construction     *)
(*   when WellFormedSpawnedBy holds throughout the trace.                    *)
(***************************************************************************)
IntraCellHappensBefore(trace, a, b) ==
    \E i \in DOMAIN trace :
      /\ trace[i].id = b
      /\ a \in trace[i].parents

CrossCellHappensBefore(trace, p, e_id) ==
    \E i \in DOMAIN trace :
      LET ev == trace[i]
      IN  /\ ev.id = e_id
          /\ ev.spawnedBy = p
          /\ p < ev.id
          /\ KernelAuthored(ev)

HappensBeforeAny(trace, a, b) ==
    \/ IntraCellHappensBefore(trace, a, b)
    \/ CrossCellHappensBefore(trace, a, b)

CrossCellAcyclicSchema ==
    \A i \in DOMAIN events :
      ~ CrossCellHappensBefore(events, events[i].id, events[i].id)

==============================================================================
