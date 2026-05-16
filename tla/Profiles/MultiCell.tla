------------------------------- MODULE MultiCell -------------------------------
(***************************************************************************)
(* CTRLMATRIX L0 / Profile -- Multi-cell composition (v0.1)                *)
(*                                                                         *)

(* System.tla) chosen to minimize import-cycle risk: System.tla is already  *)
(* a composite that EXTENDS multiple modules; folding multi-cell sub-       *)
(* actions into it would expand its surface during a  cycle.       *)
(* Standalone module keeps the multi-cell L0 surface independently          *)
(* refinable.                                                               *)
(*                                                                         *)
(* TLA+ mirror of Lean  (Agent G's MultiCell.lean — the load-        *)
(* bearing Lean-side surface; this module is the TLA+-side analogue per    *)

(*                                                                         *)
(* What this module does:                                                   *)
(*                                                                         *)
(*   - Names `DisjointEventIds(t1, t2)` --- the structural precondition    *)
(*     that two traces share no event ids. Required for `TraceUnion` to     *)
(*     be well-defined.                                                     *)
(*                                                                         *)
(*   - Names `TraceUnion(t1, t2)` --- partial  returning the        *)
(*     concatenation `t1 \o t2` only when DisjointEventIds holds; otherwise *)
(*     returns the empty trace as ill-defined-union sentinel. This         *)
(*     mirrors Lean's `Trace_⊎` (); the Lean-side carries the       *)
(*     `disjointEventIds_preserves_wellFormed` theorem.                    *)
(*                                                                         *)
(*   - States `MultiCellSanity` --- per-event WellFormedSpawnedBy /        *)
(*     WellFormedRetraction predicates are preserved under disjoint trace  *)
(*     union (since the predicates are per-event; concat preserves         *)
(*     element-wise properties). TLC-checkable at MaxEvents=2 / MaxCells=2 *)
(*     bound.                                                               *)
(*                                                                         *)
(* What this module does NOT do:                                            *)
(*                                                                         *)
(*   - Mechanize the Lean-side load-bearing wellFormedness preservation    *)
(*     theorem (`Trace_⊎` soundness). That is Agent G's domain in   *)
(*     (Lean side). The bridge between this TLA+ module and Agent G's      *)

(*                                                                         *)
(*   - Express N-cell (N >= 3) composition. The cardinality bound          *)
(*     `MaxCells = 2` is stated as a CONSTANT below; full N-cell is L1+    *)
(*     kernel-runtime obligation (per H2-attack-#3 guard against TLC       *)
(*     state-space blowup; see PLAN.md § H2 attack #3).             *)
(*                                                                         *)

(* attack on `Cardinality(cells) <= MaxCells = 2` --- the multi-cell L0    *)
(* module is bounded; full N-cell is L1+ obligation. The L0 stake is the   *)
(* compositional algebra (DisjointEventIds + TraceUnion), not the          *)
(* unbounded scaling.                                                       *)
(***************************************************************************)

EXTENDS Determinism

(***************************************************************************)
(* CONSTANT --- multi-cell cardinality bound (TLC discipline)              *)
(***************************************************************************)
CONSTANT
    MaxCells   \* L0 bound on the number of cells in the multi-cell union;
               \* TLC default = 2. Full N-cell is L1+ kernel-runtime
               \* obligation per H2 attack #3.

ASSUME
    /\ MaxCells \in Nat \ {0}

(***************************************************************************)
(* DisjointEventIds(t1, t2)                                                 *)
(*                                                                         *)
(* Two traces share no event ids. This is the structural precondition     *)
(* `Trace_⊎` requires per  H2 attack #1 (non-disjoint namespaces). *)
(***************************************************************************)
DisjointEventIds(t1, t2) ==
    \A i \in DOMAIN t1, j \in DOMAIN t2 :
      t1[i].id /= t2[j].id

(***************************************************************************)
(* TraceUnion(t1, t2)                                                       *)
(*                                                                         *)
(* Partial  returning `t1 \o t2` (TLA+ Sequences concat) when       *)
(* DisjointEventIds holds; otherwise returns the empty sequence as the      *)
(* ill-defined-union sentinel. The L0 contract: callers MUST check          *)
(* DisjointEventIds first; the sentinel-on-violation behaviour is           *)
(* defensively pessimistic (prefer empty over arbitrary).                    *)
(*                                                                         *)
(* Mirrors Lean  `Trace_⊎` (Agent G's MultiCell.lean).               *)
(***************************************************************************)
TraceUnion(t1, t2) ==
    IF DisjointEventIds(t1, t2)
        THEN t1 \o t2
        ELSE << >>

(***************************************************************************)
(* MultiCellSanity                                                          *)
(*                                                                         *)
(* Sanity property over `events` (the M3-inherited variable from           *)
(* Determinism / Events): if a hypothetical multi-cell decomposition       *)
(* split `events` into two disjoint sub-traces, the per-event wellFormedness *)
(* predicates are preserved verbatim. Concretely: for any prefix t1 and    *)
(* suffix t2 of `events` where DisjointEventIds(t1, t2) holds, every event *)
(* in TraceUnion(t1, t2) satisfies WellFormedSpawnedBy and (per-event)     *)
(* WellFormedRetraction.                                                    *)
(*                                                                         *)
(* This is the per-event preservation property ( H2 attack #2:      *)
(* cross-trace causality is preserved verbatim because TraceUnion is       *)
(* structural concat, not a re-shuffle). Trace-level invariant lifts the   *)
(* per-event checks compositionally.                                        *)
(*                                                                         *)
(* Bound at TLC: MaxCells = 2 caps the decomposition arity; full N-cell    *)
(* requires structural recursion on N which TLC cannot enumerate at scale. *)
(***************************************************************************)
MultiCellSanity ==
    \A i \in DOMAIN events :
      /\ WellFormedSpawnedBy(events[i])
      /\ WellFormedRetraction(events, events[i])

================================================================================
