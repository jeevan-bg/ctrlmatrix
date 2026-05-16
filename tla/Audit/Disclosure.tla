---- MODULE Disclosure ----
(***************************************************************************)
(* CTRLMATRIX M7 v0.1 -- Selective Disclosure (TLA+ side)                  *)
(*                                                                         *)

(*   - Operational disclosure semantics: Init_M7, Next_M7                  *)
(*     (CommitAction / RevealAction / VerifyDisclosureAction).             *)
(*   - Bounded TLC sanity invariants: TypeOK, DisclosureCorrectness,       *)
(*     PositionBinding.                                                    *)
(*                                                                         *)

(*   - Structural T8 theorem -- Lean side                                  *)
(*     (lean/AgentKernel/Disclosure.lean).                          *)
(*   - Position-binding hardness of the abstract                           *)
(*     VectorCommitmentScheme -- Sec. 8 black-box (asserted at L0;         *)
(*     concrete instantiation -- Merkle, KZG, RSA accumulator --           *)
(*     deferred to L2 per scope memo Sec. 5).                              *)
(*                                                                         *)
(* Mock primitive (TLC enumerates concretely):                             *)
(*   Commit(xs)         == xs       (identity)                             *)
(*   Open(xs, i)        == "proof"  (constant mock proof)                  *)
(*   Verify(c, i, v, p) == i \in DOMAIN c /\ c[i] = v /\ p \in Proofs      *)
(* Position-binding holds tautologically under the mock; cryptographic     *)
(* strength is asserted at Sec. 8 black-box and is not exercised by TLC.   *)

(* conformance side).                                                      *)
(*                                                                         *)

(*   committed         <-> implicit holder map (xs |-> Commit(xs))         *)
(*   verifiedSet       <-> set of accepted [c, i, v, p] tuples for which   *)
(*                          Lean's `verify c i v p = true`.                *)
(*   DisclosureCorrectness <-> Lean's `Disclosure.consistent` predicate.   *)
(*   PositionBinding   <-> T8's left disjunct (v = v') when the right      *)
(*                          disjunct (position-binding violation) is       *)
(*                          foreclosed by the mock.                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Values,        \* finite alphabet of vector values
    MaxVecLen      \* bound on vector length (TLC enumeration cap)

VARIABLES
    committed,     \* set of [vec, c] records -- holder-published commitments
    revealed,      \* set of [c, i, v, p] records -- holder-published openings
    verifiedSet    \* set of [c, i, v, p] records -- verifier-accepted openings

vars == <<committed, revealed, verifiedSet>>

(*--------------------------- Mock primitive --------------------------*)

Indices == 1..MaxVecLen

\* All vectors of length 1..MaxVecLen over Values, represented as TLA+
\* functions [1..n -> Values]. UNION over n flattens the size-indexed
\* family into a single set TLC can enumerate.
Vectors == UNION {[1..n -> Values] : n \in 1..MaxVecLen}

Commitments == Vectors          \* identity mock

Proofs == {"proof"}             \* single-element mock proof type

Verify(c, i, v, p) ==
    /\ i \in DOMAIN c
    /\ c[i] = v
    /\ p \in Proofs

(*------------------------------ Init ---------------------------------*)

Init ==
    /\ committed   = {}
    /\ revealed    = {}
    /\ verifiedSet = {}

(*--------------------- Operational transitions ----------------------*)

\* Holder publishes a commitment over a chosen vector. Identity mock:
\* Commit(xs) = xs.
CommitAction ==
    \E xs \in Vectors :
        /\ committed' = committed \cup {[vec |-> xs, c |-> xs]}
        /\ UNCHANGED <<revealed, verifiedSet>>

\* Holder reveals a single position of a previously-committed vector.
\* The opening is constructed honestly from the recorded vector;
\* dishonest holders are out of TLC scope (Sec. 8 black-box covers
\* binding-violation adversaries).
RevealAction ==
    \E entry \in committed :
    \E i \in DOMAIN entry.vec :
        LET d == [c |-> entry.c,
                  i |-> i,
                  v |-> entry.vec[i],
                  p |-> "proof"]
        IN  /\ revealed' = revealed \cup {d}
            /\ UNCHANGED <<committed, verifiedSet>>

\* Verifier accepts an opening that passes Verify. Idempotent.
VerifyDisclosureAction ==
    \E d \in revealed :
        /\ Verify(d.c, d.i, d.v, d.p)
        /\ verifiedSet' = verifiedSet \cup {d}
        /\ UNCHANGED <<committed, revealed>>

Next ==
    \/ CommitAction
    \/ RevealAction
    \/ VerifyDisclosureAction

Spec == Init /\ [][Next]_vars

(*----------------------------- Invariants ---------------------------*)

TypeOK ==
    /\ committed   \subseteq [vec : Vectors, c : Commitments]
    /\ revealed    \subseteq [c : Commitments, i : Indices,
                              v : Values,     p : Proofs]
    /\ verifiedSet \subseteq [c : Commitments, i : Indices,
                              v : Values,     p : Proofs]

\* Every verified opening corresponds to a committed (vec, c) entry
\* whose vec[i] = v. Mirrors Lean's `Disclosure.consistent` predicate.
DisclosureCorrectness ==
    \A d \in verifiedSet :
        \E entry \in committed :
            /\ entry.c = d.c
            /\ d.i \in DOMAIN entry.vec
            /\ entry.vec[d.i] = d.v

\* No two verified openings disagree on the same (c, i). Mirrors T8's
\* left disjunct (when the right disjunct -- position-binding violation
\* -- is foreclosed by the mock). Cryptographic strength asserted at
\* Sec. 8 black-box.
PositionBinding ==
    \A d1, d2 \in verifiedSet :
        (d1.c = d2.c /\ d1.i = d2.i) => d1.v = d2.v

============================================================================
