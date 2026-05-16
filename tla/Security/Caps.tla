--------------------------------- MODULE Caps ---------------------------------

EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS
    CapId,
    Principal,
    Transformers,
    AuthRel,
    AttenuatesRel,
    NoParent,
    MaxCaps,
    StoreRoot,
    Bytes
                        \* (TLC default-instantiates to a finite
                        \* singleton; reachable states never exercise
                        \* non-default values per Caveat C2)
                        \* stability; the `caveats` field type now
                        \* uses the typed `Caveat` record schema
                        \* below. `Bytes` is unused at the v0.4 schema
                        \* layer but kept for the System.tla INSTANCE
                        \* WITH-clause compatibility (System.tla
                        \* threads `Bytes <- Bytes`).

ASSUME
    /\ IsFiniteSet(CapId)
    /\ IsFiniteSet(Principal)
    /\ IsFiniteSet(Transformers)
    /\ IsFiniteSet(Bytes)
    /\ NoParent \notin CapId
    /\ AuthRel \subseteq (Principal \X Transformers)
    /\ AttenuatesRel \subseteq (Transformers \X Transformers)
    /\ MaxCaps \in Nat

\* DEFINED IN-MODULE (not a CONSTANT) so that System.tla's M5
\* bound is 0 (singleton 0..0) for v0.4: reachable states never
\* exercise non-default expires/caveats so the `now` value does not
\* gate any authorization at v0.4; the singleton bound is the
\* smallest non-trivial enumerable set. Wider values exercise
\* NotExpiredAt / CaveatHolds timeBound non-trivially at L1+ and
\* are a v0.5+ amendment.
MaxNow == 0



ParentRef == CapId \cup {NoParent}



CaveatType == {"timeBound", "requesterIs", "parentMustExist", "noCaveat"}

Caveat == [
    type   : CaveatType,
    untilT : 0..MaxNow,                           \* timeBound payload
    cid    : CapId \cup {NoParent}                \* requesterIs payload
                                                  \* (NoParent sentinel for
                                                  \* non-requesterIs)
]



RequestCtx == [
    now          : 0..MaxNow,
    requesterCid : CapId
]

Capability == [
    id      : CapId,
    granted : Transformers,
    parent  : ParentRef,
    expires : 0..MaxNow \cup {-1},
                                                  \* (v0.4: Nat narrowed to
                                                  \* 0..MaxNow for TLC;
                                                  \* full Nat is the abstract
                                                  \* spec.)
    caveats : Seq(Caveat)
                                                  \* Caveat record, was
                                                  \* opaque Seq(Bytes) at
                                                  \* v0.3.)
]



VARIABLES
    store,
    lastPublishedRoot

vars == <<store, lastPublishedRoot>>

Init ==
    /\ store = {}
    /\ lastPublishedRoot = -1

(*****************************************************************************
  Helpers
 *****************************************************************************)

UsedIds(s) == { c.id : c \in s }

(*****************************************************************************
  Closure invariant (operational form of T5)

  Every capability in the store is either kernel-minted (parent =
  NoParent) or descends from a present parent via an AttenuatesRel
  step. Maintained inductively by MintCap and Delegate; checked by
  TLC at every reachable state.
 *****************************************************************************)

CapClosure ==
    \A cap \in store :
        \/ cap.parent = NoParent
        \/ \E p \in store :
                /\ p.id = cap.parent
                /\ <<p.granted, cap.granted>> \in AttenuatesRel

IdsUnique ==
    \A c1, c2 \in store : c1.id = c2.id => c1 = c2

CapsTypeOK ==
    /\ store \subseteq Capability
    /\ Cardinality(store) <= MaxCaps



\* Legacy 2-place predicate (extracted from v0.3 inline; preserved
\*
\* Lean source: `def authorizes who what := who.granted = what`
\* TLA+ encoding: `<<who, cap.granted>> \in AuthRel` (the AuthRel
\* relation IS the operational refinement of `who.granted = what` at
\* the M5/M8 layer; AuthRel is a deployment-supplied subset of
\* `Principal \X Transformers`).
Authorizes(cap, who) == <<who, cap.granted>> \in AuthRel

\* Lean source (Caps.lean lines 338-343, `Capability.notExpired`):
\*     match cap.expires with
\*       | none   => true                   -- TLA+ encoding: cap.expires = -1
\*       | some t => decide (now ≤ t)       -- TLA+ encoding: now <= cap.expires
NotExpiredAt(cap, now) ==
    \/ cap.expires = -1
    \/ now <= cap.expires

\* Lean source (Caps.lean lines 361-370, `Caveat.holds`): match on the
\* 4-constructor inductive. TLA+ encoding: discriminate on `c.type`
\* and reduce to the corresponding payload-field test.
\*
\* `parent : CapId \cup {NoParent}` mirrors Lean's `parent : Option CapId`.
\* `parentInStore : BOOLEAN` is a caller-supplied verdict.
CaveatHolds(c, ctx, parent, parentInStore) ==
    \/ /\ c.type = "timeBound"
       /\ ctx.now <= c.untilT
    \/ /\ c.type = "requesterIs"
       /\ ctx.requesterCid = c.cid
    \/ /\ c.type = "parentMustExist"
       /\ parent /= NoParent
       /\ parentInStore = TRUE
    \/ c.type = "noCaveat"

\* Lean source (Caps.lean lines 377-382, `Capability.caveatsHold`):
\*     cap.caveats.all (Caveat.holds ctx cap.parent parentInStore)
\* TLA+ encoding: universal quantifier over the indexed sequence.
\* Empty caveat list trivially satisfies (vacuous TRUE), mirroring
\* Lean's `List.all` on `[]`. v0.3 Caveat C2 carries forward: every
\* MintCap/Delegate sets `caveats |-> << >>`, so reachable states
\* trivially satisfy this; deployment-policy obligation that
\* production caps set non-trivial caveats is unchanged.
CaveatsHoldAt(cap, ctx, parentInStore) ==
    \A i \in DOMAIN cap.caveats :
        CaveatHolds(cap.caveats[i], ctx, cap.parent, parentInStore)

\* of Lean's `authorizes_at`).
\*
\* Lean source (Caps.lean lines 405-413, `authorizes_at`):
\*     who.granted = what
\*       ∧ who.notExpired ctx.now = true
\*       ∧ who.caveatsHold ctx parentInStore = true
\*
\* TLA+ encoding mirrors structurally: conjunction of the legacy
\* 2-place test (`Authorizes`) with the two new runtime tests.
\* TLA+ layer by NAMING the runtime gate (mirrors Caps.lean's L0
\* B- close at lines 469-487 `quiet_authorize_foreclosed`).
AuthorizesAt(cap, who, ctx, parentInStore) ==
    /\ Authorizes(cap, who)
    /\ NotExpiredAt(cap, ctx.now)
    /\ CaveatsHoldAt(cap, ctx, parentInStore)

(*****************************************************************************
  Actions
 *****************************************************************************)

MintCap ==
    /\ Cardinality(store) < MaxCaps
    /\ \E newId \in CapId \ UsedIds(store) :
       \E g     \in Transformers :
            LET cap == [id      |-> newId,
                        granted |-> g,
                        parent  |-> NoParent,
                        expires |-> -1,
                        caveats |-> << >>]
            IN
            /\ store' = store \cup {cap}
            /\ UNCHANGED lastPublishedRoot

Delegate ==
    /\ Cardinality(store) < MaxCaps
    /\ \E parent \in store :
       \E newId  \in CapId \ UsedIds(store) :
       \E g      \in Transformers :
            /\ <<parent.granted, g>> \in AttenuatesRel
            /\ LET cap == [id      |-> newId,
                           granted |-> g,
                           parent  |-> parent.id,
                           expires |-> -1,
                           caveats |-> << >>]
               IN
               /\ store' = store \cup {cap}
               /\ UNCHANGED lastPublishedRoot



\* `ParentInStore(cap)` is the deterministic cap-store lookup verdict
\* used as the `parentInStore` argument to `AuthorizesAt`. Mirrors
\* Lean's L0 split (Caps.lean line 392-398 module-doc): the caller
\* supplies the verdict from cap-store discipline; binding it to
\* the deterministic `\E p \in store : p.id = cap.parent` test makes
\* the verdict a function of the current state rather than a free
\* existential, which keeps TLC tractable (no extra branching factor
\* at Invoke). The kernel-minted case (cap.parent = NoParent) returns
\* FALSE per Lean's `parentMustExist` semantics for kernel-minted
ParentInStore(cap) ==
    /\ cap.parent /= NoParent
    /\ \E p \in store : p.id = cap.parent

Invoke ==
    /\ \E cap \in store :
       \E who \in Principal :
       \E ctx \in RequestCtx :
            /\ AuthorizesAt(cap, who, ctx, ParentInStore(cap))
            /\ UNCHANGED <<store, lastPublishedRoot>>



PublishStoreSnapshot ==
    /\ lastPublishedRoot' = StoreRoot[store]
    /\ UNCHANGED store

Next_M5 == MintCap \/ Delegate \/ Invoke \/ PublishStoreSnapshot

Spec_M5 == Init /\ [][Next_M5]_vars

(*****************************************************************************
  Composite invariants for TLC
 *****************************************************************************)

M5_Inv ==
    /\ CapsTypeOK
    /\ IdsUnique
    /\ CapClosure

CapStoreExtensibility ==
    Cardinality(store) < MaxCaps => ENABLED Next_M5



PublishedRootMatchesAtLastPublish ==
    lastPublishedRoot \in {-1} \cup { StoreRoot[s] : s \in SUBSET store }

M5_FullInv ==
    /\ M5_Inv
    /\ CapStoreExtensibility
    /\ PublishedRootMatchesAtLastPublish

(*****************************************************************************
  Reference instantiation helpers (used only via cfg  substitution).
  Mirrors Lattice.tla's DefaultAuthRel pattern: TLC cfg parser cannot
  consume tuple-literal sets directly in CONSTANT = ... bindings, so
  the relations are defined here as operators and the cfg uses
  `AuthRel <- DefaultAuthRel` and `AttenuatesRel <- DefaultAttenuatesRel`.
 *****************************************************************************)

DefaultAuthRel ==
    { <<"p1", "Identity">>, <<"p1", "DropWeb">>, <<"p2", "Identity">> }

DefaultAttenuatesRel ==
    { <<"Identity", "Identity">>,
      <<"Identity", "DropWeb">>,
      <<"DropWeb", "DropWeb">> }



DefaultStoreRoot ==
    [s \in SUBSET Capability |-> Cardinality(s)]



DefaultBytes ==
    {0}

==============================================================================
