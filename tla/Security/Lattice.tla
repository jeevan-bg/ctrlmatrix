------------------------------- MODULE Lattice -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Sigma_C, Sigma_I, Sigma_P,
    Principal,
    Transformers,
    TransformerFn,
    AuthRel,
    MintingTrusted,
    NoOpTransformers,
    MaxEvents

ASSUME
    /\ IsFiniteSet(Sigma_C)
    /\ IsFiniteSet(Sigma_I)
    /\ IsFiniteSet(Sigma_P)
    /\ IsFiniteSet(Principal)
    /\ IsFiniteSet(Transformers)
    /\ AuthRel \subseteq (Principal \X Transformers)
    /\ NoOpTransformers \subseteq Transformers
    /\ MaxEvents \in Nat

(*****************************************************************************
  Lattice algebra
 *****************************************************************************)

Label == [c : SUBSET Sigma_C, i : SUBSET Sigma_I, p : SUBSET Sigma_P]

Join(L1, L2) == [c |-> L1.c \union L2.c,
                 i |-> L1.i \union L2.i,
                 p |-> L1.p \union L2.p]

Meet(L1, L2) == [c |-> L1.c \intersect L2.c,
                 i |-> L1.i \intersect L2.i,
                 p |-> L1.p \intersect L2.p]

Leq(L1, L2) == /\ L1.c \subseteq L2.c
               /\ L1.i \subseteq L2.i
               /\ L1.p \subseteq L2.p

Bottom == [c |-> {}, i |-> {}, p |-> {}]

RECURSIVE LabelJoinSet(_)
LabelJoinSet(LS) ==
    IF LS = {} THEN Bottom
    ELSE LET x == CHOOSE y \in LS : TRUE
         IN Join(x, LabelJoinSet(LS \ {x}))



EventId == Nat

Kinds == {"NonDeclass", "Declass", "DeclassMint"}

DeclassPayload == [
    what           : Transformers,
    who            : Principal,
    where          : EventId,
    when_evaluated : BOOLEAN
]

NullPayload == [what  |-> CHOOSE t \in Transformers : TRUE,
                who   |-> CHOOSE p \in Principal    : TRUE,
                where |-> 0,
                when_evaluated |-> FALSE]

Event == [
    id       : EventId,
    kind     : Kinds,
    parents  : SUBSET EventId,
    inLabel  : Label,
    outLabel : Label,
    payload  : DeclassPayload
]

(*****************************************************************************
   -- Provenance monotonicity (non-declassification events)
 *****************************************************************************)

R2_Holds(e) ==
    e.kind = "NonDeclass" =>
        /\ e.inLabel.c \subseteq e.outLabel.c
        /\ e.inLabel.i \subseteq e.outLabel.i
        /\ e.inLabel.p \subseteq e.outLabel.p

(*****************************************************************************
   -- Declassification well-formedness (apply arm)
 *****************************************************************************)

R3_Holds(e) ==
    e.kind = "Declass" =>
        LET pl == e.payload
            transformer == TransformerFn[pl.what]
        IN
        /\ <<pl.who, pl.what>> \in AuthRel
        /\ pl.where = e.id
        /\ pl.when_evaluated = TRUE
        /\ e.outLabel.p = transformer[e.inLabel.p]
        /\ e.inLabel.c \subseteq e.outLabel.c
        /\ e.inLabel.i \subseteq e.outLabel.i



R4_Holds(e) ==
    e.kind = "DeclassMint" =>
        LET pl == e.payload
            transformer == TransformerFn[pl.what]
            provLabel   == [c |-> {}, i |-> {}, p |-> e.inLabel.p]
        IN
        /\ <<pl.who, pl.what>> \in AuthRel
        /\ pl.where = e.id
        /\ Leq(provLabel, MintingTrusted)
        /\ (e.inLabel.p # {} \/ pl.what \in NoOpTransformers)
        /\ e.outLabel.p = transformer[e.inLabel.p]

(*****************************************************************************
  Operational semantics
 *****************************************************************************)

VARIABLE events
vars == <<events>>

Init == events = << >>

EmitNonDeclass ==
    /\ Len(events) < MaxEvents
    /\ \E parents \in SUBSET (1 .. Len(events)) :
       \E outL \in Label :
            LET newId == Len(events) + 1
                inL == LabelJoinSet({ events[pid].outLabel : pid \in parents })
                e == [id |-> newId,
                      kind |-> "NonDeclass",
                      parents |-> parents,
                      inLabel |-> inL,
                      outLabel |-> outL,
                      payload |-> NullPayload]
            IN
            /\ R2_Holds(e)
            /\ events' = Append(events, e)

EmitDeclass ==
    /\ Len(events) < MaxEvents
    /\ \E parents \in SUBSET (1 .. Len(events)) :
       \E who    \in Principal :
       \E what   \in Transformers :
       \E whenEv \in BOOLEAN :
       \E outC   \in SUBSET Sigma_C :
       \E outI   \in SUBSET Sigma_I :
            LET newId == Len(events) + 1
                inL == LabelJoinSet({ events[pid].outLabel : pid \in parents })
                outP == TransformerFn[what][inL.p]
                outL == [c |-> outC, i |-> outI, p |-> outP]
                pl == [what  |-> what,
                       who   |-> who,
                       where |-> newId,
                       when_evaluated |-> whenEv]
                e == [id |-> newId,
                      kind |-> "Declass",
                      parents |-> parents,
                      inLabel |-> inL,
                      outLabel |-> outL,
                      payload |-> pl]
            IN
            /\ R3_Holds(e)
            /\ events' = Append(events, e)


EmitDeclassMint ==
    /\ Len(events) < MaxEvents
    /\ \E parents \in SUBSET (1 .. Len(events)) :
       \E who    \in Principal :
       \E what   \in Transformers :
       \E whenEv \in BOOLEAN :
       \E outC   \in SUBSET Sigma_C :
       \E outI   \in SUBSET Sigma_I :
            LET newId == Len(events) + 1
                inL == LabelJoinSet({ events[pid].outLabel : pid \in parents })
                outP == TransformerFn[what][inL.p]
                outL == [c |-> outC, i |-> outI, p |-> outP]
                pl == [what  |-> what,
                       who   |-> who,
                       where |-> newId,
                       when_evaluated |-> whenEv]
                e == [id |-> newId,
                      kind |-> "DeclassMint",
                      parents |-> parents,
                      inLabel |-> inL,
                      outLabel |-> outL,
                      payload |-> pl]
            IN
            /\ R4_Holds(e)
            /\ events' = Append(events, e)

Next_M4 == EmitNonDeclass \/ EmitDeclass \/ EmitDeclassMint

Spec_M4 == Init /\ [][Next_M4]_vars

(*****************************************************************************
  Invariants
 *****************************************************************************)

LabelFlowSanity ==
    \A i \in 1 .. Len(events) :
        LET e == events[i] IN
        /\ R2_Holds(e)
        /\ R3_Holds(e)
        /\ R4_Holds(e)

ParentJoinConsistent ==
    \A i \in 1 .. Len(events) :
        LET e == events[i] IN
        e.inLabel = LabelJoinSet({ events[pid].outLabel : pid \in e.parents })

M4_Inv == LabelFlowSanity /\ ParentJoinConsistent

LabelFlowExtensibility ==
    Len(events) < MaxEvents => ENABLED Next_M4

(*****************************************************************************
  Reference instantiation helpers (used only via CONSTANT override in cfg).
  Keep the module polymorphic: the body of the spec never references these.
 *****************************************************************************)

DefaultTransformerFn ==
    [t \in {"Identity", "DropWeb"} |->
        IF t = "Identity"
           THEN [P \in SUBSET {"web", "user"} |-> P]
           ELSE [P \in SUBSET {"web", "user"} |-> P \ {"web"}]]

DefaultAuthRel ==
    { <<"p1", "Identity">>, <<"p1", "DropWeb">>, <<"p2", "Identity">> }


DefaultMintingTrusted ==
    [c |-> {}, i |-> {}, p |-> {"trusted_input", "system"}]

DefaultNoOpTransformers == {"Identity"}

==============================================================================
