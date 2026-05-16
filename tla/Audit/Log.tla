--------------------------------- MODULE Log ---------------------------------


EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
    Bytes,            \* finite set of byte payload representatives
    Hash,             \* finite set of hash output representatives
    Genesis,
    H,                \* [Bytes -> Hash]; total function
    Serialize,        \* [Hash \X Bytes -> Bytes]; total function
    MaxLen,           \* TLC bound on chain length (finite-state guard)
    CapRoots,
                      \* existential. Subset of Nat \cup {-1}; Entry.capRoot
                      \* is typed as Nat \cup {-1} (spec) but the existential
                      \* ranges over CapRoots for TLC tractability.
    DetWitnessHashes,
                      \* mirroring Lean's Option Hash content-hash space.
                      \* TLC-finite for state exploration; deployment
                      \* supplies cryptographic hash function at L1+.
    NoWitnessRef
                      \* analogous to NoParent / -1 in other modules.
                      \* Disjoint from DetWitnessHashes by ASSUME.

ASSUME
    /\ Genesis \in Bytes
    /\ H \in [Bytes -> Hash]
    /\ Serialize \in [Hash \X Bytes -> Bytes]
    /\ MaxLen \in Nat
    /\ CapRoots \subseteq (Nat \cup {-1})
    /\ IsFiniteSet(CapRoots)
    /\ IsFiniteSet(DetWitnessHashes)
    /\ NoWitnessRef \notin DetWitnessHashes

VARIABLE
    chain         \* Seq(Entry); tail is most-recently-appended

vars == <<chain>>

(******************************************************************************
  Schema
 *****************************************************************************)



Entry == [prev: Hash,
          payload: Bytes,
          capRoot: Nat \cup {-1},
          detWitnessRef: DetWitnessHashes \cup {NoWitnessRef}]



RECURSIVE Root(_)
Root(c) ==
    IF Len(c) = 0
    THEN H[Genesis]
    ELSE LET prefix == SubSeq(c, 1, Len(c) - 1)
             last   == c[Len(c)]
         IN  H[Serialize[<<Root(prefix), last.payload>>]]

(******************************************************************************
  Well-formedness

  A chain is well-formed iff every entry's `prev` field equals the
  root of the prefix preceding it. The first entry's `prev` equals
  `H(Genesis)` (the root of the empty prefix).

  Mirrors LogChain.wellFormed in Lean.
 *****************************************************************************)

RECURSIVE WellFormedAt(_, _)
WellFormedAt(c, i) ==
    IF i = 0
    THEN TRUE
    ELSE LET prefix == SubSeq(c, 1, i - 1)
         IN  /\ c[i].prev = Root(prefix)
             /\ WellFormedAt(c, i - 1)

ChainWellFormed == WellFormedAt(chain, Len(chain))

(******************************************************************************
  Type + bound invariants
 *****************************************************************************)

LogTypeOK == chain \in Seq(Entry)

BoundedLen == Len(chain) <= MaxLen

(******************************************************************************
  Operational actions

  AppendEntry(b)  -- Append a new entry whose payload is `b` and
                     whose prev field is Root(chain). By
                     construction this preserves ChainWellFormed.

  PublishRoot     -- Externalize (Root(chain), Len(chain)) without
                     mutating state. v0.1 stutter; future versions
                     may model a transparency-log abstraction.
 *****************************************************************************)

AppendEntry(b, capRoot, wref) ==
    /\ Len(chain) < MaxLen
    /\ chain' = Append(chain,
            [prev          |-> Root(chain),
             payload       |-> b,
             capRoot       |-> capRoot,
             detWitnessRef |-> wref])

PublishRoot ==
    /\ UNCHANGED chain



MatchesCapStore(cr) ==
    \* Hypothesis-shape conjunct, L0 boundary. At the Log.tla layer in
    \* isolation this is TRUE (operational; lets TLC explore the
    \* discharges this conjunct by coupling to a same-step
    \* Caps.PublishStoreSnapshot so that `cr = Caps.lastPublishedRoot`.
    \* Documented at the module-doc Caps-Log atomic coupling note.
    TRUE

PublishAndAudit(b, cr, wref) ==
    /\ chain # << >>
    /\ Len(chain) < MaxLen
    /\ MatchesCapStore(cr)
    /\ chain' = Append(chain,
            [prev          |-> Root(chain),
             payload       |-> b,
             capRoot       |-> cr,
             detWitnessRef |-> wref])

Init_M6 ==
    chain = <<>>

Next_M6 ==
    \/ \E b \in Bytes :
       \E cr \in CapRoots :
       \E wref \in DetWitnessHashes \cup {NoWitnessRef} :
           AppendEntry(b, cr, wref)
    \/ PublishRoot
    \/ \E b \in Bytes, cr \in CapRoots,
         wref \in DetWitnessHashes \cup {NoWitnessRef} :
           PublishAndAudit(b, cr, wref)



CapSnapshotPublished(cr) ==
    \E i \in 1 .. Len(chain) : chain[i].capRoot = cr



WitnessBound(e) ==
    e.detWitnessRef \in DetWitnessHashes

WitnessCommitPublished(wref) ==
    \E i \in 1 .. Len(chain) : chain[i].detWitnessRef = wref

Spec_M6 == Init_M6 /\ [][Next_M6]_vars

(******************************************************************************
  Composite invariant for TLC
 *****************************************************************************)

M6_FullInv ==
    /\ LogTypeOK
    /\ BoundedLen
    /\ ChainWellFormed



DefaultH ==
    [b \in Bytes |->
        CASE b = "b1" -> "h1"
          [] b = "b2" -> "h2"
          [] b = "b3" -> "h3"]

DefaultSerialize ==
    [pair \in Hash \X Bytes |-> pair[2]]



DefaultCapRoots == {-1, 0, 1, 2}



DefaultDetWitnessHashes == {0}

DefaultNoWitnessRef == -1

==============================================================================
