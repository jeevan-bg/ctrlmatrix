------------------------------ MODULE MultiParty ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    CapHandles,         \* Opaque alphabet of Capability handles. Mirrors
                        \* Caps.tla's Capability schema; TLC default-
                        \* instantiates to a finite singleton.
    MaxThreshold,       \* TLC bound on the `k` parameter of
                        \* ThresholdProfile (to keep state space finite).
    MaxAnchors          \* TLC bound on |anchors| of DelegatedProfile.

ASSUME
    /\ IsFiniteSet(CapHandles)
    /\ MaxThreshold \in Nat
    /\ MaxAnchors \in Nat



ProfileKind == { "single", "threshold", "joint", "humanGate", "delegated" }

\* Tier 1 -- single-party shape (current Capability pin verbatim).
SingleProfile(cap) ==
    [ kind    |-> "single"
    , payload |-> cap ]

\* Tier 2 -- k-of-n threshold (L7+ semantics).
ThresholdProfile(k, caps) ==
    [ kind    |-> "threshold"
    , payload |-> [ k |-> k, caps |-> caps ] ]

\* Tier 2 -- joint AND-aggregation (L7+ semantics).
JointProfile(caps) ==
    [ kind    |-> "joint"
    , payload |-> caps ]

HumanGateProfile(cap) ==
    [ kind    |-> "humanGate"
    , payload |-> cap ]

\* Tier 2 -- multi-principal delegation chain (L7+ semantics;
\* NOT equivalent to Caps.tla's `parent` chain).
DelegatedProfile(anchors) ==
    [ kind    |-> "delegated"
    , payload |-> anchors ]

(*****************************************************************************
  Profile -- the reserved set. Documentation-grade union of the five
  Tier 1 + Tier 2 constructors. TLC does not enumerate this set
  (it is parameterized over CapHandles, k, and anchor lists); the
  constructors above are the entry points an L7+ amendment instantiates.
 *****************************************************************************)

Profile ==
    { SingleProfile(c) : c \in CapHandles }
    \cup { ThresholdProfile(k, caps) :
              k \in 0 .. MaxThreshold,
              caps \in UNION { [1 .. n -> CapHandles] : n \in 0 .. MaxAnchors } }
    \cup { JointProfile(caps) :
              caps \in UNION { [1 .. n -> CapHandles] : n \in 0 .. MaxAnchors } }
    \cup { HumanGateProfile(c) : c \in CapHandles }
    \cup { DelegatedProfile(anchors) :
              anchors \in UNION { [1 .. n -> CapHandles] : n \in 0 .. MaxAnchors } }

(*****************************************************************************
  Tier-discipline tag (mirrors Lean's `Profile.tier1`).

  Documentation-grade -- L0 does not consume this; L7+ deployments
  may instantiate it in their authorization predicate.
 *****************************************************************************)

IsTier1(p) ==
    p.kind = "single"

(*****************************************************************************
  Schema-shape ASSUMEs (no INVARIANTS; no ACTIONS).

  These ASSUMEs pin the alphabet shape for documentation-grade
  reservation. They are not invariant clauses (no INVARIANT keyword);
  they are static type-shape commitments.
 *****************************************************************************)

ASSUME
    /\ ProfileKind \subseteq STRING
    /\ "anonymous" \notin ProfileKind          \* Tier 4 forbidden
    /\ "trustless" \notin ProfileKind          \* Tier 4 forbidden

================================================================================
\* Zero new INVARIANTS; zero new ACTIONS; zero new TLAPS obligations.
\* No INSTANCE substitution into System.tla; module ships standalone.
\* Cross-artifact mirror at:
\*   - Lean: lean/AgentKernel/MultiParty.lean
\*   - Spec memo: spec/multi-party-profile-reservation.md
\*   - scope.md: §7 M5 forward bindings + §10 L7 row + §8.5 Item 21.
