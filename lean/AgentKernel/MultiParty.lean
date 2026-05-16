import AgentKernel.Caps



namespace AgentKernel.MultiParty

open AgentKernel.Caps (Capability)

-- ============================================================
-- Profile — the L7 reserved profile alphabet
-- ============================================================


inductive Profile (Tag_C Tag_I Tag_P : Type) where
  
  | single    : Capability Tag_C Tag_I Tag_P
              → Profile Tag_C Tag_I Tag_P
  /-- Tier 2 — k-of-n threshold (L7+ semantics). -/
  | threshold : (k : Nat)
              → (caps : List (Capability Tag_C Tag_I Tag_P))
              → Profile Tag_C Tag_I Tag_P
  /-- Tier 2 — joint AND-aggregation (L7+ semantics). -/
  | joint     : (caps : List (Capability Tag_C Tag_I Tag_P))
              → Profile Tag_C Tag_I Tag_P
  
  | humanGate : Capability Tag_C Tag_I Tag_P
              → Profile Tag_C Tag_I Tag_P
  /-- Tier 2 — multi-principal delegation chain (L7+ semantics;
      NOT equivalent to L0 `Capability.parent`). -/
  | delegated : (anchors : List (Capability Tag_C Tag_I Tag_P))
              → Profile Tag_C Tag_I Tag_P

namespace Profile
  variable {Tag_C Tag_I Tag_P : Type}

  
  def tier1 : Profile Tag_C Tag_I Tag_P → Bool
    | .single _    => true
    | .threshold _ _ => false
    | .joint _       => false
    | .humanGate _   => false
    | .delegated _   => false

  /-- **Tier 1 lift.** Every `Capability` lifts to `Profile.single`
      structurally. This is the boundary at which L7 deployments
      that pin `Principal := Profile` reuse L0 code that pins
      `Principal := Capability` — wrap at the boundary. -/
  @[inline] def ofCapability
      (c : Capability Tag_C Tag_I Tag_P) : Profile Tag_C Tag_I Tag_P :=
    .single c

end Profile

end AgentKernel.MultiParty

-- ============================================================
-- Zero new named theorems. Zero new axioms.
-- ============================================================

-- ============================================================
-- integration memo (DOCUMENTATION-GRADE; zero new theorems).
--
-- pre-existing `MultiParty.Profile.humanGate` Tier-2 reservation
--
--
-- alphabet member. The `wellFormedSessionBind` predicate
-- (Replay.lean) enforces:
--   (a) `e.kind = Kind.session_bind → e.author = .kernel` — only
--       the kernel may author session-init bind events (forgery
--       defense + cap-chain termination at the kernel terminus).
--   (b) `e.kind = Kind.session_bind → e.kernelAuthored = true` —
--
-- The L0 surface names the kernel-authorship arm of the cap-chain
-- termination at `{kernel, IdP}`. The IdP-attestation arm (the
-- counterpart side of the binding cap chain) is L1+ kernel-runtime
--
-- ## Sibling-not-aliases relationship to MultiParty.Profile.humanGate
--
-- `Profile.humanGate : Capability → Profile` (line 259-261 above) is
-- the L7+ identity-layer reservation for human-in-loop authorization
--
-- `Replay.Kind.session_bind` is the L0 event-alphabet promotion for
-- the SESSION-INIT human-principal binding event class.
--
-- These are SIBLINGS, not aliases:
--   * Profile.humanGate is L7+ identity-layer SCHEMA reservation
--     Capability-handle pinned for human-in-loop authorization.
--   * Kind.session_bind is L0 event-class PROMOTION (Tier-1
--     It names the event recording the kernel-authored
--     session-init binding act.
--
-- `Kind.session_bind` (session-init human-principal binding); the
-- human-assent). The two are also siblings, not aliases. The current
-- `Kind.humanGate` for the runtime binding semantics.
--
-- ## What this block does NOT do
--
-- * No new `Profile` constructor. The `Profile` alphabet at L0
--   (`single`, `threshold`, `joint`, `humanGate`, `delegated`).
--   Adding a `Profile.sessionBind` constructor was considered and
--   REJECTED at H1: `Profile.humanGate` is the appropriate
--   not a new principal-shape class at L7+.
--
-- * No new named theorem. The cap-chain integration is documented
--   here; the substantive load-bearing content is
--   `Replay.Event.wellFormedSessionBind` + `System.session_bind_sound`
--   + `System.t7_inherits_session_bind_sound` (3 theorems shipped at
--
-- * No edits to lines 1-293 above. This block is TAIL-ADDITIVE
--   past `end AgentKernel.MultiParty` per v1.6 forbidden-file
--   discipline (head md5 boundary preserved at v1.6  baseline
--   `489949e1af4b70bbdee7cc35fca4bf2e`).
--
--
-- An L7+ deployment that pins `Principal := Profile` and uses the
-- `Profile.humanGate cap` constructor for session authorization
-- MUST author the corresponding `Replay.Event { kind :=
-- session_bind, author := .kernel, kernelAuthored := true, ... }`
-- event in the kernel runtime when the human session-init binding
-- act occurs. Field-level discipline:
--
--   * `e.author = KernelOrTenant.kernel` — kernel terminus enforced
--     at L0 by `wellFormedSessionBind` clause (a).
--     L0 by clause (b).
--   * `e.parents` — kernel runtime threads the prior
--     `Profile.humanGate` cap-chain anchor (the existing capability
--     SpawnedBy discipline; L1+ TCB.
--   * IdP-attestation receipt (the counterpart side of the binding
--     (NOT enforced at L0; the L0 spec asserts presence of the
--     kernel-authored `Kind.session_bind` event, not the
--     attestation pairing).
--
-- ## Tier-distribution impact
--
-- substantive theorems are in System.lean tail-additive block; this
-- ============================================================

-- ============================================================
-- ============================================================
--
-- scope at v1.7 ") ships the `Replay.Kind.humanGate` constructor
-- cap) and the 1-clause `Replay.Event.wellFormedHumanGate` predicate
-- at L0 EVENT layer. This block documents the relationship to the
-- pre-existing `MultiParty.Profile.humanGate : Capability → Profile`
-- Tier-2 reservation (line 259-261 above) AND to the `Kind.session_bind`
--
--
-- v1.7  ships `Replay.Kind.humanGate` as the 21st closed-alphabet
-- constructor, with `Event.wellFormedHumanGate e` enforcing ONE
--
--   `e.kind = Kind.humanGate → e.author = .kernel` — only the
--   kernel may author a human-gate event. A tenant action handler
--   cannot forge a human-gate event under this clause (forgery
--   defense). The IdP-cap-chain anchor pairing schema is L1+
--   at v1.7  Route (c) close.
--
-- ## Three-layer sibling-not-aliases relationship
--
-- After v1.7  Route (c) ships, three distinct "humanGate" /
-- "session-bind" objects coexist at non-overlapping layers:
--
--   * `MultiParty.Profile.humanGate : Capability Tag_C Tag_I Tag_P
--     → Profile` (line 259-261 above) — L7+ identity-layer SCHEMA
--     a human-in-loop authorization regime. Reserved for Tier-2
--     identity-layer wiring; carries no L0 event semantics.
--   * `Replay.Kind.session_bind` — L0 event-class promotion (Tier-1
--     arm. Fires once at session-open, terminating cap chains at
--     `{kernel, IdP}`.
--   * `Replay.Kind.humanGate` — L0 event-class promotion (Tier-1
--     *mid-run human-assent* arm. Fires per-policy-point; pairs
--     human-in-loop authorization with kernel-mediated action under
--     `Profile.humanGate` cap-chain anchor (the L7+ identity-layer
--     binding semantics; L0 names only the kernel-authorship
--     discriminator).
--
-- The three are siblings, not aliases. Each is necessary at its
-- layer; none of the three subsumes another:
--   * `Profile.humanGate` (L7+ SCHEMA) names the cap-chain class.
--   * `Kind.session_bind` (L0 EVENT) is the session-init arm.
--   * `Kind.humanGate` (L0 EVENT) is the mid-run-assent arm.
--
-- ## What this block does NOT do
--
-- This block adds zero theorems and zero axioms at the MultiParty
-- block precedent above, the L7+ identity-layer wiring of the three
-- objects (anchoring `Kind.humanGate` events to `Profile.humanGate`
-- cap-chain instances at runtime) is L1+ TCB obligation, NOT a v1.7
--  deliverable.
--
-- System.lean §6.D080c + §7.D080c:
--   * `Replay.Event.wellFormedHumanGate_default_event_holds`
--     legacy-default vacuity lemma; Tier 1 axiom-free.
--     (c) close: "a human-gate event has kernel as its author
--     terminus." Tier 1 axiom-free predicted.
--   * `System.t7_inherits_human_gate_sound` — SystemState-context
--     T7 inheritance lift. Tier 1 axiom-free predicted.
--
-- planned 2-clause shape). The dedicated `humanGateContext :
-- Option HumanGateRecord := none` field + `HumanGateRecord`
-- payload struct + clause (a) field-presence predicate are
--
--
-- The L0 spec asserts a kernel-authored `Replay.Kind.humanGate`
-- event records the kernel-mediated mid-run human-assent decision.
-- It does NOT mandate, at L0, the IdP-cap-chain anchor that pairs
-- the human-assent record with its identity-layer authorization.
--
--     authored human-gate events. L0 spec asserts kernel
--     authorship; the IdP-cap-chain anchor is L1+ Disclosure-
--     human-gate-sequence semantics is L1+ kernel-runtime
--     obligation (per-event L0 predicate; multi-event coherence
--     is L1+).
--     note.
--     `HumanGateRecord` struct + clause (a) field-presence
--     Option A factor (head+tail Event-record split) prerequisite.
--
-- ## Tier-distribution impact
--
-- This block adds zero theorems and zero axioms. The  Route (c)
-- block; this file's tier-distribution remains unchanged from
-- ============================================================
