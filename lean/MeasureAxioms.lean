import AgentKernel.IFC
import AgentKernel.IFC.LowEquiv
import AgentKernel.Bridge.M1
import AgentKernel.Bridge.M2
import AgentKernel.Bridge.M3
import AgentKernel.Bridge.M4
import AgentKernel.Bridge.M5
import AgentKernel.Bridge.M6
import AgentKernel.Bridge.M7
import AgentKernel.Bridge.M8
import AgentKernel.Bridge.MultiCell
import AgentKernel.Bridge.Liveness
import AgentKernel.Bridge.Universal
import AgentKernel.Contracts
import AgentKernel.PayloadDiscipline
import AgentKernel.System
import AgentKernel.ConformantL1
import AgentKernel.MultiCell
-- module is independent of System.lean / Disclosure.lean by design.

#print axioms AgentKernel.IFC.provenance_monotonicity_R2
#print axioms AgentKernel.IFC.declassification_well_formed_R3

#print axioms AgentKernel.IFC.r4_declass_origin_integrity
#print axioms AgentKernel.IFC.r4_declass_mint_has_payload

-- honest-naming verdict — closure is over `Kind` partitions, not
-- over `Event` authors; the authorship arm is L1+ TCB surfaced as
-- `event_authorship_predicate` + `taint_authorship_relay` below.)
#print axioms AgentKernel.IFC.taint_kind_closure

-- r4_declass_mint_nonvacuous closes the X1 vacuous-mint laundering
-- composition vector structurally at L0.
--
-- HYPOTHESIS-FREE derivation. The back-link conjunct is now a
-- structural part of  in IFC.wellLabeledStep (the 6th conjunct of
-- the declass-apply arm); the L1+ dmap_origin_predicate that pre-P4
-- gated the relay theorem is now logically redundant (preserved for
-- modulo signature change.
#print axioms AgentKernel.IFC.r4_declass_mint_nonvacuous
#print axioms AgentKernel.IFC.dmap_origin_relay

-- documentation upgrade. Author-boundary L0 predicate
-- `event_authorship_predicate` (a free `def`, not a theorem) +
-- `dmap_origin_predicate` + `dmap_origin_relay` pattern. The
-- predicate names the kernel-vs-tenant authorship boundary as L1+
-- TCB obligation; the theorem combines L0 structural
-- `taint_kind_closure` with L1+ `event_authorship_predicate` to
-- enrich the conclusion to `kernelAuthored e`.
--
-- Adds `author : KernelOrTenant := .tenant` field to Replay.Event +
-- IFC.Event + Causality.Event + SystemEvent. Drops the
-- `kernelAuthored : Event → Prop` opaque parameter from
-- `event_authorship_predicate` — predicate is now PURELY STRUCTURAL,
-- references `e.author = KernelOrTenant.kernel` directly.
-- `taint_authorship_relay` likewise drops the opaque parameter; the
-- conclusion now surfaces the structural discriminator
-- discharging `dmap_origin_predicate` via 's 6th-conjunct
-- structural back-link — same shape at the AUTHORSHIP axis as
#print axioms AgentKernel.IFC.taint_authorship_relay

#print axioms AgentKernel.Bridge.M5.BridgeSound_M5
#print axioms AgentKernel.Bridge.M5.MintStep_preserves_closed
#print axioms AgentKernel.Bridge.M5.DelegateStep_preserves_closed
#print axioms AgentKernel.Bridge.M5.InvokeStep_preserves_closed
#print axioms AgentKernel.Bridge.M5.LeanStep_M5_preserves_closed

#print axioms AgentKernel.Bridge.M6.BridgeSound_M6
#print axioms AgentKernel.Bridge.M6.AppendStep_preserves_wellFormed
#print axioms AgentKernel.Bridge.M6.PublishRootStep_preserves_wellFormed
#print axioms AgentKernel.Bridge.M6.LeanStep_M6_preserves_wellFormed

-- excludes mint events (LeanStep_M4 line 300); rename surfaces this.
#print axioms AgentKernel.Bridge.M4.BridgeSound_M4_nonMint
#print axioms AgentKernel.Bridge.M4.wellLabeledStep_lifts_under_extension
#print axioms AgentKernel.Bridge.M4.EmitNonDeclassStep_preserves_wellLabeled
#print axioms AgentKernel.Bridge.M4.EmitDeclassStep_preserves_wellLabeled
#print axioms AgentKernel.Bridge.M4.LeanStep_M4_preserves_wellLabeled

#print axioms AgentKernel.Bridge.M7.BridgeSound_M7
#print axioms AgentKernel.Bridge.M7.CommitAction_preserves_inv
#print axioms AgentKernel.Bridge.M7.RevealAction_preserves_inv
#print axioms AgentKernel.Bridge.M7.VerifyDisclosureAction_preserves_inv
#print axioms AgentKernel.Bridge.M7.LeanStep_M7_preserves_inv
#print axioms AgentKernel.Bridge.M7.commit_method_used
#print axioms AgentKernel.Bridge.M7.verify_method_used
#print axioms AgentKernel.Bridge.M7.M7State.init_invariant

#print axioms AgentKernel.Contracts.RegisterContractStep_preserves_closed
#print axioms AgentKernel.Contracts.operatorRootedB_implies_parent_witnessed
#print axioms AgentKernel.Contracts.operatorRooted_implies_parent_witnessed
#print axioms AgentKernel.Contracts.replayed_contract_after_window_close
-- propagates a caller-supplied admissibility witness. Statement + proof
-- preserved verbatim; only the identifier changed.
#print axioms AgentKernel.Contracts.contract_auth_propagates
#print axioms AgentKernel.Contracts.RegisterContractStep_yields_admissible

#print axioms AgentKernel.Contracts.registry_built_by_step_extends
#print axioms AgentKernel.Contracts.registry_built_by_yields_admissible
#print axioms AgentKernel.Contracts.registry_origin_invariant
#print axioms AgentKernel.Contracts.T_contract_auth_via_history

-- free `hStoreLift` audit-data hypothesis of `T_contract_auth_via_history`
-- with a derivation from a deployment-supplied `CapDigest` function +
-- audit-published `CapSnapshotRecord` history under the L0-boundary
-- collision-resistance hypothesis on the digest function. Same shape as
-- M6's `H ∘ serialize` CR-of-MTH carry-forward in §8. Mirrors the
-- derivation under a strengthened invariant). The original
-- backward-compat-rename precedent. `audited_snapshots_match_via_digest`
-- is a Tier 1 documentation lemma witnessing the
-- `auditPublishesSnapshot` ↔ TLA+ `CapSnapshotPublished` correspondence.
#print axioms AgentKernel.Contracts.T_contract_auth_via_history_audited
#print axioms AgentKernel.Contracts.audited_snapshots_match_via_digest

-- RegistryHistory pattern for the cBindings side-table:
-- `CBindingHistory : List CBindingStepRecord` + `wellFormedCBindingHistory`
-- at L0 by deriving `hCapBoundToContract` from the history rather than
-- accepting it as a free hypothesis. The new `T_contract_auth_via_history_with_cbindings`
-- corollary strengthens `T_contract_auth_via_history_audited`'s signature:
-- instead of accepting `cBindings` + `hCapBoundToContract` as free
-- hypotheses, it takes a well-formed `CBindingHistory` and derives both
#print axioms AgentKernel.Contracts.cbindings_built_by_step_extends
#print axioms AgentKernel.Contracts.cbindings_built_by_aux_origin
#print axioms AgentKernel.Contracts.wellFormedCBindingHistoryFrom_step_yields_witness
#print axioms AgentKernel.Contracts.cbindings_origin_invariant
#print axioms AgentKernel.Contracts.T_contract_auth_via_history_with_cbindings

-- Withholding / log truncation). Reachable via existing AgentKernel.Bridge.M6
-- import (which itself imports AgentKernel.Log).
#print axioms AgentKernel.Log.t4_prime_publish_consistency
#print axioms AgentKernel.Log.t4_audit_integrity_via_t4_prime
#print axioms AgentKernel.Log.LogChain.wellFormed_take

--   * IFC.t3_noninterference_modulo_payload_discipline — strengthens
--     T3's non-declass arm conclusion from `Factor.leq` to `=` under
--     the additional hypothesis `PayloadDiscipline.holds t`. Same
--     signature as T3 plus the extra hypothesis.
--   * PayloadDiscipline.payload_discipline_implies_label_join — the
--     leq direction derivable from `holds` alone (no `wellLabeled`
--     hypothesis). The L1+ binding the SDK calls when it cites
--     "labels were joined".
--   * PayloadDiscipline.compose_label_joins — structural correctness
--     lemma for `LabeledPayload.compose`: the result's label is the
--     join of the source labels.
-- Predicate `PayloadDiscipline.holds` defined in IFC.lean (sub-namespace
-- under IFC) to avoid an import cycle with PayloadDiscipline.lean.
-- LabeledPayload structured type lives in PayloadDiscipline.lean.
#print axioms AgentKernel.IFC.t3_noninterference_modulo_payload_discipline
#print axioms AgentKernel.PayloadDiscipline.payload_discipline_implies_label_join
#print axioms AgentKernel.PayloadDiscipline.compose_label_joins

-- well-labeling. New named theorem `t3_visible_projection_well_labeling`
-- is a one-line forwarder to `t3_noninterference` (preserved verbatim
-- Sabelfeld-Sands two-trace low-equivalence variant deferred as
-- future work). Predicted axiom tier: 2 [propext] inherited from
-- `t3_noninterference`.
#print axioms AgentKernel.IFC.t3_visible_projection_well_labeling

-- IFC.Event via default-valued field `outLabelPayload : LabeledPayload
-- A.3 — LabeledPayload + compose_label_joins structurally orphan at L0
-- pre-Session-43). New named theorem `t3_noninterference_modulo_
-- `outLabelPayloadCoherent` coherence conjunct: every visible event's
-- `outLabelPayload.label = outLabel`. Structure `LabeledPayload` lifted
-- from PayloadDiscipline.lean to IFC.lean to break the import cycle;
-- `compose` + named theorems remain in PayloadDiscipline.lean
-- `author : KernelOrTenant := .tenant` default-valued discipline at
-- Caveat 5 transitions from "structurally orphan" to "structurally
-- wired with L1+ TCB obligation." Predicted axiom tier: 2 [propext]
-- inherited from `t3_noninterference_modulo_payload_discipline`.
#print axioms AgentKernel.IFC.t3_noninterference_modulo_payload_discipline_strong

--   * Caps.authorizes_at_implies_authorizes_static — runtime-aware
--     `authorizes_at` strictly strengthens the legacy 2-place
--     `authorizes`. One-line projection (Tier 1, axiom-free).
--   * Caps.quiet_authorize_foreclosed — THE LOAD-BEARING B-ATTACK 3
--     CLOSE: an expired cap (`expires = some t`, `now > t`) cannot
--     satisfy `authorizes_at` for any `what`/`parentInStore`. Tier 2
--     [propext].
--     under the vacuous-deployment shape (`expires = none`,
--     `caveats = []`), `authorizes_at` and legacy `authorizes` agree
--     exactly. Justifies the default-valued-fields preservation of
#print axioms AgentKernel.Caps.authorizes_at_implies_authorizes_static
#print axioms AgentKernel.Caps.quiet_authorize_foreclosed
#print axioms AgentKernel.Caps.caveats_empty_implies_static_equiv

-- Two named theorems on Causality.lean (M2 v0.2):
--   * Causality.causal_completeness_implies_acyclic_strict — under
--     `causalCompleteness W`, every kernel-authored event's parents
--     are realized as kernel-authored events in W. Tier 1 axiom-free.
--   * Causality.kernel_authored_parents_in_trace_implies_no_orphan_injection —
--     in W whose claimed parent id is absent from W can be
--     kernelAuthored. Tier 1 axiom-free.
-- New `kernelAuthored : Bool := false` field on Replay.Event +
-- Causality.Event uses default-valued discipline (System.lean
-- `SystemEvent.toReplay`/`toCausality` projections compile unchanged).
#print axioms AgentKernel.Causality.causal_completeness_implies_acyclic_strict
#print axioms AgentKernel.Causality.kernel_authored_parents_in_trace_implies_no_orphan_injection

-- Three named theorems on Log.lean (M6 v0.2.2):
--   * LogChain.wellFormed_witnessRef_none — wellFormed chains have
--     `detWitnessRef = none` on every entry (the new wellFormedAux
--     conjunct). Tier 1 axiom-free.
--   * LogChain.witnessBoundCount_nil — empty chain has zero bound
--     witnesses (foldl base case). Tier 1 axiom-free.
--   * witness_binding_propagates — STRUCTURAL-ARITHMETIC IDENTITY:
--     witnessBoundCount increments by exactly 1 under append-with-
--     binding; unchanged under append-without-binding. Tier 1
--     axiom-free. The L0 hook the auditor cites for SLA-style
--     bounded-rate invariants ("kernel binds witness on at least
--     k% of entries").
-- New `Entry.detWitnessRef : Option Hash := none` field uses default-
-- valued discipline (Conformance.lean's `emit_append` compiles
-- unchanged via the default). T4 family preserved at Tier 3 — proof
-- amended with the 3-conjunct Entry.mk.injEq form, tier unchanged.
#print axioms AgentKernel.Log.LogChain.wellFormed_witnessRef_none
#print axioms AgentKernel.Log.LogChain.witnessBoundCount_nil
#print axioms AgentKernel.Log.witness_binding_propagates

-- CLOSE at L0. Two named theorems on System.lean (M8):
--   * System.system_event_id_coherence — for any SystemEvent e,
--     toReplay/toIFC/toCausality all agree on `id`. Proof is
--     three rfl. Tier 1 axiom-free.
--   * System.system_trace_projection_id_coherence — pairwise chain
--     corollary for trace-membership. Tier 1 axiom-free.
-- "Axiom" framing is honest-naming for "load-bearing structural
-- pattern. The trivial proof + load-bearing NAMING converts the
-- silent invariant into a CITED theorem in T7 inheritance composition.
-- TLA+ side: `EventIdCoherence` invariant in System.tla mirrors the
#print axioms AgentKernel.System.system_event_id_coherence
#print axioms AgentKernel.System.system_trace_projection_id_coherence

-- STRUCTURALLY at L0:
--   * Contracts.wellFormedRegistryHistory_now_monotone — i ≤ j →
--     H[i].now ≤ H[j].now. List-indexed monotonicity statement;
--     Tier 2 [propext].
--   * Contracts.wellFormedCBindingHistory_now_monotone — analogous on
--     CBindingHistory. Tier 2 [propext].
--   * Caps.quiet_authorize_foreclosed_with_audit — strengthens
--     quiet_authorize_foreclosed with audit-publication discipline:
--     ctx.matchesAuditedNow auditedNow + auditedNow > t ⟹ ¬ authorizes_at.
#print axioms AgentKernel.Contracts.wellFormedRegistryHistory_now_monotone
#print axioms AgentKernel.Contracts.wellFormedCBindingHistory_now_monotone
#print axioms AgentKernel.Caps.quiet_authorize_foreclosed_with_audit

-- bridge mechanization that began at P1 (M5 probe) and P1-followon
-- (M4/M6/M7). All four BridgeSound_M_i theorems target Tier 1 axiom-free
-- per Fix #1's meta-theorem template; preservation lemmas Tier 2 [propext]
-- (mirroring M4/M6/M7 P1-followon shape).
--
-- M1 Bridge (Replay machine + payload alphabet):
-- closure completeness, not a refinement derivation. Same finding-shape
#print axioms AgentKernel.Bridge.M1.BridgeSound_M1
#print axioms AgentKernel.Bridge.M1.AppendEventStep_preserves_captured
#print axioms AgentKernel.Bridge.M1.LeanStep_M1_preserves_captured

-- Substantive 9-arm action-label structural-packaging shape REPLACES
-- (`Iff.rfl` BridgeSound; load-bearing content is NAMING the T9
-- liveness alphabet). Temporal `~>` (leadsto) refinement strength
-- discharged).  lands the universal lift BridgeSound_Universal
-- consuming this + the M-series + MultiCell.
#print axioms AgentKernel.Bridge.Liveness.BridgeSound_Liveness

-- quantifier over the 10-arm Bridge module alphabet (M1..M8 +
-- MultiCell + Liveness). The proof is case-analysis on the
-- `ActionLabel_Universal` 10-arm identifier; each arm discharges via
-- the named per-module `BridgeSound_M_i` theorem already mechanized
-- load-bearing content is the universal quantifier, NOT new
-- refinement-strength content. Tier 2 [propext] inherited from the
-- M4 `_nonMint` clause (supremum of the 10 conjunct tiers).
-- .5 full operational-refinement upgrade CUT from v1.10 at Session
-- translation-validation + Verus-Rust cycle.
#print axioms AgentKernel.Bridge.Universal.BridgeSound_Universal

-- M2 Bridge (Causality / parents-older / kernelParents):
-- Substantive iff per Fix #1 meta-template (LeanStep_M2 defined
-- independently, not as existential closure of TLAStep_M2). Proof
-- requires `by_cases` on the kernelAuthored Bool — non-Iff.rfl. Closes
-- Note: file naming inversion vs spec/m-numbering-convention.md memo
-- (memo line 11/13 inverts M2/M3); see M-numbering memo amendment for
-- reconciliation.
#print axioms AgentKernel.Bridge.M2.BridgeSound_M2
#print axioms AgentKernel.Bridge.M2.EmitTenantEventStep_preserves_causalCompleteness
#print axioms AgentKernel.Bridge.M2.EmitKernelEventStep_preserves_causalCompleteness
#print axioms AgentKernel.Bridge.M2.LeanStep_M2_preserves_causalCompleteness
#print axioms AgentKernel.Bridge.M2.init_causalCompleteness

-- M3 Bridge (Determinism / replay-completeness / wellWitnessed):
-- Substantive iff per Fix #1 meta-template (case-split on
-- e.kernelAuthored Bool). Closes preservation of `Trace.captured`
-- under append. Connects Replay.lean's wellWitnessed/captured to
-- TLA+ Determinism.tla's WellWitnessed + KernelAuthoredParentsInTrace.
-- via `empty_trace_kernelAuthored_admissible`.
#print axioms AgentKernel.Bridge.M3.BridgeSound_M3
#print axioms AgentKernel.Bridge.M3.WellWitnessedAppendStep_preserves_captured
#print axioms AgentKernel.Bridge.M3.KernelAuthoredAppendStep_preserves_captured
#print axioms AgentKernel.Bridge.M3.LeanStep_M3_preserves_captured
#print axioms AgentKernel.Bridge.M3.empty_trace_kernelAuthored_admissible

-- M8 Bridge (System composition):
-- Composes per-module M{4,5,6,7} bridges plus M8-local emit/atomic
-- arms. BridgeSound_M8 is `Iff.rfl` (existential-closure shape per
-- M5/M7 sibling); composition-content lives in per-arm preservation
-- captured as a single LeanStep_M8 arm with atomicity-of-mutations
-- threading verified via `author_field_threaded` (rfl on three
-- projections). 13 of 16 theorems Tier 1 axiom-free; 3 Tier 2 [propext]
-- inherited from M7/Caps base.
#print axioms AgentKernel.Bridge.M8.BridgeSound_M8
#print axioms AgentKernel.Bridge.M8.M5Step_preserves_closed
#print axioms AgentKernel.Bridge.M8.M6Step_preserves_wellFormed
#print axioms AgentKernel.Bridge.M8.PublishAndAuditStep_preserves_wellFormed
#print axioms AgentKernel.Bridge.M8.PublishAndAuditWithCapMatchStep_preserves_wellFormed
#print axioms AgentKernel.Bridge.M8.M7Step_preserves_inv
#print axioms AgentKernel.Bridge.M8.LeanStep_M8_preserves_capStore_closed
#print axioms AgentKernel.Bridge.M8.LeanStep_M8_preserves_auditChain_wellFormed
#print axioms AgentKernel.Bridge.M8.LeanStep_M8_preserves_m7_invariant
#print axioms AgentKernel.Bridge.M8.publishAndAuditWithCapMatch_atomicity
#print axioms AgentKernel.Bridge.M8.decoupled_arms_clear_atomic_flag
#print axioms AgentKernel.Bridge.M8.M8State.init_capStore_closed
#print axioms AgentKernel.Bridge.M8.M8State.init_auditChain_wellFormed
#print axioms AgentKernel.Bridge.M8.M8State.init_m7_invariant
#print axioms AgentKernel.Bridge.M8.M8State.init_atomic_false
#print axioms AgentKernel.Bridge.M8.author_field_threaded

-- inheritance lemmas via And.intro (STRUCTURAL PACKAGING per
-- composition as citable rather than implicit; honestly named in
--   * T7_cross_replay_disclose — Replay (T1-obs) × Disclosure (T8').
--     Tier 2 [propext] inherited.
--   * T7_cross_audit_ifc — Audit (T4) × IFC (T3). Tier 3
--     [propext, Quot.sound] inherited from t7_inherits_t4 (NO new
--     Tier 3+ inflation; existing T4 axiom-load).
--   * T7_cross_cap_disclose — Capability (T5) × Disclosure (T8').
--     Tier 2 [propext] inherited from t7_inherits_t8'.
-- (UNCITED-theorem critique).
#print axioms AgentKernel.Bridge.M8.T7_cross_replay_disclose
#print axioms AgentKernel.Bridge.M8.T7_cross_audit_ifc
#print axioms AgentKernel.Bridge.M8.T7_cross_cap_disclose

-- Each new cross-theorem is `And.intro`-trivial over two M8-bridge
-- (`LeanStep_M8_preserves_events_extension`) factors out the trace-
-- side trivial structural packaging (per-arm ⟨[], rfl⟩ or ⟨[e], rfl⟩).
--   * LeanStep_M8_preserves_events_extension — Tier 1 axiom-free.
--   * T7_cross_replay_disclose_step_preserving — Tier 2 [propext]
--     inherited from `LeanStep_M8_preserves_m7_invariant`.
--   * T7_cross_audit_ifc_step_preserving — Tier 1 axiom-free; one tier
--     (Tier 3 [propext, Quot.sound]) because the bridge-step-level
--     `auditChain_wellFormed` aggregate dispatches structurally over
--     ActionLabel_M8 arms without the subst-rewrite that
--     `t7_inherits_t4` requires.
--   * T7_cross_cap_disclose_step_preserving — Tier 2 [propext]
--     inherited from `LeanStep_M8_preserves_m7_invariant`.
-- NO new axioms beyond inherited; NO Tier 4 inflation.
#print axioms AgentKernel.Bridge.M8.LeanStep_M8_preserves_events_extension
#print axioms AgentKernel.Bridge.M8.T7_cross_replay_disclose_step_preserving
#print axioms AgentKernel.Bridge.M8.T7_cross_audit_ifc_step_preserving
#print axioms AgentKernel.Bridge.M8.T7_cross_cap_disclose_step_preserving

-- to L0 not a typed predicate"). One named theorem on
-- `AgentKernel/ConformantL1.lean`:
--   * ConformantL1.T_L1_Lift — every SystemState satisfying
--     `ConformantL1.holds` inherits the eight L0 state-level
--     invariants (Replay-captured, IFC.wellLabeled, cap-store
--     closure, cap-map cross-table consistency, causalCompleteness,
--     audit-chain wellFormed, disclosure consistency,
--     PayloadDiscipline) by structural conjunct extraction. Tier 2
--     [propext] measured — proof body is `h` itself, but elaboration
--     of inner `wellLabeled` / `PayloadDiscipline.holds` / `consistent`
--     predicates costs `propext` (same mechanism as T7-T1obs / T7-T3 /
--     T7-T8' which also land at Tier 2 via the same elaboration).
--     ("trivial proof, load-bearing NAMING"). The load-bearing
--     content is the typed Lean predicate `ConformantL1.holds :
--     typed predicate exists); L1's PROOF obligation (preservation
--     under L1 step relation) is L1's territory per asymmetric-
--     ownership pattern.
#print axioms AgentKernel.ConformantL1.T_L1_Lift

-- residual close (additive). New default-valued field
-- `mintEventId : Option EventId := none` on `IFC.DeclassPayload`
-- carrying the mint-event-id semantics; `locus` preserved verbatim
-- as consuming-event-id legacy alias. New L0 named predicate
-- `mintEventId_consistent` (L1+ wiring obligation; default-vacuous
-- over `none`). New named theorem
-- `T_locus_mintEventId_correspondence` chains 's 6th conjunct
-- the L1+ wiring predicate to yield `mid = eMint.id` when L1+
-- follow-on `outLabelPayloadCoherent` (default-valued + L1+
-- structural population obligation). Predicted Tier 2 [propext]
-- ( if_pos discharge + L1+ predicate transitivity; same shape
-- as `dmap_origin_relay` + `taint_authorship_relay`). NO new
-- record-literal construction sites required (zero existing
-- DeclassPayload.mk literals across lean/); default-valued
-- discipline preserves all destructure patterns (`obtain ⟨p, ...⟩`
-- prefix-projects ignore the new tail field).
#print axioms AgentKernel.IFC.T_locus_mintEventId_correspondence

-- RegistryHistory pattern for the cap-mint side-table:
-- `CapabilityHistory : List CapMintRecord` + `wellFormedCapabilityHistory`
-- + `traceBacked` binding to the trace + `cap_mint_origin_invariant`
-- named theorem + `T_cap_id_authorship_via_history` corollary.
-- any cap whose id appears in a well-formed CapabilityHistory backed
-- by a trace traces structurally to an in-trace `Kind.cap_mint`
-- event with matching `mintedCapId`. New `Kind.cap_mint` constructor
-- (13th) added to Replay.Kind alphabet; new default-valued
-- `mintedCapId : Option Nat := none` field on `Replay.Event`.
-- C3 cap-id collisions across traces L1+ on the kernel allocator.
-- Predicted axiom tier: 2 [propext] for both new theorems.
#print axioms AgentKernel.Caps.cap_mint_origin_invariant
#print axioms AgentKernel.Caps.T_cap_id_authorship_via_history

-- step routes payloads through `LabeledPayload.compose`. New L0
-- NAMED predicate `kernelEmit_compose_routed` (trace-level structural
-- composition witness; for every kernel-emit event there exist
-- input + ctx labeled payloads `p1 p2` such that `outLabelPayload =
-- compose concat p1 p2`). Replaces the FREE label-equality
-- obligation of Path 1 (`outLabelPayloadCoherent`) with a STRUCTURAL
-- composition obligation; combined with `compose_label_joins`
-- (Tier 1 axiom-free), the label-equality follows from compose's
-- TYPE — kernel cannot route through compose AND drop the label.
-- New named theorem `t3_noninterference_kernel_emit_compose_routed`
-- (Tier 2 [propext]) derives `outLabelPayload.label = Label.join
-- inLabel ctxLabel` STRUCTURALLY for every kernel-emit event under
-- the routing predicate. Corollary
-- `t3_noninterference_kernel_emit_compose_routed_strong` (Tier 2
-- [propext]) projects the provenance factor for the chain into
-- the kernel-emit axis; Caveat 5 transitions from "structurally
-- wired with L1+ TCB obligation" (post-Path 1) to "structurally
-- wired AND L0-mechanized at kernel-emit; L1+ TCB residual narrowed
-- to non-kernel-emit construction sites" (post-Path 2). Caveats:
-- L1+ TCB on Path 1's `outLabelPayloadCoherent`; C3 declass arms
-- (/) are not on the kernel-emit axis (their kinds fail
-- `Kind.isKernelEmit`); C4 corollary projects only the provenance
-- factor (full-label coherence on the C/I factors remains Path 1
-- territory). NO existing theorems break (additive-only edits).
#print axioms AgentKernel.IFC.t3_noninterference_kernel_emit_compose_routed
#print axioms AgentKernel.IFC.t3_noninterference_kernel_emit_compose_routed_strong

-- ====================================================================
-- substantive Sabelfeld–Sands two-trace low-equivalence theorem family
-- + per-event-pairing inductive predicate `lowAgree` +  wellLabeled
-- substantive consumption lever + T7 family inheritance lift.
-- ====================================================================
-- 10 more theorems + 1 inductive predicate (all Tier 2 [propext]); Wave 3
-- enumerates [propext] lines" was factually inconsistent with the live
-- baseline, which carries 54 axiom-free entries from v1.1.1-stable
-- mixed with the [propext] entries). The 20 axiom prints below cover
-- the cumulative new LowEquiv + System surface:
-- The baseline regenerated at Wave 4 is no longer byte-identical to
-- the byte-diff gate at Wave 3; Wave 4 inherits the relaxation and
-- adds 9 more lines for completeness).
-- scope.md v1.1.1 → v1.2 at the same lock.

-- Wave 1 — Layer A foundation (4 Tier 1 axiom-free + 5 Tier 2 [propext]).
#print axioms AgentKernel.IFC.LowEquiv.lowProj_nil
#print axioms AgentKernel.IFC.LowEquiv.lowProj_singleton_visible
#print axioms AgentKernel.IFC.LowEquiv.lowProj_singleton_invisible
#print axioms AgentKernel.IFC.LowEquiv.lowEquiv_refl
#print axioms AgentKernel.IFC.LowEquiv.lowEquiv_symm
#print axioms AgentKernel.IFC.LowEquiv.lowEquiv_trans
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_empty
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_minimal
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_minimal_via_event_equality

-- Wave 2 — Layers B–E (10 Tier 2 [propext]).
#print axioms AgentKernel.IFC.LowEquiv.lowProj_cons_visible
#print axioms AgentKernel.IFC.LowEquiv.lowProj_cons_invisible
#print axioms AgentKernel.IFC.LowEquiv.lowProj_append
#print axioms AgentKernel.IFC.LowEquiv.lowEquiv_cons_invisible_left
#print axioms AgentKernel.IFC.LowEquiv.lowEquiv_cons_invisible_right
#print axioms AgentKernel.IFC.LowEquiv.lowEquiv_cons_visible_match
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence
#print axioms AgentKernel.IFC.LowEquiv.lowAgree_implies_lowEquiv
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_via_event_pairing
#print axioms AgentKernel.IFC.LowEquiv.wellLabeledStep_R3_outLabel_prov_determined

-- Wave 3 — System.lean T7-family inheritance lift (1 Tier 2 [propext]).
#print axioms AgentKernel.System.t7_inherits_t3_lowEquiv

-- Full Sabelfeld-Sands input→output chain
-- (1 inductive predicate `R3InputAgreement` not printed; 2 theorems
-- predicted Tier 2 [propext]). Baseline regen across all 3  agents
-- here.
#print axioms AgentKernel.IFC.LowEquiv.r3InputAgreement_implies_lowAgree
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_via_R3_input_agreement

-- Multi-policy generalization at LowEquiv layer + System.lean lift
-- (2 LowEquiv-layer theorems + 1 System.lean lift theorem; all 3
-- predicted Tier 2 [propext]). Baseline regen across all 3  agents
-- here.
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_multipolicy
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_via_event_pairing_multipolicy
#print axioms AgentKernel.System.t7_inherits_t3_lowEquiv_multipolicy

-- `lowEquiv → lowAgree` completeness direction
-- (3 helper theorems + 1 main theorem with nested structural
-- earlier collective paraphrase that read "all predicted Tier 2
-- [propext]"): main `lowEquiv_implies_lowAgree` + first helper
-- `lowProj_eq_nil_implies_all_invisible` Tier 2 [propext];
-- nil-left/nil-right helpers `lowAgree_nil_{left,right}_of_all_invisible`
-- Tier 1 axiom-free. NO `Classical.choice`, NO new `Quot.sound`
-- (pure structural induction; no `termination_by` / no
-- `WellFoundedRecursion`). Baseline regen across all 3  agents
-- regenerated here.
#print axioms AgentKernel.IFC.LowEquiv.lowProj_eq_nil_implies_all_invisible
#print axioms AgentKernel.IFC.LowEquiv.lowAgree_nil_left_of_all_invisible
#print axioms AgentKernel.IFC.LowEquiv.lowAgree_nil_right_of_all_invisible
#print axioms AgentKernel.IFC.LowEquiv.lowEquiv_implies_lowAgree

-- `Trace.replayEquivWithMint` 5-field sibling of `Trace.replayEquiv`
-- + regression theorems showing 5-field implies 4-field at Event +
-- Trace levels (2 theorems, both predicted Tier 1 axiom-free —
-- structural projection of conjuncts).
#print axioms AgentKernel.Replay.Event.replayEquivWithMint_implies_replayEquiv
#print axioms AgentKernel.Replay.Trace.replayEquivWithMint_implies_replayEquiv

-- carry-forward): Stale-`now` orphan wiring
-- (1 stepping-rule structure `KernelAuthorizationStep` not printed;
-- 2 wiring theorems — `kernel_step_foreclosed_unreachable` predicted
-- Tier 2 [propext] composing
-- `Caps.quiet_authorize_foreclosed_with_audit`;
-- `kernel_step_implies_static_authorization` predicted Tier 1
-- axiom-free).
#print axioms AgentKernel.System.kernel_step_foreclosed_unreachable
#print axioms AgentKernel.System.kernel_step_implies_static_authorization

-- batch (Items #1 + #2):
--   Replay.Event + Causality.Event + SystemEvent (default-valued,
--   byte-preserving). Ships wellFormedSpawnedBy + M2 mirror +
--   default-event holds + projection-preservation theorems.
--   constructor); retractTarget : Option Nat side-table field;
--   wellFormedRetraction predicate (3 clauses);
--   receiptValidUnderRetraction Bool predicate + iff theorem;
--   projection-preservation theorems.
-- All  theorems predicted Tier 1 axiom-free or Tier 2 [propext];
-- NO Tier 4 inflation. Baseline regen across the  surface is
-- performed by the parent at H4 close.
#print axioms AgentKernel.Replay.Event.wellFormedSpawnedBy_default_event_holds
#print axioms AgentKernel.Replay.Event.replayEquiv_independent_of_SpawnedBy
#print axioms AgentKernel.Replay.Event.replayEquiv_independent_of_retractTarget
#print axioms AgentKernel.Replay.Trace.receiptValidUnderRetraction_iff_no_retract
#print axioms AgentKernel.System.SystemEvent.toReplay_preserves_SpawnedBy
#print axioms AgentKernel.System.SystemEvent.toCausality_preserves_SpawnedBy
#print axioms AgentKernel.System.SystemEvent.toReplay_preserves_retractTarget
#print axioms AgentKernel.System.SystemEvent.toCausality_preserves_retractTarget

-- `wellFormedRetraction_implies_HappensBefore` ( H2-A2'
-- carry-forward).
--
-- HappensBefore inductive extended additively with a third constructor
-- `cross_cell_step` (constructors are not theorems; not measurable
-- which CITES the constructor).
--
-- 6 new named theorems (all predicted Tier 1 axiom-free; structural
-- packaging / direct constructor application). NO Tier 4 inflation.
-- Baseline regen across the  surface is performed by the parent
-- at H4 close.
#print axioms AgentKernel.Causality.cross_cell_step_intro
#print axioms AgentKernel.Causality.cross_cell_step_transitive
#print axioms AgentKernel.Causality.cross_cell_acyclic
#print axioms AgentKernel.Causality.cross_cell_well_founded
#print axioms AgentKernel.Causality.cross_cell_step_kernel_authored
#print axioms AgentKernel.Causality.wellFormedRetraction_implies_HappensBefore

-- Cross-cell causal binding D9 — `SpawnedBy` signed-cap binding via
-- `CapabilityHistory`. 3 new named theorems (all predicted Tier 1
-- axiom-free; structural destructure + existential introduction +
-- composition with  `wellFormedSpawnedBy` ties spawn relationships
-- DOCUMENTED-CAVEAT (cross-tenant residual is L1+ TCB per Caveat
-- C-D9-1; tenant-equality is not expressible at L0 because there is
-- no `tenant` field on `Replay.Event`). NO Tier 4 inflation.
#print axioms AgentKernel.Caps.spawn_cap_binding_sound
#print axioms AgentKernel.Caps.spawn_cap_binding_kernel_authored
#print axioms AgentKernel.Caps.spawn_cap_binding_no_spawn_vacuous

-- Hierarchical receipt composition `Compose-Verify(parent, [children])`
-- + tree-level disclosure soundness theorem in `Disclosure.lean`.
-- multi-agent receipts cluster).
--
-- 11 new named theorems (all predicted Tier 1 axiom-free or
-- Tier 2 [propext]; structural unfolding + `Iff.rfl` shape +
-- `simp only` over the equation compiler's auto-generated lemmas
-- for the recursive `treeVerifyAll`). NO Tier 4 inflation.
--
-- (`Iff.rfl`-shape over the definitions); LOAD-BEARING content is
-- (a) the defensively-pessimistic AND choice over OR rebutting H2
-- attack #2 adversarial-children; (b) the depth-n recursive
-- closure (`HierarchicalReceiptTree` + `treeVerify_sound`)
-- rebutting H2 attack #3 width-vs-depth.
#print axioms AgentKernel.Disclosure.composeReceipt_parent_eq
#print axioms AgentKernel.Disclosure.composeReceipt_children_eq
#print axioms AgentKernel.Disclosure.composeVerifyAll_iff_constituents_consistent
#print axioms AgentKernel.Disclosure.composeVerifyAll_trivial_iff_parent
#print axioms AgentKernel.Disclosure.composeVerify_falsified_by_bad_child
#print axioms AgentKernel.Disclosure.composeVerify_falsified_by_bad_parent
#print axioms AgentKernel.Disclosure.composeVerifyAll_disclosure_independence
#print axioms AgentKernel.Disclosure.composeVerify_sound
#print axioms AgentKernel.Disclosure.HierarchicalReceiptTree.treeVerifyAll_node_iff
#print axioms AgentKernel.Disclosure.HierarchicalReceiptTree.treeVerifyAll_leaf_iff_parent
#print axioms AgentKernel.Disclosure.HierarchicalReceiptTree.treeVerify_falsified_by_bad_subtree
#print axioms AgentKernel.Disclosure.HierarchicalReceiptTree.treeVerify_sound

-- Multi-cell composition `Trace_⊎` promotion to L0 — new module
--
-- 10 new named theorems. Predicted distribution Tier 1: 4 / Tier 2:
-- 6. Measured distribution: T1 × 3 / T2 × 5 / T3 × 2 (the two T3
-- entries are `disjointEventIds_iff_disjointEventIdsBool` and
-- `Trace.union_opt_eq_union_of_disjoint`; both inherit `Quot.sound`
-- through `simp` over `List.all_eq_true`, same shape as 
-- `receiptValidUnderRetraction_iff_no_retract` and v1.3-baseline
-- `Bridge.M8.T7_cross_audit_ifc`). NO Tier 4 inflation. Within
-- v1.3-baseline tier set. Honest tier residual documented at the
-- theorem docstrings + the agent's  report § Honest tier residual.
--
--   * `Trace.disjointEventIds_symm`, `_nil_left`, `_nil_right` are
--     STRUCTURAL PACKAGING (one-line lemmas pinning structural facts
--     about the predicate).
--   * `Trace.mem_union_iff` is STRUCTURAL UNFOLDING (re-export of
--     `List.mem_append` under the `Trace.union` definitional unfold).
--   * `disjointEventIds_iff_disjointEventIdsBool` and
--     `Trace.union_opt_eq_union_of_disjoint` are STRUCTURAL
--     UNFOLDING (Bool-Prop bridge, `if`-elimination).
--   * LOAD-BEARING headlines are
--     `traceUnion_disjoint_preserves_wellFormedSpawnedBy` and
--     `traceUnion_disjoint_preserves_wellFormedRetraction` (these
--     are the actual T2 compositional invariant-preservation
--     theorems that justify promoting `Trace_⊎` to L0); plus the
--     two cross-cell happens-before sibling theorems
--     (`causalityWorld_union_extends_HappensBefore` and
--     `traceUnion_preserves_cross_cell_HappensBefore`) that make
#print axioms AgentKernel.MultiCell.disjointEventIds_iff_disjointEventIdsBool
#print axioms AgentKernel.MultiCell.Trace.union_opt_eq_union_of_disjoint
#print axioms AgentKernel.MultiCell.Trace.disjointEventIds_symm
#print axioms AgentKernel.MultiCell.Trace.disjointEventIds_nil_left
#print axioms AgentKernel.MultiCell.Trace.disjointEventIds_nil_right
#print axioms AgentKernel.MultiCell.Trace.mem_union_iff
#print axioms AgentKernel.MultiCell.traceUnion_disjoint_preserves_wellFormedSpawnedBy
#print axioms AgentKernel.MultiCell.traceUnion_disjoint_preserves_wellFormedRetraction
#print axioms AgentKernel.MultiCell.causalityWorld_union_extends_HappensBefore
#print axioms AgentKernel.MultiCell.traceUnion_preserves_cross_cell_HappensBefore

-- predicate + `revoke_transitive_sound` headline theorem in `Caps.lean`.
--
-- 5 new named theorems (all predicted Tier 1 axiom-free; structural
-- induction on the `IsDelegatedFrom` derivation + structural
-- projection of `revokedRoot` clauses + falsifier-witness
-- construction). NO Tier 4 inflation.
--
--  * `revoke_transitive_sound` — HEADLINE theorem (substantive
--    structural-recursion + contradiction-derivation through the
--    supporting lemma `IsDelegatedFrom_implies_root_in_store`).
--  * `IsDelegatedFrom_implies_root_in_store` — substantive supporting
--    lemma (induction on the `IsDelegatedFrom` derivation; carries
--    the `direct` base witness through every `transitive` step).
--  * `revoke_transitive_breaks_wellFormed_chain` — bridge to
--    `Capability.wellFormed`, exposing the broken root link directly.
--  * `revoke_root_yields_no_descendant_in_store` — STRUCTURAL
--    PACKAGING (vacuity discharge for the `direct` base when the
--    root is gone; named for citability, NOT headlined).
--  * `revoke_transitive_sound_nonvacuous` — falsifier-witness
--    constructing a concrete `(preStore, postStore, rootId, cap)`
--    tuple satisfying the headline theorem's hypotheses + conclusion.
--
-- The L1+ residual (T7 inheritance lift to System.lean's M8
-- composition) is deferred to  fold per the  file-overlap carve;
-- the  close ships the load-bearing structural primitive on
-- Caps.lean.
#print axioms AgentKernel.Caps.IsDelegatedFrom_implies_root_in_store
#print axioms AgentKernel.Caps.revoke_transitive_sound
#print axioms AgentKernel.Caps.revoke_transitive_breaks_wellFormed_chain
#print axioms AgentKernel.Caps.revoke_root_yields_no_descendant_in_store
#print axioms AgentKernel.Caps.revoke_transitive_sound_nonvacuous

-- TLA+ mirror of v1.4 + alphabet/causality extensions, plus
-- (b) BridgeSound_*, (c) per-pairing T7 SHELL — all delivered in one
-- additive  block per bridge file.
--
-- 4 new named theorems. Predicted distribution Tier 2 [propext] across
-- the BridgeSound_* + T7 shell pair. Measured distribution: T1 axiom-
-- free × 3 + T2 [propext] × 1.
--
--   * BridgeSound_M2_Retract: T1 axiom-free (predicted T2; better than
--     prediction — the by_cases on Kind decidable equality folded
--     through the structural induction without invoking propext).
--   * T7_M2_retract_local: T1 axiom-free (predicted T2; same root
--     cause as above).
--   * BridgeSound_M3_CrossCell: T1 axiom-free (predicted T2; structural
--     destructure / recompose with no propositional rewriting).
--   * T7_M3_cross_cell_local: T2 [propext] (predicted T1; honest
--     residual — `List.mem_append.mpr` routes through propext under
--     elaboration; same shape as v1.3-baseline `LeanStep_M2_preserves_*`
--     family at T2 [propext] entries).
--
-- ZERO Tier 4 inflation. All within v1.3-baseline tier set.
--
-- are STRUCTURAL PACKAGING (per-pairing SHELL theorems exposing the M2 /
-- M3 layer's contribution to the System.lean T7 inheritance lift). The
-- full T7 lift in System.lean (.. cumulative) is  carry-forward
-- per parent's  file-overlap carve. Customer-visible guarantee chain
-- closes only after  fold lands the System.lean composition.
#print axioms AgentKernel.Bridge.M2.V14R3.BridgeSound_M2_Retract
#print axioms AgentKernel.Bridge.M2.V14R3.T7_M2_retract_local
#print axioms AgentKernel.Bridge.M3.V14R3.BridgeSound_M3_CrossCell
#print axioms AgentKernel.Bridge.M3.V14R3.T7_M3_cross_cell_local

-- NEW Bridge/MultiCell.lean (V14R4 namespace) + System.lean  T7
-- inheritance lifts for the cumulative .. named theorem set per
--
-- 11 new named theorems. Predicted distribution:
--   * T1 axiom-free × 5: BridgeSound_MultiCell_TraceUnion,
--     t7_inherits_hierarchical_receipt_compose_verify,
--     t7_inherits_spawn_cap_binding_sound,
--     t7_inherits_revoke_transitive_sound,
--     t7_inherits_M2_retract.
--   * T2 [propext] × 5: T7_MultiCell_traceUnion_local,
--     T7_MultiCell_traceUnion_retraction_local,
--     t7_inherits_traceUnion_disjoint_preserves_wellFormed,
--     t7_inherits_traceUnion_disjoint_preserves_wellFormedRetraction,
--     t7_inherits_M3_cross_cell.
--   * T3 [propext, Quot.sound] × 1: BridgeSound_MultiCell_TraceUnionOpt_disjoint
--     (predicted T2; honest residual — inherits from -baseline-T3
--     `Trace.union_opt_eq_union_of_disjoint`).
--
-- Measured distribution matches predicted.
--
-- ZERO Tier 4 inflation. All within v1.3-baseline tier set.
--
-- STRUCTURAL THREADING (direct apply of the underlying / theorem
-- with the SystemState projection passed through). The LOAD-BEARING
-- content lives in the underlying / theorems (Caps.lean,
-- Disclosure.lean, MultiCell.lean, Bridge/M2.lean, Bridge/M3.lean).
-- The Bridge/MultiCell.lean BridgeSound is `rfl`-trivial (named as
-- STRUCTURAL PACKAGING per H1).
#print axioms AgentKernel.Bridge.MultiCell.V14R4.BridgeSound_MultiCell_TraceUnion
#print axioms AgentKernel.Bridge.MultiCell.V14R4.BridgeSound_MultiCell_TraceUnionOpt_disjoint
#print axioms AgentKernel.Bridge.MultiCell.V14R4.T7_MultiCell_traceUnion_local
#print axioms AgentKernel.Bridge.MultiCell.V14R4.T7_MultiCell_traceUnion_retraction_local
#print axioms AgentKernel.System.t7_inherits_hierarchical_receipt_compose_verify
#print axioms AgentKernel.System.t7_inherits_spawn_cap_binding_sound
#print axioms AgentKernel.System.t7_inherits_revoke_transitive_sound
#print axioms AgentKernel.System.t7_inherits_traceUnion_disjoint_preserves_wellFormed
#print axioms AgentKernel.System.t7_inherits_traceUnion_disjoint_preserves_wellFormedRetraction
#print axioms AgentKernel.System.t7_inherits_M2_retract
#print axioms AgentKernel.System.t7_inherits_M3_cross_cell

-- the inductive `R3InputAgreement` 4-constructor bundle).
--
-- 2 new named theorems. Predicted distribution:
--   * T1 axiom-free × 0 / T2 [propext] × 2 (predicted at H1).
--
-- MEASURED distribution: T1 axiom-free × 1 / T2 [propext] × 1
-- (over-delivered — the parallel-induction helper
-- `r3InputAgreement_from_lowInputs_aux` lands T1 axiom-free; the
-- main theorem `t3_low_equivalence_from_lowInputs` lands T2 [propext]
-- `t3_low_equivalence_via_R3_input_agreement` at T2 [propext]).
--
-- helper over-delivered by avoiding `simp`/`omega`/`simpa` (the
-- `Classical.choice` leak path); main theorem matches predicted.
--
-- ZERO Tier 4 inflation. All within v1.3-baseline tier set.
--
-- lever-shape layer (per-position quantification → inductive
-- bundle → existing chain). Substantive mathematical content
-- textbook-shape per-position-quantified entry point complementary
#print axioms AgentKernel.IFC.LowEquiv.r3InputAgreement_from_lowInputs_aux
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_from_lowInputs

-- `cmap` (cap-mint) / `contractRegistry` / `author` oracle-map
-- axes. Each theorem is a forward-derivation relay (in-trace
-- field witness → existential origin-side witness) under an
-- explicit wellformedness predicate that names the L1+ TCB
-- runtime-discharge obligation. Mirrors `dmap_origin_relay`'s
--
-- 3 new named theorems (one per item) + 3 new wellformedness
-- predicates (one per item; `coversCapMintEvents`,
-- `wellFormedAuthorAttribution`, plus the consumption-time
-- hypothesis on `contractRegistry_origin_relay` is inline rather
-- than a named predicate per the L1+ caller-supplied semantic).
--
-- Predicted distribution (all three): T1 axiom-free × 0 / T2
-- [propext] × 3 (predicted at H1 for all three).
--
-- MEASURED distribution: T1 axiom-free × 2 / T2 [propext] × 1
-- (over-delivered on `cmap_origin_relay` and `author_origin_relay`
-- — both reduce to pure structural projection / direct
-- application of the wellformedness predicate; no `propext`-
-- requiring rewrite. `contractRegistry_origin_relay` matches
-- predicted Tier 2 [propext] via `if-then-else` case-split in
-- `registry_built_by_aux_origin`).
--
-- the over-delivery is structurally clean (mirrors
-- precedent — pure structural projection without `propext`).
--
-- ZERO Tier 4 inflation. All within v1.3-baseline tier set.
-- Carry-forward of  lesson: NO `simp`/`omega`/`simpa` (the
-- `Classical.choice` leak path); explicit `cases` /
-- `obtain` / direct-application primitives only. Confirmed
-- avoidable via direct field-projection on the wellformedness
-- predicate body.
--
-- PLAN  file-overlap discipline): single Agent CDE doing all
-- `T_cap_id_authorship_via_history`);  in `Contracts.lean`
-- `taint_authorship_relay`). The plan's  default
-- ("all in IFC.lean, single agent") was adapted at H1: Items
-- #2/#3 reference the existing `CapabilityHistory` /
-- `RegistryHistory` structures defined in `Caps.lean` /
-- `Contracts.lean` respectively, and `Caps` imports `IFC` /
-- `Contracts` imports `Caps` — placing #2/#3 in `IFC.lean`
-- per-history-file placement (the plan explicitly permits Item
-- #3 to land in `Contracts.lean`; 's history-side file
-- placement follows the same logic). The cleaner-imports
-- the cleaner-imports placement.
--
--   * `cmap_origin_relay`: STRUCTURAL relay under explicit
--     `coversCapMintEvents` L1+ TCB obligation. Substantive
--     `T_cap_id_authorship_via_history`); the L0 surface ships
--     the structural binding under the predicate.
--   * `contractRegistry_origin_relay`: STRUCTURAL PACKAGING
--     `registry_built_by_aux_origin` / `registry_origin_invariant`
--     contractId projection + ordering conjunct under explicit
--     consumption-time-stamp parameter.
--   * `author_origin_relay`: STRUCTURAL RELAY (legitimate
--     EXIT-CRITERION). Substantive content is the
--     Caveat C6 field-level drift structurally); the relay
--     packages the implication direction.
#print axioms AgentKernel.Caps.cmap_origin_relay
#print axioms AgentKernel.Contracts.contractRegistry_origin_relay
#print axioms AgentKernel.IFC.author_origin_relay

-- ============================================================
-- ============================================================
--
-- independence (Agent F = IFC.lean tail-additive; Agent G =
-- Replay.lean alphabet extension + System.lean theorem + T7 lift).
--
-- Tier predictions vs measured:
--   * `mintEventId_origin_relay`         T2 predicted, T2 measured
--   * `outLabelPayload_origin_relay`     T2 predicted, T2 measured
--   * `wellFormedTenantBinding_no_spawn_vacuous`  T1 predicted, T1 measured
--   * `tenant_binding_sound`             T1 predicted, T1 measured
--   * `t7_inherits_tenant_binding_sound` T1 predicted, T1 measured
--
--   * `mintEventId_origin_relay`: STRUCTURAL RELAY at L0.
--     `T_locus_mintEventId_correspondence`. Substantive content
--     precedent.
--   * `outLabelPayload_origin_relay`: STRUCTURAL PACKAGING at L0
--     existential projection of `kernelEmit_compose_routed`;
--     CRITICAL caveat — should NOT headline §4 of the paper.
--   * `wellFormedTenantBinding_no_spawn_vacuous`: STRUCTURAL
--     `wellFormedSpawnedBy_default_event_holds` shape; named
--     anchor for backward-compat construction-site discharge.
--   * `tenant_binding_sound`: SUBSTANTIVE close at L0 of the
--     a one-step structural projection of clause (b) of
--     `wellFormedTenantBinding`, but the LOAD-BEARING content
--     is the predicate definition's two-clause discipline that
--     forces every spawn edge to commit to either tenant-
--     forgery defense exactly. Per-tenant isolation in the kernel
--   * `t7_inherits_tenant_binding_sound`: STRUCTURAL THREADING.
--     Mirrors `t7_inherits_spawn_cap_binding_sound` shape
--     exactly; LOAD-BEARING content remains in the underlying 
--     theorem; this lift is the M8-composition citable target,
--     needed for the L0 close).
--
-- ZERO Tier 4 inflation. All within v1.3-baseline tier set.
-- Carry-forward of / lesson: NO `simp`/`omega`/`simpa`;
-- explicit `cases` / `obtain` / direct-application primitives
-- only.
--
-- PLAN ): Agent F serial on `IFC.lean` (Items #5+#6); Agent G
-- serial on `Replay.lean` + `System.lean` (). MeasureAxioms
-- updates serialized at parent (this commit).
--
-- Carry-forward residuals (α-suffixed candidates surfaced):
--     L1+ TCB on the runtime (relay carries structural back-link,
--     not temporal precedence).
--     constructor escape) remain L1+ TCB.
--     v1.5+ candidate if a future cycle wants multi-input variant.
--     `e.tenant` correctly per deployment-defined tenant
#print axioms AgentKernel.IFC.mintEventId_origin_relay
#print axioms AgentKernel.IFC.outLabelPayload_origin_relay
#print axioms AgentKernel.Replay.Event.wellFormedTenantBinding_no_spawn_vacuous
#print axioms AgentKernel.System.tenant_binding_sound
#print axioms AgentKernel.System.t7_inherits_tenant_binding_sound

-- ============================================================
--
--     through `kernelEmit_routed_at` per-event def + iff-equivalent
--     trace-level lift + EmitNonDeclassStep witness composition.
--     `Bridge/M5.InvokeStep` and `Bridge/M8.LeanStep_M8` — closes
--     honest residual at L0 type-NAMING. `_hStep` / `_LeanStep_M8`
--     undecidable in general" at L0 typed predicate-relay layer.
--     precedent); load-bearing role is the typed signature
--     obligation, not the proof.
-- ============================================================
#print axioms AgentKernel.Bridge.M4.kernelEmit_compose_routed_iff_per_event
#print axioms AgentKernel.Bridge.M4.EmitNonDeclassStep_implies_kernelEmit_routed_target
#print axioms AgentKernel.Bridge.M5.InvokeStep_admits_kernelAuthorizationStep
#print axioms AgentKernel.Bridge.M8.LeanStep_M8_invoke_admits_kernelAuthorizationStep
-- NOTE: `t8_disclosure_soundness_nontrivial`'s fully-qualified name
-- includes a doubled `AgentKernel.Disclosure.` prefix because
-- Disclosure.lean line 764 re-opens `namespace AgentKernel.Disclosure`
-- while still inside the line-93 namespace block, yielding
-- nested-namespace `AgentKernel.Disclosure.AgentKernel.Disclosure`.
-- candidate for BK batch on `main` (1-line `namespace` removal at
-- per forbidden-file discipline; use the doubled-prefix name here
-- to capture the axiom inventory honestly:
#print axioms AgentKernel.Disclosure.AgentKernel.Disclosure.t8_disclosure_soundness_nontrivial

-- ============================================================
-- `taint_kind_closure` with a kernel-supplied floor-set
-- (multi-tenant tag-policy lattice mutation defense) at L0.
-- accounting (STRUCTURAL RELAY classification); substantive
-- defense is the floor-inclusion premise (deployment-policy
-- floor non-vacuity, floor-inclusion discharge, cross-tenant
-- ============================================================
#print axioms AgentKernel.IFC.taint_kind_closure_with_kernel_floor
#print axioms AgentKernel.IFC.taint_kind_closure_floor_dominates

-- ============================================================
--
-- Common discipline: 4 new closed-alphabet `Kind` constructors
-- (`plan / exec / refusal / contractViolation`) + 4 new optional
-- side-table fields (`mode / linkedExecId / refusalReasonCode /
-- violationContractId`) added tail-additive to `Replay.Event`.
-- Each item ships:
--   * a wellFormedness predicate at Replay.lean (Event-level +
--     Trace-level lift);
--   * a structural-packaging "default-event-holds" lemma at
--     Replay.lean documenting backward-compat under defaults;
--   * 1-2 substantive named theorems at System.lean lifting the
--     predicate;
--   * 1-2 T7 inheritance lifts at System.lean SystemState layer
--
-- Predicted post-discharge tier inventory (all in baseline):
--           replay_mode_sound + t7 lift; propext via Mode-equality
--           reduction).
--           plan_exec_sound + t7 lift).
--           refusal_sound + contractViolation_sound + 2 t7 lifts).
-- TOTAL: 11 new entries; ZERO Tier 4 inflation.
-- ============================================================
#print axioms AgentKernel.Replay.Event.wellFormedReplayMode_default_event_holds
#print axioms AgentKernel.System.replay_mode_sound
#print axioms AgentKernel.System.t7_inherits_replay_mode_sound
#print axioms AgentKernel.Replay.Event.wellFormedPlanExec_default_event_holds
#print axioms AgentKernel.System.plan_exec_sound
#print axioms AgentKernel.System.t7_inherits_plan_exec_sound
#print axioms AgentKernel.Replay.Event.wellFormedRefusal_default_event_holds
#print axioms AgentKernel.System.refusal_sound
#print axioms AgentKernel.System.contractViolation_sound
#print axioms AgentKernel.System.t7_inherits_refusal_sound
#print axioms AgentKernel.System.t7_inherits_contractViolation_sound

-- ============================================================
--
-- (cumulative LoC + Repr-derivation memory ceiling), CONVERGENT
--
--   "future v1.7+ extensions should factor `Event` into a
--    head-record + extra-fields-record pair to reduce Repr-
--    derivation cost"
--
-- `humanGate` + 3 new side-table fields `failureMode /
-- humanGateContext / envDigest`) on top of v1.6 's  4-
-- constructor + 4-field expansion. The auto-derived `Repr Event`
-- elaboration cost grew super-linearly; even at maxHeartbeats =
-- 1600000 (2× ) the lean process consumed all-RAM + crashed
-- predicted ceiling event from .
--
--     does not touch Event record; +200 LoC).
--     + tail records OR drop `deriving Repr` and supply
--     manual minimal Repr to break the elaboration explosion.
--
-- See:
--
-- TOTAL  new entries: 2 (Causality.isStuck_*); ZERO Tier 4
-- inflation.
-- ============================================================

-- ============================================================
--
-- the last n events of a trace") at L0.
--
-- Surface added (Causality.lean tail-additive past v1.5/v1.4
-- close, INSIDE namespace AgentKernel.Causality block, BEFORE
-- final `end`):
--   * `kindIsProgressMarker : Replay.Kind → Bool` —
--     closed-alphabet helper classifying which `Replay.Kind`
--     constructors count as progress markers. Exhaustive on the
--     closed-alphabet discipline +  audit obligation. Progress
--     set := `{exec, externalReq, externalResp}` — agent-action
--     broadening of PLAN brief default `{exec}` justified per
--     cross-substrate cohesion with `Kind.isKernelEmit`.
--   * `Trace.isStuck (n : Nat) (t : Replay.Trace) : Prop` —
--     `∀ e ∈ t.drop (t.length - n), kindIsProgressMarker e.kind = false`.
--     Edge cases: `n = 0` vacuously true (empty observation
--     window); `n > t.length` checks all events; `t = []`
--     vacuously true (no events to witness progress).
--   * `isStuck_empty_trace (n : Nat) : Trace.isStuck n []` —
--     vacuous-discharge helper for empty traces (Tier 1
--     axiom-free via `List.drop_nil` rewrite + `cases he`).
--   * `isStuck_monotone {n n' t} (hLe : n' ≤ n)
--      (hStuck : isStuck n t) : isStuck n' t` — load-bearing
--     structural fact: stuckness propagates from larger to
--     smaller observation window. Direction reasoning: smaller
--     window is a SUFFIX of the larger window, so a fortiori
--     no progress event appears in the smaller window. The
--     OTHER direction (smaller to larger) is FALSE in general
--     (a trace stuck on its last 3 events may have made
--     progress at event 1, so widening the window from 3 to 5
--     would no longer be stuck). Tier 2 [propext] inherited
--     from `Nat.sub_le_sub_left` and `List.drop_subset_drop_left`
--     stdlib lemmas.
--
-- Predicted post-discharge tier inventory (all in baseline):
--           (Tier 1 axiom-free; over-delivered vs predicted)
--           + isStuck_monotone (Tier 2 [propext] via stdlib
--           Nat-sub + List-drop-subset).
--           Plus 2 defs (kindIsProgressMarker + Trace.isStuck)
--           which carry no axioms (definitions, not theorems).
-- TOTAL: 2 new theorem entries; ZERO Tier 4 inflation.
--
-- HONEST RESIDUALS filed at  close:
--     "progress" is L1+ deployment-policy. The L0 spec
--     classifies `{exec, externalReq, externalResp}` as a
--     structural floor; deployments may broaden/narrow per
--     their threat model.
--     deferred. The L0 predicate quantifies over a single
--     trace; multi-cell composition via `Trace.union`-style
--     machinery is L1+ runtime obligation OR future v1.7+
--     structural extension.
-- ============================================================
#print axioms AgentKernel.Causality.isStuck_empty_trace
#print axioms AgentKernel.Causality.isStuck_monotone

-- ============================================================
-- (Kind.contractRegister).
--
--   * 2 new closed-alphabet `Kind` constructors only
--     (NO new Event-record fields per parent's  pre-flight probe
--     binding: probe v1 with new field hit (deterministic) timeout
--     at isDefEq at maxHeartbeats 800000; probe v2 without new
--     field passed Replay elaboration cleanly. Field deferral
--     `registeredContractId : Option Nat` field is DEFERRED to
--
-- Each item ships:
--   * a wellFormedness predicate at Replay.lean (Event-level +
--     Trace-level lift);
--   * a structural-packaging "default-event-holds" lemma at
--     Replay.lean documenting backward-compat under defaults;
--   * 1 substantive named theorem at System.lean lifting the
--     predicate;
--   * 1 T7 inheritance lift at System.lean SystemState layer
--
--   * MultiParty.lean cap-chain integration documentation block
--     binding arm at L0 EVENT layer, sibling to Profile.humanGate
--     at L7+ SCHEMA layer).
--
--   * Contracts.lean forwarder cross-reference block (tail-additive
--     past line 2297; zero new theorems past head-2153 boundary).
--     Forwards to the ALREADY-CLOSED registry origin-integrity
--
-- Causality.lean collateral: 1-line addition to
-- `kindIsProgressMarker`'s `false` branch (`.session_bind |
-- .contractRegister`). Neither is a progress marker per the v1.6
--
-- Predicted post-discharge tier inventory (all in baseline):
--           session_bind_sound + t7 lift; pure structural
--           projection of the 2-clause predicate).
--           contract_register_sound + t7 lift; pure structural
--           projection).
-- TOTAL: 6 new entries; ZERO Tier 4 inflation.
--
-- HONEST RESIDUALS filed at  close:
--     authored session-bind events. L0 spec asserts kernel
--     authorship; the IdP-attestation receipt is L1+ Disclosure-
--     L0 predicate; multi-event session-coherence is L1+).
--     id-presence; L1+ binds `e.mintedCapId` to a registered
--     `registeredContractId : Option Nat := none` field on Event
--     DEFERRED behind the Repr-refactor prerequisite. The v1.6 
--     predicate body routes the contract-id axis through the
--     existing `e.mintedCapId` field; at v1.7+ post-refactor the
--     predicate body rewrites `e.mintedCapId` →
--     `e.registeredContractId`. The named theorem signature +
--     name remain unchanged across the rewrite (forward-
--     deferral discipline.
-- ============================================================
#print axioms AgentKernel.Replay.Event.wellFormedSessionBind_default_event_holds
#print axioms AgentKernel.System.session_bind_sound
#print axioms AgentKernel.System.t7_inherits_session_bind_sound
#print axioms AgentKernel.Replay.Event.wellFormedContractRegister_default_event_holds
#print axioms AgentKernel.System.contract_register_sound
#print axioms AgentKernel.System.t7_inherits_contract_register_sound

-- ============================================================
-- through v1.7-stable).
--
-- kind discriminator + `humanGateContext : Option HumanGateRecord
-- := none` field + `HumanGateRecord` struct + 2-clause predicate
-- pre-flight probe fired the empirical heartbeat-cost ceiling on
-- `Event`-case-analyzing theorems twice in succession (1.6M and
-- 3.2M heartbeat budgets both insufficient at +1 cumulative
-- Option-typed field beyond v1.7 ). Substrate REVERTED to v1.7
-- -close. Full  memo at the link above.
--
-- Route (c) ships:
--   * 1 new closed-alphabet `Kind` constructor (`humanGate`,
--     alphabet 20 → 21);
--   * 1-clause `Event.wellFormedHumanGate` predicate (kernel-only
--     authorship; field-presence clause DEFERRED to v1.8  /
--   * 1 Trace-level lift `Trace.wellFormedHumanGate`;
--   * 1 structural-packaging "default-event-holds" lemma at
--     Replay.lean documenting backward-compat under defaults;
--   * 1 substantive named theorem `human_gate_sound` at System.lean
--     lifting the predicate;
--   * 1 T7 inheritance lift `t7_inherits_human_gate_sound` at
--     System.lean SystemState layer.
--
-- behind Option A factor):
--   * `humanGateContext : Option HumanGateRecord := none` field
--     on `Replay.Event`.
--   * `HumanGateRecord` payload struct (`idpId : Nat` +
--     `capChainAnchor : Nat`).
--   * Clause (a) "field-presence" sub-clause of the predicate
--     (the v1.7  predicate has only the kernel-authorship
--     clause).
--
-- File-scope `set_option maxHeartbeats` STAYS at v1.7 's 1.6M
-- block past line 402 documents the three-layer sibling-not-
-- aliases relationship (Profile.humanGate L7+ SCHEMA /
-- Kind.session_bind L0 EVENT session-init arm / Kind.humanGate L0
-- EVENT mid-run-assent arm).
--
-- Causality.lean collateral: 1-line addition to
-- `kindIsProgressMarker`'s `false` branch (`.humanGate`). The mid-
-- run human-assent record is bookkeeping-only at the partition
-- layer (the assent action may unblock progress in a paired exec
-- but the humanGate event itself is non-progress).
--
-- Predicted post-discharge tier inventory (all in baseline):
--           human_gate_sound + t7 lift; pure structural projection
--           of the 1-clause predicate).
-- TOTAL: 3 new entries; ZERO Tier 4 inflation.
--
-- HONEST RESIDUALS filed at  close:
--     authored human-gate events. L0 spec asserts kernel
--     authorship; the IdP-cap-chain anchor is L1+ Disclosure-
--     human-gate-sequence semantics is L1+ kernel-runtime
--     obligation (per-event L0 predicate; multi-event coherence
--     is L1+).
--     forward-compat to v1.8+.
--     HumanGateRecord := none` field + `HumanGateRecord` payload
--     struct + clause (a) field-presence predicate DEFERRED to
--     (head+tail Event-record split) prerequisite. Closure path
--     side-table field on `Replay.Event` adds ~25-50% more `whnf`
--     / `isDefEq` cost on case-analyzing theorems
--     (`Event.parentInTrace`,
--     `Event.replayEquivWithMint_implies_replayEquiv`).
--     Records the empirical scaling for v1.8+ planning under the
--     Option A factored shape.
-- ============================================================
#print axioms AgentKernel.Replay.Event.wellFormedHumanGate_default_event_holds
#print axioms AgentKernel.System.human_gate_sound
#print axioms AgentKernel.System.t7_inherits_human_gate_sound

-- ============================================================
-- payload pivot).
--
--     PACKAGING → v1.8  PREDICATE-LOAD-BEARING). RESOLVES
--     -deferred; full payload at v1.8 ).
--
-- additive `EventPayload` arms (`humanGate` + `failureMode`) +
-- new `@[irreducible]` accessors + 2-clause well-formedness
-- predicates + soundness theorems + T7 lifts. The custom
-- `@[eliminator]` for `EventPayload` (memo § 7 intervention 2,
-- NOT REQUIRED at : the 800K legacy heartbeat budget held GREEN
-- with only the `@[irreducible]` accessor-shim discipline +
-- `precompileModules = true` from ; intervention 2 deferred to
--
--   * 1 NEW `HumanGateRecord` payload struct (Replay/Payload.lean)
--     with concrete `Nat` + `Bool` carriers per memo § 6 binding.
--     REAFFIRMED); `decisionOutcome : Bool` is L0-structural.
--   * 1 NEW `EventPayload.humanGate : HumanGateRecord →
--     EventPayload` constructor (8th in the inductive at v1.8 ;
--     strictly additive arm).
--   * 1 NEW `@[irreducible]` accessor `Event.payloadHumanGateContext
--     : Event → Option HumanGateRecord` at Replay.lean.
--   * 1 NEW Pattern (B) unfold lemma `Event.payloadHumanGateContext_unfold`
--     (the FIRST `cases payload` proof at v1.8 per α-residual
--   * 1 PROMOTED `Event.wellFormedHumanGate` predicate (v1.7 
--     1-clause → v1.8  2-clause; NAME preserved). Clause (a)
--     field-presence NEW; clause (b) kernel-only authorship
--     PRESERVED from v1.7 .
--   * 1 PROMOTED `Trace.wellFormedHumanGate` lift (NAME preserved;
--     body unchanged at the universal-quantification level).
--   * 1 PROMOTED `Event.wellFormedHumanGate_default_event_holds`
--     vacuity lemma body (1-clause `intro/absurd` → 2-clause
--     structural conjunction over false premise; NAME + STATEMENT
--     preserved).
--   * 1 PROMOTED `human_gate_sound` theorem at System.lean (NAME +
--     STATEMENT preserved verbatim; body updates from
--     `hWF e hMem hHg` to `(hWF e hMem).2 hHg` to project clause
--     (b) from the new 2-clause conjunction).
--   * 1 NEW `human_gate_field_presence_sound` clause (a) lift at
--     System.lean (substantive PREDICATE-LOAD-BEARING content).
--   * 1 PRESERVED `t7_inherits_human_gate_sound` T7 lift at
--     System.lean (body unchanged; direct apply of human_gate_sound).
--   * 1 NEW `t7_inherits_human_gate_field_presence_sound` T7 lift
--     at System.lean.
--
--   * 1 NEW closed `FailureMode` 3-variant enum at Replay/Payload.lean
--     (transient | permanent | byzantine) with auto-derived
--     `DecidableEq` + `Repr` + `Inhabited`.
--   * 1 NEW `FailureRecord` payload struct (single `mode :
--     FailureMode` field; concrete inductive-enum carrier per
--     memo § 6).
--   * 1 NEW `EventPayload.failureMode : FailureRecord →
--     EventPayload` cross-kind constructor (9th in the inductive;
--     ANY kind may carry a failure attestation per memo § 7).
--   * 1 NEW `@[irreducible]` accessor `Event.payloadFailureMode
--     : Event → Option FailureMode` at Replay.lean.
--   * 1 NEW Pattern (B) unfold lemma `Event.payloadFailureMode_unfold`.
--   * 1 NEW `Event.wellFormedFailureMode` 2-clause predicate at
--     Replay.lean. Clause (a) forgery defense (universal kernel-
--     authorship for failureMode payloads); clause (b) byzantine
--     kernel-authorship discriminator (kernelAuthored = true on
--     top of clause (a)).
--   * 1 NEW `Trace.wellFormedFailureMode` lift.
--   * 1 NEW `Event.wellFormedFailureMode_default_event_holds`
--     vacuity lemma (any event without a failureMode payload
--     trivially satisfies both clauses).
--   * 1 NEW `failure_mode_sound` clause (a) lift at System.lean
--     (PREDICATE-LOAD-BEARING content).
--   * 1 NEW `failure_mode_byzantine_kernel_authored_sound` clause
--     (b) lift at System.lean (PREDICATE-LOAD-BEARING content for
--     the byzantine subset).
--   * 1 NEW `t7_inherits_failure_mode_sound` T7 lift.
--   * 1 NEW `t7_inherits_failure_mode_byzantine_kernel_authored_sound`
--     T7 lift.
--
-- `payloadCoherent` extension (Replay.lean): 2 NEW arms added to
-- the discriminator-grid coherence floor (`Kind.humanGate ↔
-- taxonomy). The substantive PROMOTION-load-bearing arms are in
-- the per-predicate clauses (a) — payloadCoherent is the floor;
-- per-predicate clauses are the ceiling.
--
-- Predicted post-discharge tier inventory (all new theorems in
-- baseline at v1.8 ):
--           1 default-event-holds + 2 substantive lifts (clause (a)
--           + clause (b)) + 2 T7 lifts + reprints).
--           default-event-holds; 1 PRESERVED + 1 NEW substantive
--           lift; 1 PRESERVED + 1 NEW T7 lift).
-- TOTAL: 8 NEW + 4 reprinted #print invocations (2 PRESERVED
-- v1.7 theorems whose body changed — human_gate_sound +
-- wellFormedHumanGate_default_event_holds — get reprinted to
-- pick up tier-class verification; t7_inherits_human_gate_sound
-- body unchanged so its #print is mechanical).
--
-- HONEST RESIDUALS filed at  close:
--     classification.
--     discipline (3-variant cap at v1.8; v1.9+ taxonomy additions
--     require predicate updates).
--     finding: custom `@[eliminator]` for EventPayload (memo § 7
--     intervention 2; deferred from ) was NOT required at  —
--     the 800K heartbeat budget held GREEN with only the 
--     requires it.
-- ============================================================

#print axioms AgentKernel.Replay.Event.payloadHumanGateContext_unfold
#print axioms AgentKernel.System.human_gate_field_presence_sound
#print axioms AgentKernel.System.t7_inherits_human_gate_field_presence_sound

#print axioms AgentKernel.Replay.Event.payloadFailureMode_unfold
#print axioms AgentKernel.Replay.Event.wellFormedFailureMode_default_event_holds
#print axioms AgentKernel.System.failure_mode_sound
#print axioms AgentKernel.System.failure_mode_byzantine_kernel_authored_sound
#print axioms AgentKernel.System.t7_inherits_failure_mode_sound
#print axioms AgentKernel.System.t7_inherits_failure_mode_byzantine_kernel_authored_sound

-- ============================================================
-- tagged-union substrate; v1.5  / v1.6  / v1.7  -deferred).
--
-- predicate + clause (a)+clause (b) lifts + T7 lifts).
--
--   * 1 NEW `EnvDigestRecord` payload struct (Replay/Payload.lean)
--     with concrete `Nat` carrier per memo § 6 binding. `digest :
--     supplied opaque-hash representation.
--   * 1 NEW `EventPayload.envBinding : EnvDigestRecord →
--     EventPayload` cross-kind constructor (10th in the inductive
--     at v1.8 ; ANY kind may carry an env-digest attestation
--     per memo § 7).
--   * 1 NEW Repr arm on the manual minimal `Repr EventPayload`
--     instance: `| .envBinding _ => "EventPayload.envBinding⟨..⟩"`.
--   * 1 NEW `@[irreducible]` accessor `Event.payloadEnvBinding :
--     Event → Option Nat` at Replay.lean (returns `Option Nat` of
--     the digest field; sibling-shape to the kind-specific 
--     accessors rather than the  `Option HumanGateRecord` /
--     `Option FailureMode` shapes).
--   * 1 NEW Pattern (B) unfold lemma `Event.payloadEnvBinding_unfold`
--     (sibling to `payloadFailureMode_unfold`).
--   * 1 NEW arm in `Event.payloadCoherent`: cross-kind `_,
--     cross-kind failureMode arm; substantive forgery defense lives
--     in the per-predicate `wellFormedEnvBinding` clauses).
--   * 1 NEW `Event.wellFormedEnvBinding` 2-clause predicate at
--     Replay.lean. Clause (a) forgery defense (universal kernel-
--     authorship for envBinding payloads); clause (b) UNIVERSAL
--     kernelAuthored = true discriminator (no L1+ subset carve-out
--     event is universally kernel-computed over the closure context).
--   * 1 NEW `Trace.wellFormedEnvBinding` lift.
--   * 1 NEW `Event.wellFormedEnvBinding_default_event_holds`
--     vacuity lemma (any event without an envBinding payload
--     trivially satisfies both clauses).
--   * 1 NEW `env_binding_sound` clause (a) lift at System.lean
--     at v1.8 ).
--   * 1 NEW `env_binding_kernel_authored_sound` clause (b) lift at
--     System.lean (PREDICATE-LOAD-BEARING content; universal
--     kernel-authored discriminator).
--   * 1 NEW `t7_inherits_env_binding_sound` T7 lift.
--   * 1 NEW `t7_inherits_env_binding_kernel_authored_sound` T7 lift.
--
-- `payloadCoherent` extension: 1 NEW arm added to the discriminator-
-- grid coherence floor (cross-kind `_, EventPayload.envBinding _`).
--
-- Predicted post-discharge tier inventory (all new theorems in
-- baseline at v1.8 ):
--           lemma at Tier 2 [propext] (mechanical from
--           @[irreducible] match-bodied accessor) + 1 vacuity
--           default-event-holds + 2 substantive lifts (clause (a)
--           env_binding_sound + clause (b)
--           env_binding_kernel_authored_sound) + 2 T7 lifts).
-- TOTAL: 6 NEW #print invocations; ZERO Tier 4 inflation.
--
-- HONEST RESIDUALS filed at  close:
--     4 substantive-vs-redundant analysis for clause (b) at
--     substantive shape.
--     aspiration RESOLVED-VIA-SUBSTITUTION at v1.8  (env digest
--     captures closure context; subsumes tenant identity at L1+
--     runtime layer; L0 does not reason about digest content).
--     delivery via SystemEvent.tenant threading.
--     ) — custom `@[eliminator]` for EventPayload (memo § 7
--     intervention 2) STILL not required at  (the cross-kind
--     budget cleanly).
-- ============================================================

#print axioms AgentKernel.Replay.Event.payloadEnvBinding_unfold
#print axioms AgentKernel.Replay.Event.wellFormedEnvBinding_default_event_holds
#print axioms AgentKernel.System.env_binding_sound
#print axioms AgentKernel.System.env_binding_kernel_authored_sound
#print axioms AgentKernel.System.t7_inherits_env_binding_sound
#print axioms AgentKernel.System.t7_inherits_env_binding_kernel_authored_sound

-- exhaustiveness lemma (Tier 1 axiom-free, decide-shape on a
-- concrete `List Kind` of length 21):
#print axioms AgentKernel.Replay.cap_eq_21

-- DISCIPLINE-CODIFICATION sibling to `cap_eq_21`. `cases k <;> decide`
-- pattern forces compile-time pattern-exhaustivity on the `Kind`
-- inductive: adding a 22nd constructor without updating
-- `Kind.allKinds` breaks the `cases` branch coverage at proof time.
-- Tier 2 [propext] actual (post-probe; per-branch `decide` on
-- `List.Mem` routes through `instDecidableEqKind` which uses propext).
-- Tier-2 classification independent of the cap mechanism. Closes
#print axioms AgentKernel.Replay.cap_eq_21_exhaustive

-- `Trace.replayEquivAllFields` (not printed) + 2 NEW theorems both
-- predicted Tier 2 [propext]:
#print axioms AgentKernel.Replay.Event.replayEquivAllFields_implies_replayEquiv
#print axioms AgentKernel.Replay.Trace.replayEquivAllFields_implies_replayEquiv

-- Causality.Event.tenant projection-preservation theorem family.
-- lemmas per field: toReplay + toCausality; IFC.Event tenant-free
-- per Deviation A). Both predicted Tier 1 axiom-free (`rfl`).
#print axioms AgentKernel.System.SystemEvent.toReplay_preserves_tenant
#print axioms AgentKernel.System.SystemEvent.toCausality_preserves_tenant

-- lift of Layer E + the input-agreement chain + the per-position
-- entry point. 1 NEW per-event predicate `dmapCompatibleAt` (not
-- printed; `def` not theorem) + 3 NEW theorems, all predicted Tier 2
-- [propext] per the v1.3  single-policy precedent (identical proof
-- structure modulo the per-event dmap-compatibility substitution at
-- Layer E's SHARED-dmap derivation step). Closes the SECOND
#print axioms AgentKernel.IFC.LowEquiv.wellLabeledStep_R3_outLabel_prov_determined_multipolicy
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_via_R3_input_agreement_multipolicy
#print axioms AgentKernel.IFC.LowEquiv.t3_low_equivalence_from_lowInputs_multipolicy

-- rule (a)+(b) HOLD. Tail-additive in
-- `Trace.disjointEventIds` (not printed; `def` not theorem) + 1 NEW
-- composition function `Trace.union` (not printed; `def` not theorem)
-- + 2 NEW theorems, both predicted Tier 2 [propext] (substantively
-- inherits from `lowProj_append` / `List.filter_append`):
--   * `lowProj_traceUnion` — distribution lemma (LOAD-BEARING).
-- Closes A3 PARTIAL row at LOWEquiv layer; structurally packaged
-- via the IFC-event-typed `Trace.union` mirror (impedance bridge
-- to `MultiCell.Trace.union` which operates on `Replay.Event`-
-- typed traces).
-- Sub-letter ID reserved (allocated at  fold per V1.10-PLAN
-- § Context-management discipline § "Sub-letter ID allocation").
#print axioms AgentKernel.IFC.LowEquiv.lowProj_traceUnion
#print axioms AgentKernel.IFC.LowEquiv.t_multi_agent_noninterference
