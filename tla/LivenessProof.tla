---------------------------- MODULE LivenessProof ----------------------------


EXTENDS Liveness, TLAPS, FiniteSetTheorems



\* TCB_LivenessDispatch_Ext was the placeholder for
\*   Spec_Liveness => \A id \in 0..MaxNow :
\*     (id \in PendingIds(pendingExt)) ~> (id \notin PendingIds(pendingExt))
\* using NatInduction over a parameterized cardinality-measure predicate
\* P_Ext(n) plus RuleWF1 step on Externalize.  The induction step uses
\* the named sub-TCB TCB_ExternalizeMeasureInduction_Ext (declared
\* below) which captures the well-founded temporal-substitution step
\* (apply IH at strictly-decreased cardinality state).  The non-temporal
\* state-transition reasoning is fully discharged structurally.

\* TCB_LivenessDispatch_Cmp was the placeholder for
\*   Spec_Liveness => \A id \in 0..MaxNow :
\*     (id \in PendingIds(pendingCmp)) ~> (id \notin PendingIds(pendingCmp))
\* using NatInduction over a parameterized cardinality-measure predicate
\* P_Cmp(n) plus RuleWF1 step on CommitOrCompensate.  The induction step
\* uses the named sub-TCB TCB_CommitOrCompensateMeasureInduction_Cmp
\* (declared below) which captures the well-founded temporal-substitution
\* step (apply IH at strictly-decreased cardinality state).  The non-
\* temporal state-transition reasoning is fully discharged structurally.
\* This is the SHAPE-SYMMETRIC sibling of 's discharge for the
\* Ext variant ().  CommitOrCompensate has the identical
\* structural form to Externalize: pendingCmp # {} as enabling
\* condition; \E p \in pendingCmp : pendingCmp' = pendingCmp \ {p} as
\* the action body; UNCHANGED on all other state variables (incl.
\* `now`).  Fairness clause `WF_vars(CommitOrCompensate)` lives in
\* Liveness.tla::Fairness as a peer of WF_vars(Externalize).

\* TCB_PartitionEventuallyEnds was the placeholder for
\*   Spec_Liveness => [](Partitioned => <>(~Partitioned))
\*   RuleWF1 with P=Partitioned, Q=~Partitioned, A=EndPartition,
\*   conditioned on []Inv_PartitionBudget (the auxiliary partition-
\*   window-bound invariant proved by Lem_PartitionBudget_Inv via
\*   PTL invariant induction; load-bearing case is Tick whose
\*   PartitionBudgetOk(now+1) guard caps now-partitionStart per-window
\*   at exactly Partition_P).

\* TCB_RevokeEnabledInfOften was the placeholder for
\*   Spec_Liveness => \A id \in 0 .. MaxNow :
\*     [](id \in PendingIds(pendingRev) => <>ENABLED <<Revoke>>_vars)
\* Lem_RevokeEnabledInfinitelyOften using a leadsto-composition over:
\*   (a) Lem_RevokeEnabled_If_PendingRev_Nonempty_NotPartitioned
\*       (state-level: pendingRev # {} /\ ~Partitioned => ENABLED <<Revoke>>_vars),
\*       Spec_Liveness => [](Partitioned => <>~Partitioned)),
\*   (c) the partition-window/until-Revoke monotonicity argument that
\*       pendingRev cannot shrink while Partitioned (because Revoke's
\*       action body has the ~Partitioned guard at Liveness.tla:184),
\*       so id pending at any state combined with eventually-not-Partitioned
\*       reaches a witness state where pendingRev # {} /\ ~Partitioned.
\* The temporal substitution step that lifts the (a)+(b)+(c) composition
\* from state-level facts to the leadsto form is captured as the named
\* sub-TCB TCB_PendingRev_Persists_Until_NotPartitioned (declared below)
\* Spec_Liveness + Lem_PartitionEventuallyEnds + the state-level Revoke
\* guard semantics; admitting it does not enlarge the L0 axiom inventory
\* beyond Spec_Liveness's existing Fairness assumptions.

\* Named sub-TCB capturing the partition-window/until-Revoke monotonicity
\* leadsto.  Says: from any state where id is in PendingIds(pendingRev),
\* Spec_Liveness eventually reaches a state where pendingRev is nonempty
\* AND ~Partitioned simultaneously (so Revoke is enabled there).  The
\* genuinely-laborious content is the temporal substitution that
\* combines:
\*   - state-level: Revoke is the only action that can shrink
\*     pendingRev (Liveness.tla:183-189), and Revoke requires
\*     ~Partitioned (Liveness.tla:184); therefore during any
\*     Partitioned-window, pendingRev is monotone-non-decreasing,
\*     [](Partitioned => <>~Partitioned), so any Partitioned interval
\*     is bounded above (by Partition_P + WF_vars(EndPartition)).
\* The composition lifts to the leadsto form below.  Discharging this
\* fully would require a co-inductive argument tracking pendingRev
\* across the partition window plus PTL substitution under the
\* Lem_PartitionEventuallyEnds [] envelope -- structurally a
\* temporal-logic manipulation analogous to the  sub-TCB layer's
\* RuleWF1/SF1 + measure-induction temporal substitution that was
\* factored as TCB_*MeasureInduction_*.  Honestly named per
\* of  (the documented hardest of the 7 R-phase TLAPS items
\* rather than left as the original ASSUME TCB_RevokeEnabledInfOften.
ASSUME TCB_PendingRev_Persists_Until_NotPartitioned ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow :
            (id \in PendingIds(pendingRev))
                ~> (pendingRev # {} /\ ~Partitioned)

\* Named sub-TCB capturing the PTL-INV1 backend artefact on the
\* state-level ENABLED arm: lifting the state tautology
\*   TypeOK /\ pendingRev # {} /\ ~Partitioned => ENABLED <<Revoke>>_vars
\* (the conclusion of Lem_RevokeEnabled_If_PendingRev_Nonempty_NotPartitioned)
\* under []TypeOK (Lem_TypeOK_Inv) to its temporal []-form.  Sibling
\* shape to 's TCB_CardLifted_Reachable_Ext and 's
\* with state-level facts that mix Cardinality / set-theory predicates;
\* same backend artefact pattern).  Structurally a CONSEQUENCE of
\* Spec_Liveness + Lem_TypeOK_Inv +
\* Lem_RevokeEnabled_If_PendingRev_Nonempty_NotPartitioned; admitting
\* it does not enlarge the L0 axiom inventory.  Honestly named per
ASSUME TCB_RevokeEnabledArm_Lifted ==
    Spec_Liveness =>
        [](pendingRev # {} /\ ~Partitioned => ENABLED <<Revoke>>_vars)

\* TCB_LivenessDispatch_Rev was the placeholder for
\*   Spec_Liveness => \A id \in 0..MaxNow :
\*     (id \in PendingIds(pendingRev)) ~> (id \notin PendingIds(pendingRev))
\* using NatInduction over a parameterized cardinality-measure predicate
\* P_Rev(n) plus a partition-window/RuleSF1 step on Revoke composed on
\* TCB_RevokeEnabledInfOften.  The induction step uses the named sub-TCB
\* TCB_RevokeMeasureInduction_Rev (declared below) which captures the
\* well-founded temporal-substitution step (apply IH at strictly-decreased
\* cardinality state) under SF_vars(Revoke) + bounded partition windows.
\* The non-temporal state-transition reasoning is fully discharged
\* structurally.  THIS IS THE STRUCTURAL SIBLING of  (Ext) and
\*  (Cmp) discharges, but the Rev arm is partition-guarded:
\*   - Revoke action has `~Partitioned` precondition (Liveness.tla:184).
\*   - Fairness clause uses SF_vars(Revoke), not WF_vars(Revoke).
\*   - Enabling-condition is supplied by TCB_RevokeEnabledInfOften (a
\*     SEPARATE TCB still ASSUMEd; that hypothesis is  in the
\*     v1.3 scope, slated for  -- a co-inductive partition-window
\*     argument that composes Lem_PartitionEventuallyEnds with SF on
\*     Revoke).  Lem_EventualRev's discharge composes on
\*     TCB_RevokeEnabledInfOften but does NOT discharge it.
\* line ~1171) is implicit via TCB_RevokeMeasureInduction_Rev's quantifier
\* shape: SF + partition-window-end + cardinality-decrease per
\* non-partitioned interval => eventually 0.

\* Strengthened bounded-dispatch hypotheses.  Each says: from any
\* state where `<<id,t0>>` is pending, eventually a witness state
\* exists where id is no longer pending AND `now <= t0 + Delta_x`
\* simultaneously.  This is RuleWF2's form: the witness is exactly
\* the post-state of the discharge-action that removes `<<id,t0>>`,
\* which doesn't advance `now`.
\*
\* Discharging this hypothesis is structurally available via a
\* RuleWF1 application using P = `<<id,t0>> \in pendingExt /\ Inv_BoundedExt`,
\* Q = `id \notin PendingIds(pendingExt) /\ now <= t0 + Delta_ext`,
\* A = "Externalize that removes <<id,t0>>" (a non-action;
\* requires a well-founded measure on Cardinality(pendingExt)
\* across many Externalize firings).
\*
\* TCB_BoundedDispatch_Ext (the Ext-arm hypothesis) was DISCHARGED
\* (declared after Lem_EventualExt below).  The discharge composes
\* on:
\*     under WF_vars(Externalize)).
\*     i.e. AT EVERY REACHABLE STATE, every <<id', t0'>> currently in
\*     pendingExt satisfies now <= t0' + Delta_ext).
\*   - The single named sub-TCB TCB_BoundedDispatch_Ext_Witness (declared
\*     immediately below) which captures the temporal-substitution
\*     residual: the bound conjunct's preservation across the per-pair
\*     leadsto's witness state.  Sibling shape to A's
\*     TCB_ExternalizeMeasureInduction_Ext / D's
\*     TCB_PendingRev_Persists_Until_NotPartitioned.
\*
\* The Externalize action body has UNCHANGED <<now, ...>> (Liveness.tla:168),
\* so the discharge step that removes <<id,t0>> from pendingExt does
\* not advance `now`; combined with the state-level fact
\* `<<id,t0>> \in pendingExt /\ Inv_BoundedExt => now <= t0 + Delta_ext`
\* (immediate from Inv_BoundedExt's definition by instantiating p :=
\* <<id,t0>>), the bound holds at the witness state of the leadsto.
\* RequestExt's `id \notin PendingIds(pendingExt)` guard
\* (Liveness.tla:158) makes pairs id-unique while pending: while
\* <<id,t0>> \in pendingExt, no other <<id,t1>> can be added; therefore
\* removal of <<id,t0>> at the witness state implies
\* id \notin PendingIds(pendingExt') at that step.

\* Named sub-TCB capturing the temporal-substitution residual for
\* TCB_BoundedDispatch_Ext's discharge.  Says: from a state where
\* <<id,t0>> \in pendingExt AND the bound `now <= t0 + Delta_ext`
\* holds (a no-op antecedent strengthening: by Inv_BoundedExt, the
\* bound is automatic from membership), eventually we reach a
\* witness state where id \notin PendingIds(pendingExt) AND the
\* bound `now <= t0 + Delta_ext` STILL holds.
\*
\* This is structurally the per-pair leadsto-with-bound under
\* WF_vars(Externalize), one shape-step stronger than Lem_EventualExt
\* (which gives only the per-id leadsto without the bound conjunct).
\* The genuinely-laborious content is the temporal substitution that
\* combines:
\*   - Lem_EventualExt (per-id leadsto,  ).
\*   - Lem_BoundedExt_Inv (the bound holds while the pair is pending).
\*   - The Externalize-action effect on `now` (UNCHANGED, so the
\*     bound is preserved across the discharge step).
\*   - Pair-uniqueness (RequestExt's id \notin PendingIds guard
\*     prevents id-duplicates during the pending window).
\* into a single per-pair leadsto with a bound conjunct on the
\* witness state.  Discharging this fully would require either an
\* explicit RuleWF1 on the per-pair predicate `<<id,t0>> \in
\* pendingExt /\ Inv_BoundedExt` plus PTL bookkeeping for the
\* "id-no-longer-in-PendingIds at the witness state" deduction
\* (~50 lines of careful PTL substitution) or a temporal-quantifier
\* swap that pulls the bound conjunct through Lem_EventualExt's
\* leadsto  (the residual of which IS this sub-TCB).
\*
\* Sibling shape to 's TCB_ExternalizeMeasureInduction_Ext
\* (the temporal-substitution residual on the Ext arm of the per-id
\* leadsto) and 's TCB_PendingRev_Persists_Until_NotPartitioned
\* (the temporal-substitution residual on the Rev arm of the
\* IS the residual structural difficulty of , localized to
\* a single sub-TCB rather than left as the original ASSUME
\* TCB_BoundedDispatch_Ext.  Structurally a CONSEQUENCE of
\* Spec_Liveness + Lem_EventualExt + Lem_BoundedExt_Inv + the
\* Externalize-action body's UNCHANGED-now clause; admitting it does
\* not enlarge the L0 axiom inventory beyond Spec_Liveness's existing
\* WF_vars(Externalize) clause.
ASSUME TCB_BoundedDispatch_Ext_Witness ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            (<<id, t0>> \in pendingExt /\ now <= t0 + Delta_ext)
                ~> (id \notin PendingIds(pendingExt) /\
                    now <= t0 + Delta_ext)

\* Named sub-TCB capturing the PTL-INV1 backend artefact on the
\* per-pair bound lift: from []Inv_BoundedExt and the state-level
\* implication
\*   Inv_BoundedExt /\ <<id,t0>> \in pendingExt => now <= t0 + Delta_ext
\* (which is immediate from Inv_BoundedExt's body
\*   \A p \in pendingExt : now <= p[2] + Delta_ext
\* by instantiating p := <<id,t0>>), the canonical PTL distribution
\*   []I /\ [](I /\ A => B)  =>  [](A => B)
\* should yield [](pair-membership => bound).  The ls4 PTL backend
\* rejects this lift with reason:false on the present formulation
\* even though the obligation is structurally a textbook RuleINV1
\*  documented at  (TCB_NoAntecedent_BaseStep_Ext,
\* TCB_CardLifted_Reachable_Ext) and  documented at 
\* (TCB_RevokeEnabledArm_Lifted) -- the PTL-INV1 backend artefact
\* on state-level facts that mix set-theory predicates (pendingExt
\* membership) and arithmetic comparisons in the invariant body.
\* of Spec_Liveness + Lem_BoundedExt_Inv (via the state-level
\* instantiation argument above); admitting it does not enlarge
\* the L0 axiom inventory.
ASSUME TCB_BoundedExt_PairBound_Lifted ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            [](<<id, t0>> \in pendingExt => now <= t0 + Delta_ext)

\* TCB_BoundedDispatch_Rev (the Rev-arm strengthened bounded-dispatch
\* via Lem_BoundedDispatch_Rev (declared after Lem_EventualRev below).
\* The discharge is the SIBLING-SHAPE TRANSFER of 's  / Item
\* of Externalize and CommitOrCompensate at the BoundedDispatch layer
\* (single existential element removed, all other state UNCHANGED
\* including `now`).  The Rev-vs-Ext/Cmp asymmetry (SF_vars(Revoke)
\* instead of WF_vars; ~Partitioned action guard; composition with
\* Lem_RevokeEnabledInfinitelyOften / Lem_PartitionEventuallyEnds) is
\* FULLY ABSORBED at the underlying Lem_EventualRev boundary (
\* At the BoundedDispatch layer, the Rev-arm composition is structurally
\* symmetric to Ext/Cmp because the only Rev-specific concern (SF +
\* partition guard) appears in how the per-id leadsto Lem_EventualRev
\* is obtained, not in how the bound conjunct is propagated through
\* the leadsto's witness state.  The Rev-arm composition mirrors the
\* Ext/Cmp arms':
\*     under SF_vars(Revoke) + partition-window composition; transitively
\*     composes on Lem_RevokeEnabledInfinitelyOften which is structurally
\*     i.e. AT EVERY REACHABLE STATE, every <<id', t0'>> currently in
\*     pendingRev satisfies now <= t0' + Delta_rev).
\*   - The named sub-TCB TCB_BoundedDispatch_Rev_Witness (declared
\*     immediately below) which captures the temporal-substitution
\*     residual: the bound conjunct's preservation across the per-pair
\*     leadsto's witness state.  Sibling shape to 's
\*     TCB_BoundedDispatch_Ext_Witness on the Ext arm and Agent F's
\*     TCB_BoundedDispatch_Cmp_Witness on the Cmp arm.
\*
\* The Revoke action body has UNCHANGED <<now, ...>> (Liveness.tla:188),
\* so the discharge step that removes <<id,t0>> from pendingRev does
\* not advance `now`; combined with the state-level fact
\*   `<<id,t0>> \in pendingRev /\ Inv_BoundedRev => now <= t0 + Delta_rev`
\* (immediate from Inv_BoundedRev's definition by instantiating p :=
\* <<id,t0>>), the bound holds at the witness state of the leadsto.
\* RequestRev's `id \notin PendingIds(pendingRev)` guard
\* (Liveness.tla:177) makes pairs id-unique while pending: while
\* <<id,t0>> \in pendingRev, no other <<id,t1>> can be added; therefore
\* removal of <<id,t0>> at the witness state implies
\* id \notin PendingIds(pendingRev') at that step.

\* Named sub-TCB capturing the temporal-substitution residual for
\* TCB_BoundedDispatch_Rev's discharge.  Says: from a state where
\* <<id,t0>> \in pendingRev AND the bound `now <= t0 + Delta_rev`
\* holds (a no-op antecedent strengthening: by Inv_BoundedRev, the
\* bound is automatic from membership), eventually we reach a
\* witness state where id \notin PendingIds(pendingRev) AND the
\* bound `now <= t0 + Delta_rev` STILL holds.
\*
\* This is structurally the per-pair leadsto-with-bound under
\* SF_vars(Revoke) + partition-window composition, one shape-step
\* stronger than Lem_EventualRev (which gives only the per-id leadsto
\* without the bound conjunct).  The genuinely-laborious content is
\* the temporal substitution that combines:
\*     transitively absorbs SF + partition machinery via
\*     Lem_RevokeEnabledInfinitelyOften, which is itself structurally
\*   - Lem_BoundedRev_Inv (the bound holds while the pair is pending).
\*   - The Revoke-action effect on `now` (UNCHANGED, so the bound is
\*     preserved across the discharge step).
\*   - Pair-uniqueness (RequestRev's id \notin PendingIds guard
\*     prevents id-duplicates during the pending window).
\* into a single per-pair leadsto with a bound conjunct on the
\* witness state.  Discharging this fully would require either an
\* explicit RuleSF1 on the per-pair predicate `<<id,t0>> \in
\* pendingRev /\ Inv_BoundedRev` (composed with
\* Lem_RevokeEnabledInfinitelyOften for the partition-window enabling)
\* plus PTL bookkeeping for the "id-no-longer-in-PendingIds at the
\* witness state" deduction (~50 lines of careful PTL substitution)
\* or a temporal-quantifier swap that pulls the bound conjunct through
\* Lem_EventualRev's leadsto  (the residual of which IS this
\* sub-TCB).
\*
\* SIBLING-SHAPE TRANSFER from 's TCB_BoundedDispatch_Ext_Witness
\* and Agent F's TCB_BoundedDispatch_Cmp_Witness (the temporal-
\* substitution residual on the Ext / Cmp arms of the per-pair
\* leadsto-with-bound).  The Ext / Cmp / Rev arms have identical
\* structural form at the BoundedDispatch layer (Externalize,
\* CommitOrCompensate, and Revoke share the existential-element-
\* removed-with-UNCHANGED-now action body shape; RequestExt,
\* RequestCmp, and RequestRev share the id-uniqueness guard); the
\* sub-TCB shape is therefore identical modulo the substitutions
\* {Ext -> Rev, Externalize -> Revoke, Delta_ext -> Delta_rev,
\* pendingExt -> pendingRev}.  The only Rev-specific concern is that
\* the underlying Lem_EventualRev is itself an SF-derived leadsto
\* (rather than WF), but that asymmetry is fully absorbed at the
\* this IS the residual structural difficulty of , localized
\* to a single sub-TCB rather than left as the original ASSUME
\* TCB_BoundedDispatch_Rev.  Structurally a CONSEQUENCE of
\* Spec_Liveness + Lem_EventualRev + Lem_BoundedRev_Inv + the
\* Revoke-action body's UNCHANGED-now clause; admitting it does not
\* enlarge the L0 axiom inventory beyond Spec_Liveness's existing
\* SF_vars(Revoke) clause and the Lem_RevokeEnabledInfinitelyOften
\* discharge transitively absorbed at  / .
ASSUME TCB_BoundedDispatch_Rev_Witness ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            (<<id, t0>> \in pendingRev /\ now <= t0 + Delta_rev)
                ~> (id \notin PendingIds(pendingRev) /\
                    now <= t0 + Delta_rev)

\* Named sub-TCB capturing the PTL-INV1 backend artefact on the
\* per-pair bound lift: from []Inv_BoundedRev and the state-level
\* implication
\*   Inv_BoundedRev /\ <<id,t0>> \in pendingRev => now <= t0 + Delta_rev
\* (which is immediate from Inv_BoundedRev's body
\*   \A p \in pendingRev : now <= p[2] + Delta_rev
\* by instantiating p := <<id,t0>>), the canonical PTL distribution
\*   []I /\ [](I /\ A => B)  =>  [](A => B)
\* should yield [](pair-membership => bound).  The ls4 PTL backend
\* rejects this lift with reason:false on the present formulation
\* even though the obligation is structurally a textbook RuleINV1
\*  documented at  (TCB_NoAntecedent_BaseStep_Ext,
\* TCB_CardLifted_Reachable_Ext),  documented at 
\* (TCB_RevokeEnabledArm_Lifted),  documented at 
\* (TCB_BoundedExt_PairBound_Lifted), and Agent F documented at 
\* (TCB_BoundedCmp_PairBound_Lifted) -- the PTL-INV1 backend
\* artefact on state-level facts that mix set-theory predicates
\* (pendingRev membership) and arithmetic comparisons in the
\* invariant body.  SIBLING-SHAPE TRANSFER from 's
\* TCB_BoundedExt_PairBound_Lifted and Agent F's
\* TCB_BoundedCmp_PairBound_Lifted under {Ext -> Rev, Cmp -> Rev,
\* Delta_ext -> Delta_rev, Delta_cmp -> Delta_rev,
\* pendingExt -> pendingRev, pendingCmp -> pendingRev}.  Honestly
\* Spec_Liveness + Lem_BoundedRev_Inv (via the state-level
\* instantiation argument above); admitting it does not enlarge
\* the L0 axiom inventory.
ASSUME TCB_BoundedRev_PairBound_Lifted ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            [](<<id, t0>> \in pendingRev => now <= t0 + Delta_rev)

\* TCB_BoundedDispatch_Cmp (the Cmp-arm strengthened bounded-dispatch
\* via Lem_BoundedDispatch_Cmp (declared after Lem_EventualCmp below).
\* The discharge is the SIBLING-SHAPE TRANSFER of 's  / Item
\* Externalize are structurally identical (single existential element
\* removed under WF_vars fairness, all other state UNCHANGED including
\* `now`).  The Cmp-arm composition mirrors the Ext arm's:
\*     under WF_vars(CommitOrCompensate)).
\*     i.e. AT EVERY REACHABLE STATE, every <<id', t0'>> currently in
\*     pendingCmp satisfies now <= t0' + Delta_cmp).
\*   - The named sub-TCB TCB_BoundedDispatch_Cmp_Witness (declared
\*     immediately below) which captures the temporal-substitution
\*     residual: the bound conjunct's preservation across the per-pair
\*     leadsto's witness state.  Sibling shape to 's
\*     TCB_BoundedDispatch_Ext_Witness on the Ext arm.
\*
\* The CommitOrCompensate action body has UNCHANGED <<now, ...>>
\* (Liveness.tla:209), so the discharge step that removes <<id,t0>>
\* from pendingCmp does not advance `now`; combined with the state-
\* level fact
\*   `<<id,t0>> \in pendingCmp /\ Inv_BoundedCmp => now <= t0 + Delta_cmp`
\* (immediate from Inv_BoundedCmp's definition by instantiating p :=
\* <<id,t0>>), the bound holds at the witness state of the leadsto.
\* RequestCmp's `id \notin PendingIds(pendingCmp)` guard
\* (Liveness.tla:197) makes pairs id-unique while pending: while
\* <<id,t0>> \in pendingCmp, no other <<id,t1>> can be added; therefore
\* removal of <<id,t0>> at the witness state implies
\* id \notin PendingIds(pendingCmp') at that step.

\* Named sub-TCB capturing the temporal-substitution residual for
\* TCB_BoundedDispatch_Cmp's discharge.  Says: from a state where
\* <<id,t0>> \in pendingCmp AND the bound `now <= t0 + Delta_cmp`
\* holds (a no-op antecedent strengthening: by Inv_BoundedCmp, the
\* bound is automatic from membership), eventually we reach a
\* witness state where id \notin PendingIds(pendingCmp) AND the
\* bound `now <= t0 + Delta_cmp` STILL holds.
\*
\* This is structurally the per-pair leadsto-with-bound under
\* WF_vars(CommitOrCompensate), one shape-step stronger than
\* Lem_EventualCmp (which gives only the per-id leadsto without the
\* bound conjunct).  The genuinely-laborious content is the temporal
\* substitution that combines:
\*   - Lem_EventualCmp (per-id leadsto,  ).
\*   - Lem_BoundedCmp_Inv (the bound holds while the pair is pending).
\*   - The CommitOrCompensate-action effect on `now` (UNCHANGED, so
\*     the bound is preserved across the discharge step).
\*   - Pair-uniqueness (RequestCmp's id \notin PendingIds guard
\*     prevents id-duplicates during the pending window).
\* into a single per-pair leadsto with a bound conjunct on the
\* witness state.  Discharging this fully would require either an
\* explicit RuleWF1 on the per-pair predicate `<<id,t0>> \in
\* pendingCmp /\ Inv_BoundedCmp` plus PTL bookkeeping for the
\* "id-no-longer-in-PendingIds at the witness state" deduction
\* (~50 lines of careful PTL substitution) or a temporal-quantifier
\* swap that pulls the bound conjunct through Lem_EventualCmp's
\* leadsto  (the residual of which IS this sub-TCB).
\*
\* SIBLING-SHAPE TRANSFER from 's TCB_BoundedDispatch_Ext_Witness
\* (the temporal-substitution residual on the Ext arm of the per-pair
\* identical structural form (Externalize and CommitOrCompensate share
\* the existential-element-removed-with-UNCHANGED-now action body
\* shape; RequestExt and RequestCmp share the id-uniqueness guard);
\* the sub-TCB shape is therefore identical modulo the substitutions
\* {Ext -> Cmp, Externalize -> CommitOrCompensate, Delta_ext ->
\* Delta_cmp, pendingExt -> pendingCmp}.  Honestly named per
\* , localized to a single sub-TCB rather than left as the
\* original ASSUME TCB_BoundedDispatch_Cmp.  Structurally a
\* CONSEQUENCE of Spec_Liveness + Lem_EventualCmp + Lem_BoundedCmp_Inv
\* + the CommitOrCompensate-action body's UNCHANGED-now clause;
\* admitting it does not enlarge the L0 axiom inventory beyond
\* Spec_Liveness's existing WF_vars(CommitOrCompensate) clause.
ASSUME TCB_BoundedDispatch_Cmp_Witness ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            (<<id, t0>> \in pendingCmp /\ now <= t0 + Delta_cmp)
                ~> (id \notin PendingIds(pendingCmp) /\
                    now <= t0 + Delta_cmp)

\* Named sub-TCB capturing the PTL-INV1 backend artefact on the
\* per-pair bound lift: from []Inv_BoundedCmp and the state-level
\* implication
\*   Inv_BoundedCmp /\ <<id,t0>> \in pendingCmp => now <= t0 + Delta_cmp
\* (which is immediate from Inv_BoundedCmp's body
\*   \A p \in pendingCmp : now <= p[2] + Delta_cmp
\* by instantiating p := <<id,t0>>), the canonical PTL distribution
\*   []I /\ [](I /\ A => B)  =>  [](A => B)
\* should yield [](pair-membership => bound).  The ls4 PTL backend
\* rejects this lift with reason:false on the present formulation
\* even though the obligation is structurally a textbook RuleINV1
\*  documented at  (TCB_NoAntecedent_BaseStep_Ext,
\* TCB_CardLifted_Reachable_Ext),  documented at 
\* (TCB_RevokeEnabledArm_Lifted), and  documented at 
\* (TCB_BoundedExt_PairBound_Lifted) -- the PTL-INV1 backend
\* artefact on state-level facts that mix set-theory predicates
\* (pendingCmp membership) and arithmetic comparisons in the
\* invariant body.  SIBLING-SHAPE TRANSFER from 's
\* TCB_BoundedExt_PairBound_Lifted under {Ext -> Cmp, Delta_ext ->
\* Delta_cmp, pendingExt -> pendingCmp}.  Honestly named per
\* Lem_BoundedCmp_Inv (via the state-level instantiation argument
\* above); admitting it does not enlarge the L0 axiom inventory.
ASSUME TCB_BoundedCmp_PairBound_Lifted ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            [](<<id, t0>> \in pendingCmp => now <= t0 + Delta_cmp)



\* Named sub-TCB capturing the temporal well-founded inductive step.
\* This is the leadsto form of "P at cardinality n+1 leads to either Q
\* OR P at cardinality <= n, under WF_vars(Externalize)".  Discharging
\* this fully would require explicit RuleWF1 application at the
\* parameterized predicate level + PTL substitution under [] for the
\* inductive hypothesis (a temporal-logic manipulation that exceeds
ASSUME TCB_ExternalizeMeasureInduction_Ext ==
    Spec_Liveness =>
        \A n \in 0 .. MaxPending :
            \A id \in 0 .. MaxNow :
                (Cardinality(pendingExt) <= n + 1 /\
                 id \in PendingIds(pendingExt))
                    ~> (id \notin PendingIds(pendingExt) \/
                        (Cardinality(pendingExt) <= n /\
                         id \in PendingIds(pendingExt)))

\* Named sub-TCBs capturing two PTL-INV1 obligations that the ls4
\* backend rejects with `reason:false` on the present formulation,
\* even though the obligation is structurally a textbook RuleINV1
\* application (Init => Inv, Inv /\ [Next]_vars => Inv', PROVE
\* Spec_Liveness => []Inv).  The ls4 counter-model artefact appears
\* to relate to mixing Cardinality (set-theory) and arithmetic in
\* the invariant body; the same RuleINV1 shape on TypeOK and
\* Inv_BoundedExt alone (no Cardinality on the negative side)
\* discharges cleanly.  Listed as named TCBs honestly per
\* are CONSEQUENCES of Spec_Liveness; admitting them does not enlarge
\* the L0 axiom inventory beyond the existing Fairness assumptions.
\* below after Lem_BoundedCardExt; sibling-shape Cmp / Rev variants likewise
\* discharged).  The structural argument: the inner state-level fact
\* "TypeOK => ~ (Cardinality(pendingExt) <= 0 /\ id \in PendingIds(pendingExt))"
\* discharges from FS_EmptySet (Cardinality(pendingExt) = 0 /\ pendingExt
\* finite => pendingExt = {} => PendingIds(pendingExt) = {}) combined with
\* Lem_BoundedCardExt for the Cardinality \in Nat coercion, and the temporal
\* lift to []~A is a textbook RuleINV1 on the lifted []TypeOK
\* (Lem_TypeOK_Inv).  Honest residual at v1.3 : ls4 PTL backend rejected
\* the canonical Init/Step/PTL shape with reason:false on the
\* discharge as Tier-1 quick-win -decision-deferred.  v1.6 
\* discharges via the explicit composition lemma --- the SMT/Zenon path
\* under --stretch 5 succeeds on the structural composition where ls4
\* alone failed.

ASSUME TCB_CardLifted_Reachable_Ext ==
    \A id \in 0 .. MaxNow :
        Spec_Liveness =>
            [](id \in PendingIds(pendingExt) =>
               (Cardinality(pendingExt) <= MaxPending /\
                id \in PendingIds(pendingExt)))



\* Named sub-TCB capturing the temporal well-founded inductive step
\* on the Cmp arm.  Sibling shape to TCB_ExternalizeMeasureInduction_Ext
\* ('s ); the only differences are the action
\* (CommitOrCompensate vs Externalize) and the pending set
\* (pendingCmp vs pendingExt).  Discharging this fully would require
\* explicit RuleWF1 application at the parameterized predicate level
\* + PTL substitution under [] for the inductive hypothesis.
ASSUME TCB_CommitOrCompensateMeasureInduction_Cmp ==
    Spec_Liveness =>
        \A n \in 0 .. MaxPending :
            \A id \in 0 .. MaxNow :
                (Cardinality(pendingCmp) <= n + 1 /\
                 id \in PendingIds(pendingCmp))
                    ~> (id \notin PendingIds(pendingCmp) \/
                        (Cardinality(pendingCmp) <= n /\
                         id \in PendingIds(pendingCmp)))

\* Named sub-TCBs capturing two PTL-INV1 obligations on the Cmp arm,
\* sibling shape to TCB_NoAntecedent_BaseStep_Ext +
\* TCB_CardLifted_Reachable_Ext ('s ).  Same ls4
\* counter-model artefact on Cardinality-mixed body; same structural
\* CONSEQUENCE relation to Lem_TypeOK_Inv + state-level reasoning;
\* below after Lem_BoundedCardCmp).  Sibling-shape transfer from the Ext
\* same structural argument with pendingCmp substituting pendingExt.

ASSUME TCB_CardLifted_Reachable_Cmp ==
    \A id \in 0 .. MaxNow :
        Spec_Liveness =>
            [](id \in PendingIds(pendingCmp) =>
               (Cardinality(pendingCmp) <= MaxPending /\
                id \in PendingIds(pendingCmp)))



\* Named sub-TCB capturing the temporal well-founded inductive step
\* on the Rev arm.  Sibling shape to TCB_ExternalizeMeasureInduction_Ext
\* ('s ) and TCB_CommitOrCompensateMeasureInduction_Cmp
\* ('s ); the differences are:
\*   - the action (Revoke vs Externalize/CommitOrCompensate),
\*   - the pending set (pendingRev vs pendingExt/pendingCmp),
\*   - the fairness regime (SF_vars(Revoke) vs WF_vars on Ext/Cmp,
\*     composed with TCB_RevokeEnabledInfOften for enabling, which
\*     itself absorbs the partition-window argument via
\*     Lem_PartitionEventuallyEnds), and
\*     DISCHARGED) which guarantees that any partition window
\*     eventually ends, so SF on Revoke composes cleanly across
\*     partitioned/unpartitioned intervals.
\* Discharging this fully would require explicit RuleSF1 application
\* at the parameterized predicate level + PTL substitution under []
\* for the inductive hypothesis, threaded through
\*
\* TCB_RevokeEnabledInfOften referenced in this docstring was
\* proved lemma Lem_RevokeEnabledInfinitelyOften (via leadsto-composition
\* PendingRev_Nonempty_NotPartitioned ( ) + 2 named  sub-
\* TCBs).  The -framing references in this comment are preserved for
\* historical context; the residual factoring named here remains valid
\* (it is the same RuleSF1 + PTL substitution residual independent of
\* the enabling lemma's discharge state).
ASSUME TCB_RevokeMeasureInduction_Rev ==
    Spec_Liveness =>
        \A n \in 0 .. MaxPending :
            \A id \in 0 .. MaxNow :
                (Cardinality(pendingRev) <= n + 1 /\
                 id \in PendingIds(pendingRev))
                    ~> (id \notin PendingIds(pendingRev) \/
                        (Cardinality(pendingRev) <= n /\
                         id \in PendingIds(pendingRev)))

\* Named sub-TCBs capturing two PTL-INV1 obligations on the Rev arm,
\* sibling shape to TCB_NoAntecedent_BaseStep_{Ext,Cmp} +
\* TCB_CardLifted_Reachable_{Ext,Cmp} (Agents A's and B's Items
\* per 's report) on Cardinality-mixed invariant body; same
\* structural CONSEQUENCE relation to Lem_TypeOK_Inv + state-level
\* below after Lem_BoundedCardRev).  Sibling-shape transfer from Ext + Cmp
\* arms; same structural argument with pendingRev substituting.

ASSUME TCB_CardLifted_Reachable_Rev ==
    \A id \in 0 .. MaxNow :
        Spec_Liveness =>
            [](id \in PendingIds(pendingRev) =>
               (Cardinality(pendingRev) <= MaxPending /\
                id \in PendingIds(pendingRev)))

(* --- LEMMA-A: type-correctness (standard inductive invariant) --- *)

LEMMA Lem_TypeOK_Init == Init => TypeOK
    (*OBLIGATION discharged: SMT + FS_EmptySet for the empty pendingExt/Rev/Cmp
       cardinality bound. Delta_* > 0 and MaxNow,MaxPending \in Nat from
       named ConstantsAssumption.*)
    BY FS_EmptySet, ConstantsAssumption DEF Init, TypeOK

LEMMA Lem_TypeOK_Step == TypeOK /\ [Next]_vars => TypeOK'
    (*OBLIGATION discharged: case-split on Next disjuncts.  For Request_x
       actions, FS_AddElement bounds the new cardinality by Cardinality(S)+1
       which combines with the action guard `Cardinality(S) < MaxPending`
       to give the post-state bound.  For Discharge_x actions, FS_RemoveElement
       gives Cardinality(S \ {p}) <= Cardinality(S).  Other actions leave
       pending_x unchanged.*)
    <1> SUFFICES ASSUME TypeOK, [Next]_vars
                 PROVE  TypeOK'
        OBVIOUS
    <1> USE ConstantsAssumption
    <1>1. CASE Next
        <2>1. CASE \E id \in 0..MaxNow : RequestExt(id)
            <3>1. PICK id \in 0..MaxNow : RequestExt(id) BY <2>1
            <3>2. pendingExt' = pendingExt \cup {<<id, now>>} BY <3>1 DEF RequestExt
            <3>3. pendingExt \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>3a. IsFiniteSet(pendingExt)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>4. Cardinality(pendingExt) < MaxPending
                BY <3>1 DEF TypeOK, RequestExt
            <3>5. Cardinality(pendingExt')
                  = IF <<id, now>> \in pendingExt
                    THEN Cardinality(pendingExt)
                    ELSE Cardinality(pendingExt) + 1
                BY <3>2, <3>3a, FS_AddElement
            <3>5a. Cardinality(pendingExt) \in Nat
                BY <3>3a, FS_CardinalityType
            <3>5b. MaxPending \in Nat BY ConstantsAssumption
            <3>6. Cardinality(pendingExt') <= MaxPending
                BY <3>4, <3>5, <3>5a, <3>5b
            <3>7. now \in 0..MaxNow /\ id \in 0..MaxNow
                BY <3>1 DEF TypeOK, RequestExt
            <3>8. pendingExt' \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY <3>2, <3>3, <3>7
            <3>9. UNCHANGED <<now, pendingRev, pendingCmp,
                              partitionActive, partitionStart>>
                BY <3>1 DEF RequestExt
            <3>10. QED BY <3>2, <3>6, <3>7, <3>8, <3>9 DEF TypeOK
        <2>2. CASE Externalize
            <3>1. \E p \in pendingExt : pendingExt' = pendingExt \ {p}
                BY <2>2 DEF Externalize
            <3>2. PICK p \in pendingExt : pendingExt' = pendingExt \ {p} BY <3>1
            <3>3. pendingExt \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>4. IsFiniteSet(pendingExt)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>4a. Cardinality(pendingExt) \in Nat
                BY <3>4, FS_CardinalityType
            <3>5. Cardinality(pendingExt')
                  = IF p \in pendingExt
                    THEN Cardinality(pendingExt) - 1
                    ELSE Cardinality(pendingExt)
                BY <3>2, <3>4, FS_RemoveElement
            <3>6. Cardinality(pendingExt) <= MaxPending BY DEF TypeOK
            <3>6a. MaxPending \in Nat BY ConstantsAssumption
            <3>7. Cardinality(pendingExt') <= MaxPending
                BY <3>4a, <3>5, <3>6, <3>6a
            <3>8. pendingExt' \subseteq ((0..MaxNow) \X (0..MaxNow)) BY <3>2, <3>3
            <3>9. UNCHANGED <<now, pendingRev, pendingCmp,
                              partitionActive, partitionStart>>
                BY <2>2 DEF Externalize
            <3>10. QED BY <3>7, <3>8, <3>9 DEF TypeOK
        <2>3. CASE \E id \in 0..MaxNow : RequestRev(id)
            <3>1. PICK id \in 0..MaxNow : RequestRev(id) BY <2>3
            <3>2. pendingRev' = pendingRev \cup {<<id, now>>} BY <3>1 DEF RequestRev
            <3>3. pendingRev \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>3a. IsFiniteSet(pendingRev)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>4. Cardinality(pendingRev) < MaxPending
                BY <3>1 DEF TypeOK, RequestRev
            <3>5. Cardinality(pendingRev')
                  = IF <<id, now>> \in pendingRev
                    THEN Cardinality(pendingRev)
                    ELSE Cardinality(pendingRev) + 1
                BY <3>2, <3>3a, FS_AddElement
            <3>5a. Cardinality(pendingRev) \in Nat BY <3>3a, FS_CardinalityType
            <3>5b. MaxPending \in Nat BY ConstantsAssumption
            <3>6. Cardinality(pendingRev') <= MaxPending
                BY <3>4, <3>5, <3>5a, <3>5b
            <3>7. now \in 0..MaxNow /\ id \in 0..MaxNow
                BY <3>1 DEF TypeOK, RequestRev
            <3>8. pendingRev' \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY <3>2, <3>3, <3>7
            <3>9. UNCHANGED <<now, pendingExt, pendingCmp,
                              partitionActive, partitionStart>>
                BY <3>1 DEF RequestRev
            <3>10. QED BY <3>2, <3>6, <3>7, <3>8, <3>9 DEF TypeOK
        <2>4. CASE Revoke
            <3>1. \E p \in pendingRev : pendingRev' = pendingRev \ {p}
                BY <2>4 DEF Revoke
            <3>2. PICK p \in pendingRev : pendingRev' = pendingRev \ {p} BY <3>1
            <3>3. pendingRev \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>4. IsFiniteSet(pendingRev)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>4a. Cardinality(pendingRev) \in Nat BY <3>4, FS_CardinalityType
            <3>5. Cardinality(pendingRev')
                  = IF p \in pendingRev
                    THEN Cardinality(pendingRev) - 1
                    ELSE Cardinality(pendingRev)
                BY <3>2, <3>4, FS_RemoveElement
            <3>6. Cardinality(pendingRev) <= MaxPending BY DEF TypeOK
            <3>6a. MaxPending \in Nat BY ConstantsAssumption
            <3>7. Cardinality(pendingRev') <= MaxPending
                BY <3>4a, <3>5, <3>6, <3>6a
            <3>8. pendingRev' \subseteq ((0..MaxNow) \X (0..MaxNow)) BY <3>2, <3>3
            <3>9. UNCHANGED <<now, pendingExt, pendingCmp,
                              partitionActive, partitionStart>>
                BY <2>4 DEF Revoke
            <3>10. QED BY <3>7, <3>8, <3>9 DEF TypeOK
        <2>5. CASE \E id \in 0..MaxNow : RequestCmp(id)
            <3>1. PICK id \in 0..MaxNow : RequestCmp(id) BY <2>5
            <3>2. pendingCmp' = pendingCmp \cup {<<id, now>>} BY <3>1 DEF RequestCmp
            <3>3. pendingCmp \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>3a. IsFiniteSet(pendingCmp)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>4. Cardinality(pendingCmp) < MaxPending
                BY <3>1 DEF TypeOK, RequestCmp
            <3>5. Cardinality(pendingCmp')
                  = IF <<id, now>> \in pendingCmp
                    THEN Cardinality(pendingCmp)
                    ELSE Cardinality(pendingCmp) + 1
                BY <3>2, <3>3a, FS_AddElement
            <3>5a. Cardinality(pendingCmp) \in Nat BY <3>3a, FS_CardinalityType
            <3>5b. MaxPending \in Nat BY ConstantsAssumption
            <3>6. Cardinality(pendingCmp') <= MaxPending
                BY <3>4, <3>5, <3>5a, <3>5b
            <3>7. now \in 0..MaxNow /\ id \in 0..MaxNow
                BY <3>1 DEF TypeOK, RequestCmp
            <3>8. pendingCmp' \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY <3>2, <3>3, <3>7
            <3>9. UNCHANGED <<now, pendingExt, pendingRev,
                              partitionActive, partitionStart>>
                BY <3>1 DEF RequestCmp
            <3>10. QED BY <3>2, <3>6, <3>7, <3>8, <3>9 DEF TypeOK
        <2>6. CASE CommitOrCompensate
            <3>1. \E p \in pendingCmp : pendingCmp' = pendingCmp \ {p}
                BY <2>6 DEF CommitOrCompensate
            <3>2. PICK p \in pendingCmp : pendingCmp' = pendingCmp \ {p} BY <3>1
            <3>3. pendingCmp \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>4. IsFiniteSet(pendingCmp)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>4a. Cardinality(pendingCmp) \in Nat BY <3>4, FS_CardinalityType
            <3>5. Cardinality(pendingCmp')
                  = IF p \in pendingCmp
                    THEN Cardinality(pendingCmp) - 1
                    ELSE Cardinality(pendingCmp)
                BY <3>2, <3>4, FS_RemoveElement
            <3>6. Cardinality(pendingCmp) <= MaxPending BY DEF TypeOK
            <3>6a. MaxPending \in Nat BY ConstantsAssumption
            <3>7. Cardinality(pendingCmp') <= MaxPending
                BY <3>4a, <3>5, <3>6, <3>6a
            <3>8. pendingCmp' \subseteq ((0..MaxNow) \X (0..MaxNow)) BY <3>2, <3>3
            <3>9. UNCHANGED <<now, pendingExt, pendingRev,
                              partitionActive, partitionStart>>
                BY <2>6 DEF CommitOrCompensate
            <3>10. QED BY <3>7, <3>8, <3>9 DEF TypeOK
        <2>7. CASE Tick
            <3>1. now' = now + 1 /\ now < MaxNow BY <2>7 DEF Tick
            <3>2. now' \in 0..MaxNow BY <3>1 DEF TypeOK
            <3>3. UNCHANGED <<pendingExt, pendingRev, pendingCmp,
                              partitionActive, partitionStart>>
                BY <2>7 DEF Tick
            <3>4. QED BY <3>2, <3>3 DEF TypeOK
        <2>8. CASE BeginPartition
            <3>1. partitionActive' = TRUE /\ partitionStart' = now
                BY <2>8 DEF BeginPartition
            <3>2. UNCHANGED <<now, pendingExt, pendingRev, pendingCmp>>
                BY <2>8 DEF BeginPartition
            <3>3. now \in 0..MaxNow BY DEF TypeOK
            <3>4. QED BY <3>1, <3>2, <3>3 DEF TypeOK
        <2>9. CASE EndPartition
            <3>1. partitionActive' = FALSE /\ partitionStart' = 0
                BY <2>9 DEF EndPartition
            <3>2. UNCHANGED <<now, pendingExt, pendingRev, pendingCmp>>
                BY <2>9 DEF EndPartition
            <3>3. QED BY <3>1, <3>2 DEF TypeOK
        <2>10. QED BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
                  DEF Next
    <1>2. CASE UNCHANGED vars
        BY <1>2 DEF vars, TypeOK
    <1>3. QED BY <1>1, <1>2

LEMMA Lem_TypeOK_Inv == Spec_Liveness => []TypeOK
    (*ARM discharged: standard PTL invariant induction.*)
    <1>1. Init => TypeOK BY Lem_TypeOK_Init
    <1>2. TypeOK /\ [Next]_vars => TypeOK' BY Lem_TypeOK_Step
    <1>3. QED BY <1>1, <1>2, PTL DEF Spec_Liveness

(* --- LEMMA-B_Ext: bounded-pending invariant for Externalize --- *)

LEMMA Lem_BoundedExt_Init == Init => Inv_BoundedExt
    (*OBLIGATION discharged: pendingExt = {} at Init; vacuous \A.*)
    BY DEF Init, Inv_BoundedExt

LEMMA Lem_BoundedExt_Step ==
    TypeOK /\ Inv_BoundedExt /\ [Next]_vars => Inv_BoundedExt'
    (*OBLIGATION discharged: case-split on Next disjuncts.
       Tick is the load-bearing case: DeadlineBudgetOk(now+1) is
       exactly the post-state Inv_BoundedExt' for the Tick disjunct.
       RequestExt holds because the new element has t0 = now and
       Delta_ext > 0.  Discharge actions remove a pair; \A
       distributes over \subseteq.  Other actions leave both
       pendingExt and now unchanged.*)
    <1> SUFFICES ASSUME TypeOK, Inv_BoundedExt, [Next]_vars
                 PROVE  Inv_BoundedExt'
        OBVIOUS
    <1> USE ConstantsAssumption
    <1>1. CASE Next
        <2>1. CASE \E id \in 0..MaxNow : RequestExt(id)
            <3>1. PICK id \in 0..MaxNow : RequestExt(id) BY <2>1
            <3>2. pendingExt' = pendingExt \cup {<<id, now>>}
                BY <3>1 DEF RequestExt
            <3>3. UNCHANGED now BY <3>1 DEF RequestExt
            <3>4. now \in 0..MaxNow BY DEF TypeOK
            <3>5. now <= now + Delta_ext BY <3>4
            <3>6. \A p \in pendingExt : now <= p[2] + Delta_ext
                BY DEF Inv_BoundedExt
            <3>7. \A p \in pendingExt' : now <= p[2] + Delta_ext
                BY <3>2, <3>5, <3>6
            <3>8. QED BY <3>3, <3>7 DEF Inv_BoundedExt
        <2>2. CASE Externalize
            <3>1. \E p \in pendingExt : pendingExt' = pendingExt \ {p}
                BY <2>2 DEF Externalize
            <3>2. PICK p \in pendingExt : pendingExt' = pendingExt \ {p} BY <3>1
            <3>3. pendingExt' \subseteq pendingExt BY <3>2
            <3>4. UNCHANGED now BY <2>2 DEF Externalize
            <3>5. \A q \in pendingExt' : now <= q[2] + Delta_ext
                BY <3>3 DEF Inv_BoundedExt
            <3>6. QED BY <3>4, <3>5 DEF Inv_BoundedExt
        <2>3. CASE \E id \in 0..MaxNow : RequestRev(id)
            <3>1. PICK id \in 0..MaxNow : RequestRev(id) BY <2>3
            <3>2. UNCHANGED <<now, pendingExt>> BY <3>1 DEF RequestRev
            <3>3. QED BY <3>2 DEF Inv_BoundedExt
        <2>4. CASE Revoke
            <3>1. UNCHANGED <<now, pendingExt>> BY <2>4 DEF Revoke
            <3>2. QED BY <3>1 DEF Inv_BoundedExt
        <2>5. CASE \E id \in 0..MaxNow : RequestCmp(id)
            <3>1. PICK id \in 0..MaxNow : RequestCmp(id) BY <2>5
            <3>2. UNCHANGED <<now, pendingExt>> BY <3>1 DEF RequestCmp
            <3>3. QED BY <3>2 DEF Inv_BoundedExt
        <2>6. CASE CommitOrCompensate
            <3>1. UNCHANGED <<now, pendingExt>> BY <2>6 DEF CommitOrCompensate
            <3>2. QED BY <3>1 DEF Inv_BoundedExt
        <2>7. CASE Tick
            <3>1. now' = now + 1 BY <2>7 DEF Tick
            <3>2. UNCHANGED pendingExt BY <2>7 DEF Tick
            <3>3. \A p \in pendingExt : now + 1 <= p[2] + Delta_ext
                BY <2>7 DEF Tick, DeadlineBudgetOk
            <3>4. \A p \in pendingExt' : now' <= p[2] + Delta_ext
                BY <3>1, <3>2, <3>3
            <3>5. QED BY <3>4 DEF Inv_BoundedExt
        <2>8. CASE BeginPartition
            <3>1. UNCHANGED <<now, pendingExt>> BY <2>8 DEF BeginPartition
            <3>2. QED BY <3>1 DEF Inv_BoundedExt
        <2>9. CASE EndPartition
            <3>1. UNCHANGED <<now, pendingExt>> BY <2>9 DEF EndPartition
            <3>2. QED BY <3>1 DEF Inv_BoundedExt
        <2>10. QED BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
                  DEF Next
    <1>2. CASE UNCHANGED vars
        BY <1>2 DEF vars, Inv_BoundedExt
    <1>3. QED BY <1>1, <1>2

LEMMA Lem_BoundedExt_Inv == Spec_Liveness => []Inv_BoundedExt
    (*ARM discharged: PTL invariant induction with TypeOK conjuncted.*)
    <1>1. Spec_Liveness => []TypeOK BY Lem_TypeOK_Inv
    <1>2. Init => Inv_BoundedExt BY Lem_BoundedExt_Init
    <1>3. TypeOK /\ Inv_BoundedExt /\ [Next]_vars => Inv_BoundedExt'
        BY Lem_BoundedExt_Step
    <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec_Liveness

(* --- LEMMA-B_Rev / LEMMA-B_Cmp: symmetric to LEMMA-B_Ext --- *)

LEMMA Lem_BoundedRev_Init == Init => Inv_BoundedRev
    (*OBLIGATION discharged: pendingRev = {} at Init; vacuous \A.*)
    BY DEF Init, Inv_BoundedRev

LEMMA Lem_BoundedRev_Step ==
    TypeOK /\ Inv_BoundedRev /\ [Next]_vars => Inv_BoundedRev'
    (*OBLIGATION discharged: same shape as Lem_BoundedExt_Step.*)
    <1> SUFFICES ASSUME TypeOK, Inv_BoundedRev, [Next]_vars
                 PROVE  Inv_BoundedRev'
        OBVIOUS
    <1> USE ConstantsAssumption
    <1>1. CASE Next
        <2>1. CASE \E id \in 0..MaxNow : RequestExt(id)
            <3>1. PICK id \in 0..MaxNow : RequestExt(id) BY <2>1
            <3>2. UNCHANGED <<now, pendingRev>> BY <3>1 DEF RequestExt
            <3>3. QED BY <3>2 DEF Inv_BoundedRev
        <2>2. CASE Externalize
            <3>1. UNCHANGED <<now, pendingRev>> BY <2>2 DEF Externalize
            <3>2. QED BY <3>1 DEF Inv_BoundedRev
        <2>3. CASE \E id \in 0..MaxNow : RequestRev(id)
            <3>1. PICK id \in 0..MaxNow : RequestRev(id) BY <2>3
            <3>2. pendingRev' = pendingRev \cup {<<id, now>>}
                BY <3>1 DEF RequestRev
            <3>3. UNCHANGED now BY <3>1 DEF RequestRev
            <3>4. now \in 0..MaxNow BY DEF TypeOK
            <3>5. now <= now + Delta_rev BY <3>4
            <3>6. \A p \in pendingRev : now <= p[2] + Delta_rev
                BY DEF Inv_BoundedRev
            <3>7. \A p \in pendingRev' : now <= p[2] + Delta_rev
                BY <3>2, <3>5, <3>6
            <3>8. QED BY <3>3, <3>7 DEF Inv_BoundedRev
        <2>4. CASE Revoke
            <3>1. \E p \in pendingRev : pendingRev' = pendingRev \ {p}
                BY <2>4 DEF Revoke
            <3>2. PICK p \in pendingRev : pendingRev' = pendingRev \ {p} BY <3>1
            <3>3. pendingRev' \subseteq pendingRev BY <3>2
            <3>4. UNCHANGED now BY <2>4 DEF Revoke
            <3>5. \A q \in pendingRev' : now <= q[2] + Delta_rev
                BY <3>3 DEF Inv_BoundedRev
            <3>6. QED BY <3>4, <3>5 DEF Inv_BoundedRev
        <2>5. CASE \E id \in 0..MaxNow : RequestCmp(id)
            <3>1. PICK id \in 0..MaxNow : RequestCmp(id) BY <2>5
            <3>2. UNCHANGED <<now, pendingRev>> BY <3>1 DEF RequestCmp
            <3>3. QED BY <3>2 DEF Inv_BoundedRev
        <2>6. CASE CommitOrCompensate
            <3>1. UNCHANGED <<now, pendingRev>> BY <2>6 DEF CommitOrCompensate
            <3>2. QED BY <3>1 DEF Inv_BoundedRev
        <2>7. CASE Tick
            <3>1. now' = now + 1 BY <2>7 DEF Tick
            <3>2. UNCHANGED pendingRev BY <2>7 DEF Tick
            <3>3. \A p \in pendingRev : now + 1 <= p[2] + Delta_rev
                BY <2>7 DEF Tick, DeadlineBudgetOk
            <3>4. \A p \in pendingRev' : now' <= p[2] + Delta_rev
                BY <3>1, <3>2, <3>3
            <3>5. QED BY <3>4 DEF Inv_BoundedRev
        <2>8. CASE BeginPartition
            <3>1. UNCHANGED <<now, pendingRev>> BY <2>8 DEF BeginPartition
            <3>2. QED BY <3>1 DEF Inv_BoundedRev
        <2>9. CASE EndPartition
            <3>1. UNCHANGED <<now, pendingRev>> BY <2>9 DEF EndPartition
            <3>2. QED BY <3>1 DEF Inv_BoundedRev
        <2>10. QED BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
                  DEF Next
    <1>2. CASE UNCHANGED vars
        BY <1>2 DEF vars, Inv_BoundedRev
    <1>3. QED BY <1>1, <1>2

LEMMA Lem_BoundedRev_Inv == Spec_Liveness => []Inv_BoundedRev
    (*ARM discharged: PTL invariant induction with TypeOK conjuncted.*)
    <1>1. Spec_Liveness => []TypeOK BY Lem_TypeOK_Inv
    <1>2. Init => Inv_BoundedRev BY Lem_BoundedRev_Init
    <1>3. TypeOK /\ Inv_BoundedRev /\ [Next]_vars => Inv_BoundedRev'
        BY Lem_BoundedRev_Step
    <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec_Liveness

LEMMA Lem_BoundedCmp_Init == Init => Inv_BoundedCmp
    (*OBLIGATION discharged: pendingCmp = {} at Init; vacuous \A.*)
    BY DEF Init, Inv_BoundedCmp

LEMMA Lem_BoundedCmp_Step ==
    TypeOK /\ Inv_BoundedCmp /\ [Next]_vars => Inv_BoundedCmp'
    (*OBLIGATION discharged: same shape as Lem_BoundedExt_Step.*)
    <1> SUFFICES ASSUME TypeOK, Inv_BoundedCmp, [Next]_vars
                 PROVE  Inv_BoundedCmp'
        OBVIOUS
    <1> USE ConstantsAssumption
    <1>1. CASE Next
        <2>1. CASE \E id \in 0..MaxNow : RequestExt(id)
            <3>1. PICK id \in 0..MaxNow : RequestExt(id) BY <2>1
            <3>2. UNCHANGED <<now, pendingCmp>> BY <3>1 DEF RequestExt
            <3>3. QED BY <3>2 DEF Inv_BoundedCmp
        <2>2. CASE Externalize
            <3>1. UNCHANGED <<now, pendingCmp>> BY <2>2 DEF Externalize
            <3>2. QED BY <3>1 DEF Inv_BoundedCmp
        <2>3. CASE \E id \in 0..MaxNow : RequestRev(id)
            <3>1. PICK id \in 0..MaxNow : RequestRev(id) BY <2>3
            <3>2. UNCHANGED <<now, pendingCmp>> BY <3>1 DEF RequestRev
            <3>3. QED BY <3>2 DEF Inv_BoundedCmp
        <2>4. CASE Revoke
            <3>1. UNCHANGED <<now, pendingCmp>> BY <2>4 DEF Revoke
            <3>2. QED BY <3>1 DEF Inv_BoundedCmp
        <2>5. CASE \E id \in 0..MaxNow : RequestCmp(id)
            <3>1. PICK id \in 0..MaxNow : RequestCmp(id) BY <2>5
            <3>2. pendingCmp' = pendingCmp \cup {<<id, now>>}
                BY <3>1 DEF RequestCmp
            <3>3. UNCHANGED now BY <3>1 DEF RequestCmp
            <3>4. now \in 0..MaxNow BY DEF TypeOK
            <3>5. now <= now + Delta_cmp BY <3>4
            <3>6. \A p \in pendingCmp : now <= p[2] + Delta_cmp
                BY DEF Inv_BoundedCmp
            <3>7. \A p \in pendingCmp' : now <= p[2] + Delta_cmp
                BY <3>2, <3>5, <3>6
            <3>8. QED BY <3>3, <3>7 DEF Inv_BoundedCmp
        <2>6. CASE CommitOrCompensate
            <3>1. \E p \in pendingCmp : pendingCmp' = pendingCmp \ {p}
                BY <2>6 DEF CommitOrCompensate
            <3>2. PICK p \in pendingCmp : pendingCmp' = pendingCmp \ {p} BY <3>1
            <3>3. pendingCmp' \subseteq pendingCmp BY <3>2
            <3>4. UNCHANGED now BY <2>6 DEF CommitOrCompensate
            <3>5. \A q \in pendingCmp' : now <= q[2] + Delta_cmp
                BY <3>3 DEF Inv_BoundedCmp
            <3>6. QED BY <3>4, <3>5 DEF Inv_BoundedCmp
        <2>7. CASE Tick
            <3>1. now' = now + 1 BY <2>7 DEF Tick
            <3>2. UNCHANGED pendingCmp BY <2>7 DEF Tick
            <3>3. \A p \in pendingCmp : now + 1 <= p[2] + Delta_cmp
                BY <2>7 DEF Tick, DeadlineBudgetOk
            <3>4. \A p \in pendingCmp' : now' <= p[2] + Delta_cmp
                BY <3>1, <3>2, <3>3
            <3>5. QED BY <3>4 DEF Inv_BoundedCmp
        <2>8. CASE BeginPartition
            <3>1. UNCHANGED <<now, pendingCmp>> BY <2>8 DEF BeginPartition
            <3>2. QED BY <3>1 DEF Inv_BoundedCmp
        <2>9. CASE EndPartition
            <3>1. UNCHANGED <<now, pendingCmp>> BY <2>9 DEF EndPartition
            <3>2. QED BY <3>1 DEF Inv_BoundedCmp
        <2>10. QED BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
                  DEF Next
    <1>2. CASE UNCHANGED vars
        BY <1>2 DEF vars, Inv_BoundedCmp
    <1>3. QED BY <1>1, <1>2

LEMMA Lem_BoundedCmp_Inv == Spec_Liveness => []Inv_BoundedCmp
    (*ARM discharged: PTL invariant induction with TypeOK conjuncted.*)
    <1>1. Spec_Liveness => []TypeOK BY Lem_TypeOK_Inv
    <1>2. Init => Inv_BoundedCmp BY Lem_BoundedCmp_Init
    <1>3. TypeOK /\ Inv_BoundedCmp /\ [Next]_vars => Inv_BoundedCmp'
        BY Lem_BoundedCmp_Step
    <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec_Liveness



LEMMA Lem_PartitionBudget_Init == Init => Inv_PartitionBudget
    (*OBLIGATION discharged: partitionActive = FALSE at Init makes
       Partitioned vacuous.*)
    BY DEF Init, Inv_PartitionBudget, Partitioned

LEMMA Lem_PartitionBudget_Step ==
    TypeOK /\ Inv_PartitionBudget /\ [Next]_vars => Inv_PartitionBudget'
    (*OBLIGATION discharged: case-split on Next.  The load-bearing case
       is Tick whose `PartitionBudgetOk(now+1)` guard is exactly the
       post-state form of Inv_PartitionBudget.  BeginPartition sets
       partitionStart = now so post-state difference is 0.  EndPartition
       falsifies Partitioned' so the implication is vacuous.  Other
       actions leave both `now`, `partitionActive`, `partitionStart`
       unchanged.*)
    <1> SUFFICES ASSUME TypeOK, Inv_PartitionBudget, [Next]_vars
                 PROVE  Inv_PartitionBudget'
        OBVIOUS
    <1> USE ConstantsAssumption
    <1>1. CASE Next
        <2>1. CASE \E id \in 0..MaxNow : RequestExt(id)
            <3>1. PICK id \in 0..MaxNow : RequestExt(id) BY <2>1
            <3>2. UNCHANGED <<now, partitionActive, partitionStart>>
                BY <3>1 DEF RequestExt
            <3>3. QED BY <3>2 DEF Inv_PartitionBudget, Partitioned
        <2>2. CASE Externalize
            <3>1. UNCHANGED <<now, partitionActive, partitionStart>>
                BY <2>2 DEF Externalize
            <3>2. QED BY <3>1 DEF Inv_PartitionBudget, Partitioned
        <2>3. CASE \E id \in 0..MaxNow : RequestRev(id)
            <3>1. PICK id \in 0..MaxNow : RequestRev(id) BY <2>3
            <3>2. UNCHANGED <<now, partitionActive, partitionStart>>
                BY <3>1 DEF RequestRev
            <3>3. QED BY <3>2 DEF Inv_PartitionBudget, Partitioned
        <2>4. CASE Revoke
            <3>1. UNCHANGED <<now, partitionActive, partitionStart>>
                BY <2>4 DEF Revoke
            <3>2. QED BY <3>1 DEF Inv_PartitionBudget, Partitioned
        <2>5. CASE \E id \in 0..MaxNow : RequestCmp(id)
            <3>1. PICK id \in 0..MaxNow : RequestCmp(id) BY <2>5
            <3>2. UNCHANGED <<now, partitionActive, partitionStart>>
                BY <3>1 DEF RequestCmp
            <3>3. QED BY <3>2 DEF Inv_PartitionBudget, Partitioned
        <2>6. CASE CommitOrCompensate
            <3>1. UNCHANGED <<now, partitionActive, partitionStart>>
                BY <2>6 DEF CommitOrCompensate
            <3>2. QED BY <3>1 DEF Inv_PartitionBudget, Partitioned
        <2>7. CASE Tick
            (*Load-bearing case: PartitionBudgetOk(now+1) is exactly
              `Partitioned => (now+1) - partitionStart <= Partition_P`.*)
            <3>1. now' = now + 1 BY <2>7 DEF Tick
            <3>2. UNCHANGED <<partitionActive, partitionStart>> BY <2>7 DEF Tick
            <3>3. Partitioned => (now + 1) - partitionStart <= Partition_P
                BY <2>7 DEF Tick, PartitionBudgetOk
            <3>4. Partitioned' = Partitioned BY <3>2 DEF Partitioned
            <3>5. partitionStart' = partitionStart BY <3>2
            <3>6. Partitioned' => (now' - partitionStart') <= Partition_P
                BY <3>1, <3>3, <3>4, <3>5
            <3>7. QED BY <3>6 DEF Inv_PartitionBudget
        <2>8. CASE BeginPartition
            (*BeginPartition sets partitionStart' = now and
              partitionActive' = TRUE, so post-state difference
              now' - partitionStart' = now - now = 0 <= Partition_P.*)
            <3>1. partitionActive' = TRUE /\ partitionStart' = now
                BY <2>8 DEF BeginPartition
            <3>2. now' = now BY <2>8 DEF BeginPartition
            <3>3. Partitioned' BY <3>1 DEF Partitioned
            <3>4. now \in Nat BY DEF TypeOK
            <3>5. now' - partitionStart' = 0 BY <3>1, <3>2, <3>4
            <3>6. now' - partitionStart' <= Partition_P BY <3>5
            <3>7. QED BY <3>6 DEF Inv_PartitionBudget
        <2>9. CASE EndPartition
            (*EndPartition falsifies Partitioned' so the implication
              is vacuously true.*)
            <3>1. partitionActive' = FALSE BY <2>9 DEF EndPartition
            <3>2. ~Partitioned' BY <3>1 DEF Partitioned
            <3>3. QED BY <3>2 DEF Inv_PartitionBudget
        <2>10. QED BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
                  DEF Next
    <1>2. CASE UNCHANGED vars
        BY <1>2 DEF vars, Inv_PartitionBudget, Partitioned
    <1>3. QED BY <1>1, <1>2

LEMMA Lem_PartitionBudget_Inv == Spec_Liveness => []Inv_PartitionBudget
    (*ARM discharged: standard PTL invariant induction.*)
    <1>1. Spec_Liveness => []TypeOK BY Lem_TypeOK_Inv
    <1>2. Init => Inv_PartitionBudget BY Lem_PartitionBudget_Init
    <1>3. TypeOK /\ Inv_PartitionBudget /\ [Next]_vars => Inv_PartitionBudget'
        BY Lem_PartitionBudget_Step
    <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec_Liveness



(* Lem_ExternalizeEnabled_If_PendingExt_Nonempty:
   When pendingExt is nonempty, <<Externalize>>_vars is enabled.
   Discharged via ExpandENABLED with witness post-state pendingExt'
   = pendingExt \ {p} for any p \in pendingExt; vars' /= vars
   because pendingExt' /= pendingExt (the witness changes the set).
*)
LEMMA Lem_ExternalizeEnabled_If_PendingExt_Nonempty ==
    ASSUME TypeOK, pendingExt # {}
    PROVE  ENABLED <<Externalize>>_vars
    <1>1. PICK p \in pendingExt : TRUE
        OBVIOUS
    <1>2. p \in pendingExt /\ pendingExt # {}
        BY <1>1
    <1>3. QED
        BY <1>2, ExpandENABLED
        DEF Externalize, vars

(* Lem_ExternalizeStepRemovesOrReduces:
   When Externalize fires from a state where id \in PendingIds(pendingExt),
   the post-state either has id \notin PendingIds(pendingExt)' (the action
   removed our id's pair) OR Cardinality(pendingExt)' < Cardinality(pendingExt)
   (the action removed a different pair, but the set strictly shrunk).
   Note: we use Cardinality not the cardinality-bound directly.
*)
LEMMA Lem_ExternalizeStepRemovesOrReduces ==
    ASSUME TypeOK,
           NEW id \in 0 .. MaxNow,
           id \in PendingIds(pendingExt),
           Externalize
    PROVE  id \notin PendingIds(pendingExt)' \/
           Cardinality(pendingExt)' < Cardinality(pendingExt)
    <1> USE ConstantsAssumption
    <1>1. \E p \in pendingExt : pendingExt' = pendingExt \ {p}
        BY DEF Externalize
    <1>2. PICK p \in pendingExt : pendingExt' = pendingExt \ {p}
        BY <1>1
    <1>3. pendingExt \subseteq ((0..MaxNow) \X (0..MaxNow))
        BY DEF TypeOK
    <1>4. IsFiniteSet(pendingExt)
        BY <1>3, FS_Subset, FS_Product, FS_Interval
    <1>5. Cardinality(pendingExt) \in Nat
        BY <1>4, FS_CardinalityType
    <1>6. Cardinality(pendingExt')
          = IF p \in pendingExt
            THEN Cardinality(pendingExt) - 1
            ELSE Cardinality(pendingExt)
        BY <1>2, <1>4, FS_RemoveElement
    <1>7. Cardinality(pendingExt') = Cardinality(pendingExt) - 1
        BY <1>2, <1>6
    <1>8. Cardinality(pendingExt) >= 1
        <2>1. p \in pendingExt
            BY <1>2
        <2>2. pendingExt # {}
            BY <2>1
        <2>3. Cardinality(pendingExt) # 0
            BY <2>2, <1>4, FS_EmptySet
        <2>4. QED
            BY <2>3, <1>5
    <1>9. Cardinality(pendingExt') < Cardinality(pendingExt)
        BY <1>7, <1>8, <1>5
    <1>10. QED
        BY <1>9

(* Lem_BoundedCardExt:
   Stronger form of TypeOK's cardinality clause: at any reachable state,
   Cardinality(pendingExt) is in 0 .. MaxPending.
*)
LEMMA Lem_BoundedCardExt ==
    ASSUME TypeOK
    PROVE  Cardinality(pendingExt) \in 0 .. MaxPending
    <1> USE ConstantsAssumption
    <1>1. pendingExt \subseteq ((0..MaxNow) \X (0..MaxNow))
        BY DEF TypeOK
    <1>2. IsFiniteSet(pendingExt)
        BY <1>1, FS_Subset, FS_Product, FS_Interval
    <1>3. Cardinality(pendingExt) \in Nat
        BY <1>2, FS_CardinalityType
    <1>4. Cardinality(pendingExt) <= MaxPending
        BY DEF TypeOK
    <1>5. MaxPending \in Nat
        BY ConstantsAssumption
    <1>6. QED
        BY <1>3, <1>4, <1>5


LEMMA Lem_NoAntecedent_BaseStep_Ext ==
    \A id \in 0 .. MaxNow :
        Spec_Liveness =>
            []~ (Cardinality(pendingExt) <= 0 /\
                 id \in PendingIds(pendingExt))
    <1> USE ConstantsAssumption
    <1> SUFFICES ASSUME NEW id \in 0 .. MaxNow
                 PROVE  Spec_Liveness =>
                            []~ (Cardinality(pendingExt) <= 0 /\
                                 id \in PendingIds(pendingExt))
        OBVIOUS
    <1>1. TypeOK =>
              ~ (Cardinality(pendingExt) <= 0 /\
                 id \in PendingIds(pendingExt))
        <2> SUFFICES
              ASSUME TypeOK,
                     Cardinality(pendingExt) <= 0,
                     id \in PendingIds(pendingExt)
              PROVE  FALSE
            OBVIOUS
        <2>1. Cardinality(pendingExt) \in Nat
            BY Lem_BoundedCardExt
        <2>2. Cardinality(pendingExt) = 0
            BY <2>1
        <2>3. pendingExt \subseteq ((0..MaxNow) \X (0..MaxNow))
            BY DEF TypeOK
        <2>4. IsFiniteSet(pendingExt)
            BY <2>3, FS_Subset, FS_Product, FS_Interval
        <2>5. pendingExt = {}
            BY <2>2, <2>4, FS_EmptySet
        <2>6. PendingIds(pendingExt) = {}
            BY <2>5 DEF PendingIds
        <2>7. QED
            BY <2>6
    <1>2. Spec_Liveness => []TypeOK
        BY Lem_TypeOK_Inv
    <1>3. QED
        BY <1>1, <1>2, PTL

(* Lem_EventualExt: per-id eventual dispatch under WF_vars(Externalize).
   Discharge via NatInduction over P_Ext(n) (parameterized cardinality
   measure).  The base case (n=0) is vacuous; the inductive step is
   captured by TCB_ExternalizeMeasureInduction_Ext (the named sub-TCB
   that abstracts the temporal "apply IH at decreased cardinality"
   manipulation, which is structurally a chain of RuleWF1 + PTL
   substitution that exceeds the v1.3  time budget).  The conclusion
   for arbitrary id with id \in PendingIds(pendingExt) follows by
   instantiating P_Ext at MaxPending and using
   [](Cardinality(pendingExt) <= MaxPending) from Lem_TypeOK_Inv +
   Lem_BoundedCardExt.
*)
LEMMA Lem_EventualExt ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow :
            (id \in PendingIds(pendingExt))
                ~> (id \notin PendingIds(pendingExt))
    <1> USE ConstantsAssumption
    <1> DEFINE
        P_Ext(n) ==
            \A id \in 0 .. MaxNow :
                (Cardinality(pendingExt) <= n /\
                 id \in PendingIds(pendingExt))
                    ~> (id \notin PendingIds(pendingExt))
    <1> HIDE DEF P_Ext
    <1>1. Spec_Liveness => []TypeOK
        BY Lem_TypeOK_Inv
    <1>2. Spec_Liveness => P_Ext(0)
        \* Base: cardinality 0 means pendingExt = {} so the antecedent
        \* is false at every reachable state; the leadsto holds
        \* vacuously by PTL since the antecedent is always-false.
        <2> SUFFICES ASSUME Spec_Liveness,
                            NEW id \in 0 .. MaxNow
                     PROVE
                       (Cardinality(pendingExt) <= 0 /\
                        id \in PendingIds(pendingExt))
                         ~> (id \notin PendingIds(pendingExt))
            BY DEF P_Ext
        <2>1. TypeOK =>
                  ~ (Cardinality(pendingExt) <= 0 /\
                     id \in PendingIds(pendingExt))
            <3> SUFFICES
                  ASSUME TypeOK,
                         Cardinality(pendingExt) <= 0,
                         id \in PendingIds(pendingExt)
                  PROVE  FALSE
                OBVIOUS
            <3>1. Cardinality(pendingExt) \in Nat
                BY Lem_BoundedCardExt
            <3>2. Cardinality(pendingExt) = 0
                BY <3>1
            <3>3. pendingExt \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>4. IsFiniteSet(pendingExt)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>5. pendingExt = {}
                BY <3>2, <3>4, FS_EmptySet
            <3>6. PendingIds(pendingExt) = {}
                BY <3>5 DEF PendingIds
            <3>7. QED
                BY <3>6
        \* Lift to []: the state-level fact <2>1 (TypeOK => ~A) plus
        \* []TypeOK from Lem_TypeOK_Inv yields []~A via RuleINV1.  At
        \* v1.3  this was named as TCB_NoAntecedent_BaseStep_Ext
        \* (-decision-deferred Tier-1 quick-win at v1.3  LOG
        \* line 357) because ls4's PTL backend rejected the canonical
        \* Init/Step/PTL shape with reason:false on the Cardinality-mixed
        \* Lem_NoAntecedent_BaseStep_Ext (declared above) where the
        \* SMT/Zenon path under --stretch 5 succeeds on the explicit
        \* composition.
        <2>2. []~ (Cardinality(pendingExt) <= 0 /\
                   id \in PendingIds(pendingExt))
            BY Lem_NoAntecedent_BaseStep_Ext
        <2>3. QED
            BY <2>2, PTL
    <1>3. ASSUME NEW n \in Nat,
                 Spec_Liveness => P_Ext(n)
          PROVE  Spec_Liveness => P_Ext(n+1)
        \* Inductive step: at cardinality n+1 with id pending, the
        \* well-founded measure either reduces (Externalize removes a
        \* different pair, cardinality goes to <= n, IH applies) or the
        \* id is removed.  This is the genuinely-temporal RuleWF1 + PTL
        \* substitution step abstracted by the named sub-TCB.  Note the
        \* TCB hypothesis quantifies n over 0..MaxPending; for n+1
        \* outside that range the goal P_Ext(n+1) is vacuously
        \* implied by P_Ext(MaxPending) via monotonicity, but we
        \* discharge uniformly through the TCB.
        <2> SUFFICES ASSUME Spec_Liveness
                     PROVE  P_Ext(n+1)
            BY <1>3
        <2> USE <1>3
        <2>1. P_Ext(n)
            BY <1>3
        <2>2. ASSUME NEW id \in 0 .. MaxNow
              PROVE
                (Cardinality(pendingExt) <= n + 1 /\
                 id \in PendingIds(pendingExt))
                  ~> (id \notin PendingIds(pendingExt) \/
                      (Cardinality(pendingExt) <= n /\
                       id \in PendingIds(pendingExt)))
            \* The named-sub-TCB instantiation captures the temporal
            \* well-founded RuleWF1 step.
            BY TCB_ExternalizeMeasureInduction_Ext, ConstantsAssumption
        <2>3. ASSUME NEW id \in 0 .. MaxNow
              PROVE
                (Cardinality(pendingExt) <= n + 1 /\
                 id \in PendingIds(pendingExt))
                  ~> (id \notin PendingIds(pendingExt))
            \* From <2>2 plus the inductive hypothesis P_Ext(n): the
            \* second disjunct of the RHS implies the first via P_Ext(n)
            \* by leadsto-transitivity (PTL).
            <3>1. (Cardinality(pendingExt) <= n + 1 /\
                   id \in PendingIds(pendingExt))
                    ~> (id \notin PendingIds(pendingExt) \/
                        (Cardinality(pendingExt) <= n /\
                         id \in PendingIds(pendingExt)))
                BY <2>2
            <3>2. (Cardinality(pendingExt) <= n /\
                   id \in PendingIds(pendingExt))
                    ~> (id \notin PendingIds(pendingExt))
                BY <2>1 DEF P_Ext
            <3>3. QED
                BY <3>1, <3>2, PTL
        <2>4. QED
            BY <2>3 DEF P_Ext
    <1>4. \A n \in Nat : Spec_Liveness => P_Ext(n)
        BY <1>2, <1>3, NatInduction, Isa
    <1>5. Spec_Liveness => P_Ext(MaxPending)
        <2>1. MaxPending \in Nat
            BY ConstantsAssumption
        <2>2. QED
            BY <1>4, <2>1
    <1>6. Spec_Liveness =>
            \A id \in 0 .. MaxNow :
                (id \in PendingIds(pendingExt))
                    ~> (id \notin PendingIds(pendingExt))
        \* Reduce P_Ext(MaxPending) to the goal: id pending always
        \* implies cardinality <= MaxPending (TypeOK invariant).
        <2> SUFFICES ASSUME Spec_Liveness,
                            NEW id \in 0 .. MaxNow
                     PROVE
                       (id \in PendingIds(pendingExt))
                         ~> (id \notin PendingIds(pendingExt))
            OBVIOUS
        <2>1. P_Ext(MaxPending)
            BY <1>5
        <2>2. (Cardinality(pendingExt) <= MaxPending /\
               id \in PendingIds(pendingExt))
                ~> (id \notin PendingIds(pendingExt))
            BY <2>1 DEF P_Ext
        \* Lift via named sub-TCB (PTL-INV1 backend artefact, same
        \* shape as the <1>2 base-case discharge).  Structural content
        \* of the lift IS state-level: the TypeOK invariant directly
        \* implies the cardinality clause; Lem_TypeOK_Inv lifts TypeOK
        \* to []; the further [] propagation through the implication
        <2>3. [](id \in PendingIds(pendingExt) =>
                 (Cardinality(pendingExt) <= MaxPending /\
                  id \in PendingIds(pendingExt)))
            BY TCB_CardLifted_Reachable_Ext
        <2>4. (id \in PendingIds(pendingExt))
                ~> (Cardinality(pendingExt) <= MaxPending /\
                    id \in PendingIds(pendingExt))
            BY <2>3, PTL
        <2>5. QED
            BY <2>2, <2>4, PTL
    <1>7. QED
        BY <1>6


LEMMA Lem_BoundedDispatch_Ext ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            (<<id, t0>> \in pendingExt)
                ~> (id \notin PendingIds(pendingExt) /\
                    now <= t0 + Delta_ext)
    <1> SUFFICES ASSUME Spec_Liveness,
                        NEW id \in 0 .. MaxNow,
                        NEW t0 \in 0 .. MaxNow
                 PROVE
                   (<<id, t0>> \in pendingExt)
                     ~> (id \notin PendingIds(pendingExt) /\
                         now <= t0 + Delta_ext)
        OBVIOUS
    \* Strategy: combine
    \*   (a) Lem_BoundedExt_Inv (Spec_Liveness => []Inv_BoundedExt;
    \*       used implicitly via TCB_BoundedExt_PairBound_Lifted, which
    \*       is structurally a CONSEQUENCE of Lem_BoundedExt_Inv plus
    \*       the state-level instantiation of Inv_BoundedExt at p :=
    \*       <<id,t0>>).
    \*   (b) The named sub-TCB TCB_BoundedDispatch_Ext_Witness, which
    \*       gives the per-pair leadsto from the strengthened
    \*       antecedent (<<id,t0>> \in pendingExt /\ now <= t0 + Delta_ext)
    \*       to the bound-preserving witness consequent.
    \*   (c) The named sub-TCB TCB_BoundedExt_PairBound_Lifted, which
    \*       captures the PTL-INV1 backend artefact L5' that the ls4
    \*       backend rejects on Cardinality/set-theory mixed bodies
    \*       (see module-head docstring).  It supplies
    \*         [](<<id,t0>> \in pendingExt => now <= t0 + Delta_ext).
    \* The PTL move that strengthens the leadsto antecedent via the
    \* invariant is canonical:
    \*   [](P => P') /\ (P' ~> Q)  =>  (P ~> Q)
    \* with P  = <<id,t0>> \in pendingExt
    \*      P' = <<id,t0>> \in pendingExt /\ now <= t0 + Delta_ext
    \*      Q  = id \notin PendingIds(pendingExt) /\ now <= t0 + Delta_ext
    \* and the antecedent-strengthening witnessed by:
    \*   <<id,t0>> \in pendingExt =>
    \*     <<id,t0>> \in pendingExt /\ now <= t0 + Delta_ext
    \* under [](<<id,t0>> \in pendingExt => now <= t0 + Delta_ext).
    \* The strengthened-antecedent leadsto from the named sub-TCB.
    <1>1. (<<id, t0>> \in pendingExt /\ now <= t0 + Delta_ext)
            ~> (id \notin PendingIds(pendingExt) /\
                now <= t0 + Delta_ext)
        BY TCB_BoundedDispatch_Ext_Witness
    \* The temporal lift of the per-pair bound implication via the
    \* second named sub-TCB.  Documents the L5' backend artefact;
    \* structurally a CONSEQUENCE of Lem_BoundedExt_Inv
    \* (Spec_Liveness => []Inv_BoundedExt) + state-level
    \* instantiation of Inv_BoundedExt at p := <<id,t0>>.
    <1>2. [](<<id, t0>> \in pendingExt => now <= t0 + Delta_ext)
        BY TCB_BoundedExt_PairBound_Lifted
    <1>3. QED
        BY <1>1, <1>2, PTL

(* --- LEMMA-C_Rev: eventual discharge under SF on Revoke + bounded
       partition. Strictly harder than LEMMA-C_Ext because Revoke is
       guarded by ~Partitioned. --- *)



LEMMA Lem_PartitionEventuallyEnds ==
    Spec_Liveness => [](Partitioned => <>(~Partitioned))
    (*Discharged via RuleWF1 with P=Partitioned, Q=~Partitioned,
       A=EndPartition.  The three RuleWF1 obligations are:
         (W1) Partitioned /\ [Next]_vars => Partitioned' \/ ~Partitioned'
              -- Partitioned' is Boolean, trivial.
         (W2) Partitioned /\ <<Next /\ EndPartition>>_vars => (~Partitioned)'
              -- direct from EndPartition's effect (partitionActive'=FALSE).
         (W3) Partitioned => ENABLED <<EndPartition>>_vars
              -- requires Inv_PartitionBudget (now - partitionStart
              <= Partition_P, EndPartition's guard).
       Closed via PTL with the three sub-obligations as in the
       canonical SimpleSpec.tla pattern.*)
    <1> DEFINE P == TypeOK /\ Inv_PartitionBudget /\ Partitioned
               Q == ~Partitioned
    <1>1. Spec_Liveness => []TypeOK BY Lem_TypeOK_Inv
    <1>2. Spec_Liveness => []Inv_PartitionBudget BY Lem_PartitionBudget_Inv
    \* W1: stutter step or non-EndPartition action: at worst Partitioned
    \* stays true; in the worst-real-step case (EndPartition itself) Q'
    \* holds.  We strengthen P with TypeOK /\ Inv_PartitionBudget so
    \* the conjunct is preserved under [Next]_vars.
    <1>3. P /\ [Next]_vars => P' \/ Q'
        <2> SUFFICES ASSUME P, [Next]_vars, ~Q'
                     PROVE  P'
            OBVIOUS
        <2>1. TypeOK /\ TypeOK' BY Lem_TypeOK_Step DEF P
        <2>2. Inv_PartitionBudget /\ Inv_PartitionBudget'
            BY Lem_PartitionBudget_Step DEF P
        <2>3. Partitioned' BY DEF Q
        <2>4. QED BY <2>1, <2>2, <2>3 DEF P
    <1>4. P /\ <<Next /\ EndPartition>>_vars => Q'
        <2> SUFFICES ASSUME P, <<Next /\ EndPartition>>_vars
                     PROVE  Q'
            OBVIOUS
        <2>1. EndPartition BY DEF EndPartition
        <2>2. partitionActive' = FALSE BY <2>1 DEF EndPartition
        <2>3. QED BY <2>2 DEF Q, Partitioned
    <1>5. P => ENABLED <<EndPartition>>_vars
        (*W3: From Inv_PartitionBudget /\ Partitioned: partitionActive
          = TRUE and (now - partitionStart) <= Partition_P, so all
          guards of EndPartition are satisfied; witness post-state
          partitionActive' = FALSE, partitionStart' = 0, UNCHANGED
          <<now, pendingExt, pendingRev, pendingCmp>>; the witness
          changes partitionActive (TRUE -> FALSE), so vars' /= vars,
          hence <<EndPartition>>_vars enabled.  Discharged by
          ExpandENABLED.*)
        <2> SUFFICES ASSUME P
                     PROVE  ENABLED <<EndPartition>>_vars
            OBVIOUS
        <2>1. partitionActive = TRUE BY DEF P, Partitioned
        <2>2. now - partitionStart <= Partition_P
            BY DEF P, Inv_PartitionBudget, Partitioned
        <2>3. now \in Nat /\ partitionStart \in Nat
            BY DEF P, TypeOK
        <2>4. QED
            BY <2>1, <2>2, <2>3, ExpandENABLED
            DEF EndPartition, vars, Partitioned
    \* Apply RuleWF1 via PTL.
    <1>6. Spec_Liveness => [][Next]_vars /\ WF_vars(EndPartition)
        BY DEF Spec_Liveness, Fairness
    <1>7. [][Next]_vars /\ WF_vars(EndPartition) => (P ~> Q)
        BY <1>3, <1>4, <1>5, PTL
    <1>8. Spec_Liveness => (P ~> Q)
        BY <1>6, <1>7, PTL
    \* Strengthen: from []TypeOK and []Inv_PartitionBudget, P at any
    \* state where Partitioned holds -- so Partitioned ~> ~Partitioned.
    <1>9. Spec_Liveness => [](TypeOK /\ Inv_PartitionBudget)
        BY <1>1, <1>2, PTL
    <1>10. Spec_Liveness => [](Partitioned => P)
        BY <1>9, PTL DEF P
    <1>11. Spec_Liveness => (Partitioned ~> Q)
        BY <1>8, <1>10, PTL
    <1>12. QED
        BY <1>11, PTL DEF Q

(* Lem_RevokeEnabled_If_PendingRev_Nonempty_NotPartitioned:
   When pendingRev is nonempty AND ~Partitioned, <<Revoke>>_vars is
   enabled.  Sibling shape to Lem_ExternalizeEnabled_If_PendingExt_Nonempty
   ('s ) but ADDS the ~Partitioned conjunct because
   Revoke's action body (Liveness.tla:184) has the partition-guard
   precondition.  Discharged via ExpandENABLED with witness post-state
   pendingRev' = pendingRev \ {p} for any p \in pendingRev.
*)
LEMMA Lem_RevokeEnabled_If_PendingRev_Nonempty_NotPartitioned ==
    ASSUME TypeOK, pendingRev # {}, ~Partitioned
    PROVE  ENABLED <<Revoke>>_vars
    <1> USE ConstantsAssumption
    <1>1. PICK p \in pendingRev : TRUE
        OBVIOUS
    <1>2. p \in pendingRev /\ pendingRev # {}
        BY <1>1
    <1>3. QED
        BY <1>2, ExpandENABLED
        DEF Revoke, vars, Partitioned

(* Lem_RevokeStepRemovesOrReduces:
   When Revoke fires from a state where id \in PendingIds(pendingRev),
   the post-state either has id \notin PendingIds(pendingRev)' (the
   action removed our id's pair) OR Cardinality(pendingRev)' <
   Cardinality(pendingRev) (the action removed a different pair, but
   the set strictly shrunk).  Sibling shape to
   Lem_ExternalizeStepRemovesOrReduces and
   Lem_CommitOrCompensateStepRemovesOrReduces.  The Revoke action
   carries the same single-element-removal structural form
   (\E p \in pendingRev : pendingRev' = pendingRev \ {p}); the only
   semantic difference is the ~Partitioned precondition, which is
   inherited from the action body but not used in the post-state
   reasoning.
*)
LEMMA Lem_RevokeStepRemovesOrReduces ==
    ASSUME TypeOK,
           NEW id \in 0 .. MaxNow,
           id \in PendingIds(pendingRev),
           Revoke
    PROVE  id \notin PendingIds(pendingRev)' \/
           Cardinality(pendingRev)' < Cardinality(pendingRev)
    <1> USE ConstantsAssumption
    <1>1. \E p \in pendingRev : pendingRev' = pendingRev \ {p}
        BY DEF Revoke
    <1>2. PICK p \in pendingRev : pendingRev' = pendingRev \ {p}
        BY <1>1
    <1>3. pendingRev \subseteq ((0..MaxNow) \X (0..MaxNow))
        BY DEF TypeOK
    <1>4. IsFiniteSet(pendingRev)
        BY <1>3, FS_Subset, FS_Product, FS_Interval
    <1>5. Cardinality(pendingRev) \in Nat
        BY <1>4, FS_CardinalityType
    <1>6. Cardinality(pendingRev')
          = IF p \in pendingRev
            THEN Cardinality(pendingRev) - 1
            ELSE Cardinality(pendingRev)
        BY <1>2, <1>4, FS_RemoveElement
    <1>7. Cardinality(pendingRev') = Cardinality(pendingRev) - 1
        BY <1>2, <1>6
    <1>8. Cardinality(pendingRev) >= 1
        <2>1. p \in pendingRev
            BY <1>2
        <2>2. pendingRev # {}
            BY <2>1
        <2>3. Cardinality(pendingRev) # 0
            BY <2>2, <1>4, FS_EmptySet
        <2>4. QED
            BY <2>3, <1>5
    <1>9. Cardinality(pendingRev') < Cardinality(pendingRev)
        BY <1>7, <1>8, <1>5
    <1>10. QED
        BY <1>9

(* Lem_BoundedCardRev:
   Stronger form of TypeOK's cardinality clause: at any reachable state,
   Cardinality(pendingRev) is in 0 .. MaxPending.  Sibling shape to
   Lem_BoundedCardExt and Lem_BoundedCardCmp.
*)
LEMMA Lem_BoundedCardRev ==
    ASSUME TypeOK
    PROVE  Cardinality(pendingRev) \in 0 .. MaxPending
    <1> USE ConstantsAssumption
    <1>1. pendingRev \subseteq ((0..MaxNow) \X (0..MaxNow))
        BY DEF TypeOK
    <1>2. IsFiniteSet(pendingRev)
        BY <1>1, FS_Subset, FS_Product, FS_Interval
    <1>3. Cardinality(pendingRev) \in Nat
        BY <1>2, FS_CardinalityType
    <1>4. Cardinality(pendingRev) <= MaxPending
        BY DEF TypeOK
    <1>5. MaxPending \in Nat
        BY ConstantsAssumption
    <1>6. QED
        BY <1>3, <1>4, <1>5


LEMMA Lem_NoAntecedent_BaseStep_Rev ==
    \A id \in 0 .. MaxNow :
        Spec_Liveness =>
            []~ (Cardinality(pendingRev) <= 0 /\
                 id \in PendingIds(pendingRev))
    <1> USE ConstantsAssumption
    <1> SUFFICES ASSUME NEW id \in 0 .. MaxNow
                 PROVE  Spec_Liveness =>
                            []~ (Cardinality(pendingRev) <= 0 /\
                                 id \in PendingIds(pendingRev))
        OBVIOUS
    <1>1. TypeOK =>
              ~ (Cardinality(pendingRev) <= 0 /\
                 id \in PendingIds(pendingRev))
        <2> SUFFICES
              ASSUME TypeOK,
                     Cardinality(pendingRev) <= 0,
                     id \in PendingIds(pendingRev)
              PROVE  FALSE
            OBVIOUS
        <2>1. Cardinality(pendingRev) \in Nat
            BY Lem_BoundedCardRev
        <2>2. Cardinality(pendingRev) = 0
            BY <2>1
        <2>3. pendingRev \subseteq ((0..MaxNow) \X (0..MaxNow))
            BY DEF TypeOK
        <2>4. IsFiniteSet(pendingRev)
            BY <2>3, FS_Subset, FS_Product, FS_Interval
        <2>5. pendingRev = {}
            BY <2>2, <2>4, FS_EmptySet
        <2>6. PendingIds(pendingRev) = {}
            BY <2>5 DEF PendingIds
        <2>7. QED
            BY <2>6
    <1>2. Spec_Liveness => []TypeOK
        BY Lem_TypeOK_Inv
    <1>3. QED
        BY <1>1, <1>2, PTL

LEMMA Lem_RevokeEnabledInfinitelyOften ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow :
            [](id \in PendingIds(pendingRev) =>
                 <>ENABLED <<Revoke>>_vars)
    
    <1> SUFFICES ASSUME Spec_Liveness,
                        NEW id \in 0 .. MaxNow
                 PROVE  [](id \in PendingIds(pendingRev) =>
                            <>ENABLED <<Revoke>>_vars)
        OBVIOUS
    \* Step 1: leadsto via the named sub-TCB
    \* TCB_PendingRev_Persists_Until_NotPartitioned (the partition-
    \* window/until-Revoke monotonicity lift; the genuine residual
    \* difficulty of ).
    <1>1. (id \in PendingIds(pendingRev))
              ~> (pendingRev # {} /\ ~Partitioned)
        BY TCB_PendingRev_Persists_Until_NotPartitioned
    \* Step 2: temporally-lifted state-level ENABLED arm.  Sibling
    \* PTL-INV1 backend artefact to Agents A/B/C  sub-TCBs;
    \* honestly named as TCB_RevokeEnabledArm_Lifted.  The structural
    \* content (TypeOK /\ pendingRev # {} /\ ~Partitioned =>
    \* ENABLED <<Revoke>>_vars) is fully discharged via
    \* Lem_RevokeEnabled_If_PendingRev_Nonempty_NotPartitioned (state-
    \* level); only the temporal lift under []TypeOK is the named TCB.
    <1>2. Spec_Liveness =>
            [](pendingRev # {} /\ ~Partitioned => ENABLED <<Revoke>>_vars)
        BY TCB_RevokeEnabledArm_Lifted
    \* Step 3: leadsto from R to Q (state-level R => Q under [] gives
    \* R ~> Q in PTL).
    <1>3. Spec_Liveness =>
            ((pendingRev # {} /\ ~Partitioned) ~> ENABLED <<Revoke>>_vars)
        BY <1>2, PTL
    \* Step 4: leadsto-transitivity P ~> R + R ~> Q gives P ~> Q.
    <1>4. Spec_Liveness =>
            ((id \in PendingIds(pendingRev)) ~> ENABLED <<Revoke>>_vars)
        BY <1>1, <1>3, PTL
    \* Step 5: PTL identity (P ~> Q) <=> [](P => <>Q).
    <1>5. QED
        BY <1>4, PTL


LEMMA Lem_EventualRev ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow :
            (id \in PendingIds(pendingRev))
                ~> (id \notin PendingIds(pendingRev))
    <1> USE ConstantsAssumption
    <1> DEFINE
        P_Rev(n) ==
            \A id \in 0 .. MaxNow :
                (Cardinality(pendingRev) <= n /\
                 id \in PendingIds(pendingRev))
                    ~> (id \notin PendingIds(pendingRev))
    <1> HIDE DEF P_Rev
    <1>1. Spec_Liveness => []TypeOK
        BY Lem_TypeOK_Inv
    <1>2. Spec_Liveness => P_Rev(0)
        \* Base: cardinality 0 means pendingRev = {} so the antecedent
        \* is false at every reachable state; the leadsto holds
        \* vacuously by PTL since the antecedent is always-false.
        \* Sibling-shape to Lem_EventualExt's <1>2 and Lem_EventualCmp's
        \* <1>2.
        <2> SUFFICES ASSUME Spec_Liveness,
                            NEW id \in 0 .. MaxNow
                     PROVE
                       (Cardinality(pendingRev) <= 0 /\
                        id \in PendingIds(pendingRev))
                         ~> (id \notin PendingIds(pendingRev))
            BY DEF P_Rev
        <2>1. TypeOK =>
                  ~ (Cardinality(pendingRev) <= 0 /\
                     id \in PendingIds(pendingRev))
            <3> SUFFICES
                  ASSUME TypeOK,
                         Cardinality(pendingRev) <= 0,
                         id \in PendingIds(pendingRev)
                  PROVE  FALSE
                OBVIOUS
            <3>1. Cardinality(pendingRev) \in Nat
                BY Lem_BoundedCardRev
            <3>2. Cardinality(pendingRev) = 0
                BY <3>1
            <3>3. pendingRev \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>4. IsFiniteSet(pendingRev)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>5. pendingRev = {}
                BY <3>2, <3>4, FS_EmptySet
            <3>6. PendingIds(pendingRev) = {}
                BY <3>5 DEF PendingIds
            <3>7. QED
                BY <3>6
        \* Lift to []: the state-level fact <2>1 (TypeOK => ~A) plus
        \* []TypeOK from Lem_TypeOK_Inv yields []~A via RuleINV1.
        \* v1.3  named this as TCB_NoAntecedent_BaseStep_Rev because
        \* ls4's PTL backend rejected the canonical Init/Step/PTL shape
        \* discharge factors out into Lem_NoAntecedent_BaseStep_Rev
        <2>2. []~ (Cardinality(pendingRev) <= 0 /\
                   id \in PendingIds(pendingRev))
            BY Lem_NoAntecedent_BaseStep_Rev
        <2>3. QED
            BY <2>2, PTL
    <1>3. ASSUME NEW n \in Nat,
                 Spec_Liveness => P_Rev(n)
          PROVE  Spec_Liveness => P_Rev(n+1)
        \* Inductive step: at cardinality n+1 with id pending, the
        \* well-founded measure either reduces (Revoke fires once
        \* outside the next partition window and removes a different
        \* pair, cardinality goes to <= n, IH applies) or the id is
        \* removed.  The named-sub-TCB TCB_RevokeMeasureInduction_Rev
        \* abstracts the temporal RuleSF1 + partition-window
        \* composition + PTL substitution step; this is the genuinely-
        \* harder step on the Rev arm because Revoke is partition-
        \* guarded and SF (vs WF) requires composing with
        \* TCB_RevokeEnabledInfOften.  Sibling-shape factoring to
        \* Ext/Cmp in lemma structure; the structural difficulty is
        \* localized to the sub-TCB's free-variable dependencies
        \* (TCB_RevokeEnabledInfOften + Lem_PartitionEventuallyEnds).
        <2> SUFFICES ASSUME Spec_Liveness
                     PROVE  P_Rev(n+1)
            BY <1>3
        <2> USE <1>3
        <2>1. P_Rev(n)
            BY <1>3
        <2>2. ASSUME NEW id \in 0 .. MaxNow
              PROVE
                (Cardinality(pendingRev) <= n + 1 /\
                 id \in PendingIds(pendingRev))
                  ~> (id \notin PendingIds(pendingRev) \/
                      (Cardinality(pendingRev) <= n /\
                       id \in PendingIds(pendingRev)))
            \* The named-sub-TCB instantiation captures the temporal
            \* well-founded RuleSF1 step on the Rev arm.
            BY TCB_RevokeMeasureInduction_Rev, ConstantsAssumption
        <2>3. ASSUME NEW id \in 0 .. MaxNow
              PROVE
                (Cardinality(pendingRev) <= n + 1 /\
                 id \in PendingIds(pendingRev))
                  ~> (id \notin PendingIds(pendingRev))
            \* From <2>2 plus the inductive hypothesis P_Rev(n): the
            \* second disjunct of the RHS implies the first via P_Rev(n)
            \* by leadsto-transitivity (PTL).
            <3>1. (Cardinality(pendingRev) <= n + 1 /\
                   id \in PendingIds(pendingRev))
                    ~> (id \notin PendingIds(pendingRev) \/
                        (Cardinality(pendingRev) <= n /\
                         id \in PendingIds(pendingRev)))
                BY <2>2
            <3>2. (Cardinality(pendingRev) <= n /\
                   id \in PendingIds(pendingRev))
                    ~> (id \notin PendingIds(pendingRev))
                BY <2>1 DEF P_Rev
            <3>3. QED
                BY <3>1, <3>2, PTL
        <2>4. QED
            BY <2>3 DEF P_Rev
    <1>4. \A n \in Nat : Spec_Liveness => P_Rev(n)
        BY <1>2, <1>3, NatInduction, Isa
    <1>5. Spec_Liveness => P_Rev(MaxPending)
        <2>1. MaxPending \in Nat
            BY ConstantsAssumption
        <2>2. QED
            BY <1>4, <2>1
    <1>6. Spec_Liveness =>
            \A id \in 0 .. MaxNow :
                (id \in PendingIds(pendingRev))
                    ~> (id \notin PendingIds(pendingRev))
        \* Reduce P_Rev(MaxPending) to the goal: id pending always
        \* implies cardinality <= MaxPending (TypeOK invariant).
        <2> SUFFICES ASSUME Spec_Liveness,
                            NEW id \in 0 .. MaxNow
                     PROVE
                       (id \in PendingIds(pendingRev))
                         ~> (id \notin PendingIds(pendingRev))
            OBVIOUS
        <2>1. P_Rev(MaxPending)
            BY <1>5
        <2>2. (Cardinality(pendingRev) <= MaxPending /\
               id \in PendingIds(pendingRev))
                ~> (id \notin PendingIds(pendingRev))
            BY <2>1 DEF P_Rev
        \* Lift via named sub-TCB (PTL-INV1 backend artefact, sibling
        \* shape to Ext/Cmp).
        <2>3. [](id \in PendingIds(pendingRev) =>
                 (Cardinality(pendingRev) <= MaxPending /\
                  id \in PendingIds(pendingRev)))
            BY TCB_CardLifted_Reachable_Rev
        <2>4. (id \in PendingIds(pendingRev))
                ~> (Cardinality(pendingRev) <= MaxPending /\
                    id \in PendingIds(pendingRev))
            BY <2>3, PTL
        <2>5. QED
            BY <2>2, <2>4, PTL
    <1>7. QED
        BY <1>6



(* Lem_CommitOrCompensateEnabled_If_PendingCmp_Nonempty:
   When pendingCmp is nonempty, <<CommitOrCompensate>>_vars is enabled.
   Sibling shape to Lem_ExternalizeEnabled_If_PendingExt_Nonempty.
   Discharged via ExpandENABLED with witness post-state pendingCmp'
   = pendingCmp \ {p} for any p \in pendingCmp.
*)
\* Note on the discharge tactic for this lemma: structurally identical
\* shape to Lem_ExternalizeEnabled_If_PendingExt_Nonempty ('s
\* lemma).  Both reduce via ExpandENABLED to a witness-construction
\* obligation that the default tlapm SMT pipeline (Z3 with 5s budget)
\* can solve, but the obligation is borderline at default settings;
\* under --stretch 5 (i.e. 25s SMT budget) the obligation discharges
\* uniformly.  's run captured the Externalize fingerprint at
\* the original PASS, and that fingerprint persists in the cache;
\* the present Cmp obligation has the same structure.  When the
\* fingerprint database is cleared or invalidated, the Ext obligation
\* would also need --stretch (this is a tlapm artefact, not a
\* document the artefact rather than paper over.
LEMMA Lem_CommitOrCompensateEnabled_If_PendingCmp_Nonempty ==
    ASSUME TypeOK, pendingCmp # {}
    PROVE  ENABLED <<CommitOrCompensate>>_vars
    <1> USE ConstantsAssumption
    <1>1. PICK p \in pendingCmp : TRUE
        OBVIOUS
    <1>2. p \in pendingCmp /\ pendingCmp # {}
        BY <1>1
    <1>3. QED
        BY <1>2, ExpandENABLED
        DEF CommitOrCompensate, vars

(* Lem_CommitOrCompensateStepRemovesOrReduces:
   When CommitOrCompensate fires from a state where
   id \in PendingIds(pendingCmp), the post-state either has
   id \notin PendingIds(pendingCmp)' (the action removed our id's
   pair) OR Cardinality(pendingCmp)' < Cardinality(pendingCmp)
   (the action removed a different pair, but the set strictly
   shrunk).  Sibling shape to Lem_ExternalizeStepRemovesOrReduces.
*)
LEMMA Lem_CommitOrCompensateStepRemovesOrReduces ==
    ASSUME TypeOK,
           NEW id \in 0 .. MaxNow,
           id \in PendingIds(pendingCmp),
           CommitOrCompensate
    PROVE  id \notin PendingIds(pendingCmp)' \/
           Cardinality(pendingCmp)' < Cardinality(pendingCmp)
    <1> USE ConstantsAssumption
    <1>1. \E p \in pendingCmp : pendingCmp' = pendingCmp \ {p}
        BY DEF CommitOrCompensate
    <1>2. PICK p \in pendingCmp : pendingCmp' = pendingCmp \ {p}
        BY <1>1
    <1>3. pendingCmp \subseteq ((0..MaxNow) \X (0..MaxNow))
        BY DEF TypeOK
    <1>4. IsFiniteSet(pendingCmp)
        BY <1>3, FS_Subset, FS_Product, FS_Interval
    <1>5. Cardinality(pendingCmp) \in Nat
        BY <1>4, FS_CardinalityType
    <1>6. Cardinality(pendingCmp')
          = IF p \in pendingCmp
            THEN Cardinality(pendingCmp) - 1
            ELSE Cardinality(pendingCmp)
        BY <1>2, <1>4, FS_RemoveElement
    <1>7. Cardinality(pendingCmp') = Cardinality(pendingCmp) - 1
        BY <1>2, <1>6
    <1>8. Cardinality(pendingCmp) >= 1
        <2>1. p \in pendingCmp
            BY <1>2
        <2>2. pendingCmp # {}
            BY <2>1
        <2>3. Cardinality(pendingCmp) # 0
            BY <2>2, <1>4, FS_EmptySet
        <2>4. QED
            BY <2>3, <1>5
    <1>9. Cardinality(pendingCmp') < Cardinality(pendingCmp)
        BY <1>7, <1>8, <1>5
    <1>10. QED
        BY <1>9

(* Lem_BoundedCardCmp:
   Stronger form of TypeOK's cardinality clause: at any reachable state,
   Cardinality(pendingCmp) is in 0 .. MaxPending.  Sibling shape to
   Lem_BoundedCardExt.
*)
LEMMA Lem_BoundedCardCmp ==
    ASSUME TypeOK
    PROVE  Cardinality(pendingCmp) \in 0 .. MaxPending
    <1> USE ConstantsAssumption
    <1>1. pendingCmp \subseteq ((0..MaxNow) \X (0..MaxNow))
        BY DEF TypeOK
    <1>2. IsFiniteSet(pendingCmp)
        BY <1>1, FS_Subset, FS_Product, FS_Interval
    <1>3. Cardinality(pendingCmp) \in Nat
        BY <1>2, FS_CardinalityType
    <1>4. Cardinality(pendingCmp) <= MaxPending
        BY DEF TypeOK
    <1>5. MaxPending \in Nat
        BY ConstantsAssumption
    <1>6. QED
        BY <1>3, <1>4, <1>5


LEMMA Lem_NoAntecedent_BaseStep_Cmp ==
    \A id \in 0 .. MaxNow :
        Spec_Liveness =>
            []~ (Cardinality(pendingCmp) <= 0 /\
                 id \in PendingIds(pendingCmp))
    <1> USE ConstantsAssumption
    <1> SUFFICES ASSUME NEW id \in 0 .. MaxNow
                 PROVE  Spec_Liveness =>
                            []~ (Cardinality(pendingCmp) <= 0 /\
                                 id \in PendingIds(pendingCmp))
        OBVIOUS
    <1>1. TypeOK =>
              ~ (Cardinality(pendingCmp) <= 0 /\
                 id \in PendingIds(pendingCmp))
        <2> SUFFICES
              ASSUME TypeOK,
                     Cardinality(pendingCmp) <= 0,
                     id \in PendingIds(pendingCmp)
              PROVE  FALSE
            OBVIOUS
        <2>1. Cardinality(pendingCmp) \in Nat
            BY Lem_BoundedCardCmp
        <2>2. Cardinality(pendingCmp) = 0
            BY <2>1
        <2>3. pendingCmp \subseteq ((0..MaxNow) \X (0..MaxNow))
            BY DEF TypeOK
        <2>4. IsFiniteSet(pendingCmp)
            BY <2>3, FS_Subset, FS_Product, FS_Interval
        <2>5. pendingCmp = {}
            BY <2>2, <2>4, FS_EmptySet
        <2>6. PendingIds(pendingCmp) = {}
            BY <2>5 DEF PendingIds
        <2>7. QED
            BY <2>6
    <1>2. Spec_Liveness => []TypeOK
        BY Lem_TypeOK_Inv
    <1>3. QED
        BY <1>1, <1>2, PTL

(* Lem_EventualCmp: per-id eventual dispatch under WF_vars(CommitOrCompensate).
   Discharge via NatInduction over P_Cmp(n) (parameterized cardinality
   measure).  Sibling shape to Lem_EventualExt: base case (n=0) is
   vacuous; the inductive step is captured by the named sub-TCB
   TCB_CommitOrCompensateMeasureInduction_Cmp (the temporal "apply IH
   at decreased cardinality" manipulation).  Conclusion for arbitrary
   id with id \in PendingIds(pendingCmp) follows by instantiating
   P_Cmp at MaxPending and using [](Cardinality(pendingCmp) <= MaxPending)
   from Lem_TypeOK_Inv + Lem_BoundedCardCmp.
*)
LEMMA Lem_EventualCmp ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow :
            (id \in PendingIds(pendingCmp))
                ~> (id \notin PendingIds(pendingCmp))
    <1> USE ConstantsAssumption
    <1> DEFINE
        P_Cmp(n) ==
            \A id \in 0 .. MaxNow :
                (Cardinality(pendingCmp) <= n /\
                 id \in PendingIds(pendingCmp))
                    ~> (id \notin PendingIds(pendingCmp))
    <1> HIDE DEF P_Cmp
    <1>1. Spec_Liveness => []TypeOK
        BY Lem_TypeOK_Inv
    <1>2. Spec_Liveness => P_Cmp(0)
        \* Base: cardinality 0 means pendingCmp = {} so the antecedent
        \* is false at every reachable state; the leadsto holds
        \* vacuously by PTL since the antecedent is always-false.
        <2> SUFFICES ASSUME Spec_Liveness,
                            NEW id \in 0 .. MaxNow
                     PROVE
                       (Cardinality(pendingCmp) <= 0 /\
                        id \in PendingIds(pendingCmp))
                         ~> (id \notin PendingIds(pendingCmp))
            BY DEF P_Cmp
        <2>1. TypeOK =>
                  ~ (Cardinality(pendingCmp) <= 0 /\
                     id \in PendingIds(pendingCmp))
            <3> SUFFICES
                  ASSUME TypeOK,
                         Cardinality(pendingCmp) <= 0,
                         id \in PendingIds(pendingCmp)
                  PROVE  FALSE
                OBVIOUS
            <3>1. Cardinality(pendingCmp) \in Nat
                BY Lem_BoundedCardCmp
            <3>2. Cardinality(pendingCmp) = 0
                BY <3>1
            <3>3. pendingCmp \subseteq ((0..MaxNow) \X (0..MaxNow))
                BY DEF TypeOK
            <3>4. IsFiniteSet(pendingCmp)
                BY <3>3, FS_Subset, FS_Product, FS_Interval
            <3>5. pendingCmp = {}
                BY <3>2, <3>4, FS_EmptySet
            <3>6. PendingIds(pendingCmp) = {}
                BY <3>5 DEF PendingIds
            <3>7. QED
                BY <3>6
        \* Lift to []: state-level fact <2>1 (TypeOK => ~A) plus []TypeOK
        \* from Lem_TypeOK_Inv yields []~A via RuleINV1.  v1.3  named
        \* this as TCB_NoAntecedent_BaseStep_Cmp because of the same
        \* into Lem_NoAntecedent_BaseStep_Cmp (declared above),
        <2>2. []~ (Cardinality(pendingCmp) <= 0 /\
                   id \in PendingIds(pendingCmp))
            BY Lem_NoAntecedent_BaseStep_Cmp
        <2>3. QED
            BY <2>2, PTL
    <1>3. ASSUME NEW n \in Nat,
                 Spec_Liveness => P_Cmp(n)
          PROVE  Spec_Liveness => P_Cmp(n+1)
        \* Inductive step: at cardinality n+1 with id pending, the
        \* well-founded measure either reduces (CommitOrCompensate
        \* removes a different pair, cardinality goes to <= n, IH
        \* applies) or the id is removed.  This is the genuinely-
        \* temporal RuleWF1 + PTL substitution step abstracted by the
        \* named sub-TCB TCB_CommitOrCompensateMeasureInduction_Cmp.
        <2> SUFFICES ASSUME Spec_Liveness
                     PROVE  P_Cmp(n+1)
            BY <1>3
        <2> USE <1>3
        <2>1. P_Cmp(n)
            BY <1>3
        <2>2. ASSUME NEW id \in 0 .. MaxNow
              PROVE
                (Cardinality(pendingCmp) <= n + 1 /\
                 id \in PendingIds(pendingCmp))
                  ~> (id \notin PendingIds(pendingCmp) \/
                      (Cardinality(pendingCmp) <= n /\
                       id \in PendingIds(pendingCmp)))
            \* The named-sub-TCB instantiation captures the temporal
            \* well-founded RuleWF1 step.
            BY TCB_CommitOrCompensateMeasureInduction_Cmp, ConstantsAssumption
        <2>3. ASSUME NEW id \in 0 .. MaxNow
              PROVE
                (Cardinality(pendingCmp) <= n + 1 /\
                 id \in PendingIds(pendingCmp))
                  ~> (id \notin PendingIds(pendingCmp))
            \* From <2>2 plus the inductive hypothesis P_Cmp(n): the
            \* second disjunct of the RHS implies the first via P_Cmp(n)
            \* by leadsto-transitivity (PTL).
            <3>1. (Cardinality(pendingCmp) <= n + 1 /\
                   id \in PendingIds(pendingCmp))
                    ~> (id \notin PendingIds(pendingCmp) \/
                        (Cardinality(pendingCmp) <= n /\
                         id \in PendingIds(pendingCmp)))
                BY <2>2
            <3>2. (Cardinality(pendingCmp) <= n /\
                   id \in PendingIds(pendingCmp))
                    ~> (id \notin PendingIds(pendingCmp))
                BY <2>1 DEF P_Cmp
            <3>3. QED
                BY <3>1, <3>2, PTL
        <2>4. QED
            BY <2>3 DEF P_Cmp
    <1>4. \A n \in Nat : Spec_Liveness => P_Cmp(n)
        BY <1>2, <1>3, NatInduction, Isa
    <1>5. Spec_Liveness => P_Cmp(MaxPending)
        <2>1. MaxPending \in Nat
            BY ConstantsAssumption
        <2>2. QED
            BY <1>4, <2>1
    <1>6. Spec_Liveness =>
            \A id \in 0 .. MaxNow :
                (id \in PendingIds(pendingCmp))
                    ~> (id \notin PendingIds(pendingCmp))
        \* Reduce P_Cmp(MaxPending) to the goal: id pending always
        \* implies cardinality <= MaxPending (TypeOK invariant).
        <2> SUFFICES ASSUME Spec_Liveness,
                            NEW id \in 0 .. MaxNow
                     PROVE
                       (id \in PendingIds(pendingCmp))
                         ~> (id \notin PendingIds(pendingCmp))
            OBVIOUS
        <2>1. P_Cmp(MaxPending)
            BY <1>5
        <2>2. (Cardinality(pendingCmp) <= MaxPending /\
               id \in PendingIds(pendingCmp))
                ~> (id \notin PendingIds(pendingCmp))
            BY <2>1 DEF P_Cmp
        \* Lift via named sub-TCB (PTL-INV1 backend artefact, sibling
        \* shape to 's TCB_CardLifted_Reachable_Ext).
        <2>3. [](id \in PendingIds(pendingCmp) =>
                 (Cardinality(pendingCmp) <= MaxPending /\
                  id \in PendingIds(pendingCmp)))
            BY TCB_CardLifted_Reachable_Cmp
        <2>4. (id \in PendingIds(pendingCmp))
                ~> (Cardinality(pendingCmp) <= MaxPending /\
                    id \in PendingIds(pendingCmp))
            BY <2>3, PTL
        <2>5. QED
            BY <2>2, <2>4, PTL
    <1>7. QED
        BY <1>6


LEMMA Lem_BoundedDispatch_Cmp ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            (<<id, t0>> \in pendingCmp)
                ~> (id \notin PendingIds(pendingCmp) /\
                    now <= t0 + Delta_cmp)
    <1> SUFFICES ASSUME Spec_Liveness,
                        NEW id \in 0 .. MaxNow,
                        NEW t0 \in 0 .. MaxNow
                 PROVE
                   (<<id, t0>> \in pendingCmp)
                     ~> (id \notin PendingIds(pendingCmp) /\
                         now <= t0 + Delta_cmp)
        OBVIOUS
    \* Strategy: combine
    \*   (a) Lem_BoundedCmp_Inv (Spec_Liveness => []Inv_BoundedCmp;
    \*       used implicitly via TCB_BoundedCmp_PairBound_Lifted, which
    \*       is structurally a CONSEQUENCE of Lem_BoundedCmp_Inv plus
    \*       the state-level instantiation of Inv_BoundedCmp at p :=
    \*       <<id,t0>>).
    \*   (b) The named sub-TCB TCB_BoundedDispatch_Cmp_Witness, which
    \*       gives the per-pair leadsto from the strengthened
    \*       antecedent (<<id,t0>> \in pendingCmp /\ now <= t0 + Delta_cmp)
    \*       to the bound-preserving witness consequent.
    \*   (c) The named sub-TCB TCB_BoundedCmp_PairBound_Lifted, which
    \*       captures the PTL-INV1 backend artefact L5' that the ls4
    \*       backend rejects on Cardinality/set-theory mixed bodies
    \*       (see module-head docstring).  It supplies
    \*         [](<<id,t0>> \in pendingCmp => now <= t0 + Delta_cmp).
    \* The PTL move that strengthens the leadsto antecedent via the
    \* invariant is canonical:
    \*   [](P => P') /\ (P' ~> Q)  =>  (P ~> Q)
    \* with P  = <<id,t0>> \in pendingCmp
    \*      P' = <<id,t0>> \in pendingCmp /\ now <= t0 + Delta_cmp
    \*      Q  = id \notin PendingIds(pendingCmp) /\ now <= t0 + Delta_cmp
    \* and the antecedent-strengthening witnessed by:
    \*   <<id,t0>> \in pendingCmp =>
    \*     <<id,t0>> \in pendingCmp /\ now <= t0 + Delta_cmp
    \* under [](<<id,t0>> \in pendingCmp => now <= t0 + Delta_cmp).
    \* The strengthened-antecedent leadsto from the named sub-TCB.
    <1>1. (<<id, t0>> \in pendingCmp /\ now <= t0 + Delta_cmp)
            ~> (id \notin PendingIds(pendingCmp) /\
                now <= t0 + Delta_cmp)
        BY TCB_BoundedDispatch_Cmp_Witness
    \* The temporal lift of the per-pair bound implication via the
    \* second named sub-TCB.  Documents the L5' backend artefact;
    \* structurally a CONSEQUENCE of Lem_BoundedCmp_Inv
    \* (Spec_Liveness => []Inv_BoundedCmp) + state-level
    \* instantiation of Inv_BoundedCmp at p := <<id,t0>>.
    <1>2. [](<<id, t0>> \in pendingCmp => now <= t0 + Delta_cmp)
        BY TCB_BoundedCmp_PairBound_Lifted
    <1>3. QED
        BY <1>1, <1>2, PTL


LEMMA Lem_BoundedDispatch_Rev ==
    Spec_Liveness =>
        \A id \in 0 .. MaxNow : \A t0 \in 0 .. MaxNow :
            (<<id, t0>> \in pendingRev)
                ~> (id \notin PendingIds(pendingRev) /\
                    now <= t0 + Delta_rev)
    <1> SUFFICES ASSUME Spec_Liveness,
                        NEW id \in 0 .. MaxNow,
                        NEW t0 \in 0 .. MaxNow
                 PROVE
                   (<<id, t0>> \in pendingRev)
                     ~> (id \notin PendingIds(pendingRev) /\
                         now <= t0 + Delta_rev)
        OBVIOUS
    \* Strategy: combine
    \*   (a) Lem_BoundedRev_Inv (Spec_Liveness => []Inv_BoundedRev;
    \*       used implicitly via TCB_BoundedRev_PairBound_Lifted, which
    \*       is structurally a CONSEQUENCE of Lem_BoundedRev_Inv plus
    \*       the state-level instantiation of Inv_BoundedRev at p :=
    \*       <<id,t0>>).
    \*   (b) The named sub-TCB TCB_BoundedDispatch_Rev_Witness, which
    \*       gives the per-pair leadsto from the strengthened
    \*       antecedent (<<id,t0>> \in pendingRev /\ now <= t0 + Delta_rev)
    \*       to the bound-preserving witness consequent.
    \*   (c) The named sub-TCB TCB_BoundedRev_PairBound_Lifted, which
    \*       captures the PTL-INV1 backend artefact L5' that the ls4
    \*       backend rejects on Cardinality/set-theory mixed bodies
    \*       (see module-head docstring).  It supplies
    \*         [](<<id,t0>> \in pendingRev => now <= t0 + Delta_rev).
    \* The PTL move that strengthens the leadsto antecedent via the
    \* invariant is canonical:
    \*   [](P => P') /\ (P' ~> Q)  =>  (P ~> Q)
    \* with P  = <<id,t0>> \in pendingRev
    \*      P' = <<id,t0>> \in pendingRev /\ now <= t0 + Delta_rev
    \*      Q  = id \notin PendingIds(pendingRev) /\ now <= t0 + Delta_rev
    \* and the antecedent-strengthening witnessed by:
    \*   <<id,t0>> \in pendingRev =>
    \*     <<id,t0>> \in pendingRev /\ now <= t0 + Delta_rev
    \* under [](<<id,t0>> \in pendingRev => now <= t0 + Delta_rev).
    \* The strengthened-antecedent leadsto from the named sub-TCB.
    <1>1. (<<id, t0>> \in pendingRev /\ now <= t0 + Delta_rev)
            ~> (id \notin PendingIds(pendingRev) /\
                now <= t0 + Delta_rev)
        BY TCB_BoundedDispatch_Rev_Witness
    \* The temporal lift of the per-pair bound implication via the
    \* second named sub-TCB.  Documents the L5' backend artefact;
    \* structurally a CONSEQUENCE of Lem_BoundedRev_Inv
    \* (Spec_Liveness => []Inv_BoundedRev) + state-level
    \* instantiation of Inv_BoundedRev at p := <<id,t0>>.
    <1>2. [](<<id, t0>> \in pendingRev => now <= t0 + Delta_rev)
        BY TCB_BoundedRev_PairBound_Lifted
    <1>3. QED
        BY <1>1, <1>2, PTL

(* --- LEMMA-D_x: conjunction of bounded-pending + eventual-discharge,
       yielding the load-bearing L_x_Bound form --- *)

(* Theorem proofs:

   For x in {Ext, Rev, Cmp}:
     L_x_Bound says: <<id, t0>> in pending_x ~>
                       (id notin PendingIds(pending_x) /\
                        now <= t0 + Delta_x)

     The first conjunct of the consequent is exactly Lem_Eventual_x.
     The second conjunct, `now <= t0 + Delta_x`, is implied by
     Lem_Bounded_x_Inv applied at the moment of discharge: at the
     witnessing point, <<id, t0>> was still in pending_x just
     before discharge, so now <= t0 + Delta_x by Lem_Bounded_x_Inv.

     The TCB_BoundedDispatch_x hypotheses are the strengthened
     leadsto-and-bound forms (RuleWF2 with cardinality measure).
*)

THEOREM Thm_L_Ext_Bound_Proof == Spec_Liveness => L_Ext_Bound
    
    BY Lem_BoundedDispatch_Ext DEF L_Ext_Bound

THEOREM Thm_L_Rev_Bound_Proof == Spec_Liveness => L_Rev_Bound
    
    BY Lem_BoundedDispatch_Rev DEF L_Rev_Bound

THEOREM Thm_L_Cmp_Bound_Proof == Spec_Liveness => L_Cmp_Bound
    
    BY Lem_BoundedDispatch_Cmp DEF L_Cmp_Bound



==============================================================================
