//!
//! Tests `well_formed_replay_mode` mirror of Lean predicate
//! `Event.wellFormedReplayMode` (lean/AgentKernel/Replay.lean
//! L1006-1008). 2-clause predicate:
//!
//! - Clause (a): `kind.isKernelEmit = true → mode = Mode.live` —
//!   kernel-emit events cannot be replays (kernel I/O endpoints
//!   never replay; replay machinery must skip kernel-emit events).
//! - Clause (b): `mode = Mode.replay → ¬kind.isObservable` —
//!   replay events cannot publish observable side-effects.
//!
//!
//! The σ_min wrapper-layer `KindExt` enum collectively abstracts
//! Lean's per-member `Kind` partition (`isKernelEmit = {externalReq,
//! externalResp, read}`; `isObservable = {externalReq, commit,
//! attest}`). The σ_min predicate enforces the partition shapes,
//! NOT per-Lean-member runtime authority — that is L1+ TCB.
//!
//!
//! 1. Default-`Live` legacy event ACCEPT (default-vacuity, mirrors
//!    `wellFormedReplayMode_default_event_holds`).
//! 2. Replay-mode kernel-emit REJECT (clause (a) falsifier).
//! 3. Replay-mode observable REJECT (clause (b) falsifier).
//! 4. Replay-mode non-kernel-emit non-observable ACCEPT
//!    (`Plan`/`Exec`/`Refusal`/`ContractViolation` etc. as
//!    structurally permitted replay subjects).
//!    documented; per-event predicate accepts).
//!
//! is L1+, not L0).

use ctrlmatrix_conformance::generators::{
    live_event, replay_event, replay_kernel_emit_event, replay_observable_event,
    trace_well_formed_replay_mode, well_formed_replay_mode, Kind, KindExt, KernelEvent,
    KernelEventWithMode, ModeTrace,
};

/// Helper: construct a baseline `KernelEvent` with `Kind::Other`.
fn baseline_event(event_id: u64) -> KernelEvent {
    KernelEvent {
        event_id,
        kind: Kind::Other,
        kernel_authored: false,
        spawned_by: None,
        retract_target: None,
        parents: vec![],
    }
}

// Scenario 1 — default-`Live` legacy event ACCEPT
// Mirrors Lean `wellFormedReplayMode_default_event_holds`.

#[test]
fn default_live_legacy_event_accepted() {
    let e: KernelEventWithMode = live_event(baseline_event(0), None);
    assert!(
        well_formed_replay_mode(&e),
        "default-Live legacy event must vacuously satisfy well_formed_replay_mode \
         (mirrors Lean wellFormedReplayMode_default_event_holds)"
    );
}

#[test]
fn default_live_with_kernel_emit_kindext_accepted() {
    // Live + KernelEmit: clause (a) holds (mode = Live); clause (b)
    // vacuous (mode ≠ Replay). MUST ACCEPT.
    let e: KernelEventWithMode = live_event(baseline_event(0), Some(KindExt::KernelEmit));
    assert!(
        well_formed_replay_mode(&e),
        "live-mode kernel-emit event must accept (clause (a) holds via mode = Live)"
    );
}

#[test]
fn default_live_with_observable_kindext_accepted() {
    // Live + Observable: clause (a) trivial (¬kernel-emit); clause
    // (b) vacuous (mode ≠ Replay). MUST ACCEPT.
    let e: KernelEventWithMode = live_event(baseline_event(0), Some(KindExt::Observable));
    assert!(
        well_formed_replay_mode(&e),
        "live-mode observable event must accept"
    );
}

// Scenario 2 — replay-mode kernel-emit REJECT (clause (a) falsifier)

#[test]
fn replay_with_kernel_emit_rejected() {
    let e: KernelEventWithMode = replay_kernel_emit_event(0);
    assert!(
        !well_formed_replay_mode(&e),
        "replay-mode kernel-emit event MUST be rejected by clause (a) \
         (kernel-emit events cannot be replays L0 spec)"
    );
}

// Scenario 3 — replay-mode observable REJECT (clause (b) falsifier)

#[test]
fn replay_with_observable_rejected() {
    let e: KernelEventWithMode = replay_observable_event(0);
    assert!(
        !well_formed_replay_mode(&e),
        "replay-mode observable event MUST be rejected by clause (b) \
         (replay events cannot publish observable side-effects L0 spec)"
    );
}

// Scenario 4 — replay-mode non-kernel-emit non-observable ACCEPT

#[test]
fn replay_non_kernel_emit_non_observable_accepted() {
    // Plan / Exec / Refusal / ContractViolation / Spawn / Retract /
    // Other are all non-kernel-emit AND non-observable at σ_min.
    // Replay-mode for these is structurally permitted.
    for kind_ext in [
        KindExt::Plan,
        KindExt::Exec,
        KindExt::Refusal,
        KindExt::ContractViolation,
        KindExt::Spawn,
        KindExt::Retract,
        KindExt::Other,
    ] {
        let e: KernelEventWithMode = replay_event(baseline_event(0), Some(kind_ext));
        assert!(
            well_formed_replay_mode(&e),
            "replay-mode {:?} event must accept (non-kernel-emit, non-observable)",
            kind_ext
        );
    }
}

// Scenario 5 — mixed-mode trace at trace lift
// mixed-mode traces; longitudinal mode-coherence is L1+ kernel-runtime
// obligation.

#[test]
fn mixed_mode_trace_accepted_at_trace_lift() {
    // Trace: [live_other, replay_plan, live_observable, replay_refusal].
    // Each event individually well-formed; trace-level lift accepts.
    let trace: ModeTrace = vec![
        live_event(baseline_event(0), None),
        replay_event(baseline_event(1), Some(KindExt::Plan)),
        live_event(baseline_event(2), Some(KindExt::Observable)),
        replay_event(baseline_event(3), Some(KindExt::Refusal)),
    ];
    assert!(
        trace_well_formed_replay_mode(&trace),
        "mixed-mode trace must accept at trace lift (per-event predicate; \
         L1+ residual [ref]: longitudinal coherence is kernel-runtime)"
    );
}

#[test]
fn trace_with_replay_kernel_emit_rejected_at_trace_lift() {
    // Trace lift must FAIL if any single event fails the per-event
    // predicate. Mirrors Lean `Trace.wellFormedReplayMode` ∀-shape.
    let trace: ModeTrace = vec![
        live_event(baseline_event(0), None),
        replay_kernel_emit_event(1), // <-- clause (a) falsifier
        live_event(baseline_event(2), None),
    ];
    assert!(
        !trace_well_formed_replay_mode(&trace),
        "trace containing a replay-mode kernel-emit event MUST be rejected at trace lift"
    );
}

// =====================================================================
// =====================================================================
//
// ~5–6 NEW property tests covering `well_formed_replay_mode`'s
// 2-clause shape. Existing 9 example-based scenarios above are
// PRESERVED.

use proptest::prelude::*;

fn strategy_kind_ext() -> impl Strategy<Value = KindExt> {
    prop_oneof![
        Just(KindExt::Other),
        Just(KindExt::Spawn),
        Just(KindExt::Retract),
        Just(KindExt::Plan),
        Just(KindExt::Exec),
        Just(KindExt::Refusal),
        Just(KindExt::ContractViolation),
        Just(KindExt::KernelEmit),
        Just(KindExt::Observable),
        Just(KindExt::HumanGate),
    ]
}

proptest! {
    /// Property 1 (clause (a) — replay-mode kernel-emit ALWAYS rejected).
    #[test]
    fn prop_replay_kernel_emit_rejected(event_id in 0u64..1000) {
        let e = replay_kernel_emit_event(event_id);
        prop_assert!(!well_formed_replay_mode(&e));
    }

    /// Property 2 (clause (b) — replay-mode observable ALWAYS rejected).
    #[test]
    fn prop_replay_observable_rejected(event_id in 0u64..1000) {
        let e = replay_observable_event(event_id);
        prop_assert!(!well_formed_replay_mode(&e));
    }

    /// Property 3 (clause (a)/(b) positive — live-mode is always
    /// well-formed regardless of kind_ext).
    #[test]
    fn prop_live_mode_always_accepted(
        event_id in 0u64..1000,
        kind_ext in strategy_kind_ext(),
    ) {
        let e = live_event(baseline_event(event_id), Some(kind_ext));
        prop_assert!(well_formed_replay_mode(&e));
    }

    /// Property 4 (clause (b) positive — replay + non-observable +
    /// non-kernel-emit ALWAYS accepted).
    #[test]
    fn prop_replay_non_kernelemit_non_observable_accepted(
        event_id in 0u64..1000,
        kind_ext in prop_oneof![
            Just(KindExt::Other),
            Just(KindExt::Spawn),
            Just(KindExt::Retract),
            Just(KindExt::Plan),
            Just(KindExt::Exec),
            Just(KindExt::Refusal),
            Just(KindExt::ContractViolation),
            Just(KindExt::HumanGate),
        ],
    ) {
        let e = replay_event(baseline_event(event_id), Some(kind_ext));
        prop_assert!(well_formed_replay_mode(&e));
    }

    /// Property 5 (trace contamination — any replay-kernel-emit event
    /// in trace fails the lift).
    #[test]
    fn prop_trace_with_replay_kernel_emit_rejected(
        good_id in 0u64..500,
        bad_id in 500u64..1000,
    ) {
        prop_assume!(good_id != bad_id);
        let trace: ModeTrace = vec![
            live_event(baseline_event(good_id), None),
            replay_kernel_emit_event(bad_id),
        ];
        prop_assert!(!trace_well_formed_replay_mode(&trace));
    }

    /// Property 6 (trace lift — all-live-mode trace ALWAYS accepted).
    #[test]
    fn prop_trace_all_live_accepted(events_count in 1usize..6) {
        let trace: ModeTrace = (0..events_count as u64)
            .map(|i| live_event(baseline_event(i), None))
            .collect();
        prop_assert!(trace_well_formed_replay_mode(&trace));
    }
}
