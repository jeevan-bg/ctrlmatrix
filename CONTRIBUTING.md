# Contributing

Thanks for your interest in CTRLMATRIX. The project is currently maintained
as a single-author research artifact; external contributions are welcome but
should follow the conventions below.

## Filing an issue

For bugs in the substrate (Lean, TLA+, Rust conformance), please include:

- A minimal reproducer (the smallest event sequence or theorem statement
 that exhibits the bug)
- The toolchain versions you used (`lean --version`, `cargo --version`,
 `tlapm --version`)
- Whether the bug is observed in `lake build`, `lake env lean MeasureAxioms`,
 `cargo test --release --all-features`, or `tlapm`

For documentation or naming clarifications, prose-only issues are fine.

## Pull requests

The project enforces strict invariants on the substrate. Before opening a PR
that touches `lean/`, `tla/`, `conformance/`, or `verus/`, please discuss
the change in an issue first. Drive-by PRs that bypass the invariants will
be closed.

Concretely, the substrate enforces:

- **No new axioms in baseline** (Tier 4 axiom-free invariant; the
 `MeasureAxioms.lean` baseline must not regress)
- **No silent tier elevation** (Tier 1 → Tier 2, Tier 2 → Tier 3, etc. must
 be explicit and accompanied by a brief note)
- **No new fairness assumptions** in TLA+ liveness without a corresponding
 obligation discharge

A PR that changes a file under `lean/AgentKernel/` MUST update
`lean/AgentKernel.lean` in the same commit if a new module is introduced
(umbrella-completeness invariant).

## Build verification before submitting

```
cd lean && lake build && lake env lean MeasureAxioms.lean
cd../conformance && cargo test --release --all-features
cd../tla && tlapm --stretch 5 LivenessProof.tla # if you touched TLA+
```

All three must be green at HEAD.

## Code style

- **Lean:** match the existing module style; prefer `theorem` for named
 results, `lemma` for stepping stones, `def`/`abbrev` for helper
 definitions; avoid `Classical.choice` outside the existing
 outside-baseline tier.
- **TLA+:** match the existing operator-naming style; place `ASSUME`s
 alongside relevant operator definitions, not in a separate block.
- **Rust:** rustfmt default; clippy clean; prefer `proptest!` macros
 for new property tests.

## Licensing

All contributions are accepted under the project's Apache-2.0 license. By
submitting a contribution, you affirm that you have the right to do so and
that you grant the project a perpetual, worldwide license under those terms.
