# CTRLMATRIX

> Verified L0 substrate for AI agents.

CTRLMATRIX is a formally specified ground floor (L0) for AI-agent runtimes:
information-flow control, deterministic replay, capability-based delegation,
audit-log hash chains, and bridge theorems linking the substrate to a TLA+
operational specification.

This repository is the live implementation. For the paper bundle frozen at
the most recent paper version, see
[`ctrlmatrix-paper`](https://github.com/jeevan-bg/ctrlmatrix-paper).

## What's in this repository

| Directory | Contents |
|---|---|
| `lean/` | Lean 4 mechanization — substrate (IFC, Replay, Caps, System, Causality, Log) and bridge theorems |
| `tla/` | TLA+ specifications and TLAPS proofs of operational liveness |
| `conformance/` | Rust property-test crate exercising the substrate alphabet |
| `verus/` | Verus-Rust spec-as-code for refinement (in progress) |

## Quick start

### Lean
```
cd lean
lake build
lake env lean MeasureAxioms.lean # prints axiom envelope per named theorem
```

### TLA+ / TLAPS
```
cd tla
tlapm --stretch 5 LivenessProof.tla
```

### Rust conformance suite
```
cd conformance
cargo test --release --all-features
```

### Verus (when present)
```
cd verus
verus --version # see verus-version.txt for the pinned version
cargo build
```

See [`INSTALL.md`](INSTALL.md) for full toolchain setup.

## Status

| Component | State |
|---|---|
| Lean substrate (IFC, Replay, Caps, System, Causality, Log) | stable |
| Bridge theorems M1..M8, MultiCell, Liveness, Universal | stable |
| TLA+ + TLAPS liveness proofs | stable |
| Rust conformance suite | stable |
| Verus-Rust refinement | in progress |

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Security

See [`SECURITY.md`](SECURITY.md) for the security disclosure policy.

## License

Apache-2.0. See [`LICENSE`](LICENSE).
