# Install

CTRLMATRIX has four toolchains: Lean 4, TLAPS, Rust, and (optionally) Verus.
You only need the toolchains for the parts you want to verify.

## Lean 4

The pinned toolchain is in `lean/lean-toolchain`. Use `elan` (the official
Lean version manager):

```
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
source "$HOME/.elan/env"
cd lean
lake build
```

`elan` reads `lean/lean-toolchain` automatically and downloads the right
Lean version.

To print the axiom envelope per named theorem:

```
cd lean
lake env lean MeasureAxioms.lean
```

## TLA+ / TLAPS

Install instructions (canonical): https://github.com/tlaplus/tlapm

Quick start on macOS:

```
brew install opam
opam init -y
opam install -y tlapm
```

Then:

```
cd tla
tlapm --stretch 5 LivenessProof.tla
```

## Rust

Stable Rust (any recent version):

```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Then:

```
cd conformance
cargo test --release --all-features
```

229 tests pass at substrate-stable HEAD across 17 binaries.

## Verus (when present)

Verus pin in `verus/verus-version.txt`. Verus install instructions:
https://github.com/verus-lang/verus

```
cd verus
verus --version
cargo build
```

## CI parity

Continuous integration runs the same commands in `.github/workflows/ci.yml`
on every push. Local-vs-CI parity is the convention; if a build passes
locally but fails in CI, the CI configuration is the ground truth.
