# Security policy

## Reporting a vulnerability

If you believe you have found a security vulnerability in CTRLMATRIX —
either in the substrate proofs, the conformance suite, or in the way the
substrate could be misused as a foundation for a higher-layer runtime —
please report it privately rather than opening a public issue.

Email: jeevan0923@gmail.com

Please include:

- A description of the vulnerability
- A minimal reproducer (concrete event sequence, theorem statement, or
 configuration that exhibits the issue)
- The toolchain versions you used
- Your suggested classification of the issue (substrate-bug,
 conformance-suite-gap, documentation-issue, etc.)

You can expect an acknowledgement within seven days.

## Scope

The substrate is a verified specification of an L0 ground floor for AI-agent
runtimes. The verification artifacts (Lean, TLA+, Rust conformance suite)
are in scope.

Out of scope:

- Vulnerabilities in higher-layer L1+ runtimes that consume the substrate
 (those should be reported to the runtime maintainer)
- Issues in third-party dependencies (those should be reported upstream)

## Handling

Confirmed substrate vulnerabilities are addressed with the same discipline
as other substrate changes:

1. Reproduce the issue with a property test or a concrete proof obligation.
2. Land the fix as a substrate edit with full build-gate verification.
3. Document the fix in a public commit on `main` once the fix is shipped.

There is no embargo period; once a fix is committed and pushed, the
vulnerability is considered public.

## Past advisories

None at this time.
