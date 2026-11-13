# trust-core-profile-tests: real producer output (profile-negative and forgery tests)

This is the same build as `trust-core-bytes` (#125 at `d5d8f78c`), exported with
`sil project trust-dump --module Silmaril.Prelude.Trust.Examples`, and audited at `default`.

The export lists **9 violations**, and the recomputed audit agrees:

- **6 native runs outside `default`:** they ran under `local`, under a named set, or through the
  paired or declared forms. The audit profile governs, whatever profile the run elaborated under.
- **3 unverified native axioms:** `byDecideNative`, and the core's forgery tests `forgedDecl` and
  `forgedShape`.

Separately, the use records of `forgedDecl` and `forgedShape` are kept and flagged: the core marks
them `verified = false`, and `forgedShape`'s axiom is not a native run of its procedure. They
authorize nothing, and `--strict-trust` fails on them as well as on the violations.
