# trust-core-profile-tests: real producer output (profile-negative tests)

This is the same build as `trust-core-bytes` (core #125 at `d5d8f78c`), dumped with
`--module Silmaril.Prelude.Trust.Examples`. That module tests the profiles, and the dump is
audited at `default`. The core's own audit lines list 9 violations, and the recomputed audit
agrees:

- **6 native runs outside `default`:** they ran under `local`, under a named set, or through the
  paired or declared forms. Their `elaborated_profiles` still show the profile they ran under,
  but a theorem elaborated under `local` stays a violation in a `default` artifact.
- **3 unverified native axioms:** `byDecideNative` (matches `test.decideNative` by name only),
  and the core's forgery tests `forgedDecl` and `forgedShape` (records that the exact-head audit
  rejects).
- **1 mismatched use record:** `forgedShape`'s recorded use names an axiom that is not a native
  run of its procedure (`test.lengthNative`). The record is kept with `axiom_matches = 0`,
  reported, and authorizes nothing; under `--strict-trust` it is an error.
