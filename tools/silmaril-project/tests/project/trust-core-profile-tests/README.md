# trust-core-profile-tests: real producer output (profile-negative tests)

This is the same build as `trust-core-bytes` (core #125 at `3c731fc1`), dumped with
`--module Silmaril.Prelude.Trust.Examples`. That module tests the profiles, and the dump is
audited at `default`. The core's own audit lines list 7 violations, and the recomputed audit
agrees:

- **6 native runs outside `default`:** they ran under `local`, under a named set, or through the
  paired or declared forms. Their `elaborated_profiles` still show the profile they ran under,
  but a theorem elaborated under `local` stays a violation in a `default` artifact.
- **1 unverified native axiom** (`byDecideNative`, `test.decideNative`): the axiom matches the
  procedure by name only, and no recorded use produced it.
