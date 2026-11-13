# trust-core-profile-tests: real producer output (profile-negative tests)

This is the same build as `trust-core-bytes` (core #125 at `91f7e0de`, v1 API), produced with
`--module Silmaril.Prelude.Trust.Examples`. That module tests the profiles: its theorems run
procedures natively under `local`, a named set or the paired and declared forms. The dump is
audited at the `default` profile, so the six theorems that ran natively outside `default` are
**violations**, as they should be. A theorem elaborated under `local` stays a violation for a
`default` artifact.

Each use line keeps the profile it ran under (`local`, `toys`, …). The audit uses the header's
`profile` and `ceiling`.
