# trust-elf-excluded: real producer output with an explicit exclusion (#127)

This is the same checkout as `trust-elf-staged` (#127 at `67503c32`, core #125 at `34ec436e`).
It was dumped with both example modules and one recorded exclusion:

```
sil project trust-dump --module Silmaril.Elf.Staged.Example.Thms --module Silmaril.Elf.Staged.Example.Profiles \
  --root Silmaril.Elf.Staged \
  --exclude "Silmaril.Elf.Staged.Example.Profiles=profile-negative tests: local-profile native runs and cross-leaf identity forgeries, deliberately flagged at default"
```

The profile-test module is described (its imports and digest) but not audited. Its 2 violations
are not counted, and coverage is **partial**.

In the checkout, with the sources present, `--strict-trust` passes and prints `policy valid on
partial coverage (not a full audit …)`. The same dump without the exclusion
(`trust-elf-profile-tests`) fails strict validation.
