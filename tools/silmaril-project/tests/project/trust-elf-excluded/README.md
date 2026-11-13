# trust-elf-excluded: real producer output with a module excluded, and its reason (#127)

This is the same checkout as `trust-elf-staged` (#127 at `67503c32`). The export command was:

```
sil project trust-dump --module Silmaril.Elf.Staged.Example.Thms --module Silmaril.Elf.Staged.Example.Profiles \
  --root Silmaril.Elf.Staged \
  --exclude "Silmaril.Elf.Staged.Example.Profiles=profile-negative tests: local-profile native runs and cross-leaf identity forgeries, deliberately flagged at default"
```

`trust.json` is the core's export, unchanged. `Example.Profiles` is described in it but not
listed for audit. `trust.json.exclusions.json` is the database-owned sidecar `trust-dump` wrote.
It is bound to the export's SHA-256 and records the exclusion's reason, which the database stores
in `trust_modules.reason` (coverage `excluded`). Coverage is partial. In the checkout,
`--strict-trust` passes and prints "not a full audit".
