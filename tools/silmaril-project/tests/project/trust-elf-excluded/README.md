# trust-elf-excluded: real producer output with a module left out of the audit (#127)

This is the same checkout as `trust-elf-staged` (#127 at `67503c32`). The export command was:

```
sil project trust-dump --module Silmaril.Elf.Staged.Example.Thms --module Silmaril.Elf.Staged.Example.Profiles \
  --root Silmaril.Elf.Staged --exclude Silmaril.Elf.Staged.Example.Profiles
```

`Example.Profiles` holds profile-negative tests. It is described (imports, digest) but not listed
for audit, so it is `unaudited` and coverage is partial. The frozen export has no field for an
audit exclusion's reason, so the reason is recorded here and in the command, not in the database.
In the checkout, `--strict-trust` passes and prints "not a full audit".
