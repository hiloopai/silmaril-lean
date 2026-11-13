# trust-elf-profile-tests: real producer output for ELF profile tests (#127)

This is the same checkout as `trust-elf-staged` (#127 at `67503c32`), exported with
`--module Silmaril.Elf.Staged.Example.Profiles --root Silmaril.Elf.Staged`.

Audited at `default`, `loader_local` (`elf.loader`) and `main_local` (`elf.tiles.x86`) are
**violations**, as expected; the export and the recomputed audit agree. `--strict-trust` fails.
