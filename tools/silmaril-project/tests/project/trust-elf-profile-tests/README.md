# trust-elf-profile-tests: real producer output for ELF profile tests (#127)

This is the same checkout as `trust-elf-staged` (#127 at `449a063e`), dumped with
`--module Silmaril.Elf.Staged.Example.Profiles --root Silmaril.Elf.Staged`. That module tests the
`local` profile. Audited at `default`, `loader_local` (`elf.loader`) and `main_local`
(`elf.tiles.x86`) are **violations**, as expected. The core's audit and the recomputed audit
agree.

`449a063e` only merges `main` into `91edfc6b`. `git diff 91edfc6b 449a063e` is empty for `Silmaril/Elf`, `Silmaril/Prelude`, `Silmaril/Data/IncludeBytes`, `policy.toml`, `lean-toolchain` and `lake-manifest.json`, so this dump is the dump of `91edfc6b` (core #125 `3c731fc1`).
