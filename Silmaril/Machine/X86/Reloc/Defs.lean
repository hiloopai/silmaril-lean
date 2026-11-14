module

public import Silmaril.Machine.Link.Defs
public import Silmaril.Raw.Machine.X86.Linking.Relocation

/-! # x86-64 static RELA relocation profile (header)

Re-exports `an earlier development` `Silmaril/X86/Linking/Relocation.lean`
(`Silmaril.Raw.Machine.X86.Linking.Relocation`, namespace
`Silmaril.X86.Linking.Relocation`), whose only source change is its import of
the shared linker through `Silmaril.Machine.Link.Defs`.

Kinds: `R_X86_64_64` (1), `PC32` (2), `PLT32` (4), `32` (10), `32S` (11).
`value r = S + A - P` for PC32/PLT32 and `S + A` otherwise; `Fits` is the
range check; `PLT32` resolves directly to the unique non-interposable
definition (no PLT/GOT synthesis, no relaxation). `staticObject` rejects weak,
COMMON, IFUNC, TLS symbols and section groups even when unreferenced.
`link`/`linkBytes` instantiate `Silmaril.Formats.ELF.Link.link`.

Supported build profile: `-fno-pic -no-pie` (plus `--no-relax` for `ld`), static,
no TLS/IFUNC/`.init_array`. Anything else is an explicit rejection.
-/
