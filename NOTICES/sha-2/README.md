# sha-2 (amosnier)-derived object code

`Silmaril/Raw/X86/Bench/Objects/RightRotClangO0.lean` and
`Silmaril/Raw/Machine/CSupport/Crypto/X86/Objects/Sha256ClangO0.lean` embed, byte for byte, the
x86-64 object `sha256.o` (clang `-O0`, SHA-256 `db9c53be9bd77f1b963d1c5dc2c2c90550d00fe8b0ef90adab38ac6975865b54`).
It is compiled from `sha-256.c` of [amosnier/sha-2](https://github.com/amosnier/sha-2) at commit
[`565f65009bdd98267361b17d50cddd7c9beb3e6c`](https://github.com/amosnier/sha-2/tree/565f65009bdd98267361b17d50cddd7c9beb3e6c)
(unmodified; the function `right_rot` is that file's), linked by `ld -r` with an in-house
wrapper (`xc_sha256.c`). The modules built on it (`Silmaril.X86.Bench.Objects.RightRotClangO0`,
`Silmaril.X86.Decompile.RightRot`, `Silmaril.X86.FnContract.RightRot`, and, with the decompiler,
`Silmaril.Machine.CSupport.Crypto.X86.Objects.Sha256ClangO0`) state facts about that code.

[LICENSE.md](LICENSE.md) is the exact upstream licence at that commit: the Unlicense or the
Zero Clause BSD licence, at the user's option, © 2021 Alain Mosnier.
