# Derived from the RSA Data Security, Inc. MD5 Message-Digest Algorithm

`Silmaril/Raw/X86/Bench/Objects/Md5MemcpyClangO0.lean` embeds, byte for byte, the x86-64 object
`md5.o` (clang `-O0`, SHA-256 `58e6cee7dd3718cc60df4e4852dabd5e93ab4d62875d8d584d043f26afc827fe`),
compiled from `md5c.c`, the reference implementation of
[RFC 1321](https://www.rfc-editor.org/rfc/rfc1321.txt) (appendices A.1 to A.3: `global.h`,
`md5.h`, `md5c.c`, unmodified, built with `-DPROTOTYPES=1`), linked by `ld -r` with an in-house
wrapper (`xc_md5.c`).
`Silmaril/Raw/X86/Decompile/Md5Memcpy.lean` decompiles its function `MD5_memcpy`, and the modules
built on them (`Silmaril.X86.Bench.Objects.Md5MemcpyClangO0`, `Silmaril.X86.Decompile.Md5Memcpy`,
`Silmaril.X86.Sep.Demo` and its proofs `Silmaril.Proofs.X86.Sep.Demo.Md5Memcpy`) state facts
about that code. This material is derived from the RSA Data Security, Inc. MD5 Message-Digest
Algorithm.

[md5c.c-NOTICE](md5c.c-NOTICE) is the copyright and licence notice of `md5c.c`, exactly as it
appears at the head of that file (sha256 of the file
`90c96bf1981b5553938e47c8ebcf20fe46f91aef950dcc0915dca4ce06e16210`).
