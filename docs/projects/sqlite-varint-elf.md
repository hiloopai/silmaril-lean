# SQLite one-byte varint ELF proof

The proof uses the existing unstripped SQLite 3.54.1 x86-64 Linux library built with
Debian GCC 14.2.0-19 at `-O2`. The archive and ELF identities are recorded in the
[compiler manifest](../../corpus/sqlite/equivalence/native-compilers/manifest.json).
The file and ELF virtual offsets coincide for these spans.

| Pin | SHA-256 |
| --- | --- |
| Official `sqlite-amalgamation-3540100.zip` | `0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9` |
| `corpus/variants/sqlite/3.54.1/default/x86_64/O2/unstripped/libsqlite3.so` | `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8` |
| `btreeParseCellPtrNoPayload`, `[0x117b0, 0x117e2)` | `e51e80745b69d060c89aa80ab417ec3c4214e13adbdfd07eac96f6c677acdef0` |
| `sqlite3GetVarint` through the common return, `[0x10a40, 0x10a78)` | `98d4342657a0a7833bdc244b0593229a582dd13bd3a2938b1164e59500a35566` |

[Definitions and contract](../../Silmaril/Elf/Corpus/SqliteOneByteVarint/Defs.lean) ·
[Public theorems](../../Silmaril/Elf/Corpus/SqliteOneByteVarint/Thms.lean)

`firstReturn` begins with the caller at the supplied load bias in the modeled
read-only image of this file. The entry has a System V stack and readable saved
return word. RSI points to the cell and the byte at RSI+4 is backed, readable and
less than 128. RDX points to a writable 24-byte `CellInfo`. The private slot
`[RSP-8, RSP)` is writable and readable after the CALL writes its continuation.
The output and private slot are disjoint from each other, the input byte, the saved
outer return word and both executable windows. The addresses used for the input,
output and stack are bounded. The four bytes preceding the varint and the
`MemPage *` argument play no role in this compiled path.

| Order | Data access | Size |
| --- | --- | --- |
| 1 | Write the call continuation at RSP−8 | 8 |
| 2 | Read the input at RSI+4 | 1 |
| 3 | Write the zero-extended key at RDX | 8 |
| 4 | Read the call continuation at RSP−8 | 8 |
| 5 | Write zero payload length at RDX+16 | 4 |
| 6 | Write the null payload pointer at RDX+8 | 8 |
| 7 | Write cell size five at RDX+22 | 2 |
| 8 | Write zero local payload length at RDX+20 | 2 |
| 9 | Read the outer return word at the original RSP | 8 |

The exact data-event trace is attached to successfully decoded and executed
`Open9` steps. The final state has the popped outer stack, the saved return PC,
preserved callee-saved registers and the expected bytes of `CellInfo`. All other
memory outside the two write spans and all mapping metadata are preserved.

`file_codeAt` kernel-checks executable segment containment and exact file
bytes. `symbol_at` checks the two named local function symbols and that their
file windows start at those symbols and stay within their extents. The run checks each retired instruction at its biased PC, the immediate
displacement of the direct CALL, the callee's conditional branch to the common
return, the callee RET to the pushed continuation and the caller's first
return. The path has no dynamic symbol or PLT transfer. The ELF placement and
read-only mapping are supplied through `Placement` and `RoLoaded`. Dynamic
relocation application, live Linux loading and hardware adequacy are outside
the theorem. The standalone example uses two modeled executable windows at a
nonzero bias and an input mapping with exactly one readable byte.

## Replay

```sh
(cd corpus/variants/sqlite/3.54.1/default/x86_64/O2/unstripped && sha256sum -c SHA256SUMS)
lake build --wfail +Silmaril.Elf.Corpus.SqliteOneByteVarint.Checks
for mod in Silmaril.Elf.Corpus.SqliteOneByteVarint.Defs \
  Silmaril.Elf.Corpus.SqliteOneByteVarint.Thms \
  Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint.Run \
  Silmaril.Elf.Corpus.SqliteOneByteVarint.Checks; do
  SILMARIL_REPLAY_MODULE="$mod" lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit 1
done
```

The build prints the transitive axioms of the public theorems. The [example
and audit](../../Silmaril/Elf/Corpus/SqliteOneByteVarint/Checks.lean) use
kernel decision for the bounded witness.
