# ELF carriers, decoding, addresses and assembly functions

Four layers on top of the ELF verification API ([elf.md](elf.md)), each a separate module of
`Silmaril.Elf`. They add no second reader: every fact is stated through the specification parse
`Silmaril.Elf.read` and the file's bytes (`Blob`, `blobRead`), and every existing fact (`Parses`,
`CodeAt`, `SymbolAt`, the staged `PartIs` rows) is reused as is.

| module | what it adds | main names |
|---|---|---|
| `Silmaril.Elf.Like` | one interface for whatever may denote an ELF file | `ElfLike`, `ElfLike.ofSource`, `Denotes`, `MachineIs`, `EntryPoint`, `File.entries`, `EntriesAre`, `IsEntry` |
| `Silmaril.Elf.Decode` | unsupported, invalid and incomplete as distinct answers | `decode`, `Decoded`, `whole`, `prefixOf`, `windows`, `Refines` |
| `Silmaril.Elf.Image` | file offsets, virtual addresses, load addresses and zero fill | `File.origins`, `File.resolve`, `Origin`, `MapsFile`, `FileBytes`, `SegBytes`, `Untouched` |
| `Silmaril.Elf.Asm` | an assembly function and its evidence, dimension by dimension | `AsmFunction`, `Isa`, `ArchOf`, `BytesAt`, `SymbolOf`, `DecodesAs`, `LinesTile`, `RefsGrounded` |

## Carriers (`Silmaril.Elf.Like`)

`ElfLike α` has one method, `ast? : α → Option File`. Byte representations already have a class,
`Silmaril.ByteSource` (`ByteArray`, `KBytes`, `List UInt8`); `ElfLike.ofSource` makes any of them
ELF-like through the specification parse, and is a `def`, so no type has two instances. The other
instances: `Blob` (the parse), `Silmaril.Formats.Bytes` and project values (`blobOf`, the form
`Shapes.file` already uses), the ELF readers' byte arrays, `BinaryImage`, the lossless CST
(through its serialization) and the AST itself.

Bridges (`Like.Thms`), so a fact through any carrier is a fact about the same file:
`denotes_byteArray` and `denotes_value` are definitional; `denotes_kbytes` takes the equation
`x.toByteArray = raw` that `kbytes_def … of_include` proves without decoding a byte, so
`include_bytes` files keep their kernel checking; `cst_ast` takes a checked CST. `MachineIs`
accepts any `e_machine`. `File.entries` lists entry points by kind (`e_entry`, exported
`.dynsym` functions, `.symtab` functions of `ET_REL`); three shapes state them:
`silmaril.shapes.elf.{machine,entries,is_entry}`.

## Decoding (`Silmaril.Elf.Decode`)

| answer | meaning |
|---|---|
| `ok A` | the bytes parse to `A`, whatever `e_machine` says |
| `unsupported u` | a well-identified ELF file outside what the specification reads: `ELFCLASS32`, big-endian, an `EI_VERSION` other than 1 |
| `invalid i` | not ELF, a malformed identification, truncated, or a table the specification rejects |
| `incomplete o w` | the view does not hold the `w` bytes at `o`: no fact about the file |

`decode` runs the parse specification three-valued and, only when it rejects, reads the
identification to say why. On whole files nothing changes (`decode_whole_ok_iff : decode (whole F)
= .ok A ↔ Parses F A`), and a whole file is never `incomplete`. On partial views
(`prefixOf F k`, `windows ws r`) a final answer is stable: a fuller view gives the same one
(`decode_refines`). Kernel-checked examples (`Decode.Examples`) cover each answer, including an
`ELFCLASS32` file identified from an 8-byte prefix and a file with an unknown `e_machine` that
decodes `ok` and has `MachineIs … 0x1234`.

## Addresses (`Silmaril.Elf.Image`)

`File.origins A v` lists **every** `PT_LOAD` mapping the virtual address `v`, with where its byte
comes from: `file o` (file offset `o`) or `zeroFill` (past `p_filesz`, before `p_memsz`). The parse
does not reject overlapping segments, so `File.resolve` answers `unmapped`, `unique i o` or
`ambiguous hits`. The existing first-match lookups are related to it rather than replaced:
`offsetOf_origin`/`vaddrOf_origin` (the staged layout's `offsetOf`/`vaddrOf` give one of the
origins), `offsetOf_of_unique` (they give *the* origin when it is unique), and
`codeAt_segBytes`/`codeAt_of_segBytes` (`CodeAt` is `SegBytes` in the first read-only executable
segment). `Untouched A v len` says no dynamic relocation writes into a range (each by the width its type writes; unknown widths touch everything); memory after loading
equals file bytes only there (or under a loading model, `Silmaril.Elf.Link.ElfBind`).

## Assembly functions (`Silmaril.Elf.Asm`)

An `AsmFunction` is data: name, architecture (`e_machine`, class, data, OS ABI), an ABI
reference identifier (`abiRef`, metadata only), the code extent (virtual address, size, and the
file offset, segment and section when known), the exact bytes, a symbol table entry, listing lines
(`off`, `len`, `text`, `label`) and references (to a target address or symbol, from a relocation,
from a decoded branch, or from the listing). What is believed about it is a set of independent
propositions:

| evidence | proposition |
|---|---|
| `ArchOf F f` | the file's header names `f.arch` |
| `BytesAt F f` | `f.bytes` are file bytes at `f.extent.fileOff`, mapped by segment `f.extent.segment` to `f.extent.vaddr` (none zero fill) |
| `SectionBytesAt F f` | the same through section `f.extent.shndx`: the grounding of a relocatable object (no segments) |
| `CodeAt F f.extent.vaddr f.bytes` | the API's code fact (`bytesAt_codeAt`, `codeAt_bytesAt`) |
| `SymbolOf F f` | `f.symbol` is a function symbol named `f.name` with `f.extent`'s value and size |
| `DecodesAs isa f d` | the instruction model `isa`, for `f.arch.machine`, decodes `f.bytes` into `d`, back to back |
| `LinesTile f` | the listing lines' byte ranges tile the bytes |
| `RefsGrounded F f isa d` | each relocation reference is the file's relocation (offset, type, addend, symbol name); each decoded reference is the branch target of the decoded instruction |

The listing text is never read: every proposition is invariant under replacing the lines or the
ABI identifier (`bytesAt_withLines`, `decodesAs_withLines`, …, all `Iff.rfl`). A decoding is a
separate value checked by a decoder (`decodes`, `decodeAll`, `decodes_iff_decodeAll`), so a
display listing does not become a decoding. Decoding is unique per model (`DecodesAs.unique`), and
bytes are unique per extent (`bytesAt_unique`).

Instruction models are parameters (`Isa`): `Asm.X86` adapts three existing decoders,
`x86Ext` (`Silmaril.X86.Ext.decode`), `x86Open` (`Silmaril.X86.Open.decode`) and `x86Open9`
(`Silmaril.X86.Open9.decode`). A function for an `e_machine` with no model is still grounded; it
has no `DecodesAs`.

### Sample functions (`Silmaril.Elf.Asm.Example`)

Four functions of the pinned static executable
`examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums`, each dimension a separate
kernel-checked theorem on the file's `include_bytes` (standard axioms only):

| function | vaddr | bytes | decoded by | not decoded by | references | existing contract |
|---|---|---|---|---|---|---|
| `adler32_z` | `0x401410` | 1135 | `x86Open9` (297 instructions) | `x86Open` | | `Open9` |
| `adler32` | `0x401880` | 7 | `x86Open9` | | `jmp adler32_z` | `Open9` |
| `crc32_z` | `0x401990` | 291 | `x86Open` (75 instructions) | `x86Ext` | | `Open` |
| `crc32` | `0x401ac0` | 7 | `x86Open`, `x86Ext` | | `jmp crc32_z` | `Open` |

The contracts are the existing `Silmaril.X86.Ladder.ZlibChecksums` theorems, stated beside the
grounded bytes. The table shows why the dimensions stay separate: `crc32_z`'s contract is proved on
`Open` and the base decoder `x86Ext` does not decode it; `adler32_z`'s is proved on `Open9` and
`x86Open` does not decode it. `otherMachine` (the bytes of `crc32` claimed for `e_machine 0x1234`)
has `BytesAt`, `¬ ArchOf`, and no x86 decoding. The address theorems on the same file
(`textResolves`, `bssZeroFill`, `offsetZero`, `unmapped`) separate a file-backed address, a zero-fill
segment whose `p_offset` is 0, file offset 0 (mapped at `0x400000`) and an unmapped address.

A relocatable object (`Silmaril.Elf.Asm.Example.Reloc`): `examples/elf-asm/reloc/scaled.o`
(936 bytes, built from `scaled.c` by `build.sh`, which compares with the pinned SHA-256), one
function `scaled_plus_bias` whose `.text` carries `R_X86_64_PLT32 scale - 4` and
`R_X86_64_PC32 bias - 4`. Its parse is one run of the specification on the kernel bytes
(`parses`); it has no program headers, so `not_bytesAt` (no function of it has `BytesAt`) and its
bytes are `SectionBytesAt` section 1; `refs` grounds both references in `.rela.text` (offset, type,
addend, symbol name); `call_unrelocated` shows the decoded `call` targets offset 9, its own
successor, which is where the unrelocated displacement points and not where the call goes.

The display lines come from `objdump -d` (`scripts/elf-asm/gen.sh`, which records the objdump
version in the generated module); they are display data, regenerated by hand.

### JSON for views (`silmaril.elf.asm/1`)

`Silmaril.Elf.Asm.Export` fixes the JSON form (schema in its module doc): addresses and file
offsets as hexadecimal strings, unknown values as `null`, display lines, decodings (model,
instructions, renderings) and an **evidence array** with `kind`, `decl`, `model`, `axioms` and
`hypotheses` per theorem, with no single status rank. `tools/elf-asm` writes it for the sample
functions to [examples/elf-asm/samples.json](../../examples/elf-asm/samples.json):
it imports the checked theorem modules, reads every theorem's statement and classifies its
conjuncts by their head constant, function argument and file argument; theorem names are not read.
Before writing, it runs a self-test on decoys (`tools/elf-asm/ElfAsmDecoys.lean`): a true fact
about a moved copy of a function, a fact about the right function against another file, a
contract stated without bytes, an evidence-like name on `True`, and a decoding of the same bytes
under another function give no evidence, and a conditional fact gives evidence with its premise
listed; any other classification fails the tool. `make elf-check` runs `elf-asm --check` against
the committed file.

```
lake build elf-asm
lake env .lake/build/bin/elf-asm examples/elf-asm/samples.json
lake env .lake/build/bin/elf-asm --check examples/elf-asm/samples.json
```

## Not here

- Dynamic relocations (`RefOrigin.reloc .dynamic`) in a sample (code of shared objects has none;
  the relocatable sample exercises `.forSection`), and `.dynsym`-only stripped files.
- ABI conformance: no proposition reads `abiRef`. A typed ABI belongs to the calling-convention
  layer, which can refer to an `AsmFunction` and its evidence.
- A theorem relating a machine's fetch to a decoder (`decodes`); a contract on a machine is evidence
  about the bytes, not about any decoder.
- ELFCLASS32 and big-endian files are reported `unsupported`, never parsed.
- The analysis prototypes this port comes from (classification, load-mode entries, reachability
  and effect bounds) are not ported yet.

## Provenance

`Like` and `Decode` port the authors' development of the ELF API: `BytesLike`/`ElfLike`, entry
points and machine shapes, and three-valued decoding. The port deduplicates them onto
`Silmaril.ByteSource` and plain oracles (the development had two `BytesLike` classes and two
`ElfLike` classes), splits `unsupported` out of `invalid`, and adds the bridge theorems and
examples. `Image` and `Asm` are new.
