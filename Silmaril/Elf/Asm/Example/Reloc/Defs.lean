module

public import Silmaril.Data.IncludeBytes.Kernel
public import Silmaril.Elf.Asm.Example.Reloc.Listing
public import Silmaril.Elf.Asm.X86
public import Silmaril.Elf.Staged.Reader.Defs

/-! # A relocatable object: references that only relocations ground

`examples/elf-asm/reloc/scaled.o` (936 bytes, SHA-256 `eb323d7e…28f1`, built from `scaled.c` by
`build.sh`) is an `ET_REL` object with one function,

```c
extern int scale(int);
extern int bias;
int scaled_plus_bias(int x) { return scale(x) + bias; }
```

whose 20 bytes of `.text` carry two relocations in `.rela.text`: `R_X86_64_PLT32 scale - 4` at
offset 5 (the `call`) and `R_X86_64_PC32 bias - 4` at offset 11 (the RIP-relative load). The
object has no program headers, so its bytes are grounded through section 1 (`SectionBytesAt`),
and its references through relocations (`RefOrigin.reloc`): the decoded `call` targets the
unrelocated displacement (`call 9`, as the display listing also prints), which is not where the
call goes after linking. -/

@[expose] public section

namespace Silmaril.Elf.Asm.Example.Reloc

/-- The pinned file's path, from the repository root. -/
def path : String := "examples/elf-asm/reloc/scaled.o"

/-- Its SHA-256 (`scaled.o.sha256`). -/
def fileSha256 : String := "eb323d7e658cf727b72810143eb6ca0d4bbecf28eeca56d9946c9167a0c228f1"

/-- The file, as `include_bytes`. -/
noncomputable def raw : ByteArray := include_bytes "../../../../../examples/elf-asm/reloc/scaled.o"

kbytes_def K of_include raw

/-- The file the specification reads. -/
noncomputable abbrev F : Silmaril.X86.Link.Blob := Silmaril.Elf.blobOf ⟨raw⟩

/-- Its parse, computed by the specification on the kernel bytes. -/
noncomputable def ast : File := (read.run (Staged.Reader.kread K)).get (by decide +kernel)

/-- `scaled_plus_bias`: `sub $8,%rsp; call scale; add bias(%rip),%eax; add $8,%rsp; ret`. -/
def scaledPlusBias : AsmFunction where
  name := "scaled_plus_bias"
  arch := .x86_64
  abiRef := some "sysv64"
  extent := { vaddr := 0, size := 20, fileOff := some 0x40, shndx := some 1 }
  symbol := some ⟨.symtab, 2⟩
  bytes := [0x48, 0x83, 0xec, 0x08, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x03, 0x05, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x83, 0xc4, 0x08, 0xc3]
  lines := scaledLines
  refs := [
    { off := 5, symbol := some "scale", kind := 4, addend := -4, origin := .reloc (.forSection 1) 0 },
    { off := 11, symbol := some "bias", kind := 2, addend := -4, origin := .reloc (.forSection 1) 1 }]

/-- Its decoding by the base decoder. -/
def scaledDecoding : List (Nat × x86Ext.Instr) := (decodeAll x86Ext scaledPlusBias.bytes).getD []

end Silmaril.Elf.Asm.Example.Reloc
