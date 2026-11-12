module

public import Silmaril.Elf.Link.Dyn.Elf.Defs
public import Silmaril.Process.Memory
public import Silmaril.X86.Basic
public import Silmaril.X86.Encoding

/-! # Binding a function of an ELF file

The layer between a pinned ELF file and a statement about one of its functions. A library
spec names functions (`adler32_z`, `strlen`), never addresses; this module says, for a file
`F` given as its bytes (`Blob`), **which code a name denotes** and **what memory holds when
that code runs**, so that one spec applies mechanically to every file.

* `Sel`: how a function is found.
  - `.dyn r`: ld.so's lookup of the reference `r` (name, requested version) in the file's
    `.dynsym` (`DynElf.Elf.lookupDef`, glibc 2.39's `do_lookup_x` and `check_match`). This is
    the definition an executable importing `r` binds to when the file is the first object of
    its scope that defines `r`: the case of a shared object (`libz.so.1`, `libc.so.6`).
  - `.sym n`: the defined global or weak `STT_FUNC` symbol named `n` in `.symtab` (the static
    symbol table): the case of a static executable or an unstripped object. A stripped
    static file has no `.symtab`; its functions are then bound by a certificate (a `.sym`
    over a side table), not by this reader.
* `Sel.find`: the reading program (`DynElf.Rd`) of a selector: the symbol's value and
  whether it is an `STT_GNU_IFUNC`. `Bound F s v`: it runs on the whole file and finds a
  non-IFUNC definition at `v`. A file is a `Blob` (one number), so a statement about it is
  checked on a sparse view (pages or chunks) and transferred with `DynElf.run_sparse`.
* `CodeAt F v code`: the read-only executable `PT_LOAD` segment that maps `v` holds `code`
  there (one wide read; `code` as a little-endian number).
* `Placement F base`: the load bases a statement quantifies over: `0` for `ET_EXEC`, any
  page-aligned base for `ET_DYN`; in both cases every `PT_LOAD` must lie below `2^47` (the
  user address space) and have `p_filesz ≤ p_memsz`. A file violating these has no
  placement; a row asks for one.
* `RoLoaded F base mem`: every read-only `PT_LOAD` of `F` is in `mem` at `base + p_vaddr`:
  each window of its file bytes is readable there if the segment is `PF_R` and fetchable if
  it is `PF_X`. This is what a loader guarantees of a file without `DT_TEXTREL` (relocations
  only write writable segments). Writable segments (`.data`, `.got`, `.bss`) are not
  constrained: the program may have changed them.
* `InImage F base a`: `a` lies in some `PT_LOAD` (memory extent) of `F` at `base`.

Nothing here is trusted beyond the readers' agreement with the ELF format (and, for `.dyn`,
with ld.so, as in `DynElf`).
-/

@[expose] public section

namespace Silmaril.Elf.Link.ElfBind

open Silmaril.Elf.Link.DynElf
open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)

/-! ## Section headers and the static symbol table -/

/-- A section header (the fields the symbol readers use). -/
structure Shdr where
  kind : Nat
  off : Nat
  size : Nat
  link : Nat
  deriving DecidableEq, Repr

-- The inner `Elf` (the loader's view of a file) repeats the region's name.
set_option linter.dupNamespace false

namespace Elf

open DynElf.Elf (u8 u16 u32 u64 strIs Sym)

/-- Section header `i` of the table at `o`. -/
def shdr (o : Nat) : Rd Shdr := do
  let kind ← u32 (o + 4)
  let off ← u64 (o + 0x18)
  let size ← u64 (o + 0x20)
  let link ← u32 (o + 0x28)
  pure ⟨kind, off, size, link⟩

/-- The section headers (ELF64, `e_shentsize = 64`). -/
def shdrs : Rd (List Shdr) := do
  let shoff ← u64 0x28
  Rd.guard ((← u16 0x3a) = 64)
  let num ← u16 0x3c
  (List.range num).mapM fun i => shdr (shoff + 64 * i)

/-- The `.symtab` entry at file offset `o`. -/
def symAt (o : Nat) : Rd Sym := do
  let name ← u32 o
  let info ← u8 (o + 4)
  let other ← u8 (o + 5)
  let shndx ← u16 (o + 6)
  let value ← u64 (o + 8)
  pure ⟨name, info, other, shndx, value⟩

/-- Scan `k` symbols from offset `o` for a defined global or weak function (`STT_FUNC` or
`STT_GNU_IFUNC`) whose name, in the string table at `strs`, is `n`. -/
def scan (n : Name) (strs : Nat) : Nat → Nat → Rd (Option Sym)
  | 0, _ => pure none
  | k + 1, o => do
    let s ← symAt o
    if s.shndx ≠ 0 ∧ (s.bind = 1 ∨ s.bind = 2) ∧ (s.type = 2 ∨ s.type = 10) then
      if ← strIs (strs + s.name) n then return some s
    scan n strs k (o + 24)

/-- The definition of `n` in `.symtab` (the first section of type `SHT_SYMTAB`, its string
table the section `sh_link` names). -/
def symtabFind (n : Name) : Rd (Option Sym) := do
  let shs ← shdrs
  let st ← Rd.ofOption (shs.find? (·.kind == 2))
  let strs ← Rd.ofOption shs[st.link]?
  scan n strs.off (st.size / 24) st.off

/-- `e_type`: `2` (`ET_EXEC`) or `3` (`ET_DYN`). -/
def etype : Rd Nat := u16 16

end Elf

/-! ## Selectors and bindings -/

/-- How a function is found in a file (module doc). -/
inductive Sel where
  /-- ld.so's lookup of a reference in `.dynsym`. -/
  | dyn (ref : DynElf.Elf.Ref)
  /-- A defined global function in `.symtab`. -/
  | sym (name : Name)
  /-- An exported function, wherever the file defines it: `.dyn r` if the file has a
  `PT_DYNAMIC` segment and ld.so's lookup finds `r` there, otherwise `.sym r.name`. One
  selector thus covers a shared library and an executable linking the library statically. -/
  | fn (ref : DynElf.Elf.Ref)

/-- ld.so's lookup in `.dynsym`. -/
def findDyn (r : DynElf.Elf.Ref) : Rd (Option (Nat × Bool)) := do
  let d ← DynElf.Elf.dynInfo
  let x ← DynElf.Elf.lookupDef d r false
  pure (x.bind fun e => if e.abs then none else some (e.value, e.ifunc))

/-- The `.symtab` lookup. -/
def findSym (n : Name) : Rd (Option (Nat × Bool)) := do
  let s ← Elf.symtabFind n
  pure (s.map fun s => (s.value, s.type == 10))

/-- The reading program of a selector: `some (value, ifunc)` for a definition. -/
def Sel.find : Sel → Rd (Option (Nat × Bool))
  | .dyn r => findDyn r
  | .sym n => findSym n
  | .fn r => do
    let phs ← DynElf.Elf.phdrs
    let x ← if phs.any (·.kind == 2) then findDyn r else pure none
    match x with
    | some x => pure (some x)
    | none => findSym r.name

/-- **`F` binds the selector `s` to the (non-IFUNC) function at `v`.** -/
def Bound (F : Blob) (s : Sel) (v : Nat) : Prop :=
  s.find.run (blobRead F) = some (some (v, false))

/-! ## Segments, code and placement -/

/-- `ph` is a `PT_LOAD` segment. -/
def isLoad (ph : DynElf.Elf.Phdr) : Bool := ph.kind == 1

/-- `ph` is not writable (`PF_W` clear). -/
def isRo (ph : DynElf.Elf.Phdr) : Bool := ph.flags / 2 % 2 == 0

/-- `ph` is executable (`PF_X`). -/
def isExec (ph : DynElf.Elf.Phdr) : Bool := ph.flags % 2 == 1

/-- `ph` is readable (`PF_R`). -/
def isReadable (ph : DynElf.Elf.Phdr) : Bool := ph.flags / 4 % 2 == 1

/-- The read of the `len` file bytes that a read-only executable `PT_LOAD` maps at `v`. -/
def codeRead (v len : Nat) : Rd Nat := do
  let phs ← DynElf.Elf.phdrs
  let ph ← Rd.ofOption (phs.find? fun ph =>
    isLoad ph && isRo ph && isExec ph && decide (ph.vaddr ≤ v) && decide (v + len ≤ ph.vaddr + ph.filesz))
  Rd.le (ph.off + (v - ph.vaddr)) len

/-- **`F` holds `code` at `v`**, inside one read-only executable `PT_LOAD` segment. -/
def CodeAt (F : Blob) (v : Nat) (code : List Byte) : Prop :=
  (codeRead v code.length).run (blobRead F) = some (Blob.valueLE code)

/-- The program headers of `F`, when its ELF header is an x86-64 ELF64 one. -/
def phdrsOf (F : Blob) : Option (List DynElf.Elf.Phdr) := DynElf.Elf.phdrs.run (blobRead F)

/-- **The load bases a statement covers** (module doc). -/
def Placement (F : Blob) (base : Word) : Prop :=
  ∃ t phs, Elf.etype.run (blobRead F) = some t ∧ phdrsOf F = some phs ∧
    (t = 2 ∧ base = 0 ∨ t = 3 ∧ base.toNat % 4096 = 0) ∧
    ∀ ph ∈ phs, isLoad ph = true → ph.filesz ≤ ph.memsz ∧ base.toNat + ph.vaddr + ph.memsz ≤ 2 ^ 47

/-- The `w` bytes of the little-endian number `n`. -/
def leBytes (n w : Nat) : List Byte := (List.range w).map fun i => BitVec.ofNat 8 (n >>> (8 * i))

/-- **The read-only segments of `F` are loaded at `base` in `mem`** (module doc). -/
def RoLoaded (F : Blob) (base : Word) (mem : Memory) : Prop :=
  ∀ phs, phdrsOf F = some phs → ∀ ph ∈ phs, isLoad ph = true → isRo ph = true →
    ∀ o w n, ph.off ≤ o → o + w ≤ ph.off + ph.filesz → blobRead F o w = some n →
      (isReadable ph = true → mem.readBytes (base.toNat + ph.vaddr + (o - ph.off)) w = some (leBytes n w)) ∧
      (isExec ph = true → mem.fetchBytes (base.toNat + ph.vaddr + (o - ph.off)) w = some (leBytes n w))

/-- `a` lies in a `PT_LOAD` segment (its memory extent) of `F` at `base`. -/
def InImage (F : Blob) (base : Word) (a : Nat) : Prop :=
  ∃ phs, phdrsOf F = some phs ∧ ∃ ph ∈ phs, isLoad ph = true ∧
    base.toNat + ph.vaddr ≤ a ∧ a < base.toNat + ph.vaddr + ph.memsz

/-! ## Linking: GOT slots bound to the file's own definitions -/

/-- **Every symbol slot of `F` that `F` itself defines holds that definition** at `base`: for
each `R_X86_64_GLOB_DAT` (6) or `R_X86_64_JUMP_SLOT` (7) relocation whose reference ld.so's
lookup resolves in `F` to a non-IFUNC definition at `v`, the 8 bytes at `base + r_offset` are
`base + v`. This is the post-load state when `F` is the first object of the scope that defines
those symbols (no interposition) and the slots are bound (eager binding, `DF_BIND_NOW` or
`LD_BIND_NOW`, or after the first lazy call). It is what a call from one export to another
through the PLT needs (zlib 1.3.2's `crc32_combine64` calls `crc32_combine_gen64@plt`).
Interposition is another scope, hence another context and another row. -/
def SelfBound (F : Blob) (base : Word) (mem : Memory) : Prop :=
  ∀ d, DynElf.Elf.dynInfo.run (blobRead F) = some d →
  ∀ rs, (DynElf.Elf.relas d).run (blobRead F) = some rs →
  ∀ r ∈ rs.1 ++ rs.2, (r.kind = 6 ∨ r.kind = 7) → r.sym ≠ 0 →
  ∀ ref v, (DynElf.Elf.refOf d r.sym).run (blobRead F) = some ref →
    (findDyn ref).run (blobRead F) = some (some (v, false)) →
    mem.readBytes (base.toNat + r.off) 8 = some (leBytes (base.toNat + v) 8)

end Silmaril.Elf.Link.ElfBind
