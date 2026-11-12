module

public import Silmaril.Elf.Parse.Defs
public import Silmaril.Elf.Index.Defs

/-! # Facts about an ELF file

Each fact is **one separate statement** about a file `F` (a `Blob`), read through its parse
(`Parses F A`, which determines `A`), so that a proof of one never re-proves another and a
consumer cites exactly what it uses:

| fact | statement | reads |
|---|---|---|
| `KindIs F k` | `F` is an object of kind `k` (`ET_REL`, `ET_EXEC`, shared, PIE, static PIE) | AST |
| `SymbolAt F t i s` | entry `i` of table `t` is `s` (raw entry and name) | AST |
| `Lookup F sel d` | the selector `sel` denotes `d` (ld.so lookup or `.symtab`) | AST |
| `Needed F ns` | the `DT_NEEDED` names are `ns` | AST |
| `Relocs F rs sel` | the relocations `sel` names are `rs` | AST |
| `Placement F base` | `F` may be loaded at `base` | AST |
| `CodeAt F v code` | a read-only executable `PT_LOAD` maps `code` at `v` | AST + code bytes |
| `Binds F sel v code` | `sel` denotes a plain function at `v` whose code is `code` | both |

`Binds` is the compound a function specification uses (`Binds.lookup`, `Binds.code`:
it is the conjunction, `binds_iff`). Every fact but `CodeAt` is a function of the AST, never of
the code bytes (`Thms.lookup_frame`; with `Task.parse_frame`, two files that differ only in
code have the same lookups).

`Placement` says which load bases a statement covers, with the base a `Nat`; loading models
are stated elsewhere and relate to these facts through it.
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Formats.ELF (NameBytes ObjectSymbol)
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

/-- **`F` is an object of kind `k`.** -/
def KindIs (F : Blob) (k : Kind) : Prop := ∃ A, Parses F A ∧ A.kind = k

/-- **Entry `i` of the symbol table `t` of `F` is `s`.** -/
def SymbolAt (F : Blob) (t : Table) (i : Nat) (s : ObjectSymbol) : Prop :=
  ∃ A, Parses F A ∧ (A.symbols t)[i]? = some s

/-- **In `F`, the selector `sel` denotes `d`** (`none`: nothing). -/
def Lookup (F : Blob) (sel : Sel) (d : Option Def) : Prop :=
  ∃ A, Parses F A ∧ A.select sel = some d

/-- **The `DT_NEEDED` names of `F` are `ns`, in order.** -/
def Needed (F : Blob) (ns : List NameBytes) : Prop := ∃ A, Parses F A ∧ A.needed = ns

/-- **The relocations of `F` that `sel` names are `rs`.** -/
def Relocs (F : Blob) (sel : File.RelocSel) (rs : List File.Reloc) : Prop :=
  ∃ A, Parses F A ∧ A.relocs sel = rs

/-- `ph` is a read-only executable `PT_LOAD` mapping `[v, v + len)` from the file. -/
def codeSeg (v len : Nat) (ph : Silmaril.Formats.ELF.ProgramHeader) : Bool :=
  ph.kind == PT_LOAD && ph.flags / 2 % 2 == 0 && ph.flags % 2 == 1 &&
    decide (ph.virtualAddress ≤ v) && decide (v + len ≤ ph.virtualAddress + ph.fileSize)

/-- **`F` holds `code` at virtual address `v`**, in the first read-only executable `PT_LOAD`
mapping it (as `ElfBind.CodeAt`): one wide read of the file. -/
def CodeAt (F : Blob) (v : Nat) (code : List (BitVec 8)) : Prop :=
  ∃ A, Parses F A ∧ ∃ ph, A.phdrs.find? (codeSeg v code.length) = some ph ∧
    blobRead F (ph.offset + (v - ph.virtualAddress)) code.length = some (Blob.valueLE code)

/-- **The load bases a statement covers** (as `ElfBind.Placement`): `0` for `ET_EXEC`, a
page-aligned base for `ET_DYN`, with every `PT_LOAD` below `2^47` and `p_filesz ≤ p_memsz`. -/
def Placement (F : Blob) (base : Nat) : Prop :=
  ∃ A, Parses F A ∧
    (A.header.fileType = ET_EXEC ∧ base = 0 ∨ A.header.fileType = ET_DYN ∧ base % 4096 = 0) ∧
    ∀ ph ∈ A.loads, ph.fileSize ≤ ph.memorySize ∧ base + ph.virtualAddress + ph.memorySize ≤ 2 ^ 47

/-- **`F` binds `sel` to a plain function at `v` whose code is `code`**: the lookup finds a
definition at `v` that is neither an IFUNC nor absolute, and `CodeAt F v code`. -/
def Binds (F : Blob) (sel : Sel) (v : Nat) (code : List (BitVec 8)) : Prop :=
  (∃ d, Lookup F sel (some d) ∧ d.value = v ∧ d.ifunc = false ∧ d.abs = false) ∧ CodeAt F v code

/-- **The parse of `F` reads no code byte**: every read of the specification `read` run on `F`
(`Parse.trace`) is disjoint from the code spans of its parse `A`. Decidable; true of every
well-formed file, but not of all files (a section-name table whose range overlaps `.text` makes
the parse read code), which is why `Task.parse_frame` takes it as a hypothesis. -/
def AvoidsCode (F : Blob) (A : File) : Prop :=
  ∀ x ∈ Parse.trace (blobRead F) read, ∀ s ∈ A.codeSpans, s.off + s.len ≤ x.1 ∨ x.1 + x.2 ≤ s.off

instance (F : Blob) (A : File) : Decidable (AvoidsCode F A) :=
  inferInstanceAs (Decidable (∀ x ∈ _, _))

/-- **The parse never reads code**: if the parse of `F` reads no code byte (`AvoidsCode`), two
files that agree outside the code spans of the parse of the first have the same parse. Proved:
`Silmaril.Elf.parse_frame` (`Check.Thms`). -/
def Task.parse_frame : Prop :=
  ∀ (F G : Blob) (A : File), Parses F A → AvoidsCode F A → F.len = G.len →
    (∀ o w, (∀ s ∈ A.codeSpans, s.off + s.len ≤ o ∨ o + w ≤ s.off) → blobRead F o w = blobRead G o w) →
    Parses G A

end Silmaril.Elf
