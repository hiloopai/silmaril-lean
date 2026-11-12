module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.Project.Defs

/-! # Problem shapes: facts about an ELF file

Every fact of `Silmaril.Elf.Facts` as a **problem shape** over a registered file (`X : Value V`, any
format; only its bytes are read, as the file `blobOf X.bytes`). A project fills in a row per
file and fact; the parse row is the one a Rust emitter's output is checked against.

| name | statement |
|---|---|
| `silmaril.shapes.elf.parses` | `Parses X A`: the metadata of `X` is the AST `A` |
| `silmaril.shapes.elf.index` | `IndexIs X ix`: the lookup index of `X` is `ix` |
| `silmaril.shapes.elf.kind` | `KindIs X k`: `X` is an object of kind `k` |
| `silmaril.shapes.elf.symbol_at` | `SymbolAt X t i s`: entry `i` of table `t` is `s` |
| `silmaril.shapes.elf.lookup` | `Lookup X sel d`: the selector `sel` denotes `d` |
| `silmaril.shapes.elf.needed` | `Needed X ns`: the `DT_NEEDED` names are `ns` |
| `silmaril.shapes.elf.relocs` | `Relocs X sel rs`: the relocations `sel` names are `rs` |
| `silmaril.shapes.elf.placement` | `Placement X base`: `X` may be loaded at `base` |
| `silmaril.shapes.elf.code_at` | `CodeAt X v code`: `code` is mapped read-only executable at `v` |
| `silmaril.shapes.elf.binds` | `Binds X sel v code`: `sel` denotes the plain function at `v`, code `code` (compound: `lookup` ∧ `code_at`, `Shapes.binds_iff`) |
| `silmaril.shapes.elf.entry_point` | `EntryIs X v`: the entry point (`e_entry`) of `X` is `v` |

They sit beside the loader shapes `silmaril.shapes.elf.loads` and `silmaril.shapes.elf.entry`
(`Silmaril.Project.Shapes.Elf`, the LPS `ET_EXEC` loader), which these do not replace.

A row, for `adler32_z` of a registered `libz.so.1` (`zlib.libz132`), names the function by a
lookup rather than by section, symbol and program-header indices:

```lean
silmaril instance zlib.libz132.adler32_z := silmaril.shapes.elf.binds
  (X := zlib.libz132) (sel := .dyn { name := nameOf "adler32_z" })
  (v := 0x3350) (code := Zlib.adler32zCode)
```

Trust: a row is a closed `Prop`. A consumer that *assumes* the parse row of a file (an AST emitted
by a tool, not yet checked) takes it as a hypothesis, or cites the open problem
(`@[conjecture]`); it is never an axiom.
-/

@[expose] public section

namespace Silmaril.Elf

/-- **The entry point of `F` is `v`** (`e_entry`; for `ET_DYN`, relative to the load base). -/
def EntryIs (F : Silmaril.X86.Link.Blob) (v : Nat) : Prop := ∃ A, Parses F A ∧ A.header.entry = v

end Silmaril.Elf

namespace Silmaril.Elf.Shapes

open Silmaril.Project (Value)
open Silmaril.Formats.ELF (NameBytes ObjectSymbol)

/-- The file of a value. -/
abbrev file {V : Type} (X : Value V) := blobOf X.bytes

/-- **The metadata of `X` is `A`.** -/
@[problem "silmaril.shapes.elf.parses" (title := "The parse of an ELF file is a given AST")]
def Parses {V : Type} (X : Value V) (A : File) : Prop := Silmaril.Elf.Parses (file X) A

/-- **The lookup index of `X` is `ix`.** -/
@[problem "silmaril.shapes.elf.index" (title := "The lookup index of an ELF file")]
def IndexIs {V : Type} (X : Value V) (ix : Index) : Prop :=
  ∃ A, Silmaril.Elf.Parses (file X) A ∧ Index.build A = some ix

/-- **`X` is an object of kind `k`.** -/
@[problem "silmaril.shapes.elf.kind" (title := "An ELF file's object kind")]
def KindIs {V : Type} (X : Value V) (k : Kind) : Prop := Silmaril.Elf.KindIs (file X) k

/-- **Entry `i` of the symbol table `t` of `X` is `s`.** -/
@[problem "silmaril.shapes.elf.symbol_at" (title := "A symbol table entry of an ELF file")]
def SymbolAt {V : Type} (X : Value V) (t : Table) (i : Nat) (s : ObjectSymbol) : Prop :=
  Silmaril.Elf.SymbolAt (file X) t i s

/-- **In `X`, the selector `sel` denotes `d`.** -/
@[problem "silmaril.shapes.elf.lookup" (title := "What a name denotes in an ELF file")]
def Lookup {V : Type} (X : Value V) (sel : Sel) (d : Option Def) : Prop :=
  Silmaril.Elf.Lookup (file X) sel d

/-- **The `DT_NEEDED` names of `X` are `ns`.** -/
@[problem "silmaril.shapes.elf.needed" (title := "The libraries an ELF file needs")]
def Needed {V : Type} (X : Value V) (ns : List NameBytes) : Prop := Silmaril.Elf.Needed (file X) ns

/-- **The relocations of `X` that `sel` names are `rs`.** -/
@[problem "silmaril.shapes.elf.relocs" (title := "The relocations of an ELF file")]
def Relocs {V : Type} (X : Value V) (sel : File.RelocSel) (rs : List File.Reloc) : Prop :=
  Silmaril.Elf.Relocs (file X) sel rs

/-- **`X` may be loaded at `base`.** -/
@[problem "silmaril.shapes.elf.placement" (title := "A load base an ELF file admits")]
def Placement {V : Type} (X : Value V) (base : Nat) : Prop := Silmaril.Elf.Placement (file X) base

/-- **`X` maps `code` read-only executable at `v`.** -/
@[problem "silmaril.shapes.elf.code_at" (title := "The code an ELF file maps at an address")]
def CodeAt {V : Type} (X : Value V) (v : Nat) (code : List (BitVec 8)) : Prop :=
  Silmaril.Elf.CodeAt (file X) v code

/-- **`X` binds `sel` to the plain function at `v` with code `code`.** -/
@[problem "silmaril.shapes.elf.binds" (title := "A name of an ELF file binds a function with given code")]
def Binds {V : Type} (X : Value V) (sel : Sel) (v : Nat) (code : List (BitVec 8)) : Prop :=
  Silmaril.Elf.Binds (file X) sel v code

/-- **The entry point of `X` is `v`.** -/
@[problem "silmaril.shapes.elf.entry_point" (title := "The entry point of an ELF file")]
def EntryIs {V : Type} (X : Value V) (v : Nat) : Prop := Silmaril.Elf.EntryIs (file X) v

end Silmaril.Elf.Shapes
