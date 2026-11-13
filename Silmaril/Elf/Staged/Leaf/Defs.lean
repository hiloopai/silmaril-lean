module

public import Silmaril.Elf.Staged.Defs
public import Silmaril.Elf.Link.Dyn.Pages.Defs
public import Silmaril.X86.Ext.Decode
public import Silmaril.Prelude.Bytes.Defs

/-! # Leaf checks: one checker, two byte sources (`Silmaril.Elf.Staged.Leaf`)

A **leaf** is the unit an acceleration framework schedules: a named, closed Boolean check of a
small certificate `c : σ` against the bytes of a file, with one soundness lemma. The checker
`run r c` is written once, over an abstract byte source `r`, so the same definition runs

* **natively** on the `ByteArray` of an included file (`Leaf.native`, `fastRead`), and
* **in the kernel** on core's kernel bytes (`Leaf.kbytes`, `Silmaril.KBytes.readLE`) or on
  4 KiB page literals (`Leaf.kernel`, `pageRead`),

and both conclude the **same proposition** `P F c` about the **same file** `F = blobOf b`
(`Leaf.of_native`, `Leaf.of_kbytes`, `Leaf.of_kernel`, in `Thms`): the source-byte binding is
the `Sub` lemma of each source (`sub_fast`, `sub_kbytes`, `Check.sub_pages`), not a property of
the certificate.

The policy that picks a mode for a named leaf belongs to the trust framework
(`Silmaril.Prelude.Trust`); `Silmaril.Elf.Staged.Native` registers the native runs and provides
the `elf_leaf` tactic that selects between the two runs.

## Leaves defined here (`Thms`)

| name | certificate `σ` | proposition |
|---|---|---|
| `elf.layout` | `Layout` | `LayoutIs F L` |
| `elf.body` | `Layout × SectionHeader × Body` | `BodyIs F L sh b` |
| `elf.loader` | `Layout × Loader` | `LoaderIs F L ld` |
| `elf.rela` | `Nat × Nat × List Rela` (offset, first index, entries) | `EntriesAt F Parse.rela o 24 i es` |
| `elf.tiles` | `Nat × List Nat` (start, lengths) | `TilesAt F (fun _ _ => true) o lens` |
| `elf.tiles.x86` | `Nat × List Nat` | `TilesAt F x86Ok o lens` |
| `elf.symbols.byName`, `elf.symbols.byAddr` | a symbol index (`Silmaril.Elf.Staged.Symbols`) | its entries are the table's |

Unsupported, listed so nothing is registered for them yet: a symbol *trie* (the sorted index
stands in for it), DWARF line and DIE tables, `.eh_frame` function bounds, and windows of the
other tables (symbols, `REL`, `RELR`, hash tables).
-/

@[expose] public section

namespace Silmaril.Elf.Staged

open Silmaril.Elf.Check (Src)
open Silmaril.X86.Link (Blob)

/-- **A leaf check** (module doc): a named checker over any byte source, sound for every
source that answers as the file. -/
structure Leaf (σ : Type) where
  /-- The registry name (`elf.layout`, …). -/
  name : String
  /-- What a successful check establishes about the file. -/
  P : Blob → σ → Prop
  /-- The checker, over an abstract byte source. -/
  run : Src → σ → Bool
  sound : ∀ {r : Src} {F : Blob} {c : σ}, Check.Sub r F → run r c = true → P F c

/-- The native run: on the bytes of an included file. -/
def Leaf.native {σ : Type} (l : Leaf σ) (b : Silmaril.Formats.Bytes) (c : σ) : Bool :=
  l.run (fastRead b.data) c

/-- The kernel run: on the 4 KiB pages of a file. -/
def Leaf.kernel {σ : Type} (l : Leaf σ) (pg : List Silmaril.Elf.Link.DynElf.Chunk) (c : σ) :
    Bool :=
  l.run (Silmaril.Elf.Link.DynElf.pageRead 4096 pg) c

/-- The kernel run on core's kernel bytes (`Silmaril.KBytes`, `readLE`): a tree the kernel
reads with a few big-number operations per read. -/
def Leaf.kbytes {σ : Type} (l : Leaf σ) (x : Silmaril.KBytes) (c : σ) : Bool :=
  l.run x.readLE c

/-- The per-tile predicate of `elf.tiles.x86`: the local x86 model (`Silmaril.X86.Ext.decode`)
reads exactly one instruction of `l` bytes from the little-endian bytes `v`. -/
def x86Ok (l v : Nat) : Bool :=
  match Silmaril.X86.Ext.decode ((List.range l).map fun i => BitVec.ofNat 8 (v >>> (8 * i))) with
  | some (_, n) => n == l
  | none => false

end Silmaril.Elf.Staged
