module

public import Silmaril.Prelude.Trust.Decl.Defs
public import Silmaril.Elf.Staged.Leaf.Thms

/-! # The ELF leaves in the trust registry

One `ProcDecl` per implemented leaf of `Silmaril.Elf.Staged.Leaf`, with the leaf's two runs as
the backends:

* native: `Leaf.native l b c`, compiled `fastRead` on a `ByteArray`, with `Leaf.of_native`;
* kernel: `Leaf.kernel l pg c`, `pageRead` on 4 KiB page literals, with `Leaf.of_kernel`.

Both conclude `l.P F c` about the same file. Every leaf shares the two runners, so each entry is
**bound** to its leaf constant: `sil_check elf.layout` accepts only checks of `Leaf.layout`, and
the audit counts a native axiom for `elf.layout` only if its statement is
`Leaf.native Leaf.layout … = true`. A native run trusts the compiled ELF readers (`readLayout`,
`Parse.*`, `Symbols.*`, the x86 decoder) and the Lean runtime; the kernel run does not.

Only implemented leaves are declared. Not registered here: a symbol trie, DWARF line and DIE
tables, `.eh_frame` bounds, and windows of other tables.
-/

@[expose] public section

namespace Silmaril.Procedures.elf

/-- Stage 1 layout: ELF header, program and section headers, section names. -/
def layout : Silmaril.Trust.ProcDecl where
  doc := "Stage 1 layout: ELF header, program and section headers, section names. Native: compiled fastRead on the file's ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.Leaf.native, ``Silmaril.Elf.Staged.Leaf.of_native⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Leaf.kernel, ``Silmaril.Elf.Staged.Leaf.of_kernel⟩
  format := some `elf
  bound := some ``Silmaril.Elf.Staged.Leaf.layout

/-- One section body (Parse.body). -/
def body : Silmaril.Trust.ProcDecl where
  doc := "One section body (Parse.body). Native: compiled fastRead on the file's ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.Leaf.native, ``Silmaril.Elf.Staged.Leaf.of_native⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Leaf.kernel, ``Silmaril.Elf.Staged.Leaf.of_kernel⟩
  format := some `elf
  bound := some ``Silmaril.Elf.Staged.Leaf.body

/-- The loader's view: PT_DYNAMIC, PT_INTERP and DT_STRTAB names. -/
def loader : Silmaril.Trust.ProcDecl where
  doc := "The loader's view: PT_DYNAMIC, PT_INTERP and DT_STRTAB names. Native: compiled fastRead on the file's ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.Leaf.native, ``Silmaril.Elf.Staged.Leaf.of_native⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Leaf.kernel, ``Silmaril.Elf.Staged.Leaf.of_kernel⟩
  format := some `elf
  bound := some ``Silmaril.Elf.Staged.Leaf.loader

/-- A window of a RELA table: offset, first index, entries. -/
def rela : Silmaril.Trust.ProcDecl where
  doc := "A window of a RELA table: offset, first index, entries. Native: compiled fastRead on the file's ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.Leaf.native, ``Silmaril.Elf.Staged.Leaf.of_native⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Leaf.kernel, ``Silmaril.Elf.Staged.Leaf.of_kernel⟩
  format := some `elf
  bound := some ``Silmaril.Elf.Staged.Leaf.rela

/-- Consecutive byte tiles lie in the file. -/
def tiles : Silmaril.Trust.ProcDecl where
  doc := "Consecutive byte tiles lie in the file. Native: compiled fastRead on the file's ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.Leaf.native, ``Silmaril.Elf.Staged.Leaf.of_native⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Leaf.kernel, ``Silmaril.Elf.Staged.Leaf.of_kernel⟩
  format := some `elf
  bound := some ``Silmaril.Elf.Staged.Leaf.tiles

/-- Each tile is one instruction of the local x86 model (Silmaril.X86.Ext.decode). -/
def tiles.x86 : Silmaril.Trust.ProcDecl where
  doc := "Each tile is one instruction of the local x86 model (Silmaril.X86.Ext.decode). Native: compiled fastRead on the file's ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.Leaf.native, ``Silmaril.Elf.Staged.Leaf.of_native⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Leaf.kernel, ``Silmaril.Elf.Staged.Leaf.of_kernel⟩
  format := some `elf
  bound := some ``Silmaril.Elf.Staged.Leaf.tilesX86

/-- A sorted by-name symbol index whose entries are the table's. -/
def symbols.byName : Silmaril.Trust.ProcDecl where
  doc := "A sorted by-name symbol index whose entries are the table's. Native: compiled fastRead on the file's ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.Leaf.native, ``Silmaril.Elf.Staged.Leaf.of_native⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Leaf.kernel, ``Silmaril.Elf.Staged.Leaf.of_kernel⟩
  format := some `elf
  bound := some ``Silmaril.Elf.Staged.Leaf.byName

/-- A sorted by-address symbol index whose entries are the table's. -/
def symbols.byAddr : Silmaril.Trust.ProcDecl where
  doc := "A sorted by-address symbol index whose entries are the table's. Native: compiled fastRead on the file's ByteArray."
  native := some ⟨``Silmaril.Elf.Staged.Leaf.native, ``Silmaril.Elf.Staged.Leaf.of_native⟩
  kernel := some ⟨``Silmaril.Elf.Staged.Leaf.kernel, ``Silmaril.Elf.Staged.Leaf.of_kernel⟩
  format := some `elf
  bound := some ``Silmaril.Elf.Staged.Leaf.byAddr

end Silmaril.Procedures.elf
