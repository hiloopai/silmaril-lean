module

public import Silmaril.Elf.Corpus.SqliteOneByteVarint.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint.Run

public section

namespace Silmaril.Elf.Corpus.SqliteOneByteVarint

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (F)
open Silmaril.X86

/-- Both windows are read-only executable spans of the included SQLite ELF. -/
theorem file_codeAt (window : Window) : CodeAt F window.va window.code :=
  Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint.file_codeAt window

/-- Both entry addresses and their enclosing function symbols are read from
the same ELF's static symbol table. -/
theorem symbol_at (w : Window) : ∃ symbol,
    SymbolAt F .symtab w.symbolIndex symbol ∧
    symbol.name = w.symbolName.toUTF8.data.toList.map UInt8.toBitVec ∧
    symbol.binding = 0 ∧ symbol.kind = 2 ∧ symbol.raw.sectionIndex ≠ 0 ∧
    symbol.raw.value = w.va ∧ w.code.length ≤ symbol.raw.size :=
  Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint.symbol_at w

/-- The same first-return proof for any two placements of this instruction
sequence whose wrapper encodes the checked direct call. -/
theorem firstReturn_at {layout : Layout} {bias : Word} {entry : MState} {byte : Byte}
    (checked : layout.checkPath = true) (direct : layout.DirectCall)
    (loaded : ∀ w : Window,
      Ext.Loaded entry.memory (bias + BitVec.ofNat 64 (layout.va w)) (layout.code w))
    (admit : EntryAt layout bias entry byte) :
    ∃ final, ResultAt layout bias entry final byte :=
  Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint.firstReturn_at checked direct loaded admit

/-- A caller can supply two mapped windows directly. This form admits a
standalone example with only the pages needed by the slice. -/
theorem firstReturn_of_loaded {bias : Word} {entry : MState} {byte : Byte}
    (loaded : ∀ w : Window, Ext.Loaded entry.memory (bias + BitVec.ofNat 64 w.va) w.code)
    (admit : Entry bias entry byte) :
    ∃ final, Result bias entry final byte :=
  Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint.firstReturn_of_loaded loaded admit

/-- The direct CALL, the callee's taken one-byte branch and RET, and the
caller's continuation to its outer first return, on the exact ELF windows at
the supplied bias. Placement and the read-only loaded image are premises. -/
theorem firstReturn {bias : Word} {entry : MState} {byte : Byte}
    (placement : Placement F bias.toNat)
    (image : Link.ElfBind.RoLoaded F bias entry.memory)
    (admit : Entry bias entry byte) :
    ∃ final, Result bias entry final byte :=
  Silmaril.Proofs.Elf.Corpus.SqliteOneByteVarint.firstReturn placement image admit

end Silmaril.Elf.Corpus.SqliteOneByteVarint
