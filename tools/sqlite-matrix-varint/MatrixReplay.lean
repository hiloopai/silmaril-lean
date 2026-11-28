module

public import Silmaril.Elf.Corpus.SqliteOneByteVarint.Thms
public import Silmaril.Elf.Link.ElfBind.Thms
public import Silmaril.Elf.Staged.Reader.Defs
import Silmaril.Elf.Staged.Reader.Thms

/-! Replay this module beside the digest-checked matrix ELF. -/

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteOneByteVarint.Matrix

open Silmaril.Elf.Link
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Staged.Reader (kread sub_kbytes)
open Silmaril.X86

namespace Canonical
export Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (K F)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So in
theorem read {α : Type} {reader : Rd α} {value : α}
    (checked : reader.run (kread K) = some value) :
    reader.run (blobRead F) = some value :=
  Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ checked

end Canonical

noncomputable def raw : ByteArray := include_bytes "libsqlite3.so"

kbytes_def K of_include raw

noncomputable abbrev file : Silmaril.X86.Link.Blob := Silmaril.Elf.blobOf ⟨raw⟩

def layout : Layout := ⟨0xf140, 0xe700, 0xfffff5b1⟩

/-- Both path windows are checked through the whole matrix file's executable
program header reader. -/
theorem codeAt (window : Window) : ElfBind.CodeAt file (layout.va window) (layout.code window) := by
  cases window <;> exact Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel)

/-- The two whole readers have the same 274 bytes within executable segments. -/
noncomputable def readerBytes : List Byte :=
  ElfBind.leBytes ((kread Canonical.K 0x10a40 274).getD 0) 274

theorem sameReader :
    ElfBind.CodeAt Canonical.F 0x10a40 readerBytes ∧ ElfBind.CodeAt file 0xe700 readerBytes :=
  ⟨Canonical.read (by decide +kernel),
   Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel)⟩

/-- A single indexed local function, using the ELF section's linked string table. -/
def localFunction (index : Nat) (name : String) (va size : Nat) : Rd Bool := do
  let sections ← ElfBind.Elf.shdrs
  let symbols ← Rd.ofOption (sections.find? (·.kind == 2))
  let strings ← Rd.ofOption (sections[symbols.link]?)
  Rd.guard ((index + 1) * 24 ≤ symbols.size ∧ strings.kind = 3)
  let offset := symbols.off + index * 24
  let symbol ← ElfBind.Elf.symAt offset
  let extent ← Silmaril.Elf.Link.DynElf.Elf.u64 (offset + 16)
  let label := name.toUTF8.data.toList.map UInt8.toNat
  Rd.guard (symbol.name + label.length + 1 ≤ strings.size)
  let named ← Silmaril.Elf.Link.DynElf.Elf.strIs (strings.off + symbol.name) label
  pure (named && decide (symbol.type = 2 ∧ symbol.bind = 0 ∧ symbol.shndx ≠ 0 ∧
    symbol.value = va ∧ extent = size))

theorem symbols :
    (localFunction 64 "btreeParseCellPtrNoPayload" 0xf140 50).run (blobRead file) = some true ∧
    (localFunction 25 "sqlite3GetVarint" 0xe700 274).run (blobRead file) = some true :=
  ⟨Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel),
   Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel)⟩

theorem placement_zero : ElfBind.Placement file 0 :=
  ElfBind.placement_of_rd (Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel))

theorem directCall : layout.DirectCall := by decide +kernel

-- The old immediate is valid in the original ELF. It must fail in this layout.
example : ¬ ({ layout with displacement := corpusLayout.displacement }).DirectCall := by decide +kernel

/-- The shared execution contract, now bound to the real matrix artifact. -/
theorem matrixFirstReturn {bias : Word} {entry : MState} {byte : Byte}
    (placement : ElfBind.Placement file bias)
    (image : ElfBind.RoLoaded file bias entry.memory)
    (admit : EntryAt layout bias entry byte) :
    ∃ final, ResultAt layout bias entry final byte :=
  firstReturn_at (by decide +kernel) directCall
    (fun w => (ElfBind.code_loaded (codeAt w) placement image).1) admit

#print axioms codeAt
#print axioms sameReader
#print axioms symbols
#print axioms placement_zero
#print axioms directCall
#print axioms matrixFirstReturn

end Silmaril.Elf.Corpus.SqliteOneByteVarint.Matrix
