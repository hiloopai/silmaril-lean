module

public import Silmaril.Elf.Corpus.SqliteRead.Defs
public import Silmaril.Machine.SqliteRead.Thms
public import Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.Functions.Part0
import Silmaril.Proofs.Elf.Corpus.SqliteRead

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteRead

open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext.Wire (Platform)
open Silmaril.Machine SqliteRead Behaviour Observable
open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So

/-- The local `readDbPage` function symbol encloses the selected call site. -/
theorem symbol_identity :
    Staged.Reader.PartIs F [⟨1146992, 24⟩, ⟨1187650, 11⟩] (Parse.symbol sh27 1146992) s26_941 ∧
    s26_941.name = "readDbPage".toUTF8.data.toList.map UInt8.toBitVec ∧
    s26_941.kind = 2 ∧ s26_941.raw.value = 0x4b020 ∧ s26_941.raw.size = 315 ∧
    s26_941.raw.value ≤ region.base ∧
    region.base + region.bytes.length ≤ s26_941.raw.value + s26_941.raw.size :=
  ⟨sym_26_941, by decide +kernel⟩

/-- The selected bytes are in the pinned ELF's executable `PT_LOAD`. -/
theorem code_at : CodeAt F region.base region.bytes :=
  Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

/-- The admitted offset is exact before interpreting it as a signed `i64`. -/
theorem request_offset {initial : MState} {page : PageRead} {methods target : Word}
    (entry : Entry initial page methods target) : page.request.offset.toNat = page.index * page.count.toNat := by
  have bound := entry.signedRange
  rw [PageRead.request, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- At the admitted entry the cut retires all three instructions, supplies
the four arguments and transfers control to the installed address. -/
theorem run_dispatch {platform : Platform} {initial : MState} {page : PageRead} {methods target : Word}
    (entry : Entry initial page methods target) :
    ∃ next, Dispatches platform initial page.request target next :=
  Proofs.Elf.Corpus.SqliteRead.run_dispatch entry

/-- The call only changes the stack slot, not the output buffer. -/
theorem buffer_unchanged {platform : Platform} {initial next : MState} {page : PageRead} {methods target : Word}
    (entry : Entry initial page methods target) (cut : Dispatches platform initial page.request target next)
    (index : Nat) (within : index < page.count.toNat) :
    next.memory.bytes.get? (page.buffer.toNat + index) = initial.memory.bytes.get? (page.buffer.toNat + index) :=
  Proofs.Elf.Corpus.SqliteRead.buffer_unchanged entry cut index within

/-- Transfer the VM's no-UB dispatch contract to `X86.Ext.Wire.step`.
`Safe` is separate from the loaded-code and ABI premises; this theorem does
not execute the handler or require it to return. -/
theorem sound {platform : Platform} {initial : MState} {page : PageRead} {methods target : Word} {env : Context}
    (entry : Entry initial page methods target) (safe : Safe ((contract env).spec page.request)) :
    observe (run platform 3 initial) ∈ (contract env).spec page.request :=
  Proofs.Elf.Corpus.SqliteRead.sound entry safe

end Silmaril.Elf.Corpus.SqliteRead
