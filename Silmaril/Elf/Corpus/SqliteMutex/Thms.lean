module

public import Silmaril.Elf.Corpus.SqliteMutex.Defs
public import Silmaril.Machine.SqliteMutex.Thms
public import Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.Functions.Part0
import Silmaril.Proofs.Elf.Corpus.SqliteMutex

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteMutex

open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext.Wire (Platform)
open Silmaril.Machine SqliteMutex Behaviour Observable
open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So

/-- The `.dynsym` row read from the pinned ELF identifies this exact region. -/
theorem symbol_identity :
    Staged.Reader.PartIs F [⟨4896, 24⟩, ⟨11476, 20⟩] (Parse.symbol sh4 4896) s3_77 ∧
    s3_77.name = "sqlite3_mutex_leave".toUTF8.data.toList.map UInt8.toBitVec ∧
    s3_77.kind = 2 ∧ s3_77.raw.value = region.base ∧ s3_77.raw.size = region.bytes.length :=
  ⟨sym_3_77, by decide +kernel⟩

/-- The region is the pinned ELF's actual bytes, in its executable `PT_LOAD`. -/
theorem code_at : CodeAt F region.base region.bytes :=
  Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

/-- The nonnull path retires the indirect jump in three steps. The handler's
instruction pointer changes, but `RDI`, `RSP`, all other GPRs and memory are
unchanged. Nothing is assumed about the handler's eventual return. -/
theorem run_dispatch {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller target) (nonNull : initial.core.read .rdi ≠ 0#64) :
    ∃ next, run platform caller 3 initial = .handlerEntry next ∧
      next.core.rip = target ∧ next.core.regs = initial.core.regs ∧ next.memory = initial.memory :=
  Proofs.Elf.Corpus.SqliteMutex.run_dispatch entry nonNull

/-- The null path returns in three steps, popping the caller's return address
without using the callback slot or writing memory. -/
theorem run_return {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller target) (isNull : initial.core.read .rdi = 0#64) :
    ∃ final, run platform caller 3 initial = .callerReturn final ∧
      final.core.rip = caller ∧ final.core.read .rsp = initial.core.read .rsp + 8 ∧
      final.memory = initial.memory :=
  Proofs.Elf.Corpus.SqliteMutex.run_return entry isNull

/-- Transfer the VM contract to the deterministic `X86.Ext.Wire.step` cut.
`Safe` is an explicit no-UB obligation over the VM behaviour set, discharged
by nullness or the calling context's lifetime, ownership and installation facts. -/
theorem sound {platform : Platform} {initial : MState} {caller target : Word} {env : Context}
    (entry : Entry initial caller target) (safe : Safe ((contract env).spec (initial.core.read .rdi))) :
    observe (run platform caller 3 initial) ∈ (contract env).spec (initial.core.read .rdi) :=
  Proofs.Elf.Corpus.SqliteMutex.sound entry safe

end Silmaril.Elf.Corpus.SqliteMutex
