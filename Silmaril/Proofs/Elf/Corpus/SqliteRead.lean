module

public import Silmaril.Elf.Corpus.SqliteRead.Defs
public import Silmaril.Machine.SqliteRead.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteRead

open Silmaril.Elf.Corpus.SqliteRead
open Silmaril.Machine SqliteRead Behaviour Observable
open Silmaril.X86 (State MState Word pushWord pushWord_eq_some pushWord_readBytes pushWord_writesOnly)
open Silmaril.X86.Ext (Mem imulFlags loadN)
open Silmaril.X86.Ext.Wire
open Silmaril.Process (Memory)

private def loadMem : Mem := .ofReg .rdi none 0
private def slotMem : Mem := .ofReg .rax none 16
private def loadOp : Decoded := ⟨.canonical (.load .q .rax loadMem), [0x48, 0x8b, 0x07]⟩
private def mulOp : Decoded := ⟨.canonical (.imul .q .rcx (.reg .rdx)), [0x48, 0x0f, 0xaf, 0xca]⟩
private def callOp : Decoded := ⟨.callRM (.mem slotMem), [0xff, 0x50, 0x10]⟩

set_option maxRecDepth 4096

private theorem stepAt {platform : Platform} {state : MState}
    (code : state.memory.fetchBytes region.base region.bytes.length = some region.bytes)
    (offset : Nat) (op : Decoded) (addr : state.core.rip.toNat = region.base + offset)
    (start : offset < region.bytes.length) (within : offset + op.length ≤ region.bytes.length)
    (bytes : (region.bytes.drop offset).take op.length = op.bytes)
    (decoded : decode op.bytes = some op) :
    step platform continuation state =
      match exec platform op state.core state.memory with
      | .ok core memory =>
        if op.instr = .canonical .ret ∧ core.rip = continuation then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault op.instr
      | .divideError => .divideFault
      | .undefinedCondition cond => .undefinedCondition cond
      | .trap => .trapped := by
  apply step_of_fetch _ decoded
  rw [addr, ← bytes]
  exact Memory.readWith_sub_range code start within

private def loaded (initial : MState) (methods : Word) : MState :=
  ⟨{ initial.core.write .rax methods with rip := 0x4b110 }, initial.memory⟩

private def multiplied (initial : MState) (methods : Word) : MState :=
  let state := (loaded initial methods).core
  let index := state.read .rcx
  let count := state.read .rdx
  ⟨{ state.write .rcx (index * count) with flags := imulFlags index count, rip := 0x4b114 },
    initial.memory⟩

private theorem step_load {platform : Platform} {initial : MState} {page : PageRead}
    {methods target : Word} (entry : Entry initial page methods target) :
    step platform continuation initial = .retired (loaded initial methods) := by
  rw [stepAt entry.code 0 loadOp (by rw [entry.rip]; rfl) (by decide) (by decide) rfl (by decide +kernel)]
  have read : X86.Ext.readRM .q (.mem loadMem) initial.core initial.memory
      (initial.core.rip + BitVec.ofNat 64 loadOp.length) = some methods := by
    simp [X86.Ext.readRM, loadMem, X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, entry.file, entry.fileTable,
      show X86.Ext.Sz.q.bytes = 8 from rfl]
  simp only [exec, execWithLength, loadOp, X86.Ext.execWithLength, X86.Ext.exec] at read ⊢
  rw [read]
  simp [loaded, X86.Ext.retire, X86.Ext.Sz.write, entry.rip, Decoded.length]

private theorem step_mul {platform : Platform} {initial : MState} {page : PageRead}
    {methods target : Word} (entry : Entry initial page methods target) :
    step platform continuation (loaded initial methods) = .retired (multiplied initial methods) := by
  rw [stepAt (state := loaded initial methods) entry.code 3 mulOp rfl
    (by decide) (by decide) rfl (by decide +kernel)]
  rfl

private theorem step_call {platform : Platform} {initial : MState} {page : PageRead}
    {methods target : Word} (entry : Entry initial page methods target) :
    ∃ pushed after, pushWord (multiplied initial methods).core initial.memory continuation = some (pushed, after) ∧
      step platform continuation (multiplied initial methods) = .retired ⟨{ pushed with rip := target }, after⟩ := by
  let state := (multiplied initial methods).core
  have rsp : state.read .rsp = initial.core.read .rsp := by
    simp [state, multiplied, loaded]
  have stack : initial.memory.Permitted .write (state.read .rsp - 8#64).toNat 8 := by
    rw [rsp]; exact entry.stackWritable
  obtain ⟨pushed, after, push⟩ : ∃ pushed after,
      pushWord state initial.memory continuation = some (pushed, after) :=
    ⟨_, _, pushWord_eq_some stack⟩
  refine ⟨pushed, after, push, ?_⟩
  have rax : state.read .rax = methods := by simp [state, multiplied, loaded]
  have read : X86.Ext.readRM .q (.mem slotMem) state initial.memory
      (state.rip + BitVec.ofNat 64 callOp.length) = some target := by
    simp [X86.Ext.readRM, slotMem, X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, rax,
      show X86.Ext.Sz.q.bytes = 8 from rfl]
    exact entry.readSlot
  have next : state.rip + BitVec.ofNat 64 callOp.length = continuation := rfl
  have executed : exec platform callOp (multiplied initial methods).core (multiplied initial methods).memory =
      .ok { pushed with rip := target } after := by
    change (match X86.Ext.readRM .q (.mem slotMem) state initial.memory
        (state.rip + BitVec.ofNat 64 callOp.length) with
      | none => X86.Ext.Result.dataFault
      | some address =>
        match pushWord state initial.memory (state.rip + BitVec.ofNat 64 callOp.length) with
        | none => X86.Ext.Result.dataFault
        | some (core, memory) => X86.Ext.Result.ok { core with rip := address } memory) = _
    rw [read, next, push]
  rw [stepAt (state := multiplied initial methods) entry.code 7 callOp rfl
    (by decide) (by decide) rfl (by decide +kernel), executed]
  rfl

theorem run_dispatch {platform : Platform} {initial : MState} {page : PageRead} {methods target : Word}
    (entry : Entry initial page methods target) :
    ∃ next, Dispatches platform initial page.request target next := by
  obtain ⟨pushed, after, push, call⟩ := step_call (platform := platform) entry
  have rsp : (multiplied initial methods).core.read .rsp = initial.core.read .rsp := by
    simp [multiplied, loaded]
  have stackRead : initial.memory.Permitted .read
      ((multiplied initial methods).core.read .rsp - 8#64).toNat 8 := by
    rw [rsp]; exact entry.stackReadable
  refine ⟨⟨{ pushed with rip := target }, after⟩, ⟨?_, ?_, rfl, ?_, ?_, ?_⟩⟩
  · simp only [run, step_load entry, entry.rip, step_mul entry, show (loaded initial methods).core.rip =
      0x4b110 from rfl, call]
    rfl
  · rw [X86.pushWord_state push]
    simp [argument, PageRead.request, multiplied, loaded, entry.file, entry.buffer, entry.count, entry.index]
    have widened : page.count.setWidth 64 = BitVec.ofNat 64 page.count.toNat := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      exact Nat.lt_trans page.count.isLt (by decide)
    rw [widened, BitVec.ofNat_mul_ofNat]
  · rw [X86.pushWord_state push]
    simp [rsp]
  · simpa only [stackSlot, rsp] using pushWord_readBytes push stackRead
  · simpa only [stackSlot, rsp] using pushWord_writesOnly push

theorem buffer_unchanged {platform : Platform} {initial next : MState} {page : PageRead} {methods target : Word}
    (entry : Entry initial page methods target) (cut : Dispatches platform initial page.request target next)
    (index : Nat) (within : index < page.count.toNat) :
    next.memory.bytes.get? (page.buffer.toNat + index) = initial.memory.bytes.get? (page.buffer.toNat + index) := by
  apply cut.frame.2
  rcases entry.stackApart with above | below
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

theorem sound {platform : Platform} {initial : MState} {page : PageRead} {methods target : Word} {env : Context}
    (entry : Entry initial page methods target) (safe : Safe ((contract env).spec page.request)) :
    observe (run platform 3 initial) ∈ (contract env).spec page.request := by
  obtain ⟨next, dispatches⟩ := run_dispatch (platform := platform) entry
  rw [Observable.Contract.spec_of_pre ((safe_iff_admitted _ _).mp safe)]
  change observe (run platform 3 initial) = dispatch page.request
  rw [dispatches.executed]
  simp only [observe, dispatches.request]

end Silmaril.Proofs.Elf.Corpus.SqliteRead
