module

public import Silmaril.Compiler.Native.Emit.Epilogue.Defs
public import Silmaril.Compiler.Native.Emit.Prologue.Thms
public import Silmaril.Compiler.Native.Emit.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionLower.Thms
public import Silmaril.X86.Ext.SymExec
public import Silmaril.X86.Ext.Store
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.Epilogue
open Silmaril Silmaril.X86
open Silmaril.Process (Memory)
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
attribute [local cbv_eval] String.toUTF8_eq_toByteArray

private theorem decimalDigits (number : Nat) :
    Nat.toDigits 10 number = if number < 10 then [number.digitChar]
      else Nat.toDigits 10 (number / 10) ++ [(number % 10).digitChar] :=
  Nat.toDigits_eq_ite (by decide)
attribute [local cbv_eval] decimalDigits Nat.repr_eq_ofList_toDigits Nat.toString_eq_ofList_toDigits

private theorem decimalDigit8 : Nat.digitChar 8 = '8' :=
  Nat.digitChar_eq_eight.mpr rfl
attribute [local cbv_eval] decimalDigit8

theorem code_length : code.length = 6 := by decide +kernel

theorem code_bytes : code = [0x48, 0x8b, 0x45, 0xa8, 0xc9, 0xc3] := by decide +kernel

theorem render_equivalent : render = "  mov rax, QWORD PTR [rbp - 88]\n  leave\n  ret\n" := by cbv

private def coreWith (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) : X86.State :=
  { regs := fun r => if r = .rsp then sp else if r = .rbp then bp else if r = .rax then ax else initial.read r,
    rip := pc, flags, fsBase := initial.fsBase }

private theorem coreWith_read_rsp (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).read .rsp = sp := by simp [coreWith, State.read]
private theorem coreWith_read_rbp (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).read .rbp = bp := by simp [coreWith, State.read]
private theorem coreWith_read_rax (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).read .rax = ax := by simp [coreWith, State.read]

private theorem coreWith_initial (initial : X86.State) :
    coreWith initial initial.rip (initial.read .rsp) (initial.read .rbp) (initial.read .rax)
      initial.flags = initial := by
  cases initial with
  | mk regs rip flags fsBase =>
    simp only [coreWith, State.read, State.mk.injEq, and_true]
    funext r
    cases r <;> rfl

private theorem coreWith_regs (initial : X86.State) (pc sp bp ax : Word) (flags : Flags)
    (r : Reg) (hrsp : r ≠ .rsp) (hrbp : r ≠ .rbp) (hrax : r ≠ .rax) :
    (coreWith initial pc sp bp ax flags).read r = initial.read r := by
  simp [coreWith, State.read, hrsp, hrbp, hrax]

private theorem coreWith_write_rsp (initial : X86.State) (pc sp bp ax value : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).write .rsp value = coreWith initial pc value bp ax flags := by
  simp only [coreWith, State.write, State.mk.injEq, and_true]
  funext r
  cases r <;> simp [Machine.RegisterFile.write, State.read]
private theorem coreWith_write_rbp (initial : X86.State) (pc sp bp ax value : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).write .rbp value = coreWith initial pc sp value ax flags := by
  simp only [coreWith, State.write, State.mk.injEq, and_true]
  funext r
  cases r <;> simp [Machine.RegisterFile.write, State.read]
private theorem coreWith_write_rax (initial : X86.State) (pc sp bp ax value : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).write .rax value = coreWith initial pc sp bp value flags := by
  simp only [coreWith, State.write, State.mk.injEq, and_true]
  funext r
  cases r <;> simp [Machine.RegisterFile.write, State.read]

private theorem coreWith_rip (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).rip = pc := rfl
private theorem coreWith_set_rip (initial : X86.State) (pc sp bp ax next : Word) (flags : Flags) :
    { coreWith initial pc sp bp ax flags with rip := next } =
      coreWith initial next sp bp ax flags := rfl
private theorem coreWith_set_flags (initial : X86.State) (pc sp bp ax : Word) (flags next : Flags) :
    { coreWith initial pc sp bp ax flags with flags := next } =
      coreWith initial pc sp bp ax next := rfl

private theorem coreWith_set_flags_rip (initial : X86.State) (pc sp bp ax next : Word)
    (flags updated : Flags) :
    { coreWith initial pc sp bp ax flags with flags := updated, rip := next } =
      coreWith initial next sp bp ax updated := rfl

private theorem slot_address (initial : X86.State) (pc stack currentSp ax next : Word) (flags : Flags) :
    (Prologue.slot 10).addr (coreWith initial pc currentSp (stack - 8) ax flags) next = stack - 96 := by
  have displacement : (-(BitVec.ofNat 32 (8 * (10 + 1)))).signExtend 64 = -(88 : Word) := by decide +kernel
  simp only [Prologue.slot, Ext.Mem.ofReg, Ext.Mem.addr, Ext.Base.value_reg,
    coreWith_read_rbp, Option.map_none, Option.getD_none]
  rw [displacement]
  change stack - 8 + (0 : Word) + -(88 : Word) = stack - 96
  rw [add_zero, ← sub_eq_add_neg, sub_sub]
  rfl

private theorem load_generic (target : Ext.Mem) (state : X86.State) (memory : Memory) (value : Word)
    (length : (Ext.Instr.load .q .rax target).length = 4)
    (held : memory.readBytes (target.addr state (state.rip + 4)).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [value])) :
    Ext.exec (.load .q .rax target) state memory =
      .ok { state.write .rax value with rip := state.rip + 4 } memory := by
  have holds : Ext.HoldsLE memory (target.addr state (state.rip + 4)).toNat 8 value := by
    simpa only [Ext.HoldsLE, Ext.leBytes_eight] using held
  have loaded := Ext.loadN_of_holdsLE_eight holds
  simp only [Ext.exec, length, Ext.readRM, Ext.retire]
  change (match ((Ext.loadN memory (target.addr state (state.rip + 4)) 8).map (fun v => v)).map
      (fun v => (state.write .rax v, memory)) with
    | some (next, mem) => Ext.Result.ok { next with rip := state.rip + 4 } mem
    | none => Ext.Result.dataFault) = _
  rw [loaded]
  rfl

private theorem exec_load (initial : X86.State) (pc stack currentSp ax value : Word) (flags : Flags)
    (memory : Memory) (held : memory.readBytes (stack - 96).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [value])) :
    Ext.exec (.load .q .rax (Prologue.slot 10))
      (coreWith initial pc currentSp (stack - 8) ax flags) memory =
      .ok (coreWith initial (pc + 4) currentSp (stack - 8) value flags) memory := by
  have slot : Prologue.slot 10 = Ext.Mem.ofReg .rbp none (0xffffffa8 : BitVec 32) := rfl
  have length : (Ext.Instr.load .q .rax (Prologue.slot 10)).length = 4 := by rw [slot]; decide +kernel
  have actual := load_generic (Prologue.slot 10) (coreWith initial pc currentSp (stack - 8) ax flags)
    memory value length (by simpa only [slot_address, coreWith_rip] using held)
  simpa only [coreWith_write_rax, coreWith_rip, coreWith_set_rip] using actual

private theorem exec_leave (initial : X86.State) (pc currentSp stack ax savedBp : Word) (flags : Flags)
    (memory : Memory) (saved : memory.readBytes (stack - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [savedBp])) :
    Ext.exec .leave (coreWith initial pc currentSp (stack - 8) ax flags) memory =
      .ok (coreWith initial (pc + 1) stack savedBp ax flags) memory := by
  have popped := X86.popWord_of_readBytes (s := coreWith initial pc (stack - 8) (stack - 8) ax flags)
    (by simpa only [coreWith_read_rsp] using saved)
  simp only [Ext.exec, coreWith_read_rbp, coreWith_write_rsp, popped, Option.map_some,
    Ext.retire, coreWith_rip, coreWith_read_rsp, coreWith_write_rbp, coreWith_set_rip]
  change Ext.Result.ok (coreWith initial (pc + 1) (stack - 8 + 8) savedBp ax flags) memory = _
  rw [sub_add_cancel]

private theorem exec_ret (initial : X86.State) (pc stack bp ax exit : Word) (flags : Flags)
    (memory : Memory) (returned : memory.readBytes stack.toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit])) :
    Ext.exec .ret (coreWith initial pc stack bp ax flags) memory =
      .ok (coreWith initial exit (stack + 8) bp ax flags) memory := by
  have popped := X86.popWord_of_readBytes (s := coreWith initial pc stack bp ax flags)
    (by simpa only [coreWith_read_rsp] using returned)
  simp only [Ext.exec, popped, coreWith_write_rsp, coreWith_read_rsp, coreWith_set_rip]
  rfl

private theorem phases (caller before : X86.MState) (value exit : Word) (entry : Entry caller before value exit) :
    ∃ one two final : X86.State,
      Ext.exec (.load .q .rax (Prologue.slot 10)) before.core before.memory = .ok one before.memory ∧
      Ext.exec .leave one before.memory = .ok two before.memory ∧
      Ext.exec .ret two before.memory = .ok final before.memory ∧
      one.rip = before.core.rip + 4 ∧ two.rip = before.core.rip + 5 ∧
      Ready caller before ⟨final, before.memory⟩ value exit := by
  let stack := caller.core.read .rsp
  let bp := caller.core.read .rbp
  let ax := before.core.read .rax
  let currentSp := before.core.read .rsp
  let pc := before.core.rip
  let flags := before.core.flags
  have represented : coreWith before.core pc currentSp (stack - 8) ax flags = before.core := by
    change coreWith before.core before.core.rip (before.core.read .rsp) (caller.core.read .rsp - 8)
      (before.core.read .rax) before.core.flags = before.core
    rw [← entry.base]
    exact coreWith_initial _
  let c1 := coreWith before.core (pc + 4) currentSp (stack - 8) value flags
  let c2 := coreWith before.core (pc + 4 + 1) stack bp value flags
  let c3 := coreWith before.core exit (stack + 8) bp value flags
  have e1 : Ext.exec (.load .q .rax (Prologue.slot 10)) before.core before.memory = .ok c1 before.memory := by
    have actual := exec_load before.core pc stack currentSp ax value flags before.memory entry.result
    simpa only [represented] using actual
  have e2 : Ext.exec .leave c1 before.memory = .ok c2 before.memory :=
    exec_leave before.core (pc + 4) currentSp stack value bp flags before.memory entry.saved
  have e3 : Ext.exec .ret c2 before.memory = .ok c3 before.memory :=
    exec_ret before.core (pc + 4 + 1) stack bp value exit flags before.memory entry.returnAddress
  refine ⟨c1, c2, c3, e1, e2, e3, rfl, ?_, ?_⟩
  · change pc + 4 + 1 = pc + 5
    rw [add_assoc]
    rfl
  · exact ⟨rfl, coreWith_read_rsp _ _ _ _ _ _, coreWith_read_rbp _ _ _ _ _ _,
      coreWith_read_rax _ _ _ _ _ _, coreWith_regs _ _ _ _ _ _, rfl, rfl, rfl⟩

/-- Three real decoded steps derive restoration and the scalar result from
independently readable words, without any target execution premise. -/
theorem execute (caller before : X86.MState) (value exit : Word) (entry : Entry caller before value exit) :
    ∃ final, Prologue.Executes instructions before final ∧ Ready caller before final value exit := by
  obtain ⟨one, two, final, load, leave, ret, _, _, ready⟩ := phases caller before value exit entry
  exact ⟨⟨final, before.memory⟩,
    .cons _ _ before ⟨one, before.memory⟩ _ load
      (.cons _ _ ⟨one, before.memory⟩ ⟨two, before.memory⟩ _ leave
      (.cons _ _ ⟨two, before.memory⟩ ⟨final, before.memory⟩ _ ret (.nil _))), ready⟩

private theorem decode_load : Ext.decode ((code.drop 0).take 4) =
    some (.load .q .rax (Prologue.slot 10), 4) := by cbv
private theorem decode_leave : Ext.decode ((code.drop 4).take 1) = some (.leave, 1) := by cbv
private theorem decode_ret : Ext.decode ((code.drop 5).take 1) = some (.ret, 1) := by cbv

/-- An independently loaded real six-byte image executes two retirements and
returns to the supplied caller address. Loaded supplies actual fetch bounds. -/
theorem execute_fetched (caller before : X86.MState) (value exit : Word)
    (entry : Entry caller before value exit) (loaded : Ext.Loaded before.memory before.core.rip code) :
    ∃ middle final,
      Silmaril.Machine.Execution.run (Ext.stepOpt exit) 2 before = some middle ∧
      Ext.step exit middle = .returned final ∧ Ready caller before final value exit := by
  obtain ⟨one, two, final, load, leave, ret, onePc, twoPc, ready⟩ := phases caller before value exit entry
  have first : Ext.stepOpt exit before = some ⟨one, before.memory⟩ :=
    Ext.stepOpt_of_loaded loaded (by simp) (by rw [code_length]; decide +kernel) decode_load (by simp) load
  have second : Ext.stepOpt exit ⟨one, before.memory⟩ = some ⟨two, before.memory⟩ :=
    Ext.stepOpt_of_loaded loaded onePc (by rw [code_length]; decide +kernel) decode_leave (by simp) leave
  have returned : Ext.step exit ⟨two, before.memory⟩ = .returned ⟨final, before.memory⟩ :=
    Ext.step_returned_of_loaded loaded twoPc (by rw [code_length]) decode_ret ret ready.pc
  refine ⟨⟨two, before.memory⟩, ⟨final, before.memory⟩, ?_, returned, ready⟩
  rw [Silmaril.Machine.Execution.run_succ, first]
  change Silmaril.Machine.Execution.run (Ext.stepOpt exit) 1 ⟨one, before.memory⟩ = _
  rw [Silmaril.Machine.Execution.run_succ, second]
  rfl

/-- RAX supplies the actual INTEGER-state signed32 ABI result. Upper bits
are deliberately unconstrained by this existing ABI boundary. -/
theorem Ready.int32 {caller before final : X86.MState} {value exit : Word}
    (ready : Ready caller before final value exit) :
    Silmaril.C.Api.SysV.ResultAt final (some .int32) (value.setWidth 32) := by
  change (final.core.read .rax).setWidth 32 = value.setWidth 32
  rw [ready.result]

/-- The restored suffix supplies the existing limited integer-state SysV
return discipline once the body's other callee-saved registers agree. -/
theorem Ready.sysv_return {caller before final : X86.MState} {value exit : Word}
    (ready : Ready caller before final value exit) (base : Word)
    (bodySaved : ∀ register ∈ Silmaril.X86.sysv64.calleeSaved, register ≠ .rbp →
      before.core.read register = caller.core.read register) :
    Silmaril.C.Api.SysV.Return ⟨base, exit, caller⟩ final := by
  refine ⟨ready.pc, ready.stack, ?_⟩
  intro register member
  by_cases isBase : register = .rbp
  · exact isBase ▸ ready.base
  · have notSp : register ≠ .rsp := by cases register <;> simp_all [Silmaril.X86.sysv64]
    have notAx : register ≠ .rax := by cases register <;> simp_all [Silmaril.X86.sysv64]
    exact (ready.registers register notSp isBase notAx).trans (bodySaved register member isBase)


/-- The real addition body returns virtual register 10. The actual emitter
selects this suffix from its actual signature metadata for every ABI plan. -/
theorem addition_terminator (left right : Silmaril.Machine.Lir.Word) (unit index : Nat)
    (info : Silmaril.Compiler.Native.FunctionInfo) (plan : Silmaril.Machine.SystemV.Abi.CallPlan)
    (metadata : (Silmaril.Compiler.Native.Correctness.AdditionLower.artifact left right).functions.find?
      (·.name == (Silmaril.Compiler.Native.Correctness.AdditionLower.function left right).name) = some info) :
    Emit.terminator unit index (Silmaril.Compiler.Native.Correctness.AdditionLower.function left right) info plan
      (Silmaril.Compiler.Native.Correctness.AdditionLower.body left right).term = .ok render := by
  let expected : Silmaril.Compiler.Native.FunctionInfo :=
    { name := "main", signature := ⟨.int 4 true, [], false, true⟩,
      tags := ∅, frameBytes := 0, frameAlign := 16 }
  have found : (Silmaril.Compiler.Native.Correctness.AdditionLower.artifact left right).functions.find?
      (·.name == (Silmaril.Compiler.Native.Correctness.AdditionLower.function left right).name) = some expected := rfl
  have same : info = expected := Option.some.inj (metadata.symm.trans found)
  rw [same]
  rfl

/-- Both signature selection and the real scalar suffix are derived from the
actual Artifact; no successful native execution is assumed. -/
theorem addition_selected (left right : Silmaril.Machine.Lir.Word) (unit index : Nat) :
    ∃ info plan,
      (Silmaril.Compiler.Native.Correctness.AdditionLower.artifact left right).functions.find?
        (·.name == (Silmaril.Compiler.Native.Correctness.AdditionLower.function left right).name) = some info ∧
      Emit.functionPlan info = .ok plan ∧
      Emit.terminator unit index (Silmaril.Compiler.Native.Correctness.AdditionLower.function left right) info plan
        (Silmaril.Compiler.Native.Correctness.AdditionLower.body left right).term = .ok render := by
  obtain ⟨info, plan, metadata, selected, _⟩ := Prologue.addition_selected left right
  exact ⟨info, plan, metadata, selected, addition_terminator left right unit index info plan metadata⟩

/-- The actual bounded signed32 addition result is represented by RAX's low
32 bits once the physical result slot represents the actual Mir body word. -/
theorem Ready.addition_int32 {caller before final : X86.MState} {exit : Word}
    (left right : Int) (bounded : Silmaril.Compiler.Native.Correctness.AdditionSource.Bounds left right)
    (ready : Ready caller before final
      (Silmaril.Compiler.Native.Correctness.AdditionLower.bodyValue (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) exit) :
    Silmaril.C.Api.SysV.ResultAt final (some .int32) ((BitVec.ofInt 64 (left + right)).setWidth 32) := by
  simpa only [Silmaril.Compiler.Native.Correctness.AdditionLower.body_value left right bounded] using ready.int32

end Silmaril.Compiler.Native.Emit.Epilogue
