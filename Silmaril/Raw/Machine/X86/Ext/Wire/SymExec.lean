module

public import Silmaril.X86.Ext.Wire.Machine
public import Silmaril.X86.Ext.SymExec

/-! # Fetched wire steps from loaded code images -/
@[expose] public section
namespace Silmaril.X86.Ext.Wire
open Silmaril.X86 (Byte Word MState State)
open Silmaril.Process (Memory)

/-- Fetch from an immutable spelling in a loaded image, at its actual length. -/
theorem step_of_loaded {platform : Platform} {exit base : Word} {bytes : List Byte}
    {m : MState} {offset : Nat} {d : Decoded} (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + d.length ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take d.length) = some d) :
    step platform exit m =
      match exec platform d m.core m.memory with
      | .ok core memory =>
        if d.instr = .canonical .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault d.instr
      | .divideError => .divideFault
      | .undefinedCondition c => .undefinedCondition c
      | .trap => .trapped := by
  have pos := (decode_length decoded).1
  have hrip : m.core.rip.toNat = base.toNat + offset := by
    rw [at_offset]
    exact loaded.toNat_add (by omega)
  refine step_of_fetch (bytes := (bytes.drop offset).take d.length) ?_ decoded
  rw [hrip]
  exact loaded.fetchBytes_sub pos fits

/-- A retiring wire step from loaded code; useful for chaining actual slices. -/
theorem stepOpt_of_loaded {platform : Platform} {exit base : Word} {bytes : List Byte}
    {m : MState} {offset : Nat} {d : Decoded} {core : State} {memory : Memory}
    (loaded : Loaded m.memory base bytes)
    (at_offset : m.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + d.length ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take d.length) = some d)
    (not_ret : d.instr ≠ .canonical .ret)
    (executed : exec platform d m.core m.memory = .ok core memory) :
    stepOpt platform exit m = some ⟨core, memory⟩ := by
  rw [stepOpt_eq_some_iff, step_of_loaded loaded at_offset fits decoded, executed]
  simp [not_ret]

end Silmaril.X86.Ext.Wire
