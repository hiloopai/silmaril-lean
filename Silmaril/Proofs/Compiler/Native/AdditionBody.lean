module

public import Silmaril.Compiler.Native.Emit.AdditionBody.Defs
public import Silmaril.Compiler.Native.Emit.Scalar.Thms
public import Silmaril.Compiler.Native.Correctness.AdditionLower.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.AdditionBody
open Silmaril Silmaril.X86
open Correctness
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

/-- Exact actual Mir operations, before any native execution. -/
theorem selected (left right : Word) :
    (operations left right).map (fun operation => Silmaril.Compile.Mir.Instr.op operation.lir) =
      (AdditionLower.body left right).instrs.toList := rfl

/-- The actual operation renderer used by Emit.function selects this text.
Text-to-canonical-byte assembly adequacy is separate. -/
theorem rendered (left right : Word) :
    (AdditionLower.body left right).instrs.toList.foldlM (fun text instruction => do
      let emitted ← match instruction with
        | .op operation => Asm.operation operation
        | _ => .error "not a scalar operation"
      pure (text ++ emitted)) "" = .ok (render left right) := rfl

theorem instruction_count (left right : Word) : (instructions left right).length = 26 := rfl

theorem code_length (left right : Word) : (code left right).length = 109 :=
  Scalar.code_length (operations left right)

/-- Pure virtual values are calculated independently; actual physical slot
backing and machine instruction success are derived by execute. -/
theorem evaluated (left right : Word) :
    Scalar.evaluate (operations left right) .empty = some (AdditionLower.bodyFrame .empty left right) := rfl

theorem execute (stack : Word) (before : X86.MState) (left right : Word) (entry : Entry stack before) :
    ∃ after, Prologue.Executes (instructions left right) before after ∧ Ready stack before after left right :=
  Scalar.sequence stack before .empty (operations left right) _ entry (Scalar.Represents.empty _ _) (evaluated left right)

/-- The real physical virtual-register-10 slot now holds the actual Mir
result word, with no supplied body trace or result-slot premise. -/
theorem result_word {stack : Word} {before after : X86.MState} {left right : Word}
    (ready : Ready stack before after left right) :
    after.memory.readBytes (stack - 96).toNat 8 = some
      (Silmaril.Machine.LittleEndian.encodeWords [AdditionLower.bodyValue left right]) := by
  have held := ready.represented 8 (AdditionLower.bodyValue left right) rfl
  change Ext.HoldsLE after.memory (stack - 96).toNat 8 (AdditionLower.bodyValue left right) at held
  simpa only [Ext.HoldsLE, Ext.leBytes_eight] using held

/-- Every read wholly above the nine scalar slots is exactly preserved,
including a read that originally faulted. -/
theorem preserves_read {stack : Word} {before after : X86.MState} {left right : Word}
    (ready : Ready stack before after left right) (address count : Nat) (above : stack.toNat - 24 ≤ address) :
    after.memory.readBytes address count = before.memory.readBytes address count := by
  apply ready.memory.readBytes
  intro offset bound inside
  unfold Scalar.footprint at inside
  omega

/-- All existing integer SysV callee-saved registers survive the actual body.
RAX/R10 and arithmetic flags remain explicitly designated scratch state. -/
theorem callee_saved {stack : Word} {before after : X86.MState} {left right : Word}
    (ready : Ready stack before after left right) :
    ∀ register ∈ sysv64.calleeSaved, after.core.read register = before.core.read register := by
  intro register member
  exact ready.registers register
    (by cases register <;> simp_all [sysv64]) (by cases register <;> simp_all [sysv64])

theorem reserved_preserved {stack : Word} {before after : X86.MState} {left right : Word}
    (ready : Ready stack before after left right) (entry : Entry stack before) :
    after.memory.readBytes (stack - 16).toNat 8 = before.memory.readBytes (stack - 16).toNat 8 := by
  apply preserves_read ready
  have address : (stack - 16).toNat = stack.toNat - 16 := Ext.toNat_sub_ofNat (k := 16) (by have := entry.lower; omega) (by decide)
  rw [address]
  omega

/-- Actual body execution supplies the physical result premise required by
the frozen epilogue. Saved-BP and return reads are independent initial words,
and their preservation follows from the body's exact write footprint. -/
theorem epilogue_entry (caller before after : X86.MState) (left right exit : Word)
    (entry : Entry (caller.core.read .rsp) before)
    (ready : Ready (caller.core.read .rsp) before after left right)
    (saved : before.memory.readBytes (caller.core.read .rsp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [caller.core.read .rbp]))
    (returned : before.memory.readBytes (caller.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit])) :
    Epilogue.Entry caller after (AdditionLower.bodyValue left right) exit := by
  refine ⟨(ready.registers .rbp (by decide) (by decide)).trans entry.base, result_word ready, ?_, ?_⟩
  · have address : (caller.core.read .rsp - 8).toNat = (caller.core.read .rsp).toNat - 8 :=
      Ext.toNat_sub_ofNat (k := 8) (by have := entry.lower; omega) (by decide)
    have above : (caller.core.read .rsp).toNat - 24 ≤ (caller.core.read .rsp - 8).toNat := by rw [address]; omega
    exact (preserves_read ready _ 8 above).trans saved
  · exact (preserves_read ready _ 8 (by omega)).trans returned

end Silmaril.Compiler.Native.Emit.AdditionBody
