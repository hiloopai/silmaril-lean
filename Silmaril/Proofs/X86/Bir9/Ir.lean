module

public import Silmaril.X86.Bir9.Defs

/-!
# Bir9: basic equations of the IR semantics

`LInstr.exec_ext`, `Fault.liftR_toResult` and `runStmts_append`.
-/

@[expose] public section

namespace Silmaril.X86.Bir9

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

@[simp] theorem LInstr.exec_ext (i : Silmaril.X86.Ext.Instr) (s : XState) (m : Memory) (len : Nat) :
    (LInstr.ext i).exec s m len = liftR s.xmm (Silmaril.X86.Ext.exec i s.core m len) := rfl

@[simp] theorem Fault.liftR_toResult (f : Fault) (x : Xmm) : liftR x f.toResult = f.toX := by
  cases f <;> rfl

theorem runStmts_append (l₁ l₂ : List Stmt) (env : Env) :
    runStmts (l₁ ++ l₂) env =
      match runStmts l₁ env with
      | .error f => .error f
      | .ok env' => runStmts l₂ env' := by
  induction l₁ generalizing env with
  | nil => rfl
  | cons st rest ih =>
    simp only [List.cons_append, runStmts]
    cases st.run env with
    | error f => rfl
    | ok env' => exact ih env'

end Silmaril.X86.Bir9
