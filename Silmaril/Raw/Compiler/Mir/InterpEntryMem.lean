module

public import Silmaril.Compiler.Mir.InterpStart.Defs
@[expose] public section

/-! # Memory preservation at interpreter entry -/

namespace Silmaril.Compile.Mir.Interp

/-- Starting a function keeps the supplied memory. -/
theorem start_mem (code : Array Func) (f : Nat) (args : List UInt64) (mem : Mem)
    (m : Machine) (hs : start code f args mem = .ok m) : m.mem = mem := by
  cases hf : code[f]? with
  | none => simp [start, hf] at hs
  | some fn =>
    cases hw : (Frame.empty fn.regs).writeAll fn.params args with
    | none => simp [start, hf, hw] at hs
    | some fr =>
      simp [start, hf, hw] at hs
      cases hs
      rfl

end Silmaril.Compile.Mir.Interp
