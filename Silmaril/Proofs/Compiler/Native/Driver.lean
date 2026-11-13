module

public import Silmaril.Compiler.Native.Driver.Defs
public import Silmaril.Compiler.Native.Frontend.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Driver

open Silmaril.Compile.Driver

/-- The native entry point preserves the imported frontend's exact typed-Ail
and diagnostic result; it additionally retains the real desugaring state. -/
theorem frontend_program (options : Options) (source : ByteArray) :
    (frontend options source).map Frontend.Result.program =
      Silmaril.Compile.Driver.frontend options source := by
  unfold frontend Silmaril.Compile.Driver.frontend
  cases filtered : asmText source with
  | error diagnostic => rfl
  | ok text =>
    simp only [bind, Except.bind]
    have erased := Frontend.run_program text
    cases retained : Frontend.run text with
    | error reject =>
      simp only [retained, Except.map] at erased
      rw [← erased]
      rfl
    | ok result =>
      simp only [retained, Except.map] at erased
      rw [← erased]
      rfl

end Silmaril.Compiler.Native.Driver
