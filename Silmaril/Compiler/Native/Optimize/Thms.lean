module

public import Silmaril.Compiler.Native.Optimize.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Thms
public import Silmaril.Compiler.Native.Optimize.LocalSSA.Thms
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize

open Silmaril.Compile

/-- The cleanup stage has the imported, independent Mir refinement contract.
This theorem intentionally makes no claim about the new SSA round trip. -/
theorem cleanup_correct (cfg : Config) :
    Contract.mirPass (Mir.Pass.runAll (cleanupPasses cfg)) :=
  Mir.Pass.runAll_correct _

/-- With local SSA disabled, the complete selected optimizer is a proved Mir pass. -/
theorem optimizeWith_correct_withoutSSA (cfg : Config) (h : cfg.localSSA = false) :
    Contract.mirPass (optimizeWith cfg) := by
  have same : optimizeWith cfg = Mir.Pass.runAll (cleanupPasses cfg) := by
    funext us
    simp only [optimizeWith, h, Bool.false_eq_true, ↓reduceIte]
  rw [same]
  exact cleanup_correct cfg

end Silmaril.Compiler.Native.Optimize
