module

public import Silmaril.Compiler.Passes.Defs
@[expose] public section
namespace Silmaril.Compiler.Passes

/-- Pipeline concatenation runs the first selection before the second selection. -/
theorem runAll_append (first second : List MirPass) :
    Silmaril.Compile.Mir.Pass.runAll (first ++ second) =
      Silmaril.Compile.Mir.Pass.runAll second ∘
        Silmaril.Compile.Mir.Pass.runAll first := by
  induction first with
  | nil => rfl
  | cons pass rest inductionHypothesis =>
      simp only [List.cons_append, Silmaril.Compile.Mir.Pass.runAll, inductionHypothesis]
      rfl

end Silmaril.Compiler.Passes
