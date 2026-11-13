module

public import Silmaril.Compiler.Core.Verified.StmtIf.Defs
/-! Kernel-checked branch polarity and safety boundary examples. -/

public section
namespace Silmaril.Compile.Core.Verified.StmtIf

open IntExpr

example : (choose (.lit 0) (.lit 10) (.lit 20)).val 0 = 10 := by decide
example : (choose (.lit 1) (.lit 10) (.lit 20)).val 0 = 20 := by decide
example : (choose (.lit (-1)) (.lit 10) (.lit 20)).val 0 = 10 := by decide

-- An unchosen overflowing arm does not make a defined branch undefined.
example : (choose (.lit 0) (.lit 10) (.lit 2147483648)).Ok 0 := by
  simp [choose, Term.Ok, Term.val, Guard.compare, Guard.holds, ConvInt.IsInt]
example : ¬ (choose (.lit 1) (.lit 10) (.lit 2147483648)).Ok 0 := by
  simp [choose, Term.Ok, Term.val, Guard.compare, Guard.holds, ConvInt.IsInt]

-- Selection computes the test over a variable at run time.
example : (choose .var (.bin .add .var (.lit 2)) (.lit 20)).val 5 = 7 := by decide
example : (choose .var (.bin .add .var (.lit 2)) (.lit 20)).val 1 = 20 := by decide

end Silmaril.Compile.Core.Verified.StmtIf
