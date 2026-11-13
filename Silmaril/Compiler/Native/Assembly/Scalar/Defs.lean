module

public import Silmaril.Compiler.Native.Assembly.Defs
/-! Modular register-arithmetic grammar extension and compositional source
lines. Tokenization and byte layout retain their existing actual meanings. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Assembly.Scalar
open Silmaril Silmaril.X86

inductive Spells : List String → Statement → Prop where
  | basic {tokens : List String} {statement : Statement} (spelled : Assembly.Spells tokens statement) :
      Spells tokens statement
  | arithmetic {operation destination source : String} {op : AluOp} {d s : Reg}
      (mnemonic : X86.Assembly.alu? operation = some op)
      (dst : RegToken destination d 64) (src : RegToken source s 64) :
      Spells [operation, destination, ",", source] (.plain (.alu .q op (.reg d) s))

inductive Lines : List (List String) → List Statement → Prop where
  | nil : Lines [] []
  | blank {lines : List (List String)} {statements : List Statement}
      (rest : Lines lines statements) : Lines ([] :: lines) statements
  | cons {line : List String} {statement : Statement} {lines : List (List String)} {statements : List Statement}
      (head : Spells line statement) (rest : Lines lines statements) :
      Lines (line :: lines) (statement :: statements)

def Parses (source : String) (statements : List Statement) : Prop :=
  Lines ((X86.Assembly.split '\n' source.toList).map (fun chars => X86.Assembly.tokenizeChars chars [] [])) statements

/-- Each source line receives exactly one terminating newline. -/
def linesText (lines : List String) : String :=
  lines.foldr (fun line tail => line ++ "\n" ++ tail) ""

end Silmaril.Compiler.Native.Assembly.Scalar
