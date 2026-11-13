module

public import Silmaril.Compiler.Native.Optimize.Validation.Defs
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.Validation

open Silmaril.Machine

/-- A concrete interpretation of symbolic inputs, expression references and
effect results. Partiality retains unwritten registers and failed operations. -/
structure Interpretation where
  input : Nat → Option Lir.Word
  slot : Nat → Option Lir.Word
  value : Nat → Option Lir.Word
  address : String → Nat → Option Lir.Word
  load : Nat → Option Lir.Word
  result : Nat → Nat → Option Lir.Word

def Expr.eval (i : Interpretation) : Expr → Option Lir.Word
  | .input r => i.input r
  | .slot n => i.slot n
  | .const w => some w
  | .unary op a => (i.value a).map op.eval
  | .binary op a b => (i.value a).bind fun x => (i.value b).bind (op.eval x)
  | .float op a b => (i.value a).bind fun x => (i.value b).map (op.eval x)
  | .addr sym off => i.address sym off
  | .load event => i.load event
  | .result event index => i.result event index

/-- DAG references to a constant must denote the constant's word. -/
def ConstantsAgree (nodes : Array Expr) (i : Interpretation) : Prop :=
  ∀ index word, nodes[index]? = some (.const word) → i.value index = some word

/-- Symbolic constant normalization preserves the partial concrete evaluator.
It cannot turn a failing division/remainder into a successful constant. This
lemma covers one checker component, not the whole block validator. -/
theorem normalize_eval (nodes : Array Expr) (i : Interpretation)
    (constants : ConstantsAgree nodes i) (e : Expr) :
    (normalize nodes e).eval i = e.eval i := by
  cases e with
  | unary op a =>
    simp only [normalize]
    split
    · rename_i word hword
      simp only [Expr.eval, constants a word hword, Option.map_some]
    · rfl
  | binary op a b =>
    simp only [normalize]
    split
    · rename_i left right hleft hright
      split
      · rename_i word hword
        simp only [Expr.eval, constants a left hleft, constants b right hright,
          Option.bind_some, hword]
      · rfl
    · rfl
  | _ => rfl

end Silmaril.Compiler.Native.Optimize.Validation
