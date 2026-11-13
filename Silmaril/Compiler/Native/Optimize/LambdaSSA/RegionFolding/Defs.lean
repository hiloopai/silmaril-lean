module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding.Defs
/-! Declared outgoing tuple shapes and actual finite region evaluation agreement.
These propositions reuse the existing operational semantics unchanged. -/
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.RegionFolding
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Machine.RTL (Opcode CallOracle packValues)
open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.Lir (Word)
open Folding

/-- The actual outgoing label carries a tuple of its declared width. -/
def Exits (labels : List Nat) (label : Nat) (value : Value Word) : Prop :=
  ∃ width words, labels[label]? = some width ∧ (Shape.tuple width).Holds value words

/-- Actual region evaluations agree, and each finite source exit has its shape
and leaves the initial memory unchanged. This is proof support, not an evaluator. -/
def EquivalentAt (oracle : CallOracle) (env : Semantics.Env Word) (labels : List Nat)
    (source target : Old.Region) : Prop :=
  ∀ (before : Memory) (label : Nat) (value : Value Word) (after : Memory),
    (Semantics.Region.Eval (Opcode.step oracle) env source before label value after ↔
      Semantics.Region.Eval (Opcode.step oracle) env target before label value after) ∧
    (Semantics.Region.Eval (Opcode.step oracle) env source before label value after →
      Exits labels label value ∧ after = before)


end Silmaril.Compiler.Native.Optimize.LambdaSSA.RegionFolding
