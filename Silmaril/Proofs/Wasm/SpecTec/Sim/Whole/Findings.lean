module

public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# The float and vector typing interfaces, after the typing fix

Round 1 refuted family V's `Vec.FloatTyping` and `Vec.VecTyping` (`Whole.not_floatTyping`,
`Whole.not_vecTyping`, at commit `0236b9f97`): both ask for a float numeral to inhabit some
`num_(e)`, which the IL evaluator's untested `SubE` matching made impossible. With the typing
track's fix to the ported semantics (`Sem.argSubOk`, `Sem.bindQuants`), those refutations no longer
hold: the two fields they used are now *proved* (`floatTyping_num`, `vecTyping_vec`). Whether the
remaining fields of the two structures hold is the float track's question.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-- `FloatTyping.num` holds in every `simEnv B`: every numeral, float or integer, inhabits
`num_(t)`. -/
theorem floatTyping_num (B : Builtins) (x : IL.Id) (n : Silmaril.Wasm.Execution.Core.NumVal) :
    Vec.TypedDep (simEnv B) x (Vec.numTypeV n.type) (Vec.numT x) (numV n) :=
  Typing.typedDep_num x n

/-- `VecTyping.vec` holds in every `simEnv B`. -/
theorem vecTyping_vec (B : Builtins) (a : BitVec 128) :
    TypedV (simEnv B) Vec.vecT (Vec.vecV a) :=
  Typing.typedV_vecT a

end Silmaril.Wasm.SpecTec.Sim.Whole
