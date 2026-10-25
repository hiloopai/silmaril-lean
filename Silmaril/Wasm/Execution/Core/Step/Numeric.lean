module

public import Silmaril.Wasm.Execution.Core.Store
public import Silmaril.Wasm.Numerics.Profile

@[expose] public section

/-! # Reduction family: scalar numeric instructions (pure, profile-dependent)

Spec rules (all 8 present): `Step_pure/unop-val`, `unop-trap`, `binop-val`,
`binop-trap`, `testop`, `relop`, `cvtop-val`, `cvtop-trap`.

Integer operators are the existing total functions of `Numerics/Integer.lean`
(`$unop_`/`$binop_` on `Inn` are singletons or empty on division by zero and
overflow, which is `intBinOp = .error`). Float operators use the profile-aware
result relations of `Numerics/Profile.lean`, so under `Profile.spec` they are
*exactly* the relations the V1 and Lime1 machines use (`floatUnOpRel`, …): the
Lime1 → Core numeric cases hold by `Iff.rfl`. The float `unop-trap`/`binop-trap`
rules apply when the result set is empty, which never happens (`*_self`
lemmas), so they are omitted for floats; integer `unop` never traps.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics

inductive NumericStep (P : Profile) : List Admin → List Admin → Prop where
  /-- `Step_pure/unop-val` (integers). -/
  | intUnOp {t : IntType} {op : IntUnOp} {x : BitVec t.width} :
      NumericStep P [.plain (.intConst t x), .plain (.intUnOp t op)]
        [.plain (.intConst t (intUnOp t op x))]
  /-- `Step_pure/unop-val` (floats). -/
  | floatUnOp {t : FloatType} {op : FloatUnOp} {x z : BitVec t.width}
      (h : floatUnOpP P t op x z) :
      NumericStep P [.plain (.floatConst t x), .plain (.floatUnOp t op)] [.plain (.floatConst t z)]
  /-- `Step_pure/binop-val` (integers). -/
  | intBinOp {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
      (h : intBinOp t op x y = .ok z) :
      NumericStep P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)]
        [.plain (.intConst t z)]
  /-- `Step_pure/binop-trap` (integers: division by zero, overflow). -/
  | intBinOpTrap {t : IntType} {op : IntBinOp} {x y : BitVec t.width} {e : IntTrap}
      (h : intBinOp t op x y = .error e) :
      NumericStep P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intBinOp t op)]
        [.trap]
  /-- `Step_pure/binop-val` (floats). -/
  | floatBinOp {t : FloatType} {op : FloatBinOp} {x y z : BitVec t.width}
      (h : floatBinOpP P t op x y z) :
      NumericStep P [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatBinOp t op)]
        [.plain (.floatConst t z)]
  /-- `Step_pure/testop`. -/
  | intTestOp {t : IntType} {op : IntTestOp} {x : BitVec t.width} :
      NumericStep P [.plain (.intConst t x), .plain (.intTestOp t op)]
        [constI32 (intTestOp t op x)]
  /-- `Step_pure/relop` (integers). -/
  | intRelOp {t : IntType} {op : IntRelOp} {x y : BitVec t.width} :
      NumericStep P [.plain (.intConst t x), .plain (.intConst t y), .plain (.intRelOp t op)]
        [constI32 (intRelOp t op x y)]
  /-- `Step_pure/relop` (floats). -/
  | floatRelOp {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width} :
      NumericStep P [.plain (.floatConst t x), .plain (.floatConst t y), .plain (.floatRelOp t op)]
        [constI32 (floatRelOp t op x y)]
  /-- `Step_pure/cvtop-val`. -/
  | convert {op : ConvertOp} {x : BitVec op.source.width} {z : BitVec op.target.width}
      (h : convertP P op x (.ok z)) :
      NumericStep P [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]
        [(Val.num ⟨op.target, z⟩).toAdmin]
  /-- `Step_pure/cvtop-trap`. -/
  | convertTrap {op : ConvertOp} {x : BitVec op.source.width} {e : FloatTrap}
      (h : convertP P op x (.error e)) :
      NumericStep P [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)] [.trap]

end Silmaril.Wasm.Execution.Core
