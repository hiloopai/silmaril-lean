module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.BodyTypFlat

/-!
# IL typing of the covered instructions with two payloads, `select`, `ref.null`, constants

As `BodyTypFlat`, with no hypothesis: `call_indirect`, `table.copy`, `table.init`, `br_table`
(`hasTyp_pair`), `select`, `ref.null`, and the constants (`Whole.typedV_admin_val20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.BodyTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

set_option maxRecDepth 100000

variable {B : Builtins}

/-- A pair of payloads, the second typed in every term-only scope. -/
theorem hasTyp_pair {a b : IL.Id} {ta tb : Typ} {u v : Value}
    (hu : HasTyp (simEnv20 B) VarEnv.empty ta u) (hv : TypedV (simEnv20 B) tb v) :
    HasTyp (simEnv20 B) VarEnv.empty (.tupT [.mk a ta, .mk b tb]) (.tuple [u, v]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hu,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_bind hv _ valsOnly_empty _ _,
      hasTypTup_nil_iff.2 rfl⟩⟩⟩

theorem typedA_callIndirect (x : TableIdx) (y : TypeIdx) : TypedA B (.callIndirect x y) :=
  typedA_case rfl (hasTyp_pair (typedV_idxA (by decide) x _ valsOnly_empty)
    (typedV_idxA (by decide) y))
theorem typedA_tableCopy (x y : TableIdx) : TypedA B (.tableCopy x y) :=
  typedA_case rfl (hasTyp_pair (typedV_idxA (by decide) x _ valsOnly_empty)
    (typedV_idxA (by decide) y))
theorem typedA_tableInit (x : TableIdx) (y : ElemIdx) : TypedA B (.tableInit x y) :=
  typedA_case rfl (hasTyp_pair (typedV_idxA (by decide) x _ valsOnly_empty)
    (typedV_idxA (by decide) y))
theorem typedA_brTable (ls : List LabelIdx) (l : LabelIdx) : TypedA B (.brTable ls l) :=
  typedA_case rfl (hasTyp_pair (typedV_idxsA (by decide) ls _ valsOnly_empty)
    (typedV_idxA (by decide) l))

theorem typedA_select (ts : Option (List V2.ValType)) : TypedA B (.select ts) := by
  refine typedA_case rfl (hasTyp_iterT_opt_iff.2 ?_)
  rcases ts with _ | ts
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl, Whole.typedV_valTypes20 ts _ valsOnly_empty⟩

theorem typedA_refNull (t : V2.RefType) : TypedA B (.refNull t) :=
  typedA_case rfl (Whole.typedV_refType20 t _ valsOnly_empty)

theorem typedA_intConst (t : IntType) (b : BitVec t.width) : TypedA B (.intConst t b) :=
  Whole.typedV_admin_val20 (.num ⟨.int t, b⟩)

theorem typedA_floatConst (t : FloatType) (b : BitVec t.width) : TypedA B (.floatConst t b) :=
  Whole.typedV_admin_val20 (.num ⟨.float t, b⟩)

theorem typedA_vecConst (b : BitVec 128) : TypedA B (.vecConst b) :=
  Whole.typedV_admin_val20 (.vec b)

end Silmaril.Wasm.SpecTec.Sim20.BodyTyp
