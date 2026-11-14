module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Lits

/-!
# The encodings are typed, in `fixed`

The quantifiers of the fragment's rules range over `S`, `exp`, `val`, `num`, the operator sorts
and `bool`; every value the completeness proof instantiates them with has its type:
`typedV_enc` (an encoded expression is an `exp`), `typedV_lit_val`, `typedV_encNum`, the operator
lemmas, and `typedV_emptyS`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

set_option maxRecDepth 100000

theorem variant_exp : VariantDef envF "exp" (casesF "exp") := rfl
theorem variant_unop : VariantDef envF "unop" (casesF "unop") := rfl
theorem variant_boolunop : VariantDef envF "boolunop" (casesF "boolunop") := rfl
theorem variant_numunop : VariantDef envF "numunop" (casesF "numunop") := rfl
theorem variant_binop : VariantDef envF "binop" (casesF "binop") := rfl
theorem variant_boolbinop : VariantDef envF "boolbinop" (casesF "boolbinop") := rfl
theorem variant_numbinop : VariantDef envF "numbinop" (casesF "numbinop") := rfl
theorem variant_cmpop : VariantDef envF "cmpop" (casesF "cmpop") := rfl
theorem variant_numcmpop : VariantDef envF "numcmpop" (casesF "numcmpop") := rfl

/-- A nullary constructor of a closed variant type. -/
theorem typedV_nullary {x : IL.Id} {c : MixopS} (hd : VariantDef envF x (casesF x))
    (hc : FindCase (casesF x) c (.tupT [])) : TypedV envF (.varT x []) (con c []) :=
  typedV_con hd hc fun _ _ => hasTypTup_nil

/-- A one-field constructor. -/
theorem typedV_con1 {x : IL.Id} {c : MixopS} {y : IL.Id} {t : Typ} {w : Value}
    (hd : VariantDef envF x (casesF x)) (hc : FindCase (casesF x) c (.tupT [.mk y t]))
    (hw : ∀ ρ, ValsOnly ρ → HasTyp envF ρ t w) : TypedV envF (.varT x []) (con c [w]) :=
  typedV_con hd hc fun _ hρ => hasTypTup_cons hρ hw fun _ _ => hasTypTup_nil

theorem typedV_unop (op : UnOp) : TypedV envF (.varT "unop" []) (encUnOp op) := by
  cases op <;> exact typedV_nullary variant_unop rfl

theorem typedV_binop (op : BinOp) : TypedV envF (.varT "binop" []) (encBinOp op) := by
  cases op <;> exact typedV_nullary variant_binop rfl

theorem typedV_cmpop (op : CmpOp) : TypedV envF (.varT "cmpop" []) (encCmpOp op) := by
  cases op <;> exact typedV_nullary variant_cmpop rfl

theorem typedV_bool (b : Bool) : ∀ ρ, ValsOnly ρ → HasTyp envF ρ .boolT (.bool b) :=
  fun _ _ => hasTyp_boolT_iff.2 ⟨b, rfl⟩

theorem typedV_numT {m : Num} {t : NumTyp} (h : Num.subTyp (Num.toTyp m) t = true) :
    ∀ ρ, ValsOnly ρ → HasTyp envF ρ (.numT t) (.num m) :=
  fun _ _ => ⟨1, by simp [hasTyp, Value.asNum?, h]⟩

/-- **An encoded fragment expression is an `exp`.** -/
theorem typedV_enc : ∀ e : FExp, TypedV envF (.varT "exp" []) e.enc
  | .bool b => typedV_con1 variant_exp rfl (typedV_bool b)
  | .nat n => typedV_con1 variant_exp rfl (typedV_numT (m := .natN n) rfl)
  | .int i => typedV_con1 variant_exp rfl (typedV_numT (m := .intN i) rfl)
  | .un op _ a => typedV_con variant_exp rfl fun _ hρ =>
      hasTypTup_cons hρ (typedV_unop op) fun _ hρ' =>
        hasTypTup_cons hρ' (typedV_enc a) fun _ _ => hasTypTup_nil
  | .bin op _ a b => typedV_con variant_exp rfl fun _ hρ =>
      hasTypTup_cons hρ (typedV_binop op) fun _ hρ' =>
        hasTypTup_cons hρ' (typedV_enc a) fun _ hρ'' =>
          hasTypTup_cons hρ'' (typedV_enc b) fun _ _ => hasTypTup_nil
  | .cmp op _ a b => typedV_con variant_exp rfl fun _ hρ =>
      hasTypTup_cons hρ (typedV_cmpop op) fun _ hρ' =>
        hasTypTup_cons hρ' (typedV_enc a) fun _ hρ'' =>
          hasTypTup_cons hρ'' (typedV_enc b) fun _ _ => hasTypTup_nil

/-- A literal value is a `val`. -/
theorem typedV_lit_val {v : Value} (h : IsLitV v) : TypedV envF (.varT "val" []) (encVal v) := by
  match v, h with
  | .bool b, _ => exact typedV_con1 variant_val rfl (typedV_bool b)
  | .num (.natN n), _ => exact typedV_con1 variant_val rfl (typedV_numT (m := .natN n) rfl)
  | .num (.intN i), _ => exact typedV_con1 variant_val rfl (typedV_numT (m := .intN i) rfl)

/-- A `nat` or `int` numeral is a `num`. -/
theorem typedV_encNum {m : Num} (h : NatInt m) : TypedV envF (.varT "num" []) (encNum m) := by
  match m, h with
  | .natN n, _ => exact typedV_con1 variant_num rfl (typedV_numT (m := .natN n) rfl)
  | .intN i, _ => exact typedV_con1 variant_num rfl (typedV_numT (m := .intN i) rfl)

/-- The empty store is an `S`. -/
theorem typedV_emptyS : TypedV envF (.varT "S" []) emptyS := by
  intro ρ hρ
  refine (hasTyp_varT_global_iff (localTyp_none hρ "S")).2 ⟨_, [], rfl, evalArgs_nil _ _, ?_⟩
  exact ⟨20, by with_unfolding_all rfl⟩

end Silmaril.Wasm.SpecTec.Meta
