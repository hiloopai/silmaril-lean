module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Inv

/-!
# Literals of the fragment, and the closed variant types they inhabit

`litOf` reads a scalar value back as a literal expression; the results of the fragment's
operators on literals are literals (`unValue_lit`, `binValues_lit`, `cmpValues_lit`). An encoded
expression of type `num` is a `nat`/`int` literal and one of type `val` is any literal
(`num_of_typed`, `lit_of_typed_val`): their cases `UN`, `BIN`, `CMP` are not cases of those
types.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

set_option maxRecDepth 100000

/-! ## Literal values -/

/-- A Boolean, `nat` or `int` value. -/
def IsLitV : Value → Prop
  | .bool _ => True
  | .num (.natN _) => True
  | .num (.intN _) => True
  | _ => False

/-- The literal expression of a literal value. -/
def litOf : Value → Option FExp
  | .bool b => some (.bool b)
  | .num (.natN n) => some (.nat n)
  | .num (.intN i) => some (.int i)
  | _ => none

theorem litOf_spec {v : Value} (h : IsLitV v) :
    ∃ l, litOf v = some l ∧ l.enc = encVal v ∧ l.strict = some v := by
  match v, h with
  | .bool b, _ => exact ⟨.bool b, rfl, rfl, rfl⟩
  | .num (.natN n), _ => exact ⟨.nat n, rfl, rfl, rfl⟩
  | .num (.intN i), _ => exact ⟨.int i, rfl, rfl, rfl⟩

theorem isLitV_num {m : Num} (h : NatInt m) : IsLitV (.num m) := by
  cases m <;> simp_all [NatInt, IsLitV]

/-- The step to a literal: `x` is the encoding of `w`, which `e` evaluates to. -/
theorem close_lit {e : FExp} {x w : Value} (hx : x = encVal w) (hw : IsLitV w)
    (he : e.strict = some w) :
    ∃ e' : FExp, x = e'.enc ∧ ∀ v, e'.strict = some v → e.strict = some v := by
  obtain ⟨l, -, hl, hs⟩ := litOf_spec hw
  exact ⟨l, hx.trans hl.symm, fun v hv => he.trans (hs.symm.trans hv)⟩

theorem encVal_inj {u v : Value} (hu : IsLitV u) (hv : IsLitV v) (h : encVal u = encVal v) :
    u = v := by
  match u, v, hu, hv with
  | .bool _, .bool _, _, _ => simp_all [encVal, con]
  | .bool _, .num (.natN _), _, _ => simp_all [encVal, encNum, con]
  | .bool _, .num (.intN _), _, _ => simp_all [encVal, encNum, con]
  | .num (.natN _), .bool _, _, _ => simp_all [encVal, encNum, con]
  | .num (.natN _), .num (.natN _), _, _ => simp_all [encVal, encNum, con]
  | .num (.natN _), .num (.intN _), _, _ => simp_all [encVal, encNum, con]
  | .num (.intN _), .bool _, _, _ => simp_all [encVal, encNum, con]
  | .num (.intN _), .num (.natN _), _, _ => simp_all [encVal, encNum, con]
  | .num (.intN _), .num (.intN _), _, _ => simp_all [encVal, encNum, con]

/-! ## Results of the operators on literals -/

theorem un_natInt {op : UnOp} {m m' : Num} (hm : NatInt m) (h : Num.un op m = some m') :
    NatInt m' := by
  cases m <;> cases op <;> simp_all [NatInt, Num.un] <;> subst h <;> trivial

theorem bin_natInt {op : BinOp} {a b m : Num} (ha : NatInt a) (hb : NatInt b)
    (h : Num.bin op a b = some m) : NatInt m := by
  cases a <;> cases b <;> simp only [NatInt] at ha hb <;> cases op <;>
    simp only [Num.bin] at h <;> (try split at h) <;> (try split at h) <;>
    simp_all [NatInt] <;> subst h <;> trivial

theorem unValue_num {op : UnOp} {m : Num} {v : Value}
    (h : FExp.resVal (unValue op (.num m)) = some v) : ∃ m', Num.un op m = some m' ∧ v = .num m' := by
  cases hu : Num.un op m with
  | none => cases op <;> simp [unValue, hu, FExp.resVal, Res.ofOption] at h
  | some m' =>
    refine ⟨m', rfl, ?_⟩
    cases op <;> simp_all [unValue, FExp.resVal, Res.ofOption, eq_comm]

theorem binValues_num {op : BinOp} {a b : Num} {v : Value}
    (h : FExp.resVal (binValues op (.num a) (.num b)) = some v) :
    ∃ m, Num.bin op a b = some m ∧ v = .num m := by
  cases hb : Num.bin op a b with
  | none => simp [binValues, hb, FExp.resVal, Res.ofOption] at h
  | some m =>
    refine ⟨m, rfl, ?_⟩
    simpa [binValues, hb, FExp.resVal, Res.ofOption, eq_comm] using h

/-! ## The closed variant types `num` and `val` -/

/-- The cases of the closed variant type `x` in `fixed`. -/
noncomputable def casesF (x : IL.Id) : List TypCase :=
  match envF.findTyp? x with
  | some ([], [.instD [] [] (.variantT cs)]) => cs
  | _ => []

theorem variant_num : VariantDef envF "num" (casesF "num") := rfl
theorem ops_num : (casesF "num").map TypCase.op = ["NAT", "INT", "RAT", "REAL"] := rfl
theorem variant_val : VariantDef envF "val" (casesF "val") := rfl
theorem ops_val : (casesF "val").map TypCase.op =
    ["NAT", "INT", "RAT", "REAL", "BOOL", "TEXT", "TUP", "INJ", "OPT", "LIST", "STR"] := rfl

/-- An encoded expression of type `num` is a `nat` or `int` literal. -/
theorem num_of_typed {e : FExp} (h : TypedIn envF (.varT "num" []) e.enc) :
    ∃ m, NatInt m ∧ e.enc = encNum m ∧ e.strict = some (.num m) := by
  obtain ⟨ρ, hρ, ht⟩ := h
  obtain ⟨c, w, he, hc⟩ := case_of_typed hρ variant_num ht
  rw [ops_num] at hc
  cases e with
  | nat n => exact ⟨.natN n, trivial, rfl, rfl⟩
  | int i => exact ⟨.intN i, trivial, rfl, rfl⟩
  | _ =>
    simp only [FExp.enc, con, Value.case.injEq] at he
    obtain ⟨rfl, -⟩ := he
    simp at hc

/-- An encoded expression of type `val` is a literal. -/
theorem lit_of_typed_val {e : FExp} (h : TypedIn envF (.varT "val" []) e.enc) :
    ∃ v, IsLitV v ∧ e.enc = encVal v ∧ e.strict = some v := by
  obtain ⟨ρ, hρ, ht⟩ := h
  obtain ⟨c, w, he, hc⟩ := case_of_typed hρ variant_val ht
  rw [ops_val] at hc
  cases e with
  | bool b => exact ⟨.bool b, trivial, rfl, rfl⟩
  | nat n => exact ⟨.num (.natN n), trivial, rfl, rfl⟩
  | int i => exact ⟨.num (.intN i), trivial, rfl, rfl⟩
  | _ =>
    simp only [FExp.enc, con, Value.case.injEq] at he
    obtain ⟨rfl, -⟩ := he
    simp at hc

end Silmaril.Wasm.SpecTec.Meta
