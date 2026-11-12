module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Instr

/-!
# Round 5: `FloatMissel` is exactly what the instance selection leaves untyped

`not_typedV_of_floatMissel`: no `FloatMissel` instruction has a typed image, in any `simEnv B`
and at any shape. With `simdTypingSel`, a bounded SIMD instruction Core accepts is a typed
`instr` **iff** it is not `FloatMissel`, so `SimdTypingSel` restricts `Pos.SimdTyping` no more
than it must.

The selected (integer) instance either has no case of the float operator's name (`SQRT`, `DIV`,
`RELAXED_MADD`, `CONVERT`, …) or one whose payload type does not hold the float operator's
payload: `MIN sx`/`MAX sx` carry an `sx`, `LT (sx)`, … a one-field tuple, while the float
operators carry none.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d271)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## Inversion -/

/-- The operator of a typed two-field instruction is typed in the scope binding its first
field. -/
theorem hasTyp_snd_of_typedV {op : MixopS} {T X : IL.Id} {u w : Value} {prems : List Prem}
    (hf : IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0) op =
      some (.tupT [.mk T (.varT T []), .mk "_" (.varT X [.expA (.varE T)])], prems))
    (h : TypedV (simEnv B) (.varT "instr" []) (.case op (.tuple [u, w]))) :
    HasTyp (simEnv B) (VarEnv.empty.bindVal T u) (.varT X [.expA (.varE T)]) w :=
  (Typing.hasTyp_pair_inv (IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant (IntNumeric.findTyp_instr' B) (h _ empty_valsOnly)) hf)).2

/-- A family selecting its `%X%(Jnn <: lanetype, M)` instance types only that instance's cases. -/
theorem hasTypCase_of_jnnFam {x : IL.Id} {ps q : List Param} {cs : List TypCase}
    {rest : List Inst}
    (htd : (simEnv B).findTyp? x = some (ps, .instD q [.expA jnnShapePat] (.variantT cs) :: rest))
    {ρ : VarEnv} {e : Exp} {sh : Shape} (he : EvalExp (simEnv B) ρ e (Vec.shapeV sh))
    {v : Value} (h : HasTyp (simEnv B) ρ (.varT x [.expA e]) v) :
    ∃ op w, v = .case op w ∧ HasTypCase (simEnv B) (jnnScope sh) cs op w := by
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain ⟨v, hv, rfl⟩ := evalArgs_expA_iff.1 hargs
  obtain rfl := hv.unique he
  rw [shapeV_eq] at hi
  exact hasTypDef_variantT_iff.1 (hasTypDef_of_insts_match (matchArgs_jnnShapePat _ _) hi)

/-- `sx` holds no tuple. -/
theorem not_hasTyp_sx_tuple {ρ : VarEnv} (hρ : ValsOnly ρ) {vs : List Value} :
    ¬ HasTyp (simEnv B) ρ (.varT "sx" []) (.tuple vs) := fun h => by
  have hl : localTyp? ρ "sx" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [IntNumeric.findTyp_sx] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hr
  · obtain ⟨op, w, he, -⟩ := hasTypDef_variantT_iff.1 hd
    cases he
  · exact not_hasTypInsts_nil hr

/-- A one-field tuple type holds no empty tuple. -/
theorem not_hasTyp_tup1_nil {ρ : VarEnv} {x : IL.Id} {t : Typ} :
    ¬ HasTyp (simEnv B) ρ (.tupT [.mk x t]) (.tuple []) := fun h => by
  obtain ⟨vs, hvs, ht⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨w, ws, he, -⟩ := hasTypTup_cons_iff.1 ht
  cases he

/-! ## The four families -/

set_option maxRecDepth 100000 in
theorem findTyp_vunopE : ∃ ps qs p rest, (simEnv B).findTyp? "vunop_" = some (ps,
    .instD qs [.expA jnnShapePat] (.variantT [.mk "ABS" (.tupT []) [] [],
      .mk "NEG" (.tupT []) [] [], .mk "POPCNT" (.tupT []) [] p]) :: rest) :=
  ⟨_, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_vbinopE : ∃ ps qs p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ rest, (simEnv B).findTyp? "vbinop_" =
    some (ps, .instD qs [.expA jnnShapePat] (.variantT [.mk "ADD" (.tupT []) [] [],
      .mk "SUB" (.tupT []) [] [], .mk "ADD_SAT" (.varT "sx" []) [] p₁,
      .mk "SUB_SAT" (.varT "sx" []) [] p₂, .mk "MUL" (.tupT []) [] p₃,
      .mk "AVGRU" (.tupT []) [] p₄, .mk "Q15MULR_SATS" (.tupT []) [] p₅,
      .mk "RELAXED_Q15MULRS" (.tupT []) [] p₆, .mk "MIN" (.varT "sx" []) [] p₇,
      .mk "MAX" (.varT "sx" []) [] p₈]) :: rest) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_vternopE : ∃ ps qs rest, (simEnv B).findTyp? "vternop_" = some (ps,
    .instD qs [.expA jnnShapePat] (.variantT [.mk "RELAXED_LANESELECT" (.tupT []) [] []]) ::
      rest) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_vrelopE : ∃ ps qs p₁ p₂ p₃ p₄ rest, (simEnv B).findTyp? "vrelop_" = some (ps,
    .instD qs [.expA jnnShapePat] (.variantT [.mk "EQ" (.tupT []) [] [],
      .mk "NE" (.tupT []) [] [], .mk "LT" (.tupT [.mk "sx" (.varT "sx" [])]) [] p₁,
      .mk "GT" (.tupT [.mk "sx" (.varT "sx" [])]) [] p₂,
      .mk "LE" (.tupT [.mk "sx" (.varT "sx" [])]) [] p₃,
      .mk "GE" (.tupT [.mk "sx" (.varT "sx" [])]) [] p₄]) :: rest) :=
  ⟨_, _, _, _, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_vcvtopE : ∃ ps qs p rest, (simEnv B).findTyp? "vcvtop__" = some (ps,
    .instD qs [.expA (shPat "Jnn_1" "M_1"), .expA (shPat "Jnn_2" "M_2")]
      (.variantT [.mk "EXTEND" (.tupT [.mk "half" (.varT "half" []), .mk "sx" (.varT "sx" [])])
        [] p]) :: rest) := ⟨_, _, _, _, rfl⟩

/-- The shape, bound by the instruction. -/
theorem evalExp_shapeVar {u : Value} :
    EvalExp (simEnv B) (VarEnv.empty.bindVal "shape" u) (.varE "shape") u := evalExp_last

set_option maxRecDepth 100000 in
/-- A float `VUNOP` that is `FloatMissel` is untyped. -/
theorem not_typedV_vecFloatUnOp {s : FloatShape} {op : FloatUnOp}
    (hm : FloatMissel (.vecFloatUnOp s op) = true) :
    ¬ TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecFloatUnOp s op)) := fun h => by
  obtain ⟨ps, qs, p, rest, htd⟩ := findTyp_vunopE (B := B)
  obtain ⟨o, w, hv, hc⟩ := hasTypCase_of_jnnFam htd evalExp_shapeVar
    (hasTyp_snd_of_typedV (op := "VUNOP") (u := Vec.shapeV (.float s)) (w := Vec.vFloatUnOpV op)
      rfl h)
  obtain ⟨t, qs', prems, hmem, -⟩ := hasTypCase_mem hc
  cases op <;> simp only [FloatMissel, Bool.false_eq_true] at hm <;>
    simp only [Vec.vFloatUnOpV, caseNilV, Value.case.injEq] at hv <;> obtain ⟨rfl, rfl⟩ := hv <;>
    simp at hmem

set_option maxRecDepth 100000 in
/-- A float `VBINOP` that is `FloatMissel` is untyped. -/
theorem not_typedV_vecFloatBinOp {s : FloatShape} {op : VecFloatBinOp}
    (hm : FloatMissel (.vecFloatBinOp s op) = true) :
    ¬ TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecFloatBinOp s op)) := fun h => by
  obtain ⟨ps, qs, p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, rest, htd⟩ := findTyp_vbinopE (B := B)
  obtain ⟨o, w, hv, hc⟩ := hasTypCase_of_jnnFam htd evalExp_shapeVar
    (hasTyp_snd_of_typedV (op := "VBINOP") (u := Vec.shapeV (.float s))
      (w := Vec.vFloatBinOpV op) rfl h)
  obtain ⟨t, qs', prems, hmem, ht, -⟩ := hasTypCase_mem hc
  have hsx : ¬ HasTyp (simEnv B) (jnnScope (.float s)) (.varT "sx" []) (.tuple []) :=
    not_hasTyp_sx_tuple (valsOnly_jnnScope _)
  cases op <;> simp only [FloatMissel, Bool.false_eq_true] at hm <;>
    simp only [Vec.vFloatBinOpV, caseNilV, Value.case.injEq] at hv <;> obtain ⟨rfl, rfl⟩ := hv <;>
    simp at hmem <;> exact hsx (hmem.1 ▸ ht)

set_option maxRecDepth 100000 in
/-- A float `VTERNOP` is untyped. -/
theorem not_typedV_vecFloatTernOp {s : FloatShape} {op : VecFloatTernOp} :
    ¬ TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecFloatTernOp s op)) := fun h => by
  obtain ⟨ps, qs, rest, htd⟩ := findTyp_vternopE (B := B)
  obtain ⟨o, w, hv, hc⟩ := hasTypCase_of_jnnFam htd evalExp_shapeVar
    (hasTyp_snd_of_typedV (op := "VTERNOP") (u := Vec.shapeV (.float s))
      (w := Vec.vFloatTernOpV op) rfl h)
  obtain ⟨t, qs', prems, hmem, -⟩ := hasTypCase_mem hc
  cases op <;> simp only [Vec.vFloatTernOpV, caseNilV, Value.case.injEq] at hv <;>
    obtain ⟨rfl, rfl⟩ := hv <;> simp at hmem

set_option maxRecDepth 100000 in
/-- A float `VRELOP` that is `FloatMissel` is untyped. -/
theorem not_typedV_vecFloatRelOp {s : FloatShape} {op : FloatRelOp}
    (hm : FloatMissel (.vecFloatRelOp s op) = true) :
    ¬ TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecFloatRelOp s op)) := fun h => by
  obtain ⟨ps, qs, p₁, p₂, p₃, p₄, rest, htd⟩ := findTyp_vrelopE (B := B)
  obtain ⟨o, w, hv, hc⟩ := hasTypCase_of_jnnFam htd evalExp_shapeVar
    (hasTyp_snd_of_typedV (op := "VRELOP") (u := Vec.shapeV (.float s))
      (w := Vec.vFloatRelOpV op) rfl h)
  obtain ⟨t, qs', prems, hmem, ht, -⟩ := hasTypCase_mem hc
  cases op <;> simp only [FloatMissel, Bool.false_eq_true] at hm <;>
    simp only [Vec.vFloatRelOpV, caseNilV, Value.case.injEq] at hv <;> obtain ⟨rfl, rfl⟩ := hv <;>
    simp at hmem <;> exact not_hasTyp_tup1_nil (hmem.1 ▸ ht)

set_option maxRecDepth 100000 in
/-- A `VCVTOP` other than `EXTEND` is untyped, at any shapes. -/
theorem not_typedV_vecConvert {s t : Shape} {op : VecConvertOp}
    (hm : FloatMissel (.vecConvert s t op) = true) :
    ¬ TypedV (simEnv B) (.varT "instr" []) (instrToV (.vecConvert s t op)) := fun h => by
  obtain ⟨ps, qs, p, rest, htd⟩ := findTyp_vcvtopE (B := B)
  have hp := IntNumeric.hasTyp_of_hasTypCase (Typing.hasTypCase_of_closedVariant
    (IntNumeric.findTyp_instr' B) (h _ empty_valsOnly)) (op := "VCVTOP")
    (t := .tupT [.mk "shape_1" (.varT "shape" []), .mk "shape_2" (.varT "shape" []),
      .mk "_" (.varT "vcvtop__" [.expA (.varE "shape_2"), .expA (.varE "shape_1")])])
    (prems := []) rfl
  have h₃ := (ConfigOk.hasTyp_triple_inv hp).2.2
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h₃
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  have hws : EvalArgs (simEnv B) ((VarEnv.empty.bindVal "shape_1" (Vec.shapeV t)).bindVal
      "shape_2" (Vec.shapeV s)) [.expA (.varE "shape_2"), .expA (.varE "shape_1")]
      [.val (Vec.shapeV s), .val (Vec.shapeV t)] :=
    Pos.evalArgs_vars (by simp) (by simp)
  obtain ⟨n₁, h₁⟩ := hargs
  obtain ⟨n₂, h₂⟩ := hws
  have hw : ws = [.val (Vec.shapeV s), .val (Vec.shapeV t)] := Except.ok.inj
    ((evalArgs_ok_of_le (le_max_left n₁ n₂) h₁).symm.trans (evalArgs_ok_of_le (le_max_right n₁ n₂) h₂))
  subst hw
  rw [shapeV_eq, shapeV_eq] at hi
  obtain ⟨op', w', hc, hcase⟩ := hasTypDef_variantT_iff.1 (hasTypDef_of_insts_match
    (matchArgs_cons (matchArg_expA (matchExp_shPat (by simp) _ _ (by simp)))
      (matchArgs_cons (matchArg_expA (matchExp_shPat (by simp) _ _ (by simp))) matchArgs_nil)) hi)
  obtain ⟨t', qs', prems, hmem, -⟩ := hasTypCase_mem hcase
  cases op <;> simp [FloatMissel, Vec.vConvertOpV, caseNilV] at hm hc <;>
    (obtain ⟨rfl, -⟩ := hc; simp at hmem)

/-- **No `FloatMissel` instruction has a typed image**, in any `simEnv B`. -/
theorem not_typedV_of_floatMissel {i : Instr} (hm : FloatMissel i = true) :
    ¬ TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  cases i <;> simp only [FloatMissel] at hm
  case vecFloatUnOp s op => exact not_typedV_vecFloatUnOp (by simpa [FloatMissel] using hm)
  case vecFloatBinOp s op => exact not_typedV_vecFloatBinOp (by simpa [FloatMissel] using hm)
  case vecFloatTernOp s op => exact not_typedV_vecFloatTernOp
  case vecFloatRelOp s op => exact not_typedV_vecFloatRelOp (by simpa [FloatMissel] using hm)
  case vecConvert s t op => exact not_typedV_vecConvert (by simpa [FloatMissel] using hm)
  all_goals exact absurd hm (by decide)

/-- **A bounded SIMD instruction Core accepts is a typed `instr` exactly when it is not
`FloatMissel`**, in every `simEnv B`. -/
theorem typedV_iff_not_floatMissel {C : Validation.Context} {i : Instr}
    {it : Validation.InstrType} (hok : Validation.InstrOk C i it)
    (hb : Round4.instrBnd i = true) (hs : Pos.InstrSimd i = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV i) ↔ FloatMissel i = false := by
  constructor
  · intro h
    cases hm : FloatMissel i
    · rfl
    · exact absurd h (not_typedV_of_floatMissel hm)
  · exact simdTypingSel B C i it hok hb hs

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
