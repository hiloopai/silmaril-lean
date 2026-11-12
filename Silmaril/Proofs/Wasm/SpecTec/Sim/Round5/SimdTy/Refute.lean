module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Round 5: `Pos.SimdTyping` is false

SpecTec selects the instance of a type family by matching the actual arguments against each
instance's patterns in order (`hasTypInsts`). The vector operator families `vunop_(shape)`,
`vbinop_(shape)`, `vternop_(shape)`, `vrelop_(shape)` and `vcvtop__(shape, shape)` have one
instance for integer shapes, with pattern `%X%(Jnn <: lanetype, M)`, before one for float shapes,
with pattern `%X%(Fnn <: lanetype, M)`. The evaluator's `matchExp` of a nested `subE e _ _` does
not test the subtype (`Sem.argSubOk` tests only a top-level `subE` argument pattern). So the
`Jnn` instance matches every shape, float shapes included, and a float operator is typed only
if the integer instance happens to have a case of the same name and payload.

`f32x4.sqrt` is valid in Core and within SpecTec's syntax (`Round4.instrBnd`), but its image
`VUNOP (F32 X 4) SQRT` is not a typed `instr` in any `simEnv B`: the integer instance of
`vunop_` has only `ABS`, `NEG` and `POPCNT`. Hence:

* `not_typedV_f32x4Sqrt`: the image of `f32x4.sqrt` is not a typed `instr`;
* `not_simdTyping`: `Pos.SimdTyping B` is false, for every `B`;
* `not_instrTyping`, `not_posTypingNE`: so are `Pos.InstrTyping B` and `Pos.PosTypingNE B hn`.

This is the same evaluator defect as the round-2 `$packfield_` finding (aggregates track,
finding 2), now at nested patterns of type-family instances.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## Instance selection -/

/-- **The first instance whose patterns match is the one that types the value.** -/
theorem hasTypDef_of_insts_match {env : Env} {qs : List Param} {pats : List Arg} {dt : DefTyp}
    {is : List Inst} {ws : List ArgV} {σ : VarEnv} {v : Value}
    (hm : MatchArgs env VarEnv.empty pats ws σ)
    (h : HasTypInsts env (.instD qs pats dt :: is) ws v) : HasTypDef env σ dt v := by
  obtain ⟨n₁, h₁⟩ := hm
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => rw [hasTypInsts_zero] at h; simp at h
  | succ n =>
    rw [hasTypInsts_succ_cons] at h
    unfold Res.elimUndef at h
    split at h
    · rename_i σ' hσ'
      obtain rfl := IntNumeric.matchArgs_det ⟨n₁, h₁⟩ hσ'
      exact ⟨n, h⟩
    · simp at h
    · rename_i hu
      have e₁ := matchArgs_undef_of_le (le_max_left n n₁) hu
      have e₂ := matchArgs_ok_of_le (le_max_right n n₁) h₁
      rw [e₁] at e₂
      cases e₂

/-- The integer-shape pattern `%X%(Jnn <: lanetype, M)`. -/
abbrev jnnShapePat : Exp :=
  .caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])

/-- **`%X%(Jnn <: lanetype, M)` matches every shape**, float shapes included: the nested `subE`
is not tested. -/
theorem matchArgs_jnnShapePat (l m : Value) :
    MatchArgs (simEnv B) VarEnv.empty [.expA jnnShapePat] [.val (.case "%X%" (.tuple [l, m]))]
      ((VarEnv.empty.bindVal "Jnn" l).bindVal "M" m) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE
    (Equiv.Validation.matchExp_tup_iff.2 ⟨_, rfl, Equiv.Validation.matchExps_cons_iff.2
      ⟨_, _, _, rfl, Prims.matchExp_subE (matchExp_varE (by simp)),
        Equiv.Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl,
          matchExp_varE (by simp),
          Equiv.Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩))) matchArgs_nil

set_option maxRecDepth 100000 in
/-- `vunop_`'s instances: the integer one (`ABS`, `NEG`, `POPCNT`) first. -/
theorem findTyp_vunop : ∃ ps qs p rest, (simEnv B).findTyp? "vunop_" = some (ps,
    .instD qs [.expA jnnShapePat] (.variantT [.mk "ABS" (.tupT []) [] [],
      .mk "NEG" (.tupT []) [] [], .mk "POPCNT" (.tupT []) [] p]) :: rest) :=
  ⟨_, _, _, _, rfl⟩

/-- **`SQRT` is not a `vunop_` at a float shape.** -/
theorem not_hasTyp_vunop_sqrt {ρ : VarEnv} {e : Exp} {l m : Value}
    (he : EvalExp (simEnv B) ρ e (.case "%X%" (.tuple [l, m]))) :
    ¬ HasTyp (simEnv B) ρ (.varT "vunop_" [.expA e]) (caseNilV "SQRT") := by
  intro h
  obtain ⟨ps, qs, p, rest, htd⟩ := findTyp_vunop (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain ⟨v, hv, rfl⟩ := evalArgs_expA_iff.1 hargs
  obtain rfl := hv.unique he
  obtain ⟨op, w, hc, hcase⟩ :=
    hasTypDef_variantT_iff.1 (hasTypDef_of_insts_match (matchArgs_jnnShapePat l m) hi)
  obtain ⟨rfl, rfl⟩ := Value.case.inj hc
  obtain ⟨t, qs', prems, hmem, -⟩ := hasTypCase_mem hcase
  simp at hmem

/-! ## `f32x4.sqrt` -/

/-- `f32x4.sqrt`. -/
abbrev f32x4Sqrt : Instr := .vecFloatUnOp .f32x4 .sqrt

/-- It is valid, in every context. -/
theorem instrOk_f32x4Sqrt (C : Context) :
    InstrOk C f32x4Sqrt (.plain [.v128] [.v128]) :=
  .vector (.vecFloatUnOp _ _)

theorem instrBnd_f32x4Sqrt : Round4.instrBnd f32x4Sqrt = true := rfl

theorem instrSimd_f32x4Sqrt : Pos.InstrSimd f32x4Sqrt = true := rfl

theorem instrToV_f32x4Sqrt :
    instrToV f32x4Sqrt = .case "VUNOP" (.tuple [Vec.fshV .f32x4, caseNilV "SQRT"]) := rfl

set_option maxRecDepth 100000 in
/-- **The image of `f32x4.sqrt` is not a typed `instr`**, in any `simEnv B`. -/
theorem not_typedV_f32x4Sqrt :
    ¬ TypedV (simEnv B) (.varT "instr" []) (instrToV f32x4Sqrt) := by
  intro h
  rw [instrToV_f32x4Sqrt] at h
  have hc := Typing.hasTypCase_of_closedVariant (IntNumeric.findTyp_instr' B)
    (h _ ConfigOk.valsOnly_empty)
  have hp := IntNumeric.hasTyp_of_hasTypCase hc
    (t := .tupT [.mk "shape" (.varT "shape" []),
      .mk "_" (.varT "vunop_" [.expA (.varE "shape")])]) (prems := []) rfl
  exact not_hasTyp_vunop_sqrt (l := Vec.floatLaneV .f32x4) (m := pctV FloatShape.f32x4.lanes) (evalExp_var (by simp [Vec.fshV])) (Typing.hasTyp_pair_inv hp).2

/-- **`Pos.SimdTyping` is false**, for every `B`. -/
theorem not_simdTyping (B : Builtins) : ¬ Pos.SimdTyping B := fun h =>
  not_typedV_f32x4Sqrt (h {} f32x4Sqrt _ (instrOk_f32x4Sqrt {}) instrBnd_f32x4Sqrt
    instrSimd_f32x4Sqrt)

/-- **`Pos.InstrTyping` is false**, for every `B`. -/
theorem not_instrTyping (B : Builtins) : ¬ Pos.InstrTyping B := fun h =>
  not_typedV_f32x4Sqrt (h {} f32x4Sqrt _ (instrOk_f32x4Sqrt {}) instrBnd_f32x4Sqrt)

/-- **`Pos.PosTypingNE` is false**, for every `B` and encoding. -/
theorem not_posTypingNE {H : Type} (B : Builtins) (hn : H → String) : ¬ Pos.PosTypingNE B hn :=
  fun h => not_typedV_f32x4Sqrt (h.instr {} f32x4Sqrt _ (instrOk_f32x4Sqrt {}) instrBnd_f32x4Sqrt)

/-! ## Family V's `VecTyping` is false: `lanes` asks every list to be lanes -/

/-- Some instance types a value that a type-family application types. -/
theorem hasTypDef_of_insts {env : Env} :
    ∀ {is : List Inst} {ws : List ArgV} {v : Value}, HasTypInsts env is ws v →
      ∃ qs pats dt σ, Inst.instD qs pats dt ∈ is ∧ HasTypDef env σ dt v
  | [], _, _, h => absurd h not_hasTypInsts_nil
  | .instD qs pats dt :: is, ws, v, h => by
    rcases hasTypInsts_cons_inv h with ⟨σ, -, hd⟩ | hr
    · exact ⟨qs, pats, dt, σ, List.mem_cons_self, hd⟩
    · obtain ⟨qs', pats', dt', σ', hm, hd⟩ := hasTypDef_of_insts hr
      exact ⟨qs', pats', dt', σ', List.mem_cons_of_mem _ hm, hd⟩

/-- **A family whose every instance a boolean fails to inhabit does not type a boolean**, in
any scope, at any non-empty argument list. -/
theorem not_hasTyp_bool_of_insts {env : Env} {x : IL.Id} {ps : List Param} {is : List Inst}
    (htd : env.findTyp? x = some (ps, is))
    (hall : ∀ qs pats dt σ, Inst.instD qs pats dt ∈ is → ¬ HasTypDef env σ dt (.bool true))
    {ρ : VarEnv} {a : Arg} {args : List Arg} :
    ¬ HasTyp env ρ (.varT x (a :: args)) (.bool true) := by
  intro h
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain ⟨qs, pats, dt, σ, hm, hd⟩ := hasTypDef_of_insts hi
  exact hall qs pats dt σ hm hd

/-- A variant holds injections only. -/
theorem not_hasTypDef_variant_bool {env : Env} {σ : VarEnv} {cs : List TypCase} :
    ¬ HasTypDef env σ (.variantT cs) (.bool true) := fun h => by
  obtain ⟨op, w, he, -⟩ := hasTypDef_variantT_iff.1 h
  cases he

set_option maxRecDepth 100000 in
theorem findTyp_uN' : ∃ ps q p cs, (simEnv B).findTyp? "uN" = some (ps, [.instD q p (.variantT cs)]) :=
  ⟨_, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_fN' : ∃ ps q p cs, (simEnv B).findTyp? "fN" = some (ps, [.instD q p (.variantT cs)]) :=
  ⟨_, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_iN' : ∃ ps q p a, (simEnv B).findTyp? "iN" =
    some (ps, [.instD q p (.aliasT (.varT "uN" [a]))]) := ⟨_, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_num' : ∃ ps q₁ p₁ a₁ q₂ p₂ a₂, (simEnv B).findTyp? "num_" = some (ps,
    [.instD q₁ p₁ (.aliasT (.varT "iN" [a₁])), .instD q₂ p₂ (.aliasT (.varT "fN" [a₂]))]) :=
  ⟨_, _, _, _, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_pack' : ∃ ps q p a, (simEnv B).findTyp? "pack_" =
    some (ps, [.instD q p (.aliasT (.varT "iN" [a]))]) := ⟨_, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_lane' : ∃ ps q₁ p₁ a₁ q₂ p₂ a₂ q₃ p₃ a₃, (simEnv B).findTyp? "lane_" = some (ps,
    [.instD q₁ p₁ (.aliasT (.varT "num_" [a₁])), .instD q₂ p₂ (.aliasT (.varT "pack_" [a₂])),
     .instD q₃ p₃ (.aliasT (.varT "iN" [a₃]))]) :=
  ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

/-- A single-instance variant family types no boolean. -/
theorem not_hasTyp_bool_variant {x : IL.Id}
    (h : ∃ ps q p cs, (simEnv B).findTyp? x = some (ps, [.instD q p (.variantT cs)]))
    {ρ : VarEnv} {a : Arg} {args : List Arg} :
    ¬ HasTyp (simEnv B) ρ (.varT x (a :: args)) (.bool true) := by
  obtain ⟨ps, q, p, cs, htd⟩ := h
  refine not_hasTyp_bool_of_insts htd fun _ _ _ _ hm => ?_
  simp only [List.mem_singleton, Inst.instD.injEq] at hm
  obtain ⟨-, -, rfl⟩ := hm
  exact not_hasTypDef_variant_bool

/-- `iN(N)` types no boolean. -/
theorem not_hasTyp_bool_iN {ρ : VarEnv} {a : Arg} {args : List Arg} :
    ¬ HasTyp (simEnv B) ρ (.varT "iN" (a :: args)) (.bool true) := by
  obtain ⟨ps, q, p, a', htd⟩ := findTyp_iN' (B := B)
  refine not_hasTyp_bool_of_insts htd fun _ _ _ _ hm hd => ?_
  simp only [List.mem_singleton, Inst.instD.injEq] at hm
  obtain ⟨-, -, rfl⟩ := hm
  exact not_hasTyp_bool_variant findTyp_uN' (hasTypDef_aliasT_iff.1 hd)

/-- **No lane value is a boolean**: `lane_(lt)` types no boolean, in any scope. -/
theorem not_hasTyp_bool_lane {ρ : VarEnv} {a : Arg} {args : List Arg} :
    ¬ HasTyp (simEnv B) ρ (.varT "lane_" (a :: args)) (.bool true) := by
  obtain ⟨ps, q₁, p₁, a₁, q₂, p₂, a₂, q₃, p₃, a₃, htd⟩ := findTyp_lane' (B := B)
  refine not_hasTyp_bool_of_insts htd fun _ _ _ _ hm hd => ?_
  simp only [List.mem_cons, Inst.instD.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · obtain ⟨ps', q, p, b₁, q', p', b₂, htd'⟩ := findTyp_num' (B := B)
    refine not_hasTyp_bool_of_insts htd' (fun _ _ _ _ hm' hd' => ?_) (hasTypDef_aliasT_iff.1 hd)
    simp only [List.mem_cons, Inst.instD.injEq, List.not_mem_nil, or_false] at hm'
    rcases hm' with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact not_hasTyp_bool_iN (hasTypDef_aliasT_iff.1 hd')
    · exact not_hasTyp_bool_variant findTyp_fN' (hasTypDef_aliasT_iff.1 hd')
  · obtain ⟨ps', q, p, b, htd'⟩ := findTyp_pack' (B := B)
    refine not_hasTyp_bool_of_insts htd' (fun _ _ _ _ hm' hd' => ?_) (hasTypDef_aliasT_iff.1 hd)
    simp only [List.mem_singleton, Inst.instD.injEq] at hm'
    obtain ⟨-, -, rfl⟩ := hm'
    exact not_hasTyp_bool_iN (hasTypDef_aliasT_iff.1 hd')
  · exact not_hasTyp_bool_iN (hasTypDef_aliasT_iff.1 hd)

/-- **Family V's `VecTyping` is false**, for every `B`: its `lanes` field asks every list,
`[true]` included, to be a list of lanes. -/
theorem not_vecTyping (B : Builtins) : ¬ Vec.VecTyping (simEnv B) := fun Ty => by
  let ρ : VarEnv := (VarEnv.empty.bindVal "Jnn" (Vec.intLaneV .i8x16)).bindVal "M"
    (pctV IntShape.i8x16.lanes)
  have h := Ty.lanes .i8x16 [.bool true] ρ ⟨rfl, rfl, rfl⟩ (by simp [ρ]) (by simp [ρ])
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := (Value.list.inj hvs).symm
  exact not_hasTyp_bool_lane (hasTypList_iff.1 hl _ List.mem_cons_self)

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
