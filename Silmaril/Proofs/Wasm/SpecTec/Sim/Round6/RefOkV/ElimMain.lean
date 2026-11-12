module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Elim

/-!
# Round 6: SpecTec's `Ref_ok` gives `RefOkE`, from `AgreeTy`

* `elim_extern`, `elim_sub`: the two rules of `Ref_ok` with premises on relations;
* `refM_of_dderivesB`: by the recursor of the mutual `DDerivesB`/`DPremB` (with `DPremB`'s motive
  `PremM`: a `Ref_ok` premise satisfies the claim at its value), every `Ref_ok` derivation at
  `(storeV hn s, refToValue r, w)` has `w = tyV rt` with `RefOkE s r rt`, given `AgreeTy`'s
  elimination fields.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue refToValue_inj)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round6.Reading

variable {H : Type} {B : Builtins}

/-- `REF ANY`, non-null, as `Ref_ok/extern`'s premise writes it. -/
theorem evalExp_refAny {ρ : VarEnv} :
    EvalExp (simEnv B) ρ (refNonNullE (absE "ANY")) (tyV (Ty.ref false (Ty.abs .any))) :=
  evalExp_case (evalExp_tup2 (evalExp_optE_none_iff.2 rfl)
    (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))

/-- The reference of a `REF.EXTERN` case. -/
theorem extern_of_case {r : Ref} {xv : Value} (hr : refToValue r = .case "REF.EXTERN" xv) :
    ∃ r', r = .extern r' ∧ xv = refToValue r' := by
  cases r <;> simp_all [refToValue]

/-- `ref =/= REF.NULL_ADDR`, inverted. -/
theorem ne_null_of_prem {O : ElseI} {els : Prop} {ρ : VarEnv} {r' : Ref}
    (hR : ρ.findVal? "ref" = some (refToValue r'))
    (h : DPremB (simEnv B) O els ρ
      (.ifPr (.cmpE .neOp .boolT (.varE "ref") (.caseE "REF.NULL_ADDR" (.tupE []))))) :
    r' ≠ .null := by
  cases h with
  | ifPr he =>
    obtain ⟨v₁, v₂, h₁, h₂, h₃⟩ := evalExp_cmpE_iff.1 he
    have e₁ : v₁ = refToValue r' := Option.some.inj ((evalExp_varE_iff.1 h₁).symm.trans hR)
    have e₂ : v₂ = refToValue .null :=
      h₂.unique (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    have hne : v₁ ≠ v₂ := by simpa [cmpValues] using h₃
    exact fun e => hne (by rw [e₁, e₂, e])

/-- `Ref_ok/extern`, inverted. -/
theorem elim_extern {O : ElseI} {els : Prop} {ρ : VarEnv} {hn : H → String} {s : Store H}
    {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (baseConcl "REF.EXTERN" "ref" (absE "EXTERN"))
      (.tuple [storeV hn s, refToValue r, w]))
    (hp : ∀ pr ∈ externPrems, DPremB (simEnv B) O els ρ pr)
    (ih : ∀ pr ∈ externPrems, PremM B hn s ρ pr) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨hS, ⟨xv, hX, hr⟩, h₃⟩ := baseConcl_inv he
  have hw := refNonNullAbs_inv (a := .extern) rfl h₃
  obtain ⟨r', rfl, rfl⟩ := extern_of_case hr
  have hv : EvalExp (simEnv B) ρ (.tupE [.varE "s", .varE "ref", refNonNullE (absE "ANY")])
      (.tuple [storeV hn s, refToValue r', tyV (Ty.ref false (Ty.abs .any))]) :=
    evalExp_tup3 (evalExp_var hS) (evalExp_var hX) evalExp_refAny
  obtain ⟨rt, hrt, hok⟩ := ih _ (List.mem_cons_self ..) rfl _ hv r' _ rfl
  have hrt' : rt = Ty.ref false (Ty.abs .any) := (tyV_inj _ _ hrt).symm
  subst hrt'
  have hn := ne_null_of_prem hX (hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  exact ⟨_, hw, .extern hok hn⟩

/-- A premise on a relation, inverted at a three-component value. -/
theorem rulePr_inv {O : ElseI} {els : Prop} {ρ : VarEnv} {x : IL.Id} {op : MixopS} {e : Exp}
    (h : DPremB (simEnv B) O els ρ (.rulePr x [] op e)) :
    ∃ v, EvalExp (simEnv B) ρ e v ∧ DDerivesB (simEnv B) O x op [] v := by
  cases h with
  | rulePr ha he hd =>
    obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 ha
    exact ⟨_, he, hd⟩

theorem evalExp_tup3_ex {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂, e₃]) v) :
    ∃ a b c, v = .tuple [a, b, c] ∧ EvalExp env ρ e₁ a ∧ EvalExp env ρ e₂ b ∧
      EvalExp env ρ e₃ c := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨a, ws, rfl, ha, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨b, us, rfl, hb, hus⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  obtain ⟨c, zs, rfl, hc, hzs⟩ := Equiv.Validation.evalExps_cons_iff.1 hus
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hzs
  exact ⟨a, b, c, rfl, ha, hb, hc⟩

/-- `Ref_ok/sub`, inverted, through `AgreeTy`'s elimination fields. -/
theorem elim_sub (A : AgreeTy (simEnv B)) {O : ElseI} {els : Prop} {ρ : VarEnv}
    {hn : H → String} {s : Store H} {r : Ref} {w : Value}
    (he : EvalExp (simEnv B) ρ (.tupE [.varE "s", .varE "ref", .varE "rt"])
      (.tuple [storeV hn s, refToValue r, w]))
    (hp : ∀ pr ∈ [Prem.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s", .varE "ref", .varE "rt'"]),
       .rulePr "Reftype_ok" [] "%|-%:OK" (.tupE [ctx0E, .varE "rt"]),
       .rulePr "Reftype_sub" [] "%|-%<:%" (.tupE [ctx0E, .varE "rt'", .varE "rt"])],
      DPremB (simEnv B) O els ρ pr)
    (ih : ∀ pr ∈ [Prem.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s", .varE "ref", .varE "rt'"]),
       .rulePr "Reftype_ok" [] "%|-%:OK" (.tupE [ctx0E, .varE "rt"]),
       .rulePr "Reftype_sub" [] "%|-%<:%" (.tupE [ctx0E, .varE "rt'", .varE "rt"])],
      PremM B hn s ρ pr) :
    ∃ rt, w = tyV rt ∧ RefOkE s r rt := by
  obtain ⟨hS, hR, hW⟩ := Round5.RefOk.evalExp_tup3_inv he
  obtain ⟨v₁, hv₁, -⟩ := rulePr_inv (hp _ (List.mem_cons_self ..))
  obtain ⟨a, b, w', rfl, ha, hb, hw'⟩ := evalExp_tup3_ex hv₁
  have ea : a = storeV hn s := ha.unique hS
  have eb : b = refToValue r := hb.unique hR
  obtain ⟨rt₁, rfl, hok₁⟩ := ih _ (List.mem_cons_self ..) rfl _ hv₁ r w' (by rw [ea, eb])
  obtain ⟨v₃, hv₃, hd₃⟩ := rulePr_inv
    (hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have ev₃ : v₃ = .tuple [ctx0V, tyV rt₁, w] :=
    hv₃.unique (evalExp_tup3 evalExp_ctx0 hw' hW)
  obtain ⟨rt₂, rfl, hsub⟩ := A.subElim O rt₁ w (ev₃ ▸ hd₃)
  obtain ⟨v₂, hv₂, hd₂⟩ := rulePr_inv (hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have ev₂ : v₂ = .tuple [ctx0V, tyV rt₂] := hv₂.unique (evalExp_tup2 evalExp_ctx0 hW)
  exact ⟨rt₂, rfl, .sub hok₁ (A.okElim O rt₂ (ev₂ ▸ hd₂)) hsub⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
