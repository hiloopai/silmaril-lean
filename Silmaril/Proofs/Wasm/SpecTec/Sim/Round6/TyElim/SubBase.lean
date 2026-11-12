module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.OkElim

/-!
# Round 6: the claim for `Reftype_sub {}`, and the facts its rules use

`Heaptype_sub` and `Deftype_sub` in `{}` are read back by the recursor of `DDerivesB`, with the
claim `SubM`:

* `Heaptype_sub {} a b`: from an image `a = tyV h₁`, `b` is an image `tyV h₂` with
  `RefOkV.SubE h₁ h₂`; and from an image `b`, `a` is one (`HsRes`). Both directions are needed:
  `Heaptype_sub/none` reads its premise `heaptype <: ANY` from the right.
* `Deftype_sub {} a b`: `a` and `b` are images of defined types related by `SubE` (`DsRes`).

`RS P r` says rule `r` establishes `P` on its conclusion, from its premises and the claim at its
relational premises (`PremS`). This file also proves the facts the rules consult:

* `cohH_of_heaptypeOk`: `Heaptype_ok {}` at an image makes it coherent (the middle of `trans`);
* `expand_inv`: `Expand` at the image of a defined type is Core's `Expand`, under `DDerivesB`;
* `not_evalExp_types0`, `not_evalExp_recs0`: `C.TYPES[x]` and `C.RECS[i]` have no value in `{}`,
  so `typeidx-l`, `typeidx-r` and the four `rec-*` rules never fire there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj natV headV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.RefOkB (ctxR)
open Round6.RefOkV (SubE CohH)

/-! ## The claim -/

/-- `Heaptype_sub {} a b`, read back in both directions. -/
def HsRes (a b : Value) : Prop :=
  (∀ h₁ : CHeapType, a = tyV h₁ → ∃ h₂ : CHeapType, b = tyV h₂ ∧ SubE h₁ h₂) ∧
    (∀ h₂ : CHeapType, b = tyV h₂ → ∃ h₁ : CHeapType, a = tyV h₁ ∧ SubE h₁ h₂)

/-- `Deftype_sub {} a b`, read back. -/
def DsRes (a b : Value) : Prop := ∃ d₁ d₂ : DefType, a = tyV d₁ ∧ b = tyV d₂ ∧ SubE d₁ d₂

/-- The claim at a derivation of relation `x` at value `v`. -/
def SubM (x : IL.Id) (v : Value) : Prop :=
  (x = "Heaptype_sub" → ∀ a b, v = .tuple [ctx0V, a, b] → HsRes a b) ∧
    (x = "Deftype_sub" → ∀ a b, v = .tuple [ctx0V, a, b] → DsRes a b)

/-- The claim at a premise: a relational premise satisfies it at its value. -/
def PremS (env : Env) (ρ : VarEnv) : Prem → Prop
  | .rulePr x _ _ e => ∀ v, EvalExp env ρ e v → SubM x v
  | _ => True

/-- Rule `r` establishes `P` on its conclusion in `{}`, from its premises and the claim at them. -/
def RS (env : Env) (P : Value → Value → Prop) : Rule → Prop
  | .ruleD _ qs _ e prems => ∀ e' ∈ conclAlts e, ∀ (O : ElseI) (els : Prop)
      (σ : List (IL.Id × Value)), QuantsOk env (VarEnv.empty.bindVals σ) qs → ∀ a b,
      EvalExp env (VarEnv.empty.bindVals σ) e' (.tuple [ctx0V, a, b]) →
      (∀ pr ∈ prems, DPremB env O els (VarEnv.empty.bindVals σ) pr) →
      (∀ pr ∈ prems, PremS env (VarEnv.empty.bindVals σ) pr) → P a b

/-! ## Reading premises and conclusions -/

/-- The claim at a `Heaptype_sub` premise. -/
theorem ih_hs {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {a b : Value}
    (ih : PremS env ρ (.rulePr "Heaptype_sub" [] op e))
    (he : EvalExp env ρ e (.tuple [ctx0V, a, b])) : HsRes a b :=
  (ih _ he).1 rfl a b rfl

/-- The claim at a `Deftype_sub` premise. -/
theorem ih_ds {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {a b : Value}
    (ih : PremS env ρ (.rulePr "Deftype_sub" [] op e))
    (he : EvalExp env ρ e (.tuple [ctx0V, a, b])) : DsRes a b :=
  (ih _ he).2 rfl a b rfl

/-- A conclusion `(C, x, y)`, read: `C` is `{}`. -/
theorem concl_C {env : Env} {ρ : VarEnv} {e₂ e₃ : Exp} {a b : Value}
    (he : EvalExp env ρ (.tupE [.varE "C", e₂, e₃]) (.tuple [ctx0V, a, b])) :
    ρ.findVal? "C" = some ctx0V ∧ EvalExp env ρ e₂ a ∧ EvalExp env ρ e₃ b :=
  have h := ev3 he
  ⟨evalExp_varE_iff.1 h.1, h.2.1, h.2.2⟩

/-- A heap type whose image is that of a defined type is that defined type. -/
theorem heap_of_def {h : CHeapType} {d : DefType} (e : tyV h = tyV d) : h = .use (.dt d) :=
  tyV_inj _ _ e

/-- A heap type whose image is that of an abstract heap type is that type. -/
theorem heap_of_abs {h : CHeapType} {a : AbsHeapType} (e : tyV h = tyV (Ty.abs a : CHeapType)) :
    h = .abs a :=
  tyV_inj _ _ e

variable {B : Builtins}

/-- A quantifier typed at `heaptype` holds an image. -/
theorem quant_heap {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id} {v : Value}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP x (.varT "heaptype" []) ∈ qs) (hx : (VarEnv.empty.bindVals σ).findVal? x = some v) :
    ∃ h : CHeapType, v = tyV h := by
  obtain ⟨w, hw, ht⟩ := hq x _ hm
  have e : w = v := Option.some.inj (hw.symm.trans hx)
  exact e ▸ img_heap (Round5.Multi.hasE_of_valsOnly (valsOnly_bind σ) ht)

/-- A quantifier typed at `deftype` holds an image. -/
theorem quant_def {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id} {v : Value}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP x (.varT "deftype" []) ∈ qs) (hx : (VarEnv.empty.bindVals σ).findVal? x = some v) :
    ∃ d : DefType, v = tyV d := by
  obtain ⟨w, hw, ht⟩ := hq x _ hm
  have e : w = v := Option.some.inj (hw.symm.trans hx)
  exact e ▸ img_def (Round5.Multi.hasE_of_valsOnly (valsOnly_bind σ) ht)

/-! ## `TYPES` and `RECS` are empty in `{}` -/

/-- `C.TYPES[x]` has no value in `{}`. -/
theorem not_evalExp_types0 {env : Env} {ρ : VarEnv} (hC : ρ.findVal? "C" = some ctx0V)
    {e : Exp} {v : Value} : ¬ EvalExp env ρ (.idxE (.dotE (.varE "C") "TYPES") e) v := by
  intro h
  obtain ⟨w, i, hw, -, hi⟩ := evalExp_idxE_iff.1 h
  obtain ⟨c, hc, hf⟩ := evalExp_dotE_iff.1 hw
  have ec : c = ctx0V := Option.some.inj ((evalExp_varE_iff.1 hc).symm.trans hC)
  have ew : w = .list [] := by
    rw [ec] at hf
    exact (Option.some.inj hf).symm
  rw [ew] at hi
  simp at hi

/-- `C.RECS[i]` has no value in `{}`. -/
theorem not_evalExp_recs0 {env : Env} {ρ : VarEnv} (hC : ρ.findVal? "C" = some ctx0V)
    {e : Exp} {v : Value} : ¬ EvalExp env ρ (.idxE (.dotE (.varE "C") "RECS") e) v := by
  intro h
  obtain ⟨w, i, hw, -, hi⟩ := evalExp_idxE_iff.1 h
  obtain ⟨c, hc, hf⟩ := evalExp_dotE_iff.1 hw
  have ec : c = ctx0V := Option.some.inj ((evalExp_varE_iff.1 hc).symm.trans hC)
  have ew : w = .list [] := by
    rw [ec] at hf
    exact (Option.some.inj hf).symm
  rw [ew] at hi
  simp at hi

/-- An `if` premise comparing `C.RECS[i]` has no value in `{}`. -/
theorem not_dpremB_recs0 {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv}
    (hC : ρ.findVal? "C" = some ctx0V) {i e : Exp} {op : CmpOp} {t : OpTyp} :
    ¬ DPremB env O els ρ (.ifPr (.cmpE op t (.idxE (.dotE (.varE "C") "RECS") i) e)) := by
  intro h
  cases h with
  | ifPr hc =>
    obtain ⟨v₁, -, h₁, -⟩ := evalExp_cmpE_iff.1 hc
    exact not_evalExp_recs0 hC h₁

/-! ## The middle type of `trans` is coherent -/

variable {prof : Silmaril.Wasm.Numerics.Profile} {H : Type} {hn : H → String}
  {host : Silmaril.Wasm.Execution.Core.HostSemantics H}

/-- **`Heaptype_ok {}` at an image makes it coherent**, on the concrete `B`. -/
theorem cohH_of_heaptypeOk {O : ElseI} {m : CHeapType}
    (h : DDerivesB (simEnv (Prims.builtins prof hn host)) O "Heaptype_ok" "%|-%:OK" []
      (.tuple [ctx0V, tyV m])) : CohH m := by
  cases m with
  | abs => trivial
  | bot => trivial
  | use u =>
    cases u with
    | idx => trivial
    | recv => trivial
    | dt d =>
      exact coh_of_deftypeOk _ (Nat.lt_succ_self _) (L := [])
        (typeuseOk_def (heaptypeOk_def (d := d) h))

/-! ## `Expand` -/

/-- `Expand`'s premise `$unrolldt(deftype) = SUB final? typeuse* comptype`, at the image of a
defined type. -/
theorem expandPrem_inv {O : ElseI} {els : Prop} {ρ : VarEnv} (hρ : ValsOnly ρ) {d : DefType}
    {w : Value} (hD : ρ.findVal? "deftype" = some (tyV d)) (hC : ρ.findVal? "comptype" = some w)
    (h : DPremB (simEnv (Prims.builtins prof hn host)) O els ρ Prims.expandPrem) :
    ∃ ct, Expand d ct ∧ w = tyV ct := by
  cases h with
  | ifPr hc =>
    obtain ⟨v₁, v₂, hv₁, hv₂, hcv⟩ := evalExp_cmpE_iff.1 hc
    have ha := applies_of_call (hn := hn) (host := host) hρ
      (Equiv.evalArgs_cons (evalExp_var hD) Equiv.evalArgs_nil) hv₁
    obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 ((Prims.applies_unrolldt hn host d v₁).1 ha)
    obtain ⟨a, b, c, hc', rfl⟩ := Prims.evalExp_sub3_inv hv₂
    have ec : c = w := Option.some.inj ((evalExp_varE_iff.1 hc').symm.trans hC)
    exact ec ▸ Prims.expand_of_sub hst
      (Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcv)

/-- **`Expand` at the image of a defined type is Core's `Expand`**, under `DDerivesB`, on the
concrete `B`. -/
theorem expand_inv {O : ElseI} {d : DefType} {w : Value}
    (h : DDerivesB (simEnv (Prims.builtins prof hn host)) O "Expand" "%~~%" [] (.tuple [tyV d, w])) :
    ∃ ct, Expand d ct ∧ w = tyV ct := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, -, he, hp⟩ :=
    dderivesB_inv (Prims.findRel_expand _) h
  have hrule : Prims.expandRule = .ruleD nm qs "%~~%" e prems := by
    rcases i with _ | i
    · exact Option.some.inj hr
    · simp at hr
  simp only [Prims.expandRule, Rule.ruleD.injEq] at hrule
  obtain ⟨-, -, -, rfl, rfl⟩ := hrule
  obtain ⟨h₁, h₂⟩ := ev2 ((concl_eq halt rfl) ▸ he)
  exact expandPrem_inv (valsOnly_bind σ) (evalExp_varE_iff.1 h₁) (evalExp_varE_iff.1 h₂)
    (hp _ (List.mem_singleton_self _))

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
