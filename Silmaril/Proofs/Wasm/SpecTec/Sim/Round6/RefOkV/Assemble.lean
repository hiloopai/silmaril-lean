module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.ElimMain
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Reduce

/-!
# Round 6: `Agree` from `AgreeTy`, for every `B`

* `refM_of_dderivesB`: every `Ref_ok` derivation lands in `RefOkE`, by the recursor of the mutual
  `DDerivesB`/`DPremB` and one inversion per rule (`Elim.lean`, `ElimMain.lean`);
* `agree_of_agreeTy`: with `dderivesB_refOk_of_refOk` (`IntroMain.lean`), the interpreter half
  `Agree` reduces to `AgreeTy`, which involves no store;
* `refOkBV_of_agreeTy`: so `RefOkBV (simEnv B)` follows from `AgreeTy (simEnv B)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round6.Reading

variable {H : Type} {B : Builtins}

/-- `Ref_ok`'s rules, one inversion each. -/
theorem refM_rule (A : AgreeTy (simEnv B)) {O : ElseI} {els : Prop} {hn : H → String}
    {s : Store H} {i : Nat} {nm : IL.Id} {qs : List Param} {op : MixopS} {e e' : Exp}
    {prems : List Prem} {ρ : VarEnv} {v : Value}
    (hrule : (Round5.RefOk.relOf Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d627).2.2.2[i]? =
      some (Rule.ruleD nm qs op e prems))
    (halt : e' ∈ conclAlts e) (he : EvalExp (simEnv B) ρ e' v)
    (hp : ∀ pr ∈ prems, DPremB (simEnv B) O els ρ pr) (ih : ∀ pr ∈ prems, PremM B hn s ρ pr) :
    RefM hn s v := by
  intro r w hv
  subst hv
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals simp only [Round5.RefOk.relOf, Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d627,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, Rule.ruleD.injEq,
    List.getElem?_nil, reduceCtorEq] at hrule
  all_goals obtain ⟨-, -, -, rfl, rfl⟩ := hrule
  all_goals rw [conclAlts_of_not rfl, List.mem_singleton] at halt
  all_goals subst halt
  · exact elim_null he
  · exact elim_i31 he
  · exact elim_struct he (hp _ (List.mem_cons_self ..))
  · exact elim_array he (hp _ (List.mem_cons_self ..))
  · exact elim_func he (hp _ (List.mem_cons_self ..))
  · exact elim_exn he (hp _ (List.mem_cons_self ..))
  · exact elim_host he
  · exact elim_extern he hp ih
  · exact elim_sub A he hp ih

/-- **Every `Ref_ok` derivation lands in `RefOkE`**, given `AgreeTy`'s elimination fields. -/
theorem refM_of_dderivesB (A : AgreeTy (simEnv B)) {O : ElseI} {hn : H → String} {s : Store H}
    {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (h : DDerivesB (simEnv B) O x op args v) : x = "Ref_ok" → RefM hn s v := by
  refine DDerivesB.rec (motive_1 := fun x _ _ v _ => x = "Ref_ok" → RefM hn s v)
    (motive_2 := fun _ ρ pr _ => PremM B hn s ρ pr) ?_ (by intros; trivial) (by intros; trivial)
    (by intros; trivial) ?_ (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) h
  · intro x op args v ps t rules i nm qs e e' prems ρ₀ σ hrel hrule halt _ _ he hp ih hx
    subst hx
    have hr : (ps, op, t, rules) =
        Round5.RefOk.relOf Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d627 :=
      Option.some.inj (hrel.symm.trans (Round5.RefOk.findRel_refOk B))
    have hrules : rules = (Round5.RefOk.relOf
        Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d627).2.2.2 := congrArg (fun p => p.2.2.2) hr
    subst hrules
    exact refM_rule A hrule halt he hp ih
  · intro els ρ x args op e avs w _ he _ ih hx v hv
    exact (hv.unique he) ▸ ih hx

/-- **SpecTec's `Ref_ok` at a type's image is `RefOkE`**, given `AgreeTy`. -/
theorem refOkE_of_dderivesB (A : AgreeTy (simEnv B)) {O : ElseI} {hn : H → String}
    {s : Store H} {r : Ref} {rt : CRefType}
    (h : DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [storeV hn s, refToValue r, tyV rt])) :
    RefOkE s r rt := by
  obtain ⟨rt', e, hok⟩ := refM_of_dderivesB A h rfl r _ rfl
  exact (tyV_inj _ _ e) ▸ hok

/-- **The interpreter half reduces to `AgreeTy`**, for every `B`. -/
theorem agree_of_agreeTy (A : AgreeTy (simEnv B)) : Agree (simEnv B) where
  refOk _ _ _ hs hS hb hok O r :=
    ⟨fun h => refOkS_of_refOk (refOk_of_refOkE hS hok (refOkE_of_dderivesB A h)), fun h =>
      dderivesB_refOk_of_refOk A O hs hS r (refOk_of_refOkS hS hok h) hok hb⟩

/-- **`RefOkBV` from `AgreeTy`**, for every `B`. -/
theorem refOkBV_of_agreeTy (A : AgreeTy (simEnv B)) : RefOkB.RefOkBV (simEnv B) :=
  refOkBV_of_agree (agree_of_agreeTy A)

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
