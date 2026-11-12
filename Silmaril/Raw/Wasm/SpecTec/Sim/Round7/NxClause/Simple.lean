module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Thms

/-!
# Round 8, REH route 2: simple expressions commute with erasure (unrefined)

`simpAt`: at every fuel, a `simpleE` expression (variables, literals, `unE`, `cvtE`, iterations of
these) evaluates on the erased scope to the erased value, in every scope and environment, with no
hypothesis. Hence `patLen_erase`: the lengths `Sem.patLen` reads at a `lenOk` expression agree.
The proofs follow round 3's `EraseAll.step_*` with every value in the swap set.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT allIn_top)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope find?_eraseScope)

/-- **Simple expressions commute with erasure at fuel `n`.** -/
structure SimpAt (env : Env) (n : Nat) : Prop where
  exp : ∀ ρ e, simpleE e = true →
    ER eraseV (AllIn QT) (evalExp n env ρ e) (evalExp n env (eraseScope ρ) e)
  doms : ∀ ρ ds, simpleDs ds = true →
    ER (List.map eraseP) (fun xvs => ∀ p ∈ xvs, AllIn QT p.2)
      (evalDoms n env ρ ds) (evalDoms n env (eraseScope ρ) ds)
  iter : ∀ ρ e it ds, simpleE e = true → simpleI it = true → simpleDs ds = true →
    ER eraseV (AllIn QT) (evalIterE n env ρ e it ds) (evalIterE n env (eraseScope ρ) e it ds)
  iterList : ∀ ρ e xvs ido k, simpleE e = true →
    ER eraseV (AllIn QT) (evalIterList n env ρ e xvs ido k)
      (evalIterList n env (eraseScope ρ) e (xvs.map eraseP) ido k)
  rounds : ∀ ρ e rs, simpleE e = true →
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn QT v)
      (evalRounds n env ρ e rs) (evalRounds n env (eraseScope ρ) e (rs.map (List.map eraseP)))

theorem simpleDs_mem : ∀ {ds : List Dom}, simpleDs ds = true → ∀ d ∈ ds, simpleE (domSrc d) = true
  | [], _, _, h => by simp at h
  | .mk x e :: ds, h, d, hd => by
    simp only [simpleDs, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact simpleDs_mem h.2 d hd

section
variable {env : Env} {n : Nat}

theorem simpAt_zero (env : Env) : SimpAt env 0 where
  exp _ _ _ := by simp only [evalExp]; exact ER.error _
  doms _ _ _ := by simp only [evalDoms]; exact ER.error _
  iter _ _ _ _ _ _ _ := by simp only [evalIterE]; exact ER.error _
  iterList _ _ _ _ _ _ := by simp only [evalIterList]; exact ER.error _
  rounds _ _ _ _ := by simp only [evalRounds]; exact ER.error _

theorem simp_exp (ih : SimpAt env n) (ρ : VarEnv) (e : Exp) (he : simpleE e = true) :
    ER eraseV (AllIn QT) (evalExp (n + 1) env ρ e) (evalExp (n + 1) env (eraseScope ρ) e) := by
  cases e with
  | varE x =>
    simp only [evalExp]
    exact ER.ofOption (find?_eraseScope ρ x) fun v _ => allIn_top v
  | boolE b => simp only [evalExp]; exact ER.ok (a := Value.bool b) trivial
  | numE m => simp only [evalExp]; exact ER.ok (a := Value.num m) trivial
  | textE t => simp only [evalExp]; exact ER.ok (a := Value.text t) trivial
  | unE op t e =>
    simp only [simpleE] at he
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e he) fun v _ _ => ?_
    rw [unValue_eraseV]
    exact ER.of_bool_num (Erase.unValue_bn _ v)
  | cvtE e t₁ t₂ =>
    simp only [simpleE] at he
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e he) fun v _ _ => ?_
    rw [asNum?_eraseV]
    cases v.asNum? with
    | none => exact ER.error _
    | some m =>
      exact ER.of_bool_num fun u hu => by
        simp only [Res.ofOption_some, bind, Except.bind, Res.ofOption_eq_ok,
          Option.map_eq_some_iff] at hu
        obtain ⟨k, -, rfl⟩ := hu
        exact .inr ⟨_, rfl⟩
  | iterE e it =>
    obtain ⟨it, ds⟩ := it
    simp only [simpleE, Bool.and_eq_true] at he
    simp only [evalExp]
    exact ih.iter ρ e it ds he.1.2 he.1.1 he.2
  | _ => simp [simpleE] at he

theorem simp_doms (ih : SimpAt env n) (ρ : VarEnv) (ds : List Dom) (hd : simpleDs ds = true) :
    ER (List.map eraseP) (fun xvs => ∀ p ∈ xvs, AllIn QT p.2)
      (evalDoms (n + 1) env ρ ds) (evalDoms (n + 1) env (eraseScope ρ) ds) := by
  simp only [evalDoms]
  refine ER.mapM' ds fun d hd' => ?_
  exact ER.map (fun v => (domVar d, v)) (fun _ _ => rfl) (fun _ h => h)
    (ih.exp ρ _ (simpleDs_mem hd d hd'))

theorem simp_iterList (ih : SimpAt env n) (ρ : VarEnv) (e : Exp) (xvs : List (IL.Id × Value))
    (ido : Option IL.Id) (k : Nat) (he : simpleE e = true) :
    ER eraseV (AllIn QT) (evalIterList (n + 1) env ρ e xvs ido k)
      (evalIterList (n + 1) env (eraseScope ρ) e (xvs.map eraseP) ido k) := by
  simp only [evalIterList, mapM_asList_erase]
  cases hds : (xvs.mapM fun (p : IL.Id × Value) => p.2.asList?.map fun l => (p.1, l)) with
  | none => exact ER.error _
  | some ds =>
    simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
    refine ER.assert (by simp [List.all_map, Function.comp_def]) fun _ => ?_
    rw [iterRows_erase]
    refine ER.bind (ih.rounds ρ e _ he) fun vs _ _ => ?_
    have h := ER.ok (f := eraseV) (allIn_top (.list vs))
    rw [eraseV_list'] at h
    exact h

theorem simp_rounds (ih : SimpAt env n) (ρ : VarEnv) (e : Exp) (rs : List (List (IL.Id × Value)))
    (he : simpleE e = true) :
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn QT v)
      (evalRounds (n + 1) env ρ e rs)
      (evalRounds (n + 1) env (eraseScope ρ) e (rs.map (List.map eraseP))) := by
  simp only [evalRounds]
  refine ER.mapM rs fun r _ => ?_
  rw [← eraseScope_bindVals]
  exact ih.exp _ e he

theorem simp_iter (ih : SimpAt env n) (ρ : VarEnv) (e : Exp) (it : Iter) (ds : List Dom)
    (he : simpleE e = true) (hi : simpleI it = true) (hd : simpleDs ds = true) :
    ER eraseV (AllIn QT) (evalIterE (n + 1) env ρ e it ds)
      (evalIterE (n + 1) env (eraseScope ρ) e it ds) := by
  cases it with
  | opt =>
    simp only [evalIterE]
    refine ER.bind (ih.doms ρ ds hd) fun xvs _ _ => ER.assert Iff.rfl fun _ => ?_
    rw [mapM_asOpt_erase]
    cases hos : (xvs.mapM fun (p : IL.Id × Value) => p.2.asOpt?.map fun o => (p.1, o)) with
    | none => exact ER.error _
    | some os =>
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      have hn : ((os.map fun (p : IL.Id × Option Value) => (p.1, p.2.map eraseV)).all
          fun p => p.2.isNone) = os.all fun p => p.2.isNone := by
        simp [List.all_map, Function.comp_def]
      have hs : ((os.map fun (p : IL.Id × Option Value) => (p.1, p.2.map eraseV)).all
          fun p => p.2.isSome) = os.all fun p => p.2.isSome := by
        simp [List.all_map, Function.comp_def]
      rw [hn, hs, filterMap_opt_erase]
      split
      · exact ER.ok (a := Value.opt none) trivial
      · split
        · rw [← eraseScope_bindVals]
          refine ER.bind (ih.exp _ e he) fun v _ _ => ?_
          exact ER.ok (a := Value.opt (some v)) (allIn_top v)
        · exact ER.error _
  | list =>
    simp only [evalIterE]
    refine ER.bind (ih.doms ρ ds hd) fun xvs _ _ => ER.assert Iff.rfl fun _ => ?_
    rw [headLen_erase]
    cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ih.iterList ρ e xvs none k he
  | list1 =>
    simp only [evalIterE]
    refine ER.bind (ih.doms ρ ds hd) fun xvs _ _ => ER.assert Iff.rfl fun _ => ?_
    rw [headLen_erase]
    cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ER.assert Iff.rfl fun _ => ih.iterList ρ e xvs none k he
  | listN eₙ ido =>
    simp only [simpleI] at hi
    simp only [evalIterE]
    refine ER.bind (ih.doms ρ ds hd) fun xvs _ _ =>
      ER.bind (ih.exp ρ eₙ hi) fun kv _ _ => ?_
    rw [asNat?_eraseV]
    cases kv.asNat? with
    | none => exact ER.error _
    | some k =>
      simp only [Res.ofOption_some, bind, Except.bind]
      exact ih.iterList ρ e xvs ido k he

theorem simpAt_succ (ih : SimpAt env n) : SimpAt env (n + 1) where
  exp ρ e he := simp_exp ih ρ e he
  doms ρ ds hd := simp_doms ih ρ ds hd
  iter ρ e it ds he hi hd := simp_iter ih ρ e it ds he hi hd
  iterList ρ e xvs ido k he := simp_iterList ih ρ e xvs ido k he
  rounds ρ e rs he := simp_rounds ih ρ e rs he

end

/-- **Simple expressions commute with erasure at every fuel.** -/
theorem simpAt (env : Env) : ∀ n, SimpAt env n
  | 0 => simpAt_zero env
  | n + 1 => simpAt_succ (simpAt env n)

/-- **`patLen` at a `lenOk` expression reads alike before and after erasure.** -/
theorem patLen_erase (env : Env) (ρ : VarEnv) : ∀ (n : Nat) (e : Exp), lenOk e = true →
    patLen n env (eraseScope ρ) e = patLen n env ρ e
  | 0, _, _ => by simp only [patLen]
  | n + 1, e, he => by
    have hgen : ∀ e, simpleE e = true →
        (do let v ← evalExp n env (eraseScope ρ) e; Res.ofOption v.len? : Res Nat) =
          (do let v ← evalExp n env ρ e; Res.ofOption v.len?) := by
      intro e he
      rw [((simpAt env n).exp ρ e he).1]
      cases evalExp n env ρ e with
      | error _ => rfl
      | ok v => simp only [Functor.map, Except.map, bind, Except.bind, len?_eraseV]
    cases e
    case listE es => simp only [patLen]
    case catE e₁ e₂ =>
      simp only [lenOk, Bool.and_eq_true] at he
      simp only [patLen, patLen_erase env ρ n e₁ he.1, patLen_erase env ρ n e₂ he.2]
    case iterE e₀ it =>
      obtain ⟨i, ds⟩ := it
      cases i
      case listN eₙ x =>
        simp only [lenOk] at he
        simp only [patLen]
        rw [((simpAt env n).exp ρ eₙ he).1]
        cases evalExp n env ρ eₙ with
        | error _ => rfl
        | ok v => simp only [Functor.map, Except.map, bind, Except.bind, asNat?_eraseV]
      all_goals simp only [patLen]; exact hgen _ he
    all_goals simp only [patLen]; exact hgen _ he

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
