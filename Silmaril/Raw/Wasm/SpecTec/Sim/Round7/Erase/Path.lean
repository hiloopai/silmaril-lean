module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Erase.FO

/-!
# Round 7, the export swap: paths and record updates over the first-order fragment (unrefined)

* `pathGet_erase`: on a first-order path (`FOp`), reading at the erased scope and erased root
  gives the erased answer, in the swap set.
* `pathSet_erase_eq`: writing at the erased scope and root, with the erased value, gives the
  erased result. `allIn_pathSet` (`Round7.Roots`) adds the swap set under `SafeWrites`.
* `eraseUpd`, `eraseExt`: **the update `e₁[p = e₂]` and the extension `e₁[p =.. e₂]`** with
  first-order parts commute with erasing the scope, and stay in the swap set when the writes
  into the root that `e₁` evaluates to are safe. This is where item 2 (typed update roots) enters
  item 1: `SafeWrites` is the hypothesis, discharged by `Roots.safeWrites_of_noExp` at roots
  without `EXPORTS` records along the path, and false at `.TABLES[i]`/`.MEMS[i]` of a module image
  (`Roots.not_allIn_QC_tables`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Erase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Roots (SafeWrites allIn_pathSet)

variable {Q : Value → Prop} {env : Env} {ρ : VarEnv}

theorem pathGet_erase (hQ : QInj Q) (hρ : ScopeIn Q ρ) {v : Value} (hv : AllIn Q v) :
    ∀ {p : Path}, FOp p → ∀ n,
      EOK Q (pathGet n env ρ v p) (pathGet n env (eraseScope ρ) (eraseV v) p)
  | _, _, 0 => by simp only [pathGet]; exact EOK.error _
  | _, .rootP, _ + 1 => by simp only [pathGet]; exact EOK.ok hv
  | _, .idxP hp he, n + 1 => by
    simp only [pathGet]
    refine (pathGet_erase hQ hρ hv hp n).bind fun u _ hu =>
      (eraseFO hQ env n hρ he).bind fun iv _ _ => ?_
    rw [asNat?_eraseV]
    cases iv.asNat? with
    | none => exact EOK.error _
    | some i =>
      show EOK Q (Res.ofOption (u.idx? i)) (Res.ofOption ((eraseV u).idx? i))
      exact EOK.ofOption (idx?_eraseV u i) fun w hw => hu.idx? hw
  | _, .sliceP hp h₁ h₂, n + 1 => by
    simp only [pathGet]
    refine (pathGet_erase hQ hρ hv hp n).bind fun u _ hu =>
      (eraseFO hQ env n hρ h₁).bind fun x _ _ => (eraseFO hQ env n hρ h₂).bind fun y _ _ => ?_
    rw [asNat?_eraseV, asNat?_eraseV]
    cases x.asNat? with
    | none => exact EOK.error _
    | some i =>
      cases y.asNat? with
      | none => exact EOK.error _
      | some k =>
        show EOK Q (Res.ofOption (u.slice? i k)) (Res.ofOption ((eraseV u).slice? i k))
        exact EOK.ofOption (slice?_eraseV u i k) fun w hw => hu.slice? hw
  | _, .dotP hp ha, n + 1 => by
    simp only [pathGet]
    refine (pathGet_erase hQ hρ hv hp n).bind fun u _ hu => ?_
    exact EOK.ofOption (field?_eraseV ha u) fun w hw => hu.field? hw

/-- Read the erased side of an `EOK` at an answer. -/
theorem EOK.eq_ok {r r' : Res Value} {v : Value} (h : EOK Q r r') (hr : r = .ok v) :
    r' = .ok (eraseV v) := by
  rw [h.1, hr]; rfl

theorem EOK.eq_error {r r' : Res Value} {e : Stuck} (h : EOK Q r r') (hr : r = .error e) :
    r' = .error e := by
  rw [h.1, hr]; rfl

theorem pathSet_erase_eq (hQ : QInj Q) (hρ : ScopeIn Q ρ) {v : Value} (hv : AllIn Q v) :
    ∀ {p : Path}, FOp p → ∀ n w,
      pathSet n env (eraseScope ρ) (eraseV v) p (eraseV w) = eraseV <$> pathSet n env ρ v p w
  | _, _, 0, _ => by simp only [pathSet]; rfl
  | _, .rootP, _ + 1, _ => by simp only [pathSet]; rfl
  | _, .idxP hp he, n + 1, w => by
    simp only [pathSet]
    have hg := pathGet_erase (env := env) hQ hρ hv hp n
    cases h₁ : pathGet n env ρ v _ with
    | error e => rw [hg.eq_error h₁]; rfl
    | ok u =>
      rw [hg.eq_ok h₁]
      have he' := eraseFO hQ env n hρ he
      cases h₂ : evalExp n env ρ _ with
      | error e => rw [he'.eq_error h₂]; rfl
      | ok iv =>
        rw [he'.eq_ok h₂]
        simp only [bind, Except.bind, asNat?_eraseV]
        cases iv.asNat? with
        | none => rfl
        | some i =>
          simp only [Res.ofOption, setIdx_eraseV]
          cases u.setIdx i w with
          | none => rfl
          | some u' => exact pathSet_erase_eq hQ hρ hv hp n u'
  | _, .sliceP hp h₁ h₂, n + 1, w => by
    simp only [pathSet]
    have hg := pathGet_erase (env := env) hQ hρ hv hp n
    cases hr : pathGet n env ρ v _ with
    | error e => rw [hg.eq_error hr]; rfl
    | ok u =>
      rw [hg.eq_ok hr]
      have e₁ := eraseFO hQ env n hρ h₁
      have e₂ := eraseFO hQ env n hρ h₂
      cases hx : evalExp n env ρ _ with
      | error e => rw [e₁.eq_error hx]; rfl
      | ok x =>
        rw [e₁.eq_ok hx]
        cases hy : evalExp n env ρ _ with
        | error e => simp only [bind, Except.bind]; rw [e₂.eq_error hy]; rfl
        | ok y =>
          simp only [bind, Except.bind]
          rw [e₂.eq_ok hy]
          simp only [asNat?_eraseV]
          cases x.asNat? with
          | none => rfl
          | some i =>
            cases y.asNat? with
            | none => rfl
            | some k =>
              simp only [Res.ofOption, setSlice_eraseV]
              cases u.setSlice i k w with
              | none => rfl
              | some u' => exact pathSet_erase_eq hQ hρ hv hp n u'
  | _, .dotP hp ha, n + 1, w => by
    simp only [pathSet]
    have hg := pathGet_erase (env := env) hQ hρ hv hp n
    cases hr : pathGet n env ρ v _ with
    | error e => rw [hg.eq_error hr]; rfl
    | ok u =>
      rw [hg.eq_ok hr]
      simp only [bind, Except.bind, Res.ofOption, setField_eraseV ha]
      cases u.setField _ w with
      | none => rfl
      | some u' => exact pathSet_erase_eq hQ hρ hv hp n u'

/-- **A record update with first-order parts**, under safe writes. -/
theorem eraseUpd (hQ : QInj Q) (hρ : ScopeIn Q ρ) {e₁ e₂ : Exp} {p : Path} (h₁ : FO e₁)
    (h₂ : FO e₂) (hp : FOp p) (n : Nat)
    (hs : ∀ v₁, evalExp n env ρ e₁ = .ok v₁ → SafeWrites Q env ρ v₁ p) :
    EOK Q (evalExp (n + 1) env ρ (.updE e₁ p e₂))
      (evalExp (n + 1) env (eraseScope ρ) (.updE e₁ p e₂)) := by
  simp only [evalExp]
  refine (eraseFO hQ env n hρ h₁).bind fun v₁ hv₁ hA₁ =>
    (eraseFO hQ env n hρ h₂).bind fun v₂ _ hA₂ => ?_
  exact ⟨pathSet_erase_eq hQ hρ hA₁ hp n v₂,
    fun u hu => allIn_pathSet hA₁ p n v₂ u hA₂ (hs v₁ hv₁) hu⟩

/-- **A record extension with first-order parts**, under safe writes. -/
theorem eraseExt (hQ : QInj Q) (hρ : ScopeIn Q ρ) {e₁ e₂ : Exp} {p : Path} (h₁ : FO e₁)
    (h₂ : FO e₂) (hp : FOp p) (n : Nat)
    (hs : ∀ v₁, evalExp n env ρ e₁ = .ok v₁ → SafeWrites Q env ρ v₁ p) :
    EOK Q (evalExp (n + 1) env ρ (.extE e₁ p e₂))
      (evalExp (n + 1) env (eraseScope ρ) (.extE e₁ p e₂)) := by
  simp only [evalExp]
  refine (eraseFO hQ env n hρ h₁).bind fun v₁ hv₁ hA₁ =>
    (eraseFO hQ env n hρ h₂).bind fun v₂ _ hA₂ =>
      (pathGet_erase hQ hρ hA₁ hp n).bind fun u _ hu => ?_
  rw [cat?_eraseV]
  cases hc : Value.cat? u v₂ with
  | none => exact EOK.error _
  | some u' =>
    have hu' : AllIn Q u' := AllIn.cat? hu hA₂ hc
    show EOK Q (pathSet n env ρ v₁ p u') (pathSet n env (eraseScope ρ) (eraseV v₁) p (eraseV u'))
    exact ⟨pathSet_erase_eq hQ hρ hA₁ hp n u',
      fun w hw => allIn_pathSet hA₁ p n u' w hu' (hs v₁ hv₁) hw⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.Erase
