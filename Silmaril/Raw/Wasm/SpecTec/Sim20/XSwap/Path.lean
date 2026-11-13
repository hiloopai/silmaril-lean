module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.FO

/-!
# function code erasure: paths over the first-order fragment (copied )

Round 9 copy 's `Round8.CodeErase` (itself a copy 's export erasure) for
`EXPORTS` fields with an arbitrary injective replacement `XTau.τ` (`swapX`); the prose below,
written for the earlier copies, speaks of erasure. Every value is in the swap set (`fun _ => True`).

* `pathGet_erase`: on a first-order path (`FOp`), reading at the erased scope and erased root
  gives the erased answer, in the swap set.
* `pathSet_erase_eq`: writing at the erased scope and root, with the erased value, gives the
  erased result.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap

variable {Q : Value → Prop} {env : Env} {ρ : VarEnv}

theorem pathGet_erase (hQ : QInj Q) (hρ : ScopeIn Q ρ) {v : Value} (hv : AllIn Q v) :
    ∀ {p : Path}, FOp p → ∀ n,
      EOK Q (pathGet n env ρ v p) (pathGet n env (eraseScope ρ) (swapX v) p)
  | _, _, 0 => by simp only [pathGet]; exact EOK.error _
  | _, .rootP, _ + 1 => by simp only [pathGet]; exact EOK.ok hv
  | _, .idxP hp he, n + 1 => by
    simp only [pathGet]
    refine (pathGet_erase hQ hρ hv hp n).bind fun u _ hu =>
      (eraseFO hQ env n hρ he).bind fun iv _ _ => ?_
    rw [asNat?_eraseC]
    cases iv.asNat? with
    | none => exact EOK.error _
    | some i =>
      show EOK Q (Res.ofOption (u.idx? i)) (Res.ofOption ((swapX u).idx? i))
      exact EOK.ofOption (idx?_eraseC u i) fun w hw => hu.idx? hw
  | _, .sliceP hp h₁ h₂, n + 1 => by
    simp only [pathGet]
    refine (pathGet_erase hQ hρ hv hp n).bind fun u _ hu =>
      (eraseFO hQ env n hρ h₁).bind fun x _ _ => (eraseFO hQ env n hρ h₂).bind fun y _ _ => ?_
    rw [asNat?_eraseC, asNat?_eraseC]
    cases x.asNat? with
    | none => exact EOK.error _
    | some i =>
      cases y.asNat? with
      | none => exact EOK.error _
      | some k =>
        show EOK Q (Res.ofOption (u.slice? i k)) (Res.ofOption ((swapX u).slice? i k))
        exact EOK.ofOption (slice?_eraseC u i k) fun w hw => hu.slice? hw
  | _, .dotP hp ha, n + 1 => by
    simp only [pathGet]
    refine (pathGet_erase hQ hρ hv hp n).bind fun u _ hu => ?_
    exact EOK.ofOption (field?_eraseC ha u) fun w hw => hu.field? hw

/-- Read the erased side of an `EOK` at an answer. -/
theorem EOK.eq_ok {r r' : Res Value} {v : Value} (h : EOK Q r r') (hr : r = .ok v) :
    r' = .ok (swapX v) := by
  rw [h.1, hr]; rfl

theorem EOK.eq_error {r r' : Res Value} {e : Stuck} (h : EOK Q r r') (hr : r = .error e) :
    r' = .error e := by
  rw [h.1, hr]; rfl

theorem pathSet_erase_eq (hQ : QInj Q) (hρ : ScopeIn Q ρ) {v : Value} (hv : AllIn Q v) :
    ∀ {p : Path}, FOp p → ∀ n w,
      pathSet n env (eraseScope ρ) (swapX v) p (swapX w) = swapX <$> pathSet n env ρ v p w
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
        simp only [bind, Except.bind, asNat?_eraseC]
        cases iv.asNat? with
        | none => rfl
        | some i =>
          simp only [Res.ofOption, setIdx_eraseC]
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
          simp only [asNat?_eraseC]
          cases x.asNat? with
          | none => rfl
          | some i =>
            cases y.asNat? with
            | none => rfl
            | some k =>
              simp only [Res.ofOption, setSlice_eraseC]
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
      simp only [bind, Except.bind, Res.ofOption, setField_eraseC ha]
      cases u.setField _ w with
      | none => rfl
      | some u' => exact pathSet_erase_eq hQ hρ hv hp n u'

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase
