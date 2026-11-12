module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Lists

/-!
# Round 7, REH route 2: `evalExp`, one step (unrefined)

`step_exp`: from `ExpAt env n`, the value of `evalExp (n + 1)` satisfies `EOk` in a conforming
scope. Every constructor is a case.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {S : Sig} {T : TSig} {Γ : List (String × AT)}

/-- An expression whose `EOk` follows from its inferred type and its `nxD` judgment, when
`ckE` falls back to them. -/
theorem EOk.of_ty_nx {e : Exp} {v : Value} (hty : vtB S (tyOf S Γ e) v = true)
    (hnx : nxD S Γ e = true → nxB v = true)
    (hck : ∀ a, ckE S T Γ a e = true →
      (atLe S atFuel (tyOf S Γ e) a || (nxAT S.good a && nxD S Γ e)) = true) :
    EOk S T Γ e v :=
  ⟨hty, hnx, fun a h => ck_default hty hnx (hck a h)⟩

/-- **An iteration.** -/
theorem EOk.iter {e : Exp} {it : Iter} {ds : List Dom} {v : Value}
    (h : IterV (EOk S T (iterΓ S Γ it ds) e) v) : EOk S T Γ (.iterE e (.mk it ds)) v := by
  have hty : vtB S (tyOf S Γ (.iterE e (.mk it ds))) v = true := by
    rw [tyOf]
    show vtB S (.iter (tyOf S (iterΓ S Γ it ds) e)) v = true
    cases v with
    | list vs => exact vtB_iter_list fun w hw => (h w hw).ty
    | opt o =>
      cases o with
      | none => exact vtB_optNone _
      | some w => exact vtB_iter_some h.ty
    | _ => cases h
  refine ⟨hty, fun hn => ?_, fun a hc => ?_⟩
  · have hn' : nxE S (iterΓ S Γ it ds) e = true := by
      simpa [nxD, nxE] using hn
    cases v with
    | list vs =>
      simp only [nxB]
      exact nxBs_of_forall fun w hw => (h w hw).nx (nxD_of_nxE e hn')
    | opt o =>
      cases o with
      | none => simp [nxB]
      | some w => simp only [nxB]; exact h.nx (nxD_of_nxE e hn')
    | _ => cases h
  · simp only [ckE, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨_, hc⟩
    · exact vtB_of_atLe S _ _ _ hc v hty
    · cases v with
      | list vs => exact vtB_list_of fun w hw => (h w hw).ck _ hc
      | opt o =>
        cases o with
        | none => exact vtB_optNone _
        | some w => exact vtB_optSome_of (h.ck _ hc)
      | _ => cases h

theorem tyOf_dotE (e : Exp) (k : AtomS) : tyOf S Γ (.dotE e k) = fieldTy S (tyOf S Γ e) k := by
  rw [tyOf]; rfl

theorem tyOf_uncaseE (e : Exp) (op : MixopS) :
    tyOf S Γ (.uncaseE e op) = caseTy S (tyOf S Γ e) op := by
  rw [tyOf]; rfl

theorem tyOf_idxE (e₁ e₂ : Exp) : tyOf S Γ (.idxE e₁ e₂) = elemAT S (tyOf S Γ e₁) := by
  rw [tyOf]

theorem tyOf_theE (e : Exp) : tyOf S Γ (.theE e) = elemAT S (tyOf S Γ e) := by
  rw [tyOf]

theorem tyOf_sliceE (e₁ e₂ e₃ : Exp) : tyOf S Γ (.sliceE e₁ e₂ e₃) = tyOf S Γ e₁ := by
  rw [tyOf]

theorem tyOf_catE (e₁ e₂ : Exp) : tyOf S Γ (.catE e₁ e₂) = tyOf S Γ e₁ := by
  rw [tyOf]

theorem tyOf_projE (e : Exp) {i : Int} (hi : 0 ≤ i) :
    tyOf S Γ (.projE e i) = compTy S (tyOf S Γ e) i.toNat := by
  rw [tyOf]
  unfold compTy unf
  split <;> simp_all

theorem tyOf_subE (e : Exp) (t₁ t₂ : Typ) : tyOf S Γ (.subE e t₁ t₂) = toAT t₂ := by
  rw [tyOf]

theorem tyOf_varE (x : IL.Id) : tyOf S Γ (.varE x) = (Γ.lookup x).getD .unk := by
  rw [tyOf]

theorem tyOf_callE (f : IL.Id) (xs : List Arg) :
    tyOf S Γ (.callE f xs) = (S.results.lookup f).getD .unk := by
  rw [tyOf]

theorem tyOf_optSome (e : Exp) : tyOf S Γ (.optE (some e)) = .iter (tyOf S Γ e) := by
  rw [tyOf, tyOfOpt]

theorem tyOf_listE_cons (e : Exp) (es : List Exp) :
    tyOf S Γ (.listE (e :: es)) = .iter (tyOf S Γ e) := by
  rw [tyOf, tyOfHead]

theorem tyOf_listE_nil : tyOf S Γ (.listE []) = .unk := by
  rw [tyOf, tyOfHead]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
