module

public import Silmaril.Calculi.LambdaCube.PER.CubeMorphisms.Defs

@[expose] public section

namespace Silmaril.Proofs.Calculi.LambdaCube.PER.CubeMorphisms

open Silmaril.Calculi.LambdaCube Silmaril.Calculi.LambdaCube.PERModel
open Silmaril.Calculi.LambdaCube.PERModel.SystemF

theorem paramSat_of_omega (M : CombAlg.{0}) (j : PTSJudgment)
    (h : SystemFOmega.ParamSat M j) : ParamSat M j := by
  obtain ⟨hs, hr⟩ := h
  have bnd : ∀ (T : Tele) (t : Tm), (∀ m, t.TyFreeIn m → m < T.numTy) →
      ∀ m, (SystemFOmega.ofFTm t).TyFreeIn m → m < (Tele.toOmega T).kctx.length :=
    fun T t ht m hm => by
      rw [Tele.toOmega_kctx, List.length_replicate]
      exact ht m (Tm.tyFreeIn_of_ofFTm t m hm)
  have rel : ∀ {Γ t B}, SystemFOmega.RelTyping M Γ t B → RelTyping M Γ t B := by
    intro Γ t B hr T t' A hT hΓ ht hA hbt
    subst hΓ ht hA
    exact relValid_of_omega (hr (Tele.toOmega T) (SystemFOmega.ofFTm t') (SystemFOmega.ofF A)
      (Tele.toOmega_wf hT) (Tele.toOmega_toPseudo T)
      (by rw [Tele.toOmega_layout, Tm.toPseudo_ofFTm])
      (by rw [Tele.toOmega_layout, Ty.toPseudo_ofF]) (bnd T t' hbt))
  cases j with
  | typing Γ t B =>
    refine ⟨?_, rel hr⟩
    intro T t' A hT hΓ ht hA hbt
    subst hΓ ht hA
    exact validEq_of_omega (hs (Tele.toOmega T) (SystemFOmega.ofFTm t') (SystemFOmega.ofF A)
      (Tele.toOmega_wf hT) (Tele.toOmega_toPseudo T)
      (by rw [Tele.toOmega_layout, Tm.toPseudo_ofFTm])
      (by rw [Tele.toOmega_layout, Ty.toPseudo_ofF]) (bnd T t' hbt))
  | equation Γ t u B =>
    refine ⟨?_, rel hr.1, rel hr.2⟩
    intro T t' u' A hT hΓ ht hu hA hbt hbu
    subst hΓ ht hu hA
    exact validEq_of_omega (hs (Tele.toOmega T) (SystemFOmega.ofFTm t') (SystemFOmega.ofFTm u')
      (SystemFOmega.ofF A) (Tele.toOmega_wf hT) (Tele.toOmega_toPseudo T)
      (by rw [Tele.toOmega_layout, Tm.toPseudo_ofFTm])
      (by rw [Tele.toOmega_layout, Tm.toPseudo_ofFTm])
      (by rw [Tele.toOmega_layout, Ty.toPseudo_ofF]) (bnd T t' hbt) (bnd T u' hbu))

end Silmaril.Proofs.Calculi.LambdaCube.PER.CubeMorphisms
