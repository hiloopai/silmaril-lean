module

public import Silmaril.Logic.HOLLight.Soundness.Defs

@[expose] public section

/-! Implementation of soundness by induction over every kernel inference rule. -/

namespace Silmaril.Proofs.Logic.HOLLight

open Silmaril.Logic.HOLLight

universe u

theorem derives_sound {sig : Signature} {theory : Theory} {H : Hyps} {p : Tm}
    (proof : Derives sig theory H p) (M : Model.{u} sig) (model : Models M theory) :
    Entails M H p := by
  induction proof with
  | «axiom» member _ => exact fun ρ ν _ => model _ member ρ ν
  | refl typing =>
      intro ρ ν _
      obtain ⟨value, ht⟩ := typing.eval_exists M ρ ν BoundEnv.empty
      exact Holds.equal ht ht rfl
  | trans left right ihl ihr =>
      intro ρ ν hH
      obtain ⟨x, hs, ht⟩ := Holds.equal_iff.mp (ihl ρ ν
        (fun q hq => hH q (Finset.mem_union_left _ hq)))
      obtain ⟨y, ht', hr⟩ := Holds.equal_iff.mp (ihr ρ ν
        (fun q hq => hH q (Finset.mem_union_right _ hq)))
      exact Holds.equal hs hr (ht.unique ht')
  | mkComb hf hx ihf ihx =>
      intro ρ ν hH
      obtain ⟨f, hf, hg⟩ := Holds.equal_iff.mp (ihf ρ ν
        (fun q hq => hH q (Finset.mem_union_left _ hq)))
      obtain ⟨x, hx, hy⟩ := Holds.equal_iff.mp (ihx ρ ν
        (fun q hq => hH q (Finset.mem_union_right _ hq)))
      exact Holds.equal (.app hf hx) (.app hg hy) rfl
  | @abs H A B s t name hA fresh h ih =>
      intro ρ ν hH
      have pointwise : ∀ x : Value M ρ A, ∃ value,
          Eval M ρ (ν.update name A x) BoundEnv.empty s B value ∧
          Eval M ρ (ν.update name A x) BoundEnv.empty t B value := by
        intro x
        apply Holds.equal_iff.mp
        apply ih ρ (ν.update name A x)
        intro q hq
        obtain ⟨v, hv, ht⟩ := hH q hq
        exact ⟨v, hv.update_fresh name x (fresh q hq), ht⟩
      choose function hs ht using pointwise
      exact Holds.equal
        (.lam hA (fun x => Eval.abstractFree name x (hs x)))
        (.lam hA (fun x => Eval.abstractFree name x (ht x))) rfl
  | @beta A B body name hA hb fresh =>
      intro ρ ν _
      obtain ⟨f, hf⟩ := (HasType.lam hA hb).eval_exists M ρ ν BoundEnv.empty
      have hx : Eval M ρ ν BoundEnv.empty (.fvar name A) A (ν name A) :=
        .fvar BoundEnv.empty name hA
      have result := Eval.app hf hx
      cases hf with
      | lam _ hbody => exact Holds.equal result ((hbody (ν name A)).open hx) rfl
  | assume _ => exact fun _ _ hH => hH _ (Finset.mem_singleton_self _)
  | eqMp heq hp iheq ihp =>
      intro ρ ν hH
      obtain ⟨value, hpv, hqv⟩ := Holds.equal_iff.mp (iheq ρ ν
        (fun q hq => hH q (Finset.mem_union_left _ hq)))
      obtain ⟨pvalue, hpv', htrue⟩ := ihp ρ ν
        (fun q hq => hH q (Finset.mem_union_right _ hq))
      exact ⟨value, hqv, (hpv.unique hpv').symm ▸ htrue⟩
  | @deductAntisym H K p q hp hq ihp ihq =>
      intro ρ ν hH
      obtain ⟨x, hx⟩ := hp.typing.eval_exists M ρ ν BoundEnv.empty
      obtain ⟨y, hy⟩ := hq.typing.eval_exists M ρ ν BoundEnv.empty
      apply Holds.equal hx hy
      apply Carrier.bool_ext
      constructor
      · intro hpx
        obtain ⟨v, hv, ht⟩ := ihq ρ ν (fun r hr => by
          by_cases eq : r = p
          · cases eq; exact ⟨x, hx, hpx⟩
          · exact hH r (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨eq, hr⟩)))
        exact (hy.unique hv).symm ▸ ht
      · intro hqy
        obtain ⟨v, hv, ht⟩ := ihp ρ ν (fun r hr => by
          by_cases eq : r = q
          · cases eq; exact ⟨y, hy, hqy⟩
          · exact hH r (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq, hr⟩)))
        exact (hx.unique hv).symm ▸ ht
  | @inst H p σ typing hp ih =>
      intro ρ ν hH
      classical
      let μ : FreeEnv M ρ := fun n A =>
        if hA : A.WellFormed sig.tyOps then
          Classical.choose ((typing n A hA).eval_exists M ρ ν BoundEnv.empty)
        else Classical.choice (A.denote M.toTypeModel ρ).property
      have hμ : ∀ n A, A.WellFormed sig.tyOps →
          Eval M ρ ν BoundEnv.empty (σ n A) A (μ n A) := by
        intro n A hA
        dsimp [μ]
        rw [dite_eq_left hA]
        exact Classical.choose_spec ((typing n A hA).eval_exists M ρ ν BoundEnv.empty)
      apply (Holds.freeSubst_iff hp.typing σ μ hμ).mpr
      apply ih ρ μ
      intro q hq
      exact (Holds.freeSubst_iff (hp.typedHyps q hq) σ μ hμ).mp
        (hH _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
  | @instType H p σ typing hp ih =>
      intro ρ ν hH
      apply (Holds.tySubst_iff hp.typing σ typing).mpr
      apply ih (TypeSubstitution.valuation M ρ σ) (TypeSubstitution.freeEnv σ ν)
      intro q hq
      exact (Holds.tySubst_iff (hp.typedHyps q hq) σ typing).mp
        (hH _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))

end Silmaril.Proofs.Logic.HOLLight
