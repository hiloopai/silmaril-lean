module

public import Silmaril.Logic.Consequence.HOL.Defs
public import Silmaril.Logic.HOLLight.Kernel.Structural

/-! Proofs for `Silmaril.Logic.Consequence.HOL.Thms`: the kernel as a consequence system. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.HOL

open Silmaril.Consequence Silmaril.Consequence.HOL Silmaril.Logic.HOLLight
open Silmaril.Logic.Institution.Metatheory (HolSig)

variable {S : HolSig}

theorem typed (Γ : List (HOLProp S)) : TypedHyps S.sig [] (Γ.map Subtype.val).toFinset := by
  intro t ht
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
  exact q.2

theorem hyps_subset {Γ Δ : List (HOLProp S)} (h : Γ ⊆ Δ) :
    (Γ.map Subtype.val).toFinset ⊆ (Δ.map Subtype.val).toFinset := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
  exact List.mem_toFinset.2 (List.mem_map_of_mem (h hq))

theorem kernelFrom_closed (Δ : Theory) :
    Structural.Closed Structural.tarskiRules (kernelFrom S Δ) where
  refl _ Γ c hc :=
    (Derives.assume c.2).weaken (Finset.singleton_subset_iff.2
      (List.mem_toFinset.2 (List.mem_map_of_mem hc))) (typed Γ)
  weak Γ Γ' _ h d := d.weaken (hyps_subset h) (typed Γ')
  cut _ ps _ hps hc := by
    refine Derives.substituteHyps hc (typed _) fun q hq => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact (hps p hp).weaken
      (hyps_subset fun x hx => List.mem_flatMap.2 ⟨p, hp, hx⟩) (typed _)

theorem kernelFrom_tySubst (Δ : Theory) (σ : Nat → Ty) (hσ : ∀ i, (σ i).WellFormed S.sig.tyOps)
    {Γ : List (HOLProp S)} {p : HOLProp S} (h : kernelFrom S Δ Γ p) :
    kernelFrom S Δ (Γ.map (HOLProp.tySubst σ hσ)) (HOLProp.tySubst σ hσ p) := by
  have e : ((Γ.map (HOLProp.tySubst σ hσ)).map Subtype.val).toFinset =
      (Γ.map Subtype.val).toFinset.image (Tm.tySubst σ) := by
    refine Finset.ext fun t => ?_
    rw [List.mem_toFinset, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hq
      exact ⟨a.1, List.mem_toFinset.2 (List.mem_map_of_mem ha), rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hr)
      exact List.mem_map.2 ⟨HOLProp.tySubst σ hσ a, List.mem_map_of_mem ha, rfl⟩
  show Derives _ _ _ _
  rw [e]
  exact Derives.instType σ hσ h

theorem kernelFrom_freeSubst (Δ : Theory) (σ : Nat → Ty → Tm)
    (hσ : ∀ n B, B.WellFormed S.sig.tyOps → HasType S.sig [] (σ n B) B)
    {Γ : List (HOLProp S)} {p : HOLProp S} (h : kernelFrom S Δ Γ p) :
    kernelFrom S Δ (Γ.map (HOLProp.freeSubst σ hσ)) (HOLProp.freeSubst σ hσ p) := by
  have e : ((Γ.map (HOLProp.freeSubst σ hσ)).map Subtype.val).toFinset =
      (Γ.map Subtype.val).toFinset.image (Tm.freeSubst σ) := by
    refine Finset.ext fun t => ?_
    rw [List.mem_toFinset, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hq
      exact ⟨a.1, List.mem_toFinset.2 (List.mem_map_of_mem ha), rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hr)
      exact List.mem_map.2 ⟨HOLProp.freeSubst σ hσ a, List.mem_map_of_mem ha, rfl⟩
  show Derives _ _ _ _
  rw [e]
  exact Derives.inst σ hσ h

end Silmaril.Proofs.Logic.Consequence.HOL
