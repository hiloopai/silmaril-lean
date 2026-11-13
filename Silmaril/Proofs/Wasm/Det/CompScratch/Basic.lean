module

public import Silmaril.Wasm.Det.CompScratch.Defs

/-!
# The scratch-buffer discipline on the reference machine: unwinding

`reach_obs`: every call state is `Obs`-related to an instantiation (confinement, by induction
on `CompReach`). With symmetry and transitivity, any two call states are related, and
observation gives statelessness (`compStateless_of_obs`). `ScratchEqH` and `ScratchCfg` are
reflexive, symmetric and transitive.

New proofs (the `ScratchEqH` lemmas follow `Silmaril.Proofs.Wasm.Det.Component.scratchEq_*`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.CompScratch

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host initConfig Engine core3P)
open Silmaril.Wasm.Det.Core.Component Silmaril.Wasm.Det.CompScratch

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

theorem reach_obs {prof : ProfileKind} {h : Host E σ} {σ0 : σ} {comp : Syntax.Component E.Module}
    {args : Instantiate.Exports E} {Obs : Config E σ → Config E σ → Prop}
    (htr : ∀ {a b c}, Obs a b → Obs b c → Obs a c) (hc : RefConfined prof h σ0 comp args Obs)
    {m : Config E σ} {es : List (String × FuncId)} (hm : CompReach prof h σ0 comp args m es) :
    ∃ m₀ i es₀, Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m₀ i es₀ ∧ Obs m₀ m := by
  induction hm with
  | inst hi => exact ⟨_, _, _, hi, hc.inst _ _ _ _ _ _ hi hi⟩
  | call hm hf hcall ih =>
    obtain ⟨m₀, i, es₀, hi, ho⟩ := ih
    exact ⟨m₀, i, es₀, hi, htr ho (hc.call _ _ hm _ _ _ _ _ _ hf hcall)⟩

/-- **Unwinding on the reference machine**: confinement and observation give statelessness. -/
theorem compStateless_of_obs {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    {Obs : Config E σ → Config E σ → Prop} (hsy : ∀ {a b}, Obs a b → Obs b a)
    (htr : ∀ {a b c}, Obs a b → Obs b c → Obs a c) (hc : RefConfined prof h σ0 comp args Obs)
    (hd : RefObsDetermines prof h σ0 comp args Obs) : CompStateless prof h σ0 comp args := by
  intro m₁ es₁ m₂ es₂ hm₁ hm₂
  obtain ⟨n₁, i₁, f₁, hi₁, ho₁⟩ := reach_obs (Obs := Obs) htr hc hm₁
  obtain ⟨n₂, i₂, f₂, hi₂, ho₂⟩ := reach_obs (Obs := Obs) htr hc hm₂
  have h₁₂ : Obs m₁ m₂ := htr (hsy ho₁) (htr (hc.inst _ _ _ _ _ _ hi₁ hi₂) ho₂)
  exact hd m₁ es₁ m₂ es₂ hm₁ hm₂ h₁₂

/-! ## The scratch relation -/

theorem scratchEqH_refl {H : Type} (m lo hi : Nat) (s : Silmaril.Wasm.Execution.Core.Store H) :
    ScratchEqH m lo hi s s := by
  refine ⟨rfl, rfl, fun _ _ => rfl, fun mi₁ mi₂ h₁ h₂ => ?_⟩
  have he : mi₁ = mi₂ := Option.some.inj (h₁.symm.trans h₂)
  rw [he]
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem scratchEqH_symm {H : Type} {m lo hi : Nat} {s₁ s₂ : Silmaril.Wasm.Execution.Core.Store H}
    (h : ScratchEqH m lo hi s₁ s₂) : ScratchEqH m lo hi s₂ s₁ := by
  obtain ⟨h₀, hl, hj, hm⟩ := h
  refine ⟨h₀.symm, hl.symm, fun j hj' => (hj j hj').symm, fun mi₁ mi₂ h₁ h₂ => ?_⟩
  obtain ⟨ht, hs, hb⟩ := hm mi₂ mi₁ h₂ h₁
  exact ⟨ht.symm, hs.symm, fun k hk => (hb k hk).symm⟩

theorem scratchEqH_trans {H : Type} {m lo hi : Nat}
    {s₁ s₂ s₃ : Silmaril.Wasm.Execution.Core.Store H} (h₁₂ : ScratchEqH m lo hi s₁ s₂)
    (h₂₃ : ScratchEqH m lo hi s₂ s₃) : ScratchEqH m lo hi s₁ s₃ := by
  obtain ⟨a₀, al, aj, am⟩ := h₁₂
  obtain ⟨b₀, bl, bj, bm⟩ := h₂₃
  refine ⟨a₀.trans b₀, al.trans bl, fun j hj => (aj j hj).trans (bj j hj), ?_⟩
  intro mi₁ mi₃ h₁ h₃
  have hlt : m < s₁.mems.length := (List.getElem?_eq_some_iff.mp h₁).1
  have h₂ : s₂.mems[m]? = some s₂.mems[m] := List.getElem?_eq_getElem (al ▸ hlt)
  obtain ⟨ta, sa, ba⟩ := am mi₁ _ h₁ h₂
  obtain ⟨tb, sb, bb⟩ := bm _ mi₃ h₂ h₃
  exact ⟨ta.trans tb, sa.trans sb, fun k hk => (ba k hk).trans (bb k hk)⟩

variable {P : Silmaril.Wasm.Numerics.Profile} {τ : Type}

theorem scratchCfg_refl (m lo hi : Nat) (c : Config (core3P P) τ) : ScratchCfg m lo hi c c :=
  ⟨rfl, scratchEqH_refl m lo hi _⟩

theorem scratchCfg_symm {m lo hi : Nat} {c₁ c₂ : Config (core3P P) τ}
    (h : ScratchCfg m lo hi c₁ c₂) : ScratchCfg m lo hi c₂ c₁ :=
  ⟨h.1.symm, scratchEqH_symm h.2⟩

theorem scratchCfg_trans {m lo hi : Nat} {c₁ c₂ c₃ : Config (core3P P) τ}
    (h₁ : ScratchCfg m lo hi c₁ c₂) (h₂ : ScratchCfg m lo hi c₂ c₃) : ScratchCfg m lo hi c₁ c₃ :=
  ⟨h₁.1.trans h₂.1, scratchEqH_trans h₁.2 h₂.2⟩

end Silmaril.Proofs.Wasm.Det.CompScratch
