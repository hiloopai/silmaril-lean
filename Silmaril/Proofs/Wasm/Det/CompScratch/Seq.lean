module

public import Silmaril.Proofs.Wasm.Det.CompScratch.Basic

/-!
# Unwinding over fresh, admissible call sequences

`seqReach_obs`: every session configuration is `Obs`-related to an instantiation
(`RefConfinedSeq`, by induction on `SeqReach`); with symmetry and transitivity any two session
configurations are related, and `RefObsDeterminesSeq` gives `CompStatelessSeq`
(`compStatelessSeq_of_obs`). `BookCfg` is reflexive, symmetric and transitive.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.CompScratch

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host initConfig Engine core3P)
open Silmaril.Wasm.Det.Core.Component Silmaril.Wasm.Det.CompScratch

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

theorem seqReach_obs {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    {Adm : String → List Value.Val → Prop} {Obs : Config E σ → Config E σ → Prop}
    (htr : ∀ {a b c}, Obs a b → Obs b c → Obs a c) (hc : RefConfinedSeq prof h σ0 comp args Adm Obs)
    {m : Config E σ} {es : List (String × FuncId)} {k : Nat}
    (hm : SeqReach prof h σ0 comp args Adm m es k) :
    ∃ m₀ i es₀, Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m₀ i es₀ ∧ Obs m₀ m := by
  induction hm with
  | inst hi => exact ⟨_, _, _, hi, hc.inst _ _ _ _ _ _ hi hi⟩
  | call hm hf ha hcall ih =>
    obtain ⟨m₀, i, es₀, hi, ho⟩ := ih
    exact ⟨m₀, i, es₀, hi, htr ho (hc.call _ _ _ hm _ _ _ _ _ hf ha hcall)⟩

/-- **Unwinding over sessions.** -/
theorem compStatelessSeq_of_obs {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    {Adm : String → List Value.Val → Prop} {Obs : Config E σ → Config E σ → Prop}
    (hsy : ∀ {a b}, Obs a b → Obs b a) (htr : ∀ {a b c}, Obs a b → Obs b c → Obs a c)
    (hc : RefConfinedSeq prof h σ0 comp args Adm Obs)
    (hd : RefObsDeterminesSeq prof h σ0 comp args Adm Obs) :
    CompStatelessSeq prof h σ0 comp args Adm := by
  intro m₁ es₁ k₁ m₂ es₂ k₂ hm₁ hm₂
  obtain ⟨n₁, i₁, f₁, hi₁, ho₁⟩ := seqReach_obs (Obs := Obs) htr hc hm₁
  obtain ⟨n₂, i₂, f₂, hi₂, ho₂⟩ := seqReach_obs (Obs := Obs) htr hc hm₂
  exact hd _ _ _ _ _ _ hm₁ hm₂ (htr (hsy ho₁) (htr (hc.inst _ _ _ _ _ _ hi₁ hi₂) ho₂))

/-- Statelessness over sessions gives observation for every relation. -/
theorem refObsDeterminesSeq_of_stateless {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    {Adm : String → List Value.Val → Prop} (Obs : Config E σ → Config E σ → Prop)
    (hs : CompStatelessSeq prof h σ0 comp args Adm) :
    RefObsDeterminesSeq prof h σ0 comp args Adm Obs :=
  fun _ _ _ _ _ _ hm₁ hm₂ _ => hs _ _ _ _ _ _ hm₁ hm₂

variable {P : Silmaril.Wasm.Numerics.Profile} {τ : Type}

theorem bookCfg_refl (m lo hi : Nat) (c : Config (core3P P) τ) : BookCfg m lo hi c c :=
  ⟨rfl, scratchEqH_refl m lo hi _⟩

theorem bookCfg_symm {m lo hi : Nat} {c₁ c₂ : Config (core3P P) τ}
    (h : BookCfg m lo hi c₁ c₂) : BookCfg m lo hi c₂ c₁ :=
  ⟨h.1.symm, scratchEqH_symm h.2⟩

theorem bookCfg_trans {m lo hi : Nat} {c₁ c₂ c₃ : Config (core3P P) τ}
    (h₁ : BookCfg m lo hi c₁ c₂) (h₂ : BookCfg m lo hi c₂ c₃) : BookCfg m lo hi c₁ c₃ :=
  ⟨h₁.1.trans h₂.1, scratchEqH_trans h₁.2 h₂.2⟩

end Silmaril.Proofs.Wasm.Det.CompScratch
