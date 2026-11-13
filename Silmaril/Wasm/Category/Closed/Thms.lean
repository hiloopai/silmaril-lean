module

public import Silmaril.Wasm.Category.Closed.Defs
public import Silmaril.Proofs.Wasm.Category.Closed.Basic

@[expose] public section

/-!
# Closed-world languages: morphisms and results

Proofs in `Silmaril.Proofs.Wasm.Category.Closed.Basic`.

* `denoteR P : Realiser (instLang P) dgameLang`: **the semantic map into games is exact**:
  the closed-world observations of `I.dstrategy P I.store` are the Core 3.0 behaviours of the
  instance (`denote_obs`, every profile). Hence a valid compiler, a comorphism of behavioural
  institutions borrowing entailment (`Realiser.entails_iff`), and a realising elaboration
  (`Realiser.realises`).
* `instantiateR P : Realiser ((modLang P).onInvariant Instantiable) (instLang P)`: instantiation
  is exact on instantiable modules; `instantiate P : Compiler (modLang P) (instLang P)` is the
  partial compiler (failing on modules without a scalar instance).
* `moduleDenoteR P`: their composite, modules to strategies.
* `denote_forget`: the finite part of the denotation is the plain module strategy `I.σ P` of
  `Silmaril.Wasm.Game` (the morphism into `Silmaril.Games`' category of signatures).
* `instObs_subset_of_dle`: strategy refinement of divergence-observing strategies gives
  inclusion of Core 3.0 behaviours (same interface, same exception bound).
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable (P : Profile)

/-- **The semantic map of instances into divergence-observing strategies**, exact by adequacy. -/
noncomputable def denoteR : Realiser (instLang P) dgameLang where
  Φ := id
  prog I := denote P I.1
  g := id
  g_injective := Function.injective_id
  iface _ := rfl
  beh I := (Set.image_id _).trans (denote_obs P I.2)

/-- **Instantiation**, exact on instantiable modules. -/
noncomputable def instantiateR : Realiser ((modLang P).onInvariant Instantiable) (instLang P) where
  Φ := id
  prog m := ⟨instOf m.2, (instOf_spec m.2).ok⟩
  g := id
  g_injective := Function.injective_id
  iface m := (moduleIface_eq m.2).symm
  beh m := (Set.image_id _).trans (modLang_beh_eq P m.2).symm

open Classical in
/-- **Instantiation as a partial compiler** from modules to instances. -/
noncomputable def instantiate : Compiler (modLang P) (instLang P) where
  conv := ⟨id, fun o o' => o = o'⟩
  run m := if h : Instantiable m then some ⟨instOf h, (instOf_spec h).ok⟩ else none
  sound m I hrun := by
    split at hrun
    · rename_i h
      have hI : (⟨instOf h, (instOf_spec h).ok⟩ : (instLang P).Prog) = I := Option.some.inj hrun
      exact hI ▸ (instantiateR P).valid ⟨m, h⟩
    · exact absurd hrun (by simp)

/-- **Modules to strategies**: instantiation, then the semantic map. -/
noncomputable def moduleDenoteR :
    Realiser ((modLang P).onInvariant Instantiable) dgameLang :=
  (instantiateR P).comp (denoteR P)

/-- The finite part of the denotation is the plain strategy of the instance. -/
theorem denote_forget (I : ScalarInstance) : (denote P I).δ.forget = I.σ P :=
  ScalarInstance.forget_dstrategy P I.store

/-- The denotation of a module is the strategy of its instance. -/
theorem moduleDenoteR_prog (m : ((modLang P).onInvariant Instantiable).Prog) :
    (moduleDenoteR P).prog m = denote P (instOf m.2) := rfl

/-- **Game refinement gives inclusion of Core 3.0 behaviours** of well-formed instances with
the same interface and exception bound: if the strategy of `J` refines that of `I`, every Core
behaviour of an export call of `J` is one of `I`. -/
theorem instObs_subset_of_dle {imp exp : List FnType} {a a' : List Nat} {s s' : Store Nat}
    (hI : ScalarInstance.Ok ⟨imp, exp, a, s⟩) (hJ : ScalarInstance.Ok ⟨imp, exp, a', s'⟩)
    (hn : s.exns.length = s'.exns.length)
    (h : ScalarInstance.dstrategy ⟨imp, exp, a', s'⟩ P s' ≤
      ScalarInstance.dstrategy ⟨imp, exp, a, s⟩ P s) :
    instObs P ⟨imp, exp, a', s'⟩ s' ⊆ instObs P ⟨imp, exp, a, s⟩ s := by
  have hs := obs_mono (S := (imp, exp)) (n := s'.exns.length) h
  have e : denote P ⟨imp, exp, a, s⟩ =
      ⟨(imp, exp), s'.exns.length, ScalarInstance.dstrategy ⟨imp, exp, a, s⟩ P s⟩ := by
    unfold denote
    rw [hn]
  rw [← denote_obs P hJ, ← denote_obs P hI, e]
  exact hs

end Silmaril.Wasm.Category
