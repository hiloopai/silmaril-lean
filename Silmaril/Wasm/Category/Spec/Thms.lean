module

public import Silmaril.Wasm.Category.Spec.Defs
public import Silmaril.Proofs.Wasm.Category.Spec.Basic

@[expose] public section

/-!
# The session ↔ closed-world edge: morphisms

Proofs in `Silmaril.Proofs.Wasm.Category.Spec.Basic`. Every profile `P`.

* `envToCore P ts K : Compiler (envSession P) (coreSession P (hostOf ts K))`: the fibre at an
  environment (every session observation under `hostOf ts K` is an environment-session
  observation).
* **`sessionToSpec P : Compiler (envSession P) (specLang P)`**, at the convention
  `SessionMatch`: for every spec-instantiable module, each closed-world observation of its
  spec instantiation (instantiation behaviour; behaviour of an export call after
  instantiation) is matched by a session observation of the same module, under the host of the
  same environment, from the store of fresh host functions (`envSession_of_spec`). The session
  side is silmaril-lean's `moduleObs` (the observation of `ExportRefines`).
* **`specDenoteR P`**: spec-instantiable modules to closed games, exact by adequacy
  (`denoteSpec_obs`): the game observations are the Core 3.0 behaviours, divergence included.

Not shown: the converse of `sessionToSpec` (every session observation is a spec observation),
which needs uniqueness of `Instantiate` under an arbitrary profile; and that the `[returns []]`
(stopped session) alternative of `SessionMatch` is vacuous (it is, for well-formed stores after
instantiation, by `Silmaril.Wasm.Game`'s private `startT_wellFormed`, not exported in a header).
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable (P : Profile)

theorem specLang_beh_pos {m : Module} (h : SpecInstantiable m) :
    (specLang P).beh m = specObs P (specOf h).1 (specOf h).2 := by
  simp only [specLang, h, ↓reduceDIte]

theorem specLang_beh_neg {m : Module} (h : ¬ SpecInstantiable m) : (specLang P).beh m = ∅ := by
  simp only [specLang, h, ↓reduceDIte]
  rfl

/-- **The fibre of environment sessions at an environment.** -/
def envToCore (ts : List FnType) (K : Env (ifaceSig ts)) :
    Compiler (envSession P) (coreSession P (hostOf ts K)) where
  conv := ⟨id, fun e o => e = ⟨ts, K, o⟩⟩
  run m := some m
  sound m m' h := by
    have e : m = m' := Option.some.inj h
    subst e
    exact (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨⟨ts, K, o⟩, ho, rfl⟩⟩

/-- **The session ↔ closed-world edge**: sessions against environments to spec instantiation,
identity on modules. -/
noncomputable def sessionToSpec : Compiler (envSession P) (specLang P) where
  conv := ⟨id, SessionMatch⟩
  run m := some m
  sound m m' h := by
    have e : m = m' := Option.some.inj h
    subst e
    refine (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ?_⟩
    by_cases hm : SpecInstantiable m
    · have ho' : o ∈ specObs P (specOf hm).1 (specOf hm).2 := by
        have e : (specLang P).beh m = specObs P (specOf hm).1 (specOf hm).2 :=
          specLang_beh_pos P hm
        exact e ▸ ho
      obtain ⟨e, he, hR⟩ := envSession_of_spec (specOf_spec hm) ho'
      exact ⟨e, he, hR⟩
    · have e : (specLang P).beh m = ∅ := specLang_beh_neg P hm
      exact absurd (e ▸ ho : o ∈ (∅ : Set SpecObs)) (Set.notMem_empty o)

/-- **Spec-instantiable modules denote closed games, exactly.** -/
noncomputable def specDenoteR :
    Realiser ((specLang P).onInvariant SpecInstantiable) closedGameLang where
  Φ := id
  prog m := denoteSpec P (specOf m.2).1 (specOf m.2).2
  g := id
  g_injective := Function.injective_id
  iface _ := rfl
  beh m := by
    have e₁ : (denoteSpec P (specOf m.2).1 (specOf m.2).2).obs =
        specObs P (specOf m.2).1 (specOf m.2).2 := denoteSpec_obs P (specOf_spec m.2)
    have e₂ : (specLang P).beh m.1 = specObs P (specOf m.2).1 (specOf m.2).2 :=
      specLang_beh_pos P m.2
    exact (Set.image_id _).trans (e₁.trans e₂.symm)

end Silmaril.Wasm.Category
