module

public import Silmaril.Wasm.Category.Closed.Defs

@[expose] public section

/-!
# Closed-world languages: proofs

Adequacy of the denotation (`denote_obs`, from `ScalarInstance.adequacy_div_comp`), exactness of
instantiation on instantiable modules (`modLang_beh_eq`, from `IsInstance.unique`) and
monotonicity of the game observations in strategy refinement (`obs_mono`). Summary in
`Silmaril.Wasm.Category.Closed.Thms`.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

/-- **Adequacy of the denotation**: the closed-world observations of the divergence-observing
strategy of a well-formed instance are its Core 3.0 behaviours, at every profile. -/
theorem denote_obs (P : Profile) {I : ScalarInstance} (hI : I.Ok) :
    (denote P I).obs = instObs P I I.store := by
  ext o
  constructor
  · rintro ⟨K, f, b, rfl, hK, hb⟩
    have e : behaviours P (hostOf I.imports K) I.store (I.addr f.1) f.2.1 =
        dcompositeObs (K.dstrategy.comp (I.dstrategy P I.store)) f :=
      ScalarInstance.adequacy_div_comp hI K hK f
    have hb' : b ∈ behaviours P (hostOf I.imports K) I.store (I.addr f.1) f.2.1 := by
      rw [e]
      exact hb
    exact ⟨K, f, b, rfl, hK, hb'⟩
  · rintro ⟨K, f, b, rfl, hK, hb⟩
    have e : behaviours P (hostOf I.imports K) I.store (I.addr f.1) f.2.1 =
        dcompositeObs (K.dstrategy.comp (I.dstrategy P I.store)) f :=
      ScalarInstance.adequacy_div_comp hI K hK f
    have hb' : b ∈ dcompositeObs (K.dstrategy.comp (I.dstrategy P I.store)) f := by
      rw [← e]
      exact hb
    exact ⟨K, f, b, rfl, hK, hb'⟩

/-- Two instances of one module are equal (the module type is determined by validation). -/
theorem isInstance_eq {m : Module} {mt mt' : CModuleType} {I J : ScalarInstance}
    (hI : IsInstance m mt I) (hJ : IsInstance m mt' J) : I = J := by
  have hmt : mt = mt' := Option.some.inj (hI.valid.symm.trans hJ.valid)
  subst hmt
  exact IsInstance.unique hI hJ

/-- **Exactness of instantiation**: the behaviours of an instantiable module are those of its
instance. -/
theorem modLang_beh_eq (P : Profile) {m : Module} (h : Instantiable m) :
    (modLang P).beh m = instObs P (instOf h) (instOf h).store := by
  ext o
  constructor
  · rintro ⟨mt, J, hJ, ho⟩
    have e : J = instOf h := isInstance_eq hJ (instOf_spec h)
    exact e ▸ ho
  · intro ho
    exact ⟨h.choose, instOf h, instOf_spec h, ho⟩

/-- The interface of an instantiable module is that of its instance. -/
theorem moduleIface_eq {m : Module} (h : Instantiable m) : moduleIface m = sIface (instOf h) := by
  simp only [moduleIface, h, ↓reduceDIte]

/-- The observations of a closed divergence-observing composite are monotone in the strategy. -/
theorem dcompositeObs_mono {ts : List FnType} {δ δ' : DStrategy Sig.empty (ifaceSig ts)}
    (h : δ ≤ δ') (f : (ifaceSig ts).Op) : dcompositeObs δ f ⊆ dcompositeObs δ' f := by
  rintro b (⟨w, hw, rfl⟩ | ⟨rfl, hd⟩)
  · exact Or.inl ⟨w, h.1 hw, rfl⟩
  · exact Or.inr ⟨rfl, h.2.1 hd⟩

/-- **Game refinement implies inclusion of closed-world observations.** -/
theorem obs_mono {S : ScalarIface} {n : Nat} {δ δ' : DStrategy (ifaceSig S.1) (ifaceSig S.2)}
    (h : δ ≤ δ') : DProg.obs ⟨S, n, δ⟩ ⊆ DProg.obs ⟨S, n, δ'⟩ := by
  rintro _ ⟨K, f, b, rfl, hK, hb⟩
  have hc : K.dstrategy.comp δ ≤ K.dstrategy.comp δ' := DStrategy.comp_mono le_rfl h
  exact ⟨K, f, b, rfl, hK, dcompositeObs_mono hc f hb⟩

end Silmaril.Wasm.Category
