module

public import Silmaril.Wasm.Category.Programs.Defs

@[expose] public section

/-!
# The category of Wasm programs is sound for Core 3.0

`wasm_programs_sound` collects the guarantees of `WasmProg P host` at an arbitrary profile `P`
(no determinism assumption):

1. **every morphism is sound**: a successful translation along a morphism has only behaviours
   that realise behaviours of its source through the morphism's convention (the behaviours
   being, for every object, observations of `Execution.Core.Step P host`);
2. **the semantic map is exact**: the closed-world observations of the divergence-observing
   strategy of a well-formed scalar instance are exactly its Core 3.0 behaviours (answers and
   divergence), and its finite part is the strategy `I.σ P` of `Silmaril.Wasm.Game`;
3. instantiation of scalar modules is exact;
4. **static linking is composition**: the semantic functor into `Silmaril.Games`' category of
   signatures identifies the formal composite of provider and consumer with the linked module,
   for every link in the scalar `Recipe.Assembly` fragment, and the Core 3.0 behaviours of the
   linked module are the observations of that composite;
5. Binaryen IR optimizations with an exact arbitrary-profile contract, conjugated to Core
   modules, are export equivalences of Core modules;
6. components over numeric Core 3.0 instances (`Silmaril.Wasm.Component.Reference.core3Sem P`): wrapping a core instance is exact and
   the component optimiser preserves strategies;
7. **the session ↔ closed-world edge**: for spec-instantiated modules (`IsSpecInstance`, the
   specification's `$instantiate`), closed games observe exactly the Core 3.0 behaviours of
   instantiation and of export calls after it, and each such observation is matched by an
   export-session observation (`moduleObs`) of the module under the host of the environment;
8. **borrowing**: entailment in the behavioural institution of instances is entailment, along
   the semantic map, in that of strategies.

`ssa_sound`: the lambda-SSA object `ssa` is sound for Core 3.0: a lambda-SSA function compiled
along `ssaToCore` has exactly its SSA observations as Core 3.0 behaviours through the
convention (every profile, divergence included), and the lambda-SSA optimiser keeps its
observations.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Wasm Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Games Silmaril.Wasm.Game
  Silmaril.Wasm.Institution Silmaril.Wasm.SSA

/-- **The category of Wasm programs is sound for Core 3.0, at every profile.** -/
theorem wasm_programs_sound {H : Type} (P : Profile) (host : HostSemantics H) :
    -- every morphism is a sound compilation
    (∀ {X Y : WasmObj} (f : WasmProg.of P host X ⟶ WasmProg.of P host Y)
        (p : (lang P host X).Prog) (p' : (lang P host Y).Prog), f.hom.run p = some p' →
        (lang P host Y).beh p' ⊆ f.hom.conv.lift ((lang P host X).beh p)) ∧
    -- the semantic map is exact: strategy observations are Core 3.0 behaviours
    (∀ I : ScalarInstance, I.Ok → (denote P I).obs = instObs P I I.store) ∧
    -- its finite part is the module strategy of `Silmaril.Wasm.Game`
    (∀ I : ScalarInstance, (denote P I).δ.forget = I.σ P) ∧
    -- instantiation is exact
    (∀ (m : Module) (h : Instantiable m),
        (modLang P).beh m = instObs P (instOf h) (instOf h).store) ∧
    -- static linking is composition in the semantic functor
    (∀ S : Linking.Setup, S.Scalar →
        (sem P).map (Linking.Setup.provArrow S).path ≫ (sem P).map (Linking.Setup.consArrow S).path =
          (sem P).map (Linking.Setup.linkArrow S).path) ∧
    -- the Core 3.0 behaviours of a linked module are those of the composite
    (∀ (S : Linking.Setup), S.Scalar → ∀ (K : Env (ifaceSig [])) (f : (ifaceSig S.exportTypes).Op),
        behaviours P (hostOf [] K) S.sl (S.linkedI.addr f.1) f.2.1 =
          compositeObs (K.strategy.comp
            ((sem P).map ((Linking.Setup.provArrow S).path ≫ (Linking.Setup.consArrow S).path))) f ∪
            {b | b = .diverges ∧ Diverges P (hostOf [] K) (invoke S.sl (S.linkedI.addr f.1) f.2.1)}) ∧
    -- forgetting divergence maps the divergence-observing semantics to the plain one
    dsem P ⋙ forgetDiv = sem P ∧
    -- exact Binaryen passes, conjugated to Core modules, are export equivalences
    (∀ (pass : ArbitraryProfile.EquivPass P (closedHost (H := H)))
        (m : (coreValid P (closedHost (H := H))).Prog),
        ExportEquiv (· = ·) P (closedHost (H := H))
          ((coreEndo P closedHost (ArbitraryProfile.Compiler.ofEquivPass pass)).run m).val m.val) ∧
    -- components over Core 3.0 instances: wrapping is exact, the optimiser preserves strategies
    (∀ c : Silmaril.Wasm.Component.Reference.NumInstance,
        (Silmaril.Wasm.Institution.Components.wrap c).denU (Silmaril.Wasm.Component.Reference.core3Sem P) =
          Silmaril.Wasm.Institution.Components.modU (Silmaril.Wasm.Component.Reference.core3Sem P) c) ∧
    (∀ c : Silmaril.Wasm.Component.Comp Silmaril.Wasm.Component.Reference.NumInstance,
        (Silmaril.Wasm.Component.optimizeComponent c).denU (Silmaril.Wasm.Component.Reference.core3Sem P) =
          c.denU (Silmaril.Wasm.Component.Reference.core3Sem P)) ∧
    -- spec instantiation: the closed games observe exactly the Core 3.0 behaviours
    (∀ {m : Module} {mt : Validation.CModuleType} {I : ScalarInstance} {c₀ : Config Nat},
        IsSpecInstance m mt I c₀ → (Silmaril.Wasm.Category.denoteSpec P I c₀).obs = specObs P I c₀) ∧
    -- the session ↔ closed-world edge: spec observations are matched by session observations
    (∀ {m : Module} {mt : Validation.CModuleType} {I : ScalarInstance} {c₀ : Config Nat},
        IsSpecInstance m mt I c₀ → ∀ o ∈ specObs P I c₀,
          ∃ e ∈ (envSession P).beh m, SessionMatch e o) ∧
    -- borrowing along the semantic map
    (∀ (K : Silmaril.Wasm.Institution.Sig (Discrete (instLang P).Iface))
        (Γ : Set ((obsSem (instLang P)).Sen K)) (s : (obsSem (instLang P)).Sen K),
        ((obsSem (instLang P)).room K).Entails Γ s ↔
          ((obsSem dgameLang).room ((Sig.map (denoteR P).ifaceFunctor).obj K)).Entails
            ((denoteR P).translation.sen '' Γ) ((denoteR P).translation.sen s)) :=
  ⟨fun f _ _ h => f.hom.sound_beh h,
    fun _ hI => denote_obs P hI,
    fun I => denote_forget P I,
    fun _ h => modLang_beh_eq P h,
    fun S hS => ((sem P).map_comp _ _).symm.trans (Linking.Setup.sem_link P S hS),
    fun S hS K f => Linking.Setup.linked_behaviours P S hS K f,
    dsem_forget P,
    fun pass m => coreEndo_exportEquiv P pass m,
    fun c => Silmaril.Wasm.Institution.Components.wrap_denU _ c,
    fun c => (Silmaril.Wasm.Component.optimizeComponent_sound' _ c).1,
    fun h => denoteSpec_obs P h,
    fun h _ ho => envSession_of_spec h ho,
    fun K Γ s => (denoteR P).entails_iff Function.surjective_id K Γ s⟩

/-- **The lambda-SSA object is sound for Core 3.0, at every profile.** -/
theorem ssa_sound {H : Type} (P : Profile) (host : HostSemantics H) :
    (∀ (f : SFunc) (p : CoreFn), (WasmProg.ssaToCore P host).hom.run f = some p →
      (lang P host .coreFn).beh p = (ssaCoreConv P).lift ((lang P host .ssa).beh f)) ∧
    (∀ f : SFunc, (lang P host .ssa).beh (optimizeSSA f) = (lang P host .ssa).beh f) :=
  ⟨fun _ _ h => ssaToCore_beh P h, optimizeSSA_beh⟩

end Silmaril.Wasm.Category
