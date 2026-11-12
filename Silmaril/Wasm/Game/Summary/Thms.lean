module

public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.Game.Linking.Thms
public import Silmaril.Wasm.Game.DivAdequacy.Thms
public import Silmaril.Wasm.Game.LinkStart.Thms
public import Silmaril.Wasm.Game.SpecInst.Thms
public import Silmaril.Wasm.Game.Examples.Thms
public import Silmaril.Wasm.Game.LinkDiv.Thms

/-!
# Games are a sound categorical semantics for scalar Core 3.0

Three summary statements.

`games_sound_categorical_semantics_profile` holds for an **arbitrary**
silmaril profile `P` (any `$ND`, relaxed choices, NaN policy, grow policy; in
particular the spec semantics `Profile.spec nd R`):

1. **The category.** Signatures and strategies form a category (`Silmaril.Games`,
   identities are copycat, composition hides the shared interface), each
   hom-set ordered by refinement with composition monotone.
2. **The semantic map.** A module `m` with an instance `I` (`IsInstance`:
   validated, function imports only, no start function, scalar interfaces,
   instantiated by `instantiateOnce?`; modules with a start function are
   covered by `games_sound_start_profile` below) denotes the strategy
   `I.σ P : ifaceSig I.imports ⟶ ifaceSig I.exports`; the instance is unique,
   so the strategy of `m` is well defined. Under a nondeterministic profile
   the strategy is a nondeterministic Silmaril strategy (Proponent may have
   several next moves). The strategy is monotone in the profile.
3. **Adequacy.** Closed against any environment `K` (a stateless,
   store-preserving partial answer function on import calls, throwing only
   existing exceptions), the Core closed-world behaviours of an export call
   under the induced host `hostOf K` are the observations of
   `K.strategy ≫ I.σ P` together with may-divergence:
   `behaviours = compositeObs ∪ {diverges | Diverges}`. Hence the
   terminating behaviours (returns, traps, uncaught exceptions) are *exactly*
   the answers of the composite (both inclusions), the absence of an answer is
   divergence, and divergence is a behaviour exactly when the invocation has
   an infinite run. This holds at the initial store and at every well-formed
   store. Plain Silmaril strategies observe only finite plays, so they cannot
   express "may diverge although some branch answers"; in this plain
   statement that clause is the Core predicate `Diverges`.
4. **Adequacy, divergence observed by the game.** The divergence-observing
   closed program `I.closedD P s K` (`Silmaril.Games.DivLTS` strategy of the
   environment's and the instance's systems composed, host-free steps
   silent, unanswered calls diverging) has the finite plays of
   `K.strategy ≫ I.σ P` and the Core behaviours are **exactly** its
   observations `dcompositeObs`: answers, and `diverges` when it may diverge
   after the question (`IsInstance.adequacy_div`), for every profile. The
   closed program is the composite `K.dstrategy.comp (I.dstrategy P s)` of
   the components' divergence-observing strategies (`closedD_eq_comp`, by
   `DStrategy.ofLTS_comp`), so divergence is read off `DStrategy.comp`.
5. **Compositionality (M3).** Static linking (`link?`) is composition:
   `σ_linked = σ_provider ≫ σ_consumer` (the provider's store persisting across
   the consumer's calls), for every profile. The inclusion `≤` is a forward
   simulation; `=` uses the backward simulations of the linker relation
   (`Linking.reachReverse_all`) and of the split world
   (`Linking.Setup.splitReflects`), proved from determinism of host-free Core
   steps up to profile choices (`Silmaril.Proofs.Wasm.Game.Choice.soft_join`).
   **With divergence and infinite plays observed**:
   `S.linkedI.dstrategy P S.sl = (S.providerI.dstrategy P S.sp).comp (S.consumerI.dstrategy P
   S.scs)` (`Setup.link_is_composition_div`, divergence-sensitive simulations in both
   directions). For global-free modules the stores of the setup are the specification's
   instantiations (`Setup.instantiate_spec`).

6. **The specification's instantiation.** For a module `m` with a spec
   instance `IsSpecInstanceAt s xas m mt I c₀` (validated, allocated by the
   spec's `prepare?` into a typed store `s` against addresses `xas` of its
   import types, which may be globals, memories, tables, tags or functions;
   the host functions of `s` are the scalar imports of the game, the rest of
   `s` is owned by the closed program; any `start` field, any data/element
   segments the validator accepts; `IsSpecInstance` is the case of fresh host
   functions), `c₀` is the configuration of `$instantiate` (silmaril-lean's
   `Instantiate P host`) for every profile and host; the instantiation observations of the closed
   program `I.closedSpec P c₀ K` are exactly the Core 3.0 behaviours
   `behavioursOf P (hostOf K) c₀` (segment initialisation, which may trap, then
   the start function, which may call imports, trap, throw or diverge), and the
   export calls right after instantiation have exactly the Core behaviours at
   the stores that run may return at. A concrete module whose start function
   calls an import satisfies the hypothesis (`Examples.ex_isSpecInstance`), and
   its instantiation diverges against an environment that never answers; a
   module importing a memory, with a data segment, is a spec instance at a
   store holding the memory (`Examples.exMem_isSpecInstanceAt`).

`games_sound_start_profile` (every profile) covers **start functions**: a
module instantiated by `instantiateOnce?` before its start function
(`IsInstanceStart`; `IsInstance` is the case without one) has a strategy with
an instantiation phase (`Silmaril.Games.Inst`), whose closed program's
instantiation observations are exactly the Core behaviours of the start
function, and whose export calls right after instantiation have exactly the
Core behaviours of the call at the stores the start function may return at;
the game-semantic link of a provider and a consumer with start functions
instantiates the provider first, fails when the provider's start function
fails, and is ready only if it may return; and **M3 with start functions**:
the finite plays of the linked module's instantiable strategy, whose
instantiation runs the provider's start function and then the consumer's, are
those of that link (`StartSetup.link_is_composition_inst`).

`games_sound_categorical_semantics` is the earlier statement for the
deterministic profiles `profile o` (any grow oracle), where adequacy is an
equality with `compositeObs` (divergence *is* the absence of an answer) and
linking is composition (equality); its adequacy clauses are derived from the
arbitrary-profile ones (`adequacy_of_no_mixed`).

## The fragment

Store-independent interfaces (numbers, `v128` and `(ref null? i31)` only
cross an interface); in this
summary, environments that are stateless across calls and do not change the
store (exactly the Core hosts of the form `hostOf K`; stateful and
nondeterministic environments, i.e. every environment strategy, are covered
by `Silmaril.Wasm.Game.StatefulEnv`, which still requires store preservation);
imported globals, memories, tables and tags only in clause 6, as state owned
by the closed program (the environment answers calls and never reads or writes
the store, so this state is not shared with it; exported non-function
entities are not observed); start functions in clause 6 (the spec's
`$instantiate` configuration) and in
`games_sound_start_profile` (`instantiateOnce?` then `$invoke(start, [])`; M3
with start functions compares finite plays only, not the divergence-observing
strategies, and is stated for the `instantiateOnce?` instances of the linker
correspondence);
for linking, the
fragment of `Recipe.Assembly` (no memories, tables, tags, data or element
segments, closed provider). The strategy of a module is taken for its
instantiation against fresh host functions (`importStore`); the linking
statement uses the instantiations over a common host-free base store that the
linker correspondence (`Setup`) is stated for. Nothing here is a
full-abstraction result: refinement of strategies is not shown to coincide
with contextual refinement of modules.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open CategoryTheory Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- **Games are a sound categorical semantics for scalar Core 3.0, for every profile** (in the
fragment of the module documentation): the game category, the well-defined strategy of a
module (monotone in the profile), adequacy w.r.t. Core closed-world behaviours (terminating
behaviours exactly, divergence as may-divergence; exactly, divergence included, for the
divergence-observing closed program) at every well-formed store, static linking as
composition (`≤` and `=`), and the specification's instantiation (segment initialisation and
the module's start function, run by Core 3.0 reduction) as the instantiation phase of the game,
with a non-vacuity witness. -/
theorem games_sound_categorical_semantics_profile :
    -- the category of signatures and strategies, ordered by refinement
    (∀ {E F : Sig.{0}} (σ : E ⟶ F), 𝟙 E ≫ σ = σ ∧ σ ≫ 𝟙 F = σ) ∧
    (∀ {E F G H : Sig.{0}} (σ : E ⟶ F) (τ : F ⟶ G) (ρ : G ⟶ H),
      (σ ≫ τ) ≫ ρ = σ ≫ (τ ≫ ρ)) ∧
    (∀ {E F G : Sig.{0}} {σ σ' : Strategy E F} {τ τ' : Strategy F G},
      σ ≤ σ' → τ ≤ τ' → σ.comp τ ≤ σ'.comp τ') ∧
    -- a module has at most one instance, hence one strategy `I.σ P` for each profile
    (∀ {m : Module} {mt : CModuleType} {I J : ScalarInstance},
      IsInstance m mt I → IsInstance m mt J → I = J) ∧
    -- the strategy is monotone in the profile
    (∀ (I : ScalarInstance) {P Q : Profile},
      (∀ c c' : Config Nat, Step P Det.noHost c c' → Step Q Det.noHost c c') →
        ∀ s, I.strategy P s ≤ I.strategy Q s) ∧
    -- adequacy for modules, every profile
    (∀ {m : Module} {mt : CModuleType} {I : ScalarInstance}, IsInstance m mt I →
      ∀ (P : Profile) (K : Env I.E), ThrowsBelow K I.store.exns.length → ∀ f : I.F.Op,
        behaviours P (hostOf I.imports K) I.store (I.addr f.1) f.2.1 =
          compositeObs (K.strategy.comp (I.σ P)) f ∪
            {b | b = .diverges ∧
              Diverges P (hostOf I.imports K) (invoke I.store (I.addr f.1) f.2.1)}) ∧
    -- adequacy for modules with divergence observed by the game, every profile
    (∀ {m : Module} {mt : CModuleType} {I : ScalarInstance}, IsInstance m mt I →
      ∀ (P : Profile) (K : Env I.E), ThrowsBelow K I.store.exns.length → ∀ f : I.F.Op,
        (I.closedD P I.store K).forget = K.strategy.comp (I.σ P) ∧
        I.closedD P I.store K = K.dstrategy.comp (I.dstrategy P I.store) ∧
        behaviours P (hostOf I.imports K) I.store (I.addr f.1) f.2.1 =
          dcompositeObs (I.closedD P I.store K) f) ∧
    -- adequacy at every well-formed store (later calls), every profile
    (∀ (I : ScalarInstance) (P : Profile) (s : Store Nat), I.WellFormed s →
      ∀ (K : Env I.E), ThrowsBelow K s.exns.length → ∀ f : I.F.Op,
        behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
          compositeObs (K.strategy.comp (I.strategy P s)) f ∪
            {b | b = .diverges ∧ Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1)}) ∧
    -- static linking refines composition, every profile
    (∀ (S : Linking.Setup), S.Scalar → ∀ P : Profile,
      (S.providerI.σ P).comp (S.consumerI.σ P) ≤ S.linkedI.σ P) ∧
    -- static linking is composition, every profile
    (∀ (S : Linking.Setup), S.Scalar → ∀ P : Profile,
      S.linkedI.σ P = (S.providerI.σ P).comp (S.consumerI.σ P)) ∧
    -- static linking is composition with divergence and infinite plays observed, every profile
    (∀ (S : Linking.Setup), S.Scalar → ∀ P : Profile,
      S.linkedI.dstrategy P S.sl =
        (S.providerI.dstrategy P S.sp).comp (S.consumerI.dstrategy P S.scs)) ∧
    -- for global-free modules the linked and provider stores are the spec's instantiations
    (∀ (S : Linking.Setup), S.provider.globals = [] ∧ S.consumer.globals = [] →
      ∀ (P : Profile) (host : HostSemantics Nat),
        Instantiate P host S.base S.provider (Link.GC.Preparation.imports []) ⟨S.sp, S.fp, []⟩ ∧
        Instantiate P host S.base S.linked (Link.GC.Preparation.imports []) ⟨S.sl, S.fl, []⟩) ∧
    -- the specification's instantiation (`$instantiate` into a typed store `s`: segment
    -- initialisation, then the module's start function) is the instantiation phase of the
    -- game, every profile
    (∀ {s : Store Nat} {xas : List ExternAddr} {m : Module} {mt : CModuleType}
      {I : ScalarInstance} {c₀ : Config Nat},
      IsSpecInstanceAt s xas m mt I c₀ → ∀ (P : Profile) (K : Env I.E),
        ThrowsBelow K I.store.exns.length →
          (∀ host : HostSemantics Nat, Instantiate P host s m xas c₀) ∧
          instObs (I.closedSpec P c₀ K) = behavioursOf P (hostOf I.imports K) c₀ ∧
          ∀ f : I.F.Op, obsAfterInst (I.closedSpec P c₀ K) f =
            {b | ∃ s', InstantiatesTo P (hostOf I.imports K) c₀ s' ∧
              b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1}) ∧
    -- non-vacuity: a module whose start function calls an import, so that instantiation
    -- diverges against an environment that never answers ...
    (∃ (m : Module) (mt : CModuleType) (I : ScalarInstance) (c₀ : Config Nat),
      IsSpecInstance m mt I c₀ ∧ m.start.isSome ∧
        ∀ P : Profile, (I.closedSpec P c₀ (Env.silent I.E)).InstDiverges) ∧
    -- ... and a module importing a memory
    (∃ (s : Store Nat) (xas : List ExternAddr) (m : Module) (mt : CModuleType)
      (I : ScalarInstance) (c₀ : Config Nat),
      IsSpecInstanceAt s xas m mt I c₀ ∧ ∃ mty, CExternType.mem mty ∈ mt.imports) :=
  ⟨fun σ => ⟨Category.id_comp σ, Category.comp_id σ⟩,
    fun σ τ ρ => Category.assoc σ τ ρ,
    fun hσ hτ => Strategy.comp_mono hσ hτ,
    fun hI hJ => IsInstance.unique hI hJ,
    fun _ _ _ hPQ s => ScalarInstance.strategy_mono hPQ s,
    fun h P K hK f => h.adequacy_profile P K hK f,
    fun h P K hK f => ⟨ScalarInstance.forget_closedD P _ K, ScalarInstance.closedD_eq_comp P _ K,
      h.adequacy_div P K hK f⟩,
    fun _ _ _ hw K hK f => ScalarInstance.adequacy_profile hw K hK f,
    fun S hS P => S.comp_le_link hS P,
    fun S hS P => S.link_is_composition_profile hS P,
    fun S hS P => S.link_is_composition_div hS P,
    fun S hg P host => let h := S.instantiate_spec hg P host; ⟨h.1, h.2.2.2⟩,
    fun h P K hK => ⟨h.instantiate P, h.adequacy_inst P K hK,
      fun f => h.adequacy_after_inst P K hK f⟩,
    ⟨Examples.exStart, Examples.exMT, Examples.exI, Examples.exC₀,
      Examples.ex_isSpecInstance, rfl, Examples.ex_diverges⟩,
    ⟨Examples.exMemStore, Examples.exMemXas, Examples.exMem, Examples.exMemMT, Examples.exMemI,
      Examples.exMemC₀, Examples.exMem_isSpecInstanceAt, Examples.memTy,
      let ⟨_, hd⟩ := Examples.exMem_imports_mem; hd ▸ List.mem_cons_self⟩⟩

/-- **Games are a sound categorical semantics for scalar Core 3.0, deterministic profiles**
(in the fragment of the module documentation): the game category, the well-defined strategy
of a module, adequacy w.r.t. Core closed-world behaviours (including divergence as the absence
of an answer) at every well-formed store, and static linking as composition. -/
theorem games_sound_categorical_semantics :
    -- the category of signatures and strategies, ordered by refinement
    (∀ {E F : Sig.{0}} (σ : E ⟶ F), 𝟙 E ≫ σ = σ ∧ σ ≫ 𝟙 F = σ) ∧
    (∀ {E F G H : Sig.{0}} (σ : E ⟶ F) (τ : F ⟶ G) (ρ : G ⟶ H),
      (σ ≫ τ) ≫ ρ = σ ≫ (τ ≫ ρ)) ∧
    (∀ {E F G : Sig.{0}} {σ σ' : Strategy E F} {τ τ' : Strategy F G},
      σ ≤ σ' → τ ≤ τ' → σ.comp τ ≤ σ'.comp τ') ∧
    -- a module has at most one instance, hence one strategy `I.σ (profile o)`
    (∀ {m : Module} {mt : CModuleType} {I J : ScalarInstance},
      IsInstance m mt I → IsInstance m mt J → I = J) ∧
    -- adequacy for modules
    (∀ {m : Module} {mt : CModuleType} {I : ScalarInstance}, IsInstance m mt I →
      ∀ (o : GrowOracle) (K : Env I.E), ThrowsBelow K I.store.exns.length → ∀ f : I.F.Op,
        behaviours (profile o) (hostOf I.imports K) I.store (I.addr f.1) f.2.1 =
          compositeObs (K.strategy.comp (I.σ (profile o))) f) ∧
    -- adequacy at every well-formed store (later calls)
    (∀ (I : ScalarInstance) (o : GrowOracle) (s : Store Nat), I.WellFormed s →
      ∀ (K : Env I.E), ThrowsBelow K s.exns.length → ∀ f : I.F.Op,
        behaviours (profile o) (hostOf I.imports K) s (I.addr f.1) f.2.1 =
          compositeObs (K.strategy.comp (I.strategy (profile o) s)) f) ∧
    -- static linking is composition
    (∀ (S : Linking.Setup), S.Scalar → ∀ o : GrowOracle,
      S.linkedI.σ (profile o) = (S.providerI.σ (profile o)).comp (S.consumerI.σ (profile o))) :=
  ⟨fun σ => ⟨Category.id_comp σ, Category.comp_id σ⟩,
    fun σ τ ρ => Category.assoc σ τ ρ,
    fun hσ hτ => Strategy.comp_mono hσ hτ,
    fun hI hJ => IsInstance.unique hI hJ,
    fun h o K hK f => h.adequacy o K hK f,
    fun _ _ _ hw K hK f => ScalarInstance.adequacy hw K hK f,
    fun S hS o => S.link_is_composition hS o⟩

/-- **Start functions, every profile**: instances before their start function generalise
instances, adequacy of instantiation and of the export calls after it, and the game-semantic
link of modules with start functions instantiating the provider first. -/
theorem games_sound_start_profile :
    -- the start-free instances are the special case
    (∀ {m : Module} {mt : CModuleType} {I : ScalarInstance},
      IsInstanceStart m mt I none ↔ IsInstance m mt I) ∧
    -- adequacy of instantiation (the start function), divergence included
    (∀ {m : Module} {mt : CModuleType} {I : ScalarInstance} {start : Option Nat},
      IsInstanceStart m mt I start → ∀ (P : Profile) (K : Env I.E),
        ThrowsBelow K I.store.exns.length →
          instObs (I.closedInst P I.store start K) =
            startBehaviours P (hostOf I.imports K) I.store start) ∧
    -- adequacy of the export calls right after instantiation
    (∀ {m : Module} {mt : CModuleType} {I : ScalarInstance} {start : Option Nat},
      IsInstanceStart m mt I start → ∀ (P : Profile) (K : Env I.E),
        ThrowsBelow K I.store.exns.length → ∀ f : I.F.Op,
          obsAfterInst (I.closedInst P I.store start K) f =
            {b | ∃ s', StartsTo P (hostOf I.imports K) I.store start s' ∧
              b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1}) ∧
    -- linking with start functions: provider failure is reported ...
    (∀ (S : Linking.StartSetup) (P : Profile) (b : Behaviour Val),
      (∃ (c' : Config Nat) (r : Result),
        Steps P (Det.noHost : HostSemantics Nat) (startConfig S.sp S.provStart) c' ∧
        c'.code = r.toAdmin ∧ (r = .trap ∨ ∃ x, r = .throw x) ∧ b = r.toBehaviour) →
        (S.linkInst P).InstFails b) ∧
    -- ... and the link is ready only if the provider's start function may return
    (∀ (S : Linking.StartSetup) (P : Profile), (S.linkInst P).InstReady →
      ∃ sp', StartsTo P (Det.noHost : HostSemantics Nat) S.sp S.provStart sp') ∧
    -- M3 with start functions (finite plays): the linked module is the link
    (∀ (S : Linking.StartSetup) (P : Profile), S.Scalar →
      (S.linkedInstStrategy P).forget = (S.linkInst P).forget) :=
  ⟨isInstanceStart_none_iff,
    fun h P K hK => h.adequacy_inst P K hK,
    fun h P K hK f => h.adequacy_after_inst P K hK f,
    fun S _ _ h => S.linkInst_instFails h,
    fun S _ h => S.linkInst_instReady_imp h,
    fun S P hS => S.link_is_composition_inst P hS⟩

end Silmaril.Wasm.Game
