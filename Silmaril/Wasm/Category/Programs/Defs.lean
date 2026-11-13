module

public import Silmaril.Wasm.Category.Session.Thms
public import Silmaril.Wasm.Category.Closed.Thms
public import Silmaril.Wasm.Category.Linking.Thms
public import Silmaril.Wasm.Category.Generic.Defs
public import Silmaril.Wasm.Category.Component.Thms
public import Silmaril.Wasm.Category.LinkSat.Thms
public import Silmaril.Wasm.Category.Exec.Thms
public import Silmaril.Wasm.Category.Spec.Thms
public import Silmaril.Wasm.Category.Programs.SSA.Thms
public import Mathlib.CategoryTheory.InducedCategory

@[expose] public section

/-!
# The category of Wasm programs

**Entry point.** The category of Wasm programs at an arbitrary silmaril profile `P` and host
relation `host` is the full subcategory `WasmProg P host` of silmaril-lean's category of
compilers (`Silmaril.Compile.Category.CompCat`) on the Wasm languages below. The `core`/`bir`
session objects and their validated variants use Core 3.0 `Execution.Core.Step P host`;
other objects use environment-derived
hosts, the closed host, SSA outcomes or strategy plays as specified by `lang`. The profile
is arbitrary, with no general determinism assumption.

## Objects (`WasmObj`, `lang P host`)

| Object | Programs | Observations |
|---|---|---|
| `core` | Core 3.0 modules | instantiation admissibility and export-session traces under `host` (`coreSession`) |
| `bir` | Binaryen IR modules | the same, of their lowering (silmaril-lean's `exportLanguage`) |
| `coreValid`, `birValid` | validated modules | the same |
| `module` | Core 3.0 modules | closed-world behaviours of their scalar instance against environments (`modLang`) |
| `inst` | well-formed scalar instances | Core 3.0 behaviours of export calls against environments (`instLang`) |
| `game` | divergence-observing strategies | observations of their composite with environments (`dgameLang`) |
| `coreComp` | numeric Core 3.0 instances as core modules of the component IR | plays of their component strategy (`modCompLang (Reference.core3Sem P)`) |
| `component` | components over Core 3.0 instances | plays of their strategy over `sigU` (`compLang (Reference.core3Sem P)`) |
| `envSession` | Core 3.0 modules | export sessions under `hostOf ts K`, for every environment `K` (`envSession`) |
| `spec`, `specValid` | (spec-instantiable) Core 3.0 modules | instantiation behaviour of `$instantiate` and export calls after it, against environments (`specLang`) |
| `closedGame` | environment-indexed closed strategies with an instantiation phase | `instObs`, `obsAfterInst` (`closedGameLang`) |
| `ssa` | lambda-SSA functions over Wasm integer primitives (`Silmaril.Wasm.SSA.SFunc`) | typed arguments with the call outcome, or none (`ssaLang`) |
| `coreFn` | closed Core 3.0 function instances (store, address, signature) | Core 3.0 behaviours of typed invocations, closed host, at `P` (`coreFnLang P`) |

The component objects use the core semantics `Silmaril.Wasm.Component.Reference.core3Sem P`:
the Core 3.0 strategy of each numeric core instance between canonical-ABI boundary adapters.
They are connected to each other (`wrap`, the component optimiser) but not to the other
objects: the faithfulness of the adapters is not proved.

## Morphisms

Morphisms are compilers: a convention (interface map and observation matching) and a partial
translation every success of which is a valid compilation (target behaviours realise source
behaviours). Named morphisms (`WasmProg.lower`, …): lowering and lifting between Core and
Binaryen IR (exact), instantiation of scalar modules (exact on instantiable modules), and
**the semantic map `denote : inst ⟶ game`** (`I ↦ I.dstrategy P I.store`, exact by adequacy);
wrapping a core instance as a component (exact), the component optimiser; **the compilation
of lambda-SSA functions to Core 3.0 `ssaToCore : ssa ⟶ coreFn`** (exact through its convention,
by `Silmaril.Wasm.SSA.compileCore_spec`, which rests on `Silmaril.Wasm.Interp.native_adequacy`) and the
lambda-SSA optimiser `ssaOptimize` as an endomorphism of `ssa`; every
optimization `EndoPass` of an object is an endomorphism (`WasmProg.endo`), in particular
silmaril-lean's and Silmaril's Binaryen passes and their conjugates on Core modules
(`Silmaril.Wasm.Category.coreEndo`).

## Functors

* `WasmProg.toCompCat`: the inclusion into the category of compilers; `WasmProg.toRel`: valid
  compilation relations (`graphFunctor`); `WasmProg.toConv`: conventions.
* **The semantics functor into games**: `sem P : Paths WObj ⥤ Sig.{0}` (`Silmaril.Wasm.Category.Linking`)
  from the free category on scalar instances into `Silmaril.Games`' category of signatures and
  strategies; static linking is composition (`Linking.Setup.sem_link`). Its
  divergence-observing version `dsem P : Paths WObj ⥤ DSig.{0}` forgets to it (`dsem_forget`).
  The `game` object is the closed-world reading of the morphisms of `DSig`.

## Institutions

Each object `X` induces its behavioural institution `WasmProg.inst X = behInst (lang P host X)`,
built with Silmaril's `ObsSemantics` construction (`Silmaril.Wasm.Institution.Generic`). A `Realiser`
packages a total program translation with exact observations through an injective read-back
map, giving a compiler and a comorphism (`Realiser.coHom`). Borrowing entailment additionally
requires that read-back map to be surjective (`Realiser.entails_iff`); exactness through an
arbitrary convention alone does not supply these data. The game-semantic logics and the Hets
graphs of `Silmaril.Wasm.Institution` (`Games`, `DivGames`, `CompGraph`) are unchanged and remain the logic
graph of the game and component nodes. Play properties transport along linking by corridors,
one per fixed partner (`Silmaril.Wasm.Category.LinkSat`: `linkCorridorA`, `linked_satA_iff`).

## Generic pieces

Round trips compose (`roundTripTrans`), projections to conventions (`compForget`,
`relForget`, `fibreOrderIso`), dialects (`Dialect`), execution semantics with relational
cofunctors and backward/forward simulations (`Exec`, `RelCofunctor`, `BackwardSim`,
`ForwardSim`), and realisers (`Realiser`) are in `Silmaril.Wasm.Category.{Generic,Exec,Institution}`.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

/-- The objects of the category of Wasm programs. -/
inductive WasmObj : Type
  /-- Core 3.0 modules, export sessions. -/
  | core
  /-- Binaryen IR modules, export sessions. -/
  | bir
  /-- Validated Core 3.0 modules, export sessions. -/
  | coreValid
  /-- Validated Binaryen IR modules, export sessions. -/
  | birValid
  /-- Scalar Core 3.0 modules, closed-world observations. -/
  | module
  /-- Well-formed scalar instances, closed-world observations. -/
  | inst
  /-- Divergence-observing strategies, closed-world observations. -/
  | game
  /-- Scalar instances as core modules of the component IR. -/
  | coreComp
  /-- Components over Core 3.0 instances. -/
  | component
  /-- Core 3.0 modules, export sessions against environments. -/
  | envSession
  /-- Core 3.0 modules instantiated by the specification, closed-world observations. -/
  | spec
  /-- Spec-instantiable Core 3.0 modules. -/
  | specValid
  /-- Closed games with an instantiation phase. -/
  | closedGame
  /-- Lambda-SSA functions over Wasm integer primitives. -/
  | ssa
  /-- Closed Core 3.0 function instances. -/
  | coreFn
  deriving DecidableEq

variable {H : Type}

/-- The language of an object. -/
noncomputable def lang (P : Profile) (host : HostSemantics H) : WasmObj → Language.{0}
  | .core => coreSession P host
  | .bir => birSession P host
  | .coreValid => coreValid P host
  | .birValid => birValid P host
  | .module => modLang P
  | .inst => instLang P
  | .game => dgameLang
  | .coreComp => modCompLang (Silmaril.Wasm.Component.Reference.core3Sem P)
  | .component => compLang (Silmaril.Wasm.Component.Reference.core3Sem P)
  | .envSession => envSession P
  | .spec => specLang P
  | .specValid => (specLang P).onInvariant SpecInstantiable
  | .closedGame => closedGameLang
  | .ssa => ssaLang
  | .coreFn => coreFnLang P

/-- **The category of Wasm programs**: the full subcategory of the category of compilers on
the Wasm languages. -/
def WasmProg (P : Profile) (host : HostSemantics H) : Type :=
  InducedCategory CompCat.{0} fun X : WasmObj => CompCat.of (lang P host X)

noncomputable instance (P : Profile) (host : HostSemantics H) : Category (WasmProg P host) :=
  inferInstanceAs (Category (InducedCategory CompCat.{0} fun X : WasmObj => CompCat.of (lang P host X)))

namespace WasmProg

variable (P : Profile) (host : HostSemantics H)

/-- An object of the category of Wasm programs. -/
def of (X : WasmObj) : WasmProg P host := X

/-- The inclusion into the category of compilers. -/
noncomputable def toCompCat : WasmProg P host ⥤ CompCat.{0} :=
  inducedFunctor fun X : WasmObj => CompCat.of (lang P host X)

/-- Valid compilation relations. -/
noncomputable def toRel : WasmProg P host ⥤ RelCat.{0} := toCompCat P host ⋙ graphFunctor

/-- Conventions. -/
noncomputable def toConv : WasmProg P host ⥤ Language.{0} := toCompCat P host ⋙ compForget

/-- A compiler between the languages of two objects as a morphism. -/
noncomputable def hom {X Y : WasmObj} (C : Compiler (lang P host X) (lang P host Y)) :
    of P host X ⟶ of P host Y :=
  InducedCategory.homMk C

/-- Lowering Binaryen IR to Core. -/
noncomputable def lower : of P host .bir ⟶ of P host .core := hom P host (lowerR P host).compiler

/-- Lifting Core to Binaryen IR. -/
noncomputable def lift : of P host .core ⟶ of P host .bir := hom P host (liftR P host).compiler

/-- Lowering validated modules. -/
noncomputable def lowerValid : of P host .birValid ⟶ of P host .coreValid :=
  hom P host (lowerValidR P host).compiler

/-- Lifting validated modules. -/
noncomputable def liftValid : of P host .coreValid ⟶ of P host .birValid :=
  hom P host (liftValidR P host).compiler

/-- Instantiation of scalar modules. -/
noncomputable def instantiate : of P host .module ⟶ of P host .inst :=
  hom P host (Silmaril.Wasm.Category.instantiate P)

/-- **The semantic map into games.** -/
noncomputable def denote : of P host .inst ⟶ of P host .game := hom P host (denoteR P).compiler

/-- Wrapping a core instance as a component. -/
noncomputable def wrap : of P host .coreComp ⟶ of P host .component :=
  hom P host (wrapR (Silmaril.Wasm.Component.Reference.core3Sem P)).compiler

/-- The component optimiser. -/
noncomputable def optimizeComponent : of P host .component ⟶ of P host .component :=
  hom P host (optimizeEndo (Silmaril.Wasm.Component.Reference.core3Sem P)).toPass.toCompiler

/-- **The session ↔ closed-world edge**: spec observations are matched by sessions. -/
noncomputable def sessionToSpec : of P host .envSession ⟶ of P host .spec :=
  hom P host (Silmaril.Wasm.Category.sessionToSpec P)

/-- Forgetting spec-instantiability. -/
noncomputable def forgetSpec : of P host .specValid ⟶ of P host .spec :=
  hom P host ⟨⟨id, fun o o' => o = o'⟩, fun m => some m.val, fun m m' h => by
    have e : m.val = m' := Option.some.inj h
    subst e
    exact (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ⟨o, ho, rfl⟩⟩⟩

/-- **Spec-instantiated modules to closed games** (exact). -/
noncomputable def denoteSpec : of P host .specValid ⟶ of P host .closedGame :=
  hom P host (specDenoteR P).compiler

/-- **Lambda-SSA functions compiled to Core 3.0** (exact through the convention). -/
noncomputable def ssaToCore : of P host .ssa ⟶ of P host .coreFn :=
  hom P host (Silmaril.Wasm.Category.ssaToCore P)

/-- The lambda-SSA optimiser. -/
noncomputable def ssaOptimize : of P host .ssa ⟶ of P host .ssa :=
  hom P host Silmaril.Wasm.Category.ssaOptimize.toPass.toCompiler

/-- An optimization of an object as an endomorphism. -/
noncomputable def endo {X : WasmObj} (E : EndoPass (lang P host X)) : of P host X ⟶ of P host X :=
  hom P host E.toPass.toCompiler

/-- The behavioural institution of an object. -/
noncomputable abbrev inst (X : WasmObj) : Silmaril.Inst.Institution₁ :=
  behInst (lang P host X)

end WasmProg

end Silmaril.Wasm.Category
