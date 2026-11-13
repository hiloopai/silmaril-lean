module

public import Silmaril.Wasm.Category.Institution.Defs
public import Silmaril.Wasm.Binaryen.ArbitraryProfileCompiler
public import Silmaril.Wasm.Binaryen.Pipeline.Thms

@[expose] public section

/-!
# Core 3.0 and Binaryen IR modules as languages of export sessions

The first two objects of the category of Wasm programs, both observed through the Core 3.0
operational semantics `Execution.Core.Step P host` at an **arbitrary** profile `P` and host
relation `host`:

* `coreSession P host`: Core 3.0 modules. An observation is the admissibility of an
  instantiation (`Instantiate P host s m xas c` in a valid store `s` with imports `xas`) or the
  trace of an export session (`moduleObs P host s xas m script`: instantiation, then a script of
  named export invocations sharing the store), with the initial store, imports and script
  recorded. These are exactly the observations of silmaril-lean's `ExportRefines`/
  `ExportEquiv` (`Silmaril.Wasm.Binaryen.Equiv`).
* `birSession P host`: Binaryen IR modules (`BModule`), observed through their lowering; this
  is silmaril-lean's `Exe.CompilerPass.exportLanguage P host`, reused.

Morphisms between them (`lowerR`, `liftR`: realisers, hence valid compilers and comorphisms of
the behavioural institutions) and the round trip `roundTrip` between the validated variants
`coreValid`/`birValid`, through which every Binaryen IR optimization conjugates to a Core
optimization (`coreEndo`). The optimizations: silmaril-lean's exact arbitrary-profile passes
(`ArbitraryProfile.EquivPass`, as endomorphisms `ArbitraryProfile.Compiler.ofEquivPass`) and
Silmaril's every-profile stages (`extraEndo`, from `Silmaril.Wasm.Binaryen.extraSelectedP`).

Nothing here is new semantics: the observation sets are silmaril-lean's, and soundness of each
optimization is its `ExportEquiv` contract.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Wasm Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type}

/-- **Core 3.0 modules observed by export sessions**, at profile `P` and host `host`: the
admissibility of instantiation and the traces of export sessions, in every valid store and
import list. -/
abbrev coreSession (P : Profile) (host : HostSemantics H) : Language.{0} where
  Iface := Unit
  Prog := Module
  iface _ := ()
  Obs := Exe.CompilerPass.Observation H
  beh m := {observation | match observation with
    | .instantiates store imports =>
      StoreOk store ∧ ∃ c, Instantiate P host store m imports c
    | .session store imports script outcomes =>
      StoreOk store ∧ outcomes ∈ moduleObs P host store imports m script}

/-- **Binaryen IR modules observed by export sessions** of their lowering (silmaril-lean's
`exportLanguage`). -/
abbrev birSession (P : Profile) (host : HostSemantics H) : Language.{0} :=
  Exe.CompilerPass.exportLanguage P host

/-- Validated Core modules. -/
abbrev coreValid (P : Profile) (host : HostSemantics H) : Language.{0} :=
  (coreSession P host).onInvariant PassAPI.CoreOk

/-- Validated Binaryen IR modules; for the closed host this is silmaril-lean's
`ArbitraryProfile.Compiler.language`. -/
abbrev birValid (P : Profile) (host : HostSemantics H) : Language.{0} :=
  (birSession P host).onInvariant BModule.Ok

theorem birValid_closedHost (P : Profile) :
    birValid P (closedHost (H := H)) = ArbitraryProfile.Compiler.language P H := rfl

variable (P : Profile) (host : HostSemantics H)

/-- **Lowering realises Binaryen IR in Core**: a Binaryen module means its lowering
(definitionally). -/
def lowerR : Realiser (birSession P host) (coreSession P host) where
  Φ := id
  prog := BModule.lower
  g := id
  g_injective := Function.injective_id
  iface _ := rfl
  beh _ := by exact Set.image_id _

/-- A lifted module has the observations of the original (`lower_lift`). -/
theorem beh_lift (m : Module) :
    (birSession P host).beh (BModule.lift m) = (coreSession P host).beh m :=
  congrArg (coreSession P host).beh (lower_lift m)

/-- **Lifting realises Core in Binaryen IR** (`lower_lift`). -/
def liftR : Realiser (coreSession P host) (birSession P host) where
  Φ := id
  prog := BModule.lift
  g := id
  g_injective := Function.injective_id
  iface _ := rfl
  beh m := (Set.image_id _).trans (beh_lift P host m)

/-- Lowering on validated modules. -/
def lowerValidR : Realiser (birValid P host) (coreValid P host) where
  Φ := id
  prog m := ⟨m.val.lower, m.property⟩
  g := id
  g_injective := Function.injective_id
  iface _ := rfl
  beh _ := by exact Set.image_id _

/-- Lifting preserves validity. -/
theorem lift_ok (m : Module) (h : PassAPI.CoreOk m) : BModule.Ok (BModule.lift m) := by
  unfold BModule.Ok
  rw [lower_lift]
  exact h

/-- Lifting on validated modules. -/
def liftValidR : Realiser (coreValid P host) (birValid P host) where
  Φ := id
  prog m := ⟨BModule.lift (m.val : Module), lift_ok m.val m.property⟩
  g := id
  g_injective := Function.injective_id
  iface _ := rfl
  beh m := (Set.image_id _).trans (beh_lift P host m.val)

/-- **The round trip Core ⇄ Binaryen IR** (validated modules): lifting then lowering is the
identity convention. -/
def roundTrip : RoundTrip (coreValid P host) (birValid P host) where
  lift := (liftValidR P host).pass
  lower := (lowerValidR P host).pass
  le_id := ⟨rfl, by
    rintro o o'' ⟨o', h₁, h₂⟩
    have e₁ : o = o' := h₁
    have e₂ : o' = o'' := h₂
    exact e₁.trans e₂⟩

/-- **A Binaryen IR optimization as a Core optimization**, conjugated by the round trip. -/
def coreEndo (E : EndoPass (birValid P host)) : EndoPass (coreValid P host) :=
  (roundTrip P host).endo E

/-- The conjugated optimization lifts, optimizes and lowers. -/
theorem coreEndo_run (E : EndoPass (birValid P host)) (m : (coreValid P host).Prog) :
    ((coreEndo P host E).run m).val =
      (E.run ((liftValidR P host).prog m)).val.lower := rfl

/-- Silmaril's every-profile Binaryen stages (`neutral-ops`, `eqz-pair`, `tee-form`, `rse-line`,
`drop-get` and the selected silmaril stages), iterated, as a Binaryen IR optimization at an
arbitrary profile. -/
def extraEndo (stages : List Silmaril.Wasm.Binaryen.Pipeline.ExtraStage)
    (h : ∀ s ∈ stages, s.anyProfile = true) (rounds : Nat) :
    EndoPass (birValid P (closedHost (H := H))) :=
  ArbitraryProfile.Compiler.ofEquivPass (Silmaril.Wasm.Binaryen.Pipeline.extraSelectedP P stages h ^ rounds)

end Silmaril.Wasm.Category
