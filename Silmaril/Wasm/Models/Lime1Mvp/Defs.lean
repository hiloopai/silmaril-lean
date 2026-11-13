module

public import Silmaril.Wasm.Models.Model.Thms

/-!
# `core‖S`: Core 3.0 restricted to `S`, with the canonical MVP initialisers admitted

The restricted syntax `Module.InFeat S` (`Silmaril.Wasm.Models.Syntax`) files `ref.null func` and
`ref.func f` under `refTypes`, including where Core 3.0 uses them only to spell two Wasm 1.0
module forms: the implicit null initialiser of an MVP table, and a function-index element of an
MVP element segment. So no Core module with a table is `InFeat lime1` or `InFeat v10`
(`Lime1Core.not_inFeat_lime1_of_table`). This topic amends the restriction **without changing
it**, by a normalisation that erases exactly those two initialiser forms:

* `isMvpInit e`: `e` is `[ref.null func]` or `[ref.func f]`;
* `normInit e`: `[]` on those, `e` otherwise;
* `mvpNorm m`: `normInit` on every table initialiser and every element initialiser;
* `InFeatM S m := Module.InFeat S (mvpNorm m)`, `ValidInM S m`;
* `coreModelM P H S`: the model `core‖S`, which is `coreModel P H S` with `ValidInM S` as its
  validity. Points, calls, observations and domain are those of `core|S`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.Lime1Mvp

open Silmaril.Wasm Silmaril.Wasm.Models
open Silmaril.Wasm.Numerics (Profile)

/-- The two canonical MVP initialisers: the implicit null of a `funcref` table, and a
function-index element. -/
def isMvpInit : Expr → Bool
  | [.refNull (.abstract .func)] => true
  | [.refFunc _] => true
  | _ => false

/-- Erase a canonical MVP initialiser. -/
def normInit (e : Expr) : Expr := if isMvpInit e then [] else e

/-- Erase the canonical MVP initialisers of a module's tables and element segments. -/
def mvpNorm (m : Module) : Module :=
  { m with
    tables := m.tables.map fun t => { t with init := normInit t.init }
    elems := m.elems.map fun e => { e with init := e.init.map normInit } }

/-- **A module of `S` up to the canonical MVP initialisers.** -/
def InFeatM (S : FeatureSet) (m : Module) : Prop := Module.InFeat S (mvpNorm m)

instance (S : FeatureSet) (m : Module) : Decidable (InFeatM S m) :=
  inferInstanceAs (Decidable (Module.InFeat S (mvpNorm m)))

/-- A valid module of `S` up to the canonical MVP initialisers. -/
def ValidInM (S : FeatureSet) (m : Module) : Prop :=
  Silmaril.Wasm.Validation.ModuleValid m ∧ InFeatM S m

/-- **The model `core‖S`**: `core|S` with the canonical MVP initialisers admitted. -/
def coreModelM (P : Profile) (H : Type) (S : FeatureSet) : WasmModel :=
  { coreModel P H S with Valid := ValidInM S }

end Silmaril.Wasm.Models.Lime1Mvp
