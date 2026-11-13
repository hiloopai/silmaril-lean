module

public import Silmaril.Wasm.Component.Param.Defs

/-!
# The reference-machine half over any engine: definitions

`refToSpec_of_arity` (`Silmaril.Wasm.Component.Reference`) is a symbolic execution of the reference
component machine over the Core 3.0 engine `core3P P`, and `Param.Core3R` re-runs it over
`core3R P V I`. Both rely on the engine having Core 3.0's stores, threads and `prepare?`. This
module isolates what the symbolic execution needs of an engine `E`, for one simple component `c`
and a core module map `ofCore`:

* `InstFacts E ofCore c cs ci addr` (**the instantiation facts**): the module `ofCore c.mod.mod`
  has no import types, `E.prepare?` instantiates it in the empty store (at the machine's host
  type `CanonHost E`) to the core store `cs` and core instance `ci` without a start function,
  and every lifted export `x` finds its core export by name, a function at address
  `addr x.core`;
* `RunFacts E cs a xs rts Out Div` (**the run facts** of the core activation of an export at
  address `a` on the flat values `xs`): every engine run from `(cs, E.invoke a xs)` never reaches
  a callout, a returned run gives values of the flat types `rts` that are an outcome `some ys`
  of `Out`, a trapping run gives the outcome `none` of `Out`, and divergence gives `Div`.

The theorems (`Silmaril.Wasm.Component.EngineRef.Thms`) re-run the instantiation and call phases of
`refToSpec_of_arity` over every engine from these facts.

* `specOut x Out Div`: the outcomes of a call of export `x` whose core activation has the outcomes
  `Out` and may diverge when `Div`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.EngineRef

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable (E : Engine)

/-- The name of the core export lifted by `x`. -/
def coreNameE (m : NumModule) (x : SimpleExport) : String :=
  ((m.exports[x.core]?).map (·.1)).getD ""

/-- **The instantiation facts** of `c` over `E`. -/
structure InstFacts (ofCore : Silmaril.Wasm.Module → E.Module) (c : Simple)
    (cs : E.Store (CanonHost E)) (ci : E.Inst) (addr : Nat → E.FuncAddr) : Prop where
  /-- The module has no import types. -/
  imports : E.importTypes (ofCore c.mod.mod) = []
  /-- It is prepared in the empty store, without a start function. -/
  prepare : E.prepare? (E.empty _) (ofCore c.mod.mod) [] = some (cs, ci, none)
  /-- Every lifted export finds a function export of the core instance. -/
  lookup : ∀ x ∈ c.exports, ∃ v, (E.exports ci).lookup (coreNameE c.mod x) = some v ∧
    E.asFunc? v = some (addr x.core)

/-- **The run facts** of the core activation of the function at `a` on `xs` from `cs`. -/
structure RunFacts {H : Type} (cs : E.Store H) (a : E.FuncAddr) (xs : List Flat)
    (rts : List Silmaril.Wasm.NumType) (Out : Set (Option (List Flat))) (Div : Prop) : Prop where
  /-- No run reaches a callout. -/
  no_callout : ∀ {s' t'} (h : H) (args : List Flat),
    CoreEngine.Steps E (cs, E.invoke a xs) (s', t') → E.status s' t' ≠ .callout h args
  /-- Returned values have the types `rts` and are an outcome. -/
  values : ∀ {s' t'} (ys : List Flat), CoreEngine.Steps E (cs, E.invoke a xs) (s', t') →
    E.status s' t' = .returned (.values ys) → some ys ∈ Out ∧ ys.map (·.type) = rts
  /-- A trap is the outcome `none`. -/
  trap : ∀ {s' t'}, CoreEngine.Steps E (cs, E.invoke a xs) (s', t') →
    E.status s' t' = .returned .trap → none ∈ Out
  /-- Divergence is allowed only when `Div`. -/
  diverges : CoreEngine.Diverges E (cs, E.invoke a xs) → Div

/-- The outcomes of a call of export `x` whose core activation has outcomes `Out` and may
diverge when `Div`. -/
def specOut (x : SimpleExport) (Out : Set (Option (List Flat))) (Div : Prop) : Set Reference.Outcome :=
  {b | ∃ r ∈ Out, b = liftOutcome x.ty r} ∪ {b | b = .diverges ∧ Div}

end Silmaril.Wasm.Component.EngineRef
