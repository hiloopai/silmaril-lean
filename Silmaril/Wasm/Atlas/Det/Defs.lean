module

public import Silmaril.Wasm.Atlas.Core.Defs
public import Silmaril.Wasm.Det.Core.Defs

/-!
# The determinism chart

The deterministic subcategory of Core (`Silmaril.Wasm.Det.Core`): stores whose every function is
deterministic modulo traps and imports (`DetFn`), against an oracle host `oracleHost F` (the
host answering `F h args` and leaving the store unchanged). The observations are the Core ones;
the chart is a restriction of the Core chart (`Det.toCore`, equal on every sentence). Its
strength is `Det.unique`/`Det.always_of_may` (in `Thms`): one terminating, non-trapping
observation of a typed call is the only one, so a single test run decides the call's
terminating behaviour.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Det

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core (DetFn oracleHost)

/-- The determinism domain: every function of the store is `DetFn`. -/
def Dom (P : Profile) (s : Store Nat) : Prop := ∀ a, DetFn P s a

/-- **The determinism chart** at profile `P` against the oracle `F`. -/
def chart (P : Profile) (F : Nat → List Val → Result) : Chart :=
  BChart (Store Nat) Core.Call (Behaviour Val) (Dom P)
    (fun s c => behaviours P (oracleHost F) s c.1 c.2)

end Silmaril.Wasm.Atlas.Det
