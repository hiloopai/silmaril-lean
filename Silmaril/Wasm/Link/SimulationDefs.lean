module

public import Silmaril.Wasm.Link.AdminScope
public import Silmaril.Wasm.Link.ControlInversion
public import Silmaril.Wasm.SingleThreaded.Determinism.Head

/-! # Invariants for linked core execution

The mode of the current frame stays fixed during a step. Nested call frames
carry their own modes through `AdminRelation.Control`. Source typing supplies
the annotation scopes needed when those frames enter actual stored bodies.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.Simulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open AdminRelation

abbrev noHost {H : Type} : HostSemantics H := SingleThreaded.Det.noHost

structure Matching {H : Type} (mode : Mode) (source target : Config H) : Prop where
  stores : StoreRelation.Related source.store target.store
  frames : Frames mode source.frame target.frame
  code : Control mode source.frame.module target.frame.module source.code target.code

def FunctionScopes {H : Type} (s : Store H) : Prop :=
  ∀ {address : Nat} {fi : FuncInst H} {code : Func}, s.funcs[address]? = some fi →
    fi.code = .wasm code → CodeScope.Instructions fi.module.types.length code.body

theorem function_scopes {H : Type} {s : Store H} (valid : StoreOk s) : FunctionScopes s :=
  fun lookup wasm => CodeScope.store_scope valid lookup wasm

theorem frame_module {H : Type} {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (step : Step P host c c') : c'.frame.module = c.frame.module := step.frame_module

end Silmaril.Wasm.Link.GC.Simulation
