module

public import Silmaril.Wasm.Component.FXRes.Handle.Defs

/-!
# Continuations as Component Model resources: an example (definitions)

A small program over the joint system of `Silmaril.Wasm.Component.FXRes.Handle`: it creates a
continuation of function `a` (`cont.new`), hands it out as an `own<cont>` handle (`new`), takes
it back (`take`) and resumes it with no handler clauses (`resume ct []`).

* `prog a ct`: the FX code `ref.func a; cont.new ct; resume ct []`;
* `contOf a fi`: the continuation `cont.new` makes of function `a` (whose instance is `fi`);
* `start s f a ct`: the empty handle table and an FX configuration with no continuations;
* `tab₁ C`, `tab₂`: the handle table holding `C` at handle `1`, and the table after `1` is
  taken (`1` on the free stack);
* `finish s f a fi`: the final state: handle `1` dead, both store entries consumed, and the
  code the resumed continuation runs (the call of `a`, under an empty handler frame).

Theorems: `Silmaril.Wasm.Component.FXRes.Example.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Resource Silmaril.Wasm.Component.FXRes
open Silmaril.Wasm.Component.Runtime (Table)

variable {H : Type}

/-- `ref.func a; cont.new ct; resume ct []`. -/
def prog (a : ℕ) (ct : TypeIdx) : List AdminFX :=
  [.core (.ref (.func a)), .fx (.contNew ct), .fx (.resume ct [])]

/-- The continuation `cont.new` makes of function `a`. -/
def contOf (a : ℕ) (fi : FuncInst H) : ContFX :=
  ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩

/-- The initial state. -/
def start (s : Store H) (f : Frame) (a : ℕ) (ct : TypeIdx) : JState H :=
  ⟨Table.empty, ⟨s, [], f, prog a ct⟩⟩

/-- The table holding `C` at handle `1`. -/
def tab₁ (C : ContFX) : Table ContFX := ⟨#[none, some C], []⟩

/-- The table after handle `1` is taken. -/
def tab₂ : Table ContFX := ⟨#[none, none], [1]⟩

/-- The final state. -/
def finish (s : Store H) (f : Frame) (a : ℕ) (fi : FuncInst H) : JState H :=
  ⟨tab₂, ⟨s, [none, none], f,
    [.handler [] [.core (.ref (.func a)), .core (.callRefType fi.type)]]⟩⟩

end Silmaril.Wasm.Component.FXRes.Example
