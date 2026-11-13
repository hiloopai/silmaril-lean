module

public import Silmaril.Wasm.Jco.Thin.Thms

/-!
# Thin-wrapper recognition: examples

A world `adder` imports `log : func(x : u32)` and exports
`add : func(a : u32, b : u32) -> u32`. Three toy core modules:

* `plainAdder` exports `add : [i32 i32] → [i32]` and imports `log : [i32] → []`:
  it follows the FFI pattern in the `plain` style, not in the `cm32p2` style;
* `mangledAdder` is the same module with `cm32p2` names: it follows the
  pattern in the `cm32p2` style only; both give the same plan;
* `wideAdder` exports `add : [i64 i64] → [i64]`: no style recognizes it (an
  adaptor is needed).

The recognitions are decided by the kernel (`decide`). The last theorem is
the agreement of the thin wrapper with the identity adaptor, at `plainAdder`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Thin.Example

open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco.Thin

/-- Toy core modules. -/
inductive Toy where
  | plainAdder | mangledAdder | wideAdder
  deriving Repr, DecidableEq

/-- `[i32 i32] → [i32]`. -/
def add32 : CoreFuncTy := ⟨[.int .i32, .int .i32], [.int .i32]⟩
/-- `[i64 i64] → [i64]`. -/
def add64 : CoreFuncTy := ⟨[.int .i64, .int .i64], [.int .i64]⟩
/-- `[i32] → []`. -/
def log32 : CoreFuncTy := ⟨[.int .i32], []⟩

instance : CoreModule Toy where
  imports
    | .mangledAdder => [("cm32p2|log", log32)]
    | _ => [("log", log32)]
  exports
    | .plainAdder => [("memory-free", ⟨[], []⟩), ("add", add32)]
    | .mangledAdder => [("cm32p2||add", add32)]
    | .wideAdder => [("add", add64)]

/-- The world. -/
def adder : World :=
  ⟨[("log", ⟨[.u32], []⟩)], [("add", ⟨[.u32, .u32], [.u32]⟩)]⟩

theorem plain_plainAdder :
    recognize .plain adder (CoreModule.imports Toy.plainAdder)
      (CoreModule.exports Toy.plainAdder) = some ⟨[0], [1]⟩ := by decide

theorem cm32p2_plainAdder :
    recognize .cm32p2 adder (CoreModule.imports Toy.plainAdder)
      (CoreModule.exports Toy.plainAdder) = none := by decide

theorem cm32p2_mangledAdder :
    recognize .cm32p2 adder (CoreModule.imports Toy.mangledAdder)
      (CoreModule.exports Toy.mangledAdder) = some ⟨[0], [0]⟩ := by decide

theorem plain_mangledAdder :
    recognize .plain adder (CoreModule.imports Toy.mangledAdder)
      (CoreModule.exports Toy.mangledAdder) = none := by decide

theorem plain_wideAdder :
    recognize .plain adder (CoreModule.imports Toy.wideAdder)
      (CoreModule.exports Toy.wideAdder) = none := by decide

theorem cm32p2_wideAdder :
    recognize .cm32p2 adder (CoreModule.imports Toy.wideAdder)
      (CoreModule.exports Toy.wideAdder) = none := by decide

/-- The thin wrapper of `plainAdder`. -/
theorem thinWrap_plainAdder :
    thinWrap? .plain adder Toy.plainAdder =
      some (.mk adder.imports [.core .plainAdder [⟨[.lower ⟨[.u32], []⟩], .call 0⟩]]
        [⟨"add", ⟨[.u32, .u32], [.u32]⟩, ⟨[.lift ⟨[.u32, .u32], [.u32]⟩], .call 2⟩⟩]) := by
  simp only [thinWrap?, plain_plainAdder, Option.map_some]
  rfl

/-- The identity adaptor is behaviourally the identity at `plainAdder`. -/
theorem plainAdder_agree (C : CoreSem Toy) :
    (wrapGlue .plain adder Toy.plainAdder (importWiring adder ⟨[0], [1]⟩)
        (Plan.glue ⟨[0], [1]⟩)).denU C =
      (thin adder Toy.plainAdder ⟨[0], [1]⟩).denU C :=
  denU_wrapGlue_glue C .plain adder Toy.plainAdder ⟨[0], [1]⟩

end Silmaril.Wasm.Jco.Thin.Example
