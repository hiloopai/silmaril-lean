module

public import Silmaril.Wasm.Component.Pipeline.Defs
public import Silmaril.Wasm.Component.Semantics.Defs
public meta import Silmaril.Wasm.Component.Pipeline.Defs

/-!
# A small example: two components linked by a parent

Three toy core modules: `producer` exports `get : [] → [i32]`; `consumer`
imports `get` and exports `run : [] → [i32]`; `logger` exports `log`.

* Component `A` instantiates `producer` and `logger` and exports `get` and
  `log` as component functions (`canon lift`).
* Component `B` imports a component function `get` and lowers it into a
  `consumer` instance (`canon lower`); it exports `run` (`canon lift`).
* The parent `P` instantiates `A` and `B`, wires `A.get` into `B`, and exports
  `B.run`. `A.log` is never used.

`optimizeComponent P` flattens the three core instances into one instance
graph; the consumer's import then reads `canon lower ∘ canon lift`, which
adapter fusion turns into a direct core-to-core call with a flat type check
(`u32` is trivially represented); the `logger` instance is dead and removed.
With `bool` instead of `u32` the fused adapter canonicalises (`canon`).
The checks below are executed (`#guard`) or decided by the kernel (`decide`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Example

open Silmaril.Wasm.Component
open Silmaril.Games

/-- Toy core modules. -/
inductive Toy where
  | producer | consumer | logger
  deriving Repr, DecidableEq, BEq

/-- A core function type `[] → [i32]`. -/
def coreGet : CoreFuncTy := ⟨[], [.int .i32]⟩

instance : CoreModule Toy where
  imports
    | .consumer => [("get", coreGet)]
    | _ => []
  exports
    | .producer => [("get", coreGet)]
    | .consumer => [("run", coreGet)]
    | .logger => [("log", coreGet)]

/-- The provider component, exporting a function of type `ft`. -/
def compA (ft : FuncTy) : Comp Toy :=
  .mk [] [.core .producer [], .core .logger []]
    [⟨"get", ft, ⟨[.lift ft], .call 0⟩⟩, ⟨"log", ft, ⟨[.lift ft], .call 1⟩⟩]

/-- The consumer component, importing a function of type `ft`. -/
def compB (ft : FuncTy) : Comp Toy :=
  .mk [("get", ft)] [.core .consumer [⟨[.lower ft], .call 0⟩]]
    [⟨"run", ft, ⟨[.lift ft], .call 1⟩⟩]

/-- The parent: `A.get` (environment function 0) feeds `B`. -/
def parent (ft : FuncTy) : Comp Toy :=
  .mk [] [.inst (compA ft) [], .inst (compB ft) [⟨[], .call 0⟩]]
    [⟨"run", ft, ⟨[], .call 2⟩⟩]

/-- `func() -> u32`. -/
def ftU32 : FuncTy := ⟨[], [.u32]⟩
/-- `func() -> bool`. -/
def ftBool : FuncTy := ⟨[], [.bool]⟩

-- Flattening exposes the cross-component `lower ∘ lift` pair.
#guard (flatten (parent ftU32)).nodes ==
    [(.producer, []), (.logger, []), (.consumer, [⟨[.lower ftU32, .lift ftU32], .call 0⟩])]

-- The optimised flat component: fused adapter, dead `logger` removed.
#guard (optimizeLinked (flatten (parent ftU32))).nodes ==
    [(.producer, []), (.consumer, [⟨[.flatCheck [] [.int .i32]], .call 0⟩])]

-- Its export now calls the consumer at its new index.
#guard ((optimizeLinked (flatten (parent ftU32))).exports.map (·.impl)) ==
    [⟨[.lift ftU32], .call 1⟩]

-- With `bool`, fusion keeps a canonicalisation.
#guard (optimizeLinked (flatten (parent ftBool))).nodes ==
    [(.producer, []), (.consumer, [⟨[.canon ftBool], .call 0⟩])]

-- The entry point on the nested IR.
#guard (optimizeComponent (parent ftU32)).nodes.length == 2

-- Dead export elimination: observing only `log` of `A` keeps one export, and
-- the `producer` instance becomes dead.
#guard ((optimizeProgram ⟨compA ftU32, some [1]⟩).comp.exports.map (·.impl)) ==
    [⟨[.lift ftU32], .call 0⟩]
#guard (optimizeProgram ⟨compA ftU32, some [1]⟩).comp.nodes.length == 1

-- The canonicalisation inside the fused `bool` adapter: `5` becomes `1`.
#guard (Adapter.canon ftBool).up (.flat [.i32 5]) == some (.flat [.i32 1])

/-! ## A toy core semantics -/

/-- Toy core semantics: `producer.get` answers `42`; `consumer.run` calls `get`
and answers its result plus one (trapping on anything else); `logger.log`
answers `0`. Any other `CoreSem` works equally well. -/
def toySem : CoreSem Toy where
  sem
    | .producer => Strategy.ofHandler fun _ => .pure (some (.flat [.i32 42]))
    | .consumer => Strategy.ofHandler fun _ =>
        .call ((⟨0, by decide⟩ : Fin (CoreModule.imports Toy.consumer).length), .flat [])
          fun (r : Option Payload) => match r with
          | some (.flat [⟨.int .i32, x⟩]) =>
            .pure (some (.flat [.i32 (BitVec.ofNat 32 (x.toNat + 1))]))
          | _ => .pure none
    | .logger => Strategy.ofHandler fun _ => .pure (some (.flat [.i32 0]))

end Silmaril.Wasm.Component.Example
