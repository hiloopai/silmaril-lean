module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionObj.Defs

/-!
# A concrete pair separating the open session object from the reference equivalence: definitions

**Scope.** Two concrete `HLinked2` values (`HLinkedSession.Defs`) with the same exporter, the same
export and host-import types, and importers that differ in one constant of their core code. They
are the witness that the open object `HLinked2.compSessionO` (`HLinkedSessionObj.Defs`, every
legal host answer an Opponent move) distinguishes components that the reference equivalence
`HLinked2.RefSessEquivFull` (typed deterministic stateful hosts) identifies.

## The importer `sepI c`

The core module `sepCore c` imports one host function `env.h : [] -> []` (function `0`), has one
mutable global `g` (initially `0`) and exports `f : [] -> [i32]` (function `1`), with body

`global.get 0; i32.const c; global.set 0; call 0; i32.const 0; global.set 0`:

it reads `g`, writes `g := c`, calls the host import `h`, writes `g := 0`, and returns the value
it read. If `h` is refused (a trap answer), the call traps right after `g := c`, and the core
store keeps `g = c` for the next call (a trapped export call keeps its store). The component
`sepI c` lowers the component import `h : func()` into `env.h` and lifts `f` as
`f : func() -> u32`.

## The linked components

`sepL c : HLinked2 := ⟨setGetS, sepI c, [], hostIface⟩`: the exporter is #697's `setGetS`
(`LinkedSession.Defs`), wired to nothing; the importer's only import is the host import
`h : func()` of the parent (`LinkedSession.hostIface`). The pair is

* `forgetL := sepL 0`: `g` is always `0`, so `f` answers `0` whenever `h` is answered;
* `rememberL := sepL 1`: `f` answers `1` exactly when the previous call of `f` was refused in `h`
  (a trap, leaving `g = 1`) and this call of `h` is answered.

The distinguishing play, a refusal of the host call `h()` followed by an answer of the same call
with no answered call in between, is legal on the open interface but no deterministic host
produces it (`HLinked2.not_hostRun_refuse_answer`); `Thms` proves the separation.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.HLinkedSep

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.LinkedSession (setGetS unitTy u32Ty unitFlat i32Flat
  unitI32Types hostIface)

/-- The importer's core module: `(import "env" "h" (func (type 0)))
(global (mut i32) (i32.const 0))
(func (type 1) global.get 0 i32.const c global.set 0 call 0 i32.const 0 global.set 0)
(export "f" (func 1))`. -/
def sepCore (c : BitVec 32) : Silmaril.Wasm.Module where
  types := unitI32Types
  imports := [⟨"env", "h", .func ⟨0⟩⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨1⟩, [], [.globalGet ⟨0⟩, .intConst .i32 c, .globalSet ⟨0⟩, .call ⟨0⟩,
    .intConst .i32 0, .globalSet ⟨0⟩]⟩]
  exports := [⟨"f", .func ⟨1⟩⟩]

/-- **The importer**: the host import `h: func()` lowered into `env.h`, and the export
`f: func() -> u32` lifted from core export `0`. -/
def sepI (c : BitVec 32) : SimpleI :=
  ⟨⟨sepCore c, [("h", unitFlat)], [("f", i32Flat)]⟩, [("h", unitTy)], [⟨"f", u32Ty, 0⟩]⟩

/-- **The linked component**: the exporter `setGetS`, wired to nothing; the importer's import
`h` is the parent's host import. -/
def sepL (c : BitVec 32) : HLinked2 := ⟨setGetS, sepI c, [], hostIface⟩

/-- **The forgetful component**: `f` answers `0` whenever its host call is answered. -/
def forgetL : HLinked2 := sepL 0

/-- **The remembering component**: `f` answers `1` after a refused call of `h` when `h` is then
answered. -/
def rememberL : HLinked2 := sepL 1

end Silmaril.Wasm.Component.Reference.HLinkedSep
