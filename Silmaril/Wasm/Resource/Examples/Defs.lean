module

public import Silmaril.Wasm.Resource.Check.Defs
public import Silmaril.Wasm.Resource.Extern.Defs
public import Silmaril.Wasm.Resource.Component.Defs
public import Silmaril.Wasm.Spec.Litmus.Defs

@[expose] public section

/-!
# Resource protocols: examples

**Loose traces** (litmus programs of `Silmaril.Wasm.Spec.Litmus`: the prefixes of one trace), on the
interface `Xh` with imports `alloc` (0), `use` (1), `free` (2) and exports `a`, `b`, `c`:

* `sessionsRun`: `alloc` in the call of `a`, `use` in the call of `b`, `free` in the call of `c`
  (three export calls, one handle `5`); `uafRun` (use after free), `doubleFreeRun`,
  `freeNeverRun` (free of a never-allocated handle), `envReuseRun` (the environment allocates a
  live handle again: its fault, so a later bad free is not the program's).
* Provider traces on `Xp` (exports `alloc`, `use`, `free`): `provRun` (allocate, use, free, allocate
  the same handle again), `provTwiceRun` (the same live handle allocated twice), `provClientBad`
  (the client frees a dead handle: its fault).
* Ownership on `Xo` (imports `alloc`, `use`, `drop`, `consume`; exports `run` with a borrowed
  argument, `keep` with an owned one): `borrowRun`, `dropBorrowRun` (a borrowed handle dropped),
  `outliveRun` (a borrowed handle used after its call returned), `giveRun` (ownership transfer, then
  use: rejected), `transferRun` (ownership taken from `keep`, used and dropped in `run`).
* `externref` handles on untyped moves (`Silmaril.Wasm.Game.Untyped`): `exRun` (the reference
  `ref.extern (host 7)` allocated, used, freed), `exUafRun`.
* Components: `Silmaril.Wasm.Spec.Component.Litmus.handleRun`/`useAfterDrop` through `nudProto`.

**Real Core 3.0 modules** (imports `alloc : [] → [i32]`, `use : [i32] → []`, `free : [i32] → []`,
export `run : [] → []`):

* `cliUseBefore`: `run` calls `use(7)` before any allocation; `cliFreeNever`: `run` calls
  `free(7)`; `cliAllocOnly`: `run` allocates and drops the handle, a dead function calls
  `use`/`free`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.Examples

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Litmus Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-! ## Loose client traces -/

/-- Imports `alloc`, `use`, `free`; exports `a`, `b`, `c`. -/
def Xh : Iface Unit := ⟨[(), (), ()], [(), (), ()]⟩

def iA : Xh.Imp := ⟨0, by decide⟩
def iU : Xh.Imp := ⟨1, by decide⟩
def iF : Xh.Imp := ⟨2, by decide⟩
def eA : Xh.Exp := ⟨0, by decide⟩
def eB : Xh.Exp := ⟨1, by decide⟩
def eC : Xh.Exp := ⟨2, by decide⟩

/-- The handle `5`. -/
abbrev h5 : Val := Val.i32 5

/-- Allocation in `a`, use in `b`, free in `c`. -/
def sessionsRun : List (Ev Xh) :=
  [.call eA [], .icall iA [], .iret iA (.returns [h5]), .ret eA (.returns []),
   .call eB [], .icall iU [h5], .iret iU (.returns []), .ret eB (.returns []),
   .call eC [], .icall iF [h5], .iret iF (.returns []), .ret eC (.returns [])]

/-- Use after free. -/
def uafRun : List (Ev Xh) := sessionsRun ++ [.call eB [], .icall iU [h5]]

/-- Double free. -/
def doubleFreeRun : List (Ev Xh) := sessionsRun ++ [.call eC [], .icall iF [h5]]

/-- Free of a never-allocated handle. -/
def freeNeverRun : List (Ev Xh) := [.call eC [], .icall iF [Val.i32 7]]

/-- The environment allocates the live handle `5` again; a later bad free is not blamed on the
program. -/
def envReuseRun : List (Ev Xh) :=
  [.call eA [], .icall iA [], .iret iA (.returns [h5]), .icall iA [], .iret iA (.returns [h5]),
   .icall iF [Val.i32 9]]

/-! ## Loose provider traces -/

/-- Exports `alloc`, `use`, `free`. -/
def Xp : Iface Unit := ⟨[], [(), (), ()]⟩

def pA : Xp.Exp := ⟨0, by decide⟩
def pU : Xp.Exp := ⟨1, by decide⟩
def pF : Xp.Exp := ⟨2, by decide⟩

/-- Allocate `1`, use, free, allocate `1` again. -/
def provRun : List (Ev Xp) :=
  [.call pA [], .ret pA (.returns [Val.i32 1]), .call pU [Val.i32 1], .ret pU (.returns []),
   .call pF [Val.i32 1], .ret pF (.returns []), .call pA [], .ret pA (.returns [Val.i32 1])]

/-- The live handle `1` allocated twice. -/
def provTwiceRun : List (Ev Xp) :=
  [.call pA [], .ret pA (.returns [Val.i32 1]), .call pA [], .ret pA (.returns [Val.i32 1])]

/-- The client frees a dead handle (its fault), then the provider allocates `1` twice. -/
def provClientBad : List (Ev Xp) :=
  [.call pF [Val.i32 3], .ret pF (.returns []) ] ++ provTwiceRun

/-! ## Loose ownership traces -/

/-- Imports `alloc`, `use`, `drop`, `consume`; exports `run` (borrowed argument), `keep` (owned
argument). -/
def Xo : Iface Unit := ⟨[(), (), (), ()], [(), ()]⟩

def oA : Xo.Imp := ⟨0, by decide⟩
def oU : Xo.Imp := ⟨1, by decide⟩
def oD : Xo.Imp := ⟨2, by decide⟩
def oG : Xo.Imp := ⟨3, by decide⟩
def oRun : Xo.Exp := ⟨0, by decide⟩
def oKeep : Xo.Exp := ⟨1, by decide⟩

/-- The roles. -/
def ρo : OBRoles Xo where
  alloc i := i = oA
  use i := i = oU
  free i := i = oD
  give i := i = oG
  lend j := j = oRun
  take j := j = oKeep

/-- A borrowed handle used during the call that lent it. -/
def borrowRun : List (Ev Xo) :=
  [.call oRun [Val.i32 3], .icall oU [Val.i32 3], .iret oU (.returns []), .ret oRun (.returns [])]

/-- A borrowed handle dropped. -/
def dropBorrowRun : List (Ev Xo) := [.call oRun [Val.i32 3], .icall oD [Val.i32 3]]

/-- A borrowed handle used after its call returned. -/
def outliveRun : List (Ev Xo) := borrowRun ++ [.call oRun [Val.i32 4], .icall oU [Val.i32 3]]

/-- Ownership given away, then used. -/
def giveRun : List (Ev Xo) :=
  [.call oKeep [Val.i32 8], .ret oKeep (.returns []), .call oRun [Val.i32 3],
   .icall oG [Val.i32 8], .iret oG (.returns []), .icall oU [Val.i32 8]]

/-- Ownership taken from `keep`, the handle used and dropped in a later call. -/
def transferRun : List (Ev Xo) :=
  [.call oKeep [Val.i32 8], .ret oKeep (.returns []), .call oRun [Val.i32 3],
   .icall oU [Val.i32 8], .iret oU (.returns []), .icall oD [Val.i32 8],
   .iret oD (.returns []), .ret oRun (.returns [])]

/-! ## `externref` handles on untyped moves -/

/-- The reference `ref.extern (host 7)`. -/
abbrev r7 : Val := .ref (.extern (.host 7))

/-- An import call of host code `h` with arguments `vs` in the empty store. -/
abbrev uAsk (h : Nat) (vs : List Val) : Silmaril.Games.Move UImp (untypedSig Unit) :=
  .inl (.ask ⟨h, {}, vs⟩)

/-- Its answer `values vs`. -/
abbrev uAns (h : Nat) (vs : List Val) : Silmaril.Games.Move UImp (untypedSig Unit) :=
  .inl (.ans ⟨h, {}, []⟩ ⟨{}, .values vs⟩)

/-- The export call. -/
abbrev uCall : Silmaril.Games.Move UImp (untypedSig Unit) := .inr (.ask ⟨(), {}, []⟩)

/-- The reference allocated (host code `0`), used (`1`), freed (`2`). -/
def exRun : List (Silmaril.Games.Move UImp (untypedSig Unit)) :=
  [uCall, uAsk 0 [], uAns 0 [r7], uAsk 1 [r7], uAns 1 [], uAsk 2 [r7], uAns 2 []]

/-- The reference used after it was freed. -/
def exUafRun : List (Silmaril.Games.Move UImp (untypedSig Unit)) := exRun ++ [uAsk 1 [r7]]

/-! ## Real Core 3.0 clients -/

/-- `[] → [i32]`. -/
def tyAlloc : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyUse : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
/-- `[] → []`. -/
def tyVoid : RecType := ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩

/-- The three imports. -/
def handleImports : List Import :=
  [⟨"env", "alloc", .func ⟨0⟩⟩, ⟨"env", "use", .func ⟨1⟩⟩, ⟨"env", "free", .func ⟨1⟩⟩]

/-- `run` calls `use(7)` before any allocation. -/
def cliUseBefore : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [], [.intConst .i32 7, .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- `run` frees the never-allocated handle `7`. -/
def cliFreeNever : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [], [.intConst .i32 7, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- `run` allocates and drops the handle; an unexported, unreferenced function uses and frees. -/
def cliAllocOnly : Module where
  types := [tyAlloc, tyUse, tyVoid]
  imports := handleImports
  funcs := [⟨⟨2⟩, [], [.call ⟨0⟩, .drop]⟩,
    ⟨⟨2⟩, [], [.intConst .i32 7, .call ⟨1⟩, .intConst .i32 7, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

end Silmaril.Wasm.Resource.Examples
