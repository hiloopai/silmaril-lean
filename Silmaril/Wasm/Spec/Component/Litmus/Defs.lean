module

public import Silmaril.Wasm.Spec.Component.Async.Defs
public import Silmaril.Wasm.Spec.Component.Ground.Defs
public import Silmaril.Wasm.Spec.Joint.Wrap.Defs
public import Silmaril.Wasm.Component.Reference.Litmus.Defs
public import Silmaril.Wasm.Component.Reference.Example.Defs

@[expose] public section

/-!
# Component litmus programs

Concrete component interfaces, values and traces for the litmus tests of
`Silmaril.Wasm.Spec.Component.Litmus.Thms`, one group per stage.

* **Scalars, records, variants** (real components): the IR components `adderS`, `recordS`,
  `optionS` of `Silmaril.Wasm.Component.Reference.Litmus` (one Core 3.0 module
  `local.get 0; local.get 1; i32.add` or `i32.mul`, lifted at `add(u32, u32) -> u32`,
  `sum(record {u32, u32}) -> u32`, `get-or-zero(option<u32>) -> u32`); `adderRef`, the
  reference adder over `core3 neverFail` with the specification embedder.
* **Strings and lists** (loose traces): `Xs` exports `greet(string) -> list<u8>` and imports
  `log(string)`; `greetRun` greets `"hi"`, logging it.
* **Handles** (loose traces): `Xh` exports `new() -> own<r>`, `use(borrow<r>) -> u32`,
  `drop(own<r>)`; `handleRun` creates, uses and drops handle `7`; `useAfterDrop` uses it again;
  `leakRun` returns a handle it was lent.
* **Streams** (loose async traces): `Xa` exports `produce() -> stream<u8>`; `streamRun` writes
  one byte to end `3` and closes it; `doubleClose` closes it twice; `openRun` never closes it.
* **Modules as components**: `addNum`, a numeric module interface, and `addModRun`, a
  module trace `add(3, 4) = 7` in Core values.
-/

namespace Silmaril.Wasm.Spec.Component.Litmus

open Silmaril.Wasm.Component.Reference (toRefVal Simple)
open Silmaril.Wasm.Component.Value (StrVal)

/-! ## Values and types -/

/-- The reference value `u32 n`. -/
abbrev u32 (n : ℕ) : RVal := .int .u32 n
/-- The reference value `u8 n`. -/
abbrev u8 (n : ℕ) : RVal := .int .u8 n
/-- A UTF-8 string lifted from a 32-bit memory. -/
def str (s : String) : RVal :=
  .string ⟨⟨s, .utf8, (Silmaril.Wasm.Component.ABI.utf8Encode s).length⟩, .i32⟩
/-- The type `u32`. -/
abbrev tU32 : CTy := .prim .u32
/-- The type `u8`. -/
abbrev tU8 : CTy := .prim .u8
/-- The type `string`. -/
abbrev tStr : CTy := .prim .string

/-! ## The reference adder -/

/-- The reference adder over `core3 neverFail`, at the interface of the IR adder. -/
def adderRef :
    RefProg (Silmaril.Wasm.Component.Engine.core3 Silmaril.Wasm.SingleThreaded.neverFail)
      (cface Silmaril.Wasm.Component.Reference.Litmus.adderS.toComp) :=
  ⟨Silmaril.Wasm.Component.Reference.Litmus.adderS.toRef, [], fun _ => "add"⟩

/-- The export `add` of the adder. -/
def addE : (cface Silmaril.Wasm.Component.Reference.Litmus.adderS.toComp).Exp :=
  Simple.expIdx _ ⟨0, by decide⟩

/-! ## Strings and lists -/

/-- `greet(string) -> list<u8>`, importing `log(string)`. -/
def Xs : CIface := ⟨[⟨[tStr], []⟩], [⟨[tStr], [.list tU8]⟩]⟩

/-- The export `greet`. -/
def greetE : Xs.Exp := ⟨0, by decide⟩
/-- The import `log`. -/
def logI : Xs.Imp := ⟨0, by decide⟩

/-- `greet("hi")` logs `"hi"` and returns its bytes. -/
def greetRun : List (CEvent Xs) :=
  [.call greetE [str "hi"], .icall logI [str "hi"], .iret logI (.returns (some [])),
    .ret greetE (.returns (some [.list [u8 104, u8 105]]))]

/-! ## Handles -/

/-- `new() -> own<r>`, `use(borrow<r>) -> u32`, `drop(own<r>)`. -/
def Xh : CIface := ⟨[], [⟨[], [.own 0]⟩, ⟨[.borrow 0], [tU32]⟩, ⟨[.own 0], []⟩]⟩

/-- `new`. -/
def newE : Xh.Exp := ⟨0, by decide⟩
/-- `use`. -/
def useE : Xh.Exp := ⟨1, by decide⟩
/-- `drop`. -/
def dropE : Xh.Exp := ⟨2, by decide⟩

/-- Create handle `7`, use it, drop it. -/
def handleRun : List (CEvent Xh) :=
  [.call newE [], .ret newE (.returns (some [.own 7])),
    .call useE [.borrow 7], .ret useE (.returns (some [u32 1])),
    .call dropE [.own 7], .ret dropE (.returns (some []))]

/-- … then use it again. -/
def useAfterDrop : List (CEvent Xh) := handleRun ++ [.call useE [.borrow 7]]

/-- `use` returns the handle it was lent, as owned. -/
def leakRun : List (CEvent Xh) := [.call useE [.borrow 7], .ret useE (.returns (some [.own 7]))]

/-! ## Streams -/

/-- `produce() -> stream<u8>`. -/
def Xa : CIface := ⟨[], [⟨[], [.stream (some tU8)]⟩]⟩

/-- `produce`. -/
def prodE : Xa.Exp := ⟨0, by decide⟩

/-- `produce` returns stream end `3`, writes `[1]` to it and closes it. -/
def streamRun : List (AEvent Xa) :=
  [.inr (.ask prodE (.args [])), .inr (.ans prodE (.out (.returns (some [.stream ⟨3⟩])))),
    .inr (.ask prodE (.write 3 [u8 1])), .inr (.ans prodE (.written 3 1)),
    .inr (.ask prodE (.close 3))]

/-- … and closes it again. -/
def doubleClose : List (AEvent Xa) := streamRun ++ [.inr (.ask prodE (.close 3))]

/-- Writes and never closes. -/
def openRun : List (AEvent Xa) := streamRun.take 4

/-! ## Modules as components -/

/-- The numeric interface `add : [i32 i32] -> [i32]`. -/
def addNum : NIface := ⟨[], [⟨[.int .i32, .int .i32], [.int .i32]⟩]⟩

/-- The export `add` at the numeric interface. -/
def addNumE : addNum.Exp := ⟨0, by decide⟩

/-- A module trace: `add(3, 4)` returns `7`. -/
def addModRun : List (Event (List Silmaril.Wasm.Execution.Core.Val)
    (Silmaril.Wasm.Behaviour Silmaril.Wasm.Execution.Core.Val) addNum) :=
  [.call addNumE [.i32 3, .i32 4], .ret addNumE (.returns [.i32 7])]

end Silmaril.Wasm.Spec.Component.Litmus
