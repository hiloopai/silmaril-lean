module

public import Silmaril.Wasm.Examples.Farkas.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs

@[expose] public section

/-!
# The Farkas checker as a component

`farkasS` wraps the Core 3.0 checker `farkasMod` (`Silmaril.Wasm.Examples.Farkas`) as a simple
component of the reference Component Model fragment (`Silmaril.Wasm.Component.Reference.Simple`):
one core instance of the module, and the three core exports `canon lift`ed at

```wit
row: func(y: s64, b: s64);
entry: func(j: u32, a: s64);
check: func() -> u32;
```

The abstract specification at the component level mirrors `Farkas.next`: `cnext` loads a
`row`/`entry` call on its IR values (`Cmd.apply` on `BitVec.toInt`, resp. `BitVec.toNat` for
`j`) and empties the state on `check`; `cloaded calls` is the state after a list of export calls
(by export index, as in `seqBehaviours`). A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Logic.LinArith (WRows Cmd)

/-- The checker module with its named numeric exports. -/
def farkasNum : NumModule :=
  ⟨farkasMod, [("row", ⟨[.int .i64, .int .i64], []⟩), ("entry", ⟨[.int .i32, .int .i64], []⟩),
    ("check", ⟨[], [.int .i32]⟩)]⟩

/-- **The checker component**: `row(s64, s64)`, `entry(u32, s64)`, `check() -> u32`. -/
def farkasS : Simple :=
  ⟨farkasNum, [⟨"row", ⟨[.s64, .s64], []⟩, 0⟩, ⟨"entry", ⟨[.u32, .s64], []⟩, 1⟩,
    ⟨"check", ⟨[], [.u32]⟩, 2⟩]⟩

/-- The loading command of a call of the core export `k` on the IR values `vs`. -/
def cmdOfC : Nat → List Silmaril.Wasm.Component.Val → Option Cmd
  | 0, [.s64 y, .s64 b] => some (.row y.toInt b.toInt)
  | 1, [.u32 j, .s64 a] => some (.entry j.toNat a.toInt)
  | _, _ => none

/-- **The abstract transition of a component call**: `row`/`entry` load, `check` empties. -/
def cnext (rs : WRows) (q : SimpleExport × List Silmaril.Wasm.Component.Val) : WRows :=
  if q.1.core = 2 then [] else
    match cmdOfC q.1.core q.2 with
    | some cmd => cmd.apply rs
    | none => rs

/-- The rows loaded by a list of component calls (export index and IR arguments). -/
def cloaded (calls : List (Fin farkasS.exports.length × List Silmaril.Wasm.Component.Val)) : WRows :=
  (specCalls farkasS calls).foldl cnext []

end Silmaril.Wasm.Examples.Farkas
