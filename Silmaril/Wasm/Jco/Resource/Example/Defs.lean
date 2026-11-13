module

public import Silmaril.Wasm.Jco.Resource.Merge.Defs

/-!
# A litmus world with a resource

Resource type `0`, a "box" whose rep is the boxed number. The world is

* `make: func(x: u32) -> own<box>`,
* `peek: func(b: borrow<box>) -> u32`,
* `open: func(b: own<box>) -> u32`.

`exRInst` implements it in the rep-passing convention: its state is its memory, `alloc` is a bump
allocator, and `make`, `peek`, `open` are the identity on one `i32` (a box's rep is its contents).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res.Example

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Component (Flat ValTy Val)

/-- The outcome of the bump allocator `alloc(size, align)`. -/
def rAllocOut (xs : List Flat) (m : Mem) : Out Mem (List Flat) :=
  match xs with
  | [⟨.int .i32, size⟩, ⟨.int .i32, align⟩] =>
    let a := (m.length + max align.toNat 1 - 1) / max align.toNat 1 * max align.toNat 1
    .ok [i32n a] (m ++ List.replicate (a - m.length + size.toNat) 0)
  | _ => .trap

/-- The identity on one `i32`. -/
def idOut (xs : List Flat) (m : Mem) : Out Mem (List Flat) :=
  match xs with
  | [⟨.int .i32, x⟩] => .ok [Flat.i32 x] m
  | _ => .trap

/-- The exports. -/
def exRCall (name : String) (xs : List Flat) : RM Mem (List Flat) := fun m o =>
  o = if name = "alloc" then rAllocOut xs m
    else if name = "make" ∨ name = "peek" ∨ name = "open" then idOut xs m
    else .trap

/-- The litmus instance. -/
def exRInst : CoreInst where
  St := Mem
  mem m := m
  setMem _ m := m
  call := exRCall

/-- The litmus world. -/
def exMdR : MetaR where
  world :=
    [⟨"make", [.base (.val .u32)], some (.own 0)⟩,
     ⟨"peek", [.borrow 0], some (.base (.val .u32))⟩,
     ⟨"open", [.own 0], some (.base (.val .u32))⟩]

end Silmaril.Wasm.Jco.Res.Example
