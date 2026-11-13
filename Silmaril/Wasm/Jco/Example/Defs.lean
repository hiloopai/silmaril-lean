module

public import Silmaril.Wasm.Jco.Wrap.Defs

/-!
# A litmus core instance for the monadic construction

`exInst` is a core instance whose state is just its linear memory, with three exports in the C
convention:

* `alloc(size, align)`: a bump allocator; it pads the memory to a multiple of `align` (at least
  1), returns that address and grows the memory by `size` zero bytes;
* `add(a: i32, b: i32) -> i32`: wrapping addition;
* `echo(ptr, len, out)`: the identity on strings in the C convention: it writes the pair
  `(ptr, len)` to the out-pointer `out` and returns nothing.

`exMeta` is the world `add: func(a: u32, b: u32) -> u32; echo: func(s: string) -> string`, and
`exWorld` the same world as resolved WIT (`Silmaril.Wasm.Wit.Binary.World`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Example

open Silmaril.Wasm.Component (Flat ValTy Val)

/-- A little-endian `u32` as four bytes. -/
def le32 (x : Nat) : List UInt8 :=
  [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256].map UInt8.ofNat

/-- The bump allocator: the padded address and the grown memory. -/
def bump (m : Mem) (size align : Nat) : Nat × Mem :=
  let a := (m.length + align - 1) / align * align
  (a, m ++ List.replicate (a - m.length + size) 0)

/-- `alloc(size, align)`. -/
def exAlloc (xs : List Flat) : RM Mem (List Flat) := fun m o =>
  match xs with
  | [⟨.int .i32, size⟩, ⟨.int .i32, align⟩] =>
    o = .ok [i32n (bump m size.toNat (max align.toNat 1)).1] (bump m size.toNat (max align.toNat 1)).2
  | _ => o = .trap

/-- `add(a, b)`. -/
def exAdd (xs : List Flat) : RM Mem (List Flat) := fun m o =>
  match xs with
  | [⟨.int .i32, a⟩, ⟨.int .i32, b⟩] => o = .ok [Flat.i32 (a + b)] m
  | _ => o = .trap

/-- `echo(ptr, len, out)`. -/
def exEcho (xs : List Flat) : RM Mem (List Flat) := fun m o =>
  match xs with
  | [⟨.int .i32, p⟩, ⟨.int .i32, l⟩, ⟨.int .i32, out⟩] =>
    match m.write out.toNat (le32 p.toNat ++ le32 l.toNat) with
    | some m' => o = .ok [] m'
    | none => o = .trap
  | _ => o = .trap

/-- The exports of the litmus instance. -/
def exCall (name : String) : List Flat → RM Mem (List Flat) :=
  if name = "alloc" then exAlloc else if name = "add" then exAdd
  else if name = "echo" then exEcho else fun _ => RM.fail

/-- The litmus instance. -/
abbrev exInst : CoreInst where
  St := Mem
  mem := id
  setMem := fun _ m => m
  call := exCall

/-- The metadata of the litmus world. -/
def exMeta : Meta where
  world := [⟨"add", [.val .u32, .val .u32], some (.val .u32)⟩, ⟨"echo", [.string], some .string⟩]

/-- The litmus world as resolved WIT. -/
def exWorld : Silmaril.Wasm.Wit.Binary.World where
  exports := [
    .func { name := "add", params := [("a", .prim .u32), ("b", .prim .u32)],
            result := some (.prim .u32) },
    .func { name := "echo", params := [("s", .prim .string)], result := some (.prim .string) }]

end Silmaril.Wasm.Jco.Example
