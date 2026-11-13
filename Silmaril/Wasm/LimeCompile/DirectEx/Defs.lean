module

public import Silmaril.Wasm.LimeCompile.Direct.Defs

/-!
# The direct 3.0 → Lime compiler on concrete modules: definitions

* `pickL`: a Lime1 module exporting `pick : [i32 i32 i32] → [i32]`, the untyped `select` of its
  three parameters;
* `pickM`: the Core 3.0 module with the same API and the typed `select (result i32)` (reference
  types proposal), which is outside Lime1;
* `refM`: a Core 3.0 module whose exported function takes a `funcref` parameter: its API is
  outside Lime1.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.DirectEx

open Silmaril.Wasm

/-- `i32`. -/
abbrev i32L : Lime1.ValType := .int .i32

/-- The body of `pick`, in Lime1. -/
def pickBodyL : Lime1.Expr := [.localGet ⟨0⟩, .localGet ⟨1⟩, .localGet ⟨2⟩, .select]

/-- **A Lime1 module**: `pick` selects between its first two parameters on the third. -/
def pickL : Lime1.Module where
  types := [⟨[i32L, i32L, i32L], [i32L]⟩]
  funcs := [⟨⟨0⟩, [], pickBodyL⟩]
  exports := [⟨"pick", .func ⟨0⟩⟩]

/-- The body of `pick` with the typed `select (result i32)`. -/
def pickBodyM : Expr :=
  [.localGet ⟨0⟩, .localGet ⟨1⟩, .localGet ⟨2⟩, .select (some [.num (.int .i32)])]

/-- **A Core 3.0 module outside Lime1** with the API of `pickL`. -/
def pickM : Module := { pickL.toCore with funcs := [⟨⟨0⟩, [], pickBodyM⟩] }

/-- **A Core 3.0 module with a 3.0-only API**: `isnull : [funcref] → [i32]`. -/
def refM : Module where
  types := [⟨[⟨true, [], .func ⟨[.ref ⟨true, .abstract .func⟩], [.num (.int .i32)]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .refIsNull]⟩]
  exports := [⟨"isnull", .func ⟨0⟩⟩]

end Silmaril.Wasm.LimeCompile.DirectEx
