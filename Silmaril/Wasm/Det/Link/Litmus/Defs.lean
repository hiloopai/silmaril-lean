module

public import Silmaril.Wasm.Game.Linking.Defs

/-!
# A concrete static link (litmus)

```wat
(module $p                                              ;; the provider
  (func (export "seven") (result i32) i32.const 7))
(module                                                 ;; the consumer
  (import "p" "seven" (func $seven (result i32)))
  (func (export "eight") (result i32) call $seven  i32.const 1  i32.add))
```

`linkP` and `linkC` are linked by silmaril-lean's GC linker `link?` (namespace `"p"`) into
`linkL`; `linkSp`, `linkSl` are the stores of `instantiateOnce?` of the provider and the linked
module over the empty store, `linkScs` the store of the consumer instantiated against host stubs
for the provider's stub set, and `linkSc` the shared store (the consumer instantiated over the
provider store, its import resolved to the provider's function). All of them are computed by kernel evaluation in
`Silmaril.Wasm.Det.Link.Litmus.Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Link.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Link Silmaril.Wasm.Link.GC
open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking

/-- The provider: exports `seven : [] → [i32]`. -/
def linkP : Module where
  types := [⟨[⟨true, [], .func ⟨[], [.num (.int .i32)]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 7]⟩]
  exports := [⟨"seven", .func ⟨0⟩⟩]

/-- The consumer: imports `p.seven` and exports `eight`, which adds one to it. -/
def linkC : Module where
  types := [⟨[⟨true, [], .func ⟨[], [.num (.int .i32)]⟩⟩]⟩]
  imports := [⟨"p", "seven", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add]⟩]
  exports := [⟨"eight", .func ⟨1⟩⟩]

/-- The base store. -/
def linkBase : Store Nat := {}

/-- The output of the linker. -/
def linkL : Module := (link? "p" linkP linkC).getD linkP

/-- A default instantiation result. -/
def noInst : Store Nat × Frame × Option FuncIdx := ({}, {}, none)

/-- The provider instantiated over the empty store. -/
def linkPI : Store Nat × Frame × Option FuncIdx :=
  (instantiateOnce? linkBase linkP (Preparation.imports [])).getD noInst

/-- The linked module instantiated over the empty store. -/
def linkLI : Store Nat × Frame × Option FuncIdx :=
  (instantiateOnce? linkBase linkL (Preparation.imports [])).getD noInst

/-- The provider store. -/
def linkSp : Store Nat := linkPI.1

/-- The linked store. -/
def linkSl : Store Nat := linkLI.1

/-- The stub set of the link (the provider's function `0`). -/
def linkStubs : List Nat := [0]

/-- The consumer instantiated against host stubs for the stub set. -/
def linkCI : Store Nat × Frame × Option FuncIdx :=
  (instantiateOnce? (stubOut linkBase.funcs.length linkStubs linkSp) linkC
    (Preparation.imports ([(⟨0⟩ : FuncIdx)].map fun f => linkBase.funcs.length + f.toNat))).getD
    noInst

/-- The consumer store with host stubs. -/
def linkScs : Store Nat := linkCI.1

/-- The consumer instantiated over the provider store (the shared world of the link: both parts
in one store, the import resolved to the provider's function). -/
def linkShI : Store Nat × Frame × Option FuncIdx :=
  (instantiateOnce? linkSp linkC
    (Preparation.imports ([(⟨0⟩ : FuncIdx)].map fun f => linkBase.funcs.length + f.toNat))).getD
    noInst

/-- The shared store. -/
def linkSc : Store Nat := linkShI.1

/-- The function addresses checked by the direct-mode and stateless checks (both functions). -/
def linkAddrs : List Nat := [0, 1]

/-- The scalar type `[] → [i32]`. -/
def i32Fn : FnType := ⟨[], [.num (.int .i32)]⟩

end Silmaril.Wasm.Det.Link.Litmus
