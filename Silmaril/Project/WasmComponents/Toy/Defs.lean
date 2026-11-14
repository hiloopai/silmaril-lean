module

public import Silmaril.Project.WasmComponents.Ref.Defs
public import Silmaril.Wasm.Resource.CompToy.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasi.Component.Defs
public import Silmaril.Wasm.Wit.Project.Defs

/-!
# The Wasm components pilot: the resource-provider toy as a binary component

The toy component defining a resource (`Silmaril.Wasm.Resource.CompToy`, `toyComp`, a correct
provider by `toy_compProvider`) as a binary component (`Silmaril.Wasm.Component.Binary.Ast`), for
the registry:

* `toyCoreBytes`: the core module `toyCore`, as written by the Binaryen encoder
  (`Binaryen.Exe.encodeModule?`, 123 bytes);
* `toyAst`: the component of the `CompToy` docstring, item by item in its order (one section
  per run of items of one kind), with that core module;
* `toySplitAst`: the same items, one per section (`Wit.Project.splitSection`): a second
  release with different bytes and the same reference program;
* `toyWorld`: its WIT world (the component type `wasm-wit project` writes): the resource
  `r` exported as `(sub resource)`, `make: func() -> own<r>`, `get: func(h: borrow<r>) -> u32`,
  `drop: func(h: own<r>)`;
* `toyLayout`, `toyFnE`: the WASI names of the exports (`make`, `get`, `drop` at top level,
  interface `""`);
* `toyDen P prof`: the reference denotation (`Ref.refDen`) at the interface `CompToy.Xt` over
  `core3P P`, choice profile `prof` and the host without functions `refHost P`; `toyDenSpec` at
  the specification profile and the nondeterministic choice profile, the denotation of the
  pilot's rows.

The certificates, rows and proofs are in `Silmaril.Project.WasmComponents.Toy.Thms`; the files
are written by `examples/wasm-components/gen/Toy.lean`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Toy

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Resource.CompToy (Xt names)

/-- The core module `toyCore`, encoded by `Binaryen.Exe.encodeModule?`. -/
def toyCoreBytes : ByteArray := ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 1, 14, 3, 96, 1, 127, 1, 127,
  96, 1, 127, 0, 96, 0, 1, 127, 2, 22, 2, 3, 114, 101, 115, 3, 110, 101, 119, 0, 0, 3, 114, 101,
  115, 4, 100, 114, 111, 112, 0, 1, 3, 4, 3, 2, 0, 1, 6, 6, 1, 127, 1, 65, 0, 11, 7, 21, 3, 4,
  109, 97, 107, 101, 0, 2, 3, 103, 101, 116, 0, 3, 4, 100, 114, 111, 112, 0, 4, 10, 36, 3, 22, 0,
  35, 0, 65, 127, 70, 4, 64, 0, 11, 35, 0, 35, 0, 65, 1, 106, 36, 0, 16, 0, 11, 4, 0, 32, 0, 11,
  6, 0, 32, 0, 16, 1, 11]⟩

/-- **The toy as a binary component** (the WAT of the `CompToy` docstring). -/
def toyAst : Ast := .mk [
  .types [.resource .i32 none],
  .exports [⟨↑"r", ⟨.type, 0⟩, none⟩],
  .canons [.resourceNew 0, .resourceDrop 0],
  .coreModule toyCoreBytes,
  .coreInstances [.exports [("new", ⟨.func, 0⟩), ("drop", ⟨.func, 1⟩)],
    .instantiate 0 [("res", 0)]],
  .aliases [⟨.core .func, .coreExport 1 "make"⟩, ⟨.core .func, .coreExport 1 "get"⟩,
    ⟨.core .func, .coreExport 1 "drop"⟩],
  .types [.val (.own 1), .val (.borrow 1), .func ⟨[], some (.idx 2), false⟩,
    .func ⟨[("h", .idx 3)], some (.prim .u32), false⟩, .func ⟨[("h", .idx 2)], none, false⟩],
  .canons [.lift 2 [] 4],
  .exports [⟨↑"make", ⟨.func, 0⟩, none⟩],
  .canons [.lift 3 [] 5],
  .exports [⟨↑"get", ⟨.func, 2⟩, none⟩],
  .canons [.lift 4 [] 6],
  .exports [⟨↑"drop", ⟨.func, 4⟩, none⟩]]

/-- **The second release**: the same items, one per section. -/
def toySplitAst : Ast := .mk (toyAst.sections.flatMap Silmaril.Wasm.Wit.Project.splitSection)

/-- **The toy's world**: the projection of `toyAst` (`Wit.Project.projectX`). -/
def toyWorld : Silmaril.Wasm.Wit.Project.WorldType := [
  .inst (.export ↑"r" (.type .subResource)),
  .inst (.alias ⟨.type, .outer 0 0⟩),
  .inst (.type (.val (.own 1))),
  .inst (.type (.val (.borrow 1))),
  .inst (.type (.func ⟨[], some (.idx 2), false⟩)),
  .inst (.type (.func ⟨[("h", .idx 3)], some (.prim .u32), false⟩)),
  .inst (.type (.func ⟨[("h", .idx 2)], none, false⟩)),
  .inst (.export ↑"make" (.func 4)),
  .inst (.export ↑"get" (.func 5)),
  .inst (.export ↑"drop" (.func 6))]

/-- The WASI name of an export of the toy: the top-level function `names j`. -/
def toyFnE (j : Xt.Exp) : Silmaril.Wasi.FnName := ⟨"", names j⟩

/-- The toy has no imports. -/
def toyFnI (i : Xt.Imp) : Silmaril.Wasi.FnName := Fin.elim0 i

/-- The WASI world of the toy: no imports, the exports `make`, `get`, `drop`. -/
def toyLayout : Silmaril.Wasi.Layout := ⟨[], [toyFnE ⟨0, by decide⟩, toyFnE ⟨1, by decide⟩,
  toyFnE ⟨2, by decide⟩]⟩

/-- **The reference denotation of the toy's binaries** at profile `P` and choice profile
`prof`, with the host without functions. -/
noncomputable def toyDen (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) : Ast → toyLayout.world.Model :=
  Ref.refDen P prof (Silmaril.Wasm.Component.Reference.refHost P) () Xt [] names toyLayout.world
    toyFnI toyFnE

/-- The denotation of the pilot's rows: the specification profile, nondeterministic choices. -/
noncomputable def toyDenSpec : Ast → toyLayout.world.Model :=
  toyDen (Silmaril.Wasm.Numerics.Profile.spec) .nondet

/-- The provider guarantee of the toy on WASI events: `make` never returns a live handle. -/
def toyGuar : Silmaril.Wasm.Resource.Protocol (Option (List ℕ)) Silmaril.Wasi.WEv :=
  Ref.provGuar toyFnE Silmaril.Wasm.Resource.CompToy.makeE Silmaril.Wasm.Resource.CompToy.dropE

/-- The upgrade from the first release to the second: one world. -/
def toyUpgrade : toyLayout.world ⟶ toyLayout.world := CategoryTheory.CategoryStruct.id _

end Silmaril.Project.WasmComponents.Toy

end
