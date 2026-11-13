module

public import Silmaril.Wasm.Wac.StreamFn.Defs
public import Silmaril.Wasm.JcoTool.KRead.Defs
public import Silmaril.Wasm.JcoTool.KLive.Defs

/-!
# WAC: the code of a stream package, read off the generated core module's bytes

`StreamPkg.Interp` (`κ : ByteArray → Option TCode`) says which transformer code a core module
implements; the WAC theorems (`StreamFn.composeText_fn_equiv`) hold for every `κ`. This module
gives the `κ` of the generated stream modules: the table of modules the tools generate.

* `Gen`: a generated module: kernel `k`, read size `N`, export name, and a transformer code
  `code` meant to have the kernel's whole output;
* `Gen.bytes`: the bytes `wasm-jco kcore NAME KERNEL N -o` writes for it,
  `KCoreEmit.wasmOf (genD k N) name`;
* `GensOK gs`: read sizes in `1..256`, each code has its kernel's whole output
  (`code.run = (trV k).run`), and each kernel's bounds hold (`KLive.KFits`);
* **`kappa gs`**: the code of the first module of `gs` whose bytes are `b` (computable: it runs
  the generator and compares bytes).

What `kappa` is worth is in `StreamCore.Thms`: its code is the whole output every finished Core
run of the decoded module produces (`kappa_core`, through `KCoreEmit.wasmOf_decode` and
`KRead.core_whole_correct`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamCore

open Silmaril.Wasm.Component.Streams.Alg (TCode)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (trV)
open Silmaril.Wasm.JcoTool.KDrop (genD)
open Silmaril.Wasm.Wac.StreamPkg (Interp)

/-- A generated stream module and the code it stands for. -/
structure Gen where
  k : KM
  N : Nat
  name : String
  code : TCode

/-- The bytes of the generated module. -/
def Gen.bytes (g : Gen) : Except String ByteArray :=
  Silmaril.Wasm.JcoTool.KCoreEmit.wasmOf (genD g.k g.N) g.name

/-- The result `x` is the bytes `b`. -/
def okIs : Except String ByteArray → ByteArray → Bool
  | .ok b', b => b'.data == b.data
  | .error _, _ => false

/-- `g` writes the bytes `b`. -/
def Gen.writes (g : Gen) (b : ByteArray) : Bool := okIs g.bytes b

/-- The table is well formed. -/
def GensOK (gs : List Gen) : Prop :=
  ∀ g ∈ gs, 0 < g.N ∧ g.N ≤ 256 ∧ g.code.run = (trV g.k).run ∧ Silmaril.Wasm.JcoTool.KLive.KFits g.k g.N

/-- **The `κ` of the generated stream modules.** -/
def kappa (gs : List Gen) : Interp := fun b => (gs.find? (·.writes b)).map (·.code)

end Silmaril.Wasm.Wac.StreamCore
