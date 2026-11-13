module

public import Silmaril.Wasm.Wac.StreamPkg.Defs
public import Silmaril.Wasm.Wac.Emit.Defs
public import Silmaril.Wasm.Component.Algebra.Plug.Defs

/-!
# WAC: a checked plug shape for stream packages

`StreamPkg.plugX_fusion` and `plugX_realizes` assume that the graph read from a binary is
`Algebra.plugGraph` of the packages' interfaces (`hG`), an equation about the elaboration of
`Emit.plugDoc` that nothing computes. The interfaces do not depend on `κ`: every package read
by `lowerXf κ`, and the default, is a stage, and all stages have the interface `stageSig`
(import `src`, export `src`). So `hG` is a property of the bytes alone, and it is decidable:

* `stageSigs`: the interface of every package (`StreamPkg.binSigs κ b = stageSigs`);
* **`plugShape b`**: the graph read from `b` with these interfaces is `plugGraph stageSigs`.

A tool can compute `plugShape` on the bytes it writes; the restated theorems
(`Silmaril.Wasm.Wac.PlugCheck.Thms`) assume `plugShape b = true` instead of `hG`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.PlugCheck

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Streams.Alg Silmaril.Wasm.Wac.StreamPkg Silmaril.Wasm.Wac.Emit

/-- The interface of every package read by `lowerXf κ` (a stage). -/
def stageSigs : Nat → PkgSig := fun _ => sigOf (stage .id)

/-- **The plug shape, checked on the bytes**: the graph read from `b` is `wac plug` of the
packages `0` (the plug) and `1` (the socket). -/
def plugShape (b : ByteArray) : Bool :=
  match binGraphX stageSigs b with
  | .ok G => decide (G = plugGraph stageSigs)
  | .error _ => false

end Silmaril.Wasm.Wac.PlugCheck
