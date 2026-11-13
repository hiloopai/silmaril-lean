module

public import Silmaril.Wasm.Wac.Emit.Defs
public import Silmaril.Wasm.Wac.Lower.Defs
public import Silmaril.Wasm.Component.Algebra.Wac.Defs

/-!
# WAC: the component of a composed binary, as a term of the component algebra

`wasm-wac compose --wasm` (and `plug`) writes a binary `b` (`Emit.composeWasm`). This module
reads the binary back into the component algebra (`Silmaril.Wasm.Component.Algebra`):

* `binGraph S b`: parse `b` and lower it to a composition graph over the package
  interfaces `S` (`Lower.graph`);
* `binTerm S b`: the algebra term of that graph (`Graph.term`), whose variables are the
  packages;
* `binComp S P b`: the component of the binary for the packages `P`, the term evaluated at `P`
  (`Graph.build`).

The theorems (`Silmaril.Wasm.Wac.EmitAlg.Thms`) say that `binTerm` is the term of the elaborated
WAC document, and that substituting equivalent packages gives an equivalent composed binary
(`composeWasm_equiv`), restating `Emit.composeWasm_congr` through the algebra.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Emit

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Binary

variable {M : Type}

/-- The composition graph of a binary, over the package interfaces `S`. -/
def binGraph (S : Nat → PkgSig) (b : ByteArray) : Except String Graph :=
  match parse b with
  | .ok a => Lower.graph S a
  | .error _ => .error "the binary does not parse"

/-- **The algebra term of a composed binary**: its variables are the packages. -/
def binTerm (S : Nat → PkgSig) (b : ByteArray) : Except String (Tm M) :=
  (binGraph S b).map (Graph.term S)

/-- The component of a composed binary for the packages `P` (interfaces `S`). -/
def binComp (S : Nat → PkgSig) (P : Nat → Comp M) (b : ByteArray) : Except String (Comp M) :=
  (binGraph S b).map (Graph.build S P)

end Silmaril.Wasm.Wac.Emit
