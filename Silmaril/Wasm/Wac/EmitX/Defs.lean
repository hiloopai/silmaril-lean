module

public import Silmaril.Wasm.Wac.EmitAlg.Defs
public import Silmaril.Wasm.Wac.SpliceX.Defs
public import Silmaril.Wasm.Perf.CanonB.Defs

/-!
# WAC: composed binaries with async packages, read back with their packages' meanings

`Emit.composeWasmRaw` (what `wasm-wac compose --wasm` and `plug` run) splices the packages'
bytes into the composition. `Emit.binComp S P b` reads the binary back as an algebra term
evaluated at package meanings `P` given *as a parameter*, and needs the base parser. This module
reads everything off the bytes, packages with the async built-ins included:

* `composeWasmX`: `composeWasmRaw` together with the canonicity check `SpliceX.canonTable` of
  the packages' bytes (the tool prints whether it holds);
* `binGraphX S b`: parse with the async built-ins (`parseX`), erase them, lower
  (`Lower.graph`);
* `binPkgs rd dflt b k`: **the meaning of the `k`-th package, read from the bytes embedded in
  `b`**: the `k`-th component of `b` (`SpliceX.pkgsOf`), lowered to the component IR by a
  package lowering `rd : AstX → Option (Comp M)` (`dflt` when there is none: an imported
  package, or a component `rd` does not lower);
* `binCompX S rd dflt b`: the binary's term evaluated at those meanings; `binTermX` the term.

Theorems in `Silmaril.Wasm.Wac.EmitX.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Emit

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync

/-- **`wasm-wac compose --wasm` with the canonicity check**: the bytes of `composeWasmRaw`,
and the packages' extended ASTs when every package's bytes are canonical. -/
def composeWasmX (env : PkgEnv) (noms : List (String × Bridge.NomTable))
    (raw : List (String × ByteArray)) (d : FuncAlias.Document) :
    Except String (ByteArray × Option SpliceX.PkgTableX) := do
  let b ← composeWasmRaw env noms raw d
  pure (b, Silmaril.Wasm.Perf.EncodeB.canonTableF (Splice.table raw))

/-- The composition graph of a binary with async packages. -/
def binGraphX (S : Nat → PkgSig) (b : ByteArray) : Except String Graph :=
  match parseX b with
  | .ok a => Lower.graph S a.erase
  | .error _ => .error "the binary does not parse"

variable {M : Type}

/-- The meaning of a component, by a package lowering, `dflt` when there is none. -/
def pkgMeaning (rd : AstX → Option (Comp M)) (dflt : Comp M) (o : Option AstX) : Comp M :=
  (o.bind rd).getD dflt

/-- **The packages' meanings, read from the bytes embedded in the binary.** -/
def binPkgs (rd : AstX → Option (Comp M)) (dflt : Comp M) (b : ByteArray) : Nat → Comp M :=
  match parseX b with
  | .ok a => fun k => pkgMeaning rd dflt ((SpliceX.pkgsOf a)[k]?).join
  | .error _ => fun _ => dflt

/-- The algebra term of a binary with async packages. -/
def binTermX (S : Nat → PkgSig) (b : ByteArray) : Except String (Tm M) :=
  (binGraphX S b).map (Graph.term S)

/-- **The component of a binary, with every package's meaning read from its own bytes.** -/
def binCompX (S : Nat → PkgSig) (rd : AstX → Option (Comp M)) (dflt : Comp M) (b : ByteArray) :
    Except String (Comp M) :=
  (binGraphX S b).map (Graph.build S (binPkgs rd dflt b))

end Silmaril.Wasm.Wac.Emit
