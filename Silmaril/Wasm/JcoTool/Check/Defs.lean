module

public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Jco.Thin.Defs
public import Silmaril.Wasm.Perf.LowerF.Defs

/-!
# `wasm-jco`: reading an output back as a thin wrapper (translation validation)

`irCheck core out` reads the component binary `out` with the independent reader of the
component IR (`Silmaril.Wasm.Component.Binary.parseComponent`: the verified parser, then the
lowering to `Comp CoreMod`; run as `Perf.LowerF.parseComponentF`, the same function with the
fast core decoder: `LowerF.parseComponentF_eq`) and decides whether the result **is** the thin wrapper
`Silmaril.Wasm.Jco.Thin.thin w m p` of a core module `m` with the bytes `core`, along a plan `p`
that the recognizer `Thin.recognize` finds for the world `w` the component shows (its imports,
and its exports with their types), with the naming style `Style.plain`.

The checks are Boolean and each has a soundness lemma (`Silmaril.Wasm.JcoTool.Check.Thms`):
`irCheck core out = true` gives the equation `parseComponent out = .ok (thin w m p)` and hence,
by `Thin.denU_wrapGlue_glue`, the behaviour of the output under every core semantics.

The IR has no linear memory: the check applies to worlds of memory-free, synchronous
functions; elsewhere it returns `false` and the tool reports it as not applicable.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Check

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Binary (CoreMod parseComponent)
open Silmaril.Wasm.Jco.Thin

/-- `im` is the wiring program `chain` ending in a call of `r`. -/
def implIs (im : Impl) (chain : List Adapter) (r : Nat) : Bool :=
  match im with
  | ⟨ch, .call r'⟩ => decide (ch = chain) && decide (r' = r)
  | _ => false

/-- Pointwise `implIs`. -/
def implsAre : List Impl → List (List Adapter × Nat) → Bool
  | [], [] => true
  | im :: is, (ch, r) :: xs => implIs im ch r && implsAre is xs
  | _, _ => false

/-- An export is `⟨name, ty, chain ⇒ call r⟩`. -/
def exportIs (x : Silmaril.Wasm.Component.Export) (name : String) (ty : FuncTy) (chain : List Adapter) (r : Nat) : Bool :=
  decide (x.name = name) && decide (x.ty = ty) && implIs x.impl chain r

/-- Pointwise `exportIs`. -/
def exportsAre : List Silmaril.Wasm.Component.Export → List (String × FuncTy × List Adapter × Nat) → Bool
  | [], [] => true
  | x :: xs, (n, t, ch, r) :: ys => exportIs x n t ch r && exportsAre xs ys
  | _, _ => false

/-- The wiring of the imports of a thin wrapper, as `(chain, target)` pairs. -/
def wiringSpec (w : World) (p : Plan) : List (List Adapter × Nat) :=
  p.imports.map fun i => ([.lower (w.imports[i]?.getD default).2], i)

/-- The exports of a thin wrapper, as `(name, type, chain, target)`. -/
def exportsSpec (e : Nat) (fs : Iface) (js : List Nat) : List (String × FuncTy × List Adapter × Nat) :=
  (fs.zip js).map fun x => (x.1.1, x.1.2, [.lift x.1.2], e + x.2)

/-- The world a lowered component shows: its imports, and its exports with their types. -/
def shownWorld : Comp CoreMod → World
  | .mk I _ xs => ⟨I, xs.map fun x => (x.name, x.ty)⟩

/-- Whether `c` is `thin w m p`. -/
def isThin (c : Comp CoreMod) (w : World) (m : CoreMod) (p : Plan) : Bool :=
  match c with
  | .mk I [.core m' args] xs =>
    decide (I = w.imports) && decide (m'.bytes.data = m.bytes.data) &&
      decide (m'.importNames = m.importNames) && decide (m'.imports = m.imports) &&
      decide (m'.exports = m.exports) &&
      implsAre args (wiringSpec w p) &&
      exportsAre xs (exportsSpec w.imports.length w.exports p.exports)
  | _ => false

/-- The core module of a single-node component. -/
def theModule : Comp CoreMod → Option CoreMod
  | .mk _ [.core m _] _ => some m
  | _ => none

/-- **The check**: `out` reads back as the thin wrapper of a module with the bytes `core`. -/
def irCheck (core out : ByteArray) : Bool :=
  match Silmaril.Wasm.Perf.LowerF.parseComponentF out with
  | .ok c =>
    match theModule c with
    | some m =>
      let w := shownWorld c
      match recognize .plain w (CoreModule.imports m) (CoreModule.exports m) with
      | some p => decide (m.bytes.data = core.data) && isThin c w m p
      | none => false
    | none => false
  | .error _ => false

end Silmaril.Wasm.JcoTool.Check
