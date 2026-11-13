module

public import Silmaril.Wasm.Tools.Component.WitText.Defs

/-!
# A fast path for elaborating large WIT worlds

Measured on a world of 512 functions (`wasm-tools-witbench`, 2026-11-10): parsing, the validity
check, elaboration and encoding take about 40 ms together, but `Wit.Tool.encodeText` took
1.1 s and the CLI's `pkgBytesF` 2.3 s:

* `Elab.Package.namesUniqueB` took 1.07 s, in `World.namesUniqueB`: the compiled
  `decide (List.Nodup (l.map WorldItem.key))` recomputes the keys inside the pairwise
  comparison (2 ms with the keys computed first);
* `WitText.encodeTextXF` (like `Wac.WitDir.encodeTextX`) binds its fallback `ext` with a
  strict `let`, so the fallback elaboration ran even when the first one succeeded.

The fast path (`encodeTextXFast`) computes each list of names once and passes it to `nodupB`
(not inlined), and delays the fallback (`fun () => …`). Every function here is proved equal to
the specification it replaces (`Silmaril.Wasm.Tools.Component.WitFast.Thms`:
`packageUnique_eq`, `elaborateFast_eq`, `encodeTextFast_eq`, `encodeTextXFast_eq`), so the
CLI's results are those of the verified elaborator and encoder.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.WitFast

open Silmaril.Wasm.Wit
open Silmaril.Wasm.Wit.Elab (labelsUniqueB)

/-- `decide l.Nodup` on a list computed by the caller. -/
@[noinline] def nodupB (l : List String) : Bool := decide l.Nodup

def interfaceUnique (b : Binary.Interface) : Bool :=
  nodupB (b.types.map (·.name)) && nodupB (b.funcs.map Binary.Func.mangled) &&
    b.types.all (fun td => labelsUniqueB td.kind)

def worldUnique (w : Binary.World) : Bool :=
  nodupB (w.imports.map Binary.WorldItem.key) && nodupB (w.exports.map Binary.WorldItem.key) &&
    w.exports.all (fun it => !it.isType) &&
    (w.imports ++ w.exports).all fun it => match it with
      | .ifaceInline _ b => interfaceUnique b
      | .type td => labelsUniqueB td.kind
      | _ => true

/-- `Elab.Package.namesUniqueB`, each list of names computed once. -/
def packageUnique (p : Binary.Package) : Bool :=
  nodupB (p.interfaces.map (·.1)) && nodupB (p.worlds.map (·.1)) &&
    p.interfaces.all (fun nb => interfaceUnique nb.2) &&
    p.worlds.all (fun nw => worldUnique nw.2)

/-- `Elab.elaborate` with `packageUnique`. -/
def elaborateFast (U : Universe) (p : PackageName) (fs : List Name := []) :
    Except String (Binary.Package × Binary.Env) := do
  let U := Universe.gate fs U
  Elab.require (check U) "invalid WIT universe"
  let c := Elab.Ctx.ofUniverse U
  let P ← Elab.lookupPkg U p
  let env ← Elab.elabEnv c
  let out ← Elab.elabPackage c env P
  let deps := env.filter (·.1.pkg != Elab.pkgName p)
  Elab.require (Elab.Package.validB out deps) "names do not survive the binary encoding"
  Elab.require (packageUnique out) "names are not unique"
  pure (out, deps)

/-- `Tool.encodeDocs` with `elaborateFast`. -/
def encodeDocsFast (d : Document) (ds : List Document) (fs : List Name) : Except String ByteArray := do
  let (P, env) ← elaborateFast (Tool.sourceUniverse d ds) d.main.name fs
  Binary.encodePackage env P

/-- `Tool.encodeText` with `elaborateFast`. -/
def encodeTextFast (main : String × String) (deps : List (String × String)) (fs : List Name := []) :
    Except String ByteArray := do
  let (d, ds) ← Tool.parseSource main deps
  encodeDocsFast d ds fs

/-- `WitText.encodeTextXF` with the fast elaboration and a delayed fallback. -/
def encodeTextXFast (main : List (String × String)) (deps : List (List (String × String)))
    (fs : List String) : Except String ByteArray :=
  let ext : Unit → Except String ByteArray := fun () => do
    let d ← Wac.WitDir.parseFiles main
    let ds ← deps.mapM Wac.WitDir.parseFiles
    encodeDocsFast d ds fs
  match main, deps.all (·.length == 1) with
  | [m], true =>
    match encodeTextFast m (deps.flatMap id) fs with
    | .ok b => .ok b
    | .error _ => ext ()
  | _, _ => ext ()

end Silmaril.Wasm.Tools.Component.WitFast
