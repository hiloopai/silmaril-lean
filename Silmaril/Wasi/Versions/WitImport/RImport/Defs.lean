module

public import Silmaril.Wasi.Versions.WitImport.Resolve.Defs
public import Silmaril.Wasi.Versions.WitImport.Select.Defs

@[expose] public section

/-!
# The importer with type environments

`importRPkg sel ver fs` runs the importer of `Silmaril.Wasi.Versions.WitImport` (with the worlds
dropped when `sel`, as `importIfaces`) and returns the resolved table of the first file's
package together with its type environment (`Silmaril.Wasi.Versions.WitImport.Resolve`):

* `rtable ver P`: `table ver P` with the interface of each function (`strip (rtable ver P) =
  table ver P` by definition);
* `envOf P deps`: the named types of the interfaces of `P` and of the dependency interfaces
  `deps` that `Elab.elaborate` returns, with doc comments dropped (`plainKind`).

This is unverified glue in the sense of `Silmaril.Wasi.Versions.WitImport`: it runs during
elaboration (`wit_rpkg%`, `Silmaril.Wasi.Versions.WitImport.RQuote`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-- A label without its doc comment. -/
def plainLabel {α : Type} (l : Binary.Labeled α) : Binary.Labeled α := { l with docs := none }

/-- A type kind without doc comments. -/
def plainKind : Binary.TyDefKind → Binary.TyDefKind
  | .record fs => .record (fs.map plainLabel)
  | .variant cs => .variant (cs.map plainLabel)
  | .enum cs => .enum (cs.map plainLabel)
  | .flags fs => .flags (fs.map plainLabel)
  | k => k

/-- The named types of an interface body. -/
def typesOf (b : Binary.Interface) : List (String × Binary.TyDefKind) :=
  b.types.map fun td => (td.name, plainKind td.kind)

/-- The functions of the interfaces of a package with their interface and signature. -/
def rtable (ver : Bool) (P : Binary.Package) : RTable :=
  P.interfaces.flatMap fun x =>
    x.2.funcs.map fun f => (⟨ifaceId ver P.name x.1, plainName f⟩, ⟨P.name, x.1⟩, f.sig)

/-- The type environment of a package and its dependencies. -/
def envOf (P : Binary.Package) (deps : Binary.Env) : TyEnv :=
  P.interfaces.map (fun x => (⟨P.name, x.1⟩, typesOf x.2)) ++ deps.map fun x => (x.1, typesOf x.2)

/-- **The importer with type environments.** -/
def importRPkg (sel ver : Bool) (fs : List Src) : Except String RPkg := do
  let ds ← fs.mapM parseSrc
  let U := if sel then (mergeDocs ds).map dropWorlds else mergeDocs ds
  let P ← U.head?.elim (.error "no package") pure
  let (B, deps) ← Elab.elaborate U P.name []
  pure (rtable ver B, envOf B deps)

end Silmaril.Wasi.Versions.WitImport
