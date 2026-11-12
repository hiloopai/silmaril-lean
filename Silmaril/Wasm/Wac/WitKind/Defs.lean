module

public import Silmaril.Wasm.Wac.CGraph.Defs

/-!
# WAC: item kinds of resolved WIT packages

The kinds WAC sees for the items of a resolved WIT package (`Wit.Binary.Package`,
the model the WIT formalization elaborates and encodes), following
wac-types' import of WIT (`crates/wac-types/src/package.rs`, wac `5a7480c`):

* an interface is an instance type `.inst (some "ns:pkg/iface@v")` exporting its type
  definitions (`.type`, resources as `.resource`) and its functions under their
  binary names (`[method]r.f`, …), with their signatures (`Func.sig`);
* a world is a component type: its imports and exports, where an interface by path is
  the instance of the interface's body found in the environment;
* a package registers its interfaces and worlds as `defs` (for package paths); a
  component *targeting* a world has the world's imports and exports (`worldPackage`).

`Silmaril.Wasm.Wac.WitKind.Thms`: these kinds are WIT-shaped (`Kind.wit`), so a registry
of components targeting WIT worlds satisfies the hypothesis of `elabDoc_typed`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Wit.Binary (TypeDef Func Interface WorldItem World Package IfaceName TyRef Owner)

namespace WitKind

/-- The kind a WIT type definition exports. -/
def ofTypeDef (d : TypeDef) : Kind :=
  match d.kind with
  | .resource => .type (.resource d.name)
  | .type t => .type (.value t)
  | _ => .type (.value (.ref ⟨.local, d.name⟩))

/-- A function, under its binary name. -/
def ofFunc (f : Func) : String × Kind := (f.mangled, .func f.sig)

/-- The exports of an interface body. -/
def ofBody (i : Interface) : Externs :=
  i.types.map (fun d => (d.name, ofTypeDef d)) ++ i.funcs.map ofFunc

/-- An interface as an instance type. -/
def ofInterface (id : Option String) (i : Interface) : Kind := .inst id (ofBody i)

/-- A world item, as a named extern. -/
def ofWorldItem (env : Wit.Binary.Env) : WorldItem → String × Kind
  | .ifaceRef i _ _ => (i.id, ofInterface (some i.id) ((env.lookup i).getD {}))
  | .ifaceInline n body => (n, ofInterface none body)
  | .func f => ofFunc f
  | .type d => (d.name, ofTypeDef d)

/-- A world as a component type: its imports and exports. -/
def ofWorld (env : Wit.Binary.Env) (w : World) : Externs × Externs :=
  (w.imports.map (ofWorldItem env), w.exports.map (ofWorldItem env))

/-- The package of a component targeting the world `w`. -/
def worldPackage (env : Wit.Binary.Env) (w : World) : PkgType :=
  { imports := (ofWorld env w).1, exports := (ofWorld env w).2 }

/-- The definitions of a WIT package: its interfaces and worlds, for package paths. -/
def defsOf (env : Wit.Binary.Env) (p : Package) : Externs :=
  p.interfaces.map (fun (n, i) => (n, .type (ofInterface (some (p.name.iface n).id) i))) ++
  p.worlds.map fun (n, w) =>
    (n, .type (.comp (some (Wit.Binary.IfaceName.id (p.name.iface n))) (ofWorld env w).1 (ofWorld env w).2))

/-- The package key `ns:name(@version)` of a WIT package name. -/
def keyOf (p : Wit.Binary.PackageName) : String :=
  p.ns ++ ":" ++ p.name ++ (match p.version with | none => "" | some v => "@" ++ v)

end WitKind

end Silmaril.Wasm.Wac
