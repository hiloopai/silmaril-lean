module

public import Silmaril.Wasm.Wac.Bridge.Text.Defs
public import Silmaril.Wasm.Wac.Bridge.Encode.Defs
public import Silmaril.Wasm.Wac.Bridge.Decode.Defs
public import Silmaril.Wasm.Wac.Elab.Defs
public import Silmaril.Wasm.Wac.Alias.Defs
public import Silmaril.Wasm.Wac.Tool.Defs

/-!
# WAC bridge: the pipeline of `wasm-wac compose`

text → `Text.Document` (`Tool.parseDoc`) → `Syntax.Document` (`ofDoc`) → `CGraph`
(`elabDoc`, given the packages) → component in the composition profile (`encode`) →
WAT (`Wat.print`).

`pkgKeys d` lists the packages a document needs (the operands of `new`, the packages of
import paths, of world item, `use` and `include` paths and of `targets`, other than the
document's own); the tool reads each from
`DEPS/ns/name.wasm` (wac's `--deps-dir` layout) and decodes it (`decodePkg`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm

mutual
/-- The packages instantiated in an expression. -/
def exprPkgs : Syntax.Expr → List String
  | .ident _ => []
  | .new p as => p.key :: argsPkgs as
  | .paren e | .access e _ | .namedAccess e _ => exprPkgs e
/-- The packages instantiated in arguments. -/
def argsPkgs : List Syntax.Arg → List String
  | [] => []
  | .named _ e :: as => exprPkgs e ++ argsPkgs as
  | _ :: as => argsPkgs as
end

/-- The key of the package of a path. -/
def pathKey (p : Syntax.PkgPath) : String := Syntax.PkgName.key ⟨p.pkg, p.version⟩

/-- The package of a WIT path (`ns:pkg/name@version`), if foreign. -/
def usePathPkgs : Wit.UsePath → List String
  | .foreign pk _ => [pk.ns ++ ":" ++ pk.name ++ (match pk.version with | none => "" | some v => "@" ++ v.str)]
  | .local _ => []

/-- The packages of the `use`s of an interface body. -/
def ifaceItemsPkgs (items : List Wit.IfaceItem) : List String :=
  items.flatMap fun | .use u => usePathPkgs u.path | _ => []

/-- The packages of a world import or export. -/
def externPkgsOf : Wit.Extern → List String
  | .path p => usePathPkgs p
  | .iface _ items => ifaceItemsPkgs items
  | .func .. => []

/-- The packages of a world item: its interface path, the `use`s of its inline
interface, the path of a `use` or an `include`. -/
def externPkgs : Wit.WorldItem → List String
  | .import e | .export e => externPkgsOf e.ext
  | .use u => usePathPkgs u.path
  | .include i => usePathPkgs i.path
  | .type _ => []

/-- The packages a statement needs. -/
def stmtPkgs : Syntax.Stmt → List String
  | .import ⟨_, _, .path p⟩ => [pathKey p]
  | .import ⟨_, _, .iface items⟩ => ifaceItemsPkgs items
  | .type (.world w) => w.items.flatMap externPkgs
  | .type (.iface i) => ifaceItemsPkgs i.items
  | .let _ e | .export e _ => exprPkgs e
  | _ => []

/-- The packages a document needs, once each, without its own. -/
def pkgKeys (d : Syntax.Document) : List String :=
  let ks := d.stmts.flatMap stmtPkgs ++ (d.targets.map pathKey).toList
  (ks.filter fun k => k != d.pkg.key && (k.splitOn "@").headD k != d.pkg.name).eraseDups

/-- The nominal definition of a WIT type definition (`res`: the resources in scope). -/
def witNominal (res : List String) (d : Wit.TypeDef) : Option (String × Nominal) :=
  match d.kind with
  | .record fs => some (d.name, .record (fs.map fun f => (f.name, witTy res f.ty)))
  | .variant cs => some (d.name, .variant (cs.map fun c => (c.name, c.ty.map (witTy res))))
  | .enum ls => some (d.name, .enum (ls.map (·.name)))
  | .flags ls => some (d.name, .flags (ls.map (·.name)))
  | _ => none

/-- The resources an interface body declares. -/
def ifaceResources (items : List Wit.IfaceItem) : List String :=
  items.filterMap fun | .type d => (match d.kind with | .resource _ => some d.name | _ => none) | _ => none

/-- The nominal definitions of an interface body. -/
def ifaceNom (items : List Wit.IfaceItem) : NomTable :=
  items.filterMap fun | .type d => witNominal (ifaceResources items) d | _ => none

/-- The nominal definitions of a world body. -/
def worldNom (items : List Wit.WorldItem) : NomTable :=
  items.flatMap fun
    | .type d => (witNominal [] d).toList
    | .import ⟨.iface _ is, _, _⟩ | .export ⟨.iface _ is, _, _⟩ => ifaceNom is
    | _ => []

/-- The nominal definitions of a document (its type statements and inline
interfaces). -/
def docNom (d : Syntax.Document) : NomTable :=
  d.stmts.flatMap fun
    | .type (.iface i) => ifaceNom i.items
    | .type (.world w) => worldNom w.items
    | .type (.type t) => (witNominal [] t).toList
    | .import ⟨_, _, .iface is⟩ => ifaceNom is
    | _ => []

/-- Read a document. -/
def readDoc (src : String) : Except String Syntax.Document := do
  ofDoc (← Tool.parseDoc src)

/-- Elaborate a document against packages, up to aliases (`elabDocA`: the decoded
packages' aliases, e.g. `type r2 = r` of a resource, are expanded as the document's
own are). -/
def elabStr (env : PkgEnv) (d : Syntax.Document) : Except String CGraph :=
  match elabDocA env d with
  | .ok g => .ok g
  | .error e => .error s!"elaboration: {reprStr e}"

/-- **`wasm-wac compose`**: the WAT of a document's composition. -/
def composeWat (env : PkgEnv) (nom : NomTable) (d : Syntax.Document) : Except String String := do
  let g ← elabStr env d
  let c ← encode (docNom d ++ nom) g
  pure (Component.Wat.print c)

end Silmaril.Wasm.Wac.Bridge
