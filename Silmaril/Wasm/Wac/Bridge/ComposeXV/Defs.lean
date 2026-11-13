module

public import Silmaril.Wasm.Wac.Bridge.ComposeX.Defs
public import Silmaril.Wasm.Wac.Valid.Defs

/-!
# WAC bridge: `wasm-wac compose` with function type names and validation

The pipeline of `wasm-wac compose` after the pass-3 merge: `ComposeX` (text →
`FuncAlias.Document` by `ofDocX`, elaboration by `FuncAlias.elabDocA`) with the checks
of `Silmaril.Wasm.Wac.Valid` around it, as `ComposeV` does for `Syntax.Document`:

* `Valid.checkDoc` on the WIT part `forgetV d` (below) before elaboration;
* `Valid.checkGraph` on the elaborated graph after it, against the registry with its
  aliases expanded (`env.expand`, as `FuncAlias.elabDocA` sees it) and with the package
  and `targets` of `d.forget`, which are those of `d`.

`checkDoc` sees `forgetV d`: `forget` without the WIT items that `FuncAlias` reads as
function type items, namely aliases `type g = f` and top-level imports `import b: f` of a
function type name `f` in scope (tracked as `FuncAlias` does: per interface, per world,
and at the top level). The function type items themselves are not checked for
uniqueness of names or for the scope of their parameter types here.
No theorem is stated for this composition of the two tracks: on a WIT-only document
(`ofDoc`) it is `ComposeV`'s pipeline by `FuncAlias.elabDocA_ofDoc`, which is not proved
here as an equation of `composeWatXV` either.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm

/-- Is `d` an alias `type g = f` of a name `f` of `fs`? -/
def isFuncAlias (fs : List String) (d : Wit.TypeDef) : Bool :=
  match d.kind with
  | .alias (.named f) => fs.contains f
  | _ => false

/-- The WIT items of an interface body that `FuncAlias` does not read as function type
items, with the function type names `fs` of the body so far. -/
def witItemsV : List String → List FuncAlias.IItem → List Wit.IfaceItem
  | _, [] => []
  | fs, .wit (.type d) :: is =>
    if isFuncAlias fs d then witItemsV (fs ++ [d.name]) is else .type d :: witItemsV fs is
  | fs, .wit i :: is => i :: witItemsV fs is
  | fs, .funcType n _ :: is => witItemsV (fs ++ [n]) is
  | fs, .funcRef .. :: is => witItemsV fs is

/-- The WIT items of a world body, as `witItemsV`. -/
def worldItemsV : List String → List FuncAlias.WItem → List Wit.WorldItem
  | _, [] => []
  | fs, .wit (.type d) :: is =>
    if isFuncAlias fs d then worldItemsV (fs ++ [d.name]) is else .type d :: worldItemsV fs is
  | fs, .wit i :: is => i :: worldItemsV fs is
  | fs, .import (.iface n items) :: is =>
    .import ⟨.iface n (witItemsV [] items), {}, []⟩ :: worldItemsV fs is
  | fs, .export (.iface n items) :: is =>
    .export ⟨.iface n (witItemsV [] items), {}, []⟩ :: worldItemsV fs is
  | fs, .import (.ref ..) :: is => worldItemsV fs is
  | fs, .export (.ref ..) :: is => worldItemsV fs is
  | fs, .funcType n _ :: is => worldItemsV (fs ++ [n]) is

/-- The statements of a document without its function type items, as `witItemsV`. -/
def stmtsV : List String → List FuncAlias.Stmt → List Syntax.Stmt
  | _, [] => []
  | fs, .wit (.type (.type d)) :: ss =>
    if isFuncAlias fs d then stmtsV (fs ++ [d.name]) ss else .type (.type d) :: stmtsV fs ss
  | fs, .wit (.import ⟨id, as, .ident x⟩) :: ss =>
    if fs.contains x then stmtsV fs ss else .import ⟨id, as, .ident x⟩ :: stmtsV fs ss
  | fs, .wit s :: ss => s :: stmtsV fs ss
  | fs, .iface n is :: ss => .type (.iface ⟨n, witItemsV [] is, {}, []⟩) :: stmtsV fs ss
  | fs, .world n is :: ss => .type (.world ⟨n, worldItemsV [] is, {}, []⟩) :: stmtsV fs ss
  | fs, .funcType n _ :: ss => stmtsV (fs ++ [n]) ss
  | fs, .importIface id as is :: ss => .import ⟨id, as, .iface (witItemsV [] is)⟩ :: stmtsV fs ss

/-- The document `checkDoc` validates: its WIT part without function type aliases. -/
def forgetV (d : FuncAlias.Document) : Syntax.Document :=
  ⟨d.pkg, d.targets, stmtsV [] d.stmts⟩

/-- Elaboration of a document with function type names, with validation. -/
def elabDocXV (T : Valid.Tables) (env : PkgEnv) (d : FuncAlias.Document) :
    Except Valid.VElabError CGraph :=
  match Valid.checkDoc (forgetV d) with
  | .error e => .error (.valid e)
  | .ok () => match FuncAlias.elabDocA env d with
    | .error e => .error (.elab e)
    | .ok g => match Valid.checkGraph T env.expand d.forget g with
      | .ok () => .ok g
      | .error e => .error (.valid e)

/-- **`wasm-wac compose`**: function type names and validation; `noms` are the
packages' definition tables by package key. -/
def composeWatXV (env : PkgEnv) (noms : List (String × NomTable)) (d : FuncAlias.Document) :
    Except String String := do
  let T : Valid.Tables := { doc := docNom d.forget, pkgs := noms }
  let g ← match elabDocXV T env d with
    | .ok g => .ok g
    | .error (.elab e) => .error s!"elaboration: {reprStr e}"
    | .error (.valid e) => .error s!"validation: {reprStr e}"
  let c ← encode (docNom d.forget ++ noms.flatMap (·.2)) g
  pure (Component.Wat.print c)

end Silmaril.Wasm.Wac.Bridge
