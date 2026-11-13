module

public import Silmaril.Wasm.Wac.Bridge.ComposeX.Defs
public import Silmaril.Wasm.Wac.EndToEnd.Defs
public import Silmaril.Wasm.Wac.Emit.Defs
public import Silmaril.Wasm.Wac.AsyncNames.Defs
public import Silmaril.Wasm.Wac.TextCheck.Defs
public import Silmaril.Wasm.Wit.Tool.Source.Defs

/-!
# WAC: type-only documents through the verified WIT encoder

A WAC document whose statements are all interface and world definitions (no imports, no
instantiations, no exports, no top-level type) composes to a component that only defines types:
for every interface `i` a component type exporting the instance type `ns:pkg/i@v`, for every
world `w` one exporting the component type `ns:pkg/w@v`, each exported as a type under its name
(wac's `TypeEncoder::interface` and `TypeEncoder::world`). That is exactly the layout in which
wit-component encodes a WIT package (`wasm-tools component wit --wasm`), including the wrappers
for `use`: a definition that uses types of another interface imports that interface (with its
own dependencies) and aliases the used types.

`Wac.Bridge.Encode` writes closed bodies (`ifaceDef`, `worldDef`) and does not record which
interface a used type comes from, so documents whose definitions `use` types of other interfaces
(of the document or of a package) were refused. This module reads such a document as the WIT
package it is and encodes it with the verified WIT elaborator and encoder:

* `docPackage`: the document's interfaces and worlds as a WIT package named after the document;
* `depDocs`: the packages the document needs, from their bytes: decoded and printed as WIT text
  (`Wit.Tool.witAll`, with their own dependencies as nested packages), parsed by the verified
  parser; each package once;
* `composeTypes`: `Wit.Tool.elabDocs` and `Binary.packageSections`, without the `package-docs`
  section (wac writes no documentation), encoded by the component encoder, async functions with
  their plain names (`AsyncNames.fixBytes`);
* `composeMixed`: a document with top-level types as well: those by the main encoder, the
  definitions after them by the WIT encoder.

`wasm-wac compose` uses this when the main pipeline refuses a type-only document.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.DocWit

open Silmaril.Wasm.Wac.Syntax

/-- The interfaces and worlds of a type-only document; `none` if it has another statement. -/
def defsOf : List Stmt → Option (List Wit.PackageItem)
  | [] => some []
  | .type (.iface i) :: r => (defsOf r).map (.iface i :: ·)
  | .type (.world w) :: r => (defsOf r).map (.world w :: ·)
  | _ :: _ => none

/-- The WIT package name of a document's package (read by the verified WIT parser). -/
def witName (p : PkgName) : Except String Wit.PackageName := do
  let v := match p.version with | some v => "@" ++ v | none => ""
  let d ← Wit.Tool.parseText "package name" s!"package {p.name}{v};"
  pure d.main.name

/-- **The document as a WIT package.** -/
def docPackage (d : Document) : Except String Wit.Document := do
  let some items := defsOf d.stmts | throw "not a type-only document"
  pure { main := { name := ← witName d.pkg, items } }

/-- Add packages, once each (by name). -/
def addPkgs (acc : List Wit.Package) : List Wit.Package → List Wit.Package
  | [] => acc
  | p :: ps => addPkgs (if acc.any (·.name == p.name) then acc else acc ++ [p]) ps

/-- **The packages a document needs**, from their bytes: each decoded and printed as WIT (with its
dependencies nested), parsed, and every package of it kept once. -/
def depDocs (raw : List (String × ByteArray)) : Except String (List Wit.Document) := do
  let mut acc : List Wit.Package := []
  for (k, b) in raw do
    let t ← Wit.Tool.witAll b
    let d ← Wit.Tool.parseText k t
    acc := addPkgs acc d.packages
  pure (acc.map fun p => { main := p })

/-- Drop the `package-docs` section. -/
def noDocs (ss : List Component.Binary.Section) : List Component.Binary.Section :=
  ss.filter fun
    | .custom n _ => n != "package-docs"
    | _ => true

/-- Does a type contain a `borrow` (through the aliases `al` of its scope; `f`: fuel)? -/
def hasBorrow (al : List (Wit.Name × Wit.Ty)) : Nat → Wit.Ty → Bool
  | 0, _ => false
  | _ + 1, .borrow _ => true
  | f + 1, .named n => match al.lookup n with
    | some t => hasBorrow al f t
    | none => false
  | f + 1, .list t | f + 1, .fixedList t _ | f + 1, .option t => hasBorrow al f t
  | f + 1, .map k v => hasBorrow al f k || hasBorrow al f v
  | f + 1, .tuple ts => ts.attach.any fun ⟨t, _⟩ => hasBorrow al f t
  | f + 1, .result a b =>
    (a.map (hasBorrow al f)).getD false || (b.map (hasBorrow al f)).getD false
  | f + 1, .future a | f + 1, .stream a => (a.map (hasBorrow al f)).getD false
  | _, _ => false

/-- The aliases `type x = T` of an interface body. -/
def aliasesOf (items : List Wit.IfaceItem) : List (Wit.Name × Wit.Ty) :=
  items.filterMap fun
    | .type ⟨n, .alias t, _, _⟩ => some (n, t)
    | _ => none

/-- A function of an interface body returns a borrow (wit-parser and wac reject it). -/
def borrowResult (items : List Wit.IfaceItem) : Bool :=
  let al := aliasesOf items
  items.any fun
    | .func fd => (fd.func.result.map (hasBorrow al (al.length + 8))).getD false
    | _ => false

/-- A definition of the document returns a borrow from a function. -/
def anyBorrowResult (items : List Wit.PackageItem) : Bool :=
  items.any fun
    | .iface i => borrowResult i.items
    | .world w => w.items.any fun
      | .import ⟨.iface _ b, _, _⟩ | .export ⟨.iface _ b, _, _⟩ => borrowResult b
      | .import ⟨.func _ f, _, _⟩ | .export ⟨.func _ f, _, _⟩ =>
        (f.result.map (hasBorrow [] 8)).getD false
      | _ => false
    | _ => false

/-- **The checks of the main pipeline still apply**: the text checks (`TextCheck.checkText`), no
`targets` clause, and the document's elaboration against the packages (`FuncAlias.elabDocA`)
succeeds, or fails only because a package item it names is a WIT definition with `use`s (the
wrapper layout is read as neither an interface nor a world: `notInterface`, `notWorld`). So a
document wac rejects for another reason (a borrow in a result, a non-function used as one, a
target that is not a world, …) is still rejected. A function returning a borrow is refused here
(`anyBorrowResult`), as wac refuses it. -/
def checks (src : String) (raw : List (String × ByteArray)) : Except String Unit := do
  TextCheck.checkText src
  let d ← Bridge.readDocX src
  if d.targets.isSome then throw "a type-only document with `targets`"
  if (defsOf d.forget.stmts).any anyBorrowResult then throw "a function returns a borrow"
  let (env, _, _) ← EndToEnd.readPkgs raw (Bridge.pkgKeysX d)
  match FuncAlias.elabDocA env d with
  | .ok _ => pure ()
  | .error (.notInterface _) | .error (.notWorld _) => pure ()
  | .error e => throw s!"elaboration: {reprStr e}"

/-- **A type-only document to bytes** through the verified WIT elaborator and encoder. -/
def composeTypes (src : String) (raw : List (String × ByteArray)) : Except String ByteArray := do
  checks src raw
  let d ← Bridge.readDocX src
  -- `forget` drops function type items: a document with one is not type-only here
  if d.stmts.length != d.forget.stmts.length then throw "not a type-only document"
  let w ← docPackage d.forget
  let ds ← depDocs raw
  let (P, env) ← Wit.Tool.elabDocs w ds []
  let ss ← Wit.Binary.packageSections env P
  match Component.Binary.encode (.mk (noDocs ss)) with
  | some b => pure (AsyncNames.fixBytes b)
  | none => throw "a number or size exceeds 2^32"

/-! ## Documents with top-level types as well -/

/-- The number of type indices the sections define. -/
def typeCount : List Component.Binary.Section → Nat
  | [] => 0
  | s :: ss =>
    let n := match s with
      | .types xs => xs.length
      | .imports xs => (xs.filter fun i => match i.desc with | .type _ => true | _ => false).length
      | .exports xs => (xs.filter (·.item.sort == .type)).length
      | .aliases xs => (xs.filter (·.sort == .type)).length
      | _ => 0
    n + typeCount ss

/-- An interface or world definition of the document. -/
def isDef : FuncAlias.Stmt → Bool
  | .iface .. | .world .. => true
  | .wit (.type (.iface _)) | .wit (.type (.world _)) => true
  | _ => false

/-- A top-level type statement (a type or a function type). -/
def isTopType : FuncAlias.Stmt → Bool
  | .wit (.type (.type _)) | .funcType .. => true
  | _ => false

/-- The sections of WIT items whose component types start at type index `n`: the `j`-th item
defines index `n + 2j` and exports it (wit-component's `itemSections` from an offset). -/
def itemsFrom (n : Nat) (items : List (String × List Component.Binary.ComponentDecl)) :
    List Component.Binary.Section :=
  (items.zipIdx 0).flatMap fun x =>
    [.types [.component x.1.2], .exports [⟨↑x.1.1, ⟨.type, n + 2 * x.2⟩, none⟩]]

/-- Is the section a custom section? -/
def isCustom : Component.Binary.Section → Bool
  | .custom .. => true
  | _ => false

/-- **A document of top-level types and of interface and world definitions**: the top-level
types by the main encoder (`Emit.composeAst` of the document without the definitions), then the
definitions by the verified WIT elaborator and encoder (`Binary.encodeIfaceItem`,
`encodeWorldItem`), their component types numbered after the types of the first part. -/
def composeMixed (src : String) (raw : List (String × ByteArray)) : Except String ByteArray := do
  checks src raw
  let d ← Bridge.readDocX src
  let defs := d.stmts.filter isDef
  let rest := d.stmts.filter (!isDef ·)
  if defs.isEmpty || !rest.all isTopType then throw "not a document of types and definitions"
  let (env, noms, _) ← EndToEnd.readPkgs raw (Bridge.pkgKeysX d)
  let ast ← Emit.composeAst env noms { d with stmts := rest }
  let ss₁ := ast.sections.filter (!isCustom ·)
  let w ← docPackage { pkg := d.pkg, stmts := defs.filterMap FuncAlias.Stmt.forget }
  let ds ← depDocs raw
  let (P, penv) ← Wit.Tool.elabDocs w ds []
  let env' := P.env penv
  let ifs ← P.interfaces.mapM (Wit.Binary.encodeIfaceItem env' P.name)
  let ws ← P.worlds.mapM (Wit.Binary.encodeWorldItem env' P.name)
  let ss₂ := itemsFrom (typeCount ss₁) (ifs ++ ws)
  match Component.Binary.encode (.mk (ss₁ ++ ss₂ ++ ast.sections.filter isCustom)) with
  | some b => pure (AsyncNames.fixBytes b)
  | none => throw "a number or size exceeds 2^32"

end Silmaril.Wasm.Wac.DocWit
