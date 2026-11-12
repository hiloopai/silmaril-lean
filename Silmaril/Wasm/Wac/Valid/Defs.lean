module

public import Silmaril.Wasm.Wac.Alias.Defs
public import Silmaril.Wasm.Wac.Bridge.Encode.Defs
public import Silmaril.Wasm.Wit.Name.Defs
public import Silmaril.Wasm.Wit.Binary.Decode.Defs

/-!
# WAC: the validation wac does that the elaborator does not

The differential against `wac compose` (`tests/wasm-wac/compose.sh`) found 26
documents that wac rejects and `elabDoc` accepts, plus `targets-interface-use`. This
module states what wac checks there as relations, with a checker for each
(`Silmaril.Wasm.Wac.Valid.Thms` proves every checker sound against its relation). The
sources are wac `5a7480c`, `crates/wac-parser/src/resolution.rs` (`variant_decl`,
`record_decl`, `flags_decl`, `enum_decl`, `resource_decl`, `func_type`, `ty`,
`type_alias`), `crates/wac-graph/src/graph.rs` (`import`, `export`, which call
wasmparser's `ComponentName::new`) and `crates/wac-types/src/checker.rs` (structural
comparison of defined value types).

1. **Declarations** (`DeclsOk`): the fields of a record, the cases of a variant and an
   enum and the flags are unique; a resource has at most one constructor, unique
   method and static function names (methods and statics share one namespace), and
   unique parameter names in each of its functions.
2. **Names in types** (`StmtsOk`): a named type denotes a value type or a resource
   *declared before it in the same scope* (wac's `local_item`: an interface or world
   body is its own scope, the top level is the root scope); `own`/`borrow` take a
   resource; `type x = a` with `a` an interface, world, or instance is
   `InvalidAliasType`. Names brought in by `use` and imports are accepted whatever
   they denote (`Cat.unk`), so this check never rejects for them.
3. **Extern names** (`NamesOk`): import names are component-model extern names
   (`ExternName`: kebab labels, `[constructor]`/`[method]`/`[static]` and their
   `[async …]` forms, interface names `ns:pkg/iface@version`, and the `url=<…>`,
   `relative-url=<…>`, `integrity=<…>`, `locked-dep=<…>` and `unlocked-dep=<…>`
   forms); export names are extern names other than those last forms (`Special`).
4. **Borrows in results** (`NoBorrowRes`): no function of the composition (any node's
   kind) has a result containing `borrow`. Aliases are expanded in the elaborated
   kinds, so `type a = borrow<x>; f: func() -> result<a>` is caught.
5. **Structural comparison of nominal types** (`SubS`, `ArgsOk`, `TargetsOk`): records,
   variants, enums and flags are compared by their definitions, as wac's subtype
   checker does, where kinds only keep the name. A local reference `ref ⟨.local, t⟩`
   is resolved in a table of definitions (`Bridge.NomTable`) chosen by where the kind
   came from (`Origin`: the document, or the package of an instantiation, an import
   path or an implicit import); two resolved definitions must have the same labels in
   the same order, with structurally equal types (`TyEqS`). A reference that does not
   resolve on both sides is compared by equality, as `Sub` does. Instantiation arguments (`ArgsOk`) and the
   `targets` world (`TargetsOk`) are checked this way.

`elabDocV` runs the declaration and scope checks, `elabDocA`, then the graph checks.

**Restrictions.** The tables are flat (the first definition of a name in a package or
the document is used), so two interfaces of one package with equally named nominal
types of different shapes are not told apart. A `borrow` inside a record or variant
field of a result is not found (`BorrowIn` follows the type, not the definitions).
The contents of `url=<…>`, `integrity=<…>` and dependency names are not validated, and
the version of an interface name is only checked to be non-empty and made of
alphanumerics, `.`, `-` and `+`. Structural comparison is an extra check: kinds that
`Sub` rejects because their references have different names are still rejected.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner)

namespace Valid

/-! ## Errors -/

/-- What validation reports. -/
inductive VError where
  | duplicateField (ty name : String)
  | duplicateCase (ty name : String)
  | duplicateEnumCase (ty name : String)
  | duplicateFlag (ty name : String)
  | duplicateConstructor (res : String)
  | duplicateMethod (res name : String)
  | duplicateParam (res name : String)
  | undefinedName (name : String)
  | notResourceType (name : String)
  | invalidAlias (name : String)
  | invalidImportName (name : String)
  | invalidExportName (name : String)
  | borrowInResult
  | mismatchedArg (pkg name : String)
  | targetMismatch (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- Run `x`, then `y`. -/
def andThen (x y : Except VError Unit) : Except VError Unit :=
  match x with
  | .ok () => y
  | .error e => .error e

/-- Check every element of a list, stopping at the first error. -/
def allOk {α : Type} (f : α → Except VError Unit) : List α → Except VError Unit
  | [] => .ok ()
  | a :: as => andThen (f a) (allOk f as)

/-- The first name of a list that occurs again later. -/
def firstDup : List String → Option String
  | [] => none
  | a :: as => if a ∈ as then some a else firstDup as

/-- No duplicate, or the error of the first one. -/
def noDup (mk : String → VError) (l : List String) : Except VError Unit :=
  match firstDup l with
  | none => .ok ()
  | some n => .error (mk n)

/-! ## 1. Declarations -/

/-- The name of a resource function (constructors have none). -/
def rfName : Wit.ResourceFuncKind → Option String
  | .ctor => none
  | .method n | .static n => some n

/-- Whether a resource function is a constructor. -/
def isCtor (f : Wit.ResourceFunc) : Bool :=
  match f.kind with
  | .ctor => true
  | _ => false

/-- **A type definition's labels are unique** (wac's `DuplicateRecordField`,
`DuplicateVariantCase`, `DuplicateEnumCase`, `DuplicateFlag`,
`DuplicateResourceConstructor`, `DuplicateResourceMethod`, `DuplicateParameter`). -/
def DefOk : Wit.TypeDefKind → Prop
  | .alias _ => True
  | .record fs => (fs.map (·.name)).Nodup
  | .variant cs => (cs.map (·.name)).Nodup
  | .enum ls => (ls.map (·.name)).Nodup
  | .flags ls => (ls.map (·.name)).Nodup
  | .resource fns =>
    (fns.filter isCtor).length ≤ 1 ∧ (fns.filterMap (rfName ·.kind)).Nodup ∧
      ∀ f ∈ fns, (f.func.params.map (·.1)).Nodup

/-- The type definitions of an interface body. -/
def ifaceDefs (items : List Wit.IfaceItem) : List Wit.TypeDef :=
  items.filterMap fun | .type d => some d | _ => none

/-- The type definitions of a world extern (its inline interface). -/
def externDefs : Wit.Extern → List Wit.TypeDef
  | .iface _ items => ifaceDefs items
  | _ => []

/-- The type definitions of a world body. -/
def worldDefs (items : List Wit.WorldItem) : List Wit.TypeDef :=
  items.flatMap fun
    | .type d => [d]
    | .import e | .export e => externDefs e.ext
    | _ => []

/-- The type definitions of a statement: type statements and inline interfaces. -/
def stmtDefs : Syntax.Stmt → List Wit.TypeDef
  | .type (.iface i) => ifaceDefs i.items
  | .type (.world w) => worldDefs w.items
  | .type (.type d) => [d]
  | .import ⟨_, _, .iface items⟩ => ifaceDefs items
  | _ => []

/-- The type definitions of a document. -/
def docDefs (d : Syntax.Document) : List Wit.TypeDef := d.stmts.flatMap stmtDefs

/-- **Every type definition of the document has unique labels.** -/
def DeclsOk (d : Syntax.Document) : Prop := ∀ t ∈ docDefs d, DefOk t.kind

/-- Check a resource's functions. -/
def checkResource (r : String) (fns : List Wit.ResourceFunc) : Except VError Unit :=
  if 1 < (fns.filter isCtor).length then .error (.duplicateConstructor r)
  else andThen (noDup (.duplicateMethod r) (fns.filterMap (rfName ·.kind)))
    (allOk (fun f => noDup (.duplicateParam r) (f.func.params.map (·.1))) fns)

/-- Check one type definition. -/
def checkDef (t : Wit.TypeDef) : Except VError Unit :=
  match t.kind with
  | .alias _ => .ok ()
  | .record fs => noDup (.duplicateField t.name) (fs.map (·.name))
  | .variant cs => noDup (.duplicateCase t.name) (cs.map (·.name))
  | .enum ls => noDup (.duplicateEnumCase t.name) (ls.map (·.name))
  | .flags ls => noDup (.duplicateFlag t.name) (ls.map (·.name))
  | .resource fns => checkResource t.name fns

/-- Check the declarations of a document. -/
def checkDecls (d : Syntax.Document) : Except VError Unit := allOk checkDef (docDefs d)

/-! ## 2. Names in types -/

/-- What a name of a scope denotes, as far as types are concerned. -/
inductive Cat where
  /-- A value type (a record, variant, enum, flags or an alias of a value type). -/
  | val
  /-- A resource (or an alias of one). -/
  | res
  /-- Unknown here (a `use`d name, an import): accepted in every position. -/
  | unk
  /-- Not a type (an interface, a world, a `let`). -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- A scope: the names declared so far, in order. -/
abbrev CScope := List (String × Cat)

mutual
/-- The names a type refers to: `(false, n)` for a named type `n`, `(true, n)` for a
handle `own<n>`/`borrow<n>`. -/
def refsOf : Wit.Ty → List (Bool × String)
  | .named n => [(false, n)]
  | .own n | .borrow n => [(true, n)]
  | .list t | .option t | .fixedList t _ => refsOf t
  | .map k v => refsOf k ++ refsOf v
  | .tuple ts => refsOfList ts
  | .result a b => refsOfOpt a ++ refsOfOpt b
  | .future t | .stream t => refsOfOpt t
  | _ => []
/-- `refsOf` of an optional type. -/
def refsOfOpt : Option Wit.Ty → List (Bool × String)
  | none => []
  | some t => refsOf t
/-- `refsOf` of a list of types. -/
def refsOfList : List Wit.Ty → List (Bool × String)
  | [] => []
  | t :: ts => refsOf t ++ refsOfList ts
end

/-- Which categories a reference accepts: a handle a resource, a named type a value
type or a resource. -/
def CatOk : Bool → Cat → Prop
  | true, c => c = .res ∨ c = .unk
  | false, c => c = .val ∨ c = .res ∨ c = .unk

/-- A reference is to a name of the scope, of an accepted category. -/
def RefOk (sc : CScope) (r : Bool × String) : Prop := ∃ c, sc.lookup r.2 = some c ∧ CatOk r.1 c

/-- **A type is well scoped.** -/
def TyOk (sc : CScope) (t : Wit.Ty) : Prop := ∀ r ∈ refsOf t, RefOk sc r

/-- A function type is well scoped. -/
def FuncOk (sc : CScope) (f : Wit.Func) : Prop :=
  (∀ p ∈ f.params, TyOk sc p.2) ∧ ∀ t ∈ f.result, TyOk sc t

/-- The types a type definition mentions. -/
def defTys : Wit.TypeDefKind → List Wit.Ty
  | .alias t => [t]
  | .record fs => fs.map (·.ty)
  | .variant cs => cs.filterMap (·.ty)
  | .resource fns => fns.flatMap fun f => f.func.params.map (·.2) ++ f.func.result.toList
  | _ => []

/-- The scope a type definition's types are read in: a resource's functions see the
resource. -/
def defScope (sc : CScope) (d : Wit.TypeDef) : CScope :=
  match d.kind with
  | .resource _ => sc ++ [(d.name, .res)]
  | _ => sc

/-- The category a type definition declares. -/
def defCat (sc : CScope) (d : Wit.TypeDef) : Cat :=
  match d.kind with
  | .resource _ => .res
  | .alias (.named n) => match sc.lookup n with
    | some .res => .res
    | some .unk => .unk
    | _ => .val
  | _ => .val

/-- A type definition is well scoped. -/
def TypeDefOk (sc : CScope) (d : Wit.TypeDef) : Prop := ∀ t ∈ defTys d.kind, TyOk (defScope sc d) t

/-- The names a `use` binds. -/
def useScope (u : Wit.Use) : CScope := u.names.map fun un => (un.bound, .unk)

/-- **The items of an interface body are well scoped**, each in the scope of the items
before it. -/
def IfaceItemsOk : CScope → List Wit.IfaceItem → Prop
  | _, [] => True
  | sc, .type d :: rest => TypeDefOk sc d ∧ IfaceItemsOk (sc ++ [(d.name, defCat sc d)]) rest
  | sc, .func f :: rest => FuncOk sc f.func ∧ IfaceItemsOk sc rest
  | sc, .use u :: rest => IfaceItemsOk (sc ++ useScope u) rest

/-- A world extern is well scoped (an inline interface is a scope of its own). -/
def ExternOk (sc : CScope) : Wit.Extern → Prop
  | .func _ f => FuncOk sc f
  | .iface _ items => IfaceItemsOk [] items
  | .path _ => True

/-- **The items of a world body are well scoped.** -/
def WorldItemsOk : CScope → List Wit.WorldItem → Prop
  | _, [] => True
  | sc, .type d :: rest => TypeDefOk sc d ∧ WorldItemsOk (sc ++ [(d.name, defCat sc d)]) rest
  | sc, .use u :: rest => WorldItemsOk (sc ++ useScope u) rest
  | sc, .import e :: rest => ExternOk sc e.ext ∧ WorldItemsOk sc rest
  | sc, .export e :: rest => ExternOk sc e.ext ∧ WorldItemsOk sc rest
  | sc, .include _ :: rest => WorldItemsOk sc rest

/-- The type of an import is well scoped. -/
def ImportTyOk (sc : CScope) : Syntax.ImportType → Prop
  | .func f => FuncOk sc f
  | .iface items => IfaceItemsOk [] items
  | _ => True

/-- **The statements of a document are well scoped**, in the root scope. -/
def StmtsOk : CScope → List Syntax.Stmt → Prop
  | _, [] => True
  | sc, .type (.iface i) :: rest => IfaceItemsOk [] i.items ∧ StmtsOk (sc ++ [(i.name, .other)]) rest
  | sc, .type (.world w) :: rest => WorldItemsOk [] w.items ∧ StmtsOk (sc ++ [(w.name, .other)]) rest
  | sc, .type (.type d) :: rest => TypeDefOk sc d ∧ StmtsOk (sc ++ [(d.name, defCat sc d)]) rest
  | sc, .import i :: rest => ImportTyOk sc i.ty ∧ StmtsOk (sc ++ [(i.id, .unk)]) rest
  | sc, .let x _ :: rest => StmtsOk (sc ++ [(x, .other)]) rest
  | sc, .export _ _ :: rest => StmtsOk sc rest

/-- Check a reference. -/
def checkRef (sc : CScope) (r : Bool × String) : Except VError Unit :=
  match sc.lookup r.2, r.1 with
  | none, _ => .error (.undefinedName r.2)
  | some .unk, _ | some .res, _ | some .val, false => .ok ()
  | some .val, true => .error (.notResourceType r.2)
  | some .other, _ => .error (.invalidAlias r.2)

/-- Check a type. -/
def checkTy (sc : CScope) (t : Wit.Ty) : Except VError Unit := allOk (checkRef sc) (refsOf t)

/-- Check a function type. -/
def checkFunc (sc : CScope) (f : Wit.Func) : Except VError Unit :=
  andThen (allOk (fun p => checkTy sc p.2) f.params)
    (allOk (checkTy sc) f.result.toList)

/-- Check a type definition. -/
def checkTypeDef (sc : CScope) (d : Wit.TypeDef) : Except VError Unit :=
  allOk (checkTy (defScope sc d)) (defTys d.kind)

/-- Check the items of an interface body. -/
def checkIfaceItems : CScope → List Wit.IfaceItem → Except VError Unit
  | _, [] => .ok ()
  | sc, .type d :: rest => andThen (checkTypeDef sc d)
      (checkIfaceItems (sc ++ [(d.name, defCat sc d)]) rest)
  | sc, .func f :: rest => andThen (checkFunc sc f.func)
      (checkIfaceItems sc rest)
  | sc, .use u :: rest => checkIfaceItems (sc ++ useScope u) rest

/-- Check a world extern. -/
def checkExtern (sc : CScope) : Wit.Extern → Except VError Unit
  | .func _ f => checkFunc sc f
  | .iface _ items => checkIfaceItems [] items
  | .path _ => .ok ()

/-- Check the items of a world body. -/
def checkWorldItems : CScope → List Wit.WorldItem → Except VError Unit
  | _, [] => .ok ()
  | sc, .type d :: rest => andThen (checkTypeDef sc d)
      (checkWorldItems (sc ++ [(d.name, defCat sc d)]) rest)
  | sc, .use u :: rest => checkWorldItems (sc ++ useScope u) rest
  | sc, .import e :: rest => andThen (checkExtern sc e.ext)
      (checkWorldItems sc rest)
  | sc, .export e :: rest => andThen (checkExtern sc e.ext)
      (checkWorldItems sc rest)
  | sc, .include _ :: rest => checkWorldItems sc rest

/-- Check the type of an import. -/
def checkImportTy (sc : CScope) : Syntax.ImportType → Except VError Unit
  | .func f => checkFunc sc f
  | .iface items => checkIfaceItems [] items
  | _ => .ok ()

/-- Check the statements of a document. -/
def checkStmts : CScope → List Syntax.Stmt → Except VError Unit
  | _, [] => .ok ()
  | sc, .type (.iface i) :: rest => andThen (checkIfaceItems [] i.items)
      (checkStmts (sc ++ [(i.name, .other)]) rest)
  | sc, .type (.world w) :: rest => andThen (checkWorldItems [] w.items)
      (checkStmts (sc ++ [(w.name, .other)]) rest)
  | sc, .type (.type d) :: rest => andThen (checkTypeDef sc d)
      (checkStmts (sc ++ [(d.name, defCat sc d)]) rest)
  | sc, .import i :: rest => andThen (checkImportTy sc i.ty)
      (checkStmts (sc ++ [(i.id, .unk)]) rest)
  | sc, .let x _ :: rest => checkStmts (sc ++ [(x, .other)]) rest
  | sc, .export _ _ :: rest => checkStmts sc rest

/-! ## 3. Extern names -/

/-- A kebab-case label (wasmparser's `KebabStr`, the same words as WIT identifiers). -/
def Label (cs : List Char) : Prop := ∀ w ∈ Wit.splitDash cs, Wit.Word w

/-- A character of an interface name's version. -/
def verChar (c : Char) : Bool := c.isAlphanum || c == '.' || c == '-' || c == '+'

/-- The version of an interface name: non-empty, of `verChar`s. -/
def VerOk (v : List Char) : Prop := v ≠ [] ∧ ∀ c ∈ v, verChar c = true

/-- The prefixes of the names that are hashes, URLs or dependencies. -/
def specialPrefixes : List (List Char) :=
  ["url=<".toList, "relative-url=<".toList, "integrity=<".toList, "locked-dep=<".toList,
   "unlocked-dep=<".toList]

/-- `@v` for a version, nothing without one. -/
def verSuffix : Option (List Char) → List Char
  | none => []
  | some v => '@' :: v

open Silmaril.Wasm.Wit.Binary (pConstructor pMethod pStatic pAsync pAsyncMethod pAsyncStatic)

/-- **Component-model extern names** (wasmparser's `ComponentName`), as characters. -/
inductive ExternName : List Char → Prop
  | label {l : List Char} : Label l → ExternName l
  | ctor {r : List Char} : Label r → ExternName (pConstructor ++ r)
  | async {l : List Char} : Label l → ExternName (pAsync ++ l)
  | method {r m : List Char} : Label r → Label m → ExternName (pMethod ++ r ++ '.' :: m)
  | static {r m : List Char} : Label r → Label m → ExternName (pStatic ++ r ++ '.' :: m)
  | asyncMethod {r m : List Char} : Label r → Label m → ExternName (pAsyncMethod ++ r ++ '.' :: m)
  | asyncStatic {r m : List Char} : Label r → Label m → ExternName (pAsyncStatic ++ r ++ '.' :: m)
  | iface {ns pkg i : List Char} {v : Option (List Char)} :
      Label ns → Label pkg → Label i → (∀ s ∈ v, VerOk s) →
      ExternName (ns ++ ':' :: (pkg ++ '/' :: (i ++ verSuffix v)))
  | special {p body : List Char} : p ∈ specialPrefixes → ExternName (p ++ body ++ ['>'])

/-- A hash, URL or dependency name. -/
def Special (cs : List Char) : Prop := ∃ p ∈ specialPrefixes, ∃ body, cs = p ++ body ++ ['>']

/-- A valid import name (wac-graph's `import`). -/
def ImportNameOk (s : String) : Prop := ExternName s.toList

/-- A valid export name (wac-graph's `export`: not a hash, URL or dependency). -/
def ExportNameOk (s : String) : Prop := ExternName s.toList ∧ ¬ Special s.toList

/-- **The import and export names of a composition are valid.** -/
def NamesOk (g : CGraph) : Prop :=
  (∀ p ∈ g.imports, ImportNameOk p.1) ∧ ∀ p ∈ g.exports, ExportNameOk p.1

/-- Decide `Label`. -/
def labelB (cs : List Char) : Bool := (Wit.splitDash cs).all fun w => decide (Wit.Word w)

/-- Decide `VerOk`. -/
def verB (v : List Char) : Bool := !v.isEmpty && v.all verChar

open Silmaril.Wasm.Wit.Binary (dropPrefix? splitAt?)

/-- `r.m` with two labels. -/
def dotB (r : List Char) : Bool :=
  match splitAt? '.' r with
  | some (a, b) => labelB a && labelB b
  | none => false

/-- A name after a prefix. -/
def afterB (p : List Char) (k : List Char → Bool) (cs : List Char) : Bool :=
  match dropPrefix? p cs with
  | some r => k r
  | none => false

/-- An interface name `ns:pkg/iface(@version)?`. -/
def ifaceB (cs : List Char) : Bool :=
  match splitAt? ':' cs with
  | none => false
  | some (ns, r) => match splitAt? '/' r with
    | none => false
    | some (pkg, r2) => labelB ns && labelB pkg && match splitAt? '@' r2 with
      | some (i, v) => labelB i && verB v
      | none => labelB r2

/-- A name ending in `>` after one of the special prefixes. -/
def specialB (cs : List Char) : Bool :=
  specialPrefixes.any fun p => afterB p (fun r => r.getLast? == some '>') cs

/-- Decide (soundly) `ExternName`. -/
def externB (cs : List Char) : Bool :=
  labelB cs || afterB pConstructor labelB cs || afterB pAsync labelB cs ||
    afterB pMethod dotB cs || afterB pStatic dotB cs || afterB pAsyncMethod dotB cs ||
    afterB pAsyncStatic dotB cs || ifaceB cs || specialB cs

/-- Check the names of a composition. -/
def checkNames (g : CGraph) : Except VError Unit :=
  andThen (allOk (fun p => if externB p.1.toList then .ok () else .error (.invalidImportName p.1)) g.imports)
    (allOk (fun p => if externB p.1.toList && !specialB p.1.toList then .ok ()
      else .error (.invalidExportName p.1)) g.exports)

/-! ## 4. Borrows in results -/

/-- `borrow` occurs in a type. -/
inductive BorrowIn : Ty → Prop
  | borrow (r : TyRef) : BorrowIn (.borrow r)
  | list {t : Ty} : BorrowIn t → BorrowIn (.list t)
  | fixedList {t : Ty} {n : Nat} : BorrowIn t → BorrowIn (.fixedList t n)
  | mapK {k v : Ty} : BorrowIn k → BorrowIn (.map k v)
  | mapV {k v : Ty} : BorrowIn v → BorrowIn (.map k v)
  | option {t : Ty} : BorrowIn t → BorrowIn (.option t)
  | resultOk {t : Ty} {e : Option Ty} : BorrowIn t → BorrowIn (.result (some t) e)
  | resultErr {o : Option Ty} {t : Ty} : BorrowIn t → BorrowIn (.result o (some t))
  | tuple {t : Ty} {ts : List Ty} : t ∈ ts → BorrowIn t → BorrowIn (.tuple ts)
  | future {t : Ty} : BorrowIn t → BorrowIn (.future (some t))
  | stream {t : Ty} : BorrowIn t → BorrowIn (.stream (some t))

/-- A function type occurs in a kind. -/
inductive SigIn : Kind → Sig → Prop
  | func (s : Sig) : SigIn (.func s) s
  | type {k : Kind} {s : Sig} : SigIn k s → SigIn (.type k) s
  | inst {i : Option String} {es : Externs} {n : String} {k : Kind} {s : Sig} :
      (n, k) ∈ es → SigIn k s → SigIn (.inst i es) s
  | compI {i : Option String} {is es : Externs} {n : String} {k : Kind} {s : Sig} :
      (n, k) ∈ is → SigIn k s → SigIn (.comp i is es) s
  | compE {i : Option String} {is es : Externs} {n : String} {k : Kind} {s : Sig} :
      (n, k) ∈ es → SigIn k s → SigIn (.comp i is es) s

/-- **No function of the composition returns a borrow.** -/
def NoBorrowRes (g : CGraph) : Prop :=
  ∀ nd ∈ g.nodes, ∀ s, SigIn nd.kind s → ∀ t ∈ s.result, ¬ BorrowIn t

mutual
/-- Whether `borrow` occurs in a type. -/
def hasBorrow : Ty → Bool
  | .borrow _ => true
  | .list t | .fixedList t _ | .option t => hasBorrow t
  | .map k v => hasBorrow k || hasBorrow v
  | .result a b => hasBorrowOpt a || hasBorrowOpt b
  | .tuple ts => hasBorrowList ts
  | .future t | .stream t => hasBorrowOpt t
  | _ => false
/-- `hasBorrow` of an optional type. -/
def hasBorrowOpt : Option Ty → Bool
  | none => false
  | some t => hasBorrow t
/-- `hasBorrow` of a list of types. -/
def hasBorrowList : List Ty → Bool
  | [] => false
  | t :: ts => hasBorrow t || hasBorrowList ts
end

mutual
/-- Whether some function of a kind returns a borrow. -/
def badKind : Kind → Bool
  | .func s => hasBorrowOpt s.result
  | .value _ | .resource _ => false
  | .type k => badKind k
  | .inst _ es => badEx es
  | .comp _ is es => badEx is || badEx es
/-- `badKind` of named items. -/
def badEx : Externs → Bool
  | [] => false
  | (_, k) :: es => badKind k || badEx es
end

/-- Check the kinds of a composition. -/
def checkBorrows (g : CGraph) : Except VError Unit :=
  allOk (fun nd => if badKind nd.kind then .error .borrowInResult else .ok ()) g.nodes

/-! ## 5. Structural comparison of nominal types -/

open Bridge (Nominal NomTable)

/-- The definition a reference resolves to in a table: local references only. -/
def nomOf (A : NomTable) (r : TyRef) : Option Nominal :=
  match r.owner with
  | .local => A.lookup r.name
  | _ => none

mutual
/-- **Structural equality of value types** under the tables `A` (left) and `B`
(right). -/
inductive TyEqS : NomTable → NomTable → Ty → Ty → Prop
  | prim {A B : NomTable} (p : Silmaril.Wasm.Component.Binary.PrimValType) :
      TyEqS A B (.prim p) (.prim p)
  | refOpaque {A B : NomTable} {r : TyRef} : nomOf A r = none ∨ nomOf B r = none →
      TyEqS A B (.ref r) (.ref r)
  | refNom {A B : NomTable} {r r' : TyRef} {a b : Nominal} : nomOf A r = some a →
      nomOf B r' = some b → NomEqS A B a b → TyEqS A B (.ref r) (.ref r')
  | list {A B : NomTable} {t u : Ty} : TyEqS A B t u → TyEqS A B (.list t) (.list u)
  | fixedList {A B : NomTable} {t u : Ty} (n : Nat) : TyEqS A B t u →
      TyEqS A B (.fixedList t n) (.fixedList u n)
  | map {A B : NomTable} {k v k' v' : Ty} : TyEqS A B k k' → TyEqS A B v v' →
      TyEqS A B (.map k v) (.map k' v')
  | option {A B : NomTable} {t u : Ty} : TyEqS A B t u → TyEqS A B (.option t) (.option u)
  | result {A B : NomTable} {a b a' b' : Option Ty} : OptEqS A B a a' → OptEqS A B b b' →
      TyEqS A B (.result a b) (.result a' b')
  | tuple {A B : NomTable} {ts us : List Ty} : TysEqS A B ts us → TyEqS A B (.tuple ts) (.tuple us)
  | own {A B : NomTable} (r : TyRef) : TyEqS A B (.own r) (.own r)
  | borrow {A B : NomTable} (r : TyRef) : TyEqS A B (.borrow r) (.borrow r)
  | future {A B : NomTable} {a a' : Option Ty} : OptEqS A B a a' → TyEqS A B (.future a) (.future a')
  | stream {A B : NomTable} {a a' : Option Ty} : OptEqS A B a a' → TyEqS A B (.stream a) (.stream a')
/-- `TyEqS` of optional types. -/
inductive OptEqS : NomTable → NomTable → Option Ty → Option Ty → Prop
  | none {A B : NomTable} : OptEqS A B none none
  | some {A B : NomTable} {t u : Ty} : TyEqS A B t u → OptEqS A B (some t) (some u)
/-- `TyEqS` of lists of types, pointwise. -/
inductive TysEqS : NomTable → NomTable → List Ty → List Ty → Prop
  | nil {A B : NomTable} : TysEqS A B [] []
  | cons {A B : NomTable} {t u : Ty} {ts us : List Ty} : TyEqS A B t u → TysEqS A B ts us →
      TysEqS A B (t :: ts) (u :: us)
/-- Named types (record fields, parameters), pointwise with equal names. -/
inductive FieldsEqS : NomTable → NomTable → List (String × Ty) → List (String × Ty) → Prop
  | nil {A B : NomTable} : FieldsEqS A B [] []
  | cons {A B : NomTable} {n : String} {t u : Ty} {fs gs : List (String × Ty)} :
      TyEqS A B t u → FieldsEqS A B fs gs → FieldsEqS A B ((n, t) :: fs) ((n, u) :: gs)
/-- Variant cases, pointwise with equal names and the same payloads. -/
inductive CasesEqS : NomTable → NomTable → List (String × Option Ty) → List (String × Option Ty) → Prop
  | nil {A B : NomTable} : CasesEqS A B [] []
  | cons {A B : NomTable} {n : String} {t u : Option Ty} {cs ds : List (String × Option Ty)} :
      OptEqS A B t u → CasesEqS A B cs ds → CasesEqS A B ((n, t) :: cs) ((n, u) :: ds)
/-- **Structural equality of nominal definitions** (wac's checker: the same labels in
the same order, structurally equal types). -/
inductive NomEqS : NomTable → NomTable → Nominal → Nominal → Prop
  | record {A B : NomTable} {fs gs : List (String × Ty)} : FieldsEqS A B fs gs →
      NomEqS A B (.record fs) (.record gs)
  | variant {A B : NomTable} {cs ds : List (String × Option Ty)} : CasesEqS A B cs ds →
      NomEqS A B (.variant cs) (.variant ds)
  | enum {A B : NomTable} (ls : List String) : NomEqS A B (.enum ls) (.enum ls)
  | flags {A B : NomTable} (ls : List String) : NomEqS A B (.flags ls) (.flags ls)
end

/-- Structural equality of function types. -/
def SigEqS (A B : NomTable) (s s' : Sig) : Prop :=
  s.async = s'.async ∧ FieldsEqS A B s.params s'.params ∧ OptEqS A B s.result s'.result

mutual
/-- **Structural subtyping** `SubS A B a b`: `Sub` with value and function types
compared structurally (`a` read in `A`, `b` in `B`; the tables swap for the
contravariant imports of components). -/
inductive SubS : NomTable → NomTable → Kind → Kind → Prop
  | func {A B : NomTable} {s s' : Sig} : SigEqS A B s s' → SubS A B (.func s) (.func s')
  | value {A B : NomTable} {t u : Ty} : TyEqS A B t u → SubS A B (.value t) (.value u)
  | resource {A B : NomTable} (r : String) : SubS A B (.resource r) (.resource r)
  | type {A B : NomTable} {a b : Kind} : SubS A B a b → SubS A B (.type a) (.type b)
  | inst {A B : NomTable} {i j : Option String} {as bs : Externs} : SubExS A B as bs →
      SubS A B (.inst i as) (.inst j bs)
  | comp {A B : NomTable} {i j : Option String} {ai ae bi be : Externs} :
      SubExS B A bi ai → SubExS A B ae be → SubS A B (.comp i ai ae) (.comp j bi be)
/-- Every item `(k, b)` of `bs` has an item `(k, a)` of `as` with `SubS A B a b`. -/
inductive SubExS : NomTable → NomTable → Externs → Externs → Prop
  | nil {A B : NomTable} (as : Externs) : SubExS A B as []
  | cons {A B : NomTable} {as bs : Externs} {k : String} {a b : Kind} :
      (k, a) ∈ as → SubS A B a b → SubExS A B as bs → SubExS A B as ((k, b) :: bs)
end

/-! ### The checker, with fuel (every recursive call uses one unit) -/

mutual
/-- Decide (soundly) `TyEqS`. -/
def tyEqS : Nat → NomTable → NomTable → Ty → Ty → Bool
  | 0, _, _, _, _ => false
  | n + 1, A, B, t, u => match t, u with
    | .prim p, .prim q => p == q
    | .ref r, .ref r' => match nomOf A r, nomOf B r' with
      | some a, some b => nomEqS n A B a b
      | _, _ => r == r'
    | .list t, .list u | .option t, .option u => tyEqS n A B t u
    | .fixedList t k, .fixedList u k' => k == k' && tyEqS n A B t u
    | .map k v, .map k' v' => tyEqS n A B k k' && tyEqS n A B v v'
    | .result a b, .result a' b' => optEqS n A B a a' && optEqS n A B b b'
    | .tuple ts, .tuple us => tysEqS n A B ts us
    | .own r, .own r' | .borrow r, .borrow r' => r == r'
    | .future a, .future a' | .stream a, .stream a' => optEqS n A B a a'
    | _, _ => false
/-- Decide (soundly) `OptEqS`. -/
def optEqS : Nat → NomTable → NomTable → Option Ty → Option Ty → Bool
  | 0, _, _, _, _ => false
  | _ + 1, _, _, none, none => true
  | n + 1, A, B, some t, some u => tyEqS n A B t u
  | _ + 1, _, _, _, _ => false
/-- Decide (soundly) `TysEqS`. -/
def tysEqS : Nat → NomTable → NomTable → List Ty → List Ty → Bool
  | 0, _, _, _, _ => false
  | _ + 1, _, _, [], [] => true
  | n + 1, A, B, t :: ts, u :: us => tyEqS n A B t u && tysEqS n A B ts us
  | _ + 1, _, _, _, _ => false
/-- Decide (soundly) `FieldsEqS`. -/
def fieldsEqS : Nat → NomTable → NomTable → List (String × Ty) → List (String × Ty) → Bool
  | 0, _, _, _, _ => false
  | _ + 1, _, _, [], [] => true
  | n + 1, A, B, (k, t) :: fs, (k', u) :: gs => k == k' && tyEqS n A B t u && fieldsEqS n A B fs gs
  | _ + 1, _, _, _, _ => false
/-- Decide (soundly) `CasesEqS`. -/
def casesEqS : Nat → NomTable → NomTable → List (String × Option Ty) → List (String × Option Ty) → Bool
  | 0, _, _, _, _ => false
  | _ + 1, _, _, [], [] => true
  | n + 1, A, B, (k, t) :: cs, (k', u) :: ds => k == k' && optEqS n A B t u && casesEqS n A B cs ds
  | _ + 1, _, _, _, _ => false
/-- Decide (soundly) `NomEqS`. -/
def nomEqS : Nat → NomTable → NomTable → Nominal → Nominal → Bool
  | 0, _, _, _, _ => false
  | n + 1, A, B, .record fs, .record gs => fieldsEqS n A B fs gs
  | n + 1, A, B, .variant cs, .variant ds => casesEqS n A B cs ds
  | _ + 1, _, _, .enum ls, .enum ls' => ls == ls'
  | _ + 1, _, _, .flags ls, .flags ls' => ls == ls'
  | _ + 1, _, _, _, _ => false
end

/-- Decide (soundly) `SigEqS`. -/
def sigEqS (n : Nat) (A B : NomTable) (s s' : Sig) : Bool :=
  s.async == s'.async && fieldsEqS n A B s.params s'.params && optEqS n A B s.result s'.result

mutual
/-- Decide (soundly) `SubS`. -/
def subS : Nat → NomTable → NomTable → Kind → Kind → Bool
  | 0, _, _, _, _ => false
  | n + 1, A, B, a, b => match a, b with
    | .func s, .func s' => sigEqS n A B s s'
    | .value t, .value u => tyEqS n A B t u
    | .resource r, .resource r' => r == r'
    | .type a, .type b => subS n A B a b
    | .inst _ as, .inst _ bs => subExS n A B as bs
    | .comp _ ai ae, .comp _ bi be => subExS n B A bi ai && subExS n A B ae be
    | _, _ => false
/-- Decide (soundly) `SubExS`. -/
def subExS : Nat → NomTable → NomTable → Externs → Externs → Bool
  | 0, _, _, _, _ => false
  | _ + 1, _, _, _, [] => true
  | n + 1, A, B, as, (k, b) :: bs => anyMatchS n A B as k b && subExS n A B as bs
/-- Some item `(k, a)` of `as` has `subS A B a b`. -/
def anyMatchS : Nat → NomTable → NomTable → Externs → String → Kind → Bool
  | 0, _, _, _, _, _ => false
  | _ + 1, _, _, [], _, _ => false
  | n + 1, A, B, (k', a) :: as, k, b => (k' == k && subS n A B a b) || anyMatchS n A B as k b
end

/-- The fuel of the structural checks. -/
def fuel : Nat := 100000

/-! ### Where kinds come from -/

/-- The origin of a kind: the document, or a package of the registry. -/
inductive Origin where
  | doc
  | pkg (key : String)
  deriving Repr, DecidableEq, Inhabited

/-- The definition tables: the document's, and each package's by key. -/
structure Tables where
  doc : NomTable := []
  pkgs : List (String × NomTable) := []
  deriving Inhabited

/-- The table of an origin. -/
def Tables.of (T : Tables) : Origin → NomTable
  | .doc => T.doc
  | .pkg k => (T.pkgs.lookup k).getD []

/-- The package of an interface or world identifier `ns:pkg/name@v` (the registry key
`ns:pkg@v`, else `ns:pkg`), unless it is the document's own or not in the registry. -/
def idOrigin (env : PkgEnv) (doc : String) (id : String) : Origin :=
  match WitDecl.ifaceNameOf id with
  | some I =>
    let k := WitDecl.pkgKeyOf I.pkg
    let k0 := I.pkg.ns ++ ":" ++ I.pkg.name
    if k = doc ∨ k0 = doc then .doc
    else if (env.lookup k).isSome then .pkg k
    else if (env.lookup k0).isSome then .pkg k0
    else .doc
  | none => .doc

/-- The identifier of an instance or component kind. -/
def kindId : Kind → Option String
  | .inst (some id) _ | .comp (some id) _ _ => some id
  | _ => none

/-- The package of an implicit import: the first instantiation importing its name. -/
def implicitOrigin (g : CGraph) (n : String) : Origin :=
  match g.nodes.findSome? (fun nd => match nd.op with
      | .inst p imps _ => if (Externs.find imps n).isSome then some p else none
      | _ => none) with
  | some p => .pkg p
  | none => .doc

/-- The origin of node `i` (with fuel, for alias chains). -/
def originN (env : PkgEnv) (doc : String) (g : CGraph) : Nat → Nat → Origin
  | 0, _ => .doc
  | f + 1, i => match g.opOf? i with
    | some (.inst p _ _) => .pkg p
    | some (.alias src _) => originN env doc g f src
    | some (.implicit n) => implicitOrigin g n
    | some (.imp _) => match kindId (g.kindOf i) with
      | some id => idOrigin env doc id
      | none => .doc
    | _ => .doc

/-- The origin of node `i`. -/
def origin (env : PkgEnv) (doc : String) (g : CGraph) (i : Nat) : Origin :=
  originN env doc g g.nodes.length i

/-- **Instantiation arguments match structurally**: every argument `(n, j)` of an
instantiation of `p` is a structural subtype of `p`'s import `n`, its kind read in the
table of its origin, the import in `p`'s table. -/
def ArgsOk (T : Tables) (env : PkgEnv) (doc : String) (g : CGraph) : Prop :=
  ∀ nd ∈ g.nodes, ∀ p imps args, nd.op = .inst p imps args →
    ∀ a ∈ args, ∀ k, Externs.find imps a.1 = some k →
      SubS (T.of (origin env doc g a.2)) (T.of (.pkg p)) (g.kindOf a.2) k

/-- Check the arguments of one node. -/
def checkNodeArgs (T : Tables) (env : PkgEnv) (doc : String) (g : CGraph) (nd : CNode) :
    Except VError Unit :=
  match nd.op with
  | .inst p imps args => allOk (fun a => match Externs.find imps a.1 with
      | some k => if subS fuel (T.of (origin env doc g a.2)) (T.of (.pkg p)) (g.kindOf a.2) k then .ok ()
        else .error (.mismatchedArg p a.1)
      | none => .ok ()) args
  | _ => .ok ()

/-- Check every instantiation's arguments. -/
def checkArgsS (T : Tables) (env : PkgEnv) (doc : String) (g : CGraph) : Except VError Unit :=
  allOk (checkNodeArgs T env doc g) g.nodes

/-! ### The `targets` world -/

/-- The kind a `targets` path names, and its origin: a declaration of the document (an
exported definition of the graph) or a definition of a package. -/
def targetKind (env : PkgEnv) (d : Syntax.Document) (g : CGraph) : Option (Kind × Origin) :=
  match d.targets with
  | none => none
  | some p => match p.segments with
    | [] => none
    | s :: ss =>
      if p.pkg = d.pkg.name then
        ((g.exports.lookup s).bind fun j => walkKind (g.kindOf j) ss).map (·, .doc)
      else
        let key := Syntax.PkgName.key ⟨p.pkg, p.version⟩
        ((env.lookup key).bind fun pk => (pk.defs.find s).bind fun k => walkKind k ss).map (·, .pkg key)

/-- The import nodes of a graph: index, name and kind. -/
def importNodes (g : CGraph) : List (Nat × String × Kind) :=
  (List.range g.nodes.length).filterMap fun i => match g.nodes[i]? with
    | some nd => match nd.op with
      | .imp n | .implicit n => some (i, n, nd.kind)
      | _ => none
    | none => none

/-- **The `targets` world is satisfied structurally**: every import of the composition
that the world imports is a structural supertype of the world's import, and every
export of the world that the composition exports is a structural supertype of the
composition's export (`checkTarget` already requires the names). -/
def TargetsOk (T : Tables) (env : PkgEnv) (d : Syntax.Document) (g : CGraph) : Prop :=
  ∀ i wi we o, targetKind env d g = some (.type (.comp i wi we), o) →
    (∀ q ∈ importNodes g, ∀ k', Externs.find wi q.2.1 = some k' →
      SubS (T.of o) (T.of (origin env d.pkg.key g q.1)) k'.promote q.2.2) ∧
    (∀ q ∈ we, ∀ j, g.exports.lookup q.1 = some j →
      SubS (T.of (origin env d.pkg.key g j)) (T.of o) (g.kindOf j) q.2.promote)

/-- Check the `targets` world. -/
def checkTargetsS (T : Tables) (env : PkgEnv) (d : Syntax.Document) (g : CGraph) : Except VError Unit :=
  match targetKind env d g with
  | some (.type (.comp _ wi we), o) =>
    andThen (allOk (fun q => match Externs.find wi q.2.1 with
        | some k' => if subS fuel (T.of o) (T.of (origin env d.pkg.key g q.1)) k'.promote q.2.2 then .ok ()
          else .error (.targetMismatch q.2.1)
        | none => .ok ()) (importNodes g))
      (allOk (fun q => match g.exports.lookup q.1 with
        | some j => if subS fuel (T.of (origin env d.pkg.key g j)) (T.of o) (g.kindOf j) q.2.promote then .ok ()
          else .error (.targetMismatch q.1)
        | none => .ok ()) we)
  | _ => .ok ()

/-! ## Everything together -/

/-- **What validation requires of a document.** -/
structure DocOk (d : Syntax.Document) : Prop where
  decls : DeclsOk d
  scopes : StmtsOk [] d.stmts

/-- **What validation requires of its composition graph.** -/
structure GraphOk (T : Tables) (env : PkgEnv) (d : Syntax.Document) (g : CGraph) : Prop where
  names : NamesOk g
  borrows : NoBorrowRes g
  args : ArgsOk T env d.pkg.key g
  targets : TargetsOk T env d g

/-- Check a document. -/
def checkDoc (d : Syntax.Document) : Except VError Unit :=
  andThen (checkDecls d)
    (checkStmts [] d.stmts)

/-- Check a composition graph. -/
def checkGraph (T : Tables) (env : PkgEnv) (d : Syntax.Document) (g : CGraph) : Except VError Unit :=
  andThen (checkNames g) (andThen (checkBorrows g)
    (andThen (checkArgsS T env d.pkg.key g) (checkTargetsS T env d g)))

/-- An error of elaboration with validation. -/
inductive VElabError where
  | elab (e : ElabError)
  | valid (e : VError)
  deriving Repr

/-- **Elaboration with validation**: the document checks, `elabDocA`, then the graph
checks (against the registry with its aliases expanded, as `elabDocA` sees it). -/
def elabDocV (T : Tables) (env : PkgEnv) (d : Syntax.Document) : Except VElabError CGraph :=
  match checkDoc d with
  | .error e => .error (.valid e)
  | .ok () => match elabDocA env d with
    | .error e => .error (.elab e)
    | .ok g => match checkGraph T env.expand d g with
      | .ok () => .ok g
      | .error e => .error (.valid e)

end Valid

end Silmaril.Wasm.Wac
