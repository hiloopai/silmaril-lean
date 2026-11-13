module

public import Silmaril.Wasm.Component.Binary.Defs

/-!
# Resolved WIT packages: the model the binary encoding works on

The WIT binary encoding (wit-component's `encode`, see `tools/wasm-tools/README.md`) does not
encode WIT *text*: it encodes a *resolved* package, after `use` statements,
`include`s, feature gates and implicit world imports have been elaborated by
the resolver. This module is that resolved form, kept close to wit-parser's
`Resolve` (wit-parser `0.263.0`, `src/lib.rs`):

* a type reference names its owner (`Owner.local` is the interface or world
  the reference occurs in, `Owner.iface` another interface) and a type name;
  anonymous types (`list<T>`, `option<T>`, `tuple<…>`, `own<R>`, …) are trees
  (`Ty`), so two structurally equal anonymous types are equal, as after
  wit-parser's interning of anonymous types;
* a named type's kind (`TyDefKind`) mirrors wit-parser's `TypeDefKind`: `type
  x = list<u8>` is the kind `.type (.list (.prim .u8))`, `use i.{t}` is the kind
  `.type (.ref ⟨.iface i, "t"⟩)`, and a resource name used as a value type is
  `own<R>` (`Ty.own`);
* functions carry their kind (freestanding, method, static, constructor) and
  their explicit parameter list (methods include `self: borrow<R>`);
* world items are elaborated imports and exports.

This is the *local interface* of the binary track: the WIT AST and resolver
(`Silmaril/Wasm/Wit/Ast`, separate track) produce it, the binary encoder consumes
it. Docs and stability are kept on every item that wit-parser keeps them on.
Version strings are kept as text (`"0.2.0"`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary (PrimValType)

/-- `@since` / `@unstable` / `@deprecated` gates, as wit-parser's `Stability`. -/
inductive Stability where
  | unknown
  | unstable (feature : String) (deprecated : Option String)
  | stable (since : String) (deprecated : Option String)
  deriving Repr, DecidableEq, Inhabited

/-- A package name `ns:name@version`. -/
structure PackageName where
  ns : String
  name : String
  version : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- An interface of a package: `ns:name/iface@version`. -/
structure IfaceName where
  pkg : PackageName
  name : String
  deriving Repr, DecidableEq, Inhabited

/-- The owner of a named type: the item the reference occurs in, or another
interface. -/
inductive Owner where
  | local
  | iface (i : IfaceName)
  deriving Repr, DecidableEq, Inhabited

/-- A reference to a named type. -/
structure TyRef where
  owner : Owner
  name : String
  deriving Repr, DecidableEq, Inhabited

/-- WIT value types after resolution. -/
inductive Ty where
  | prim (p : PrimValType)
  | ref (r : TyRef)
  | list (t : Ty)
  | fixedList (t : Ty) (n : Nat)
  | map (k v : Ty)
  | option (t : Ty)
  | result (ok err : Option Ty)
  | tuple (ts : List Ty)
  | own (r : TyRef)
  | borrow (r : TyRef)
  | future (t : Option Ty)
  | stream (t : Option Ty)
  deriving Repr, Inhabited

mutual
/-- Decidable equality of types (not derivable for the nested inductive). -/
def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .prim a, .prim b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .ref a, .ref b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .list a, .list b => match Ty.decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .fixedList a n, .fixedList b m => match Ty.decEq a b, Nat.decEq n m with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .map a a', .map b b' => match Ty.decEq a b, Ty.decEq a' b' with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .option a, .option b => match Ty.decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .result a a', .result b b' => match Ty.decEqOpt a b, Ty.decEqOpt a' b' with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .tuple a, .tuple b => match Ty.decEqList a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .own a, .own b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .borrow a, .borrow b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .future a, .future b => match Ty.decEqOpt a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .stream a, .stream b => match Ty.decEqOpt a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .prim _, .ref _ | .prim _, .list _ | .prim _, .fixedList _ _ | .prim _, .map _ _
  | .prim _, .option _ | .prim _, .result _ _ | .prim _, .tuple _ | .prim _, .own _
  | .prim _, .borrow _ | .prim _, .future _ | .prim _, .stream _ | .ref _, .prim _
  | .ref _, .list _ | .ref _, .fixedList _ _ | .ref _, .map _ _ | .ref _, .option _
  | .ref _, .result _ _ | .ref _, .tuple _ | .ref _, .own _ | .ref _, .borrow _
  | .ref _, .future _ | .ref _, .stream _ | .list _, .prim _ | .list _, .ref _
  | .list _, .fixedList _ _ | .list _, .map _ _ | .list _, .option _ | .list _, .result _ _
  | .list _, .tuple _ | .list _, .own _ | .list _, .borrow _ | .list _, .future _
  | .list _, .stream _ | .fixedList _ _, .prim _ | .fixedList _ _, .ref _ | .fixedList _ _, .list _
  | .fixedList _ _, .map _ _ | .fixedList _ _, .option _ | .fixedList _ _, .result _ _ | .fixedList _ _, .tuple _
  | .fixedList _ _, .own _ | .fixedList _ _, .borrow _ | .fixedList _ _, .future _ | .fixedList _ _, .stream _
  | .map _ _, .prim _ | .map _ _, .ref _ | .map _ _, .list _ | .map _ _, .fixedList _ _
  | .map _ _, .option _ | .map _ _, .result _ _ | .map _ _, .tuple _ | .map _ _, .own _
  | .map _ _, .borrow _ | .map _ _, .future _ | .map _ _, .stream _ | .option _, .prim _
  | .option _, .ref _ | .option _, .list _ | .option _, .fixedList _ _ | .option _, .map _ _
  | .option _, .result _ _ | .option _, .tuple _ | .option _, .own _ | .option _, .borrow _
  | .option _, .future _ | .option _, .stream _ | .result _ _, .prim _ | .result _ _, .ref _
  | .result _ _, .list _ | .result _ _, .fixedList _ _ | .result _ _, .map _ _ | .result _ _, .option _
  | .result _ _, .tuple _ | .result _ _, .own _ | .result _ _, .borrow _ | .result _ _, .future _
  | .result _ _, .stream _ | .tuple _, .prim _ | .tuple _, .ref _ | .tuple _, .list _
  | .tuple _, .fixedList _ _ | .tuple _, .map _ _ | .tuple _, .option _ | .tuple _, .result _ _
  | .tuple _, .own _ | .tuple _, .borrow _ | .tuple _, .future _ | .tuple _, .stream _
  | .own _, .prim _ | .own _, .ref _ | .own _, .list _ | .own _, .fixedList _ _
  | .own _, .map _ _ | .own _, .option _ | .own _, .result _ _ | .own _, .tuple _
  | .own _, .borrow _ | .own _, .future _ | .own _, .stream _ | .borrow _, .prim _
  | .borrow _, .ref _ | .borrow _, .list _ | .borrow _, .fixedList _ _ | .borrow _, .map _ _
  | .borrow _, .option _ | .borrow _, .result _ _ | .borrow _, .tuple _ | .borrow _, .own _
  | .borrow _, .future _ | .borrow _, .stream _ | .future _, .prim _ | .future _, .ref _
  | .future _, .list _ | .future _, .fixedList _ _ | .future _, .map _ _ | .future _, .option _
  | .future _, .result _ _ | .future _, .tuple _ | .future _, .own _ | .future _, .borrow _
  | .future _, .stream _ | .stream _, .prim _ | .stream _, .ref _ | .stream _, .list _
  | .stream _, .fixedList _ _ | .stream _, .map _ _ | .stream _, .option _ | .stream _, .result _ _
  | .stream _, .tuple _ | .stream _, .own _ | .stream _, .borrow _ | .stream _, .future _ =>
    isFalse (by intro e; cases e)

def Ty.decEqOpt : (a b : Option Ty) → Decidable (a = b)
  | none, none => isTrue rfl
  | some a, some b => match Ty.decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | none, some _ => isFalse (by intro e; cases e)
  | some _, none => isFalse (by intro e; cases e)

def Ty.decEqList : (a b : List Ty) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs => match Ty.decEq a b, Ty.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq Ty := Ty.decEq

/-- A record field, variant case, enum case or flag with its doc comment. -/
structure Labeled (α : Type) where
  name : String
  ty : α
  docs : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- The kind of a named type (wit-parser's `TypeDefKind`). `type x = t` is
`.type t`; wit-component encodes a `.type` kind whose `t` is a reference by
that reference, and any other `.type` kind as a fresh definition. -/
inductive TyDefKind where
  | record (fields : List (Labeled Ty))
  | variant (cases : List (Labeled (Option Ty)))
  | enum (cases : List (Labeled Unit))
  | flags (flags : List (Labeled Unit))
  | resource
  | type (t : Ty)
  deriving Repr, DecidableEq, Inhabited

/-- A named type definition. -/
structure TypeDef where
  name : String
  kind : TyDefKind
  docs : Option String := none
  stability : Stability := .unknown
  deriving Repr, DecidableEq, Inhabited

/-- Function kinds; the resource is named by its (local) type name. -/
inductive FuncKind where
  | freestanding
  | method (resource : String)
  | static (resource : String)
  | constructor (resource : String)
  deriving Repr, DecidableEq, Inhabited

/-- A function. For a constructor, `name` is the resource name. -/
structure Func where
  name : String
  kind : FuncKind := .freestanding
  async : Bool := false
  params : List (String × Ty)
  result : Option Ty := none
  docs : Option String := none
  stability : Stability := .unknown
  deriving Repr, DecidableEq, Inhabited

/-- A function signature: wit-component's `FunctionKey`. -/
structure Sig where
  async : Bool
  params : List (String × Ty)
  result : Option Ty
  deriving Repr, DecidableEq, Inhabited

def Func.sig (f : Func) : Sig := ⟨f.async, f.params, f.result⟩

/-- An interface body. -/
structure Interface where
  types : List TypeDef := []
  funcs : List Func := []
  docs : Option String := none
  stability : Stability := .unknown
  deriving Repr, DecidableEq, Inhabited

/-- A world import or export. -/
inductive WorldItem where
  /-- `import ns:pkg/iface@v;` (the interface's body is in the environment). -/
  | ifaceRef (i : IfaceName) (docs : Option String := none) (stability : Stability := .unknown)
  /-- `import name: interface { … }` (also a plain name for a named interface
  is not covered: see `tools/wasm-tools/README.md`). -/
  | ifaceInline (name : String) (body : Interface)
  | func (f : Func)
  /-- A type in a world (imports only). -/
  | type (t : TypeDef)
  deriving Repr, DecidableEq, Inhabited

/-- A world. -/
structure World where
  imports : List WorldItem := []
  exports : List WorldItem := []
  docs : Option String := none
  stability : Stability := .unknown
  deriving Repr, DecidableEq, Inhabited

/-- A package: its name, docs, interfaces and worlds in order. -/
structure Package where
  name : PackageName
  docs : Option String := none
  interfaces : List (String × Interface) := []
  worlds : List (String × World) := []
  deriving Repr, DecidableEq, Inhabited

/-- The interfaces an encoding may refer to, with their bodies: the package's
own interfaces and those of its dependencies. -/
abbrev Env := List (IfaceName × Interface)

/-! ## Names in the binary -/

/-- `ns:name`. -/
def PackageName.prefix (p : PackageName) : List Char :=
  p.ns.toList ++ ':' :: p.name.toList

/-- `@version` or nothing. -/
def versionSuffix : Option String → List Char
  | none => []
  | some v => '@' :: v.toList

/-- `ns:name/iface@version`, the import/export name of an interface. -/
def IfaceName.idChars (i : IfaceName) : List Char :=
  i.pkg.prefix ++ '/' :: (i.name.toList ++ versionSuffix i.pkg.version)

def IfaceName.id (i : IfaceName) : String := String.ofList i.idChars

/-- The interface `name` of package `p`. -/
def PackageName.iface (p : PackageName) (name : String) : IfaceName := ⟨p, name⟩

/-- The prefixes of function names, as characters. -/
def pConstructor : List Char := ['[', 'c', 'o', 'n', 's', 't', 'r', 'u', 'c', 't', 'o', 'r', ']']
def pMethod : List Char := ['[', 'm', 'e', 't', 'h', 'o', 'd', ']']
def pStatic : List Char := ['[', 's', 't', 'a', 't', 'i', 'c', ']']
def pAsync : List Char := ['[', 'a', 's', 'y', 'n', 'c', ']']
def pAsyncMethod : List Char := ['[', 'a', 's', 'y', 'n', 'c', ' ', 'm', 'e', 't', 'h', 'o', 'd', ']']
def pAsyncStatic : List Char := ['[', 'a', 's', 'y', 'n', 'c', ' ', 's', 't', 'a', 't', 'i', 'c', ']']

/-- The binary name of a function: `f`, `[async]f`, `[method]r.f`,
`[async method]r.f`, `[static]r.f`, `[async static]r.f`, `[constructor]r`. -/
def Func.mangledChars (f : Func) : List Char :=
  match f.kind with
  | .freestanding => (if f.async then pAsync else []) ++ f.name.toList
  | .method r => (if f.async then pAsyncMethod else pMethod) ++ r.toList ++ '.' :: f.name.toList
  | .static r => (if f.async then pAsyncStatic else pStatic) ++ r.toList ++ '.' :: f.name.toList
  | .constructor r => pConstructor ++ r.toList

def Func.mangled (f : Func) : String := String.ofList f.mangledChars

/-- The resource a function belongs to. -/
def FuncKind.resource? : FuncKind → Option String
  | .freestanding => none
  | .method r | .static r | .constructor r => some r

end Silmaril.Wasm.Wit.Binary
