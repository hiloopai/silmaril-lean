module

/-!
# WIT: abstract syntax

The abstract syntax of WIT (WebAssembly Interface Types), following `design/mvp/WIT.md`
of WebAssembly/component-model at commit `8505ba73dda2775b9438c0b8d169b96a556f864a`
(the revision `Silmaril.Wasm.Component.Binary` follows) and the AST of `wit-parser`
(bytecodealliance/wasm-tools). It is the output of a WIT text parser after lexing:
identifiers have lost their `%` escape, doc comments (`///` and `/** … */`) are kept
as `Docs`, other comments and whitespace are gone, and items keep their source order.

* `Version`: a semantic version (`1.2.3-pre.1+build`).
* `PackageName`: `namespace:name@version`.
* `Gate`: the feature-gate attributes `@since(version = …)`, `@unstable(feature = …)`,
  `@deprecated(version = …)`; `Stability` is what a valid list of them means.
* `Ty`: type expressions: primitives, `list<T>`, `list<T, N>`, `map<K, V>`, `tuple<…>`,
  `option<T>`, `result<T, E>` (each side optional), `own<R>`, `borrow<R>`,
  `future<T>`/`future`, `stream<T>`/`stream`, `error-context`, and names.
* `TypeDef`: `type x = T;`, `record`, `variant`, `enum`, `flags` and `resource` (with
  constructor, methods and static functions).
* `Use`: `use path.{a, b as c};` with `UsePath` a local interface or
  `ns:pkg/iface@version`.
* `Interface`, `World` (imports and exports of named functions, named inline
  interfaces and interface paths; `use`; type definitions; `include … with { a as b }`),
  `Package` (interfaces, worlds and top-level `use … as …;`) and `Document`
  (a main package together with nested `package ns:name { … }` blocks).

Every declaration carries its `Docs` and its gates. Name resolution and validation
are in `Silmaril.Wasm.Wit.Resolve` and `Silmaril.Wasm.Wit.Valid`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit

/-- A WIT identifier, without its `%` escape. Validity (kebab case) is `ValidId`. -/
abbrev Name := String

/-- A semantic version `major.minor.patch(-pre)?(+build)?`; `pre` and `build` are the
dot-separated identifiers. -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  pre : List String := []
  build : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- A package name `ns:name@version`. -/
structure PackageName where
  ns : Name
  name : Name
  version : Option Version := none
  deriving Repr, DecidableEq, Inhabited

/-- Documentation: the doc comments of a declaration, joined by newlines with their
comment markers removed (wit-parser's `Docs`). -/
structure Docs where
  contents : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- A feature-gate attribute. -/
inductive Gate where
  /-- `@since(version = v)`. -/
  | since (v : Version)
  /-- `@unstable(feature = f)`. -/
  | unstable (feature : Name)
  /-- `@deprecated(version = v)`. -/
  | deprecated (v : Version)
  deriving Repr, DecidableEq, Inhabited

/-- The stability of an item (wit-parser's `Stability`). -/
inductive Stability where
  /-- No gate. -/
  | unknown
  /-- `@since(version = since)`, possibly `@deprecated`. -/
  | stable (since : Version) (deprecated : Option Version)
  /-- `@unstable(feature = f)`, possibly `@deprecated`. -/
  | unstable (feature : Name) (deprecated : Option Version)
  deriving Repr, DecidableEq, Inhabited

/-- The stability a list of gates denotes, if it is one of the accepted combinations:
none, one `@since` or `@unstable`, optionally with one `@deprecated` (in either order). -/
def Gate.stability : List Gate → Option Stability
  | [] => some .unknown
  | [.since v] => some (.stable v none)
  | [.unstable f] => some (.unstable f none)
  | [.since v, .deprecated d] | [.deprecated d, .since v] => some (.stable v (some d))
  | [.unstable f, .deprecated d] | [.deprecated d, .unstable f] => some (.unstable f (some d))
  | _ => none

/-- WIT type expressions. -/
inductive Ty where
  | bool | s8 | s16 | s32 | s64 | u8 | u16 | u32 | u64 | f32 | f64 | char | string
  /-- `error-context`. -/
  | errorContext
  /-- A named type (type definition, resource or `use`d name). A bare resource name in
  a type position is an owned handle. -/
  | named (n : Name)
  /-- `list<T>`. -/
  | list (t : Ty)
  /-- `list<T, N>`. -/
  | fixedList (t : Ty) (len : Nat)
  /-- `map<K, V>`. -/
  | map (k v : Ty)
  /-- `tuple<T, …>`. -/
  | tuple (ts : List Ty)
  /-- `option<T>`. -/
  | option (t : Ty)
  /-- `result<T, E>`, `result<_, E>`, `result<T>` and `result`. -/
  | result (ok err : Option Ty)
  /-- `own<R>`. -/
  | own (r : Name)
  /-- `borrow<R>`. -/
  | borrow (r : Name)
  /-- `future<T>` and `future`. -/
  | future (t : Option Ty)
  /-- `stream<T>` and `stream`. -/
  | stream (t : Option Ty)
  deriving Repr, Inhabited

/-! `deriving DecidableEq` does not handle the nesting through `List` and `Option`;
equality is decided by a structural Boolean equality. -/

mutual
/-- Structural Boolean equality of types. -/
def Ty.beq : Ty → Ty → Bool
  | .named a, .named b | .own a, .own b | .borrow a, .borrow b => a == b
  | .list a, .list b | .option a, .option b => Ty.beq a b
  | .fixedList a n, .fixedList b m => Ty.beq a b && n == m
  | .map a c, .map b d => Ty.beq a b && Ty.beq c d
  | .result a c, .result b d => Ty.beqOpt a b && Ty.beqOpt c d
  | .future a, .future b | .stream a, .stream b => Ty.beqOpt a b
  | .tuple a, .tuple b => Ty.beqList a b
  | a, b => a.ctorIdx == b.ctorIdx
/-- `Ty.beq` on optional types. -/
def Ty.beqOpt : Option Ty → Option Ty → Bool
  | none, none => true
  | some a, some b => Ty.beq a b
  | _, _ => false
/-- `Ty.beq` on lists of types. -/
def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false
end

mutual
theorem Ty.eq_of_beq : (a b : Ty) → Ty.beq a b = true → a = b
  | a, b, h => by
    cases a <;> cases b <;> simp_all [Ty.beq, Ty.ctorIdx]
    all_goals first
      | exact Ty.eq_of_beq _ _ h
      | exact Ty.eq_of_beq _ _ h.1
      | exact ⟨Ty.eq_of_beq _ _ h.1, Ty.eq_of_beq _ _ h.2⟩
      | exact ⟨Ty.eq_of_beqOpt _ _ h.1, Ty.eq_of_beqOpt _ _ h.2⟩
      | exact Ty.eq_of_beqOpt _ _ h
      | exact Ty.eq_of_beqList _ _ h
theorem Ty.eq_of_beqOpt : (a b : Option Ty) → Ty.beqOpt a b = true → a = b
  | none, none, _ => rfl
  | some a, some b, h => by rw [Ty.eq_of_beq a b (by simpa [Ty.beqOpt] using h)]
  | none, some _, h | some _, none, h => by simp [Ty.beqOpt] at h
theorem Ty.eq_of_beqList : (a b : List Ty) → Ty.beqList a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Ty.beqList, Bool.and_eq_true] at h
    rw [Ty.eq_of_beq a b h.1, Ty.eq_of_beqList as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Ty.beqList] at h
end

mutual
theorem Ty.beq_self (a : Ty) : Ty.beq a a = true := by
    cases a
    all_goals first
      | rfl
      | simp only [Ty.beq, beq_self_eq_true]; done
      | simp only [Ty.beq, Bool.and_eq_true, beq_self_eq_true, and_true]
        first
          | exact Ty.beq_self _
          | exact ⟨Ty.beq_self _, Ty.beq_self _⟩
          | exact ⟨Ty.beqOpt_self _, Ty.beqOpt_self _⟩
          | exact Ty.beqOpt_self _
          | exact Ty.beqList_self _
theorem Ty.beqOpt_self : (a : Option Ty) → Ty.beqOpt a a = true
  | none => rfl
  | some a => by simpa [Ty.beqOpt] using Ty.beq_self a
theorem Ty.beqList_self : (a : List Ty) → Ty.beqList a a = true
  | [] => rfl
  | a :: as => by simpa [Ty.beqList] using ⟨Ty.beq_self a, Ty.beqList_self as⟩
end

instance : DecidableEq Ty := fun a b =>
  if h : Ty.beq a b then isTrue (Ty.eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ Ty.beq_self a))

/-- A record field. -/
structure Field where
  name : Name
  ty : Ty
  docs : Docs := {}
  deriving Repr, DecidableEq, Inhabited

/-- A variant case, with an optional payload. -/
structure Case where
  name : Name
  ty : Option Ty := none
  docs : Docs := {}
  deriving Repr, DecidableEq, Inhabited

/-- An enum case or a flag. -/
structure Label where
  name : Name
  docs : Docs := {}
  deriving Repr, DecidableEq, Inhabited

/-- A function type `async? func(params) -> result`. -/
structure Func where
  params : List (Name × Ty) := []
  result : Option Ty := none
  async : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The kind of a function inside a `resource` block. -/
inductive ResourceFuncKind where
  /-- `constructor(params);` -/
  | ctor
  /-- `name: func(params) -> result;` (with an implicit `self: borrow<R>`). -/
  | method (name : Name)
  /-- `name: static func(params) -> result;` -/
  | static (name : Name)
  deriving Repr, DecidableEq, Inhabited

/-- A function of a `resource` block. -/
structure ResourceFunc where
  kind : ResourceFuncKind
  func : Func
  docs : Docs := {}
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- The body of a type definition. -/
inductive TypeDefKind where
  /-- `type x = T;` -/
  | alias (t : Ty)
  | record (fields : List Field)
  | variant (cases : List Case)
  | enum (cases : List Label)
  | flags (flags : List Label)
  /-- `resource r;` or `resource r { … }`. -/
  | resource (funcs : List ResourceFunc)
  deriving Repr, DecidableEq, Inhabited

/-- A type definition. -/
structure TypeDef where
  name : Name
  kind : TypeDefKind
  docs : Docs := {}
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- The path of a `use`, `include` or interface import/export. -/
inductive UsePath where
  /-- An interface or world of the current package, or a top-level `use` alias. -/
  | local (name : Name)
  /-- `ns:pkg/name@version`. -/
  | foreign (pkg : PackageName) (name : Name)
  deriving Repr, DecidableEq, Inhabited

/-- One name of a `use`: `name` or `name as alias`. -/
structure UseName where
  name : Name
  as : Option Name := none
  deriving Repr, DecidableEq, Inhabited

/-- The name a `use` binds. -/
def UseName.bound (u : UseName) : Name := u.as.getD u.name

/-- `use path.{names};` -/
structure Use where
  path : UsePath
  names : List UseName
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- A named function `name: func(…)`. -/
structure FuncDef where
  name : Name
  func : Func
  docs : Docs := {}
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- An item of an interface body (also the body of an inline interface). -/
inductive IfaceItem where
  | type (d : TypeDef)
  | use (u : Use)
  | func (f : FuncDef)
  deriving Repr, DecidableEq, Inhabited

/-- `interface name { items }`. -/
structure Interface where
  name : Name
  items : List IfaceItem
  docs : Docs := {}
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- What a world imports or exports. -/
inductive Extern where
  /-- `name: func(…);` -/
  | func (name : Name) (f : Func)
  /-- `name: interface { items }` -/
  | iface (name : Name) (items : List IfaceItem)
  /-- `path;` — an interface by its path. -/
  | path (p : UsePath)
  deriving Repr, DecidableEq, Inhabited

/-- An import or export of a world, with its docs and gates. -/
structure WorldExtern where
  ext : Extern
  docs : Docs := {}
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- `a as b` in `include … with { … }`. -/
structure IncludeName where
  name : Name
  as : Name
  deriving Repr, DecidableEq, Inhabited

/-- `include path with { names };` -/
structure Include where
  path : UsePath
  names : List IncludeName := []
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- An item of a world. -/
inductive WorldItem where
  | «import» (e : WorldExtern)
  | «export» (e : WorldExtern)
  | use (u : Use)
  | type (d : TypeDef)
  | «include» (i : Include)
  deriving Repr, DecidableEq, Inhabited

/-- `world name { items }`. -/
structure World where
  name : Name
  items : List WorldItem
  docs : Docs := {}
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- A top-level `use path as name;` (`as` omitted: the interface's own name). -/
structure TopUse where
  path : UsePath
  as : Option Name := none
  gates : List Gate := []
  deriving Repr, DecidableEq, Inhabited

/-- An item of a package. -/
inductive PackageItem where
  | iface (i : Interface)
  | world (w : World)
  | use (u : TopUse)
  deriving Repr, DecidableEq, Inhabited

/-- A package: its name, its docs (the doc comments of `package …;`) and its items. -/
structure Package where
  name : PackageName
  items : List PackageItem
  docs : Docs := {}
  deriving Repr, DecidableEq, Inhabited

/-- A WIT document: the package declared by `package ns:name;` with the items at top
level, and the packages declared by nested `package ns:name { … }` blocks. -/
structure Document where
  main : Package
  nested : List Package := []
  deriving Repr, DecidableEq, Inhabited

/-- The packages a document declares. -/
def Document.packages (d : Document) : List Package := d.main :: d.nested

end Silmaril.Wasm.Wit
