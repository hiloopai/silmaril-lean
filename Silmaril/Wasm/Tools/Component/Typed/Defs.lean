module

public import Silmaril.Wasm.Component.RefValid.Defs

/-!
# Typed rules of wasmparser 1.262.0 that the copied validator lacks

`Gates` holds rules that read the syntax only. The rules here need the types the reference
validator computes, so they replay its fold: `walkDefs` runs `checkDef?` (the copied
validator's step, at the Core 3.0 profile) definition by definition and looks at the state
before and after each step. Each rule is transcribed from
`crates/wasmparser/src/validator/component.rs` of wasm-tools 1.262.0 and was found by the
differential suite `tools/wasm-tools/tests/compval/validate.sh`:

* **`task.return` results** (`canon task.return`, line 1473): the result type cannot contain a
  `borrow` ("`task.return` result cannot contain a `borrow` type");
* **📡 accessors and constructors** (`check_name_with_type`, lines 4880-5060, and the setter
  rule of `add_entity_name`, lines 4806-4845), for the imports and exports of components:
  a `[constructor]` function cannot be `async`; a `[get]`/`[set]` function cannot be `async`;
  a getter has no parameters (besides `self` for `[method]`) and returns a value, which is not
  a `result` without an `ok` type; a setter has exactly one parameter (besides `self`) and
  returns nothing or a `result` without `ok` type; a setter needs a preceding getter of the
  same kind (import or export) named with `[get]`, whose property type (its result, unwrapped
  from `result<T, _>`) equals the setter's last parameter type;
* **limits** (`TypeInfo::combine`, `combine_type_sizes`): the nesting depth of every type
  definition (value, function, instance and component types) and of every component (its
  imports and exports together, wasmparser's `ComponentState::type_info`) is at most 100
  ("type nesting is too deep") and its effective size is below 1,000,000 ("effective type
  size exceeds the limit of 1000000"). Depth and size are wasmparser's: a leaf (primitive,
  `own`, `borrow`, resource) has depth and size 1; an aggregate has depth one more than its
  deepest member and size one more than the sum of its members' sizes. The size is computed
  with a budget, so that a shared (exponential) type is rejected after at most a million
  steps.

* **accessors in type declarations** (`typeNames`): the same accessor rules on the exports
  of instance types and the imports and exports of component types, read from the declared
  type (the copied validator checks declarations in `checkDefType?` without exposing its
  states, so the rule sees the finished type: the declared type and the instance and
  component types it imports or exports, not types declared inside it and not exported);
* **inline value exports** (`inlineValueProblem`): a value exported by an inline-export
  instance cannot contain a `borrow`.

Not covered: types declared inside a type declaration and not exported (see above), and the size of core module types (counted as 1: wasmparser counts
their core types, so this only accepts more).

These are executable rules (`walkProblem`), not part of the relational specification;
`Validate.check` runs them after the copied validator accepted, so they only reject.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Typed

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Component.Syntax (PlainName Accessor)

/-- Semantic value types. -/
abbrev VT := Types.ValType Nat

/-- Semantic function types. -/
abbrev FT := Types.FuncType Nat

/-! ## Silmaril.Wasm.Component.Limits -/

/-- wasmparser's `MAX_WASM_COMPONENT_TYPE_DEPTH`. -/
def maxDepth : Nat := 100

/-- wasmparser's `MAX_WASM_TYPE_SIZE`. -/
def maxSize : Nat := 1000000

/-- The type information wasmparser keeps (`TypeInfo`): the nesting depth and the size,
the latter counted from an accumulator and bounded by a budget (`none` once it reaches the
budget, which also bounds the work on shared types). -/
abbrev Info := Option (Nat × Nat)

/-- A node with no members: depth 1, size one more than the accumulator. -/
def leaf (b acc : Nat) : Info := if acc + 1 < b then some (1, acc + 1) else none

/-- `TypeInfo::combine`: add a member's information to an aggregate's. -/
def combine (i : Nat × Nat) (m : Nat → Info) : Info :=
  (m i.2).map fun (d, acc) => (max i.1 (d + 1), acc)

/-- Fold `combine` over members. -/
def combineAll {α : Type} (f : Nat → α → Info) : Info → List α → Info
  | i, [] => i
  | i, a :: as => combineAll f (i >>= fun i => combine i (f · a)) as

mutual
/-- The information of a value type. -/
partial def infoV (b acc : Nat) : VT → Info
  | .list u | .fixedList u _ | .option u | .map _ u => combineAll (infoV b) (leaf b acc) [u]
  | .record fs => combineAll (infoV b) (leaf b acc) (fs.map (·.2))
  | .tuple ts => combineAll (infoV b) (leaf b acc) ts
  | .variant cs => combineAll (infoV b) (leaf b acc) (cs.filterMap (·.2))
  | .result x y => combineAll (infoV b) (leaf b acc) (x.toList ++ y.toList)
  | .future u | .stream u => combineAll (infoV b) (leaf b acc) u.toList
  | _ => leaf b acc

/-- The information of a function type (its parameters and result). -/
partial def infoF (b acc : Nat) (ft : FT) : Info :=
  combineAll (infoV b) (leaf b acc) (ft.params.map (·.2) ++ ft.result.toList)

/-- The information of an entity type (core module types count as leaves). -/
partial def infoE {X : Type} (b acc : Nat) : Types.Entity Nat X → Info
  | .module _ => leaf b acc
  | .func ft => infoF b acc ft
  | .value t => infoV b acc t
  | .type t => infoT b acc t
  | .instance t => infoI b acc t
  | .component t => infoC b acc t

/-- The information of a type definition. -/
partial def infoT {X : Type} (b acc : Nat) : Types.TypeDef Nat X → Info
  | .val t => infoV b acc t
  | .resource _ => leaf b acc
  | .func ft => infoF b acc ft
  | .instance t => infoI b acc t
  | .component t => infoC b acc t

/-- An instance type: its exports. -/
partial def infoI {X : Type} (b acc : Nat) (t : Types.InstanceType Nat X) : Info :=
  combineAll (infoE b) (leaf b acc) (t.exports.map (·.2))

/-- A component type: its imports and exports. -/
partial def infoC {X : Type} (b acc : Nat) (t : Types.ComponentType Nat X) : Info :=
  combineAll (infoE b) (leaf b acc) (t.imports.map (·.2) ++ t.exports.map (·.2))
end

/-- The limit problem of some type information. -/
def limit : Info → Option String
  | none => some s!"effective type size exceeds the limit of {maxSize}"
  | some (d, _) => if d > maxDepth then some "type nesting is too deep" else none

/-- The limit problem of a value type. -/
def valLimit (t : VT) : Option String := limit (infoV maxSize 0 t)

/-- The limit problem of a type definition. -/
def defLimit {X : Type} (t : Types.TypeDef Nat X) : Option String := limit (infoT maxSize 0 t)

/-- The limit problem of a component's state: its imports and exports together. -/
def ctxLimit {X : Type} (Γ : Ctx X) : Option String :=
  limit (combineAll (infoE maxSize) (leaf maxSize 0) (Γ.imports.map (·.2) ++ Γ.exports.map (·.2)))

/-! ## Accessors and constructors -/

/-- The accessor of a plain name, and whether it is a `[method]`. -/
def accessorOf : PlainName → Option (Accessor × Bool)
  | .get _ => some (.get, false)
  | .set _ => some (.set, false)
  | .method (some a) _ _ => some (a, true)
  | .static (some a) _ _ => some (a, false)
  | _ => none

/-- The getter's name of a setter (`[set]` replaced by `[get]`). -/
def getterOf : PlainName → Option String
  | .set l => some (PlainName.get l).render
  | .method (some .set) r m => some (PlainName.method (some .get) r m).render
  | .static (some .set) r m => some (PlainName.static (some .get) r m).render
  | _ => none

/-- A `result` with no `ok` type. -/
def isResultNoOk : Option VT → Bool
  | some (.result none _) => true
  | _ => false

/-- The property type of a getter: its result, unwrapped from `result<T, _>`. -/
def propertyType : Option VT → Option VT
  | some (.result (some t) _) => some t
  | t => t

/-- The problem of a function named `n` with type `ft` (`kind`: `import` or `export`;
`prev`: the functions of that kind already named, with their types). -/
def nameProblem (kind : String) (prev : List (String × FT)) (n : String) (ft : FT) :
    Option String :=
  match Syntax.parsePlainName? n with
  | none => none
  | some p =>
    match p with
    | .constructor _ =>
      if ft.async_ then some "constructor function cannot be async" else none
    | _ =>
    match accessorOf p with
    | none => none
    | some (a, method) =>
      let desc := match a with | .get => "getter" | .set => "setter"
      let own := if method then ft.params.length - 1 else ft.params.length
      let besides := if method then " besides `self`" else ""
      if ft.async_ then some s!"{desc} function cannot be async"
      else match a with
        | .get =>
          if own ≠ 0 then some s!"getter function should have no parameters{besides}"
          else if ft.result.isNone then some "getter function should return a value"
          else if isResultNoOk ft.result then
            some "if a getter function returns a result, that result must have a value type"
          else none
        | .set =>
          if own ≠ 1 then some s!"setter function should have exactly one parameter{besides}"
          else if !(ft.result.isNone || isResultNoOk ft.result) then
            some "setter function should return nothing or `(result (error $E)?)`"
          else match getterOf p with
            | none => none
            | some g =>
              match prev.lookup g with
              | none => some s!"{kind} name `{n}` requires a preceding {kind} named `{g}`"
              | some gt =>
                if (ft.params.getLast?.map (·.2)) == propertyType gt.result then none
                else some s!"{kind} `{n}`'s parameter type must match the return type of `{g}`"

/-- The functions among the imports or exports of a context. -/
def funcsOf {X : Type} (l : List (String × Types.Entity Nat X)) : List (String × FT) :=
  l.filterMap fun | (n, .func ft) => some (n, ft) | _ => none

/-- The rule for a new import or export: the entries after the step that were not there
before, checked against the earlier ones. -/
def newNameProblem {X : Type} (kind : String) (before after : List (String × Types.Entity Nat X)) :
    Option String :=
  let prev := funcsOf before
  (funcsOf (after.drop before.length)).findSome? fun (n, ft) => nameProblem kind prev n ft

/-! ## The walk -/

/-- The limits of the new type of a `type` definition. -/
def typeLimit {X : Type} (before after : Ctx X) : Option String :=
  if after.types.length = before.types.length + 1 then
    match after.types.getLast? with
    | some s => defLimit s.def_
    | none => none
  else none

/-- The accessor rules along a declaration list: each function checked against the earlier
ones (`kind`: `import` or `export`). -/
def seqNameProblem {X : Type} (kind : String) (l : List (String × Types.Entity Nat X)) :
    Option String :=
  (List.range l.length).findSome? fun i => newNameProblem kind (l.take i) (l.take (i + 1))

mutual
/-- **The accessor rules inside instance and component type declarations** (wasmparser runs
`add_entity_name` on the exports of an instance type and the imports and exports of a component
type as they are declared): on the declared type and on the instance and component types it
exports or imports. -/
partial def typeNames {X : Type} : Types.TypeDef Nat X → Option String
  | .instance t => seqNameProblem "export" t.exports <|> t.exports.findSome? (entNames ·.2)
  | .component t =>
    seqNameProblem "import" t.imports <|> seqNameProblem "export" t.exports <|>
      (t.imports ++ t.exports).findSome? (entNames ·.2)
  | _ => none

/-- The rules on the types an entity carries. -/
partial def entNames {X : Type} : Types.Entity Nat X → Option String
  | .instance t => typeNames (.instance t)
  | .component t => typeNames (.component t)
  | .type t => typeNames t
  | _ => none
end

/-- The accessor rules of the new type of a `type` definition. -/
def typeNameProblem {X : Type} (before after : Ctx X) : Option String :=
  if after.types.length = before.types.length + 1 then
    match after.types.getLast? with
    | some s => typeNames s.def_
    | none => none
  else none

/-- wasmparser's `add_entity` with `ExternKind::Silmaril.Wasm.Component.Export` on an inline-export instance
(`instance (export …)`): an exported value's type cannot contain a `borrow`. -/
def inlineValueProblem {X : Type} (Γ : Ctx X)
    (items : List (Syntax.ExternName × Syntax.SortIdx Syntax.Sort_)) : Option String :=
  items.findSome? fun (_, it) =>
    match it.sort, Γ.value? it.idx with
    | .value, some (t, _) =>
      if ABI.containsBorrow t then some "exported value type cannot contain a `borrow` type"
      else none
    | _, _ => none

/-- The Core 3.0 checker's step. -/
abbrev step (feat : Features) (sc : Scopes Core3Extern) (s : DefState Core3Extern)
    (d : Syntax.Definition Silmaril.Wasm.Module) :=
  checkDef? feat core3Profile core3ModuleType? sc s d

mutual
/-- The problem of one definition, given the states before and after the reference's step. -/
def defProblem (feat : Features) (sc : Scopes Core3Extern)
    (s s' : DefState Core3Extern) : Syntax.Definition Silmaril.Wasm.Module → Option String
  | .component defs =>
    let (sc', Γ) := Scopes.enter sc s.ctx .component
    walkDefs feat sc' { st := s.st.child Γ } 0 defs
  | .canon (.builtin (.taskReturn r _)) =>
    match resolveOpt? s.ctx r with
    | .ok (some t) =>
      if ABI.containsBorrow t then some "`task.return` result cannot contain a `borrow` type"
      else none
    | _ => none
  | .import_ _ _ => newNameProblem "import" s.ctx.imports s'.ctx.imports
  | .export_ _ _ _ => newNameProblem "export" s.ctx.exports s'.ctx.exports
  | .type _ => typeLimit s.ctx s'.ctx <|> typeNameProblem s.ctx s'.ctx
  | .instance_ (.exports items) => inlineValueProblem s.ctx items
  | _ => none

/-- Replay the reference's fold and report the first problem; `oa` is the size of the
types aliased from the enclosing component so far (wasmparser's `outer_alias_type_size`,
charged here for `alias outer 1`). -/
def walkDefs (feat : Features) (sc : Scopes Core3Extern) (s : DefState Core3Extern)
    (oa : Nat) : List (Syntax.Definition Silmaril.Wasm.Module) → Option String
  | [] => ctxLimit s.ctx
  | d :: ds =>
    match step feat sc s d with
    | .error _ => none
    | .ok s' =>
      match defProblem feat sc s s' d with
      | some e => some e
      | none =>
        match d, s'.ctx.types.getLast? with
        | .alias (.outer 1 _ .type), some t =>
          match infoT maxSize oa t.def_ with
          | none => some s!"effective type size exceeds the limit of {maxSize}"
          | some (_, oa') => walkDefs feat sc s' oa' ds
        | _, _ => walkDefs feat sc s' oa ds
end

/-! ## The entry point

The walk repeats the reference's work, including core module validation (about 0.1 s more
on the 3.1 MB `cat-debug.wasm`). It always runs: the limits can fire on components without
any type definition (instances of nested components exported level by level). -/

/-- **The typed rules** on a component: the first problem, if any. -/
def walkProblem (feat : Features) (c : Syntax.Component Silmaril.Wasm.Module) : Option String :=
  walkDefs feat [] initState 0 c

end Silmaril.Wasm.Tools.Component.Typed
