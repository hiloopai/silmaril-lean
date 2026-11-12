module

public import Silmaril.Wasm.Wac.Text.Parse.Defs

/-!
# WAC: two checks of `wac`'s resolver that the validation of `Silmaril.Wasm.Wac.Valid` lacks

Found by the corpus suite (`tools/wac/tests/corpus.sh`, wac's
`crates/wac-parser/tests/resolution/fail`):

* **Duplicate parameter names** (`duplicate-func-param`, wac's `DuplicateParameter` in
  `func_type`): every function type of the document (type aliases `type f = func(…)`, interface
  and inline-interface exports, world items, imports, resource methods and constructors) has
  distinct parameter names. `Valid` checks this for resource functions only.
* **Interfaces and worlds are not value types** (`invalid-value-type`, `InvalidValueType`): a
  type in a function type at the top level of the document does not name a top-level interface
  or world. (Inside an interface or world body, names are looked up in that body's scope, which
  `Valid.StmtsOk` covers.)

`check d` is `.ok ()` or the first error. The tool runs it on the parsed text before the
pipeline (`EndToEndR.composeTextR`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TextCheck

open Silmaril.Wasm.Wac.Text

/-- The first name of a list that occurs again later. -/
def firstDup : List String → Option String
  | [] => none
  | a :: as => if a ∈ as then some a else firstDup as

mutual
/-- The identifiers a value type names. -/
def tyIdents : Ty → List String
  | .ident id | .borrow id => [id]
  | .tuple ts => tyIdentsL ts
  | .list t | .option t => tyIdents t
  | .result a b => tyIdentsO a ++ tyIdentsO b
  | .stream t | .future t => tyIdentsO t
  | _ => []
/-- `tyIdents` of an optional type. -/
def tyIdentsO : Option Ty → List String
  | none => []
  | some t => tyIdents t
/-- `tyIdents` of types. -/
def tyIdentsL : List Ty → List String
  | [] => []
  | t :: ts => tyIdents t ++ tyIdentsL ts
end

/-- The identifiers a function type names. -/
def funcIdents (f : FuncType) : List String :=
  (f.params.map fun p => tyIdents p.ty).flatten ++
    match f.results with
    | .empty => []
    | .scalar t => tyIdents t

/-- The function types of a resource. -/
def methodFuncs : ResourceMethod → List FuncType
  | .ctor _ ps => [⟨false, ps, .empty⟩]
  | .method _ _ _ f => [f]

/-- The function types of a type declaration. -/
def itemDeclFuncs : ItemTypeDecl → List FuncType
  | .resource _ _ ms => ms.flatMap methodFuncs
  | .decl (.alias _ _ (.func f)) => [f]
  | .decl _ => []

/-- The function types of an interface item. -/
def ifaceItemFuncs : InterfaceItem → List FuncType
  | .use _ => []
  | .type d => itemDeclFuncs d
  | .export_ _ _ (.func f) => [f]
  | .export_ _ _ (.ident _) => []

/-- The function types of a world item path. -/
def pathFuncs : WorldItemPath → List FuncType
  | .named _ (.func f) => [f]
  | .named _ (.interface items) => items.flatMap ifaceItemFuncs
  | _ => []

/-- The function types of a world item. -/
def worldItemFuncs : WorldItem → List FuncType
  | .type d => itemDeclFuncs d
  | .import_ _ p | .export_ _ p => pathFuncs p
  | _ => []

/-- Every function type of a statement. -/
def stmtFuncs : Statement → List FuncType
  | .import_ _ _ _ (.func f) => [f]
  | .import_ _ _ _ (.interface items) => items.flatMap ifaceItemFuncs
  | .type (.interface _ _ items) => items.flatMap ifaceItemFuncs
  | .type (.world _ _ items) => items.flatMap worldItemFuncs
  | .type (.type (.alias _ _ (.func f))) => [f]
  | _ => []

/-- The function types at the top level of a statement (outside interface and world bodies). -/
def topFuncs : Statement → List FuncType
  | .import_ _ _ _ (.func f) => [f]
  | .type (.type (.alias _ _ (.func f))) => [f]
  | _ => []

/-- The interfaces and worlds declared at the top level. -/
def topIfaces (d : Document) : List String :=
  d.statements.filterMap fun
    | .type (.interface _ id _) | .type (.world _ id _) => some id
    | _ => none

/-- **The checks.** -/
def check (d : Document) : Except String Unit := do
  for f in d.statements.flatMap stmtFuncs do
    if let some x := firstDup (f.params.map (·.id)) then
      throw s!"duplicate function parameter `{x}`"
  let ifs := topIfaces d
  for f in d.statements.flatMap topFuncs do
    for x in funcIdents f do
      if x ∈ ifs then throw s!"`{x}` is an interface or world and cannot be used as a value type"

/-- The checks on a text (`.ok ()` when it does not parse: the pipeline reports that). -/
def checkText (src : String) : Except String Unit :=
  match parse src with
  | some d => check d
  | none => .ok ()

end Silmaril.Wasm.Wac.TextCheck
