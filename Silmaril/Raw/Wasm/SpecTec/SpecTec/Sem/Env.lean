module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Value
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The environment of the internal language

A transcription of `spectec/src/il/env.ml` at
`608711107b7f1edb13efd57b7d79b49477462d36`: the table that the IL validator
(`spectec/src/il/valid.ml`) and the IL evaluator (`spectec/src/il/eval.ml`)
look declarations up in, together with the pass that builds it from a script
(`env.ml:99-118`).  This is step 2 of `docs/projects/spectec/README.md`.

## What this file proves

`envOfDefs_eq` is the engine: folding `envOfDef` over a list of definitions
leaves `vars` alone and pushes a computable prefix — `typsOfDefs ds`,
`defsOfDefs ds`, `relsOfDefs ds`, `gramsOfDefs ds` — onto each of the other
four namespaces.  Everything else follows from it by rewriting:
`envOfScript_append`, the monotonicity lemmas `memTyp_envOfDefs_of_memTyp` and
friends, and the characterization `mem_typs_envOfScript_iff`, which says that
an identifier is a type of the environment exactly when some definition of the
script declares it — inside a `RecD` group or not — and is not the wildcard.
`Silmaril/SpecTec/Sem/Env.lean` is a leaf of the semantics, so the lemmas are
stated in the form the validator and the evaluator will consume them: all
through `find?` and `mem`, never through the shape of a map.

## The representation of a map

OCaml uses `Map.Make(String)` (`env.ml:15`), a balanced tree.  Here a map is an
association list, `Map α := List (IL.Id × α)`, with `bind` *prepending* and
`find?` returning the first match.  Two reasons:

* Every operation this file needs is a two-line structural recursion whose
  equations are definitional, so each lemma below is a plain list induction
  with no side conditions on the shape of the data.  `Std.HashMap` would make
  `find?` after `bind` an appeal to `getElem?_insert` and would drag a
  `BEq`/`LawfulBEq`/`Hashable` bundle through every statement; worse, the
  characterization `mem_typs_envOfScript_iff` would have to reason about the
  internal bucket array, which is the one thing a verification target should
  never have to do.
* The script-to-environment pass is a left fold over a few hundred
  definitions, so the asymptotics of an association list are irrelevant here;
  the only consumer that cares is the evaluator, which can be given a
  different representation behind the same `find?` interface.

The cost is that the representation is not canonical: `bind` shadows rather
than replaces, so a map may hold a stale pair for a key it has rebound, and
two maps that agree on every key need not be equal.  Nothing below ever states
an equality of maps that depends on the difference — every lemma is phrased
through `find?` or `mem` — except `envOfDefs_eq`, which is an equality of maps
*as built*, and is all the stronger for it.

## Deviations from `env.ml`

* `find` (`env.ml:47-50`) raises `Util.Error.error` on an undeclared
  identifier.  It has no total counterpart; use `find?`, which is `find_opt`
  (`env.ml:44-45`).  The `phase` reference (`env.ml:7-9`) that `find`'s message
  mentions is likewise not transcribed.
* The duplicate-declaration check of `bind` is commented out at the pin
  (`env.ml:55-58`, `TODO(3, rossberg): reactivate?`), so `bind` silently
  shadows an existing binding.  `bind` below transcribes what the code *does*;
  see its docstring.
* `rebind` (`env.ml:62-64`) begins with `assert (Map.mem id.it map)`.  An
  assertion is not a value, so `Map.rebind` carries it as a documented
  precondition and is otherwise `Map.add`.
* `binds` is not in `env.ml`.  It is the fold shape `env_of_params`
  (`env.ml:106`) uses, lifted to each of the five namespaces.
* `env_of_def`'s `HintD` branch (`env.ml:115`) returns the environment
  unchanged; `IL.Def` has no `hintD` constructor at all (see
  `Silmaril/SpecTec/IL/Ast.lean`), so that branch simply does not appear.

The `import all` above is only for the examples at the end: `spectec_import`
(`Silmaril/SpecTec/Import.lean`) adds its definitions with `Lean.addDecl`,
which does not mark them `@[expose]`, so a plain `public import` of
`Silmaril.SpecTec.Specs` gives the kernel nothing to unfold.  With it, the
environment of the pinned wasm 1.0 script is computed and checked by the
kernel in about three seconds.
-/

@[expose] public section

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod

/-! ## Maps (`spectec/src/il/env.ml:15`) -/

/-- `module Map = Map.Make(String)` (`spectec/src/il/env.ml:15`), as an
association list ordered newest binding first.  See the module docstring for
why this representation and not `Std.HashMap`. -/
abbrev Map (α : Type) : Type := List (IL.Id × α)

namespace Map

variable {α : Type}

/-- `Map.empty` (`spectec/src/il/env.ml:35-39`). -/
def empty : Map α := []

/-- `Map.find_opt`, as used by `find_opt` (`spectec/src/il/env.ml:44-45`): the
value of the *first*, i.e. most recent, binding of `x`. -/
def find? : Map α → IL.Id → Option α
  | [], _ => none
  | (y, v) :: m, x => if y = x then some v else find? m x

/-- `Map.mem`, as used by `mem` (`spectec/src/il/env.ml:42`).  OCaml's `mem`
does not go through `find_opt`; the two agree (`mem_iff_find?`). -/
def mem (m : Map α) (x : IL.Id) : Bool := (m.find? x).isSome

/-- `bind` (`spectec/src/il/env.ml:52-60`).

Two things are worth spelling out.  First, the identifier `"_"` is ignored
(`env.ml:53-54`): the elaborator uses it for a binder whose value is never
referred to, and binding it would make `"_"` resolve to whichever wildcard was
elaborated last.  Second, the check that rejects a duplicate declaration is
commented out at the pin (`env.ml:55-58`), so a second `bind` of the same
identifier silently shadows the first; reactivating it would be a *validation*
error, not a change to this function's result on well-formed input. -/
def bind (m : Map α) (x : IL.Id) (v : α) : Map α :=
  if x = "_" then m else (x, v) :: m

/-- `rebind` (`spectec/src/il/env.ml:62-64`), which replaces an existing
binding.  Its `assert (Map.mem id.it map)` (`env.ml:63`) is a precondition
here: `rebind` on an unbound identifier is `Map.add`, as in OCaml with
assertions disabled.  Unlike `bind` it does not special-case `"_"`. -/
def rebind (m : Map α) (x : IL.Id) (v : α) : Map α := (x, v) :: m

/-- Bind a list of identifiers left to right, so that later entries shadow
earlier ones.  Not in `env.ml`; this is the shape of `env_of_params`
(`spectec/src/il/env.ml:106`). -/
def binds (m : Map α) (xs : List (IL.Id × α)) : Map α :=
  xs.foldl (fun m xv => m.bind xv.1 xv.2) m

/-! ### Lemmas about maps -/

/-- `Map.empty` is the empty list. -/
@[simp] theorem empty_def : (empty : Map α) = [] := rfl

/-- Nothing is bound in the empty map. -/
@[simp] theorem find?_nil (x : IL.Id) : find? ([] : Map α) x = none := rfl

/-- `find?` looks at the head binding first. -/
@[simp] theorem find?_cons (m : Map α) (y x : IL.Id) (v : α) :
    find? ((y, v) :: m) x = if y = x then some v else m.find? x := rfl

/-- The empty map binds nothing. -/
@[simp] theorem mem_nil (x : IL.Id) : mem ([] : Map α) x = false := rfl

/-- `mem` and `find_opt` (`spectec/src/il/env.ml:42,44`) agree. -/
theorem mem_iff_find? (m : Map α) (x : IL.Id) : m.mem x ↔ ∃ v, m.find? x = some v := by
  simp [mem, Option.isSome_iff_exists]

/-- An identifier is bound exactly when it is one of the keys. -/
theorem mem_iff_mem_keys (m : Map α) (x : IL.Id) : m.mem x ↔ x ∈ m.map Prod.fst := by
  induction m with
  | nil => simp
  | cons yv m ih =>
    obtain ⟨y, v⟩ := yv
    by_cases h : y = x
    · subst h; simp [mem]
    · simp [mem, h, Ne.symm h] at *; simpa [mem] using ih

/-- `bind` ignores the wildcard identifier (`spectec/src/il/env.ml:53-54`). -/
@[simp] theorem bind_underscore (m : Map α) (v : α) : m.bind "_" v = m := by
  simp [bind]

/-- `find?` after `bind`, in one equation. -/
theorem find?_bind (m : Map α) (x y : IL.Id) (v : α) :
    (m.bind x v).find? y = if x ≠ "_" ∧ x = y then some v else m.find? y := by
  by_cases h : x = "_"
  · subst h; simp
  · by_cases h' : x = y
    · subst h'; simp [bind, h]
    · simp [bind, h, h']

/-- The hit case of `find?` after `bind`. -/
@[simp] theorem find?_bind_self (m : Map α) {x : IL.Id} (h : x ≠ "_") (v : α) :
    (m.bind x v).find? x = some v := by
  simp [find?_bind, h]

/-- The miss case of `find?` after `bind`. -/
@[simp] theorem find?_bind_of_ne (m : Map α) {x y : IL.Id} (h : x ≠ y) (v : α) :
    (m.bind x v).find? y = m.find? y := by
  simp [find?_bind, h]

/-- `mem` after `bind`. -/
theorem mem_bind (m : Map α) (x y : IL.Id) (v : α) :
    (m.bind x v).mem y ↔ (x ≠ "_" ∧ x = y) ∨ m.mem y := by
  by_cases h : x = "_"
  · subst h; simp
  · by_cases h' : x = y
    · subst h'; simp [mem, bind, h]
    · simp [mem, bind, h, h']

/-- `bind` never unbinds: it is monotone in `mem`. -/
theorem mem_bind_of_mem (m : Map α) (x y : IL.Id) (v : α) (h : m.mem y) :
    (m.bind x v).mem y := by
  simp [mem_bind, h]

/-- `find?` on a concatenation: the left map shadows the right one. -/
theorem find?_append (m₁ m₂ : Map α) (x : IL.Id) :
    (m₁ ++ m₂).find? x = (m₁.find? x).or (m₂.find? x) := by
  induction m₁ with
  | nil => simp
  | cons yv m₁ ih =>
    obtain ⟨y, v⟩ := yv
    by_cases h : y = x <;> simp [h, ih]

/-- `mem` on a concatenation. -/
theorem mem_append (m₁ m₂ : Map α) (x : IL.Id) :
    (m₁ ++ m₂).mem x ↔ m₁.mem x ∨ m₂.mem x := by
  simp [mem, find?_append, Option.isSome_or]

/-- `find?` on a concatenation whose left map misses. -/
theorem find?_append_of_not_mem (m₁ m₂ : Map α) (x : IL.Id) (h : ¬ m₁.mem x) :
    (m₁ ++ m₂).find? x = m₂.find? x := by
  simp only [mem, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
  simp [find?_append, h]

/-- `binds` is the left fold its definition says it is. -/
theorem binds_cons (m : Map α) (xv : IL.Id × α) (xs : List (IL.Id × α)) :
    m.binds (xv :: xs) = (m.bind xv.1 xv.2).binds xs := rfl

/-- `binds` of nothing is the identity. -/
@[simp] theorem binds_nil (m : Map α) : m.binds [] = m := rfl

end Map

/-! ## The environment (`spectec/src/il/env.ml:17-29`) -/

/-- `type var_def = typ` (`spectec/src/il/env.ml:17`). -/
abbrev VarDef : Type := Typ

/-- `type typ_def = param list * inst list` (`spectec/src/il/env.ml:18`). -/
abbrev TypDef : Type := List Param × List Inst

/-- `type rel_def = param list * mixop * typ * rule list`
(`spectec/src/il/env.ml:19`). -/
abbrev RelDef : Type := List Param × MixopS × Typ × List Rule

/-- `type def_def = param list * typ * clause list`
(`spectec/src/il/env.ml:20`). -/
abbrev DefDef : Type := List Param × Typ × List Clause

/-- `type gram_def = param list * typ * prod list`
(`spectec/src/il/env.ml:21`). -/
abbrev GramDef : Type := List Param × Typ × List IL.Prod

/-- An interpretation of the specification's *primitive* functions.

`spectec`'s `hint(builtin)` marks a function the script declares but does not
define: `$iand_`, `$ishl_`, `$truncz`, the twenty-six float operations, and the
width conversions.  In the pinned script those have no clause at all, so the IL
denotes nothing at them (`Equiv/Numerics.lean`'s negative results), and every
reduction rule that reaches one is stuck.

`Builtins` supplies them from outside the IL.  `call x ws` is the value `$x`
takes on the argument values `ws`, or `none` where the interpretation says
nothing.  `Sem/Eval.lean`'s `callDef` consults it *only* where the script
itself supplies nothing, so `Builtins.none` is the pinned reading on the nose
(`callDef_builtinsNone`). -/
structure Builtins where
  /-- The value of `$x` at the argument values `ws`, if the interpretation
  gives it one. -/
  call : IL.Id → List ArgV → Option Value

/-- The empty interpretation: the pinned script, read exactly as it is. -/
def Builtins.none : Builtins := ⟨fun _ _ => Option.none⟩

instance : Inhabited Builtins := ⟨Builtins.none⟩

/-- `Builtins` is a function, so it has no useful `Repr`; `Env` derives one and
this keeps that working. -/
instance : Repr Builtins := ⟨fun _ _ => "⟨builtins⟩"⟩

/-- `type t` (`spectec/src/il/env.ml:23-29`): the five namespaces a
declaration can be looked up in. -/
structure Env where
  /-- `vars : var_def Map.t` (`spectec/src/il/env.ml:24`): the type of each
  expression variable in scope. -/
  vars : Map VarDef
  /-- `typs : typ_def Map.t` (`spectec/src/il/env.ml:25`). -/
  typs : Map TypDef
  /-- `defs : def_def Map.t` (`spectec/src/il/env.ml:26`). -/
  defs : Map DefDef
  /-- `rels : rel_def Map.t` (`spectec/src/il/env.ml:27`). -/
  rels : Map RelDef
  /-- `grams : gram_def Map.t` (`spectec/src/il/env.ml:28`). -/
  grams : Map GramDef
  /-- The interpretation of the `hint(builtin)` functions.  Not part of
  `il/env.ml`: the official frontend has nowhere to put one, because it never
  executes the IL.  `Builtins.none` is the pinned reading. -/
  builtins : Builtins := Builtins.none
  deriving Repr, Inhabited

namespace Env

/-- `empty` (`spectec/src/il/env.ml:34-40`). -/
def empty : Env := ⟨Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, Builtins.none⟩



/-! ### `mem` (`spectec/src/il/env.ml:66-70`) -/

/-- `mem_var` (`spectec/src/il/env.ml:66`). -/
def memVar (env : Env) (x : IL.Id) : Bool := env.vars.mem x

/-- `mem_typ` (`spectec/src/il/env.ml:67`). -/
def memTyp (env : Env) (x : IL.Id) : Bool := env.typs.mem x

/-- `mem_def` (`spectec/src/il/env.ml:68`). -/
def memDef (env : Env) (x : IL.Id) : Bool := env.defs.mem x

/-- `mem_rel` (`spectec/src/il/env.ml:69`). -/
def memRel (env : Env) (x : IL.Id) : Bool := env.rels.mem x

/-- `mem_gram` (`spectec/src/il/env.ml:70`). -/
def memGram (env : Env) (x : IL.Id) : Bool := env.grams.mem x

/-! ### `find_opt` (`spectec/src/il/env.ml:72-76`)

`find` (`env.ml:78-82`) is `find_opt` followed by an error on `None`; see the
module docstring for why it is not transcribed. -/

/-- `find_opt_var` (`spectec/src/il/env.ml:72`). -/
def findVar? (env : Env) (x : IL.Id) : Option VarDef := env.vars.find? x

/-- `find_opt_typ` (`spectec/src/il/env.ml:73`). -/
def findTyp? (env : Env) (x : IL.Id) : Option TypDef := env.typs.find? x

/-- `find_opt_def` (`spectec/src/il/env.ml:74`). -/
def findDef? (env : Env) (x : IL.Id) : Option DefDef := env.defs.find? x

/-- `find_opt_rel` (`spectec/src/il/env.ml:75`). -/
def findRel? (env : Env) (x : IL.Id) : Option RelDef := env.rels.find? x

/-- `find_opt_gram` (`spectec/src/il/env.ml:76`). -/
def findGram? (env : Env) (x : IL.Id) : Option GramDef := env.grams.find? x

/-! ### `bind` (`spectec/src/il/env.ml:84-88`) -/

/-- `bind_var` (`spectec/src/il/env.ml:84`). -/
def bindVar (env : Env) (x : IL.Id) (v : VarDef) : Env :=
  { env with vars := env.vars.bind x v }

/-- `bind_typ` (`spectec/src/il/env.ml:85`). -/
def bindTyp (env : Env) (x : IL.Id) (v : TypDef) : Env :=
  { env with typs := env.typs.bind x v }

/-- `bind_def` (`spectec/src/il/env.ml:86`). -/
def bindDef (env : Env) (x : IL.Id) (v : DefDef) : Env :=
  { env with defs := env.defs.bind x v }

/-- `bind_rel` (`spectec/src/il/env.ml:87`). -/
def bindRel (env : Env) (x : IL.Id) (v : RelDef) : Env :=
  { env with rels := env.rels.bind x v }

/-- `bind_gram` (`spectec/src/il/env.ml:88`). -/
def bindGram (env : Env) (x : IL.Id) (v : GramDef) : Env :=
  { env with grams := env.grams.bind x v }

/-- Install an interpretation of the primitives.  Every `findDef?`/`findRel?`
fact about `env` survives, because only the new field changes. -/
def withBuiltins (env : Env) (B : Builtins) : Env := { env with builtins := B }

@[simp] theorem findDef?_withBuiltins (env : Env) (B : Builtins) (x : IL.Id) :
    (env.withBuiltins B).findDef? x = env.findDef? x := rfl

@[simp] theorem findRel?_withBuiltins (env : Env) (B : Builtins) (x : IL.Id) :
    (env.withBuiltins B).findRel? x = env.findRel? x := rfl

@[simp] theorem builtins_withBuiltins (env : Env) (B : Builtins) :
    (env.withBuiltins B).builtins = B := rfl

/-! ### `binds`

Not in `env.ml`; the fold shape of `env_of_params`
(`spectec/src/il/env.ml:106`), one per namespace. -/

/-- Bind a list of expression variables left to right. -/
def bindVars (env : Env) (xs : List (IL.Id × VarDef)) : Env :=
  { env with vars := env.vars.binds xs }

/-- Bind a list of syntax types left to right. -/
def bindTyps (env : Env) (xs : List (IL.Id × TypDef)) : Env :=
  { env with typs := env.typs.binds xs }

/-- Bind a list of definitions left to right. -/
def bindDefs (env : Env) (xs : List (IL.Id × DefDef)) : Env :=
  { env with defs := env.defs.binds xs }

/-- Bind a list of relations left to right. -/
def bindRels (env : Env) (xs : List (IL.Id × RelDef)) : Env :=
  { env with rels := env.rels.binds xs }

/-- Bind a list of grammars left to right. -/
def bindGrams (env : Env) (xs : List (IL.Id × GramDef)) : Env :=
  { env with grams := env.grams.binds xs }

/-! ### `rebind` (`spectec/src/il/env.ml:90-94`)

Each one asserts that the identifier is already bound (`env.ml:63`); see
`Map.rebind`. -/

/-- `rebind_var` (`spectec/src/il/env.ml:90`). -/
def rebindVar (env : Env) (x : IL.Id) (v : VarDef) : Env :=
  { env with vars := env.vars.rebind x v }

/-- `rebind_typ` (`spectec/src/il/env.ml:91`). -/
def rebindTyp (env : Env) (x : IL.Id) (v : TypDef) : Env :=
  { env with typs := env.typs.rebind x v }

/-- `rebind_def` (`spectec/src/il/env.ml:92`). -/
def rebindDef (env : Env) (x : IL.Id) (v : DefDef) : Env :=
  { env with defs := env.defs.rebind x v }

/-- `rebind_rel` (`spectec/src/il/env.ml:93`). -/
def rebindRel (env : Env) (x : IL.Id) (v : RelDef) : Env :=
  { env with rels := env.rels.rebind x v }

/-- `rebind_gram` (`spectec/src/il/env.ml:94`). -/
def rebindGram (env : Env) (x : IL.Id) (v : GramDef) : Env :=
  { env with grams := env.grams.rebind x v }

/-! ### `find?` after `bind`, namespace by namespace -/

@[simp] theorem findVar?_bindVar (env : Env) (x y : IL.Id) (v : VarDef) :
    (env.bindVar x v).findVar? y = if x ≠ "_" ∧ x = y then some v else env.findVar? y := by
  simp [findVar?, bindVar, Map.find?_bind]

/-- `find_opt_typ` after `bind_typ` (`spectec/src/il/env.ml:73,85`). -/
@[simp] theorem findTyp?_bindTyp (env : Env) (x y : IL.Id) (v : TypDef) :
    (env.bindTyp x v).findTyp? y = if x ≠ "_" ∧ x = y then some v else env.findTyp? y := by
  simp [findTyp?, bindTyp, Map.find?_bind]

/-- `find_opt_def` after `bind_def` (`spectec/src/il/env.ml:74,86`). -/
@[simp] theorem findDef?_bindDef (env : Env) (x y : IL.Id) (v : DefDef) :
    (env.bindDef x v).findDef? y = if x ≠ "_" ∧ x = y then some v else env.findDef? y := by
  simp [findDef?, bindDef, Map.find?_bind]

/-- `find_opt_rel` after `bind_rel` (`spectec/src/il/env.ml:75,87`). -/
@[simp] theorem findRel?_bindRel (env : Env) (x y : IL.Id) (v : RelDef) :
    (env.bindRel x v).findRel? y = if x ≠ "_" ∧ x = y then some v else env.findRel? y := by
  simp [findRel?, bindRel, Map.find?_bind]

/-- `find_opt_gram` after `bind_gram` (`spectec/src/il/env.ml:76,88`). -/
@[simp] theorem findGram?_bindGram (env : Env) (x y : IL.Id) (v : GramDef) :
    (env.bindGram x v).findGram? y = if x ≠ "_" ∧ x = y then some v else env.findGram? y := by
  simp [findGram?, bindGram, Map.find?_bind]

/-- Binding the wildcard changes nothing at all — not just the lookups, the
whole environment (`spectec/src/il/env.ml:53-54`). -/
@[simp] theorem bindTyp_underscore (env : Env) (v : TypDef) : env.bindTyp "_" v = env := by
  simp [bindTyp]

/-- Binding the wildcard expression variable changes nothing. -/
@[simp] theorem bindVar_underscore (env : Env) (v : VarDef) : env.bindVar "_" v = env := by
  simp [bindVar]

/-- Binding the wildcard definition changes nothing. -/
@[simp] theorem bindDef_underscore (env : Env) (v : DefDef) : env.bindDef "_" v = env := by
  simp [bindDef]

/-- Binding the wildcard relation changes nothing. -/
@[simp] theorem bindRel_underscore (env : Env) (v : RelDef) : env.bindRel "_" v = env := by
  simp [bindRel]

/-- Binding the wildcard grammar changes nothing. -/
@[simp] theorem bindGram_underscore (env : Env) (v : GramDef) : env.bindGram "_" v = env := by
  simp [bindGram]

end Env

/-! ## Extraction (`spectec/src/il/env.ml:97-118`) -/

/-- `env_of_param` (`spectec/src/il/env.ml:99-104`).  A type, definition or
grammar parameter is entered with an empty right-hand side: the parameter is
abstract inside the declaration it is a parameter of. -/
def envOfParam (env : Env) : Param → Env
  | .expP x t => env.bindVar x t
  | .typP x => env.bindTyp x ([], [])
  | .defP x ps t => env.bindDef x (ps, t, [])
  | .gramP x ps t => env.bindGram x (ps, t, [])

/-- `env_of_params` (`spectec/src/il/env.ml:106`). -/
def envOfParams (env : Env) (ps : List Param) : Env := ps.foldl envOfParam env

mutual

/-- `env_of_def` (`spectec/src/il/env.ml:108-115`), minus the `HintD` branch
(`env.ml:115`), which `IL.Def` has no constructor for.  Note that this never
touches the `vars` namespace: an expression variable is bound by a parameter
(`envOfParam`), never by a top-level definition (`vars_envOfDefs`). -/
def envOfDef (env : Env) : Def → Env
  | .typD x ps insts => env.bindTyp x (ps, insts)
  | .decD x ps t clauses => env.bindDef x (ps, t, clauses)
  | .relD x ps op t rules => env.bindRel x (ps, op, t, rules)
  | .gramD x ps t prods => env.bindGram x (ps, t, prods)
  | .recD ds => envOfDefs env ds

/-- `List.fold_left env_of_def` (`spectec/src/il/env.ml:114,118`), as a
structural recursion so that the `RecD` group of `envOfDef` can call it. -/
def envOfDefs (env : Env) : List Def → Env
  | [] => env
  | d :: ds => envOfDefs (envOfDef env d) ds

end

/-- `env_of_script` (`spectec/src/il/env.ml:117-118`). -/
def envOfScript (ds : Script) : Env := envOfDefs Env.empty ds

/-! ## What `envOfScript` builds -/

/-! ### The bindings a definition contributes

`envOfDef` prepends to each namespace, so `envOfDefs env ds` is `env` with a
*prefix* pushed on top of each of its four declaration maps.  The four
functions below are those prefixes, and `envOfDefs_eq` is the statement that
they are.  Each is the list of bindings its definitions add, newest first, so
a `RecD` group contributes its members in reverse order — which is exactly the
order a left fold leaves them in. -/

mutual

/-- The `typs` bindings `d` adds, newest first.  `Map.empty.bind x v` is
empty when `x` is the wildcard (`spectec/src/il/env.ml:53-54`). -/
def typsOfDef : Def → Map TypDef
  | .typD x ps insts => Map.empty.bind x (ps, insts)
  | .decD _ _ _ _ => Map.empty
  | .relD _ _ _ _ _ => Map.empty
  | .gramD _ _ _ _ => Map.empty
  | .recD ds => typsOfDefs ds

/-- The `typs` bindings `ds` adds, newest first. -/
def typsOfDefs : List Def → Map TypDef
  | [] => Map.empty
  | d :: ds => typsOfDefs ds ++ typsOfDef d

end

mutual

/-- The `defs` bindings `d` adds, newest first. -/
def defsOfDef : Def → Map DefDef
  | .typD _ _ _ => Map.empty
  | .decD x ps t clauses => Map.empty.bind x (ps, t, clauses)
  | .relD _ _ _ _ _ => Map.empty
  | .gramD _ _ _ _ => Map.empty
  | .recD ds => defsOfDefs ds

/-- The `defs` bindings `ds` adds, newest first. -/
def defsOfDefs : List Def → Map DefDef
  | [] => Map.empty
  | d :: ds => defsOfDefs ds ++ defsOfDef d

end

mutual

/-- The `rels` bindings `d` adds, newest first. -/
def relsOfDef : Def → Map RelDef
  | .typD _ _ _ => Map.empty
  | .decD _ _ _ _ => Map.empty
  | .relD x ps op t rules => Map.empty.bind x (ps, op, t, rules)
  | .gramD _ _ _ _ => Map.empty
  | .recD ds => relsOfDefs ds

/-- The `rels` bindings `ds` adds, newest first. -/
def relsOfDefs : List Def → Map RelDef
  | [] => Map.empty
  | d :: ds => relsOfDefs ds ++ relsOfDef d

end

mutual

/-- The `grams` bindings `d` adds, newest first. -/
def gramsOfDef : Def → Map GramDef
  | .typD _ _ _ => Map.empty
  | .decD _ _ _ _ => Map.empty
  | .relD _ _ _ _ _ => Map.empty
  | .gramD x ps t prods => Map.empty.bind x (ps, t, prods)
  | .recD ds => gramsOfDefs ds

/-- The `grams` bindings `ds` adds, newest first. -/
def gramsOfDefs : List Def → Map GramDef
  | [] => Map.empty
  | d :: ds => gramsOfDefs ds ++ gramsOfDef d

end

/-- `envOfDefs` pushes a prefix onto each declaration namespace and leaves
`vars` alone.  This is the one equality of maps in this file that depends on
the representation, and it is the engine for everything below. -/
theorem envOfDefs_eq (env : Env) (ds : List Def) :
    envOfDefs env ds =
      { vars := env.vars,
        typs := typsOfDefs ds ++ env.typs,
        defs := defsOfDefs ds ++ env.defs,
        rels := relsOfDefs ds ++ env.rels,
        grams := gramsOfDefs ds ++ env.grams,
        builtins := env.builtins } := by
  refine envOfDefs.induct
    (motive_1 := fun _ d => ∀ e : Env, envOfDef e d =
      { vars := e.vars, typs := typsOfDef d ++ e.typs, defs := defsOfDef d ++ e.defs,
        rels := relsOfDef d ++ e.rels, grams := gramsOfDef d ++ e.grams,
        builtins := e.builtins })
    (motive_2 := fun _ ds => ∀ e : Env, envOfDefs e ds =
      { vars := e.vars, typs := typsOfDefs ds ++ e.typs, defs := defsOfDefs ds ++ e.defs,
        rels := relsOfDefs ds ++ e.rels, grams := gramsOfDefs ds ++ e.grams,
        builtins := e.builtins })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ env ds env
  · intro _ x ps insts e
    by_cases h : x = "_" <;>
      simp [envOfDef, typsOfDef, defsOfDef, relsOfDef, gramsOfDef, Env.bindTyp, Map.bind, h]
  · intro _ x ps t clauses e
    by_cases h : x = "_" <;>
      simp [envOfDef, typsOfDef, defsOfDef, relsOfDef, gramsOfDef, Env.bindDef, Map.bind, h]
  · intro _ x ps op t rules e
    by_cases h : x = "_" <;>
      simp [envOfDef, typsOfDef, defsOfDef, relsOfDef, gramsOfDef, Env.bindRel, Map.bind, h]
  · intro _ x ps t prods e
    by_cases h : x = "_" <;>
      simp [envOfDef, typsOfDef, defsOfDef, relsOfDef, gramsOfDef, Env.bindGram, Map.bind, h]
  · intro _ ds ih e
    simpa [envOfDef, typsOfDef, defsOfDef, relsOfDef, gramsOfDef] using ih e
  · intro _ e
    simp [envOfDefs, typsOfDefs, defsOfDefs, relsOfDefs, gramsOfDefs, Map.empty]
  · intro _ d ds ih₁ ih₂ e
    simp [envOfDefs, typsOfDefs, defsOfDefs, relsOfDefs, gramsOfDefs, ih₁ e, ih₂]

/-! ### Reading the five namespaces off a script -/

@[simp] theorem vars_envOfDefs (env : Env) (ds : List Def) :
    (envOfDefs env ds).vars = env.vars := by rw [envOfDefs_eq]

/-- The `typs` of a fold. -/
@[simp] theorem typs_envOfDefs (env : Env) (ds : List Def) :
    (envOfDefs env ds).typs = typsOfDefs ds ++ env.typs := by rw [envOfDefs_eq]

/-- The `defs` of a fold. -/
@[simp] theorem defs_envOfDefs (env : Env) (ds : List Def) :
    (envOfDefs env ds).defs = defsOfDefs ds ++ env.defs := by rw [envOfDefs_eq]

/-- The `rels` of a fold. -/
@[simp] theorem rels_envOfDefs (env : Env) (ds : List Def) :
    (envOfDefs env ds).rels = relsOfDefs ds ++ env.rels := by rw [envOfDefs_eq]

/-- The `grams` of a fold. -/
@[simp] theorem grams_envOfDefs (env : Env) (ds : List Def) :
    (envOfDefs env ds).grams = gramsOfDefs ds ++ env.grams := by rw [envOfDefs_eq]

/-- A script binds no expression variable: those come from parameters only
(`spectec/src/il/env.ml:101`). -/
@[simp] theorem vars_envOfScript (ds : Script) : (envOfScript ds).vars = [] := by
  simp [envOfScript, Env.empty]

/-- The `typs` of a script's environment. -/
@[simp] theorem typs_envOfScript (ds : Script) : (envOfScript ds).typs = typsOfDefs ds := by
  simp [envOfScript, Env.empty]

/-- The `defs` of a script's environment. -/
@[simp] theorem defs_envOfScript (ds : Script) : (envOfScript ds).defs = defsOfDefs ds := by
  simp [envOfScript, Env.empty]

/-- The `rels` of a script's environment. -/
@[simp] theorem rels_envOfScript (ds : Script) : (envOfScript ds).rels = relsOfDefs ds := by
  simp [envOfScript, Env.empty]

/-- The `grams` of a script's environment. -/
@[simp] theorem grams_envOfScript (ds : Script) : (envOfScript ds).grams = gramsOfDefs ds := by
  simp [envOfScript, Env.empty]

/-! ### `envOfScript` of an append, and monotonicity -/

@[simp] theorem envOfDefs_nil (env : Env) : envOfDefs env [] = env := rfl

/-- One step of the fold (`spectec/src/il/env.ml:118`). -/
@[simp] theorem envOfDefs_cons (env : Env) (d : Def) (ds : List Def) :
    envOfDefs env (d :: ds) = envOfDefs (envOfDef env d) ds := rfl

/-- The `RecD` branch of `env_of_def` (`spectec/src/il/env.ml:114`). -/
@[simp] theorem envOfDef_recD (env : Env) (ds : List Def) :
    envOfDef env (.recD ds) = envOfDefs env ds := rfl

/-- `envOfDefs` never touches the builtin interpretation: it only adds
declarations.  So an environment built from a script carries whatever
interpretation it was started with — and `envOfScript` starts from
`Env.empty`, which carries none. -/
@[simp] theorem builtins_envOfDefs (env : Env) (ds : List Def) :
    (envOfDefs env ds).builtins = env.builtins := by
  rw [envOfDefs_eq]

/-- A script is read with no interpretation of the primitives installed: the
pinned reading. -/
@[simp] theorem builtins_envOfScript (ds : Script) :
    (envOfScript ds).builtins = Builtins.none := by
  rw [envOfScript, builtins_envOfDefs]; rfl

/-- `envOfDefs` is `List.fold_left env_of_def` (`spectec/src/il/env.ml:118`);
the Lean definition recurses structurally so that the `RecD` branch of
`envOfDef` can call it. -/
theorem envOfDefs_eq_foldl (env : Env) (ds : List Def) :
    envOfDefs env ds = ds.foldl envOfDef env := by
  induction ds generalizing env with
  | nil => rfl
  | cons d ds ih => simp [ih]

/-- `envOfScript` is `List.fold_left env_of_def empty`
(`spectec/src/il/env.ml:117-118`). -/
theorem envOfScript_eq_foldl (ds : Script) : envOfScript ds = ds.foldl envOfDef Env.empty :=
  envOfDefs_eq_foldl _ _

/-- A fold over an append is the fold of the folds. -/
theorem envOfDefs_append (env : Env) (ds₁ ds₂ : List Def) :
    envOfDefs env (ds₁ ++ ds₂) = envOfDefs (envOfDefs env ds₁) ds₂ := by
  induction ds₁ generalizing env with
  | nil => rfl
  | cons d ds ih => simp [ih]

/-- `envOfScript` of an append is the fold of the second half over the
environment of the first. -/
theorem envOfScript_append (ds₁ ds₂ : Script) :
    envOfScript (ds₁ ++ ds₂) = envOfDefs (envOfScript ds₁) ds₂ :=
  envOfDefs_append _ _ _

/-- Folding more definitions never unbinds a type. -/
theorem memTyp_envOfDefs_of_memTyp (env : Env) (ds : List Def) {x : IL.Id}
    (h : env.memTyp x) : (envOfDefs env ds).memTyp x := by
  simpa [Env.memTyp, Map.mem_append] using Or.inr h

/-- Folding more definitions never unbinds a definition. -/
theorem memDef_envOfDefs_of_memDef (env : Env) (ds : List Def) {x : IL.Id}
    (h : env.memDef x) : (envOfDefs env ds).memDef x := by
  simpa [Env.memDef, Map.mem_append] using Or.inr h

/-- Folding more definitions never unbinds a relation. -/
theorem memRel_envOfDefs_of_memRel (env : Env) (ds : List Def) {x : IL.Id}
    (h : env.memRel x) : (envOfDefs env ds).memRel x := by
  simpa [Env.memRel, Map.mem_append] using Or.inr h

/-- Folding more definitions never unbinds a grammar. -/
theorem memGram_envOfDefs_of_memGram (env : Env) (ds : List Def) {x : IL.Id}
    (h : env.memGram x) : (envOfDefs env ds).memGram x := by
  simpa [Env.memGram, Map.mem_append] using Or.inr h

/-- A type declared by the first half of a script survives the second half. -/
theorem memTyp_envOfScript_append_left (ds₁ ds₂ : Script) {x : IL.Id}
    (h : (envOfScript ds₁).memTyp x) : (envOfScript (ds₁ ++ ds₂)).memTyp x := by
  rw [envOfScript_append]
  exact memTyp_envOfDefs_of_memTyp _ _ h

/-! ### Which identifiers a script declares

`DeclaresTyp d x` is the `typs` half of `Il.Free.bound_def`
(`spectec/src/il/free.ml:205-211`): `d` is a `TypD` for `x`, or a `RecD` one of
whose members declares `x`.  `mem_typs_envOfScript_iff` is the statement
downstream validation and evaluation proofs want — an identifier is in the
environment's `typs` exactly when some definition of the script declares it,
nesting included, and is not the wildcard. -/

/-- `d` declares the syntax type `x`, possibly inside a recursive group. -/
inductive DeclaresTyp : Def → IL.Id → Prop where
  /-- `TypD (id, _, _)` declares `id` (`spectec/src/il/env.ml:110`). -/
  | typD (x : IL.Id) (ps : List Param) (insts : List Inst) :
      DeclaresTyp (.typD x ps insts) x
  /-- `RecD ds` declares whatever its members declare
  (`spectec/src/il/env.ml:114`). -/
  | recD {ds : List Def} {d : Def} {x : IL.Id} (hd : d ∈ ds) (h : DeclaresTyp d x) :
      DeclaresTyp (.recD ds) x

/-- The identifiers `typsOfDef d` binds are exactly the non-wildcard types
`d` declares. -/
theorem mem_typsOfDef_iff (d : Def) (x : IL.Id) :
    (typsOfDef d).mem x ↔ x ≠ "_" ∧ DeclaresTyp d x := by
  refine typsOfDef.induct
    (motive_1 := fun d => ∀ y : IL.Id, (typsOfDef d).mem y ↔ y ≠ "_" ∧ DeclaresTyp d y)
    (motive_2 := fun ds => ∀ y : IL.Id, (typsOfDefs ds).mem y ↔
      y ≠ "_" ∧ ∃ d ∈ ds, DeclaresTyp d y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ d x
  · intro y ps insts z
    constructor
    · intro h
      obtain ⟨hy, hz⟩ := (Map.mem_bind _ _ _ _).1 h |>.resolve_right (by simp)
      exact ⟨hz ▸ hy, hz ▸ .typD y ps insts⟩
    · rintro ⟨hz, h⟩
      cases h
      exact (Map.mem_bind _ _ _ _).2 (.inl ⟨hz, rfl⟩)
  · intro _ _ _ _ z; simp [typsOfDef]; rintro - h; cases h
  · intro _ _ _ _ _ z; simp [typsOfDef]; rintro - h; cases h
  · intro _ _ _ _ z; simp [typsOfDef]; rintro - h; cases h
  · intro ds ih z
    simp only [typsOfDef, ih z]
    constructor
    · rintro ⟨hz, d, hd, h⟩; exact ⟨hz, .recD hd h⟩
    · rintro ⟨hz, h⟩; cases h with | recD hd h => exact ⟨hz, _, hd, h⟩
  · intro z; simp [typsOfDefs]
  · intro d ds ih₁ ih₂ z
    simp only [typsOfDefs, Map.mem_append, ih₁ z, ih₂ z]
    constructor
    · rintro (⟨hz, e, he, h⟩ | ⟨hz, h⟩)
      · exact ⟨hz, e, .tail _ he, h⟩
      · exact ⟨hz, d, .head _, h⟩
    · rintro ⟨hz, e, he, h⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact .inr ⟨hz, h⟩
      · exact .inl ⟨hz, e, he, h⟩

/-- The identifiers `typsOfDefs ds` binds are exactly the non-wildcard types
declared by some member of `ds`. -/
theorem mem_typsOfDefs_iff (ds : List Def) (x : IL.Id) :
    (typsOfDefs ds).mem x ↔ x ≠ "_" ∧ ∃ d ∈ ds, DeclaresTyp d x := by
  induction ds with
  | nil => simp [typsOfDefs]
  | cons d ds ih =>
    simp only [typsOfDefs, Map.mem_append, ih, mem_typsOfDef_iff]
    constructor
    · rintro (⟨hz, e, he, h⟩ | ⟨hz, h⟩)
      · exact ⟨hz, e, .tail _ he, h⟩
      · exact ⟨hz, d, .head _, h⟩
    · rintro ⟨hz, e, he, h⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact .inr ⟨hz, h⟩
      · exact .inl ⟨hz, e, he, h⟩

/-- **The characterization of `typs`.**  An identifier is a type of
`envOfScript ds` exactly when some definition of `ds` declares it — inside a
`RecD` group or not — and it is not the wildcard `"_"`
(`spectec/src/il/env.ml:53-54,110,114`). -/
theorem mem_typs_envOfScript_iff (ds : Script) (x : IL.Id) :
    (envOfScript ds).memTyp x ↔ x ≠ "_" ∧ ∃ d ∈ ds, DeclaresTyp d x := by
  simpa [Env.memTyp] using mem_typsOfDefs_iff ds x

/-- `envOfScript` is monotone: a type declared anywhere in the script is in
the environment. -/
theorem memTyp_envOfScript (ds : Script) {d : Def} {x : IL.Id} (hd : d ∈ ds)
    (h : DeclaresTyp d x) (hx : x ≠ "_") : (envOfScript ds).memTyp x :=
  (mem_typs_envOfScript_iff ds x).2 ⟨hx, d, hd, h⟩

/-- The common case of `memTyp_envOfScript`: a top-level `TypD`. -/
theorem memTyp_envOfScript_of_typD (ds : Script) {x : IL.Id} {ps : List Param}
    {insts : List Inst} (hd : Def.typD x ps insts ∈ ds) (hx : x ≠ "_") :
    (envOfScript ds).memTyp x :=
  memTyp_envOfScript ds hd (.typD x ps insts) hx

/-- A top-level `DecD` is in `defs`. -/
theorem memDef_envOfScript_of_decD (ds : Script) {x : IL.Id} {ps : List Param} {t : Typ}
    {clauses : List Clause} (hd : Def.decD x ps t clauses ∈ ds) (hx : x ≠ "_") :
    (envOfScript ds).memDef x := by
  induction ds with
  | nil => cases hd
  | cons d ds ih =>
    rcases List.mem_cons.1 hd with rfl | hd
    · simp [Env.memDef, defsOfDefs, Map.mem_append, Map.mem_bind, defsOfDef, hx]
    · have := ih hd
      simp_all [Env.memDef, defsOfDefs, Map.mem_append]

/-- A top-level `RelD` is in `rels`. -/
theorem memRel_envOfScript_of_relD (ds : Script) {x : IL.Id} {ps : List Param} {op : MixopS}
    {t : Typ} {rules : List Rule} (hd : Def.relD x ps op t rules ∈ ds) (hx : x ≠ "_") :
    (envOfScript ds).memRel x := by
  induction ds with
  | nil => cases hd
  | cons d ds ih =>
    rcases List.mem_cons.1 hd with rfl | hd
    · simp [Env.memRel, relsOfDefs, Map.mem_append, Map.mem_bind, relsOfDef, hx]
    · have := ih hd
      simp_all [Env.memRel, relsOfDefs, Map.mem_append]

/-- A top-level `GramD` is in `grams`. -/
theorem memGram_envOfScript_of_gramD (ds : Script) {x : IL.Id} {ps : List Param} {t : Typ}
    {prods : List IL.Prod} (hd : Def.gramD x ps t prods ∈ ds) (hx : x ≠ "_") :
    (envOfScript ds).memGram x := by
  induction ds with
  | nil => cases hd
  | cons d ds ih =>
    rcases List.mem_cons.1 hd with rfl | hd
    · simp [Env.memGram, gramsOfDefs, Map.mem_append, Map.mem_bind, gramsOfDef, hx]
    · have := ih hd
      simp_all [Env.memGram, gramsOfDefs, Map.mem_append]

/-! ### Parameters -/

@[simp] theorem envOfParams_nil (env : Env) : envOfParams env [] = env := rfl

/-- One step of `env_of_params` (`spectec/src/il/env.ml:106`). -/
@[simp] theorem envOfParams_cons (env : Env) (p : Param) (ps : List Param) :
    envOfParams env (p :: ps) = envOfParams (envOfParam env p) ps := rfl

/-- `env_of_params` of an append (`spectec/src/il/env.ml:106`). -/
theorem envOfParams_append (env : Env) (ps₁ ps₂ : List Param) :
    envOfParams env (ps₁ ++ ps₂) = envOfParams (envOfParams env ps₁) ps₂ := by
  induction ps₁ generalizing env with
  | nil => rfl
  | cons p ps ih => simp [ih]

/-! ## Examples -/

section Examples

-- The `wasm10` examples at the end of this section are checked by the kernel,
-- which needs more than the default elaboration recursion depth; this is the
-- `set_option` `Silmaril/SpecTec/Specs.lean:29` uses.
set_option maxRecDepth 100000

/-- A three-definition script: a syntax type, a recursive group holding a
function and a second syntax type, and a relation. -/
def exampleScript : Script :=
  [ .typD "valtype" [] [],
    .recD [.decD "size" [] (.numT .natT) [], .typD "instr" [] []],
    .relD "Step" [] "~>" .boolT [] ]

example : (envOfScript exampleScript).memTyp "valtype" := by decide

/-- A type declared inside a `RecD` group is in the environment too. -/
example : (envOfScript exampleScript).memTyp "instr" := by decide

example : (envOfScript exampleScript).memDef "size" := by decide

example : (envOfScript exampleScript).memRel "Step" := by decide

example : (envOfScript exampleScript).memGram "instr" = false := by decide

/-- Nothing declares an expression variable (`vars_envOfScript`). -/
example : (envOfScript exampleScript).vars = [] := by decide

example : (envOfScript exampleScript).findTyp? "valtype" = some ([], []) := rfl

example : (envOfScript exampleScript).findDef? "size" = some ([], .numT .natT, []) := rfl

/-- The wildcard is not bound (`spectec/src/il/env.ml:53-54`). -/
example : envOfScript [.typD "_" [] []] = Env.empty := rfl

/-- A later declaration shadows an earlier one: the duplicate check is
commented out at the pin (`spectec/src/il/env.ml:55-58`). -/
example :
    (envOfScript [.typD "t" [] [], .typD "t" [] [.instD [] [] (.aliasT .boolT)]]).findTyp? "t"
      = some ([], [.instD [] [] (.aliasT .boolT)]) := rfl

/-! ### The environment of the pinned wasm 1.0 specification

`Silmaril.SpecTec.Specs.wasm10` is the 315-definition script imported from
`specs/spectec/wasm-1.0.ast`.  Its definitions are added by the
`spectec_import` elaborator with `Lean.addDecl`, which does not mark them
`@[expose]`, so the plain `public import` above sees only their types; the
extra `import all` is what lets the kernel unfold `wasm10` here.  Each example
below is checked by the kernel, which is why `maxRecDepth` has to be raised —
the same `set_option` `Silmaril/SpecTec/Specs.lean:29` uses. -/

example : Specs.wasm10.length = 315 := by rfl

/-- The 315 definitions declare 89 syntax types, 131 functions, 35 relations
and 61 grammars; the sum exceeds 315 because of the `RecD` groups. -/
example :
    ((envOfScript Specs.wasm10).typs.length, (envOfScript Specs.wasm10).defs.length,
      (envOfScript Specs.wasm10).rels.length, (envOfScript Specs.wasm10).grams.length)
      = (89, 131, 35, 61) := by rfl

/-- `valtype` is a syntax type of wasm 1.0. -/
example : (envOfScript Specs.wasm10).memTyp "valtype" := by rfl

/-- `instr` is declared inside a `rec` group, and is in the environment all
the same. -/
example : (envOfScript Specs.wasm10).memTyp "instr" := by rfl

/-- `min` is a function. -/
example : (envOfScript Specs.wasm10).memDef "min" := by rfl

/-- `Limits_ok` is a relation. -/
example : (envOfScript Specs.wasm10).memRel "Limits_ok" := by rfl

/-- `Bbyte` is a grammar. -/
example : (envOfScript Specs.wasm10).memGram "Bbyte" := by rfl

/-- A miss. -/
example : (envOfScript Specs.wasm10).memTyp "no_such_type" = false := by rfl

/-- The namespaces are separate: `instr` is a type, not a function. -/
example : (envOfScript Specs.wasm10).memDef "instr" = false := by rfl

/-- A lookup that returns the whole right-hand side:
`(typ "resulttype" (inst (alias (iter (var "valtype") opt))))`
(`specs/spectec/wasm-1.0.ast:880`). -/
example : (envOfScript Specs.wasm10).findTyp? "resulttype"
    = some ([], [.instD [] [] (.aliasT (.iterT (.varT "valtype" []) .opt))]) := by rfl

/-- And one from the `defs` namespace:
`(def "Ki" nat (clause (num (nat 1024))))` (`specs/spectec/wasm-1.0.ast:6`). -/
example : (envOfScript Specs.wasm10).findDef? "Ki"
    = some ([], .numT .natT, [.defD [] [] (.numE (.natN 1024)) []]) := by rfl

end Examples

end Silmaril.SpecTec.Sem
