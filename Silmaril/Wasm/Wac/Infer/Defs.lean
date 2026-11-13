module

public import Silmaril.Wasm.Wac.Names.Defs
public import Silmaril.Wasm.Wac.CGraph.Defs
public import Silmaril.Wasm.Wac.Syntax.Defs

/-!
# WAC: name inference, as functions and as relations

The naming rules of `LANGUAGE.md` (wac `5a7480c`), as the functions the elaborator
uses and as relations stating each rule with its precedence. `Silmaril.Wasm.Wac.Infer.Thms`
proves every function equal to the unique name its relation allows.

* **Interface-name matching** (`find_matching_interface_name`): a local identifier
  `x` names the *unique* extern whose path ends with `x` (`foo:bar/x`, `foo:bar/x@1.0`),
  unless `x` is itself an extern name. `MatchIface x names n`.
* **Inferred instantiation arguments** `new p { x }` (`InferArg`), in order of
  precedence:
  1. `x` is an instance of an interface with path `p` and the package imports `p`;
  2. `x` is an import or an alias of an export, and the package imports that name;
  3. exactly one import's path ends with `x`;
  4. `x` itself.
* **Named arguments** `new p { x: e }` (`NamedArg`): an identifier `x` names the
  import whose path ends with `x` (if unique), else `x`; a string is verbatim.
* **Access** `e.x` (`TailOrSelf` over the exports of `e`); `e["n"]` is `n`.
* **Export names** `export e;` (`ExportName`): the interface path of an instance,
  else the import name, else the alias's export name; else an `as` is required.
* **Spread arguments** `...c` (`PickExport`): each import not given yet takes the
  export of `c` of the same name, or else the *first* export whose name is
  semver-compatible with it.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

/-! ## Functions -/

/-- The externs among `names` whose path ends with `x`. -/
def tailMatches (x : String) (names : List String) : List String :=
  names.filter fun m => tail m == some x

/-- wac's `find_matching_interface_name`. -/
def matchIface (x : String) (names : List String) : Option String :=
  if x ∈ names then none
  else match tailMatches x names with
    | [n] => some n
    | _ => none

/-- The interface match of `x`, or `x`. -/
def tailOrSelf (x : String) (names : List String) : String := (matchIface x names).getD x

/-- The name an import or alias node carries (`get_import_name`, `get_alias_source`). -/
def CGraph.origin? (g : CGraph) (i : Nat) : Option String := g.importName? i <|> g.aliasName? i

/-- The name of the inferred argument `x` (node `i`) for a package importing `imps`
(`inferred_instantiation_arg`). -/
def inferArg (g : CGraph) (imps : List String) (x : String) (i : Nat) : String :=
  match (g.kindOf i).instId with
  | some p => if p ∈ imps then p else inferArgOrigin g imps x i
  | none => inferArgOrigin g imps x i
where
  inferArgOrigin (g : CGraph) (imps : List String) (x : String) (i : Nat) : String :=
    match g.origin? i with
    | some m => if m ∈ imps then m else tailOrSelf x imps
    | none => tailOrSelf x imps

/-- The name of a named argument (`named_instantiation_arg`). -/
def namedArg (imps : List String) : Syntax.ArgName → String
  | .ident x => tailOrSelf x imps
  | .str s => s

/-- The name an export statement without `as` gives (`infer_export_name`). -/
def exportName? (g : CGraph) (i : Nat) : Option String :=
  match (g.kindOf i).instId with
  | some p => some p
  | none => g.origin? i

/-- The export of an instance matching the import `n` of a spread argument. -/
def pickExport (exps : List String) (n : String) : Option String :=
  if n ∈ exps then some n else exps.find? fun e => compat e n

/-- The (import, export) pairs a spread argument fills: the imports in `expected`
not already supplied, with a matching export. -/
def spreadPlan (exps : List String) (expected supplied : List String) : List (String × String) :=
  expected.filterMap fun n => if n ∈ supplied then none else (pickExport exps n).map (n, ·)

/-! ## Relations -/

/-- `x` names the unique extern of `names` whose path ends with `x`, and is not itself
an extern name. -/
def MatchIface (x : String) (names : List String) (n : String) : Prop :=
  x ∉ names ∧ tailMatches x names = [n]

/-- The interface match of `x` if there is one, else `x`. -/
inductive TailOrSelf (x : String) (names : List String) : String → Prop
  | tail {n : String} : MatchIface x names n → TailOrSelf x names n
  | self : (∀ n, ¬ MatchIface x names n) → TailOrSelf x names x

/-- Rule 1 applies: node `i` is an instance of an imported interface path `p`. -/
def ByIdApplies (g : CGraph) (imps : List String) (i : Nat) (p : String) : Prop :=
  (g.kindOf i).instId = some p ∧ p ∈ imps

/-- Rule 2 applies: node `i` carries the imported name `m`. -/
def ByOriginApplies (g : CGraph) (imps : List String) (i : Nat) (m : String) : Prop :=
  g.origin? i = some m ∧ m ∈ imps

/-- **The inferred-argument rules, in order of precedence.** -/
inductive InferArg (g : CGraph) (imps : List String) (x : String) (i : Nat) : String → Prop
  | byId {p : String} : ByIdApplies g imps i p → InferArg g imps x i p
  | byOrigin {m : String} : (∀ p, ¬ ByIdApplies g imps i p) → ByOriginApplies g imps i m →
      InferArg g imps x i m
  | byTail {n : String} : (∀ p, ¬ ByIdApplies g imps i p) → (∀ m, ¬ ByOriginApplies g imps i m) →
      MatchIface x imps n → InferArg g imps x i n
  | byLocal : (∀ p, ¬ ByIdApplies g imps i p) → (∀ m, ¬ ByOriginApplies g imps i m) →
      (∀ n, ¬ MatchIface x imps n) → InferArg g imps x i x

/-- The name of a named argument. -/
inductive NamedArg (imps : List String) : Syntax.ArgName → String → Prop
  | ident {x n : String} : TailOrSelf x imps n → NamedArg imps (.ident x) n
  | str (s : String) : NamedArg imps (.str s) s

/-- The name an export statement without `as` gives. -/
inductive ExportName (g : CGraph) (i : Nat) : String → Prop
  | byId {p : String} : (g.kindOf i).instId = some p → ExportName g i p
  | byOrigin {m : String} : (g.kindOf i).instId = none → g.origin? i = some m → ExportName g i m

/-- The export a spread argument passes for the import `n`: `n` itself, or else the
first semver-compatible export. -/
inductive PickExport (exps : List String) (n : String) : String → Prop
  | exact : n ∈ exps → PickExport exps n n
  | semver {e : String} (pre post : List String) : n ∉ exps → exps = pre ++ e :: post →
      compat e n = true → (∀ e' ∈ pre, compat e' n = false) → PickExport exps n e

end Silmaril.Wasm.Wac
