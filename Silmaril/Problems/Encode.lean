module

public import Lean

/-!
# Canonical statement encoding

The encoding that `sil spec` hashes (`scripts/Spec.lean`, `docs/Spec.md`) and
that the problems format (`docs/Problems.md`) uses for statement hashes. It is
defined once, here, so that a milestone hash and a problem statement hash of
the same proposition agree.

The encoding drops binder names and `mdata` and replaces universe parameters
by their index, so renaming a bound variable or a universe is not a statement
change, while an added hypothesis, a weakened conclusion or a different
constant is. Binder *info* is kept: making a hypothesis implicit changes how
the theorem may be used. Constants are encoded by name, not unfolded; the
*closure* encoding (`encodeClosure`) additionally covers the definitions a
statement mentions.

Hashing (`sha256:` of the UTF-8 encoding) is done by the consumers
(`tools/sil/src/spec.rs`, `scripts/problems/check.py`).
-/

public meta section

namespace Silmaril.Problems.Encode

open Lean

/-- Canonical form of a universe level. -/
partial def encodeLevel (params : Std.HashMap Name Nat) : Level → String
  | .zero => "0"
  | .succ l => "s(" ++ encodeLevel params l ++ ")"
  | .max a b => "m(" ++ encodeLevel params a ++ "," ++ encodeLevel params b ++ ")"
  | .imax a b => "i(" ++ encodeLevel params a ++ "," ++ encodeLevel params b ++ ")"
  | .param name => match params[name]? with
    | some index => "u" ++ toString index
    | none => "U" ++ toString name
  | .mvar id => "?" ++ toString id.name

/-- Canonical form of binder information. -/
def encodeBinder : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Canonical form of an expression. -/
partial def encodeExpr (params : Std.HashMap Name Nat) : Expr → String
  | .bvar index => "b" ++ toString index
  | .fvar id => "f" ++ toString id.name
  | .mvar id => "?" ++ toString id.name
  | .sort level => "S(" ++ encodeLevel params level ++ ")"
  | .const name levels =>
    "C(" ++ toString name ++ ";" ++ ",".intercalate (levels.map (encodeLevel params)) ++ ")"
  | .app fn arg => "A(" ++ encodeExpr params fn ++ "," ++ encodeExpr params arg ++ ")"
  | .lam _ ty body info =>
    "L" ++ encodeBinder info ++ "(" ++ encodeExpr params ty ++ "," ++ encodeExpr params body ++ ")"
  | .forallE _ ty body info =>
    "P" ++ encodeBinder info ++ "(" ++ encodeExpr params ty ++ "," ++ encodeExpr params body ++ ")"
  | .letE _ ty value body _ =>
    "E(" ++ encodeExpr params ty ++ "," ++ encodeExpr params value ++ ","
      ++ encodeExpr params body ++ ")"
  | .lit (.natVal n) => "N" ++ toString n
  | .lit (.strVal s) => "T" ++ s.quote
  | .mdata _ body => encodeExpr params body
  | .proj struct index body =>
    "J(" ++ toString struct ++ "," ++ toString index ++ "," ++ encodeExpr params body ++ ")"

/-- The universe-parameter index map of a declaration. -/
def paramsOf (info : ConstantInfo) : Std.HashMap Name Nat :=
  info.levelParams.toArray.zipIdx.foldl (fun map (name, index) => map.insert name index) {}

/-- Encode an expression in the universe context of `info`, with the `v1` header. -/
def encodeIn (info : ConstantInfo) (e : Expr) : String :=
  "v1;" ++ toString info.levelParams.length ++ ";" ++ encodeExpr (paramsOf info) e

/-- The canonical encoding of a declaration's statement (its type). This is
what `sil spec` hashes for a `@[milestone]`. -/
def encodeStatement (info : ConstantInfo) : String :=
  encodeIn info info.type

/-- The canonical encoding of a definition's value, or `none` for a
declaration without one. A problem's statement is the *value* of its
`Prop`-valued definition, so this is what a problem's statement hash covers. -/
def encodeValue? (info : ConstantInfo) : Option String :=
  match info with
  | .defnInfo d => some (encodeIn info d.value)
  | .opaqueInfo _ => none
  | _ => none

/-- The constants a declaration mentions: its type, and its value unless it is
a theorem (proofs are irrelevant to what a statement says). -/
def statementConstants (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  match info with
  | .thmInfo _ => fromType
  | .inductInfo i => fromType ++ i.ctors.toArray
  | .ctorInfo c => fromType.push c.induct
  | _ => match info.value? with
    | some v => fromType ++ v.getUsedConstants
    | none => fromType

/--
The closure of `root` over the constants it mentions, restricted to those
`inScope` accepts (normally: declared in a module of the developing package,
not in `Init`, `Lean` or Mathlib). Sorted by name. The root is always included.
-/
partial def closure (env : Environment) (inScope : Name → Bool) (root : Name) : Array Name :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | n :: rest =>
      if seen.contains n then go rest seen
      else
        let seen := seen.insert n
        match env.find? n with
        | none => go rest seen
        | some info =>
          let next := (statementConstants info).toList.filter fun m => inScope m && !seen.contains m
          go (next ++ rest) seen
  (go [root] {}).toArray.qsort Name.quickLt

/-- The kind tag of a declaration. -/
def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- One line of the closure encoding: the declaration's kind, name, type and,
for a non-theorem, its value. -/
def encodeClosureItem (info : ConstantInfo) : String :=
  let value := match info with
    | .thmInfo _ => ""
    | _ => match info.value? with
      | some v => encodeIn info v
      | none => ""
  kindOf info ++ " " ++ toString info.name ++ " : " ++ encodeStatement info ++ " := " ++ value

/-- The closure encoding of `root`: one `encodeClosureItem` line per in-scope
declaration it (transitively) mentions, sorted by name. Unlike the statement
encoding, this changes when a definition the statement uses changes. -/
def encodeClosure (env : Environment) (inScope : Name → Bool) (root : Name) : String :=
  "closure-v1\n" ++ "\n".intercalate
    ((closure env inScope root).toList.filterMap fun n =>
      (env.find? n).map encodeClosureItem)

end Silmaril.Problems.Encode
