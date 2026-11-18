module

public import Silmaril.Formats.LeanNDJSON.Validate.Defs
public import Silmaril.Logic.Consequence.Arithmetic.Derivation.SExp.Thms

/-!
# PA proofs from Lean-NDJSON: lean4export files of proof declarations, read and checked

`importCheck T bytes d` takes a lean4export 3.1.0 file and the name of a declaration in it, and
returns the judgment that declaration proves in `T`, or why not:

1. **decode** the file strictly (`Silmaril.Formats.LeanNDJSON.parseFile`);
2. **validate** its references: every id is the next of its table and every reference is to an
   entry written before it (no duplicates, no forward references, no cycles), and declared names
   are distinct;
3. find the declaration: it must be a **definition** (`def`) with no universe parameters. An
   axiom, theorem, opaque, quotient or inductive declaration is refused: an axiom has no proof
   object, and the other kinds are not proof objects of this format;
4. **translate** its *value* (never its declared type) to the S-expression proof format
   `silmaril.derivation.tree`, by the fixed table below; anything else is refused, naming the
   expression and the constant;
5. **check** the S-expression with `checkTree T` (decode, elaborate, check every step).

Steps 1–4 are untrusted: only step 5 is relied on, so `Thms.importCheck_sound` follows from
`checkTree_sound`. The header metadata, the declared type, and any other declaration in the file
are never taken as evidence.

**The translation table** (implicit and type arguments are skipped; their values are not used):

| Lean constant (applied) | S-expression |
|---|---|
| `ProofTree.assume j`, `ProofTree.infer r c ts` | `(assume J)`, `(infer R J T*)` |
| `List.cons x xs`, `List.nil` | the list's elements |
| `SE.atom s` (a string literal), `SE.list xs` | `s`, `(xs…)` |
| `Seq.mk n Γ φ` | `(seq n (Γ…) φ)` |
| `Formula.bot`, `.equal`, `.imp`, `.conj`, `.disj`, `.all`, `.ex` | `false`, `=`, `->`, `and`, `or`, `forall`, `exists` |
| `Term.var i`, `.zero`, `.succ`, `.add`, `.mul` | `(var i)`, `zero`, `succ`, `+`, `*` |
| a literal `n`, or `OfNat.ofNat T n _` with `T` = `Nat` or `Fin _` | the decimal `n` |
| a constant naming a definition in the file with no universe parameters | its value |

The translation expands shared subterms, so it stops at `sizeLimit` S-expression nodes.
-/

@[expose] public section

namespace Silmaril.ProofFormats.LeanNDJSON.Arithmetic

open Silmaril.Formats.LeanNDJSON
open Silmaril.Consequence.Arithmetic.ND (Seq Theory Rejection checkTree)
open Silmaril.Logic.Smt (SE)

/-- Why a declaration was not imported. -/
inductive ImportError where
  | decode (e : DecodeError)
  /-- A record breaks serial validity (line number, reason). -/
  | invalid (line : Nat) (why : String)
  | duplicateDeclarations
  | missing (decl : String)
  /-- The declaration is not a definition (its kind). -/
  | notDefinition (decl kind : String)
  | universePolymorphic (decl : String)
  /-- An expression (by id) outside the translation table. -/
  | unsupported (expr : Nat) (why : String)
  /-- The proof was read but the checker rejected it. -/
  | rejected (r : Rejection)
  deriving DecidableEq, Repr

/-- The tables of a valid file: names and expressions by id, declarations by name. -/
structure Tables where
  names : Array (Option NameNode)
  exprs : Array ExprNode
  decls : List (Nat × Declaration)

/-- Collect the tables (ids are dense, so pushing in order indexes by id). -/
def Tables.ofEvents (es : List Event) : Tables :=
  es.foldl (init := ⟨#[none], #[], []⟩) fun t e =>
    match e with
    | .name _ n => { t with names := t.names.push (some n) }
    | .expr _ x => { t with exprs := t.exprs.push x }
    | .declaration d => { t with decls := d.names.map (·, d) ++ t.decls }
    | .level _ _ => t

/-- A name's dotted text (`fuel` bounds the prefix chain). -/
def Tables.name? (t : Tables) : (fuel : Nat) → Nat → Option String
  | _, 0 => some ""
  | 0, _ => none
  | fuel + 1, i => do
    match ← t.names[i]?.join with
    | .str p s => let pre ← t.name? fuel p; pure (if pre.isEmpty then s else pre ++ "." ++ s)
    | .num p k => let pre ← t.name? fuel p; pure (if pre.isEmpty then toString k else pre ++ "." ++ toString k)

/-- The declaration with this dotted name. -/
def Tables.decl? (t : Tables) (name : String) : Option Declaration :=
  (t.decls.find? fun (n, _) => t.name? t.names.size n == some name).map (·.2)

/-- The kind of a declaration, for messages. -/
def kindOf : Declaration → String
  | .axiomCode .. => "axiom"
  | .definitionCode .. => "definition"
  | .theoremCode .. => "theorem"
  | .opaqueCode .. => "opaque"
  | .quot .. => "quotient"
  | .inductive .. => "inductive"

/-- The S-expression node budget. -/
def sizeLimit : Nat := 1000000

/-- Translation, with a node budget. -/
abbrev M := ExceptT ImportError (StateM Nat)

/-- Spend one node of the budget. -/
def tick (e : Nat) : M Unit := do
  let b ← get
  if b = 0 then throw (.unsupported e s!"the proof expands beyond {sizeLimit} nodes") else set (b - 1)

/-- An expression node, for messages. -/
def _root_.Silmaril.Formats.LeanNDJSON.ExprNode.describe : ExprNode → String
  | .bvar i => s!"a bound variable (#{i})"
  | .sort _ => "a sort"
  | .const .. => "a constant"
  | .app .. => "an application"
  | .lam .. => "a λ-abstraction"
  | .forallE .. => "a Π-type"
  | .letE .. => "a let-expression"
  | .proj .. => "a projection"
  | .natVal s => s!"the literal {s}"
  | .strVal s => s!"the string {s.quote}"

/-- The head of an application and its arguments. -/
def spine (t : Tables) : (fuel : Nat) → Nat → List Nat → M (ExprNode × Nat × List Nat)
  | 0, e, _ => throw (.unsupported e "application too deep")
  | fuel + 1, e, args =>
    match t.exprs[e]? with
    | some (.app f a) => spine t fuel f (a :: args)
    | some x => pure (x, e, args)
    | none => throw (.unsupported e "no such expression")

/-- The constant at the head of an expression, with its arguments. -/
def head (t : Tables) (e : Nat) : M (String × List Nat) := do
  match ← spine t t.exprs.size e [] with
  | (.const n _, _, args) =>
    match t.name? t.names.size n with
    | some s => pure (s, args)
    | none => throw (.unsupported e "a constant with no name")
  | (x, h, _) => throw (.unsupported h s!"{x.describe} is not a constant application")

/-- A parameterless definition's value. -/
def Tables.delta? (t : Tables) (name : String) : Option Nat :=
  match t.decl? name with
  | some (.definitionCode _ [] _ v _ _ _) => some v
  | _ => none

/-- A string literal. -/
def strLit (t : Tables) (e : Nat) : M String :=
  match t.exprs[e]? with
  | some (.strVal s) => pure s
  | _ => throw (.unsupported e "not a string literal")

/-- A natural-number literal: `n`, or `OfNat.ofNat T n _` with `T` = `Nat` or `Fin _`. -/
def natLit (t : Tables) (fuel : Nat) (e : Nat) : M String := do
  match t.exprs[e]? with
  | some (.natVal s) => pure s
  | _ =>
    let (c, args) ← head t e
    match c, args with
    | "OfNat.ofNat", [ty, n, _] =>
      let (tc, _) ← head t ty
      unless tc = "Nat" || tc = "Fin" do throw (.unsupported e s!"a numeral of type {tc}")
      match t.exprs[n]? with
      | some (.natVal s) => pure s
      | _ => throw (.unsupported n "not a literal")
    | c, [] =>
      match fuel, t.delta? c with
      | fuel + 1, some v => natLit t fuel v
      | _, _ => throw (.unsupported e s!"the constant {c} as a number")
    | c, _ => throw (.unsupported e s!"{c} as a number")

/-- The elements of a list expression. -/
def listOf {α : Type} (t : Tables) (f : Nat → M α) : (fuel : Nat) → Nat → M (List α)
  | 0, e => throw (.unsupported e "list too long")
  | fuel + 1, e => do
    tick e
    match ← head t e with
    | ("List.cons", [_, x, xs]) => return (← f x) :: (← listOf t f fuel xs)
    | ("List.nil", [_]) => return []
    | (c, []) =>
      match t.delta? c with
      | some v => listOf t f fuel v
      | none => throw (.unsupported e s!"the constant {c} as a list")
    | (c, args) => throw (.unsupported e s!"{c} applied to {args.length} arguments, as a list")

/-- **Translate** a proof-object expression to the S-expression proof format. -/
def toSE (t : Tables) : (fuel : Nat) → Nat → M SE
  | 0, e => throw (.unsupported e "too deep")
  | fuel + 1, e => do
    tick e
    let bin (op : String) (a b : Nat) : M SE := do
      return .list [.atom op, ← toSE t fuel a, ← toSE t fuel b]
    match ← head t e with
    | ("Silmaril.Consequence.ProofTree.assume", [_, _, j]) => return .list [.atom "assume", ← toSE t fuel j]
    | ("Silmaril.Consequence.ProofTree.infer", [_, _, r, c, ts]) =>
      return .list (.atom "infer" :: (← toSE t fuel r) :: (← toSE t fuel c) ::
        (← listOf t (toSE t fuel) t.exprs.size ts))
    | ("Silmaril.Logic.Smt.SE.atom", [s]) => return .atom (← strLit t s)
    | ("Silmaril.Logic.Smt.SE.list", [xs]) => return .list (← listOf t (toSE t fuel) t.exprs.size xs)
    | ("Silmaril.Consequence.Arithmetic.ND.Seq.mk", [n, Γ, φ]) =>
      return .list [.atom "seq", .atom (← natLit t fuel n),
        .list (← listOf t (toSE t fuel) t.exprs.size Γ), ← toSE t fuel φ]
    | ("Silmaril.Logic.Arithmetic.Formula.bot", [_]) => return .atom "false"
    | ("Silmaril.Logic.Arithmetic.Formula.equal", [_, a, b]) => bin "=" a b
    | ("Silmaril.Logic.Arithmetic.Formula.imp", [_, a, b]) => bin "->" a b
    | ("Silmaril.Logic.Arithmetic.Formula.conj", [_, a, b]) => bin "and" a b
    | ("Silmaril.Logic.Arithmetic.Formula.disj", [_, a, b]) => bin "or" a b
    | ("Silmaril.Logic.Arithmetic.Formula.all", [_, a]) => return .list [.atom "forall", ← toSE t fuel a]
    | ("Silmaril.Logic.Arithmetic.Formula.ex", [_, a]) => return .list [.atom "exists", ← toSE t fuel a]
    | ("Silmaril.Logic.Arithmetic.Term.var", [_, i]) => return .list [.atom "var", .atom (← natLit t fuel i)]
    | ("Silmaril.Logic.Arithmetic.Term.zero", [_]) => return .atom "zero"
    | ("Silmaril.Logic.Arithmetic.Term.succ", [_, a]) => return .list [.atom "succ", ← toSE t fuel a]
    | ("Silmaril.Logic.Arithmetic.Term.add", [_, a, b]) => bin "+" a b
    | ("Silmaril.Logic.Arithmetic.Term.mul", [_, a, b]) => bin "*" a b
    | (c, []) =>
      match t.delta? c with
      | some v => toSE t fuel v
      | none => throw (.unsupported e s!"the constant {c} (not a parameterless definition in the file)")
    | (c, args) => throw (.unsupported e s!"{c} applied to {args.length} arguments")

/-- Decode and validate a file. -/
def readFile (bytes : List UInt8) : Except ImportError (List Event) := do
  let f ← (parseFile bytes).mapError .decode
  unless serialValid? .initial f.events do
    let (line, why) := (firstInvalid 2 .initial f.events).getD (0, "invalid references")
    throw (.invalid line why)
  unless decide (declNames f.events).Nodup do throw .duplicateDeclarations
  return f.events

/-- **Read a proof declaration** of decoded, validated records as an S-expression of
`silmaril.derivation.tree`. -/
def importTreeFrom (es : List Event) (decl : String) : Except ImportError SE := do
  let t := Tables.ofEvents es
  match t.decl? decl with
  | none => throw (.missing decl)
  | some (.definitionCode _ ps _ v _ _ _) =>
    unless ps.isEmpty do throw (.universePolymorphic decl)
    (toSE t (t.exprs.size + 1) v).run.run' sizeLimit
  | some d => throw (.notDefinition decl (kindOf d))

/-- **Read and check** a proof declaration of decoded, validated records, in `T`. -/
def importCheckFrom (T : Theory) (es : List Event) (decl : String) : Except ImportError Seq := do
  let e ← importTreeFrom es decl
  (checkTree T e).mapError .rejected

/-- Read a proof declaration of a file as an S-expression. -/
def importTree (bytes : List UInt8) (decl : String) : Except ImportError SE := do
  importTreeFrom (← readFile bytes) decl

/-- **Read and check** a proof declaration of a file in `T`: its conclusion, or why not. -/
def importCheck (T : Theory) (bytes : List UInt8) (decl : String) : Except ImportError Seq := do
  importCheckFrom T (← readFile bytes) decl

end Silmaril.ProofFormats.LeanNDJSON.Arithmetic
