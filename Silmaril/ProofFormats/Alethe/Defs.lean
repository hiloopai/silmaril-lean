module

public import Silmaril.Logic.Consequence.Resolution.Defs
public import Silmaril.Logic.Smt.SExpr.Defs

/-!
# Alethe proofs: a documented propositional fragment, read and checked

`checkRefutation problem proof` reads an SMT-LIB problem and an Alethe proof (as cvc5 prints it:
optionally `unsat`, then a list of commands), translates the proof into indexed lines of the
clause derivation system `Silmaril.Consequence.Resolution.system`, and checks them against the
problem's assertions. It returns the assertions, which the proof then **refutes**
(`Thms.checkRefutation_sound`: no valuation of atoms satisfies them all).

**The problem**: `set-logic`, `set-info`, `set-option`, `declare-sort`, `declare-const`,
`declare-fun`, `assert`, `check-sat` and `exit` commands. Anything else (in particular
`define-fun`, which would change what an atom means) is refused.

**The proof** (`AletheCommand`):

```
(assume NAME TERM)
(step NAME (cl TERM*) :rule RULE [:premises (NAME*)] [:args (ARG*)])
```

Terms may carry `(! t :named @n)` annotations, which define `@n` as `t` for the rest of the proof;
they are expanded (`expand`). Each `assume` must be one of the problem's assertions. Premises
must name earlier commands.

**The supported rules**, with the clause rules they become (`Silmaril.Consequence.Resolution`):

| Alethe rule | rule | data |
|---|---|---|
| `resolution`, `th_resolution` | `resolution` | the pivots of `:args (p₁ b₁ …)` (required) |
| `or` | `orElim` | |
| `and` | `andElim i` | `:args (i)`, or the index of the conclusion in the premise |
| `not_or` | `notOrElim i` | the index of the conclusion |
| `or_pos`, `or_neg`, `and_pos`, `and_neg` | `orPos`, `orNeg`, `andPos`, `andNeg` | read from the conclusion |
| `contraction` | `contraction` | |
| `true`, `false` | `trueTaut`, `falseTaut` | |

**Refused**, each with a reason (`AletheError`): any other rule (theory rules such as `not_symm`,
`eq_reflexive`, `cong`, arithmetic, `trust`, …), subproofs (`anchor`, `:discharge`), resolution
without pivots, unknown or forward premise names, redefined names, assumptions that are not
assertions, a step the checker rejects, and a proof that does not end with the empty clause.
-/

@[expose] public section

namespace Silmaril.ProofFormats.Alethe

open Silmaril.Logic.Smt (SE readForms)
open Silmaril.Consequence Silmaril.Consequence.Resolution

/-- Why an Alethe proof was not accepted. -/
inductive AletheError where
  | syntax (why : String)
  /-- The problem has a command outside the supported list. -/
  | problem (why : String)
  /-- A proof command (by position) is not `assume` or a supported `step`. -/
  | command (index : Nat) (why : String)
  | unsupportedRule (step rule : String)
  | badArgs (step why : String)
  | unknownPremise (step name : String)
  | duplicateName (name : String)
  | notAnAssertion (name : String)
  /-- The clause checker rejects the translated lines. -/
  | rejected
  | notRefutation
  deriving DecidableEq, Repr

/-- Named terms defined so far. -/
abbrev Env := List (String × SE)

mutual

/-- **Expand named terms**: `(! t :named @n)` defines `@n`; an atom that names a term is replaced
by it. -/
def expand (env : Env) : SE → Except AletheError (SE × Env)
  | .atom a => .ok ((env.lookup a).getD (.atom a), env)
  | .list [.atom "!", t, .atom ":named", .atom n] => do
    let (t', env') ← expand env t
    if (env'.lookup n).isSome then throw (.duplicateName n)
    return (t', (n, t') :: env')
  | .list (.atom "!" :: _) => throw (.syntax "an annotation other than :named")
  | .list xs => do
    let (xs', env') ← expandList env xs
    return (.list xs', env')

/-- Expand a list of terms, left to right. -/
def expandList (env : Env) : List SE → Except AletheError (List SE × Env)
  | [] => .ok ([], env)
  | x :: xs => do
    let (x', env') ← expand env x
    let (xs', env'') ← expandList env' xs
    return (x' :: xs', env'')

end

/-- The problem commands that do not change the meaning of terms. -/
def ignoredProblemCommands : List String :=
  ["set-logic", "set-info", "set-option", "declare-sort", "declare-const", "declare-fun",
   "check-sat", "exit"]

/-- **The assertions of an SMT-LIB problem.** -/
def problemAssertions : List SE → Except AletheError (List SE)
  | [] => .ok []
  | .list [.atom "assert", φ] :: cs => return φ :: (← problemAssertions cs)
  | .list (.atom c :: _) :: cs =>
    if c ∈ ignoredProblemCommands then problemAssertions cs
    else throw (.problem s!"unsupported command {c}")
  | _ :: _ => throw (.problem "a command that is not a list headed by a name")

/-- Keyword arguments of a step: `:key value` pairs. -/
def keywords : List SE → Except AletheError (List (String × SE))
  | [] => .ok []
  | .atom k :: v :: rest =>
    if k.startsWith ":" then return (k, v) :: (← keywords rest)
    else throw (.syntax s!"expected a keyword, got {k}")
  | _ => throw (.syntax "malformed keyword arguments")

/-- The index of `x` in `xs`. -/
def indexOf? (x : SE) (xs : List SE) : Option Nat := xs.findIdx? (· == x)

/-- Resolution pivots `p₁ b₁ p₂ b₂ …`. -/
def pivots (step : String) (env : Env) : List SE → Except AletheError (List (SE × Bool))
  | [] => .ok []
  | p :: .atom b :: rest => do
    let pos ← match b with
      | "true" => pure true
      | "false" => pure false
      | _ => throw (.badArgs step s!"pivot polarity {b}")
    let (p', _) ← expand env p
    return (p', pos) :: (← pivots step env rest)
  | _ => throw (.badArgs step "pivots must come in pairs")

/-- **Elaborate a step's rule** from its name, arguments, premises and conclusion. Untrusted: the
result is checked. -/
def elabRule (step rule : String) (args : List SE) (prems : List Clause) (c : Clause)
    (env : Env) : Except AletheError Rule :=
  match rule, prems, c with
  | "resolution", _, _ | "th_resolution", _, _ =>
    if args.isEmpty then
      throw (.badArgs step "resolution without :args pivots (cvc5: --proof-alethe-res-pivots)")
    else .resolution <$> pivots step env args
  | "or", _, _ => pure .orElim
  | "and", [[.list (.atom "and" :: as)]], [a] =>
    match args with
    | [.atom i] => match i.toNat? with
      | some i => pure (.andElim i)
      | none => throw (.badArgs step s!"index {i}")
    | [] => match indexOf? a as with
      | some i => pure (.andElim i)
      | none => throw (.badArgs step "the conclusion is not a conjunct")
    | _ => throw (.badArgs step "and takes one index")
  | "not_or", [[.list [.atom "not", .list (.atom "or" :: as)]]], [.list [.atom "not", a]] =>
    match indexOf? a as with
    | some i => pure (.notOrElim i)
    | none => throw (.badArgs step "the conclusion is not a negated disjunct")
  | "or_pos", [], .list [.atom "not", .list (.atom "or" :: as)] :: _ => pure (.orPos as)
  | "or_neg", [], [.list (.atom "or" :: as), .list [.atom "not", a]] =>
    match indexOf? a as with
    | some i => pure (.orNeg as i)
    | none => throw (.badArgs step "the conclusion's negated term is not a disjunct")
  | "and_pos", [], [.list [.atom "not", .list (.atom "and" :: as)], a] =>
    match indexOf? a as with
    | some i => pure (.andPos as i)
    | none => throw (.badArgs step "the conclusion's term is not a conjunct")
  | "and_neg", [], .list (.atom "and" :: as) :: _ => pure (.andNeg as)
  | "contraction", _, _ => pure .contraction
  | "true", _, _ => pure .trueTaut
  | "false", _, _ => pure .falseTaut
  | r, _, _ => throw (.unsupportedRule step r)

/-- The proof's commands, after an optional `unsat`, in one list or at top level. -/
def proofCommands : List SE → Except AletheError (List SE)
  | [.atom "unsat", .list cs] => .ok cs
  | .atom "unsat" :: cs => .ok cs
  | [.list cs@(.list _ :: _)] => .ok cs
  | cs => .ok cs

/-- State while reading a proof: named terms, command names (by position), their clauses. -/
structure State where
  env : Env
  names : List String
  clauses : List Clause

/-- **Translate the proof's commands into indexed lines.** -/
def translate (assertions : List SE) : State → Nat → List SE →
    Except AletheError (List (Line Rule Clause))
  | _, _, [] => .ok []
  | st, i, .list [.atom "assume", .atom n, φ] :: cs => do
    if n ∈ st.names then throw (.duplicateName n)
    let (φ', env) ← expand st.env φ
    unless φ' ∈ assertions do throw (.notAnAssertion n)
    let rest ← translate assertions ⟨env, st.names ++ [n], st.clauses ++ [[φ']]⟩ (i + 1) cs
    return .assume [φ'] :: rest
  | st, i, .list (.atom "step" :: .atom n :: .list (.atom "cl" :: lits) :: kws) :: cs => do
    if n ∈ st.names then throw (.duplicateName n)
    let kv ← keywords kws
    for (k, _) in kv do
      unless k ∈ [":rule", ":premises", ":args"] do
        throw (.command i s!"step {n} has {k} (subproofs and other keywords are not supported)")
    let some (.atom rule) := kv.lookup ":rule" | throw (.syntax s!"step {n} has no :rule")
    let premNames ← match kv.lookup ":premises" with
      | some (.list ps) => ps.mapM fun | .atom p => pure p | _ => throw (.syntax s!"step {n}: premises")
      | none => pure []
      | some _ => throw (.syntax s!"step {n}: premises")
    let ixs ← premNames.mapM fun p =>
      match st.names.idxOf? p with
      | some k => pure k
      | none => throw (.unknownPremise n p)
    let args ← match kv.lookup ":args" with
      | some (.list as) => pure as
      | none => pure []
      | some _ => throw (.syntax s!"step {n}: args")
    let (c, env) ← expandList st.env lits
    let prems := ixs.filterMap (st.clauses[·]?)
    let r ← elabRule n rule args prems c env
    let rest ← translate assertions ⟨env, st.names ++ [n], st.clauses ++ [c]⟩ (i + 1) cs
    return .infer r c ixs :: rest
  | _, i, .list (.atom h :: _) :: _ => throw (.command i s!"unsupported command {h}")
  | _, i, _ :: _ => throw (.command i "not a command")

/-- Check translated lines against the assertions (as unit clauses): they must be valid and end
with the empty clause. -/
def finish (assertions : List SE) (ls : List (Line Rule Clause)) : Except AletheError (List SE) :=
  if system.checkLines (assertions.map ([·])) [] ls then
    if (ls.getLast?.map Line.concl) = some [] then .ok assertions else .error .notRefutation
  else .error .rejected

/-- Read the problem's assertions and translate the proof into lines. -/
def read (problem proof : List UInt8) : Except AletheError (List SE × List (Line Rule Clause)) := do
  let some pforms := readForms problem | throw (.syntax "the problem is not S-expressions")
  let assertions ← problemAssertions pforms
  let some forms := readForms proof | throw (.syntax "the proof is not S-expressions")
  let cs ← proofCommands forms
  return (assertions, ← translate assertions ⟨[], [], []⟩ 0 cs)

/-- **Check an Alethe refutation** of an SMT-LIB problem: the problem's assertions, when the
proof checks and ends with the empty clause. -/
def checkRefutation (problem proof : List UInt8) : Except AletheError (List SE) := do
  let (assertions, ls) ← read problem proof
  finish assertions ls

end Silmaril.ProofFormats.Alethe
