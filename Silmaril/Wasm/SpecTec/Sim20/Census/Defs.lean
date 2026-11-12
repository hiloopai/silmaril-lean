module

public import Silmaril.Wasm.SpecTec.Scripts.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata

/-!
# SpecTec 1.0 ↔ 2.0 ↔ 3.0: a census of the reduction rules

Which rules of the three reduction relations `Step`, `Step_read` and `Step_pure` are
byte-identical across the fixed scripts `Scripts.Wasm10.fixed`, `Scripts.Wasm20.fixed` and
`Scripts.Wasm30.fixed`? The answer says which per-rule lemmas proved against one script
transfer verbatim to the next (`docs/projects/spectec/README.md` §1.5, level 1).

`census a b rel` lists the rules of `rel` in `a`, in order, each with a `Verdict` against the
rules of `rel` in `b`. A rule is matched **by name**:

* `same j`: rule `j` of `b` has the same name and the same IL (`ruleS`, the `--ast` rendering,
  which is injective: `Census.ruleEqB_iff`);
* `admOnly j`: same name, and the two IL terms differ only in that `b` writes the type
  `instr` where `a` writes `admininstr` (wasm-3.0 merged administrative instructions into
  `instr`). This is a syntactic check on the rendering, not a semantic one;
* `changed j`: same name, different IL;
* `renamed j x`: no rule of that name in `b`, but rule `j` (named `x`) has the same IL up to
  the name and the `admininstr`/`instr` renaming;
* `absent`: none of the above.

The census compares **rules only**. A `same` rule can still mean something different in the two
scripts, because the types (`instr`, `val`, …) and functions (`$binop_`, …) it mentions are
looked up in each script's own environment. Transferring a per-rule lemma is sound exactly when
the lemma is stated for an arbitrary environment with the rule's provenance (`HasRuleAt`) as a
hypothesis, which is how the Round 6 lemmas are stated.

The census is computed by the kernel (`Silmaril.Wasm.SpecTec.Sim20.Census.Thms`). The errata
of the fixed scripts touch no reduction relation (`Wasm10`: `$utf8`, `Module_ok` and binary
grammars; `Wasm20`: `$dataidx_instrs` and binary grammars; `Wasm30`: binary and text grammars,
`$cont`, `$utf8`), so the census of the original scripts is the same.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Census

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

/-- The rules of the relation `x` in `s`, in order (empty if `x` is not a relation of `s`;
concatenated if it is declared more than once, which no script does). -/
def relRules (s : Script) (x : IL.Id) : List Rule :=
  (namedDefs x s).flatMap fun
    | .relD _ _ _ _ rs => rs
    | _ => []

/-- The name of a rule. -/
def ruleName : Rule → IL.Id
  | .ruleD x _ _ _ _ => x

/-- The rule with its name erased. -/
def anon : Rule → Rule
  | .ruleD _ qs op e prems => .ruleD "" qs op e prems

/-- Two rules have the same IL. -/
def ruleEqB (r r' : Rule) : Bool := ruleS r == ruleS r'

/-- The rendering of the type name `admininstr` as `instr`. -/
def admToInstr (a : String) : String :=
  if a = "\"admininstr\"" then "\"instr\"" else a

mutual
/-- Rename every atom of an S-expression. -/
def renameAtoms (f : String → String) : SExp → SExp
  | .atom a => .atom (f a)
  | .node t cs => .node t (renameAtomsL f cs)

/-- `renameAtoms` on a list. -/
def renameAtomsL (f : String → String) : List SExp → List SExp
  | [] => []
  | c :: cs => renameAtoms f c :: renameAtomsL f cs
end

/-- Two rules have the same IL once `admininstr` is read as `instr`. -/
def admEqB (r r' : Rule) : Bool :=
  renameAtoms admToInstr (ruleS r) == renameAtoms admToInstr (ruleS r')

/-- How a rule of one script fares in another. -/
inductive Verdict where
  /-- Rule `j` has the same name and the same IL. -/
  | same (j : Nat)
  /-- Rule `j` has the same name and the same IL once `admininstr` is read as `instr`. -/
  | admOnly (j : Nat)
  /-- Rule `j` has the same name and a different IL. -/
  | changed (j : Nat)
  /-- No rule has the name; rule `j`, named `x`, has the same IL up to names and
  `admininstr`/`instr`. -/
  | renamed (j : Nat) (x : IL.Id)
  /-- None of the above. -/
  | absent
  deriving DecidableEq, Repr

/-- The verdict on the rule `r` against the rule list `b`. -/
def verdict (b : List Rule) (r : Rule) : Verdict :=
  match b.findIdx? (fun r' => ruleName r' == ruleName r) with
  | some j =>
    match b[j]? with
    | some r' => if ruleEqB r r' then .same j else if admEqB r r' then .admOnly j else .changed j
    | none => .absent
  | none =>
    match b.findIdx? (fun r' => admEqB (anon r) (anon r')) with
    | some j => .renamed j ((b[j]?.map ruleName).getD "")
    | none => .absent

/-- **The census** of the relation `rel` of `a` against `b`: every rule of `rel` in `a`, with
its index and name, and its verdict. -/
def census (a b : Script) (rel : IL.Id) : List (Nat × IL.Id × Verdict) :=
  (relRules a rel).zipIdx.map fun p => (p.2, ruleName p.1, verdict (relRules b rel) p.1)

/-- Rule `i` of `rel` in `a` is rule `j` of `rel` in `b`. -/
def SameAt (a b : Script) (rel : IL.Id) (i j : Nat) : Prop :=
  ∃ r, (relRules a rel)[i]? = some r ∧ (relRules b rel)[j]? = some r

/-- The three reduction relations. -/
def reductionRels : List IL.Id := ["Step_pure", "Step_read", "Step"]

/-- The number of rules with each verdict, as `(same, admOnly, changed, renamed, absent)`. -/
def tally (c : List (Nat × IL.Id × Verdict)) : Nat × Nat × Nat × Nat × Nat :=
  c.foldr (fun e t => match e.2.2, t with
    | .same _, (a, b, c, d, e) => (a + 1, b, c, d, e)
    | .admOnly _, (a, b, c, d, e) => (a, b + 1, c, d, e)
    | .changed _, (a, b, c, d, e) => (a, b, c + 1, d, e)
    | .renamed _ _, (a, b, c, d, e) => (a, b, c, d + 1, e)
    | .absent, (a, b, c, d, e) => (a, b, c, d, e + 1)) (0, 0, 0, 0, 0)

end Silmaril.Wasm.SpecTec.Sim20.Census
