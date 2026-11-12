module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Execution
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Numerics
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `Step_pure`'s numeric block, and the boundary the pinned specification draws

Phase 4, continued.  `Equiv/Execution.lean` reaches 23 of `Step_pure`'s 79
rules and records that "the whole numeric and vector block" is not among them,
noting that the numeric ones are within reach of its machinery but need
`Equiv/Numerics.lean`'s function-level results.  This file is that step, for
the eight scalar rules

| rule | index | `4.3` |
| --- | --- | --- |
| `unop-val` | 46 | `:339` |
| `unop-trap` | 47 | `:342` |
| `binop-val` | 48 | `:346` |
| `binop-trap` | 49 | `:349` |
| `testop` | 50 | `:353` |
| `relop` | 51 | `:357` |
| `cvtop-val` | 52 | `:361` |
| `cvtop-trap` | 53 | `:364` |

leaving the 25 vector rules of the same block alone (`3.2-numerics.vector.spectec`
is untouched, as `Equiv/Numerics.lean` says).

## Why these eight go together

They are the only `Step_pure` rules whose premise is a *call*.  Four shapes:

* `unop-val`, `binop-val`, `cvtop-val` — `-- if c <- $unop_(nt, unop, c_1)`,
  a `MemE` against the operator's result, which is a **list**: these three
  operators are partial, and the list is their option-as-list;
* `unop-trap`, `binop-trap`, `cvtop-trap` — `-- if $unop_(…) = eps`, the
  same call compared against the empty list;
* `testop`, `relop` — `-- if c = $testop_(nt, testop, c_1)`, a plain equality,
  because those two are total.

So the pair (`-val`, `-trap`) partitions the operator's result, and the whole
block reduces to: *what does `$unop_`/`$binop_`/`$testop_`/`$relop_`/`$cvtop__`
denote?*

## What is proved

**Provenance.**  `HasNumericRules` lists the eight with their index in the
pinned stream; `hasNumericRules_wasm30` discharges it by `rfl` against
`Silmaril.SpecTec.Specs.wasm30`, exactly as `hasStepRules_wasm30` does.

**Eight characterisations, in both directions.**  Each `ruleFires_*_iff` says
precisely which values of `Step_pure`'s type the rule derives, with the
premise left as an explicit hypothesis about the operator call.  Neither
direction is weakened.

## The boundary, which is the point of the file

`$binop_` has 19 clauses and `$unop_` 11, so the dispatch is total in the
*opcode*; but almost every clause's body is a call to a scalar function that
the pinned specification declares `hint(builtin)` **with no clause**.
`Equiv/Numerics.lean` proves eighteen of them denote nothing — `$iand_`,
`$ishl_`, `$iclz_`, … — and that `$idiv_`/`$irem_` are defined only at divisor
zero, `$truncz` being builtin too.

The consequence for reduction: `tryClauses` does *not* fall through to the next
clause when a clause's body is undefined — it falls through only when the match
or the premises are undefined (`Res.elimUndef`, `eval.ml:655,665`).  So if the
scalar call denotes nothing, the dispatcher denotes nothing at that opcode, and
then **neither** rule of the pair can fire: `-val` wants a `c` in the result and
`-trap` wants the result to be `eps`, and there is no result at all.  Such an
instruction is *stuck* — not a value, not a trap.

`not_ruleFires_binopVal_of_undefined` and `not_ruleFires_binopTrap_of_undefined`
prove exactly that, **conditionally** on the dispatcher denoting nothing; the
`unop` pair likewise.  Discharging the condition for a particular opcode — that
`$binop_` really denotes nothing at `AND` — is a computation over `$binop_`'s
19-clause list and is *not* done here.  See "What is not reached".

## What is not reached

* **The 25 vector rules** of the same block (`vunop-val` … `vcvtop`).  They
  need `3.2-numerics.vector.spectec`, which `Equiv/Numerics.lean` leaves
  untouched.

* **The unconditional stuckness statement.**  The four
  `not_ruleFires_*_of_undefined` theorems are conditional.  To get
  `¬ Derives … (i32.and …)` outright one needs
  `∀ w, ¬ Applies env "binop_" [I32, AND, c₁, c₂] w`, which means stepping
  `tryClauses` past the `ADD`, `SUB`, `MUL`, `DIV`, `REM` … clauses (whose
  argument patterns fail to match `AND`, so `Res.elimUndef` moves on) and then
  showing the `AND` clause's body `$iand_(…)` is undefined at every fuel.  The
  machinery for the second half exists — `Equiv/Numerics.lean`'s
  `not_callDef_iand_wasm30` — but the first half, a `matchArgs` *failure*
  principle for a list of clauses, does not.  That is the next step.

* **No link to `Silmaril/Wasm/Execution/Core/Step/Numeric.lean`.**  These
  theorems relate the rules to `$unop_`/`$binop_`/… ; relating *those* to
  Silmaril's numeric steps is `Equiv/Numerics.lean`'s `callDef_iadd_intBinOp`
  composed with a bridge for `instr`, and no `derives_*`/`StepImage` theorem
  for the numeric rules exists yet.  `Equiv/Execution.lean`'s `adminV?` does
  not bridge `UNOP`/`BINOP`/`TESTOP`/`RELOP`/`CVTOP`.

* **`Step_pure` as a relation.**  As in `Equiv/Execution.lean`, these are
  `RuleFires` characterisations of individual rules; "`Derives env "Step_pure"`
  implies *this* step" would have to rule out the other 71 rules at every
  value.

* **The quantifier finding carries over.**  `anyRule` still ignores a `RuleD`'s
  `quant list`, so nothing here checks that `c_1` is a `num_(nt)`; the rules
  fire on any values of the right shape.  `Equiv/Execution.lean`'s finding 1
  applies verbatim.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecNumeric

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution

-- The same local simp set `Equiv/Execution.lean` uses to discharge the
-- "this pattern variable is (not) already bound" side conditions.
attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## The eight rules, as the pinned stream records them -/

/-- `Step_pure/unop-val`, rule 46 of the pinned stream. -/
def unopValRule : Rule :=
  (.ruleD "unop-val" [(.expP "nt" (.varT "numtype" [])), (.expP "c_1" (.varT "num_" [(.expA
   (.varE "nt"))])), (.expP "unop" (.varT "unop_" [(.expA (.varE "nt"))])), (.expP "c" (.varT
   "num_" [(.expA (.varE "nt"))]))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE [(.varE
   "nt"), (.varE "c_1")])), (.caseE "UNOP" (.tupE [(.varE "nt"), (.varE "unop")]))]), (.listE
   [(.caseE "CONST" (.tupE [(.varE "nt"), (.varE "c")]))])]) [(.ifPr (.memE (.varE "c")
   (.callE "unop_" [(.expA (.varE "nt")), (.expA (.varE "unop")), (.expA (.varE "c_1"))])))])

/-- `Step_pure/unop-trap`, rule 47 of the pinned stream. -/
def unopTrapRule : Rule :=
  (.ruleD "unop-trap" [(.expP "nt" (.varT "numtype" [])), (.expP "c_1" (.varT "num_" [(.expA
   (.varE "nt"))])), (.expP "unop" (.varT "unop_" [(.expA (.varE "nt"))]))] "%~>%" (.tupE
   [(.listE [(.caseE "CONST" (.tupE [(.varE "nt"), (.varE "c_1")])), (.caseE "UNOP" (.tupE
   [(.varE "nt"), (.varE "unop")]))]), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE
   .eqOp .boolT (.callE "unop_" [(.expA (.varE "nt")), (.expA (.varE "unop")), (.expA (.varE
   "c_1"))]) (.listE [])))])

/-- `Step_pure/binop-val`, rule 48 of the pinned stream. -/
def binopValRule : Rule :=
  (.ruleD "binop-val" [(.expP "nt" (.varT "numtype" [])), (.expP "c_1" (.varT "num_" [(.expA
   (.varE "nt"))])), (.expP "c_2" (.varT "num_" [(.expA (.varE "nt"))])), (.expP "binop"
   (.varT "binop_" [(.expA (.varE "nt"))])), (.expP "c" (.varT "num_" [(.expA (.varE
   "nt"))]))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE [(.varE "nt"), (.varE "c_1")])),
   (.caseE "CONST" (.tupE [(.varE "nt"), (.varE "c_2")])), (.caseE "BINOP" (.tupE [(.varE
   "nt"), (.varE "binop")]))]), (.listE [(.caseE "CONST" (.tupE [(.varE "nt"), (.varE
   "c")]))])]) [(.ifPr (.memE (.varE "c") (.callE "binop_" [(.expA (.varE "nt")), (.expA
   (.varE "binop")), (.expA (.varE "c_1")), (.expA (.varE "c_2"))])))])

/-- `Step_pure/binop-trap`, rule 49 of the pinned stream. -/
def binopTrapRule : Rule :=
  (.ruleD "binop-trap" [(.expP "nt" (.varT "numtype" [])), (.expP "c_1" (.varT "num_" [(.expA
   (.varE "nt"))])), (.expP "c_2" (.varT "num_" [(.expA (.varE "nt"))])), (.expP "binop"
   (.varT "binop_" [(.expA (.varE "nt"))]))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE
   [(.varE "nt"), (.varE "c_1")])), (.caseE "CONST" (.tupE [(.varE "nt"), (.varE "c_2")])),
   (.caseE "BINOP" (.tupE [(.varE "nt"), (.varE "binop")]))]), (.listE [(.caseE "TRAP" (.tupE
   []))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE "binop_" [(.expA (.varE "nt")), (.expA (.varE
   "binop")), (.expA (.varE "c_1")), (.expA (.varE "c_2"))]) (.listE [])))])

/-- `Step_pure/testop`, rule 50 of the pinned stream. -/
def testopRule : Rule :=
  (.ruleD "testop" [(.expP "nt" (.varT "numtype" [])), (.expP "c_1" (.varT "num_" [(.expA
   (.varE "nt"))])), (.expP "testop" (.varT "testop_" [(.expA (.varE "nt"))])), (.expP "c"
   (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE
   "CONST" (.tupE [(.varE "nt"), (.varE "c_1")])), (.caseE "TESTOP" (.tupE [(.varE "nt"),
   (.varE "testop")]))]), (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE "testop_" [(.expA (.varE
   "nt")), (.expA (.varE "testop")), (.expA (.varE "c_1"))])))])

/-- `Step_pure/relop`, rule 51 of the pinned stream. -/
def relopRule : Rule :=
  (.ruleD "relop" [(.expP "nt" (.varT "numtype" [])), (.expP "c_1" (.varT "num_" [(.expA
   (.varE "nt"))])), (.expP "c_2" (.varT "num_" [(.expA (.varE "nt"))])), (.expP "relop"
   (.varT "relop_" [(.expA (.varE "nt"))])), (.expP "c" (.varT "num_" [(.expA (.caseE "I32"
   (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE [(.varE "nt"), (.varE
   "c_1")])), (.caseE "CONST" (.tupE [(.varE "nt"), (.varE "c_2")])), (.caseE "RELOP" (.tupE
   [(.varE "nt"), (.varE "relop")]))]), (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE "relop_" [(.expA
   (.varE "nt")), (.expA (.varE "relop")), (.expA (.varE "c_1")), (.expA (.varE "c_2"))])))])

/-- `Step_pure/cvtop-val`, rule 52 of the pinned stream. -/
def cvtopValRule : Rule :=
  (.ruleD "cvtop-val" [(.expP "nt_1" (.varT "numtype" [])), (.expP "c_1" (.varT "num_" [(.expA
   (.varE "nt_1"))])), (.expP "nt_2" (.varT "numtype" [])), (.expP "cvtop" (.varT "cvtop__"
   [(.expA (.varE "nt_1")), (.expA (.varE "nt_2"))])), (.expP "c" (.varT "num_" [(.expA (.varE
   "nt_2"))]))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE [(.varE "nt_1"), (.varE
   "c_1")])), (.caseE "CVTOP" (.tupE [(.varE "nt_2"), (.varE "nt_1"), (.varE "cvtop")]))]),
   (.listE [(.caseE "CONST" (.tupE [(.varE "nt_2"), (.varE "c")]))])]) [(.ifPr (.memE (.varE
   "c") (.callE "cvtop__" [(.expA (.varE "nt_1")), (.expA (.varE "nt_2")), (.expA (.varE
   "cvtop")), (.expA (.varE "c_1"))])))])

/-- `Step_pure/cvtop-trap`, rule 53 of the pinned stream. -/
def cvtopTrapRule : Rule :=
  (.ruleD "cvtop-trap" [(.expP "nt_1" (.varT "numtype" [])), (.expP "c_1" (.varT "num_"
   [(.expA (.varE "nt_1"))])), (.expP "nt_2" (.varT "numtype" [])), (.expP "cvtop" (.varT
   "cvtop__" [(.expA (.varE "nt_1")), (.expA (.varE "nt_2"))]))] "%~>%" (.tupE [(.listE
   [(.caseE "CONST" (.tupE [(.varE "nt_1"), (.varE "c_1")])), (.caseE "CVTOP" (.tupE [(.varE
   "nt_2"), (.varE "nt_1"), (.varE "cvtop")]))]), (.listE [(.caseE "TRAP" (.tupE []))])])
   [(.ifPr (.cmpE .eqOp .boolT (.callE "cvtop__" [(.expA (.varE "nt_1")), (.expA (.varE
   "nt_2")), (.expA (.varE "cvtop")), (.expA (.varE "c_1"))]) (.listE [])))])

/-- The pinned wasm-3.0 specification has those eight rules at those indices
inside `Step_pure`. -/
structure HasNumericRules (env : Env) : Prop where
  /-- `Step_pure/unop-val`, rule 46. -/
  unopVal : HasRuleAt env "Step_pure" "%~>%" 46 unopValRule
  /-- `Step_pure/unop-trap`, rule 47. -/
  unopTrap : HasRuleAt env "Step_pure" "%~>%" 47 unopTrapRule
  /-- `Step_pure/binop-val`, rule 48. -/
  binopVal : HasRuleAt env "Step_pure" "%~>%" 48 binopValRule
  /-- `Step_pure/binop-trap`, rule 49. -/
  binopTrap : HasRuleAt env "Step_pure" "%~>%" 49 binopTrapRule
  /-- `Step_pure/testop`, rule 50. -/
  testop : HasRuleAt env "Step_pure" "%~>%" 50 testopRule
  /-- `Step_pure/relop`, rule 51. -/
  relop : HasRuleAt env "Step_pure" "%~>%" 51 relopRule
  /-- `Step_pure/cvtop-val`, rule 52. -/
  cvtopVal : HasRuleAt env "Step_pure" "%~>%" 52 cvtopValRule
  /-- `Step_pure/cvtop-trap`, rule 53. -/
  cvtopTrap : HasRuleAt env "Step_pure" "%~>%" 53 cvtopTrapRule

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- Discharged by `rfl` against the pinned stream, as in `Equiv/Execution.lean`. -/
theorem hasNumericRules_wasm30 : HasNumericRules (envOfScript Specs.wasm30) :=
  ⟨⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩⟩

/-! ## Inverting a function call

`Equiv/Validation.lean` built inversion principles for `derives`, for
`matchExp` and for premises; `Equiv/Numerics.lean` added `callDef_of_tryClauses`,
which *constructs* a `CallDef`.  Every rule below needs the other direction —
its premise is a call, and characterising the rule means saying exactly when
the call denotes something — so this section supplies the missing `iff`.

It belongs in `Sem/Eval.lean` beside `evalExp_callE_iff`; it is here because
this is where it is first needed. -/

/-- The clause list of `x` *definitely* fails at `ws`: it is the `hint(builtin)`
case, and the case in which `Sem/Eval.lean`'s `callDef` consults the builtin
interpretation. -/
def TryClausesUndef (env : Env) (cs : List Clause) (ws : List ArgV) : Prop :=
  ∃ n, tryClauses n env cs ws = .error .undef

/-- A call denotes `v` exactly when its arguments denote some `ws`, the
definition is in the environment (after the `ρ`-substitution `eval.ml:645`),
and either its clauses applied to `ws` denote `v`, or they definitely fail and
the builtin interpretation supplies `v` instead. -/
theorem callDef_iff {env : Env} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {v : Value} :
    CallDef env ρ x args v ↔
      ∃ ws ps t cs, EvalArgs env ρ args ws ∧
        env.findDef? ((ρ.findDef? x).getD x) = some (ps, t, cs) ∧
        (TryClauses env cs ws v ∨
          (TryClausesUndef env cs ws ∧
            env.builtins.call ((ρ.findDef? x).getD x) ws = some v)) := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [callDef] at h
    | succ n =>
        simp only [callDef, Res.bind_eq_ok] at h
        obtain ⟨ws, hw, d, hd, hc⟩ := h
        obtain ⟨ps, t, cs⟩ := d
        refine ⟨ws, ps, t, cs, ⟨n, hw⟩, Res.ofOption_eq_ok.1 hd, ?_⟩
        cases hr : tryClauses n env cs ws with
        | ok u =>
            rw [hr, Res.elimUndef_ok] at hc
            exact Or.inl ⟨n, by rw [hr]; exact congrArg _ (Validation.okInj hc)⟩
        | error e =>
            cases e with
            | outOfFuel => rw [hr] at hc; simp [Res.elimUndef] at hc
            | undef =>
                rw [hr, Res.elimUndef] at hc
                exact Or.inr ⟨⟨n, hr⟩, Res.ofOption_eq_ok.1 hc⟩
  · rintro ⟨ws, ps, t, cs, ⟨n₁, hw⟩, hd, hrest⟩
    rcases hrest with ⟨n₂, hc⟩ | ⟨⟨n₂, hu⟩, hb⟩
    · refine ⟨max n₁ n₂ + 1, ?_⟩
      have e1 := evalArgs_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) hw
      have e2 := tryClauses_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) hc
      simp only [callDef, e1, Bind.bind, Except.bind, hd, Res.ofOption_some, e2,
        Res.elimUndef_ok]
    · refine ⟨max n₁ n₂ + 1, ?_⟩
      have e1 := evalArgs_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) hw
      have e2 : tryClauses (max n₁ n₂) env cs ws = .error .undef :=
        tryClauses_undef_of_le (by omega) hu
      simp only [callDef, e1, Bind.bind, Except.bind, hd, Res.ofOption_some, e2,
        Res.elimUndef, hb, Res.ofOption_some]

/-! ## The instruction values the eight rules mention -/

/-- `(UNOP nt unop)`. -/
def unopV (nt op : Value) : Value := .case "UNOP" (.tuple [nt, op])

/-- `(BINOP nt binop)`. -/
def binopV (nt op : Value) : Value := .case "BINOP" (.tuple [nt, op])

/-- `(TESTOP nt testop)`. -/
def testopV (nt op : Value) : Value := .case "TESTOP" (.tuple [nt, op])

/-- `(RELOP nt relop)`. -/
def relopV (nt op : Value) : Value := .case "RELOP" (.tuple [nt, op])

/-- `(CVTOP nt_2 nt_1 cvtop)` — the *target* type comes first in the pinned
conclusion (`1.3-syntax.instructions.spectec`), and the rule's binds are
`nt_1` then `nt_2`, so the two are deliberately not in the same order. -/
def cvtopV (nt₂ nt₁ op : Value) : Value := .case "CVTOP" (.tuple [nt₂, nt₁, op])

/-- `$x` applied to the argument values `ws` denotes `v`.  This is `CallDef`
with the `VarEnv` quotiented away: the rules below bind their arguments to
plain values, so nothing about the matching environment survives into the
premise. -/
def Applies (env : Env) (x : IL.Id) (ws : List ArgV) (v : Value) : Prop :=
  ∃ ps t cs, env.findDef? x = some (ps, t, cs) ∧
    (TryClauses env cs ws v ∨
      (TryClausesUndef env cs ws ∧ env.builtins.call x ws = some v))

/-- **A call denotes at most one value.**  `tryClauses` is a function of its
fuel, monotone in it, so two successes agree; and a success excludes
`TryClausesUndef`, so the clause branch and the builtin branch of `Applies`
cannot both apply.  This is what makes the bounds-checked rule pairs
exclusive: `$table(z, x)` has one length, so an index cannot be both inside
and outside the table. -/
theorem not_tryClauses_and_undef {env : Env} {cs : List Clause} {ws : List ArgV}
    {v : Value} (h₁ : TryClauses env cs ws v) (h₂ : TryClausesUndef env cs ws) : False := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e₁ := Sem.tryClauses_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have e₂ := Sem.tryClauses_undef_of_le (Nat.le_max_right n₁ n₂) h₂
  rw [e₁] at e₂
  simp at e₂

theorem tryClauses_unique {env : Env} {cs : List Clause} {ws : List ArgV}
    {v₁ v₂ : Value} (h₁ : TryClauses env cs ws v₁) (h₂ : TryClauses env cs ws v₂) :
    v₁ = v₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e₁ := Sem.tryClauses_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have e₂ := Sem.tryClauses_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  rw [e₁] at e₂
  simpa using e₂

/-- `Applies` is deterministic, for any builtin interpretation. -/
theorem Applies.unique {env : Env} {x : IL.Id} {ws : List ArgV} {v₁ v₂ : Value}
    (h₁ : Applies env x ws v₁) (h₂ : Applies env x ws v₂) : v₁ = v₂ := by
  obtain ⟨ps₁, t₁, cs₁, hf₁, hc₁⟩ := h₁
  obtain ⟨ps₂, t₂, cs₂, hf₂, hc₂⟩ := h₂
  rw [hf₁] at hf₂
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hf₂
  rcases hc₁ with h₁ | ⟨hu₁, hb₁⟩ <;> rcases hc₂ with h₂ | ⟨hu₂, hb₂⟩
  · exact tryClauses_unique h₁ h₂
  · exact absurd hu₂ (fun h => not_tryClauses_and_undef h₁ h)
  · exact absurd hu₁ (fun h => not_tryClauses_and_undef h₂ h)
  · exact Option.some.inj (hb₁ ▸ hb₂)

/-- Argument evaluation is deterministic.  `Equiv/V1Binary.lean` proves the
same thing as `evalArgs_unique_v1`; both belong in `Sem/Eval.lean` beside
`EvalExp.unique`. -/
theorem evalArgs_unique {env : Env} {ρ : VarEnv} {args : List Arg} {ws₁ ws₂ : List ArgV}
    (h₁ : EvalArgs env ρ args ws₁) (h₂ : EvalArgs env ρ args ws₂) : ws₁ = ws₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e1 := evalArgs_ok_of_le (le_max_left n₁ n₂) h₁
  have e2 := evalArgs_ok_of_le (le_max_right n₁ n₂) h₂
  rw [e1] at e2
  exact Except.ok.inj e2

/-- `Applies` is exactly a `CallDef` whose arguments are variables bound in
`ρ`, provided `ρ` does not rebind the function name. -/
theorem applies_iff_callDef {env : Env} {ρ : VarEnv} {x : IL.Id} {args : List Arg}
    {ws : List ArgV} {v : Value} (hd : ρ.findDef? x = none)
    (ha : EvalArgs env ρ args ws) :
    Applies env x ws v ↔ CallDef env ρ x args v := by
  rw [callDef_iff, hd, Option.getD_none]
  constructor
  · rintro ⟨ps, t, cs, hf, hc⟩
    exact ⟨ws, ps, t, cs, ha, hf, hc⟩
  · rintro ⟨ws', ps, t, cs, ha', hf, hc⟩
    obtain rfl := evalArgs_unique ha ha'
    exact ⟨ps, t, cs, hf, hc⟩

/-- The three-variable argument list every one of the eight premises uses,
evaluated in an environment that binds all three. -/
theorem evalArgs_three {env : Env} {ρ : VarEnv} {x y z : IL.Id} {a b c : Value}
    (hx : ρ.findVal? x = some a) (hy : ρ.findVal? y = some b)
    (hz : ρ.findVal? z = some c) :
    EvalArgs env ρ [.expA (.varE x), .expA (.varE y), .expA (.varE z)]
      [.val a, .val b, .val c] :=
  evalArgs_cons (evalExp_varE_iff.2 hx)
    (evalArgs_cons (evalExp_varE_iff.2 hy)
      (evalArgs_cons (evalExp_varE_iff.2 hz) evalArgs_nil))

/-! ## The eight rules, characterised exactly -/

/-- `Step_pure/testop` (`4.3:353`): `(CONST nt c_1) (TESTOP nt testop) ~> (CONST I32 c)`
when `c = $testop_(nt, testop, c_1)`.  `$testop_` is total — its one clause is
`EQZ` — so there is no companion trap rule. -/
theorem ruleFires_testop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v testopRule ↔
      ∃ nt c₁ op c, v = stepV [constV nt c₁, testopV nt op] [constV i32V c] ∧
        Applies env "testop_" [.val nt, .val op, .val c₁] c := by
  unfold testopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨nt, c₁, τ', rfl, hnt, hc₁⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨nt', op, τ'', rfl, hnt', hop⟩ := matchExps_two_iff.1 hqvs
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt'
    obtain ⟨rfl, rfl⟩ := hnt'
    rw [matchExp_freshVar_iff (by simp)] at hop
    subst hop
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
    obtain ⟨tv, c, υ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp only [Execution.findVal?_bindVal_lit (by simp : ("c":IL.Id) ≠ "_")] at hv₁
    simp only [cmpValues] at hcmp
    have hv12 : v₁ = v₂ := eq_of_beq (by simpa using Validation.okInj hcmp)
    have hc1 : v₁ = c := (Option.some.inj hv₁).symm
    have hv2c : v₂ = c := by rw [← hv12, hc1]
    refine ⟨nt', c₁, op, c, rfl, ?_⟩
    rw [← hv2c]
    refine (applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "nt" nt').bindVal "c_1" c₁).bindVal
      "testop" op).bindVal "c" c) rfl ?_).mpr (evalExp_callE_iff.1 hv₂)
    exact evalArgs_three (by simp) (by simp) (by simp)
  · rintro ⟨nt, c₁, op, c, rfl, happ⟩
    refine ⟨(((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "testop" op).bindVal "c" c,
      (((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "testop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩, Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_, by simp [cmpValues]⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := _) rfl ?_).mp happ)
    exact evalArgs_three (by simp) (by simp) (by simp)

/-- The four-variable argument list `$binop_`, `$relop_` and `$cvtop__` use. -/
theorem evalArgs_four {env : Env} {ρ : VarEnv} {w x y z : IL.Id} {a b c d : Value}
    (hw : ρ.findVal? w = some a) (hx : ρ.findVal? x = some b)
    (hy : ρ.findVal? y = some c) (hz : ρ.findVal? z = some d) :
    EvalArgs env ρ [.expA (.varE w), .expA (.varE x), .expA (.varE y), .expA (.varE z)]
      [.val a, .val b, .val c, .val d] :=
  evalArgs_cons (evalExp_varE_iff.2 hw)
    (evalArgs_cons (evalExp_varE_iff.2 hx)
      (evalArgs_cons (evalExp_varE_iff.2 hy)
        (evalArgs_cons (evalExp_varE_iff.2 hz) evalArgs_nil)))

/-- An equality side condition against a fixed value holds exactly when the
other side denotes that value: `cmpValues` settles `=` by structural equality
(`eval.ml:260-263`). -/
theorem cmpValues_eq_true_iff {u w : Value} :
    cmpValues .eqOp u w = .ok (.bool true) ↔ u = w := by
  simp only [cmpValues, Except.ok.injEq, Value.bool.injEq, beq_iff_eq]

/-- `Step_pure/unop-val` (`4.3:339`): `(CONST nt c_1) (UNOP nt unop) ~> (CONST nt c)`
when `c <- $unop_(nt, unop, c_1)`.  The premise is a `MemE`, so the rule fires
for *every* `c` the operator's result contains; `memValue` is left in the
statement rather than specialised, because nothing in the IL forces the result
to be a list. -/
theorem ruleFires_unopVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v unopValRule ↔
      ∃ nt c₁ op c w, v = stepV [constV nt c₁, unopV nt op] [constV nt c] ∧
        Applies env "unop_" [.val nt, .val op, .val c₁] w ∧
        memValue c w = .ok (.bool true) := by
  unfold unopValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨nt, c₁, τ', rfl, hnt, hc₁⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨nt', op, τ'', rfl, hnt', hop⟩ := matchExps_two_iff.1 hqvs
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt'
    obtain ⟨hnt1, rfl⟩ := hnt'
    subst hnt1
    rw [matchExp_freshVar_iff (by simp)] at hop
    subst hop
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
    obtain ⟨tv, c, υ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_boundVar_iff (w := nt') (by simp)] at htv
    obtain ⟨htv1, rfl⟩ := htv
    subst htv1
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp only [Execution.findVal?_bindVal_lit (by simp : ("c":IL.Id) ≠ "_")] at hv₁
    have hc1 : v₁ = c := (Option.some.inj hv₁).symm
    refine ⟨tv, c₁, op, c, v₂, rfl, ?_, by rw [← hc1]; exact hmem⟩
    refine (applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "nt" tv).bindVal "c_1" c₁).bindVal
      "unop" op).bindVal "c" c) rfl ?_).mpr (evalExp_callE_iff.1 hv₂)
    exact evalArgs_three (by simp) (by simp) (by simp)
  · rintro ⟨nt, c₁, op, c, w, rfl, happ, hmem⟩
    refine ⟨(((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "unop" op).bindVal "c" c,
      (((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "unop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "nt"
      nt).bindVal "c_1" c₁).bindVal "unop" op).bindVal "c" c) rfl ?_).mp happ)
    exact evalArgs_three (by simp) (by simp) (by simp)

/-- `Step_pure/unop-trap` (`4.3:342`): the same two instructions step to `TRAP`
exactly when `$unop_` denotes the *empty* list.  Together with
`ruleFires_unopVal_iff` this partitions the operator's result — and leaves the
third possibility, that the call denotes nothing at all, covered by neither. -/
theorem ruleFires_unopTrap_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v unopTrapRule ↔
      ∃ nt c₁ op, v = stepV [constV nt c₁, unopV nt op] [trapV] ∧
        Applies env "unop_" [.val nt, .val op, .val c₁] (.list []) := by
  unfold unopTrapRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨nt, c₁, τ', rfl, hnt, hc₁⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨nt', op, τ'', rfl, hnt', hop⟩ := matchExps_two_iff.1 hqvs
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt'
    obtain ⟨rfl, rfl⟩ := hnt'
    rw [matchExp_freshVar_iff (by simp)] at hop
    subst hop
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hv₂
    obtain rfl := Validation.evalExps_nil_iff.1 hvs
    obtain rfl := cmpValues_eq_true_iff.1 hcmp
    refine ⟨nt', c₁, op, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "nt" nt').bindVal "c_1"
      c₁).bindVal "unop" op) rfl ?_).mpr (evalExp_callE_iff.1 hv₁)
    exact evalArgs_three (by simp) (by simp) (by simp)
  · rintro ⟨nt, c₁, op, rfl, happ⟩
    refine ⟨((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "unop" op,
      ((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "unop" op,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.list [], .list [], ?_,
      evalExp_listE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩,
      cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "nt"
      nt).bindVal "c_1" c₁).bindVal "unop" op) rfl ?_).mp happ)
    exact evalArgs_three (by simp) (by simp) (by simp)

/-- `Step_pure/cvtop-val` (`4.3:361`): `(CONST nt_1 c_1) (CVTOP nt_2 nt_1 cvtop)
~> (CONST nt_2 c)` when `c <- $cvtop__(nt_1, nt_2, cvtop, c_1)`.  Note that the
instruction carries its *target* type first and the rule binds `nt_1` first, so
the two orders differ; `cvtopV` follows the instruction. -/
theorem ruleFires_cvtopVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v cvtopValRule ↔
      ∃ nt₁ c₁ nt₂ cop c w, v = stepV [constV nt₁ c₁, cvtopV nt₂ nt₁ cop] [constV nt₂ c] ∧
        Applies env "cvtop__" [.val nt₁, .val nt₂, .val cop, .val c₁] w ∧
        memValue c w = .ok (.bool true) := by
  unfold cvtopValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨nt₁, c₁, τ', rfl, hnt₁, hc₁⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hnt₁
    subst hnt₁
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨nt₂, nt₁', cop, σ', τ'', rfl, hnt₂, hnt₁', hcop⟩ := matchExps_three_iff.1 hqvs
    rw [matchExp_freshVar_iff (by simp)] at hnt₂
    subst hnt₂
    rw [matchExp_boundVar_iff (w := nt₁) (by simp)] at hnt₁'
    obtain ⟨rfl, rfl⟩ := hnt₁'
    rw [matchExp_freshVar_iff (by simp)] at hcop
    subst hcop
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
    obtain ⟨tv, c, υ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_boundVar_iff (w := nt₂) (by simp)] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp only [Execution.findVal?_bindVal_lit (by simp : ("c":IL.Id) ≠ "_")] at hv₁
    have hc1 : v₁ = c := (Option.some.inj hv₁).symm
    refine ⟨nt₁', c₁, tv, cop, c, v₂, rfl, ?_, by rw [← hc1]; exact hmem⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "nt_1" nt₁').bindVal "c_1"
      c₁).bindVal "nt_2" tv).bindVal "cvtop" cop).bindVal "c" c) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨nt₁, c₁, nt₂, cop, c, w, rfl, happ, hmem⟩
    refine ⟨((((VarEnv.empty.bindVal "nt_1" nt₁).bindVal "c_1" c₁).bindVal "nt_2"
        nt₂).bindVal "cvtop" cop).bindVal "c" c,
      ((((VarEnv.empty.bindVal "nt_1" nt₁).bindVal "c_1" c₁).bindVal "nt_2"
        nt₂).bindVal "cvtop" cop).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_boundVar_iff (w := nt₁) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt₂) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "nt_1"
      nt₁).bindVal "c_1" c₁).bindVal "nt_2" nt₂).bindVal "cvtop" cop).bindVal "c" c)
      rfl ?_).mp happ)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/cvtop-trap` (`4.3:364`): the companion trap rule, firing exactly
when `$cvtop__` denotes the empty list. -/
theorem ruleFires_cvtopTrap_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v cvtopTrapRule ↔
      ∃ nt₁ c₁ nt₂ cop, v = stepV [constV nt₁ c₁, cvtopV nt₂ nt₁ cop] [trapV] ∧
        Applies env "cvtop__" [.val nt₁, .val nt₂, .val cop, .val c₁] (.list []) := by
  unfold cvtopTrapRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨nt₁, c₁, τ', rfl, hnt₁, hc₁⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hnt₁
    subst hnt₁
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨nt₂, nt₁', cop, σ', τ'', rfl, hnt₂, hnt₁', hcop⟩ := matchExps_three_iff.1 hqvs
    rw [matchExp_freshVar_iff (by simp)] at hnt₂
    subst hnt₂
    rw [matchExp_boundVar_iff (w := nt₁) (by simp)] at hnt₁'
    obtain ⟨rfl, rfl⟩ := hnt₁'
    rw [matchExp_freshVar_iff (by simp)] at hcop
    subst hcop
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hv₂
    obtain rfl := Validation.evalExps_nil_iff.1 hvs
    obtain rfl := cmpValues_eq_true_iff.1 hcmp
    refine ⟨nt₁', c₁, nt₂, cop, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "nt_1" nt₁').bindVal "c_1"
      c₁).bindVal "nt_2" nt₂).bindVal "cvtop" cop) rfl ?_).mpr (evalExp_callE_iff.1 hv₁)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨nt₁, c₁, nt₂, cop, rfl, happ⟩
    refine ⟨(((VarEnv.empty.bindVal "nt_1" nt₁).bindVal "c_1" c₁).bindVal "nt_2"
        nt₂).bindVal "cvtop" cop,
      (((VarEnv.empty.bindVal "nt_1" nt₁).bindVal "c_1" c₁).bindVal "nt_2"
        nt₂).bindVal "cvtop" cop,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_boundVar_iff (w := nt₁) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.list [], .list [], ?_,
      evalExp_listE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩,
      cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "nt_1"
      nt₁).bindVal "c_1" c₁).bindVal "nt_2" nt₂).bindVal "cvtop" cop) rfl ?_).mp happ)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/binop-val` (`4.3:346`): `(CONST nt c_1) (CONST nt c_2) (BINOP nt binop)
~> (CONST nt c)` when `c <- $binop_(nt, binop, c_1, c_2)`. -/
theorem ruleFires_binopVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v binopValRule ↔
      ∃ nt c₁ c₂ op c w,
        v = stepV [constV nt c₁, constV nt c₂, binopV nt op] [constV nt c] ∧
        Applies env "binop_" [.val nt, .val op, .val c₁, .val c₂] w ∧
        memValue c w = .ok (.bool true) := by
  unfold binopValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨nt, c₁, τ', rfl, hnt, hc₁⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨nt', c₂, τ'', rfl, hnt', hc₂⟩ := matchExps_two_iff.1 hqvs
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt'
    obtain ⟨rfl, rfl⟩ := hnt'
    rw [matchExp_freshVar_iff (by simp)] at hc₂
    subst hc₂
    obtain ⟨sv, rfl, hsv⟩ := Validation.matchExp_case_iff.1 h3
    obtain ⟨svs, rfl, hsvs⟩ := Validation.matchExp_tup_iff.1 hsv
    obtain ⟨nt'', op, τ₃, rfl, hnt'', hop⟩ := matchExps_two_iff.1 hsvs
    rw [matchExp_boundVar_iff (w := nt') (by simp)] at hnt''
    obtain ⟨rfl, rfl⟩ := hnt''
    rw [matchExp_freshVar_iff (by simp)] at hop
    subst hop
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
    obtain ⟨tv, c, υ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_boundVar_iff (w := nt'') (by simp)] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp only [Execution.findVal?_bindVal_lit (by simp : ("c":IL.Id) ≠ "_")] at hv₁
    have hc1 : v₁ = c := (Option.some.inj hv₁).symm
    refine ⟨tv, c₁, c₂, op, c, v₂, rfl, ?_, by rw [← hc1]; exact hmem⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "nt" tv).bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "binop" op).bindVal "c" c) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨nt, c₁, c₂, op, c, w, rfl, happ, hmem⟩
    refine ⟨((((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "c_2"
        c₂).bindVal "binop" op).bindVal "c" c,
      ((((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "c_2"
        c₂).bindVal "binop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "nt"
      nt).bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "binop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/binop-trap` (`4.3:349`): the companion trap rule. -/
theorem ruleFires_binopTrap_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v binopTrapRule ↔
      ∃ nt c₁ c₂ op, v = stepV [constV nt c₁, constV nt c₂, binopV nt op] [trapV] ∧
        Applies env "binop_" [.val nt, .val op, .val c₁, .val c₂] (.list []) := by
  unfold binopTrapRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨nt, c₁, τ', rfl, hnt, hc₁⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨nt', c₂, τ'', rfl, hnt', hc₂⟩ := matchExps_two_iff.1 hqvs
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt'
    obtain ⟨rfl, rfl⟩ := hnt'
    rw [matchExp_freshVar_iff (by simp)] at hc₂
    subst hc₂
    obtain ⟨sv, rfl, hsv⟩ := Validation.matchExp_case_iff.1 h3
    obtain ⟨svs, rfl, hsvs⟩ := Validation.matchExp_tup_iff.1 hsv
    obtain ⟨nt'', op, τ₃, rfl, hnt'', hop⟩ := matchExps_two_iff.1 hsvs
    rw [matchExp_boundVar_iff (w := nt') (by simp)] at hnt''
    obtain ⟨rfl, rfl⟩ := hnt''
    rw [matchExp_freshVar_iff (by simp)] at hop
    subst hop
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hv₂
    obtain rfl := Validation.evalExps_nil_iff.1 hvs
    obtain rfl := cmpValues_eq_true_iff.1 hcmp
    refine ⟨nt'', c₁, c₂, op, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "nt" nt'').bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "binop" op) rfl ?_).mpr (evalExp_callE_iff.1 hv₁)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨nt, c₁, c₂, op, rfl, happ⟩
    refine ⟨(((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "c_2"
        c₂).bindVal "binop" op,
      (((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "c_2"
        c₂).bindVal "binop" op,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.list [], .list [], ?_,
      evalExp_listE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩,
      cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "nt"
      nt).bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "binop" op) rfl ?_).mp happ)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/relop` (`4.3:357`): `(CONST nt c_1) (CONST nt c_2) (RELOP nt relop)
~> (CONST I32 c)` when `c = $relop_(nt, relop, c_1, c_2)`.  Like `$testop_`,
`$relop_` is total, so there is no trap rule. -/
theorem ruleFires_relop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v relopRule ↔
      ∃ nt c₁ c₂ op c,
        v = stepV [constV nt c₁, constV nt c₂, relopV nt op] [constV i32V c] ∧
        Applies env "relop_" [.val nt, .val op, .val c₁, .val c₂] c := by
  unfold relopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨nt, c₁, τ', rfl, hnt, hc₁⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨nt', c₂, τ'', rfl, hnt', hc₂⟩ := matchExps_two_iff.1 hqvs
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt'
    obtain ⟨rfl, rfl⟩ := hnt'
    rw [matchExp_freshVar_iff (by simp)] at hc₂
    subst hc₂
    obtain ⟨sv, rfl, hsv⟩ := Validation.matchExp_case_iff.1 h3
    obtain ⟨svs, rfl, hsvs⟩ := Validation.matchExp_tup_iff.1 hsv
    obtain ⟨nt'', op, τ₃, rfl, hnt'', hop⟩ := matchExps_two_iff.1 hsvs
    rw [matchExp_boundVar_iff (w := nt') (by simp)] at hnt''
    obtain ⟨rfl, rfl⟩ := hnt''
    rw [matchExp_freshVar_iff (by simp)] at hop
    subst hop
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
    obtain ⟨tv, c, υ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp only [Execution.findVal?_bindVal_lit (by simp : ("c":IL.Id) ≠ "_")] at hv₁
    simp only [cmpValues] at hcmp
    have hv12 : v₁ = v₂ := eq_of_beq (by simpa using Validation.okInj hcmp)
    have hc1 : v₁ = c := (Option.some.inj hv₁).symm
    have hv2c : v₂ = c := by rw [← hv12, hc1]
    refine ⟨nt'', c₁, c₂, op, c, rfl, ?_⟩
    rw [← hv2c]
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "nt" nt'').bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "relop" op).bindVal "c" c) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨nt, c₁, c₂, op, c, rfl, happ⟩
    refine ⟨((((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "c_2"
        c₂).bindVal "relop" op).bindVal "c" c,
      ((((VarEnv.empty.bindVal "nt" nt).bindVal "c_1" c₁).bindVal "c_2"
        c₂).bindVal "relop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_, by simp [cmpValues]⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "nt"
      nt).bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "relop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-! ## The boundary: an operator the specification does not define

`Equiv/Numerics.lean` proves that eighteen scalar operators — `$iand_`,
`$ishl_`, `$iclz_`, … — are `hint(builtin)` with no clause, so they denote
nothing at all (`not_callDef_iand_wasm30`, `not_callDef_ishl_wasm30`), and
that `$idiv_`/`$irem_` are defined only at divisor zero.

The eight characterisations above turn that into a statement about reduction.
`$binop_`'s `AND` clause has body `$iand_(…)`, and `tryClauses` does *not*
fall through to the next clause when a clause's body is undefined — it only
falls through when the match or the premises are undefined
(`Res.elimUndef`, `eval.ml:655,665`).  So if the scalar call denotes nothing,
the dispatcher denotes nothing, and then **neither** rule of the pair fires:
`-val` wants a `c` in the result and `-trap` wants the result to be `eps`, and
there is no result at all.

The conditional form is immediate from the two `iff`s and is stated here; what
it is conditional on — that `$binop_` really does denote nothing at `AND` — is
a computation over the pinned clause list of `$binop_`, and is **not** proved
in this file.  See "What is not reached". -/

/-- If `$unop_` denotes nothing at the arguments the rule would pick, then
`unop-val` does not fire.  `P` names the argument lists in question, so the
statement can be specialised to one opcode. -/
theorem not_ruleFires_unopVal_of_undefined {env : Env} {v : Value} {P : List ArgV → Prop}
    (hP : ∀ nt op c₁ c, v = stepV [constV nt c₁, unopV nt op] [constV nt c] →
      P [.val nt, .val op, .val c₁])
    (h : ∀ ws, P ws → ∀ w, ¬ Applies env "unop_" ws w) :
    ¬ RuleFires env "%~>%" [] [] v unopValRule := by
  intro hf
  obtain ⟨nt, c₁, op, c, w, heq, happ, -⟩ := ruleFires_unopVal_iff.1 hf
  exact h _ (hP nt op c₁ c heq) w happ

/-- …and neither does `unop-trap`. -/
theorem not_ruleFires_unopTrap_of_undefined {env : Env} {v : Value} {P : List ArgV → Prop}
    (hP : ∀ nt op c₁, v = stepV [constV nt c₁, unopV nt op] [trapV] →
      P [.val nt, .val op, .val c₁])
    (h : ∀ ws, P ws → ∀ w, ¬ Applies env "unop_" ws w) :
    ¬ RuleFires env "%~>%" [] [] v unopTrapRule := by
  intro hf
  obtain ⟨nt, c₁, op, heq, happ⟩ := ruleFires_unopTrap_iff.1 hf
  exact h _ (hP nt op c₁ heq) _ happ

/-- If `$binop_` denotes nothing at the arguments the rule would pick, then
`binop-val` does not fire. -/
theorem not_ruleFires_binopVal_of_undefined {env : Env} {v : Value} {P : List ArgV → Prop}
    (hP : ∀ nt op c₁ c₂ c, v = stepV [constV nt c₁, constV nt c₂, binopV nt op]
        [constV nt c] → P [.val nt, .val op, .val c₁, .val c₂])
    (h : ∀ ws, P ws → ∀ w, ¬ Applies env "binop_" ws w) :
    ¬ RuleFires env "%~>%" [] [] v binopValRule := by
  intro hf
  obtain ⟨nt, c₁, c₂, op, c, w, heq, happ, -⟩ := ruleFires_binopVal_iff.1 hf
  exact h _ (hP nt op c₁ c₂ c heq) w happ

/-- …and neither does `binop-trap`.  Together: an opcode whose scalar function
the pinned specification leaves uninterpreted is a **stuck** configuration — it
neither produces a value nor traps. -/
theorem not_ruleFires_binopTrap_of_undefined {env : Env} {v : Value} {P : List ArgV → Prop}
    (hP : ∀ nt op c₁ c₂, v = stepV [constV nt c₁, constV nt c₂, binopV nt op] [trapV] →
      P [.val nt, .val op, .val c₁, .val c₂])
    (h : ∀ ws, P ws → ∀ w, ¬ Applies env "binop_" ws w) :
    ¬ RuleFires env "%~>%" [] [] v binopTrapRule := by
  intro hf
  obtain ⟨nt, c₁, c₂, op, heq, happ⟩ := ruleFires_binopTrap_iff.1 hf
  exact h _ (hP nt op c₁ c₂ heq) _ happ

end Silmaril.SpecTec.Equiv.ExecNumeric
