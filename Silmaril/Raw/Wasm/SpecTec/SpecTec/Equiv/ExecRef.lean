module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecBuiltins
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `Step_pure`'s reference rules

Phase 4, continued.  `Equiv/Execution.lean` reaches 23 of `Step_pure`'s 79
rules and `Equiv/ExecNumeric.lean` the eight scalar numeric ones.  This file
takes the **reference block** — the eighteen rules that inspect a `ref` and
nothing else, plus the two indirect-call rewritings:

| group | rules | `4.3` |
| --- | --- | --- |
| `br_on_null`, `br_on_non_null` | 15–18 | `:131-147` |
| `ref.i31`, `ref.is_null`, `ref.as_non_null`, `ref.eq` | 31–38 | `:368-396` |
| `i31.get` | 39–40 | `:400-406` |
| `extern.convert_any`, `any.convert_extern` | 42–45 | `:414-428` |
| `call_indirect`, `return_call_indirect` | 19–20 | `:160-170` |

They belong together because none of them needs the store, the frame or a
function call: every premise is either a pattern (`REF.NULL ht` against
`REF.I31_NUM i`) or a structural comparison of two reference values.  That
makes them the largest block of `Step_pure` still reachable with the machinery
already built, and they need nothing from `Equiv/ExecBuiltins.lean`'s
interpretation — which is the point: the specification *does* define them.

`array.new` (rule 41) is left out: its conclusion iterates `val^n`, which needs
`matchExp_iterE_listN_iff` with a bound length, and its premise calls
`$array.new`.  It is noted in "What is not reached".

## What is proved

**Provenance.**  `HasRefRules` lists the twenty with their index in the
pinned stream; `hasRefRules_wasm30` discharges it by `rfl`, as before.  The
rule terms were generated from the `--ast` s-expressions by the same converter
that produced the numeric ones.

**Eighteen characterisations, in both directions.**  Each `ruleFires_*_iff`
says precisely which values of `Step_pure`'s type the rule derives.  The two
that are missing are `ref.i31` and `i31.get-num`, whose *conclusions* name
`$wrap__` and `$extend__`; see the section on them below.

**They hold at any builtin interpretation.**  Nothing here consults
`Env.builtins`, and the statements never mention it, so each theorem is about
the pinned script and about `wasm30WithWasmNumerics` equally.

**A finding: `else` is vacuous in a rule.**  `premHolds` sends `.elsePr` to
`.ok ρ` unconditionally, which is right for a `DecD` (where `tryClauses`
orders the clauses) and wrong for a `RelD` (where `anyRule` does not order the
rules).  So `br_on_null-addr`, `br_on_non_null-addr`, `ref.is_null-false`,
`ref.as_non_null-addr`, `extern.convert_any-addr`, `ref.eq-true` and
`ref.eq-false` all fire on inputs their `-null`/`-true` counterparts also
handle.  `ruleFires_refIsNullFalse_onNull` exhibits the sharpest case:
`(REF.NULL_ADDR) (REF.IS_NULL)` steps to **both** `1` and `0`.

## What is not reached

* **`ref.i31` and `i31.get-num`** — characterising them needs an inversion
  principle for `matchExp` at a `CallE` pattern (which goes through
  `matchDefault`).  The informal argument that they fire at nothing is in the
  section above; it is *not* proved.  The premise-side analogue **is**:
  `Equiv/ExecBuiltins.lean`'s `not_ruleFires_binopAnd_pinned`.
* **`array.new`** (rule 41) — its conclusion iterates `val^n`, needing
  `matchExp_iterE_listN_iff` at a bound length, and its premise calls
  `$array.new`.
* **The rules as a relation.**  As everywhere else in this development these
  are `RuleFires` characterisations of individual rules; "`Derives env
  "Step_pure"` implies *this* step" would have to rule out the other 63 rules
  at every value.
* **No bridge to `Silmaril/Wasm`.**  `Equiv/Execution.lean`'s `adminV?` does
  not encode `REF.I31_NUM`, `REF.EXTERN` or the `br_on_*` instructions, so
  there is no `StepImage` statement for any rule here.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecRef

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## The twenty rules, as the pinned stream records them -/

/-- `Step_pure/br_on_null-null`, rule 15 of the pinned stream. -/
def brOnNullNullRule : Rule :=
  (.ruleD "br_on_null-null" [(.expP "val" (.varT "val" [])), (.expP "l" (.varT "labelidx"
   []))] "%~>%" (.tupE [(.listE [(.subE (.varE "val") (.varT "val" []) (.varT "instr" [])),
   (.caseE "BR_ON_NULL" (.varE "l"))]), (.listE [(.caseE "BR" (.varE "l"))])]) [(.ifPr
   (.cmpE .eqOp .boolT (.varE "val") (.caseE "REF.NULL_ADDR" (.tupE []))))])

/-- `Step_pure/br_on_null-addr`, rule 16 of the pinned stream. -/
def brOnNullAddrRule : Rule :=
  (.ruleD "br_on_null-addr" [(.expP "val" (.varT "val" [])), (.expP "l" (.varT "labelidx"
   []))] "%~>%" (.tupE [(.listE [(.subE (.varE "val") (.varT "val" []) (.varT "instr" [])),
   (.caseE "BR_ON_NULL" (.varE "l"))]), (.listE [(.subE (.varE "val") (.varT "val" [])
   (.varT "instr" []))])]) [.elsePr])

/-- `Step_pure/br_on_non_null-null`, rule 17 of the pinned stream. -/
def brOnNonNullNullRule : Rule :=
  (.ruleD "br_on_non_null-null" [(.expP "val" (.varT "val" [])), (.expP "l" (.varT
   "labelidx" []))] "%~>%" (.tupE [(.listE [(.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])), (.caseE "BR_ON_NON_NULL" (.varE "l"))]), (.listE [])]) [(.ifPr (.cmpE .eqOp
   .boolT (.varE "val") (.caseE "REF.NULL_ADDR" (.tupE []))))])

/-- `Step_pure/br_on_non_null-addr`, rule 18 of the pinned stream. -/
def brOnNonNullAddrRule : Rule :=
  (.ruleD "br_on_non_null-addr" [(.expP "val" (.varT "val" [])), (.expP "l" (.varT
   "labelidx" []))] "%~>%" (.tupE [(.listE [(.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])), (.caseE "BR_ON_NON_NULL" (.varE "l"))]), (.listE [(.subE (.varE "val")
   (.varT "val" []) (.varT "instr" [])), (.caseE "BR" (.varE "l"))])]) [.elsePr])

/-- `Step_pure/ref.i31`, rule 31 of the pinned stream. -/
def refI31Rule : Rule :=
  (.ruleD "ref.i31" [(.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))]))] "%~>%"
   (.tupE [(.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])),
   (.caseE "REF.I31" (.tupE []))]), (.listE [(.caseE "REF.I31_NUM" (.callE "wrap__" [(.expA
   (.numE (.natN 32))), (.expA (.numE (.natN 31))), (.expA (.varE "i"))]))])]) [])

/-- `Step_pure/ref.is_null-true`, rule 32 of the pinned stream. -/
def refIsNullTrueRule : Rule :=
  (.ruleD "ref.is_null-true" [(.expP "ref" (.varT "ref" []))] "%~>%" (.tupE [(.listE [(.subE
   (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.IS_NULL" (.tupE []))]),
   (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.numE
   (.natN 1))]))]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "ref") (.caseE "REF.NULL_ADDR"
   (.tupE []))))])

/-- `Step_pure/ref.is_null-false`, rule 33 of the pinned stream. -/
def refIsNullFalseRule : Rule :=
  (.ruleD "ref.is_null-false" [(.expP "ref" (.varT "ref" []))] "%~>%" (.tupE [(.listE
   [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.IS_NULL" (.tupE
   []))]), (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE
   [(.numE (.natN 0))]))]))])]) [.elsePr])

/-- `Step_pure/ref.as_non_null-null`, rule 34 of the pinned stream. -/
def refAsNonNullNullRule : Rule :=
  (.ruleD "ref.as_non_null-null" [(.expP "ref" (.varT "ref" []))] "%~>%" (.tupE [(.listE
   [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.AS_NON_NULL"
   (.tupE []))]), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE
   "ref") (.caseE "REF.NULL_ADDR" (.tupE []))))])

/-- `Step_pure/ref.as_non_null-addr`, rule 35 of the pinned stream. -/
def refAsNonNullAddrRule : Rule :=
  (.ruleD "ref.as_non_null-addr" [(.expP "ref" (.varT "ref" []))] "%~>%" (.tupE [(.listE
   [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.AS_NON_NULL"
   (.tupE []))]), (.listE [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" []))])])
   [.elsePr])

/-- `Step_pure/ref.eq-null`, rule 36 of the pinned stream. -/
def refEqNullRule : Rule :=
  (.ruleD "ref.eq-null" [(.expP "ref_1" (.varT "ref" [])), (.expP "ref_2" (.varT "ref" []))]
   "%~>%" (.tupE [(.listE [(.subE (.varE "ref_1") (.varT "ref" []) (.varT "instr" [])),
   (.subE (.varE "ref_2") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.EQ" (.tupE
   []))]), (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE
   [(.numE (.natN 1))]))]))])]) [(.ifPr (.binE .andOp .boolT (.cmpE .eqOp .boolT (.varE
   "ref_1") (.caseE "REF.NULL_ADDR" (.tupE []))) (.cmpE .eqOp .boolT (.varE "ref_2") (.caseE
   "REF.NULL_ADDR" (.tupE [])))))])

/-- `Step_pure/ref.eq-true`, rule 37 of the pinned stream. -/
def refEqTrueRule : Rule :=
  (.ruleD "ref.eq-true" [(.expP "ref_1" (.varT "ref" [])), (.expP "ref_2" (.varT "ref" []))]
   "%~>%" (.tupE [(.listE [(.subE (.varE "ref_1") (.varT "ref" []) (.varT "instr" [])),
   (.subE (.varE "ref_2") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.EQ" (.tupE
   []))]), (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE
   [(.numE (.natN 1))]))]))])]) [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "ref_1") (.varE
   "ref_2")))])

/-- `Step_pure/ref.eq-false`, rule 38 of the pinned stream. -/
def refEqFalseRule : Rule :=
  (.ruleD "ref.eq-false" [(.expP "ref_1" (.varT "ref" [])), (.expP "ref_2" (.varT "ref"
   []))] "%~>%" (.tupE [(.listE [(.subE (.varE "ref_1") (.varT "ref" []) (.varT "instr"
   [])), (.subE (.varE "ref_2") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.EQ"
   (.tupE []))]), (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.numE (.natN 0))]))]))])]) [.elsePr])

/-- `Step_pure/i31.get-null`, rule 39 of the pinned stream. -/
def i31GetNullRule : Rule :=
  (.ruleD "i31.get-null" [(.expP "sx" (.varT "sx" []))] "%~>%" (.tupE [(.listE [(.caseE
   "REF.NULL_ADDR" (.tupE [])), (.caseE "I31.GET" (.varE "sx"))]), (.listE [(.caseE "TRAP"
   (.tupE []))])]) [])

/-- `Step_pure/i31.get-num`, rule 40 of the pinned stream. -/
def i31GetNumRule : Rule :=
  (.ruleD "i31.get-num" [(.expP "i" (.varT "u31" [])), (.expP "sx" (.varT "sx" []))] "%~>%"
   (.tupE [(.listE [(.caseE "REF.I31_NUM" (.varE "i")), (.caseE "I31.GET" (.varE "sx"))]),
   (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.callE "extend__" [(.expA
   (.numE (.natN 31))), (.expA (.numE (.natN 32))), (.expA (.varE "sx")), (.expA (.varE
   "i"))])]))])]) [])

/-- `Step_pure/extern.convert_any-null`, rule 42 of the pinned stream. -/
def externConvertAnyNullRule : Rule :=
  (.ruleD "extern.convert_any-null" [(.expP "ref" (.varT "ref" []))] "%~>%" (.tupE [(.listE
   [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "EXTERN.CONVERT_ANY"
   (.tupE []))]), (.listE [(.caseE "REF.NULL_ADDR" (.tupE []))])]) [(.ifPr (.cmpE .eqOp
   .boolT (.varE "ref") (.caseE "REF.NULL_ADDR" (.tupE []))))])

/-- `Step_pure/extern.convert_any-addr`, rule 43 of the pinned stream. -/
def externConvertAnyAddrRule : Rule :=
  (.ruleD "extern.convert_any-addr" [(.expP "ref" (.varT "ref" []))] "%~>%" (.tupE [(.listE
   [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "EXTERN.CONVERT_ANY"
   (.tupE []))]), (.listE [(.caseE "REF.EXTERN" (.varE "ref"))])]) [.elsePr])

/-- `Step_pure/any.convert_extern-null`, rule 44 of the pinned stream. -/
def anyConvertExternNullRule : Rule :=
  (.ruleD "any.convert_extern-null" [] "%~>%" (.tupE [(.listE [(.caseE "REF.NULL_ADDR"
   (.tupE [])), (.caseE "ANY.CONVERT_EXTERN" (.tupE []))]), (.listE [(.caseE "REF.NULL_ADDR"
   (.tupE []))])]) [])

/-- `Step_pure/any.convert_extern-addr`, rule 45 of the pinned stream. -/
def anyConvertExternAddrRule : Rule :=
  (.ruleD "any.convert_extern-addr" [(.expP "ref" (.varT "ref" []))] "%~>%" (.tupE [(.listE
   [(.caseE "REF.EXTERN" (.varE "ref")), (.caseE "ANY.CONVERT_EXTERN" (.tupE []))]), (.listE
   [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" []))])]) [])

/-- `Step_pure/call_indirect`, rule 19 of the pinned stream. -/
def callIndirectRule : Rule :=
  (.ruleD "call_indirect" [(.expP "x" (.varT "idx" [])), (.expP "yy" (.varT "typeuse" []))]
   "%~>%" (.tupE [(.listE [(.caseE "CALL_INDIRECT" (.tupE [(.varE "x"), (.varE "yy")]))]),
   (.listE [(.caseE "TABLE.GET" (.varE "x")), (.caseE "REF.CAST" (.caseE "REF" (.tupE
   [(.optE (some (.caseE "NULL" (.tupE [])))), (.subE (.varE "yy") (.varT "typeuse" [])
   (.varT "heaptype" []))]))), (.caseE "CALL_REF" (.varE "yy"))])]) [])

/-- `Step_pure/return_call_indirect`, rule 20 of the pinned stream. -/
def returnCallIndirectRule : Rule :=
  (.ruleD "return_call_indirect" [(.expP "x" (.varT "idx" [])), (.expP "yy" (.varT "typeuse"
   []))] "%~>%" (.tupE [(.listE [(.caseE "RETURN_CALL_INDIRECT" (.tupE [(.varE "x"), (.varE
   "yy")]))]), (.listE [(.caseE "TABLE.GET" (.varE "x")), (.caseE "REF.CAST" (.caseE "REF"
   (.tupE [(.optE (some (.caseE "NULL" (.tupE [])))), (.subE (.varE "yy") (.varT "typeuse"
   []) (.varT "heaptype" []))]))), (.caseE "RETURN_CALL_REF" (.varE "yy"))])]) [])

/-- The pinned wasm-3.0 specification has those twenty rules at those
indices inside `Step_pure`. -/
structure HasRefRules (env : Env) : Prop where
  /-- `Step_pure/br_on_null-null`, rule 15. -/
  brOnNullNull : HasRuleAt env "Step_pure" "%~>%" 15 brOnNullNullRule
  /-- `Step_pure/br_on_null-addr`, rule 16. -/
  brOnNullAddr : HasRuleAt env "Step_pure" "%~>%" 16 brOnNullAddrRule
  /-- `Step_pure/br_on_non_null-null`, rule 17. -/
  brOnNonNullNull : HasRuleAt env "Step_pure" "%~>%" 17 brOnNonNullNullRule
  /-- `Step_pure/br_on_non_null-addr`, rule 18. -/
  brOnNonNullAddr : HasRuleAt env "Step_pure" "%~>%" 18 brOnNonNullAddrRule
  /-- `Step_pure/ref.i31`, rule 31. -/
  refI31 : HasRuleAt env "Step_pure" "%~>%" 31 refI31Rule
  /-- `Step_pure/ref.is_null-true`, rule 32. -/
  refIsNullTrue : HasRuleAt env "Step_pure" "%~>%" 32 refIsNullTrueRule
  /-- `Step_pure/ref.is_null-false`, rule 33. -/
  refIsNullFalse : HasRuleAt env "Step_pure" "%~>%" 33 refIsNullFalseRule
  /-- `Step_pure/ref.as_non_null-null`, rule 34. -/
  refAsNonNullNull : HasRuleAt env "Step_pure" "%~>%" 34 refAsNonNullNullRule
  /-- `Step_pure/ref.as_non_null-addr`, rule 35. -/
  refAsNonNullAddr : HasRuleAt env "Step_pure" "%~>%" 35 refAsNonNullAddrRule
  /-- `Step_pure/ref.eq-null`, rule 36. -/
  refEqNull : HasRuleAt env "Step_pure" "%~>%" 36 refEqNullRule
  /-- `Step_pure/ref.eq-true`, rule 37. -/
  refEqTrue : HasRuleAt env "Step_pure" "%~>%" 37 refEqTrueRule
  /-- `Step_pure/ref.eq-false`, rule 38. -/
  refEqFalse : HasRuleAt env "Step_pure" "%~>%" 38 refEqFalseRule
  /-- `Step_pure/i31.get-null`, rule 39. -/
  i31GetNull : HasRuleAt env "Step_pure" "%~>%" 39 i31GetNullRule
  /-- `Step_pure/i31.get-num`, rule 40. -/
  i31GetNum : HasRuleAt env "Step_pure" "%~>%" 40 i31GetNumRule
  /-- `Step_pure/extern.convert_any-null`, rule 42. -/
  externConvertAnyNull : HasRuleAt env "Step_pure" "%~>%" 42 externConvertAnyNullRule
  /-- `Step_pure/extern.convert_any-addr`, rule 43. -/
  externConvertAnyAddr : HasRuleAt env "Step_pure" "%~>%" 43 externConvertAnyAddrRule
  /-- `Step_pure/any.convert_extern-null`, rule 44. -/
  anyConvertExternNull : HasRuleAt env "Step_pure" "%~>%" 44 anyConvertExternNullRule
  /-- `Step_pure/any.convert_extern-addr`, rule 45. -/
  anyConvertExternAddr : HasRuleAt env "Step_pure" "%~>%" 45 anyConvertExternAddrRule
  /-- `Step_pure/call_indirect`, rule 19. -/
  callIndirect : HasRuleAt env "Step_pure" "%~>%" 19 callIndirectRule
  /-- `Step_pure/return_call_indirect`, rule 20. -/
  returnCallIndirect : HasRuleAt env "Step_pure" "%~>%" 20 returnCallIndirectRule

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- Discharged by `rfl` against the pinned stream. -/
theorem hasRefRules_wasm30 : HasRefRules (envOfScript Specs.wasm30) :=
  ⟨⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩⟩

/-! ## The values the eighteen rules mention -/

/-- `REF.NULL_ADDR`, the null reference after `$addr`-elaboration. -/
def refNullV : Value := Execution.caseNilV "REF.NULL_ADDR"

/-- `(BR_ON_NULL l)`. -/
def brOnNullV (l : Value) : Value := .case "BR_ON_NULL" l

/-- `(BR_ON_NON_NULL l)`. -/
def brOnNonNullV (l : Value) : Value := .case "BR_ON_NON_NULL" l

/-- `REF.IS_NULL`. -/
def refIsNullV : Value := Execution.caseNilV "REF.IS_NULL"

/-- `REF.AS_NON_NULL`. -/
def refAsNonNullV : Value := Execution.caseNilV "REF.AS_NON_NULL"

/-- `REF.EQ`. -/
def refEqV : Value := Execution.caseNilV "REF.EQ"

/-- `REF.I31`. -/
def refI31V : Value := Execution.caseNilV "REF.I31"

/-- `(REF.I31_NUM i)`. -/
def refI31NumV (i : Value) : Value := .case "REF.I31_NUM" i

/-- `(REF.EXTERN r)`. -/
def refExternV (r : Value) : Value := .case "REF.EXTERN" r

/-- `EXTERN.CONVERT_ANY`. -/
def externConvertAnyV : Value := Execution.caseNilV "EXTERN.CONVERT_ANY"

/-- `ANY.CONVERT_EXTERN`. -/
def anyConvertExternV : Value := Execution.caseNilV "ANY.CONVERT_EXTERN"

/-! ## `else` is vacuous in a rule

`premHolds` sends `.elsePr` to `.ok ρ` unconditionally (`Sem/Eval.lean:1437`),
because in `spectec`'s `il/eval.ml` an `else` premise is a *syntactic* marker
of clause ordering, and ordering is what `tryClauses` uses it for.

For a `DecD` that is sound: `tryClauses` tries clauses in order and only falls
through on a definite failure, so the `else` clause really is the last resort
(`Equiv/ExecNumeric.lean` relies on exactly that for `$sat_u_`).

For a `RelD` it is **not**: `anyRule` takes any rule that fires and imposes no
order at all.  So every `-addr`/`-false` rule below, whose only premise is
`else`, fires on a *null* reference too — the `-null`/`-true` rule's case is
not excluded.  The characterisations state this exactly, and
`ruleFires_refIsNullFalse_onNull` exhibits it. -/

/-- An `else` premise holds in every scope and changes none. -/
theorem premsHold_else_iff {env : Env} {ρ ρ' : VarEnv} :
    PremsHold env ρ [.elsePr] ρ' ↔ ρ' = ρ := by
  rw [Validation.premsHold_cons_iff]
  constructor
  · rintro ⟨σ, hp, hrest⟩
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨n, hn⟩ := hp
    cases n with
    | zero => simp [premHolds] at hn
    | succ n =>
        simp only [premHolds, Except.ok.injEq] at hn
        exact hn.symm
  · rintro rfl
    exact ⟨ρ', ⟨1, by simp [premHolds]⟩, Validation.premsHold_nil_iff.2 rfl⟩

/-- A numeral pattern tests, and binds nothing (`matchExp`'s `NumE` case). -/
theorem matchExp_numE_iff {env : Env} {ρ ρ' : VarEnv} {m : Num} {v : Value} :
    MatchExp env ρ (.numE m) v ρ' ↔ v = .num m ∧ ρ' = ρ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp, Res.assert_eq_ok] at hn
        exact ⟨hn.1, (Validation.okInj hn.2).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, by simp [matchExp, Res.assert]⟩

/-! ## The rules, characterised exactly -/

/-- `Step_pure/br_on_null-null` (`4.3:131`): a null reference branches.  The
premise `val = REF.NULL_ADDR` is settled by `cmpValues` structurally, so it
pins the value exactly. -/
theorem ruleFires_brOnNullNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brOnNullNullRule ↔
      ∃ l, v = Execution.stepV [refNullV, brOnNullV l] [Execution.brV l] := by
  unfold brOnNullNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 h2
    rw [matchExp_freshVar_iff (by simp)] at hlv
    subst hlv
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    rw [matchExp_boundVar_iff (w := lv) (by simp)] at hrvv
    obtain ⟨rfl, rfl⟩ := hrvv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 hv₂
    obtain ⟨ws, hws, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain rfl := Validation.evalExps_nil_iff.1 hws
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hv₁
    exact ⟨rv, rfl⟩
  · rintro ⟨l, rfl⟩
    refine ⟨(VarEnv.empty.bindVal "val" refNullV).bindVal "l" l,
      (VarEnv.empty.bindVal "val" refNullV).bindVal "l" l,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_boundVar_iff (w := l) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    exact evalExp_cmpE_iff.2 ⟨refNullV, refNullV, evalExp_varE_iff.2 (by simp),
      evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩

/-- `Step_pure/br_on_null-addr` (`4.3:135`): the reference stays on the stack.
Its only premise is `else`, which `premHolds` discharges unconditionally, so
the rule fires on **any** reference — including a null one, which
`br_on_null-null` also handles.  The overlap is real, not an artefact of the
statement. -/
theorem ruleFires_brOnNullAddr_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brOnNullAddrRule ↔
      ∃ w l, v = Execution.stepV [w, brOnNullV l] [w] := by
  unfold brOnNullAddrRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 h2
    rw [matchExp_freshVar_iff (by simp)] at hlv
    subst hlv
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := p) (by simp)] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact ⟨r, lv, rfl⟩
  · rintro ⟨w, l, rfl⟩
    refine ⟨(VarEnv.empty.bindVal "val" w).bindVal "l" l,
      (VarEnv.empty.bindVal "val" w).bindVal "l" l,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_sub_iff.2
            ((matchExp_boundVar_iff (w := w) (by simp)).2 ⟨rfl, rfl⟩)⟩⟩⟩,
      premsHold_else_iff.2 rfl⟩

/-- `Step_pure/br_on_non_null-null` (`4.3:139`): a null reference is dropped. -/
theorem ruleFires_brOnNonNullNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brOnNonNullNullRule ↔
      ∃ l, v = Execution.stepV [refNullV, brOnNonNullV l] [] := by
  unfold brOnNonNullNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 h2
    rw [matchExp_freshVar_iff (by simp)] at hlv
    subst hlv
    rw [matchExp_listNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 hv₂
    obtain ⟨ws, hws, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain rfl := Validation.evalExps_nil_iff.1 hws
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hv₁
    exact ⟨lv, rfl⟩
  · rintro ⟨l, rfl⟩
    refine ⟨(VarEnv.empty.bindVal "val" refNullV).bindVal "l" l,
      (VarEnv.empty.bindVal "val" refNullV).bindVal "l" l,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    exact evalExp_cmpE_iff.2 ⟨refNullV, refNullV, evalExp_varE_iff.2 (by simp),
      evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩

/-- `Step_pure/br_on_non_null-addr` (`4.3:143`): a non-null reference branches
— and, `else` being vacuous, so does a null one. -/
theorem ruleFires_brOnNonNullAddr_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brOnNonNullAddrRule ↔
      ∃ w l, v = Execution.stepV [w, brOnNonNullV l] [w, Execution.brV l] := by
  unfold brOnNonNullAddrRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 h2
    rw [matchExp_freshVar_iff (by simp)] at hlv
    subst hlv
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, s, υ, rfl, hr1, hr2⟩ := matchExps_two_iff.1 hbs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := p) (by simp)] at hr1
    obtain ⟨rfl, rfl⟩ := hr1
    obtain ⟨sv, rfl, hsv⟩ := Validation.matchExp_case_iff.1 hr2
    rw [matchExp_boundVar_iff (w := lv) (by simp)] at hsv
    obtain ⟨rfl, rfl⟩ := hsv
    exact ⟨r, sv, rfl⟩
  · rintro ⟨w, l, rfl⟩
    refine ⟨(VarEnv.empty.bindVal "val" w).bindVal "l" l,
      (VarEnv.empty.bindVal "val" w).bindVal "l" l,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2
            ((matchExp_boundVar_iff (w := w) (by simp)).2 ⟨rfl, rfl⟩),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_boundVar_iff (w := l) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩,
      premsHold_else_iff.2 rfl⟩

/-- `Step_pure/ref.is_null-true` (`4.3:376`). -/
theorem ruleFires_refIsNullTrue_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refIsNullTrueRule ↔
      v = Execution.stepV [refNullV, refIsNullV]
        [Execution.constV Execution.i32V (Execution.pctV 1)] := by
  unfold refIsNullTrueRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [matchExp_caseNil_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
    obtain ⟨tv, cv, υ, rfl, htv, hcv⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    obtain ⟨cvv, rfl, hcvv⟩ := Validation.matchExp_case_iff.1 hcv
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcvv
    obtain ⟨nv, rfl, hnv⟩ := matchExps_one_iff.1 hcvs
    rw [matchExp_numE_iff] at hnv
    obtain ⟨rfl, rfl⟩ := hnv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 hv₂
    obtain ⟨ws, hws, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain rfl := Validation.evalExps_nil_iff.1 hws
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hv₁
    rfl
  · rintro rfl
    refine ⟨VarEnv.empty.bindVal "ref" refNullV, VarEnv.empty.bindVal "ref" refNullV,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_one_iff.2 ⟨_, rfl,
                      matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    exact evalExp_cmpE_iff.2 ⟨refNullV, refNullV, evalExp_varE_iff.2 (by simp),
      evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩

/-- `Step_pure/ref.is_null-false` (`4.3:380`).  `else` again being vacuous, the
rule fires on every reference — see `ruleFires_refIsNullFalse_onNull`. -/
theorem ruleFires_refIsNullFalse_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refIsNullFalseRule ↔
      ∃ w, v = Execution.stepV [w, refIsNullV]
        [Execution.constV Execution.i32V (Execution.pctV 0)] := by
  unfold refIsNullFalseRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [matchExp_caseNil_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
    obtain ⟨tv, cv, υ, rfl, htv, hcv⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    obtain ⟨cvv, rfl, hcvv⟩ := Validation.matchExp_case_iff.1 hcv
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcvv
    obtain ⟨nv, rfl, hnv⟩ := matchExps_one_iff.1 hcvs
    rw [matchExp_numE_iff] at hnv
    obtain ⟨rfl, rfl⟩ := hnv
    exact ⟨p, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨VarEnv.empty.bindVal "ref" w, VarEnv.empty.bindVal "ref" w,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_one_iff.2 ⟨_, rfl,
                      matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
      premsHold_else_iff.2 rfl⟩

/-- **The overlap, exhibited.**  `ref.is_null-false` fires on the *null*
reference, so the pinned `Step_pure` derives both `… ~> (CONST I32 1)` and
`… ~> (CONST I32 0)` for `(REF.NULL_ADDR) (REF.IS_NULL)`.  `anyRule` imposes no
order on a relation's rules, and `else` carries no condition. -/
theorem ruleFires_refIsNullFalse_onNull {env : Env} :
    RuleFires env "%~>%" [] []
      (Execution.stepV [refNullV, refIsNullV]
        [Execution.constV Execution.i32V (Execution.pctV 0)]) refIsNullFalseRule :=
  ruleFires_refIsNullFalse_iff.2 ⟨refNullV, rfl⟩

/-- `Step_pure/ref.as_non_null-null` (`4.3:384`): a null reference traps. -/
theorem ruleFires_refAsNonNullNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refAsNonNullNullRule ↔
      v = Execution.stepV [refNullV, refAsNonNullV] [Execution.trapV] := by
  unfold refAsNonNullNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [matchExp_caseNil_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 hv₂
    obtain ⟨ws, hws, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain rfl := Validation.evalExps_nil_iff.1 hws
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hv₁
    rfl
  · rintro rfl
    refine ⟨VarEnv.empty.bindVal "ref" refNullV, VarEnv.empty.bindVal "ref" refNullV,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    exact evalExp_cmpE_iff.2 ⟨refNullV, refNullV, evalExp_varE_iff.2 (by simp),
      evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩

/-- `Step_pure/ref.as_non_null-addr` (`4.3:388`). -/
theorem ruleFires_refAsNonNullAddr_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refAsNonNullAddrRule ↔
      ∃ w, v = Execution.stepV [w, refAsNonNullV] [w] := by
  unfold refAsNonNullAddrRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [matchExp_caseNil_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := p) (by simp)] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact ⟨r, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨VarEnv.empty.bindVal "ref" w, VarEnv.empty.bindVal "ref" w,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_sub_iff.2
            ((matchExp_boundVar_iff (w := w) (by simp)).2 ⟨rfl, rfl⟩)⟩⟩⟩,
      premsHold_else_iff.2 rfl⟩

/-- `Step_pure/extern.convert_any-null` (`4.3:414`). -/
theorem ruleFires_externConvertAnyNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v externConvertAnyNullRule ↔
      v = Execution.stepV [refNullV, externConvertAnyV] [refNullV] := by
  unfold externConvertAnyNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [matchExp_caseNil_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 hv₂
    obtain ⟨ws, hws, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain rfl := Validation.evalExps_nil_iff.1 hws
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hv₁
    rfl
  · rintro rfl
    refine ⟨VarEnv.empty.bindVal "ref" refNullV, VarEnv.empty.bindVal "ref" refNullV,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    exact evalExp_cmpE_iff.2 ⟨refNullV, refNullV, evalExp_varE_iff.2 (by simp),
      evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩

/-- `Step_pure/extern.convert_any-addr` (`4.3:418`). -/
theorem ruleFires_externConvertAnyAddr_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v externConvertAnyAddrRule ↔
      ∃ w, v = Execution.stepV [w, externConvertAnyV] [refExternV w] := by
  unfold externConvertAnyAddrRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [matchExp_caseNil_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    rw [matchExp_boundVar_iff (w := p) (by simp)] at hrvv
    obtain ⟨rfl, rfl⟩ := hrvv
    exact ⟨rv, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨VarEnv.empty.bindVal "ref" w, VarEnv.empty.bindVal "ref" w,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_boundVar_iff (w := w) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩,
      premsHold_else_iff.2 rfl⟩

/-- `Step_pure/any.convert_extern-null` (`4.3:422`): no binders, no premises. -/
theorem ruleFires_anyConvertExternNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v anyConvertExternNullRule ↔
      v = Execution.stepV [refNullV, anyConvertExternV] [refNullV] := by
  unfold anyConvertExternNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_caseNil_iff] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rw [matchExp_caseNil_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    rfl
  · rintro rfl
    exact ⟨VarEnv.empty, VarEnv.empty,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- `Step_pure/any.convert_extern-addr` (`4.3:426`). -/
theorem ruleFires_anyConvertExternAddr_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v anyConvertExternAddrRule ↔
      ∃ w, v = Execution.stepV [refExternV w, anyConvertExternV] [w] := by
  unfold anyConvertExternAddrRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
    rw [matchExp_freshVar_iff (by simp)] at hpv
    subst hpv
    rw [matchExp_caseNil_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := pv) (by simp)] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact ⟨r, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨VarEnv.empty.bindVal "ref" w, VarEnv.empty.bindVal "ref" w,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩,
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_sub_iff.2
            ((matchExp_boundVar_iff (w := w) (by simp)).2 ⟨rfl, rfl⟩)⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- An `else` followed by an `if` is just the `if`. -/
theorem premsHold_elseIf_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} :
    PremsHold env ρ [.elsePr, .ifPr e] ρ' ↔ ρ' = ρ ∧ EvalExp env ρ e (.bool true) := by
  rw [Validation.premsHold_cons_iff]
  constructor
  · rintro ⟨σ, hp, hrest⟩
    obtain ⟨n, hn⟩ := hp
    have hσ : σ = ρ := by
      cases n with
      | zero => simp [premHolds] at hn
      | succ n => simp only [premHolds, Except.ok.injEq] at hn; exact hn.symm
    subst hσ
    obtain ⟨κ, hpr, htail⟩ := Validation.premsHold_cons_iff.1 hrest
    obtain rfl := Validation.premsHold_nil_iff.1 htail
    obtain ⟨rfl, hev⟩ := Validation.premHolds_if_iff.1 hpr
    exact ⟨rfl, hev⟩
  · rintro ⟨rfl, hev⟩
    exact ⟨ρ', ⟨1, by simp [premHolds]⟩,
      Validation.premsHold_cons_iff.2 ⟨ρ', Validation.premHolds_if_iff.2 ⟨rfl, hev⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩

/-- `Step_pure/i31.get-null` (`4.3:400`): `I31.GET` on a null reference traps. -/
theorem ruleFires_i31GetNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v i31GetNullRule ↔
      ∃ sx, v = Execution.stepV [refNullV, .case "I31.GET" sx] [Execution.trapV] := by
  unfold i31GetNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_caseNil_iff] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨sv, rfl, hsv⟩ := Validation.matchExp_case_iff.1 h2
    rw [matchExp_freshVar_iff (by simp)] at hsv
    subst hsv
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact ⟨sv, rfl⟩
  · rintro ⟨sx, rfl⟩
    exact ⟨VarEnv.empty.bindVal "sx" sx, VarEnv.empty.bindVal "sx" sx,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- The left-hand side `ref_1 ref_2 REF.EQ` is shared by the three `ref.eq`
rules; this is its matching, once. -/
theorem matchExp_refEqLhs_iff {env : Env} {ρ' : VarEnv} {vs : List Value} :
    MatchExps env VarEnv.empty
      [.subE (.varE "ref_1") (.varT "ref" []) (.varT "instr" []),
       .subE (.varE "ref_2") (.varT "ref" []) (.varT "instr" []),
       .caseE "REF.EQ" (.tupE [])] vs ρ' ↔
      ∃ r₁ r₂, vs = [r₁, r₂, refEqV] ∧
        ρ' = (VarEnv.empty.bindVal "ref_1" r₁).bindVal "ref_2" r₂ := by
  constructor
  · rintro h
    obtain ⟨p, q, r, τ, υ, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 h
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h2
    subst h2
    rw [matchExp_caseNil_iff] at h3
    obtain ⟨rfl, rfl⟩ := h3
    exact ⟨p, q, rfl, rfl⟩
  · rintro ⟨r₁, r₂, rfl, rfl⟩
    exact matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
      Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
      Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
      matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩

/-- The right-hand side `(CONST I32 %(k))`, once. -/
theorem matchExp_constI32_iff {env : Env} {ρ ρ' : VarEnv} {k : Nat} {v : Value} :
    MatchExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
        .caseE "%" (.tupE [.numE (.natN k)])])) v ρ' ↔
      v = Execution.constV Execution.i32V (Execution.pctV k) ∧ ρ' = ρ := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨tv, cv, υ, rfl, htv, hcv⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    obtain ⟨cvv, rfl, hcvv⟩ := Validation.matchExp_case_iff.1 hcv
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcvv
    obtain ⟨nv, rfl, hnv⟩ := matchExps_one_iff.1 hcvs
    rw [matchExp_numE_iff] at hnv
    obtain ⟨rfl, rfl⟩ := hnv
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl, ?_⟩⟩
    refine matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩, ?_⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl, ?_⟩⟩
    exact matchExps_one_iff.2 ⟨_, rfl, matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩

/-- `Step_pure/ref.eq-true` (`4.3:392`): two equal references compare equal.
The `else` is vacuous, so the condition really is just `ref_1 = ref_2`. -/
theorem ruleFires_refEqTrue_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refEqTrueRule ↔
      ∃ w, v = Execution.stepV [w, w, refEqV]
        [Execution.constV Execution.i32V (Execution.pctV 1)] := by
  unfold refEqTrueRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨r₁, r₂, rfl, rfl⟩ := matchExp_refEqLhs_iff.1 has
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_constI32_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨-, hev⟩ := premsHold_elseIf_iff.1 hp
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁ hv₂
    simp at hv₁ hv₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hv₁
    subst hv₂
    exact ⟨_, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨(VarEnv.empty.bindVal "ref_1" w).bindVal "ref_2" w,
      (VarEnv.empty.bindVal "ref_1" w).bindVal "ref_2" w,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExp_refEqLhs_iff.2 ⟨w, w, rfl, rfl⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_constI32_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    exact premsHold_elseIf_iff.2 ⟨rfl,
      evalExp_cmpE_iff.2 ⟨w, w, evalExp_varE_iff.2 (by simp), evalExp_varE_iff.2 (by simp),
        ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩

/-- `Step_pure/ref.eq-false` (`4.3:396`): with only an `else`, this fires on
*every* pair of references — including two equal ones, and including two null
ones.  All three `ref.eq` rules overlap. -/
theorem ruleFires_refEqFalse_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refEqFalseRule ↔
      ∃ r₁ r₂, v = Execution.stepV [r₁, r₂, refEqV]
        [Execution.constV Execution.i32V (Execution.pctV 0)] := by
  unfold refEqFalseRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨r₁, r₂, rfl, rfl⟩ := matchExp_refEqLhs_iff.1 has
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_constI32_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact ⟨r₁, r₂, rfl⟩
  · rintro ⟨r₁, r₂, rfl⟩
    exact ⟨(VarEnv.empty.bindVal "ref_1" r₁).bindVal "ref_2" r₂,
      (VarEnv.empty.bindVal "ref_1" r₁).bindVal "ref_2" r₂,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExp_refEqLhs_iff.2 ⟨r₁, r₂, rfl, rfl⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_constI32_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      premsHold_else_iff.2 rfl⟩

/-! ## Two rules the pinned script cannot fire

`ref.i31` and `i31.get-num` put a *call* in the conclusion:
`(REF.I31_NUM $wrap__(32, 31, i))` and `(CONST I32 $extend__(31, 32, sx, i))`.
`matchExp` has no syntactic case for a `CallE`, so it falls through to
`matchDefault`, which **evaluates** the pattern and compares
(`Sem/Eval.lean:1238-1242`).  Both `$wrap__` and `$extend__` are
`hint(builtin)` with no clause (`Equiv/Numerics.lean`'s
`not_callDef_wrap_wasm30`), so at the pinned script the conclusion has no
value and the rule can fire at nothing.

That is stated here as the reason those two are **not** characterised below,
not as a theorem: it needs an inversion principle for `matchExp` at a `CallE`
pattern, which does not exist yet and which `cases`-on-fuel does not give
directly.  See "What is not reached".  The analogous *premise*-side result is
proved — `Equiv/ExecBuiltins.lean`'s `not_ruleFires_binopAnd_pinned`. -/

/-- `andOp` short-circuits only to `false`, so it never short-circuits a
conjunction to `true`.  This is what makes `ref.eq-null`'s premise force
*both* comparisons to be evaluated. -/
theorem boolShort_andOp_ne_true {u : Value} : boolShort .andOp u ≠ some (.bool true) := by
  unfold boolShort
  split <;> simp_all

/-- `Step_pure/ref.eq-null` (`4.3:388`): two null references compare equal. -/
theorem ruleFires_refEqNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refEqNullRule ↔
      v = Execution.stepV [refNullV, refNullV, refEqV]
        [Execution.constV Execution.i32V (Execution.pctV 1)] := by
  unfold refEqNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨r₁, r₂, rfl, rfl⟩ := matchExp_refEqLhs_iff.1 has
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_constI32_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨u₁, hu₁, hrest'⟩ := evalExp_binE_iff.1 hev
    obtain ⟨w₁, w₂, hw₁, hw₂, hc₁⟩ := evalExp_cmpE_iff.1 hu₁
    rw [evalExp_varE_iff] at hw₁
    simp at hw₁
    obtain ⟨z, hz, rfl⟩ := evalExp_caseE_iff.1 hw₂
    obtain ⟨zs, hzs, rfl⟩ := evalExp_tupE_iff.1 hz
    obtain rfl := Validation.evalExps_nil_iff.1 hzs
    rcases hrest' with hshort | ⟨-, u₂, hu₂, hbin⟩
    · exact absurd hshort boolShort_andOp_ne_true
    · obtain ⟨y₁, y₂, hy₁, hy₂, hc₂⟩ := evalExp_cmpE_iff.1 hu₂
      rw [evalExp_varE_iff] at hy₁
      simp at hy₁
      obtain ⟨z', hz', rfl⟩ := evalExp_caseE_iff.1 hy₂
      obtain ⟨zs', hzs', rfl⟩ := evalExp_tupE_iff.1 hz'
      obtain rfl := Validation.evalExps_nil_iff.1 hzs'
      simp only [cmpValues, Except.ok.injEq] at hc₁ hc₂
      subst hc₁; subst hc₂
      simp only [binValues, boolBin, Res.ofOption, Option.map_some, Except.ok.injEq,
        Value.bool.injEq, Bool.and_eq_true, beq_iff_eq] at hbin
      obtain ⟨rfl, rfl⟩ := hbin
      subst hw₁; subst hy₁
      rfl
  · rintro rfl
    refine ⟨(VarEnv.empty.bindVal "ref_1" refNullV).bindVal "ref_2" refNullV,
      (VarEnv.empty.bindVal "ref_1" refNullV).bindVal "ref_2" refNullV,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExp_refEqLhs_iff.2 ⟨refNullV, refNullV, rfl, rfl⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_constI32_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_binE_iff.2 ⟨.bool true, ?_, Or.inr ⟨rfl, .bool true, ?_, rfl⟩⟩
    · exact evalExp_cmpE_iff.2 ⟨refNullV, refNullV, evalExp_varE_iff.2 (by simp),
        evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩,
          rfl⟩, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    · exact evalExp_cmpE_iff.2 ⟨refNullV, refNullV, evalExp_varE_iff.2 (by simp),
        evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩,
          rfl⟩, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩

/-! ## The two indirect-call rules

`call_indirect` and `return_call_indirect` (rules 19 and 20) are pure
rewritings — one instruction to three — with no premise and no store.  They
sit here rather than in a file of their own because they need exactly the
machinery above. -/

/-- The shared right-hand side of both: `(TABLE.GET x) (REF.CAST (REF NULL? yy)) …`,
matched in a scope that already binds `x` and `yy` — which the left-hand side
has just done. -/
theorem matchExp_indirectRhs_iff {env : Env} {ρ ρ' : VarEnv} {last : MixopS}
    {xv yv : Value} {vs : List Value}
    (hx : ρ.findVal? "x" = some xv) (hy : ρ.findVal? "yy" = some yv) :
    MatchExps env ρ
      [.caseE "TABLE.GET" (.varE "x"),
       .caseE "REF.CAST" (.caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))),
         .subE (.varE "yy") (.varT "typeuse" []) (.varT "heaptype" [])])),
       .caseE last (.varE "yy")] vs ρ' ↔
      ρ' = ρ ∧
        vs = [.case "TABLE.GET" xv,
              .case "REF.CAST" (.case "REF" (.tuple [.opt (some (Execution.caseNilV "NULL")),
                yv])),
              .case last yv] := by
  constructor
  · rintro h
    obtain ⟨a, b, c, τ, υ, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 h
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 h1
    rw [matchExp_boundVar_iff hx] at hav
    obtain ⟨rfl, rfl⟩ := hav
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨bv', rfl, hbv'⟩ := Validation.matchExp_case_iff.1 hbv
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv'
    obtain ⟨o, t, κ, rfl, ho, ht⟩ := matchExps_two_iff.1 hbvs
    rw [Validation.matchExp_optSome_iff] at ho
    obtain ⟨ov, rfl, hov⟩ := ho
    rw [matchExp_caseNil_iff] at hov
    obtain ⟨rfl, rfl⟩ := hov
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hy] at ht
    obtain ⟨rfl, rfl⟩ := ht
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 h3
    rw [matchExp_boundVar_iff hy] at hcv
    obtain ⟨rfl, rfl⟩ := hcv
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_optSome_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩,
              Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩)⟩⟩⟩⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩⟩⟩

/-- `(REF.CAST (REF NULL? yy))`, the cast both rules insert. -/
def refCastNullV (yv : Value) : Value :=
  .case "REF.CAST" (.case "REF" (.tuple [.opt (some (Execution.caseNilV "NULL")), yv]))

/-- `Step_pure/call_indirect` (`4.3:160`): the elaborated form of the
instruction, as three. -/
theorem ruleFires_callIndirect_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v callIndirectRule ↔
      ∃ x yy, v = Execution.stepV [.case "CALL_INDIRECT" (.tuple [x, yy])]
        [.case "TABLE.GET" x, refCastNullV yy, .case "CALL_REF" yy] := by
  unfold callIndirectRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, rfl, hp⟩ := matchExps_one_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨xv, yv, τ, rfl, hx, hy⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hy
    subst hy
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨-, rfl⟩ := (matchExp_indirectRhs_iff (xv := xv) (yv := yv)
      (by simp) (by simp)).1 hbs
    exact ⟨xv, yv, rfl⟩
  · rintro ⟨x, yy, rfl⟩
    exact ⟨(VarEnv.empty.bindVal "x" x).bindVal "yy" yy,
      (VarEnv.empty.bindVal "x" x).bindVal "yy" yy,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        (matchExp_indirectRhs_iff (xv := x) (yv := yy) (by simp) (by simp)).2
          ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- `Step_pure/return_call_indirect` (`4.3:166`): the same, with
`RETURN_CALL_REF`. -/
theorem ruleFires_returnCallIndirect_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v returnCallIndirectRule ↔
      ∃ x yy, v = Execution.stepV [.case "RETURN_CALL_INDIRECT" (.tuple [x, yy])]
        [.case "TABLE.GET" x, refCastNullV yy, .case "RETURN_CALL_REF" yy] := by
  unfold returnCallIndirectRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, rfl, hp⟩ := matchExps_one_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨xv, yv, τ, rfl, hx, hy⟩ := matchExps_two_iff.1 hpvs
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hy
    subst hy
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨-, rfl⟩ := (matchExp_indirectRhs_iff (xv := xv) (yv := yv)
      (by simp) (by simp)).1 hbs
    exact ⟨xv, yv, rfl⟩
  · rintro ⟨x, yy, rfl⟩
    exact ⟨(VarEnv.empty.bindVal "x" x).bindVal "yy" yy,
      (VarEnv.empty.bindVal "x" x).bindVal "yy" yy,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        (matchExp_indirectRhs_iff (xv := x) (yv := yy) (by simp) (by simp)).2
          ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

end Silmaril.SpecTec.Equiv.ExecRef
