module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Validation
public import Silmaril.Wasm.Execution.Core.Step
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# SpecTec's reduction relation against Silmaril's Wasm execution

Phase 4, the execution area.  `Silmaril/SpecTec/Sem/Eval.lean` gives every
`RelD` of the internal language a denotation — `derives`, the step-indexed
least fixpoint of its rules — and `Silmaril/Wasm/Execution/Core/Step.lean` is
Silmaril's hand-written transcription of §4.3 of the WebAssembly 3.0
specification.  This file relates the two.

Every citation `4.3:n` is line `n` of
`specification/wasm-3.0/4.3-execution.instructions.spectec` at the pin
`608711107b7f1edb13efd57b7d79b49477462d36`, and likewise `4.0:n`, `1.1:n`
and `1.3:n` for `4.0-execution.configurations.spectec`,
`1.1-syntax.values.spectec` and `1.3-syntax.instructions.spectec`.

## Which relation

`4.3:5-8` declares four:

| SpecTec | shape | note |
| --- | --- | --- |
| `Step` | `config ~> config` | the whole machine |
| `Step_pure` | `instr* ~> instr*` | no store, no frame |
| `Step_read` | `config ~> instr*` | reads the state, writes nothing |
| `Steps` | `config ~>* config` | the reflexive-transitive closure |

`Step/pure` (`4.3:13-15`) and `Step/read` (`4.3:17-19`) lift the second and
third into the first.  This file is about **`Step_pure`**, the 79-rule
relation that needs neither store nor frame, because its value bridge is a
bridge for `instr` alone and not for `store`, `moduleinst` and `frame`.
`Step_pure` is definition 637 (counting from zero) of the 976 in
`specs/spectec/wasm-3.0.ast`; it has **no parameters**, so
`Equiv/Validation.lean`'s `ruleFires_nil_iff` applies to every one of its
rules unchanged.

## What is proved

**Provenance.**  `HasStepRules` lists twenty-three of `Step_pure`'s rules
with their index in the pinned stream, transcribed verbatim;
`hasStepRules_wasm30` discharges it by `rfl` against
`Silmaril.SpecTec.Specs.wasm30`.  As in `Equiv/Validation.lean`, the
provenance is by index (`HasRuleAt`) rather than by spelling out the whole
`RelD`, whose 79 rules render to 46 000 characters of Lean.

**Machinery that belongs upstream.**  `Equiv/Validation.lean` built the
inversion principles for `derives`, for `matchExp`'s non-iterating forms and
for premises, and recorded that the iteration machinery was missing.  Every
structural rule of `Step_pure` iterates, so this file adds it:

* `MatchRounds`, `MatchIterList`, with `matchRounds_single_iff`,
  `matchIterList_single_iff`;
* `BindsVar`, `bindsVar_varE`, `bindsVar_subE`, `bindsVar_subVar` — the
  "body of the iteration is the domain variable" shape every reduction rule
  uses;
* `matchExp_iterE_list_iff`, `matchExp_iterE_listN_iff`,
  `matchExp_iterE_opt_iff` — `e*`, `e^n` and `e?` over one domain, exactly;
* `NoPatLen`, `MatchFails`, `SplitFails`, `matchExp_catE_ofLeft`,
  `matchExp_catE_ofRight`, `matchExp_catE_ofSplit` — what a concatenation
  pattern needs, when it needs something it cannot have, and how the search
  for a split is placed at the first one that matches;
* `matchExps_one_iff` … `matchExps_four_iff`, `matchExp_caseNil_iff`,
  `matchExp_listNil_iff`, `matchExp_concl_iff`, `matchExp_freshVar_iff`,
  `matchExp_boundVar_iff`, `findVal?_bindVal_lit`;
* `evalExp_imm_iff`, `premsHold_immNe_iff`, `premsHold_immEq_iff` — the
  `c!%.0 =/= 0` and `c!%.0 = 0` side conditions.

**Sixteen rules, characterised exactly, in both directions.**  Each
`ruleFires_*_iff` says precisely which values of `Step_pure`'s type the rule
derives — the `→` direction is an inversion, the `←` direction a
construction, and neither is weakened.

| rule | theorem | derives exactly |
| --- | --- | --- |
| `unreachable` (`4.3:52`) | `ruleFires_unreachable_iff` | `([UNREACHABLE], [TRAP])` |
| `nop` (`4.3:55`) | `ruleFires_nop_iff` | `([NOP], [])` |
| `drop` (`4.3:58`) | `ruleFires_drop_iff` | `([w, DROP], [])`, any `w` |
| `select-true` (`4.3:62`) | `ruleFires_selectTrue_iff` | see below |
| `select-false` (`4.3:66`) | `ruleFires_selectFalse_iff` | see below |
| `if-true` (`4.3:85`) | `ruleFires_ifTrue_iff` | `bt`, both bodies free |
| `if-false` (`4.3:89`) | `ruleFires_ifFalse_iff` | likewise |
| `label-vals` (`4.3:94`) | `ruleFires_labelVals_iff` | `([LABEL_ n {cs} ws], ws)` |
| `br_if-true` (`4.3:113`) | `ruleFires_brIfTrue_iff` | `c!%.0 =/= 0` |
| `br_if-false` (`4.3:117`) | `ruleFires_brIfFalse_iff` | `c!%.0 = 0` |
| `frame-vals` (`4.3:227`) | `ruleFires_frameVals_iff` | arity *is* forced |
| `handler-vals` (`4.3:294`) | `ruleFires_handlerVals_iff` | arity is not |
| `trap-label` (`4.3:304`) | `ruleFires_trapLabel_iff` | `([LABEL_ n {cs} TRAP], [TRAP])` |
| `trap-handler` (`4.3:307`) | `ruleFires_trapHandler_iff` | likewise |
| `trap-frame` (`4.3:310`) | `ruleFires_trapFrame_iff` | likewise |
| `local.tee` (`4.3:323`) | `ruleFires_localTee_iff` | `([w, LOCAL.TEE x], [w, w, LOCAL.SET x])` |

`matchExp_selectAnnot_iff` is the companion result for `SELECT (t*)?`: the
annotation must be an option of a list, and nothing more is checked.

**Seven structural rules, fired by the `CatE` search.**  Every `br` out of a
label or a handler, every `return`, and trap propagation concatenate two `*`
iterations over domains the pattern is itself about to bind, so neither
operand of the concatenation has a `patLen` and the split has to be
*searched* for.  `Sem/Eval.lean`'s `matchExp` does search — it tries the
`n + 1` splits in increasing order and takes the first that matches — and
`ruleFires_brLabelZero`, `ruleFires_brLabelSucc`, `ruleFires_brHandler`,
`ruleFires_returnFrame`, `ruleFires_returnLabel`, `ruleFires_returnHandler`
and `ruleFires_trapInstrs` say that each of the seven rules then fires, with
the expected scope.  `matchExp_catE_ofSplit` is the construction behind them,
`matchExp_shapeA`/`B`/`C` the three concatenation shapes the rules use.

These seven are **constructions, not characterisations**: each hypothesises
that no value in front of the marker is itself a `BR`, a `RETURN` or a
`TRAP`, which is what makes the first split the intended one, and none of
them has a converse.  See "the `CatE` search" below.

**The bridge.**  `adminV?`/`adminsV?` encode Silmaril's `Admin` into the
value domain, partially: every reference value, the integer and vector
constants, and `nop`, `unreachable`, `drop`, unannotated `select`, `br`,
`br_if`, `local.set`, `local.tee` and `trap`.  `StepImage is js v` says `v`
is the SpecTec image of the Silmaril step `is ~> js`.  Then

* `ruleFires_nop_iff_image` and `ruleFires_unreachable_iff_image` —
  `Step_pure/nop` and `Step_pure/unreachable` **are** `ParametricStep.nop`
  and `ParametricStep.unreachable`, in both directions and with nothing
  left over;
* `derives_nop`, `derives_unreachable`, `derives_drop`, `derives_localTee`,
  `derives_brIfTrue`, `derives_brIfFalse`, `derives_selectTrue`,
  `derives_selectFalse` — every image of the corresponding Silmaril step is
  a `Step_pure` derivation;
* `Silmaril.Wasm.SpecTec.Thms` checks eight of `instrV?`'s ten clauses against
  `Equiv/BinaryInstr.lean`'s total `instrV` with `instrV?_agrees_binaryInstr`;
* `derives_trapLabel`, `derives_trapHandler`, `derives_trapFrame`,
  `derives_labelVals`, `derives_handlerVals`, `derives_frameVals`,
  `derives_ifTrue`, `derives_ifFalse` — the same for the administrative and
  block rules, stated for an **arbitrary** value in each position the rule
  does not inspect (a label's continuation, a frame, a handler's catch
  clauses, a block type, a branch body).  That is strictly stronger than any
  particular encoding of those components, and it is why no bridge for
  `blocktype`, `moduleinst` or `catch` is needed here.

## The two findings

They are findings about `Sem/Eval.lean`'s denotation, not about the
specification; each is proved, with a witness.

1. **The dropped quantifiers reach the reduction relation.**
   `Equiv/Validation.lean` records that `anyRule` ignores a `RuleD`'s
   `quant list` (`spectec/src/il/ast.ml:146,129,124`).  In the typing group
   that made the well-formedness judgments trivial; here it is worse,
   because the quantifier `val* : val*` is the only thing that says a label
   body consists of *values*.  `ruleFires_labelVals_nonvalue` derives
   `(LABEL_ true {} (NOP)) ~> (NOP)` — a label whose arity is the boolean
   `true` and whose body is a `NOP` — and `not_adminsV?_vals_nop` proves
   `[NOP]` is not the encoding of any `vals vs`, so no `Step.labelVals` has
   that pair as its image.  `ruleFires_drop_nonvalue` and `drop_not_image`
   are the same for `DROP`, and there the mismatch *is* a `StepImage`
   statement.
2. **`c =/= 0` does not say `c` is a numeral.**  `cmpValues` settles `=/=`
   by structural inequality of values (`eval.ml:260-263`), so
   `ruleFires_brIfTrue_nonNumeral` fires `br_if-true` on an `I32` immediate
   that is the boolean `true`, and `ruleFires_brIfTrue_textLabel` fires it
   on a label index that is a `text`.

Consequently every theorem here that goes from `derives` to Silmaril is
restricted to the shapes the bridge covers, and every theorem that goes the
other way is unconditional — the same asymmetry `Equiv/Validation.lean`
reports.

## What is not reached

See the final section of this file.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.Execution

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)

/-! ## The rules of `Step_pure`, as the pinned stream records them

`Step_pure` (`4.3:6`) is `(rel "Step_pure" "%~>%" (tup (bind "_" (iter (var
"instr") list)) (bind "_" (iter (var "instr") list))) …)` in
`specs/spectec/wasm-3.0.ast`: definition 637 of 976, counting from zero,
with **no parameters** and 79 rules.  Each rule below is that stream's `k`-th rule, transcribed
verbatim; `hasStepRules_wasm30` checks all twenty-three by `rfl`. -/

/-- `Step_pure/unreachable` (rule 0 of the relation). -/
def unreachableRule : Rule :=
  (.ruleD "unreachable" [] "%~>%" (.tupE [(.listE [(.caseE "UNREACHABLE" (.tupE []))]), (.listE
   [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_pure/nop` (rule 1 of the relation). -/
def nopRule : Rule :=
  (.ruleD "nop" [] "%~>%" (.tupE [(.listE [(.caseE "NOP" (.tupE []))]), (.listE [])]) [])

/-- `Step_pure/drop` (rule 2 of the relation). -/
def dropRule : Rule :=
  (.ruleD "drop" [(.expP "val" (.varT "val" []))] "%~>%" (.tupE [(.listE [(.subE (.varE "val")
   (.varT "val" []) (.varT "instr" [])), (.caseE "DROP" (.tupE []))]), (.listE [])]) [])

/-- `Step_pure/select-true` (rule 3 of the relation). -/
def selectTrueRule : Rule :=
  (.ruleD "select-true" [(.expP "val_1" (.varT "val" [])), (.expP "val_2" (.varT "val" [])),
   (.expP "c" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "t*?" (.iterT (.iterT
   (.varT "valtype" []) .list) .opt))] "%~>%" (.tupE [(.listE [(.subE (.varE "val_1") (.varT
   "val" []) (.varT "instr" [])), (.subE (.varE "val_2") (.varT "val" []) (.varT "instr" [])),
   (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "c")])), (.caseE "SELECT" (.iterE
   (.iterE (.varE "t") (.mk .list [(.mk "t" (.varE "t*"))])) (.mk .opt [(.mk "t*" (.varE
   "t*?"))])))]), (.listE [(.subE (.varE "val_1") (.varT "val" []) (.varT "instr" []))])])
   [(.ifPr (.cmpE .neOp .boolT (.projE (.uncaseE (.varE "c") "%") (0)) (.numE (.natN 0))))])

/-- `Step_pure/select-false` (rule 4 of the relation). -/
def selectFalseRule : Rule :=
  (.ruleD "select-false" [(.expP "val_1" (.varT "val" [])), (.expP "val_2" (.varT "val" [])),
   (.expP "c" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "t*?" (.iterT (.iterT
   (.varT "valtype" []) .list) .opt))] "%~>%" (.tupE [(.listE [(.subE (.varE "val_1") (.varT
   "val" []) (.varT "instr" [])), (.subE (.varE "val_2") (.varT "val" []) (.varT "instr" [])),
   (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "c")])), (.caseE "SELECT" (.iterE
   (.iterE (.varE "t") (.mk .list [(.mk "t" (.varE "t*"))])) (.mk .opt [(.mk "t*" (.varE
   "t*?"))])))]), (.listE [(.subE (.varE "val_2") (.varT "val" []) (.varT "instr" []))])])
   [(.ifPr (.cmpE .eqOp .boolT (.projE (.uncaseE (.varE "c") "%") (0)) (.numE (.natN 0))))])

/-- `Step_pure/if-true` (rule 5 of the relation). -/
def ifTrueRule : Rule :=
  (.ruleD "if-true" [(.expP "c" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "bt"
   (.varT "blocktype" [])), (.expP "instr_1*" (.iterT (.varT "instr" []) .list)), (.expP
   "instr_2*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "c")])), (.caseE "IF%%ELSE%" (.tupE [(.varE "bt"), (.iterE
   (.varE "instr_1") (.mk .list [(.mk "instr_1" (.varE "instr_1*"))])), (.iterE (.varE
   "instr_2") (.mk .list [(.mk "instr_2" (.varE "instr_2*"))]))]))]), (.listE [(.caseE "BLOCK"
   (.tupE [(.varE "bt"), (.iterE (.varE "instr_1") (.mk .list [(.mk "instr_1" (.varE
   "instr_1*"))]))]))])]) [(.ifPr (.cmpE .neOp .boolT (.projE (.uncaseE (.varE "c") "%") (0))
   (.numE (.natN 0))))])

/-- `Step_pure/if-false` (rule 6 of the relation). -/
def ifFalseRule : Rule :=
  (.ruleD "if-false" [(.expP "c" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP
   "bt" (.varT "blocktype" [])), (.expP "instr_1*" (.iterT (.varT "instr" []) .list)), (.expP
   "instr_2*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "c")])), (.caseE "IF%%ELSE%" (.tupE [(.varE "bt"), (.iterE
   (.varE "instr_1") (.mk .list [(.mk "instr_1" (.varE "instr_1*"))])), (.iterE (.varE
   "instr_2") (.mk .list [(.mk "instr_2" (.varE "instr_2*"))]))]))]), (.listE [(.caseE "BLOCK"
   (.tupE [(.varE "bt"), (.iterE (.varE "instr_2") (.mk .list [(.mk "instr_2" (.varE
   "instr_2*"))]))]))])]) [(.ifPr (.cmpE .eqOp .boolT (.projE (.uncaseE (.varE "c") "%") (0))
   (.numE (.natN 0))))])

/-- `Step_pure/label-vals` (rule 7 of the relation). -/
def labelValsRule : Rule :=
  (.ruleD "label-vals" [(.expP "n" (.varT "n" [])), (.expP "instr*" (.iterT (.varT "instr" [])
   .list)), (.expP "val*" (.iterT (.varT "val" []) .list))] "%~>%" (.tupE [(.listE [(.caseE
   "LABEL_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE
   "instr*"))])), (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list
   [(.mk "val" (.varE "val*"))]))]))]), (.iterE (.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))]))]) [])

/-- `Step_pure/br-label-zero` (rule 8 of the relation). -/
def brLabelZeroRule : Rule :=
  (.ruleD "br-label-zero" [(.expP "n" (.varT "n" [])), (.expP "instr'*" (.iterT (.varT "instr"
   []) .list)), (.expP "val'*" (.iterT (.varT "val" []) .list)), (.expP "val*" (.iterT (.varT
   "val" []) .list)), (.expP "l" (.varT "labelidx" [])), (.expP "instr*" (.iterT (.varT "instr"
   []) .list))] "%~>%" (.tupE [(.listE [(.caseE "LABEL_%{%}%" (.tupE [(.varE "n"), (.iterE
   (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))])), (.catE (.catE (.catE
   (.iterE (.subE (.varE "val'") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val'"
   (.varE "val'*"))])) (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk
   (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))]))) (.listE [(.caseE "BR" (.varE
   "l"))])) (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])))]))]), (.catE
   (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n")
   none) [(.mk "val" (.varE "val*"))])) (.iterE (.varE "instr'") (.mk .list [(.mk "instr'"
   (.varE "instr'*"))])))]) [(.ifPr (.cmpE .eqOp .boolT (.projE (.uncaseE (.varE "l") "%") (0))
   (.numE (.natN 0))))])

/-- `Step_pure/br-label-succ` (rule 9 of the relation). -/
def brLabelSuccRule : Rule :=
  (.ruleD "br-label-succ" [(.expP "n" (.varT "n" [])), (.expP "instr'*" (.iterT (.varT "instr"
   []) .list)), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "l" (.varT "labelidx"
   [])), (.expP "instr*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.listE [(.caseE
   "LABEL_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE
   "instr'*"))])), (.catE (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr"
   [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "BR" (.varE "l"))])) (.iterE
   (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])))]))]), (.catE (.iterE (.subE
   (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))]))
   (.listE [(.caseE "BR" (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.projE
   (.uncaseE (.varE "l") "%") (0)) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT
   .natT)])))]))]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.projE (.uncaseE (.varE "l") "%") (0))
   (.numE (.natN 0))))])

/-- `Step_pure/br-handler` (rule 10 of the relation). -/
def brHandlerRule : Rule :=
  (.ruleD "br-handler" [(.expP "n" (.varT "n" [])), (.expP "catch*" (.iterT (.varT "catch" [])
   .list)), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "l" (.varT "labelidx" [])),
   (.expP "instr*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.listE [(.caseE
   "HANDLER_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "catch") (.mk .list [(.mk "catch" (.varE
   "catch*"))])), (.catE (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr"
   [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "BR" (.varE "l"))])) (.iterE
   (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])))]))]), (.catE (.iterE (.subE
   (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))]))
   (.listE [(.caseE "BR" (.varE "l"))]))]) [])

/-- `Step_pure/br_if-true` (rule 11 of the relation). -/
def brIfTrueRule : Rule :=
  (.ruleD "br_if-true" [(.expP "c" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP
   "l" (.varT "labelidx" []))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.varE "c")])), (.caseE "BR_IF" (.varE "l"))]), (.listE [(.caseE "BR" (.varE
   "l"))])]) [(.ifPr (.cmpE .neOp .boolT (.projE (.uncaseE (.varE "c") "%") (0)) (.numE (.natN
   0))))])

/-- `Step_pure/br_if-false` (rule 12 of the relation). -/
def brIfFalseRule : Rule :=
  (.ruleD "br_if-false" [(.expP "c" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP
   "l" (.varT "labelidx" []))] "%~>%" (.tupE [(.listE [(.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.varE "c")])), (.caseE "BR_IF" (.varE "l"))]), (.listE [])]) [(.ifPr (.cmpE
   .eqOp .boolT (.projE (.uncaseE (.varE "c") "%") (0)) (.numE (.natN 0))))])

/-- `Step_pure/frame-vals` (rule 21 of the relation). -/
def frameValsRule : Rule :=
  (.ruleD "frame-vals" [(.expP "n" (.varT "n" [])), (.expP "f" (.varT "frame" [])), (.expP
   "val*" (.iterT (.varT "val" []) .list))] "%~>%" (.tupE [(.listE [(.caseE "FRAME_%{%}%" (.tupE
   [(.varE "n"), (.varE "f"), (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
   (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))]))]))]), (.iterE (.subE (.varE
   "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE
   "val*"))]))]) [])

/-- `Step_pure/return-frame` (rule 22 of the relation). -/
def returnFrameRule : Rule :=
  (.ruleD "return-frame" [(.expP "n" (.varT "n" [])), (.expP "f" (.varT "frame" [])), (.expP
   "val'*" (.iterT (.varT "val" []) .list)), (.expP "val*" (.iterT (.varT "val" []) .list)),
   (.expP "instr*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.listE [(.caseE
   "FRAME_%{%}%" (.tupE [(.varE "n"), (.varE "f"), (.catE (.catE (.catE (.iterE (.subE (.varE
   "val'") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val'" (.varE "val'*"))]))
   (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n")
   none) [(.mk "val" (.varE "val*"))]))) (.listE [(.caseE "RETURN" (.tupE []))])) (.iterE (.varE
   "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])))]))]), (.iterE (.subE (.varE "val")
   (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE
   "val*"))]))]) [])

/-- `Step_pure/return-label` (rule 23 of the relation). -/
def returnLabelRule : Rule :=
  (.ruleD "return-label" [(.expP "n" (.varT "n" [])), (.expP "instr'*" (.iterT (.varT "instr"
   []) .list)), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "instr*" (.iterT (.varT
   "instr" []) .list))] "%~>%" (.tupE [(.listE [(.caseE "LABEL_%{%}%" (.tupE [(.varE "n"),
   (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))])), (.catE (.catE
   (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val"
   (.varE "val*"))])) (.listE [(.caseE "RETURN" (.tupE []))])) (.iterE (.varE "instr") (.mk
   .list [(.mk "instr" (.varE "instr*"))])))]))]), (.catE (.iterE (.subE (.varE "val") (.varT
   "val" []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE
   "RETURN" (.tupE []))]))]) [])

/-- `Step_pure/return-handler` (rule 24 of the relation). -/
def returnHandlerRule : Rule :=
  (.ruleD "return-handler" [(.expP "n" (.varT "n" [])), (.expP "catch*" (.iterT (.varT "catch"
   []) .list)), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "instr*" (.iterT (.varT
   "instr" []) .list))] "%~>%" (.tupE [(.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"),
   (.iterE (.varE "catch") (.mk .list [(.mk "catch" (.varE "catch*"))])), (.catE (.catE (.iterE
   (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE
   "val*"))])) (.listE [(.caseE "RETURN" (.tupE []))])) (.iterE (.varE "instr") (.mk .list [(.mk
   "instr" (.varE "instr*"))])))]))]), (.catE (.iterE (.subE (.varE "val") (.varT "val" [])
   (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "RETURN"
   (.tupE []))]))]) [])

/-- `Step_pure/handler-vals` (rule 25 of the relation). -/
def handlerValsRule : Rule :=
  (.ruleD "handler-vals" [(.expP "n" (.varT "n" [])), (.expP "catch*" (.iterT (.varT "catch" [])
   .list)), (.expP "val*" (.iterT (.varT "val" []) .list))] "%~>%" (.tupE [(.listE [(.caseE
   "HANDLER_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "catch") (.mk .list [(.mk "catch" (.varE
   "catch*"))])), (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list
   [(.mk "val" (.varE "val*"))]))]))]), (.iterE (.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))]))]) [])

/-- `Step_pure/trap-instrs` (rule 26 of the relation). -/
def trapInstrsRule : Rule :=
  (.ruleD "trap-instrs" [(.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "instr*" (.iterT
   (.varT "instr" []) .list))] "%~>%" (.tupE [(.catE (.iterE (.subE (.varE "val") (.varT "val"
   []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.catE (.listE [(.caseE
   "TRAP" (.tupE []))]) (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])))),
   (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.binE .orOp .boolT (.cmpE .neOp .boolT
   (.iterE (.varE "val") (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [])) (.cmpE .neOp
   .boolT (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])) (.listE []))))])

/-- `Step_pure/trap-label` (rule 27 of the relation). -/
def trapLabelRule : Rule :=
  (.ruleD "trap-label" [(.expP "n" (.varT "n" [])), (.expP "instr'*" (.iterT (.varT "instr" [])
   .list))] "%~>%" (.tupE [(.listE [(.caseE "LABEL_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE
   "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))])), (.listE [(.caseE "TRAP" (.tupE
   []))])]))]), (.listE [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_pure/trap-handler` (rule 28 of the relation). -/
def trapHandlerRule : Rule :=
  (.ruleD "trap-handler" [(.expP "n" (.varT "n" [])), (.expP "catch*" (.iterT (.varT "catch" [])
   .list))] "%~>%" (.tupE [(.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE
   "catch") (.mk .list [(.mk "catch" (.varE "catch*"))])), (.listE [(.caseE "TRAP" (.tupE
   []))])]))]), (.listE [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_pure/trap-frame` (rule 29 of the relation). -/
def trapFrameRule : Rule :=
  (.ruleD "trap-frame" [(.expP "n" (.varT "n" [])), (.expP "f" (.varT "frame" []))] "%~>%"
   (.tupE [(.listE [(.caseE "FRAME_%{%}%" (.tupE [(.varE "n"), (.varE "f"), (.listE [(.caseE
   "TRAP" (.tupE []))])]))]), (.listE [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_pure/local.tee` (rule 30 of the relation). -/
def localTeeRule : Rule :=
  (.ruleD "local.tee" [(.expP "val" (.varT "val" [])), (.expP "x" (.varT "idx" []))] "%~>%"
   (.tupE [(.listE [(.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE
   "LOCAL.TEE" (.varE "x"))]), (.listE [(.subE (.varE "val") (.varT "val" []) (.varT "instr"
   [])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "LOCAL.SET" (.varE
   "x"))])]) [])

/-- The twenty-three `Step_pure` rules this file reaches, at their indices in
the pinned stream.  `Step_pure` has 79 rules, which render to 46 000
characters of Lean, so — exactly as `Equiv/Validation.lean` does for
`Instr_ok` — the provenance is recorded one rule at a time, by index. -/
structure HasStepRules (env : Env) : Prop where
  /-- `Step_pure/unreachable`, rule 0. -/
  unreachable : HasRuleAt env "Step_pure" "%~>%" 0 unreachableRule
  /-- `Step_pure/nop`, rule 1. -/
  nop : HasRuleAt env "Step_pure" "%~>%" 1 nopRule
  /-- `Step_pure/drop`, rule 2. -/
  drop : HasRuleAt env "Step_pure" "%~>%" 2 dropRule
  /-- `Step_pure/select-true`, rule 3. -/
  selectTrue : HasRuleAt env "Step_pure" "%~>%" 3 selectTrueRule
  /-- `Step_pure/select-false`, rule 4. -/
  selectFalse : HasRuleAt env "Step_pure" "%~>%" 4 selectFalseRule
  /-- `Step_pure/if-true`, rule 5. -/
  ifTrue : HasRuleAt env "Step_pure" "%~>%" 5 ifTrueRule
  /-- `Step_pure/if-false`, rule 6. -/
  ifFalse : HasRuleAt env "Step_pure" "%~>%" 6 ifFalseRule
  /-- `Step_pure/label-vals`, rule 7. -/
  labelVals : HasRuleAt env "Step_pure" "%~>%" 7 labelValsRule
  /-- `Step_pure/br-label-zero`, rule 8. -/
  brLabelZero : HasRuleAt env "Step_pure" "%~>%" 8 brLabelZeroRule
  /-- `Step_pure/br-label-succ`, rule 9. -/
  brLabelSucc : HasRuleAt env "Step_pure" "%~>%" 9 brLabelSuccRule
  /-- `Step_pure/br-handler`, rule 10. -/
  brHandler : HasRuleAt env "Step_pure" "%~>%" 10 brHandlerRule
  /-- `Step_pure/br_if-true`, rule 11. -/
  brIfTrue : HasRuleAt env "Step_pure" "%~>%" 11 brIfTrueRule
  /-- `Step_pure/br_if-false`, rule 12. -/
  brIfFalse : HasRuleAt env "Step_pure" "%~>%" 12 brIfFalseRule
  /-- `Step_pure/frame-vals`, rule 21. -/
  frameVals : HasRuleAt env "Step_pure" "%~>%" 21 frameValsRule
  /-- `Step_pure/return-frame`, rule 22. -/
  returnFrame : HasRuleAt env "Step_pure" "%~>%" 22 returnFrameRule
  /-- `Step_pure/return-label`, rule 23. -/
  returnLabel : HasRuleAt env "Step_pure" "%~>%" 23 returnLabelRule
  /-- `Step_pure/return-handler`, rule 24. -/
  returnHandler : HasRuleAt env "Step_pure" "%~>%" 24 returnHandlerRule
  /-- `Step_pure/handler-vals`, rule 25. -/
  handlerVals : HasRuleAt env "Step_pure" "%~>%" 25 handlerValsRule
  /-- `Step_pure/trap-instrs`, rule 26. -/
  trapInstrs : HasRuleAt env "Step_pure" "%~>%" 26 trapInstrsRule
  /-- `Step_pure/trap-label`, rule 27. -/
  trapLabel : HasRuleAt env "Step_pure" "%~>%" 27 trapLabelRule
  /-- `Step_pure/trap-handler`, rule 28. -/
  trapHandler : HasRuleAt env "Step_pure" "%~>%" 28 trapHandlerRule
  /-- `Step_pure/trap-frame`, rule 29. -/
  trapFrame : HasRuleAt env "Step_pure" "%~>%" 29 trapFrameRule
  /-- `Step_pure/local.tee`, rule 30. -/
  localTee : HasRuleAt env "Step_pure" "%~>%" 30 localTeeRule

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- The pinned wasm-3.0 specification has those twenty-three rules at those
indices. -/
theorem hasStepRules_wasm30 : HasStepRules (envOfScript Specs.wasm30) :=
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
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩,
   ⟨_, _, _, rfl, rfl, rfl⟩⟩

/-! ## Matching an iteration, and the lengths a concatenation needs

`Equiv/Validation.lean` built inversion principles for `derives`, for
`matchExp`'s non-iterating forms and for premises, and recorded that
`matchIterE`/`matchIterList`/`matchRounds` were missing.  Every structural
rule of `Step_pure` iterates, so this section supplies them — in the one
shape the reduction rules use, a single domain whose variable *is* the
body — together with what `patLen` says about a concatenation.
-/

/-- `matchRounds` as a relation (`Sem/Eval.lean`). -/
def MatchRounds (env : Env) (ρ : VarEnv) (e : Exp) (xs : List IL.Id)
    (ido : Option IL.Id) (i : Nat) (vs : List Value) (rows : List (List Value)) : Prop :=
  ∃ n, matchRounds n env ρ e xs ido i vs = .ok rows

/-- `matchIterList` as a relation (`Sem/Eval.lean`). -/
def MatchIterList (env : Env) (ρ : VarEnv) (e : Exp) (ds : List Dom)
    (ido : Option IL.Id) (vs : List Value) (ρ' : VarEnv) : Prop :=
  ∃ n, matchIterList n env ρ e ds ido vs = .ok ρ'

/-- More fuel preserves the rows `matchRounds` has committed to. -/
theorem matchRounds_ok_of_le {m n : Nat} {env ρ e xs ido i vs rows} (h : m ≤ n)
    (hv : matchRounds m env ρ e xs ido i vs = .ok rows) :
    matchRounds n env ρ e xs ido i vs = .ok rows :=
  ((monoAt_of_le h).matchRounds env ρ e xs ido i vs).ok hv

/-- More fuel preserves a scope `matchIterList` has committed to. -/
theorem matchIterList_ok_of_le {m n : Nat} {env ρ e ds ido vs ρ'} (h : m ≤ n)
    (hv : matchIterList m env ρ e ds ido vs = .ok ρ') :
    matchIterList n env ρ e ds ido vs = .ok ρ' :=
  ((monoAt_of_le h).matchIterList env ρ e ds ido vs).ok hv

/-- A pattern that binds exactly the variable `x`, whatever it is matched
against, and commits to no other binding.  The body of every iteration in
`Step_pure`'s structural rules is of this form: either `x` itself or `x`
under a subsort coercion. -/
def BindsVar (env : Env) (e : Exp) (x : IL.Id) : Prop :=
  ∀ (ρ ρ' : VarEnv) (v : Value), ρ.findVal? x = none →
    (MatchExp env ρ e v ρ' ↔ ρ' = ρ.bindVal x v)

/-- A bare variable binds itself. -/
theorem bindsVar_varE {env : Env} (x : IL.Id) : BindsVar env (.varE x) x := by
  intro ρ ρ' v hx
  rw [Validation.matchExp_var_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · rw [hx] at h; exact absurd h (by simp)
  · rintro rfl; exact Or.inl ⟨hx, rfl⟩

/-- A subsort coercion is transparent, so it preserves `BindsVar`. -/
theorem bindsVar_subE {env : Env} {e : Exp} {x : IL.Id} {t₁ t₂ : Typ}
    (h : BindsVar env e x) : BindsVar env (.subE e t₁ t₂) x := by
  intro ρ ρ' v hx
  rw [Validation.matchExp_sub_iff]
  exact h ρ ρ' v hx

/-- The subsorted variable `val : val <: instr`, the body of every value
iteration in `Step_pure`. -/
theorem bindsVar_subVar {env : Env} (x : IL.Id) (t₁ t₂ : Typ) :
    BindsVar env (.subE (.varE x) t₁ t₂) x :=
  bindsVar_subE (bindsVar_varE x)

/-- Reading one just-bound variable back out of a round's scope. -/
theorem findVals?_bindVal_single {ρ : VarEnv} {x : IL.Id} (hx : x ≠ "_") (v : Value) :
    (ρ.bindVal x v).findVals? [x] = some [v] := by
  have : (ρ.bindVal x v).findVal? x = some v := by
    simp only [VarEnv.findVal?, VarEnv.bindVal, Map.bind, hx, reduceIte, Map.find?]
  simp [VarEnv.findVals?, this]

/-- **Rounds, exactly.**  A one-domain iteration whose body binds that
domain's variable collects every element of the matched list into its own
singleton row, and nothing else is possible. -/
theorem matchRounds_single_iff {env : Env} {ρ : VarEnv} {e : Exp} {x : IL.Id}
    {i : Nat} {vs : List Value} {rows : List (List Value)} (hb : BindsVar env e x)
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") :
    MatchRounds env ρ e [x] none i vs rows ↔ rows = vs.map (fun v => [v]) := by
  induction vs generalizing i rows with
  | nil =>
      constructor
      · rintro ⟨n, hn⟩
        cases n with
        | zero => simp [matchRounds] at hn
        | succ n =>
            exact (Validation.okInj (by simpa only [matchRounds, List.map_nil] using hn)).symm
      · rintro rfl; exact ⟨1, by simp only [matchRounds, List.map_nil]⟩
  | cons v vs ih =>
      constructor
      · rintro ⟨n, hn⟩
        cases n with
        | zero => simp [matchRounds] at hn
        | succ n =>
            simp only [matchRounds, Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
            obtain ⟨σ, hσ, row, hrow, rest, hrest, heq⟩ := hn
            have : σ = ρ.bindVal x v := (hb ρ σ v hx).1 ⟨n, hσ⟩
            subst this
            rw [findVals?_bindVal_single hx'] at hrow
            injection hrow with hrow
            subst hrow
            have := (ih (i := i + 1) (rows := rest)).1 ⟨n, hrest⟩
            subst this
            simp only [← Validation.okInj heq, List.map_cons]
      · rintro rfl
        obtain ⟨n₁, h₁⟩ := (hb ρ (ρ.bindVal x v) v hx).2 rfl
        obtain ⟨n₂, h₂⟩ := (ih (i := i + 1) (rows := vs.map (fun v => [v]))).2 rfl
        refine ⟨max n₁ n₂ + 1, ?_⟩
        have e1 := Validation.matchExp_ok_mono (m := n₁) (n := max n₁ n₂) (by omega) h₁
        have e2 := matchRounds_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) h₂
        simp only [matchRounds, e1, Bind.bind, Except.bind, findVals?_bindVal_single hx',
          Res.ofOption, e2, List.map_cons]

/-- The only column of the rows a single-domain iteration collects. -/
theorem iterCol_single (vs : List Value) : iterCol (vs.map (fun v => [v])) 0 = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons, iterCol, List.filterMap_cons] at *; simp [ih]

/-- `iterCols` of those rows is the matched list itself, as one value. -/
theorem iterCols_single (vs : List Value) :
    iterCols (vs.map (fun v => [v])) 1 = [Value.list vs] := by
  simp [iterCols, iterCol_single]

/-- **A one-domain list iteration, exactly.**  It matches a list by binding
the domain *expression* to that list. -/
theorem matchIterList_single_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {x y : IL.Id}
    {vs : List Value} (hb : BindsVar env e x) (hx : ρ.findVal? x = none) (hx' : x ≠ "_") :
    MatchIterList env ρ e [.mk x (.varE y)] none vs ρ' ↔
      MatchExp env ρ (.varE y) (.list vs) ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchIterList] at hn
    | succ n =>
        simp only [matchIterList, Res.bind_eq_ok, List.map_cons, List.map_nil, domVar,
          domSrc, List.length_cons, List.length_nil, Nat.zero_add] at hn
        obtain ⟨rows, hrows, hm⟩ := hn
        have hr := (matchRounds_single_iff hb hx hx').1 ⟨n, hrows⟩
        subst hr
        rw [iterCols_single] at hm
        obtain ⟨w, ws, σ, heq, h₁, h₂⟩ := Validation.matchExps_cons_iff.1 ⟨n, hm⟩
        injection heq with hw hws
        subst hw; subst hws
        rw [(Validation.matchExps_nil_iff.1 h₂).2]
        exact h₁
  · intro h
    obtain ⟨n₁, h₁⟩ := (matchRounds_single_iff (i := 0) (rows := vs.map (fun v => [v]))
      hb hx hx').2 rfl
    obtain ⟨n₂, h₂⟩ := Validation.matchExps_cons_iff.2
      ⟨Value.list vs, [], ρ', rfl, h, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    have e1 := matchRounds_ok_of_le (m := n₁) (n := max n₁ n₂) (by omega) h₁
    have e2 := Validation.matchExps_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) h₂
    simp only [matchIterList, List.map_cons, List.map_nil, domVar, domSrc,
      List.length_cons, List.length_nil, Nat.zero_add, e1, Bind.bind, Except.bind,
      iterCols_single, e2]

/-- **`e*` over one unbound domain, exactly.** -/
theorem matchExp_iterE_list_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {x y : IL.Id}
    {v : Value} (hb : BindsVar env e x) (hx : ρ.findVal? x = none) (hx' : x ≠ "_") :
    MatchExp env ρ (.iterE e (.mk .list [.mk x (.varE y)])) v ρ' ↔
      ∃ vs, v = .list vs ∧ MatchExp env ρ (.varE y) (.list vs) ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp] at hn
        cases n with
        | zero => simp [matchIterE] at hn
        | succ n =>
            simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok,
              Value.asList?_eq_some] at hn
            obtain ⟨vs, hv, hm⟩ := hn
            exact ⟨vs, hv, (matchIterList_single_iff hb hx hx').1 ⟨n, hm⟩⟩
  · rintro ⟨vs, rfl, h⟩
    obtain ⟨n, hn⟩ := (matchIterList_single_iff hb hx hx').2 h
    exact ⟨n + 2, by
      simp only [matchExp, matchIterE, Value.asList?_list, Res.ofOption, Bind.bind,
        Except.bind, hn]⟩

/-- **`e^n` over one unbound domain, exactly.**  The counter expression is a
pattern too, and it is matched against the *length* of the list before the
rounds are run. -/
theorem matchExp_iterE_listN_iff {env : Env} {ρ ρ' : VarEnv} {e eₙ : Exp} {x y : IL.Id}
    {v : Value} :
    MatchExp env ρ (.iterE e (.mk (.listN eₙ none) [.mk x (.varE y)])) v ρ' ↔
      ∃ vs σ, v = .list vs ∧ MatchExp env ρ eₙ (.num (.natN vs.length)) σ ∧
        MatchIterList env σ e [.mk x (.varE y)] none vs ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp] at hn
        cases n with
        | zero => simp [matchIterE] at hn
        | succ n =>
            simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok,
              Value.asList?_eq_some] at hn
            obtain ⟨vs, hv, σ, hσ, hm⟩ := hn
            exact ⟨vs, σ, hv, ⟨n, hσ⟩, ⟨n, hm⟩⟩
  · rintro ⟨vs, σ, rfl, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨max n₁ n₂ + 2, ?_⟩
    have e1 := Validation.matchExp_ok_mono (m := n₁) (n := max n₁ n₂) (by omega) h₁
    have e2 := matchIterList_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) h₂
    simp only [matchExp, matchIterE, Value.asList?_list, Res.ofOption, Bind.bind,
      Except.bind, e1, e2]

/-- Reading the single binding an iteration's body leaves. -/
theorem findVals?_single_eq (ρ : VarEnv) (x : IL.Id) :
    ρ.findVals? [x] = (ρ.findVal? x).map (fun u => [u]) := by
  cases h : ρ.findVal? x <;> simp [VarEnv.findVals?, h]

/-- The same, at a known binding. -/
theorem findVals?_single {ρ : VarEnv} {x : IL.Id} {u : Value} (h : ρ.findVal? x = some u) :
    ρ.findVals? [x] = some [u] := by
  simp [findVals?_single_eq, h]

/-- **`e?` over one domain, exactly.**  This is the shape `SELECT (t*)?` has
(`1.3:223`, `(iter (iter (var "valtype") list) opt)` in the pinned
stream). -/
theorem matchExp_iterE_opt_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {x y : IL.Id}
    {v : Value} :
    MatchExp env ρ (.iterE e (.mk .opt [.mk x (.varE y)])) v ρ' ↔
      (v = .opt none ∧ MatchExp env ρ (.varE y) (.opt none) ρ') ∨
      (∃ w σ u, v = .opt (some w) ∧ MatchExp env ρ e w σ ∧ σ.findVal? x = some u ∧
        MatchExp env ρ (.varE y) (.opt (some u)) ρ') := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ n =>
        simp only [matchExp] at hn
        cases n with
        | zero => simp [matchIterE] at hn
        | succ n =>
            simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok,
              Value.asOpt?_eq_some] at hn
            obtain ⟨o, hv, hm⟩ := hn
            cases o with
            | none =>
                refine Or.inl ⟨hv, ?_⟩
                simp only [List.map_cons, List.map_nil, domSrc] at hm
                obtain ⟨w, ws, σ, heq, h₁, h₂⟩ := Validation.matchExps_cons_iff.1 ⟨n, hm⟩
                injection heq with hw hws
                subst hw; subst hws
                rw [(Validation.matchExps_nil_iff.1 h₂).2]
                exact h₁
            | some w =>
                simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, List.map_cons,
                  List.map_nil, domVar, domSrc, findVals?_single_eq] at hm
                obtain ⟨σ, hσ, us, hus, hm⟩ := hm
                cases hu : σ.findVal? x with
                | none => rw [hu] at hus; simp at hus
                | some u =>
                    rw [hu, Option.map_some] at hus
                    injection hus with hus
                    subst hus
                    refine Or.inr ⟨w, σ, u, hv, ⟨n, hσ⟩, hu, ?_⟩
                    simp only [List.map_cons, List.map_nil] at hm
                    obtain ⟨a, tl, τ, heq, h₁, h₂⟩ := Validation.matchExps_cons_iff.1 ⟨n, hm⟩
                    injection heq with ha has
                    subst ha; subst has
                    rw [(Validation.matchExps_nil_iff.1 h₂).2]
                    exact h₁
  · rintro (⟨rfl, h⟩ | ⟨w, σ, u, rfl, ⟨n₁, h₁⟩, hu, h⟩)
    · obtain ⟨n, hn⟩ := Validation.matchExps_cons_iff.2
        ⟨Value.opt none, [], ρ', rfl, h, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩
      exact ⟨n + 2, by
        simp only [matchExp, matchIterE, Value.asOpt?_opt, Res.ofOption, Bind.bind,
          Except.bind, List.map_cons, List.map_nil, domSrc, hn]⟩
    · obtain ⟨n₂, h₂⟩ := Validation.matchExps_cons_iff.2
        ⟨Value.opt (some u), [], ρ', rfl, h, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩
      refine ⟨max n₁ n₂ + 2, ?_⟩
      have e1 := Validation.matchExp_ok_mono (m := n₁) (n := max n₁ n₂) (by omega) h₁
      have e2 := Validation.matchExps_ok_of_le (m := n₂) (n := max n₁ n₂) (by omega) h₂
      simp only [matchExp, matchIterE, Value.asOpt?_opt, Res.ofOption, Bind.bind,
        Except.bind, List.map_cons, List.map_nil, domVar, domSrc, e1,
        findVals?_single hu, e2]

/-! ### `patLen`, definite failure, and the search for a split

`matchExp`'s `CatE` clause (`Sem/Eval.lean`, `eval.ml:923-932`) splits the
matched list at a length it computes with `patLen`: the *left* operand's
length if that is defined, otherwise the *right* operand's.  `patLen` knows
the length of a `ListE`, the sum for a `CatE` and the counter of a `^n`
iteration, and otherwise *evaluates* the pattern — and a `*` iteration over a
domain the pattern is about to bind evaluates to nothing.  Every
concatenation in the reduction rules has an operand of that kind, so the
clause falls through to its third branch: it tries the `vs.length + 1` splits
in increasing order and takes the **first** that matches.

Taking the first match is what the predicates below are for.  To place a
match at a chosen split one must know that every earlier split *definitely*
fails — not merely that it fails to succeed, because a split that only ran
out of fuel stops the search rather than being skipped.  `NoPatLen`,
`MatchFails` and `SplitFails` are those definite-failure statements, and
`matchExp_catE_ofSplit` is the construction they feed. -/

/-- `patLen` *definitely* has no length for `e`: at some fuel the answer is
`undef`, which no larger fuel can change (`monoAt_of_le`). -/
def NoPatLen (env : Env) (ρ : VarEnv) (e : Exp) : Prop :=
  ∃ n, patLen n env ρ e = .error .undef

/-- Matching `e` against `v` *definitely* fails, as opposed to merely not
succeeding: at some fuel the answer is `undef`. -/
def MatchFails (env : Env) (ρ : VarEnv) (e : Exp) (v : Value) : Prop :=
  ∃ n, matchExp n env ρ e v = .error .undef

/-- A definite `patLen` failure stays one when the fuel grows. -/
theorem patLen_undef_of_le {m n : Nat} {env : Env} {ρ : VarEnv} {e : Exp} (h : m ≤ n)
    (hv : patLen m env ρ e = .error .undef) : patLen n env ρ e = .error .undef :=
  (((monoAt_of_le h).patLen env ρ e).eq_of_ne_oof (by rw [hv]; simp)).trans hv

/-- A definite match failure stays one when the fuel grows. -/
theorem matchExp_undef_of_le {m n : Nat} {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : m ≤ n) (hv : matchExp m env ρ e v = .error .undef) :
    matchExp n env ρ e v = .error .undef :=
  (((monoAt_of_le h).matchExp env ρ e v).eq_of_ne_oof (by rw [hv]; simp)).trans hv

/-- A pattern `patLen` definitely cannot measure never gets measured. -/
theorem patLen_ne_ok_of_noPatLen {env : Env} {ρ : VarEnv} {e : Exp}
    (h : NoPatLen env ρ e) (m j : Nat) : patLen m env ρ e ≠ .ok j := by
  obtain ⟨n, hn⟩ := h
  intro hm
  have h₁ : patLen (max n m) env ρ e = .error .undef := patLen_undef_of_le (by omega) hn
  have h₂ : patLen (max n m) env ρ e = .ok j :=
    ((monoAt_of_le (show m ≤ max n m by omega)).patLen env ρ e).ok hm
  rw [h₁] at h₂
  exact absurd h₂ (by simp)

/-- An unbound variable has no value, at any fuel. -/
theorem evalExp_varE_ne_ok {env : Env} {ρ : VarEnv} {y : IL.Id} {n : Nat} {v : Value}
    (hy : ρ.findVal? y = none) : evalExp n env ρ (.varE y) ≠ .ok v := by
  cases n <;> simp [evalExp, hy, Res.ofOption]

/-- **A `*` iteration over an unbound domain has no `patLen`.**  `patLen`
falls back on evaluating the pattern, and the evaluation needs the domain. -/
theorem noPatLen_iterE_list {env : Env} {ρ : VarEnv} {e : Exp} {x y : IL.Id}
    (hy : ρ.findVal? y = none) :
    NoPatLen env ρ (.iterE e (.mk .list [.mk x (.varE y)])) :=
  ⟨5, by simp [patLen, evalExp, evalIterE, evalDoms, domSrc, hy, Res.ofOption,
    Bind.bind, Except.bind]⟩

/-- A concatenation whose left operand has no length has none. -/
theorem noPatLen_catE_left {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp}
    (h : NoPatLen env ρ e₁) : NoPatLen env ρ (.catE e₁ e₂) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by simp [patLen, hn, Bind.bind, Except.bind]⟩

/-- A concatenation whose left operand *has* a length and whose right has
none has none either. -/
theorem noPatLen_catE_right {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {m j : Nat}
    (h₁ : patLen m env ρ e₁ = .ok j) (h₂ : NoPatLen env ρ e₂) :
    NoPatLen env ρ (.catE e₁ e₂) := by
  obtain ⟨n, hn⟩ := h₂
  obtain ⟨N, hm, hn'⟩ : ∃ N, m ≤ N ∧ n ≤ N := ⟨max m n, by omega, by omega⟩
  refine ⟨N + 1, ?_⟩
  have e1 : patLen N env ρ e₁ = .ok j := ((monoAt_of_le hm).patLen env ρ e₁).ok h₁
  have e2 : patLen N env ρ e₂ = .error .undef := patLen_undef_of_le hn' hn
  simp [patLen, e1, e2, Bind.bind, Except.bind]

/-- A literal list states its own length (`eval.ml:923-932`'s only source). -/
theorem patLen_listE {env : Env} {ρ : VarEnv} {es : List Exp} :
    patLen 1 env ρ (.listE es) = .ok es.length := by
  simp [patLen]

/-- A `^n` iteration whose counter is an already-bound variable states its
length. -/
theorem patLen_iterE_listN_var {env : Env} {ρ : VarEnv} {e : Exp} {x y z : IL.Id}
    {j : Nat} (hz : ρ.findVal? z = some (.num (.natN j))) :
    patLen 2 env ρ (.iterE e (.mk (.listN (.varE z) none) [.mk x (.varE y)])) = .ok j := by
  simp [patLen, evalExp, hz, Res.ofOption, Bind.bind, Except.bind]

/-! #### Definite failure, compositionally -/

/-- An injection pattern fails definitely on a value that is not an injection
by that mixop. -/
theorem matchFails_caseE {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {w : Value}
    (h : ∀ u, w ≠ .case op u) : MatchFails env ρ (.caseE op e) w := by
  refine ⟨1, ?_⟩
  cases hw : w.asCase? with
  | none => simp [matchExp, hw, Res.ofOption, Bind.bind, Except.bind]
  | some p =>
      obtain ⟨op', u⟩ := p
      have hwe : w = .case op' u := Value.asCase?_eq_some.1 hw
      have hne : ¬ (op' = op) := fun hh => h u (by rw [← hh, hwe])
      simp [matchExp, hw, Res.ofOption, Bind.bind, Except.bind, Res.assert, hne]

/-- A one-element list pattern fails definitely when its element does. -/
theorem matchFails_listE_one {env : Env} {ρ : VarEnv} {e : Exp} {w : Value}
    (h : MatchFails env ρ e w) : MatchFails env ρ (.listE [e]) (.list [w]) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 2, by simp [matchExp, matchExps, Res.ofOption, hn, Bind.bind, Except.bind]⟩

/-- A concatenation whose **left** operand has a length `j`: it fails
definitely when the list is shorter than `j`, and when the split at `j`
fails. -/
theorem matchFails_catE_ofLeft {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {us : List Value}
    {j m : Nat} (hj : patLen m env ρ e₁ = .ok j)
    (h : us.length < j ∨ MatchFails env ρ e₁ (.list (us.take j)) ∨
          ∃ σ, MatchExp env ρ e₁ (.list (us.take j)) σ ∧
            MatchFails env σ e₂ (.list (us.drop j))) :
    MatchFails env ρ (.catE e₁ e₂) (.list us) := by
  rcases h with hshort | ⟨n₁, h₁⟩ | ⟨σ, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
  · refine ⟨m + 1, ?_⟩
    have hns : ¬ (j ≤ us.length) := by omega
    simp [matchExp, hj, Res.ofOption, Bind.bind, Except.bind, Res.assert, hns]
  · obtain ⟨N, hm, hb₁⟩ : ∃ N, m ≤ N ∧ n₁ ≤ N := ⟨max m n₁, by omega, by omega⟩
    refine ⟨N + 1, ?_⟩
    have e0 : patLen N env ρ e₁ = .ok j := ((monoAt_of_le hm).patLen env ρ e₁).ok hj
    have e1 : matchExp N env ρ e₁ (.list (us.take j)) = .error .undef :=
      matchExp_undef_of_le hb₁ h₁
    by_cases hle : j ≤ us.length
    · simp [matchExp, e0, e1, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]
    · simp [matchExp, e0, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]
  · obtain ⟨N, hm, hb₁, hb₂⟩ : ∃ N, m ≤ N ∧ n₁ ≤ N ∧ n₂ ≤ N :=
      ⟨max m (max n₁ n₂), by omega, by omega, by omega⟩
    refine ⟨N + 1, ?_⟩
    have e0 : patLen N env ρ e₁ = .ok j := ((monoAt_of_le hm).patLen env ρ e₁).ok hj
    have e1 : matchExp N env ρ e₁ (.list (us.take j)) = .ok σ :=
      Validation.matchExp_ok_mono hb₁ h₁
    have e2 : matchExp N env σ e₂ (.list (us.drop j)) = .error .undef :=
      matchExp_undef_of_le hb₂ h₂
    by_cases hle : j ≤ us.length
    · simp [matchExp, e0, e1, e2, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]
    · simp [matchExp, e0, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]

/-- A concatenation whose **right** operand has a length `j`, the left
having none: the same two ways to fail. -/
theorem matchFails_catE_ofRight {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {us : List Value}
    {j m : Nat} (h₀ : NoPatLen env ρ e₁) (hj : patLen m env ρ e₂ = .ok j)
    (h : us.length < j ∨ MatchFails env ρ e₁ (.list (us.take (us.length - j))) ∨
          ∃ σ, MatchExp env ρ e₁ (.list (us.take (us.length - j))) σ ∧
            MatchFails env σ e₂ (.list (us.drop (us.length - j)))) :
    MatchFails env ρ (.catE e₁ e₂) (.list us) := by
  obtain ⟨n₀, hn₀⟩ := h₀
  rcases h with hshort | ⟨n₁, h₁⟩ | ⟨σ, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
  · obtain ⟨N, hb₀, hm⟩ : ∃ N, n₀ ≤ N ∧ m ≤ N := ⟨max n₀ m, by omega, by omega⟩
    refine ⟨N + 1, ?_⟩
    have e0 : patLen N env ρ e₁ = .error .undef := patLen_undef_of_le hb₀ hn₀
    have e1 : patLen N env ρ e₂ = .ok j := ((monoAt_of_le hm).patLen env ρ e₂).ok hj
    have hns : ¬ (j ≤ us.length) := by omega
    simp [matchExp, e0, e1, Res.ofOption, Bind.bind, Except.bind, Res.assert, hns]
  · obtain ⟨N, hb₀, hm, hb₁⟩ : ∃ N, n₀ ≤ N ∧ m ≤ N ∧ n₁ ≤ N :=
      ⟨max (max n₀ m) n₁, by omega, by omega, by omega⟩
    refine ⟨N + 1, ?_⟩
    have e0 : patLen N env ρ e₁ = .error .undef := patLen_undef_of_le hb₀ hn₀
    have e1 : patLen N env ρ e₂ = .ok j := ((monoAt_of_le hm).patLen env ρ e₂).ok hj
    have e2 : matchExp N env ρ e₁ (.list (us.take (us.length - j))) = .error .undef :=
      matchExp_undef_of_le hb₁ h₁
    by_cases hle : j ≤ us.length
    · simp [matchExp, e0, e1, e2, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]
    · simp [matchExp, e0, e1, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]
  · obtain ⟨N, hb₀, hm, hb₁, hb₂⟩ : ∃ N, n₀ ≤ N ∧ m ≤ N ∧ n₁ ≤ N ∧ n₂ ≤ N :=
      ⟨max (max n₀ m) (max n₁ n₂), by omega, by omega, by omega, by omega⟩
    refine ⟨N + 1, ?_⟩
    have e0 : patLen N env ρ e₁ = .error .undef := patLen_undef_of_le hb₀ hn₀
    have e1 : patLen N env ρ e₂ = .ok j := ((monoAt_of_le hm).patLen env ρ e₂).ok hj
    have e2 : matchExp N env ρ e₁ (.list (us.take (us.length - j))) = .ok σ :=
      Validation.matchExp_ok_mono hb₁ h₁
    have e3 : matchExp N env σ e₂ (.list (us.drop (us.length - j))) = .error .undef :=
      matchExp_undef_of_le hb₂ h₂
    by_cases hle : j ≤ us.length
    · simp [matchExp, e0, e1, e2, e3, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]
    · simp [matchExp, e0, e1, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]

/-! #### Matching a concatenation -/

/-- A concatenation whose **left** operand has a length `j`, matched at that
split: `matchExp`'s first branch. -/
theorem matchExp_catE_ofLeft {env : Env} {ρ σ ρ' : VarEnv} {e₁ e₂ : Exp} {us : List Value}
    {j m : Nat} (hj : patLen m env ρ e₁ = .ok j) (hle : j ≤ us.length)
    (h₁ : MatchExp env ρ e₁ (.list (us.take j)) σ)
    (h₂ : MatchExp env σ e₂ (.list (us.drop j)) ρ') :
    MatchExp env ρ (.catE e₁ e₂) (.list us) ρ' := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  obtain ⟨N, hm, hb₁, hb₂⟩ : ∃ N, m ≤ N ∧ n₁ ≤ N ∧ n₂ ≤ N :=
    ⟨max m (max n₁ n₂), by omega, by omega, by omega⟩
  refine ⟨N + 1, ?_⟩
  have e0 : patLen N env ρ e₁ = .ok j := ((monoAt_of_le hm).patLen env ρ e₁).ok hj
  have e1 : matchExp N env ρ e₁ (.list (us.take j)) = .ok σ :=
    Validation.matchExp_ok_mono hb₁ h₁
  have e2 : matchExp N env σ e₂ (.list (us.drop j)) = .ok ρ' :=
    Validation.matchExp_ok_mono hb₂ h₂
  simp [matchExp, e0, e1, e2, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]

/-- A concatenation whose **right** operand has a length `j`, the left having
none: `matchExp`'s second branch. -/
theorem matchExp_catE_ofRight {env : Env} {ρ σ ρ' : VarEnv} {e₁ e₂ : Exp} {us : List Value}
    {j m : Nat} (h₀ : NoPatLen env ρ e₁) (hj : patLen m env ρ e₂ = .ok j)
    (hle : j ≤ us.length)
    (h₁ : MatchExp env ρ e₁ (.list (us.take (us.length - j))) σ)
    (h₂ : MatchExp env σ e₂ (.list (us.drop (us.length - j))) ρ') :
    MatchExp env ρ (.catE e₁ e₂) (.list us) ρ' := by
  obtain ⟨n₀, hn₀⟩ := h₀
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  obtain ⟨N, hb₀, hm, hb₁, hb₂⟩ : ∃ N, n₀ ≤ N ∧ m ≤ N ∧ n₁ ≤ N ∧ n₂ ≤ N :=
    ⟨max (max n₀ m) (max n₁ n₂), by omega, by omega, by omega, by omega⟩
  refine ⟨N + 1, ?_⟩
  have e0 : patLen N env ρ e₁ = .error .undef := patLen_undef_of_le hb₀ hn₀
  have e1 : patLen N env ρ e₂ = .ok j := ((monoAt_of_le hm).patLen env ρ e₂).ok hj
  have e2 : matchExp N env ρ e₁ (.list (us.take (us.length - j))) = .ok σ :=
    Validation.matchExp_ok_mono hb₁ h₁
  have e3 : matchExp N env σ e₂ (.list (us.drop (us.length - j))) = .ok ρ' :=
    Validation.matchExp_ok_mono hb₂ h₂
  simp [matchExp, e0, e1, e2, e3, Res.ofOption, Bind.bind, Except.bind, Res.assert, hle]

/-! #### The search

When neither operand has a length `matchExp` searches.  `SplitFails` is one
alternative of that search failing definitely, `splitFails_uniform` collects
finitely many such failures at a single fuel, and `matchExp_catE_ofSplit`
places the match at the first split that works. -/

/-- One alternative of the `CatE` search, at fuel `n`: match the left operand
against the first `i` elements and the right against the rest. -/
def splitAttempt (n : Nat) (env : Env) (ρ : VarEnv) (e₁ e₂ : Exp) (vs : List Value)
    (i : Nat) : Res VarEnv :=
  matchExp n env ρ e₁ (.list (vs.take i)) >>= fun σ => matchExp n env σ e₂ (.list (vs.drop i))

/-- The split at `i` fails definitely, so the search passes over it. -/
def SplitFails (env : Env) (ρ : VarEnv) (e₁ e₂ : Exp) (vs : List Value) (i : Nat) : Prop :=
  ∃ n, splitAttempt n env ρ e₁ e₂ vs i = .error .undef

/-- An alternative is monotone in the fuel, being a `bind` of two matches. -/
theorem splitAttempt_undef_of_le {m n : Nat} {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp}
    {vs : List Value} {i : Nat} (h : m ≤ n)
    (hv : splitAttempt m env ρ e₁ e₂ vs i = .error .undef) :
    splitAttempt n env ρ e₁ e₂ vs i = .error .undef := by
  have hle : Res.Le (splitAttempt m env ρ e₁ e₂ vs i) (splitAttempt n env ρ e₁ e₂ vs i) :=
    Res.bind_le ((monoAt_of_le h).matchExp _ _ _ _)
      fun _ => (monoAt_of_le h).matchExp _ _ _ _
  exact (hle.eq_of_ne_oof (by rw [hv]; simp)).trans hv

/-- The left operand failing definitely makes the split fail. -/
theorem splitFails_left {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {vs : List Value} {i : Nat}
    (h : MatchFails env ρ e₁ (.list (vs.take i))) : SplitFails env ρ e₁ e₂ vs i := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by simp [splitAttempt, hn, Bind.bind, Except.bind]⟩

/-- The right operand failing definitely, after the left succeeded, makes the
split fail. -/
theorem splitFails_right {env : Env} {ρ σ : VarEnv} {e₁ e₂ : Exp} {vs : List Value}
    {i : Nat} (h₁ : MatchExp env ρ e₁ (.list (vs.take i)) σ)
    (h₂ : MatchFails env σ e₂ (.list (vs.drop i))) : SplitFails env ρ e₁ e₂ vs i := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  obtain ⟨N, hb₁, hb₂⟩ : ∃ N, n₁ ≤ N ∧ n₂ ≤ N := ⟨max n₁ n₂, by omega, by omega⟩
  refine ⟨N, ?_⟩
  have e1 : matchExp N env ρ e₁ (.list (vs.take i)) = .ok σ :=
    Validation.matchExp_ok_mono hb₁ h₁
  have e2 : matchExp N env σ e₂ (.list (vs.drop i)) = .error .undef :=
    matchExp_undef_of_le hb₂ h₂
  simp [splitAttempt, e1, e2, Bind.bind, Except.bind]

/-- Finitely many definite failures happen at a single fuel. -/
theorem splitFails_uniform {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {vs : List Value} :
    ∀ (k : Nat), (∀ i, i < k → SplitFails env ρ e₁ e₂ vs i) →
      ∃ n, ∀ i, i < k → splitAttempt n env ρ e₁ e₂ vs i = .error .undef
  | 0, _ => ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | k+1, h => by
      obtain ⟨n, hn⟩ := splitFails_uniform k fun i hi => h i (by omega)
      obtain ⟨m, hm⟩ := h k (Nat.lt_succ_self k)
      refine ⟨max n m, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · exact splitAttempt_undef_of_le (by omega) (hn i hi')
      · exact splitAttempt_undef_of_le (by omega) hm

/-- **The `CatE` search, as a construction.**  When neither operand has a
length, `matchExp` takes the first split that matches, so a split matches
provided every earlier one fails definitely. -/
theorem matchExp_catE_ofSplit {env : Env} {ρ σ ρ' : VarEnv} {e₁ e₂ : Exp}
    {vs : List Value} {k : Nat} (h₁ : NoPatLen env ρ e₁) (h₂ : NoPatLen env ρ e₂)
    (hk : k ≤ vs.length) (hfail : ∀ i, i < k → SplitFails env ρ e₁ e₂ vs i)
    (hσ : MatchExp env ρ e₁ (.list (vs.take k)) σ)
    (hρ' : MatchExp env σ e₂ (.list (vs.drop k)) ρ') :
    MatchExp env ρ (.catE e₁ e₂) (.list vs) ρ' := by
  obtain ⟨n₀, hn₀⟩ := splitFails_uniform k hfail
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  obtain ⟨n₃, hn₃⟩ := hσ
  obtain ⟨n₄, hn₄⟩ := hρ'
  obtain ⟨N, hb₀, hb₁, hb₂, hb₃, hb₄⟩ :
      ∃ N, n₀ ≤ N ∧ n₁ ≤ N ∧ n₂ ≤ N ∧ n₃ ≤ N ∧ n₄ ≤ N :=
    ⟨max (max n₀ n₁) (max n₂ (max n₃ n₄)), by omega, by omega, by omega, by omega, by omega⟩
  refine ⟨N + 1, ?_⟩
  have e1 : patLen N env ρ e₁ = .error .undef := patLen_undef_of_le hb₁ hn₁
  have e2 : patLen N env ρ e₂ = .error .undef := patLen_undef_of_le hb₂ hn₂
  have a1 : matchExp N env ρ e₁ (.list (vs.take k)) = .ok σ :=
    Validation.matchExp_ok_mono hb₃ hn₃
  have a2 : matchExp N env σ e₂ (.list (vs.drop k)) = .ok ρ' :=
    Validation.matchExp_ok_mono hb₄ hn₄
  have e3 : (matchExp N env ρ e₁ (.list (vs.take k)) >>= fun τ =>
      matchExp N env τ e₂ (.list (vs.drop k))) = .ok ρ' := by
    simp [a1, a2, Bind.bind, Except.bind]
  have e4 : ∀ j, j < k → (matchExp N env ρ e₁ (.list (vs.take j)) >>= fun τ =>
      matchExp N env τ e₂ (.list (vs.drop j))) = .error .undef := by
    intro j hj
    have := splitAttempt_undef_of_le hb₀ (hn₀ j hj)
    simpa [splitAttempt] using this
  simp only [matchExp, Res.bind_eq_ok]
  refine ⟨vs, rfl, ?_⟩
  rw [e1, Res.elimUndef_undef, e2, Res.elimUndef_undef]
  exact Res.scan_eq_of_lt vs.length 0 k (Nat.zero_le _) (by omega) e3
    (fun j _ hj => e4 j hj)


/-! ## The SpecTec side of a reduction step

`Step_pure`'s type is `(instr*, instr*)` (`4.3:6`), so a derivation is a pair
of lists of `instr` values.  The abbreviations below name the `instr`
injections the rules this file reaches mention; each mixop is the one
`Silmaril/Wasm/SpecTec/Generated.lean`'s `instructionSchemas` and
`administrativeSchemas` record, which is an independent check on them. -/

/-- A pair of instruction sequences: one element of `Step_pure`'s type. -/
def stepV (is js : List Value) : Value := .tuple [.list is, .list js]

/-- A nullary instruction, `(case "OP" (tup))`. -/
def caseNilV (op : MixopS) : Value := .case op (.tuple [])

/-- `NOP` (`instructionSchemas`, `"NOP", []`). -/
def nopV : Value := caseNilV "NOP"

/-- `UNREACHABLE`. -/
def unreachableV : Value := caseNilV "UNREACHABLE"

/-- `DROP`. -/
def dropV : Value := caseNilV "DROP"

/-- `TRAP` (`administrativeSchemas`, `"TRAP", []`). -/
def trapV : Value := caseNilV "TRAP"

/-- `I32`, the `numtype`. -/
def i32V : Value := caseNilV "I32"

/-- `CONST nt c`. -/
def constV (nt c : Value) : Value := .case "CONST" (.tuple [nt, c])

/-- `BR l`. -/
def brV (l : Value) : Value := .case "BR" l

/-- `BR_IF l`. -/
def brIfV (l : Value) : Value := .case "BR_IF" l

/-- `BLOCK bt instr*`. -/
def blockV (bt : Value) (is : List Value) : Value := .case "BLOCK" (.tuple [bt, .list is])

/-- `IF bt instr* ELSE instr*`. -/
def ifV (bt : Value) (is js : List Value) : Value :=
  .case "IF%%ELSE%" (.tuple [bt, .list is, .list js])

/-- `SELECT (t*)?`; the annotation is a whole `(valtype*)?` value. -/
def selectV (ts : Value) : Value := .case "SELECT" ts

/-- `LOCAL.TEE x`. -/
def localTeeV (x : Value) : Value := .case "LOCAL.TEE" x

/-- `LOCAL.SET x`. -/
def localSetV (x : Value) : Value := .case "LOCAL.SET" x

/-- `LABEL_ n {instr*} instr*`. -/
def labelV (n : Value) (cont body : List Value) : Value :=
  .case "LABEL_%{%}%" (.tuple [n, .list cont, .list body])

/-- `HANDLER_ n {catch*} instr*`. -/
def handlerV (n : Value) (catches body : List Value) : Value :=
  .case "HANDLER_%{%}%" (.tuple [n, .list catches, .list body])

/-- `FRAME_ n {f} instr*`. -/
def frameV (n f : Value) (body : List Value) : Value :=
  .case "FRAME_%{%}%" (.tuple [n, f, .list body])

/-! ### Inverting the fixed-arity patterns the rules use -/

/-- A one-element pattern list. -/
theorem matchExps_one_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {vs : List Value} :
    MatchExps env ρ [e] vs ρ' ↔ ∃ a, vs = [a] ∧ MatchExp env ρ e a ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 h₂
    exact ⟨w, rfl, h₁⟩
  · rintro ⟨a, rfl, h⟩
    exact ⟨a, [], ρ', rfl, h, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩

/-- A two-element pattern list. -/
theorem matchExps_two_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {vs : List Value} :
    MatchExps env ρ [e₁, e₂] vs ρ' ↔
      ∃ a b σ, vs = [a, b] ∧ MatchExp env ρ e₁ a σ ∧ MatchExp env σ e₂ b ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, rfl, hb⟩ := matchExps_one_iff.1 h₂
    exact ⟨w, b, σ, rfl, h₁, hb⟩
  · rintro ⟨a, b, σ, rfl, h₁, h₂⟩
    exact ⟨a, [b], σ, rfl, h₁, matchExps_one_iff.2 ⟨b, rfl, h₂⟩⟩

/-- A three-element pattern list. -/
theorem matchExps_three_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ e₃ : Exp} {vs : List Value} :
    MatchExps env ρ [e₁, e₂, e₃] vs ρ' ↔
      ∃ a b c σ τ, vs = [a, b, c] ∧ MatchExp env ρ e₁ a σ ∧ MatchExp env σ e₂ b τ ∧
        MatchExp env τ e₃ c ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, c, τ, rfl, hb, hc⟩ := matchExps_two_iff.1 h₂
    exact ⟨w, b, c, σ, τ, rfl, h₁, hb, hc⟩
  · rintro ⟨a, b, c, σ, τ, rfl, h₁, h₂, h₃⟩
    exact ⟨a, [b, c], σ, rfl, h₁, matchExps_two_iff.2 ⟨b, c, τ, rfl, h₂, h₃⟩⟩

/-- A four-element pattern list. -/
theorem matchExps_four_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ e₃ e₄ : Exp}
    {vs : List Value} :
    MatchExps env ρ [e₁, e₂, e₃, e₄] vs ρ' ↔
      ∃ a b c d σ τ υ, vs = [a, b, c, d] ∧ MatchExp env ρ e₁ a σ ∧ MatchExp env σ e₂ b τ ∧
        MatchExp env τ e₃ c υ ∧ MatchExp env υ e₄ d ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, c, d, τ, υ, rfl, hb, hc, hd⟩ := matchExps_three_iff.1 h₂
    exact ⟨w, b, c, d, σ, τ, υ, rfl, h₁, hb, hc, hd⟩
  · rintro ⟨a, b, c, d, σ, τ, υ, rfl, h₁, h₂, h₃, h₄⟩
    exact ⟨a, [b, c, d], σ, rfl, h₁, matchExps_three_iff.2 ⟨b, c, d, τ, υ, rfl, h₂, h₃, h₄⟩⟩

/-- A nullary injection pattern matches exactly its own injection. -/
theorem matchExp_caseNil_iff {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {v : Value} :
    MatchExp env ρ (.caseE op (.tupE [])) v ρ' ↔ v = caseNilV op ∧ ρ' = ρ := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨vs, rfl, hvs⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 hvs
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨.tuple [], rfl, Validation.matchExp_tup_iff.2
      ⟨[], rfl, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩

/-- The empty list pattern matches exactly the empty list. -/
theorem matchExp_listNil_iff {env : Env} {ρ ρ' : VarEnv} {v : Value} :
    MatchExp env ρ (.listE []) v ρ' ↔ v = .list [] ∧ ρ' = ρ := by
  rw [Validation.matchExp_list_iff]
  constructor
  · rintro ⟨vs, rfl, hvs⟩
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 hvs
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨[], rfl, Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩

/-- The conclusion of every `Step_pure` rule is the pair `(instr*, instr'*)`. -/
theorem matchExp_concl_iff {env : Env} {ρ ρ' : VarEnv} {el er : Exp} {v : Value} :
    MatchExp env ρ (.tupE [el, er]) v ρ' ↔
      ∃ a b σ, v = .tuple [a, b] ∧ MatchExp env ρ el a σ ∧ MatchExp env σ er b ρ' := by
  rw [Validation.matchExp_tup_iff]
  constructor
  · rintro ⟨vs, rfl, hvs⟩
    obtain ⟨a, b, σ, rfl, h₁, h₂⟩ := matchExps_two_iff.1 hvs
    exact ⟨a, b, σ, rfl, h₁, h₂⟩
  · rintro ⟨a, b, σ, rfl, h₁, h₂⟩
    exact ⟨[a, b], rfl, matchExps_two_iff.2 ⟨a, b, σ, rfl, h₁, h₂⟩⟩

/-! ## The rules that do fire, characterised exactly

Each theorem below says, in **both** directions, exactly which values of
`Step_pure`'s type a single rule derives. -/

/-- `Step_pure/nop` (`4.3:55-56`): `NOP ~> eps`, and nothing else. -/
theorem ruleFires_nop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v nopRule ↔ v = stepV [nopV] [] := by
  unfold nopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 has
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hc
    obtain ⟨rfl, rfl⟩ := matchExp_listNil_iff.1 hr
    rfl
  · rintro rfl
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩, premsHold_nil⟩

/-- `Step_pure/unreachable` (`4.3:52-53`): `UNREACHABLE ~> TRAP`. -/
theorem ruleFires_unreachable_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v unreachableRule ↔ v = stepV [unreachableV] [trapV] := by
  unfold unreachableRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 has
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hc
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hd
    rfl
  · rintro rfl
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, premsHold_nil⟩

/-! ### Scopes, concretely

The rules below build their scope by binding one pattern variable at a time,
so every lookup is decided by these two equations. -/

/-- Nothing is bound in the empty scope. -/
theorem findVal?_empty (x : IL.Id) : VarEnv.empty.findVal? x = none := rfl

/-- One step of a lookup through a scope built by `bindVal`. -/
theorem findVal?_bindVal_lit {ρ : VarEnv} {x y : IL.Id} {v : Value} (hx : x ≠ "_") :
    (ρ.bindVal x v).findVal? y = if x = y then some v else ρ.findVal? y := by
  simp only [VarEnv.findVal?, VarEnv.bindVal, Map.bind, hx, reduceIte, Map.find?]

attribute [local simp] findVal?_empty findVal?_bindVal_lit

/-- A fresh pattern variable binds. -/
theorem matchExp_freshVar_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v : Value}
    (hx : ρ.findVal? x = none) : MatchExp env ρ (.varE x) v ρ' ↔ ρ' = ρ.bindVal x v :=
  bindsVar_varE x ρ ρ' v hx

/-- A pattern variable that is already bound tests. -/
theorem matchExp_boundVar_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v w : Value}
    (hx : ρ.findVal? x = some w) : MatchExp env ρ (.varE x) v ρ' ↔ v = w ∧ ρ' = ρ := by
  rw [Validation.matchExp_var_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, rfl⟩)
    · rw [hx] at h; exact absurd h (by simp)
    · rw [hx] at h; exact ⟨(Option.some.inj h).symm, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact Or.inr ⟨hx, rfl⟩

/-- `Step_pure/drop` (`4.3:58-59`): `val DROP ~> eps`.  The quantifier
`val : val` is dropped by `anyRule`, so the dropped operand is an *arbitrary*
value — see the findings. -/
theorem ruleFires_drop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v dropRule ↔ ∃ w, v = stepV [w, dropV] [] := by
  unfold dropRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨c, d, τ, rfl, -, hd⟩ := matchExps_two_iff.1 has
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hd
    obtain ⟨rfl, rfl⟩ := matchExp_listNil_iff.1 hr
    exact ⟨c, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩, premsHold_nil⟩

/-- `Step_pure/local.tee` (`4.3:323-324`):
`val (LOCAL.TEE x) ~> val val (LOCAL.SET x)`. -/
theorem ruleFires_localTee_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v localTeeRule ↔
      ∃ w x, v = stepV [w, localTeeV x] [w, w, localSetV x] := by
  unfold localTeeRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨c, d, τ, rfl, hc, hd⟩ := matchExps_two_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨xv, rfl, hx⟩ := Validation.matchExp_case_iff.1 hd
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨p, q, r, υ, κ, rfl, h₁, h₂, h₃⟩ := matchExps_three_iff.1 hbs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := c) (by simp)] at h₁
    obtain ⟨hp, rfl⟩ := h₁
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := c) (by simp)] at h₂
    obtain ⟨hq, rfl⟩ := h₂
    obtain ⟨yv, rfl, hy⟩ := Validation.matchExp_case_iff.1 h₃
    rw [matchExp_boundVar_iff (w := xv) (by simp)] at hy
    obtain ⟨hyv, -⟩ := hy
    exact ⟨c, xv, by rw [hp, hq, hyv]; rfl⟩
  · rintro ⟨w, x, rfl⟩
    refine ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff (w := w) (by simp)).2 ⟨rfl, rfl⟩),
          Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff (w := w) (by simp)).2 ⟨rfl, rfl⟩),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_boundVar_iff (w := x) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩, premsHold_nil⟩

/-- `Step_pure/trap-frame` (`4.3:310-311`):
`(FRAME_ n {f} TRAP) ~> TRAP`.  Both `n` and `f` are bare pattern variables,
so the derivation holds of *arbitrary* values there. -/
theorem ruleFires_trapFrame_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v trapFrameRule ↔
      ∃ n f, v = stepV [frameV n f [trapV]] [trapV] := by
  unfold trapFrameRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, rfl, hp⟩ := matchExps_one_iff.1 has
    obtain ⟨q, rfl, hq⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨qs, rfl, hqs⟩ := Validation.matchExp_tup_iff.1 hq
    obtain ⟨nv, fv, tv, σ₁, σ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 hqs
    rw [matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [matchExp_freshVar_iff (by simp)] at h2
    subst h2
    obtain ⟨ts, rfl, hts⟩ := Validation.matchExp_list_iff.1 h3
    obtain ⟨t, rfl, ht⟩ := matchExps_one_iff.1 hts
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hd
    exact ⟨nv, fv, rfl⟩
  · rintro ⟨n, f, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, premsHold_nil⟩

/-- `Step_pure/trap-label` (`4.3:304-305`):
`(LABEL_ n {instr*} TRAP) ~> TRAP`. -/
theorem ruleFires_trapLabel_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v trapLabelRule ↔
      ∃ n cs, v = stepV [labelV n cs [trapV]] [trapV] := by
  unfold trapLabelRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, rfl, hp⟩ := matchExps_one_iff.1 has
    obtain ⟨q, rfl, hq⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨qs, rfl, hqs⟩ := Validation.matchExp_tup_iff.1 hq
    obtain ⟨nv, iv, tv, σ₁, σ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 hqs
    rw [matchExp_freshVar_iff (by simp)] at h1
    subst h1
    obtain ⟨cs, rfl, hi⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 h2
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨ts, rfl, hts⟩ := Validation.matchExp_list_iff.1 h3
    obtain ⟨t, rfl, ht⟩ := matchExps_one_iff.1 hts
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hd
    exact ⟨nv, cs, rfl⟩
  · rintro ⟨n, cs, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
            Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, premsHold_nil⟩

/-- `Step_pure/trap-handler` (`4.3:307-308`):
`(HANDLER_ n {catch*} TRAP) ~> TRAP`. -/
theorem ruleFires_trapHandler_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v trapHandlerRule ↔
      ∃ n cs, v = stepV [handlerV n cs [trapV]] [trapV] := by
  unfold trapHandlerRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, rfl, hp⟩ := matchExps_one_iff.1 has
    obtain ⟨q, rfl, hq⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨qs, rfl, hqs⟩ := Validation.matchExp_tup_iff.1 hq
    obtain ⟨nv, iv, tv, σ₁, σ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 hqs
    rw [matchExp_freshVar_iff (by simp)] at h1
    subst h1
    obtain ⟨cs, rfl, hi⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 h2
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨ts, rfl, hts⟩ := Validation.matchExp_list_iff.1 h3
    obtain ⟨t, rfl, ht⟩ := matchExps_one_iff.1 hts
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 hd
    exact ⟨nv, cs, rfl⟩
  · rintro ⟨n, cs, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
            Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, premsHold_nil⟩

/-- `Step_pure/label-vals` (`4.3:94-95`): `(LABEL_ n {instr*} val*) ~> val*`.

The rule's quantifiers `n : n` and `val* : val*` are dropped by `anyRule`
(`Equiv/Validation.lean`, "`derives` drops a rule's quantifiers"), so `n` is
an **arbitrary value** and the label body is an **arbitrary instruction
sequence** — it is not required to consist of values.  See the findings. -/
theorem ruleFires_labelVals_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v labelValsRule ↔
      ∃ n cs ws, v = stepV [labelV n cs ws] ws := by
  unfold labelValsRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, rfl, hp⟩ := matchExps_one_iff.1 has
    obtain ⟨q, rfl, hq⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨qs, rfl, hqs⟩ := Validation.matchExp_tup_iff.1 hq
    obtain ⟨nv, iv, wv, σ₁, σ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 hqs
    rw [matchExp_freshVar_iff (by simp)] at h1
    subst h1
    obtain ⟨cs, rfl, hi⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 h2
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨ws, rfl, hw⟩ :=
      (matchExp_iterE_list_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).1 h3
    rw [matchExp_freshVar_iff (by simp)] at hw
    subst hw
    obtain ⟨bs, rfl, hb⟩ :=
      (matchExp_iterE_list_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).1 hr
    rw [matchExp_boundVar_iff (w := Value.list ws) (by simp)] at hb
    obtain ⟨hbs, -⟩ := hb
    injection hbs with hbs
    exact ⟨nv, cs, ws, by rw [hbs]; rfl⟩
  · rintro ⟨n, cs, ws, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
            (matchExp_iterE_list_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).2
              ⟨ws, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
      (matchExp_iterE_list_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).2
        ⟨ws, rfl, (matchExp_boundVar_iff (w := Value.list ws) (by simp)).2 ⟨rfl, rfl⟩⟩⟩,
      premsHold_nil⟩

/-- `Step_pure/handler-vals` (`4.3:294-295`):
`(HANDLER_ n {catch*} val*) ~> val*`, with the same two gaps. -/
theorem ruleFires_handlerVals_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v handlerValsRule ↔
      ∃ n cs ws, v = stepV [handlerV n cs ws] ws := by
  unfold handlerValsRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, rfl, hp⟩ := matchExps_one_iff.1 has
    obtain ⟨q, rfl, hq⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨qs, rfl, hqs⟩ := Validation.matchExp_tup_iff.1 hq
    obtain ⟨nv, iv, wv, σ₁, σ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 hqs
    rw [matchExp_freshVar_iff (by simp)] at h1
    subst h1
    obtain ⟨cs, rfl, hi⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 h2
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨ws, rfl, hw⟩ :=
      (matchExp_iterE_list_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).1 h3
    rw [matchExp_freshVar_iff (by simp)] at hw
    subst hw
    obtain ⟨bs, rfl, hb⟩ :=
      (matchExp_iterE_list_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).1 hr
    rw [matchExp_boundVar_iff (w := Value.list ws) (by simp)] at hb
    obtain ⟨hbs, -⟩ := hb
    injection hbs with hbs
    exact ⟨nv, cs, ws, by rw [hbs]; rfl⟩
  · rintro ⟨n, cs, ws, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
            (matchExp_iterE_list_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).2
              ⟨ws, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
      (matchExp_iterE_list_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).2
        ⟨ws, rfl, (matchExp_boundVar_iff (w := Value.list ws) (by simp)).2 ⟨rfl, rfl⟩⟩⟩,
      premsHold_nil⟩

/-- `Step_pure/frame-vals` (`4.3:227-228`): `(FRAME_ n {f} val^n) ~> val^n`.

Unlike `label-vals`, the arity here *is* constrained: the body iterates with
`^n`, and `matchIterE`'s `ListN` clause matches the counter pattern — the
already-bound `n` — against the list's length.  The frame `f` is still a bare
variable, so it is an arbitrary value. -/
theorem ruleFires_frameVals_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v frameValsRule ↔
      ∃ f ws, v = stepV [frameV (.num (.natN ws.length)) f ws] ws := by
  unfold frameValsRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, rfl, hp⟩ := matchExps_one_iff.1 has
    obtain ⟨q, rfl, hq⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨qs, rfl, hqs⟩ := Validation.matchExp_tup_iff.1 hq
    obtain ⟨nv, fv, wv, σ₁, σ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 hqs
    rw [matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [matchExp_freshVar_iff (by simp)] at h2
    subst h2
    obtain ⟨ws, τ, rfl, hn, hil⟩ := matchExp_iterE_listN_iff.1 h3
    rw [matchExp_boundVar_iff (w := nv) (by simp)] at hn
    obtain ⟨hnv, rfl⟩ := hn
    rw [matchIterList_single_iff (bindsVar_subVar _ _ _) (by simp) (by simp)] at hil
    rw [matchExp_freshVar_iff (by simp)] at hil
    subst hil
    obtain ⟨bs, τ', rfl, hn', hil'⟩ := matchExp_iterE_listN_iff.1 hr
    rw [matchExp_boundVar_iff (w := nv) (by simp)] at hn'
    obtain ⟨-, rfl⟩ := hn'
    rw [matchIterList_single_iff (bindsVar_subVar _ _ _) (by simp) (by simp)] at hil'
    rw [matchExp_boundVar_iff (w := Value.list ws) (by simp)] at hil'
    obtain ⟨hbs, -⟩ := hil'
    injection hbs with hbs
    exact ⟨fv, ws, by rw [hbs, ← hnv]; rfl⟩
  · rintro ⟨f, ws, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            matchExp_iterE_listN_iff.2 ⟨ws, _, rfl,
              (matchExp_boundVar_iff (w := Value.num (.natN ws.length)) (by simp)).2
                ⟨rfl, rfl⟩,
              (matchIterList_single_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).2
                ((matchExp_freshVar_iff (by simp)).2 rfl)⟩⟩⟩⟩⟩⟩,
      matchExp_iterE_listN_iff.2 ⟨ws, _, rfl,
        (matchExp_boundVar_iff (w := Value.num (.natN ws.length)) (by simp)).2 ⟨rfl, rfl⟩,
        (matchIterList_single_iff (bindsVar_subVar _ _ _) (by simp) (by simp)).2
          ((matchExp_boundVar_iff (w := Value.list ws) (by simp)).2 ⟨rfl, rfl⟩)⟩⟩,
      premsHold_nil⟩

/-! ### The `c =/= 0` / `c = 0` side conditions

`SELECT`, `IF` and `BR_IF` all branch on `c =/= 0` where `c : num_(I32)`.
`num_(I32) = iN(32) = uN(32)`, a one-case variant whose mixop renders as `%`
(`1.1:10-11,14-15`, `Sem/Bridge.lean`'s "`percentV`"), so the elaborated
condition is `c!%.0 =/= 0` — *uncase*, then project component 0.  Nothing
forces that component to be a numeral; see the findings. -/

/-- `x!%.0` denotes `w` exactly when `x` is a `%` injection of a tuple whose
first component is `w`. -/
theorem evalExp_imm_iff {env : Env} {ρ : VarEnv} {x : IL.Id} {c w : Value}
    (hx : ρ.findVal? x = some c) :
    EvalExp env ρ (.projE (.uncaseE (.varE x) "%") 0) w ↔
      ∃ us, c = .case "%" (.tuple (w :: us)) := by
  rw [evalExp_projE_iff]
  constructor
  · rintro ⟨vs, hv, -, hidx⟩
    rw [evalExp_uncaseE_iff, evalExp_varE_iff, hx] at hv
    injection hv with hv
    cases vs with
    | nil => simp at hidx
    | cons u us =>
        simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hidx
        subst hidx
        exact ⟨us, hv⟩
  · rintro ⟨us, rfl⟩
    exact ⟨w :: us, by rw [evalExp_uncaseE_iff, evalExp_varE_iff]; exact hx, by simp, by simp⟩

/-- The side condition `x!%.0 =/= 0`, as the only premise of a rule. -/
theorem premsHold_immNe_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {c : Value}
    (hx : ρ.findVal? x = some c) :
    PremsHold env ρ
        [.ifPr (.cmpE .neOp .boolT (.projE (.uncaseE (.varE x) "%") 0) (.numE (.natN 0)))] ρ' ↔
      ρ' = ρ ∧ ∃ w us, c = .case "%" (.tuple (w :: us)) ∧ w ≠ .num (.natN 0) := by
  rw [Validation.premsHold_cons_iff]
  constructor
  · rintro ⟨σ, hp, hn⟩
    rw [Validation.premsHold_nil_iff] at hn
    subst hn
    rw [Validation.premHolds_if_iff] at hp
    obtain ⟨rfl, he⟩ := hp
    rw [evalExp_cmpE_iff] at he
    obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := he
    rw [evalExp_numE_iff] at h₂
    subst h₂
    obtain ⟨us, hcv⟩ := (evalExp_imm_iff hx).1 h₁
    refine ⟨rfl, v₁, us, hcv, ?_⟩
    simp only [cmpValues, Except.ok.injEq, Value.bool.injEq] at hc
    simpa using hc
  · rintro ⟨rfl, w, us, hcv, hw⟩
    refine ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩, Validation.premsHold_nil_iff.2 rfl⟩
    rw [evalExp_cmpE_iff]
    exact ⟨w, .num (.natN 0), (evalExp_imm_iff hx).2 ⟨us, hcv⟩, evalExp_numE_iff.2 rfl,
      by simp [cmpValues, hw]⟩

/-- The side condition `x!%.0 = 0`, as the only premise of a rule. -/
theorem premsHold_immEq_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {c : Value}
    (hx : ρ.findVal? x = some c) :
    PremsHold env ρ
        [.ifPr (.cmpE .eqOp .boolT (.projE (.uncaseE (.varE x) "%") 0) (.numE (.natN 0)))] ρ' ↔
      ρ' = ρ ∧ ∃ us, c = .case "%" (.tuple (.num (.natN 0) :: us)) := by
  rw [Validation.premsHold_cons_iff]
  constructor
  · rintro ⟨σ, hp, hn⟩
    rw [Validation.premsHold_nil_iff] at hn
    subst hn
    rw [Validation.premHolds_if_iff] at hp
    obtain ⟨rfl, he⟩ := hp
    rw [evalExp_cmpE_iff] at he
    obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := he
    rw [evalExp_numE_iff] at h₂
    subst h₂
    obtain ⟨us, hcv⟩ := (evalExp_imm_iff hx).1 h₁
    simp only [cmpValues, Except.ok.injEq, Value.bool.injEq] at hc
    have : v₁ = Value.num (.natN 0) := by simpa using hc
    subst this
    exact ⟨rfl, us, hcv⟩
  · rintro ⟨rfl, us, hcv⟩
    refine ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩, Validation.premsHold_nil_iff.2 rfl⟩
    rw [evalExp_cmpE_iff]
    exact ⟨.num (.natN 0), .num (.natN 0), (evalExp_imm_iff hx).2 ⟨us, hcv⟩,
      evalExp_numE_iff.2 rfl, by simp [cmpValues]⟩

/-- `Step_pure/br_if-true` (`4.3:113-115`):
`(CONST I32 c) (BR_IF l) ~> (BR l)` when `c =/= 0`. -/
theorem ruleFires_brIfTrue_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brIfTrueRule ↔
      ∃ w us l, v = stepV [constV i32V (.case "%" (.tuple (w :: us))), brIfV l] [brV l] ∧
        w ≠ .num (.natN 0) := by
  unfold brIfTrueRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hpr⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, hp, hq⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨t1, cv, τ₁, rfl, ht1, hcv⟩ := matchExps_two_iff.1 hpvs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht1
    rw [matchExp_freshVar_iff (by simp)] at hcv
    subst hcv
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 hq
    rw [matchExp_freshVar_iff (by simp)] at hlv
    subst hlv
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    obtain ⟨lv', rfl, hlv'⟩ := Validation.matchExp_case_iff.1 hd
    rw [matchExp_boundVar_iff (w := lv) (by simp)] at hlv'
    obtain ⟨hll, rfl⟩ := hlv'
    rw [premsHold_immNe_iff (c := cv) (by simp)] at hpr
    obtain ⟨-, w, us, hc, hw⟩ := hpr
    exact ⟨w, us, lv, by rw [hc, hll]; rfl, hw⟩
  · rintro ⟨w, us, l, rfl, hw⟩
    refine ⟨(VarEnv.empty.bindVal "c" (.case "%" (.tuple (w :: us)))).bindVal "l" l,
      (VarEnv.empty.bindVal "c" (.case "%" (.tuple (w :: us)))).bindVal "l" l,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          (matchExp_boundVar_iff (w := l) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩, ?_⟩
    exact (premsHold_immNe_iff (c := .case "%" (.tuple (w :: us))) (by simp)).2
      ⟨rfl, w, us, rfl, hw⟩

/-- `Step_pure/br_if-false` (`4.3:117-119`):
`(CONST I32 c) (BR_IF l) ~> eps` when `c = 0`. -/
theorem ruleFires_brIfFalse_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v brIfFalseRule ↔
      ∃ us l, v = stepV [constV i32V (.case "%" (.tuple (.num (.natN 0) :: us))), brIfV l] [] := by
  unfold brIfFalseRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hpr⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, hp, hq⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨t1, cv, τ₁, rfl, ht1, hcv⟩ := matchExps_two_iff.1 hpvs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht1
    rw [matchExp_freshVar_iff (by simp)] at hcv
    subst hcv
    obtain ⟨lv, rfl, hlv⟩ := Validation.matchExp_case_iff.1 hq
    rw [matchExp_freshVar_iff (by simp)] at hlv
    subst hlv
    obtain ⟨rfl, rfl⟩ := matchExp_listNil_iff.1 hr
    rw [premsHold_immEq_iff (c := cv) (by simp)] at hpr
    obtain ⟨-, us, hc⟩ := hpr
    exact ⟨us, lv, by rw [hc]; rfl⟩
  · rintro ⟨us, l, rfl⟩
    refine ⟨(VarEnv.empty.bindVal "c" (.case "%" (.tuple (.num (.natN 0) :: us)))).bindVal "l" l,
      (VarEnv.empty.bindVal "c" (.case "%" (.tuple (.num (.natN 0) :: us)))).bindVal "l" l,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩, ?_⟩
    exact (premsHold_immEq_iff (c := .case "%" (.tuple (.num (.natN 0) :: us))) (by simp)).2
      ⟨rfl, us, rfl⟩

/-- `Step_pure/if-true` (`4.3:85-87`):
`(CONST I32 c) (IF bt instr_1* ELSE instr_2*) ~> (BLOCK bt instr_1*)` when
`c =/= 0`. -/
theorem ruleFires_ifTrue_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v ifTrueRule ↔
      ∃ w us bt is js,
        v = stepV [constV i32V (.case "%" (.tuple (w :: us))), ifV bt is js] [blockV bt is] ∧
        w ≠ .num (.natN 0) := by
  unfold ifTrueRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hpr⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, hp, hq⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨t1, cv, τ₁, rfl, ht1, hcv⟩ := matchExps_two_iff.1 hpvs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht1
    rw [matchExp_freshVar_iff (by simp)] at hcv
    subst hcv
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 hq
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨btv, i1, i2, κ₁, κ₂, rfl, hbt, h1, h2⟩ := matchExps_three_iff.1 hqvs
    rw [matchExp_freshVar_iff (by simp)] at hbt
    subst hbt
    obtain ⟨is, rfl, hi1⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 h1
    rw [matchExp_freshVar_iff (by simp)] at hi1
    subst hi1
    obtain ⟨js, rfl, hi2⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 h2
    rw [matchExp_freshVar_iff (by simp)] at hi2
    subst hi2
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    obtain ⟨dv, rfl, hdv⟩ := Validation.matchExp_case_iff.1 hd
    obtain ⟨dvs, rfl, hdvs⟩ := Validation.matchExp_tup_iff.1 hdv
    obtain ⟨btv', is', μ, rfl, hbt', his'⟩ := matchExps_two_iff.1 hdvs
    rw [matchExp_boundVar_iff (w := btv) (by simp)] at hbt'
    obtain ⟨hbe, rfl⟩ := hbt'
    obtain ⟨ks, rfl, hks⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 his'
    rw [matchExp_boundVar_iff (w := Value.list is) (by simp)] at hks
    obtain ⟨hke, rfl⟩ := hks
    injection hke with hke
    rw [premsHold_immNe_iff (c := cv) (by simp)] at hpr
    obtain ⟨-, w, us, hc, hw⟩ := hpr
    exact ⟨w, us, btv, is, js, by rw [hc, hbe, hke]; rfl, hw⟩
  · rintro ⟨w, us, bt, is, js, rfl, hw⟩
    refine ⟨((((VarEnv.empty.bindVal "c" (.case "%" (.tuple (w :: us)))).bindVal "bt" bt).bindVal
        "instr_1*" (.list is)).bindVal "instr_2*" (.list js)),
      ((((VarEnv.empty.bindVal "c" (.case "%" (.tuple (w :: us)))).bindVal "bt" bt).bindVal
        "instr_1*" (.list is)).bindVal "instr_2*" (.list js)),
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨is, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨js, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_boundVar_iff (w := bt) (by simp)).2 ⟨rfl, rfl⟩,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨is, rfl, (matchExp_boundVar_iff (w := Value.list is) (by simp)).2
                ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩, ?_⟩
    exact (premsHold_immNe_iff (c := .case "%" (.tuple (w :: us))) (by simp)).2
      ⟨rfl, w, us, rfl, hw⟩

/-- `Step_pure/if-false` (`4.3:89-91`):
`(CONST I32 c) (IF bt instr_1* ELSE instr_2*) ~> (BLOCK bt instr_2*)` when
`c = 0`. -/
theorem ruleFires_ifFalse_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v ifFalseRule ↔
      ∃ us bt is js,
        v = stepV [constV i32V (.case "%" (.tuple (.num (.natN 0) :: us))), ifV bt is js]
          [blockV bt js] := by
  unfold ifFalseRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hpr⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, hp, hq⟩ := matchExps_two_iff.1 has
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 hp
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨t1, cv, τ₁, rfl, ht1, hcv⟩ := matchExps_two_iff.1 hpvs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht1
    rw [matchExp_freshVar_iff (by simp)] at hcv
    subst hcv
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 hq
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨btv, i1, i2, κ₁, κ₂, rfl, hbt, h1, h2⟩ := matchExps_three_iff.1 hqvs
    rw [matchExp_freshVar_iff (by simp)] at hbt
    subst hbt
    obtain ⟨is, rfl, hi1⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 h1
    rw [matchExp_freshVar_iff (by simp)] at hi1
    subst hi1
    obtain ⟨js, rfl, hi2⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 h2
    rw [matchExp_freshVar_iff (by simp)] at hi2
    subst hi2
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    obtain ⟨dv, rfl, hdv⟩ := Validation.matchExp_case_iff.1 hd
    obtain ⟨dvs, rfl, hdvs⟩ := Validation.matchExp_tup_iff.1 hdv
    obtain ⟨btv', js', μ, rfl, hbt', hjs'⟩ := matchExps_two_iff.1 hdvs
    rw [matchExp_boundVar_iff (w := btv) (by simp)] at hbt'
    obtain ⟨hbe, rfl⟩ := hbt'
    obtain ⟨ks, rfl, hks⟩ :=
      (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).1 hjs'
    rw [matchExp_boundVar_iff (w := Value.list js) (by simp)] at hks
    obtain ⟨hke, rfl⟩ := hks
    injection hke with hke
    rw [premsHold_immEq_iff (c := cv) (by simp)] at hpr
    obtain ⟨-, us, hc⟩ := hpr
    exact ⟨us, btv, is, js, by rw [hc, hbe, hke]; rfl⟩
  · rintro ⟨us, bt, is, js, rfl⟩
    refine ⟨((((VarEnv.empty.bindVal "c" (.case "%" (.tuple (.num (.natN 0) :: us)))).bindVal
        "bt" bt).bindVal "instr_1*" (.list is)).bindVal "instr_2*" (.list js)),
      ((((VarEnv.empty.bindVal "c" (.case "%" (.tuple (.num (.natN 0) :: us)))).bindVal
        "bt" bt).bindVal "instr_1*" (.list is)).bindVal "instr_2*" (.list js)),
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨is, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨js, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_boundVar_iff (w := bt) (by simp)).2 ⟨rfl, rfl⟩,
            (matchExp_iterE_list_iff (bindsVar_varE _) (by simp) (by simp)).2
              ⟨js, rfl, (matchExp_boundVar_iff (w := Value.list js) (by simp)).2
                ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩, ?_⟩
    exact (premsHold_immEq_iff (c := .case "%" (.tuple (.num (.natN 0) :: us))) (by simp)).2
      ⟨rfl, us, rfl⟩

/-- **The `SELECT (t*)?` annotation, exactly.**  `1.3:223` gives `SELECT` the
payload `(valtype*)?`, which elaborates to a `?`
iteration over a `*` iteration (`(iter (iter (var "valtype") list) opt)` in
the pinned stream).  Matching it against a value forces an option of a list
and binds the whole annotation to `t*?`; the element type is *not* checked,
because the quantifier `t*? : valtype*?` is dropped. -/
theorem matchExp_selectAnnot_iff {env : Env} {ρ ρ' : VarEnv} {v : Value}
    (h₁ : ρ.findVal? "t" = none) (h₂ : ρ.findVal? "t*" = none)
    (h₃ : ρ.findVal? "t*?" = none) :
    MatchExp env ρ (.iterE (.iterE (.varE "t") (.mk .list [.mk "t" (.varE "t*")]))
        (.mk .opt [.mk "t*" (.varE "t*?")])) v ρ' ↔
      (v = .opt none ∨ ∃ l : List Value, v = .opt (some (.list l))) ∧
        ρ' = ρ.bindVal "t*?" v := by
  rw [matchExp_iterE_opt_iff]
  constructor
  · rintro (⟨rfl, hy⟩ | ⟨wv, σ, u, rfl, hinner, hu, hy⟩)
    · rw [matchExp_freshVar_iff h₃] at hy
      exact ⟨Or.inl rfl, hy⟩
    · obtain ⟨l, rfl, hl⟩ :=
        (matchExp_iterE_list_iff (bindsVar_varE _) h₁ (by simp)).1 hinner
      rw [matchExp_freshVar_iff h₂] at hl
      subst hl
      rw [findVal?_bindVal_lit (by simp)] at hu
      simp only [reduceIte, Option.some.injEq] at hu
      subst hu
      rw [matchExp_freshVar_iff h₃] at hy
      exact ⟨Or.inr ⟨l, rfl⟩, hy⟩
  · rintro ⟨hv | ⟨l, rfl⟩, rfl⟩
    · subst hv
      exact Or.inl ⟨rfl, (matchExp_freshVar_iff h₃).2 rfl⟩
    · refine Or.inr ⟨.list l, ρ.bindVal "t*" (.list l), .list l, rfl, ?_, ?_,
        (matchExp_freshVar_iff h₃).2 rfl⟩
      · exact (matchExp_iterE_list_iff (bindsVar_varE _) h₁ (by simp)).2
          ⟨l, rfl, (matchExp_freshVar_iff h₂).2 rfl⟩
      · rw [findVal?_bindVal_lit (by simp)]
        simp

/-- `Step_pure/select-true` (`4.3:62-64`):
`val_1 val_2 (CONST I32 c) (SELECT (t*)?) ~> val_1` when `c =/= 0`. -/
theorem ruleFires_selectTrue_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v selectTrueRule ↔
      ∃ v₁ v₂ w us ts,
        v = stepV [v₁, v₂, constV i32V (.case "%" (.tuple (w :: us))), selectV ts] [v₁] ∧
        w ≠ .num (.natN 0) ∧
        (ts = .opt none ∨ ∃ l : List Value, ts = .opt (some (.list l))) := by
  unfold selectTrueRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hpr⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨a1, a2, pc, ps, κ₁, κ₂, κ₃, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h2
    subst h2
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h3
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨t1, cv, κ, rfl, ht1, hcv⟩ := matchExps_two_iff.1 hpvs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht1
    rw [matchExp_freshVar_iff (by simp)] at hcv
    subst hcv
    obtain ⟨tsv, rfl, hts⟩ := Validation.matchExp_case_iff.1 h4
    rw [matchExp_selectAnnot_iff (by simp) (by simp) (by simp)] at hts
    obtain ⟨hshape, rfl⟩ := hts
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := a1) (by simp)] at hd
    obtain ⟨hde, rfl⟩ := hd
    rw [premsHold_immNe_iff (c := cv) (by simp)] at hpr
    obtain ⟨-, w, us, hc, hw⟩ := hpr
    exact ⟨a1, a2, w, us, tsv, by rw [hc, hde]; rfl, hw, hshape⟩
  · rintro ⟨v₁, v₂, w, us, ts, rfl, hw, hshape⟩
    refine ⟨((((VarEnv.empty.bindVal "val_1" v₁).bindVal "val_2" v₂).bindVal "c"
        (.case "%" (.tuple (w :: us)))).bindVal "t*?" ts),
      ((((VarEnv.empty.bindVal "val_1" v₁).bindVal "val_2" v₂).bindVal "c"
        (.case "%" (.tuple (w :: us)))).bindVal "t*?" ts),
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          (matchExp_selectAnnot_iff (by simp) (by simp) (by simp)).2 ⟨hshape, rfl⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_sub_iff.2
          ((matchExp_boundVar_iff (w := v₁) (by simp)).2 ⟨rfl, rfl⟩)⟩⟩⟩, ?_⟩
    exact (premsHold_immNe_iff (c := .case "%" (.tuple (w :: us))) (by simp)).2
      ⟨rfl, w, us, rfl, hw⟩

/-- `Step_pure/select-false` (`4.3:66-68`):
`val_1 val_2 (CONST I32 c) (SELECT (t*)?) ~> val_2` when `c = 0`. -/
theorem ruleFires_selectFalse_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v selectFalseRule ↔
      ∃ v₁ v₂ us ts,
        v = stepV [v₁, v₂, constV i32V (.case "%" (.tuple (.num (.natN 0) :: us))),
          selectV ts] [v₂] ∧
        (ts = .opt none ∨ ∃ l : List Value, ts = .opt (some (.list l))) := by
  unfold selectFalseRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hpr⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨tl, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨a1, a2, pc, ps, κ₁, κ₂, κ₃, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 has
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h1
    subst h1
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at h2
    subst h2
    obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h3
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
    obtain ⟨t1, cv, κ, rfl, ht1, hcv⟩ := matchExps_two_iff.1 hpvs
    obtain ⟨rfl, rfl⟩ := matchExp_caseNil_iff.1 ht1
    rw [matchExp_freshVar_iff (by simp)] at hcv
    subst hcv
    obtain ⟨tsv, rfl, hts⟩ := Validation.matchExp_case_iff.1 h4
    rw [matchExp_selectAnnot_iff (by simp) (by simp) (by simp)] at hts
    obtain ⟨hshape, rfl⟩ := hts
    obtain ⟨bs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨d, rfl, hd⟩ := matchExps_one_iff.1 hbs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := a2) (by simp)] at hd
    obtain ⟨hde, rfl⟩ := hd
    rw [premsHold_immEq_iff (c := cv) (by simp)] at hpr
    obtain ⟨-, us, hc⟩ := hpr
    exact ⟨a1, a2, us, tsv, by rw [hc, hde]; rfl, hshape⟩
  · rintro ⟨v₁, v₂, us, ts, rfl, hshape⟩
    refine ⟨((((VarEnv.empty.bindVal "val_1" v₁).bindVal "val_2" v₂).bindVal "c"
        (.case "%" (.tuple (.num (.natN 0) :: us)))).bindVal "t*?" ts),
      ((((VarEnv.empty.bindVal "val_1" v₁).bindVal "val_2" v₂).bindVal "c"
        (.case "%" (.tuple (.num (.natN 0) :: us)))).bindVal "t*?" ts),
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
        Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          (matchExp_selectAnnot_iff (by simp) (by simp) (by simp)).2 ⟨hshape, rfl⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_sub_iff.2
          ((matchExp_boundVar_iff (w := v₂) (by simp)).2 ⟨rfl, rfl⟩)⟩⟩⟩, ?_⟩
    exact (premsHold_immEq_iff (c := .case "%" (.tuple (.num (.natN 0) :: us))) (by simp)).2
      ⟨rfl, us, rfl⟩

/-! ## The seven rules the search unblocks

`matchExp`'s `CatE` search (above, and `Sem/Eval.lean`) is what makes the
*structural* rules of `Step_pure` fire: every `br` out of a label or a
handler, every `return`, and trap propagation concatenates two `*`
iterations over domains the pattern is itself about to bind, so neither
operand has a `patLen` and the split has to be found.

The search takes the **first** split that matches, which is what the
hypotheses below say: the values in front of the marker must not themselves
look like the marker.  That is exactly the condition under which the
specification's own reading — "`val*` is a maximal run of values, and the
next instruction is the `BR`/`RETURN`/`TRAP`" — picks the same split, and it
holds for every genuine value sequence, since no `val` is a `BR`, a `RETURN`
or a `TRAP`.

These are constructions, not characterisations: each says the rule *does*
fire at the stated pair with the stated scope.  The converse — that it fires
at nothing else — would have to invert the search, and is not proved. -/

/-- `RETURN`. -/
def returnV : Value := caseNilV "RETURN"

/-- `val*` as the reduction rules write it: a `*` iteration whose body is the
subsorted variable `x : val <: instr`, over the domain `y`. -/
def valsPat (x y : IL.Id) : Exp :=
  .iterE (.subE (.varE x) (.varT "val" []) (.varT "instr" [])) (.mk .list [.mk x (.varE y)])

/-- `val^n`: the same body, iterated as many times as the bound counter `z`
names. -/
def valsNPat (x y z : IL.Id) : Exp :=
  .iterE (.subE (.varE x) (.varT "val" []) (.varT "instr" []))
    (.mk (.listN (.varE z) none) [.mk x (.varE y)])

/-- A plain `*` iteration over one domain whose body is that domain's element
variable: `instr*`, `instr'*`, `catch*`. -/
def iterPat (x y : IL.Id) : Exp := .iterE (.varE x) (.mk .list [.mk x (.varE y)])

/-- A one-element literal list: the `BR l`, `RETURN` and `TRAP` markers that
separate the two iterations. -/
def markPat (e : Exp) : Exp := .listE [e]

/-- A marker consumes exactly one element, and says so syntactically — this
is the one `patLen` source `eval.ml:923-932` also has. -/
theorem patLen_markPat {env : Env} {ρ : VarEnv} {e : Exp} :
    patLen 1 env ρ (markPat e) = .ok 1 := by
  simp [markPat, patLen]

/-- A `val*` pattern over an unbound domain has no length. -/
theorem noPatLen_valsPat {env : Env} {ρ : VarEnv} {x y : IL.Id}
    (hy : ρ.findVal? y = none) : NoPatLen env ρ (valsPat x y) :=
  noPatLen_iterE_list hy

/-- Neither has a plain `*` iteration. -/
theorem noPatLen_iterPat {env : Env} {ρ : VarEnv} {x y : IL.Id}
    (hy : ρ.findVal? y = none) : NoPatLen env ρ (iterPat x y) :=
  noPatLen_iterE_list hy

/-- Every index of a list, as `getElem?`: the fact behind
`iterRows_singleton`. -/
theorem mapRange_getElem? {α : Type} (l : List α) :
    (List.range l.length).map (fun i => l[i]?) = l.map some := by
  have key : ∀ (post pre : List α),
      (List.range' pre.length post.length).map (fun i => (pre ++ post)[i]?)
        = post.map some := by
    intro post
    induction post with
    | nil => intro pre; simp
    | cons w ws ih =>
        intro pre
        have hw : (pre ++ w :: ws)[pre.length]? = some w := by
          simp
        have hassoc : pre ++ w :: ws = (pre ++ [w]) ++ ws := by simp
        have hlen : (pre ++ [w]).length = pre.length + 1 := by simp
        simp only [List.length_cons]
        rw [List.range'_succ, List.map_cons, hw]
        congr 1
        rw [hassoc, ← hlen]
        exact ih (pre ++ [w])
  have h0 := key l []
  simp only [List.length_nil, List.nil_append] at h0
  rw [List.range_eq_range']
  exact h0

/-- The rounds of a one-domain, counter-free iteration: one round per
element, binding the domain variable to it. -/
theorem iterRows_singleton (x : IL.Id) (ws : List Value) :
    iterRows [(x, ws)] none ws.length = ws.map (fun w => [(x, w)]) := by
  have h : ∀ i, iterRow [(x, ws)] none i
      = ((ws[i]?).map (fun v => (x, v))).toList := by
    intro i
    rw [iterRow]
    rcases hi : ws[i]? with _ | v <;> simp [hi]
  have hmap : (List.range ws.length).map (iterRow [(x, ws)] none)
      = ((List.range ws.length).map (fun i => ws[i]?)).map
        (fun o => (o.map (fun v => (x, v))).toList) := by
    rw [List.map_map]
    exact List.map_congr_left fun i _ => h i
  rw [iterRows, hmap, mapRange_getElem?, List.map_map]
  simp

/-- The value of a one-domain `*` iteration whose body denotes the round's
own binding — a bare variable, or one under a subsort coercion: the list the
domain is bound to.  `d` is the extra fuel the body needs. -/
theorem evalExp_iterBody_var {env : Env} {ρ : VarEnv} {b : Exp} {x y : IL.Id} {d : Nat}
    (hb : ∀ (σ : VarEnv) (w : Value), σ.findVal? x = some w →
      evalExp (d + 1) env σ b = .ok w)
    (hx : x ≠ "_") {vs : List Value} (h : ρ.findVal? y = some (.list vs)) :
    EvalExp env ρ (.iterE b (.mk .list [.mk x (.varE y)])) (.list vs) := by
  refine evalExp_iterE_iff.mpr ⟨d + 4, ?_⟩
  have hdoms : evalDoms (d + 3) env ρ [.mk x (.varE y)] = .ok [(x, Value.list vs)] := by
    simp [evalDoms, domVar, domSrc, evalExp, h]
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, Value.asList?,
    List.isEmpty_cons]
  refine ⟨[(x, Value.list vs)], rfl, trivial, vs.length, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok, List.mapM_cons,
    List.mapM_nil]
  refine ⟨[(x, vs)], by simp [Value.asList?], by simp, vs, ?_, rfl⟩
  rw [iterRows_singleton, evalRounds]
  clear hdoms h
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.map_cons, List.mapM_cons, Res.bind_eq_ok]
      refine ⟨v, ?_, vs, ih, rfl⟩
      exact hb _ v (by simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx])

/-- `val*` evaluates to the list its domain is bound to. -/
theorem evalExp_valsPat {env : Env} {ρ : VarEnv} {x y : IL.Id} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? y = some (.list vs)) :
    EvalExp env ρ (valsPat x y) (.list vs) :=
  evalExp_iterBody_var (d := 1)
    (fun σ w hw => by simp [evalExp, hw, Res.ofOption]) hx h

/-- …and so does a plain `*` iteration. -/
theorem evalExp_iterPat {env : Env} {ρ : VarEnv} {x y : IL.Id} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? y = some (.list vs)) :
    EvalExp env ρ (iterPat x y) (.list vs) :=
  evalExp_iterBody_var (d := 0)
    (fun σ w hw => by simp [evalExp, hw, Res.ofOption]) hx h

/-- Hence, once its domain is bound, `val*` *does* have a `patLen`: the
length of that list.  This is why the right-hand side of each rule needs no
search. -/
theorem patLen_valsPat_bound {env : Env} {ρ : VarEnv} {x y : IL.Id} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? y = some (.list vs)) :
    ∃ m, patLen m env ρ (valsPat x y) = .ok vs.length := by
  obtain ⟨n, hn⟩ := evalExp_valsPat (env := env) hx h
  refine ⟨n + 1, ?_⟩
  simp only [valsPat] at hn ⊢
  simp [patLen, hn, Res.ofOption, Bind.bind, Except.bind, Value.len?]

/-- A fresh `val*` binds its domain to whatever list it is given. -/
theorem matchExp_valsPat_fresh {env : Env} {ρ : VarEnv} {x y : IL.Id}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") (hy : ρ.findVal? y = none)
    (vs : List Value) :
    MatchExp env ρ (valsPat x y) (.list vs) (ρ.bindVal y (.list vs)) :=
  (matchExp_iterE_list_iff (bindsVar_subVar x _ _) hx hx').2
    ⟨vs, rfl, (matchExp_freshVar_iff hy).2 rfl⟩

/-- A `val*` whose domain is already bound tests instead of binding. -/
theorem matchExp_valsPat_bound {env : Env} {ρ : VarEnv} {x y : IL.Id}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") {vs : List Value}
    (hy : ρ.findVal? y = some (.list vs)) :
    MatchExp env ρ (valsPat x y) (.list vs) ρ :=
  (matchExp_iterE_list_iff (bindsVar_subVar x _ _) hx hx').2
    ⟨vs, rfl, (matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩⟩

/-- The same two facts for a plain `*` iteration. -/
theorem matchExp_iterPat_fresh {env : Env} {ρ : VarEnv} {x y : IL.Id}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") (hy : ρ.findVal? y = none)
    (vs : List Value) :
    MatchExp env ρ (iterPat x y) (.list vs) (ρ.bindVal y (.list vs)) :=
  (matchExp_iterE_list_iff (bindsVar_varE x) hx hx').2
    ⟨vs, rfl, (matchExp_freshVar_iff hy).2 rfl⟩

/-- A `val^n` whose counter is bound to the list's own length. -/
theorem matchExp_valsNPat {env : Env} {ρ : VarEnv} {x y z : IL.Id}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") (hy : ρ.findVal? y = none)
    {vs : List Value} (hz : ρ.findVal? z = some (.num (.natN vs.length))) :
    MatchExp env ρ (valsNPat x y z) (.list vs) (ρ.bindVal y (.list vs)) :=
  matchExp_iterE_listN_iff.2 ⟨vs, ρ, rfl, (matchExp_boundVar_iff hz).2 ⟨rfl, rfl⟩,
    (matchIterList_single_iff (bindsVar_subVar x _ _) hx hx').2
      ((matchExp_freshVar_iff hy).2 rfl)⟩

/-- A marker that binds an immediate, such as `BR l`. -/
theorem matchExp_markPat_var {env : Env} {ρ : VarEnv} {op : MixopS} {l : IL.Id}
    (hl : ρ.findVal? l = none) (w : Value) :
    MatchExp env ρ (markPat (.caseE op (.varE l))) (.list [.case op w]) (ρ.bindVal l w) :=
  Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
    Validation.matchExp_case_iff.2 ⟨w, rfl, (matchExp_freshVar_iff hl).2 rfl⟩⟩⟩

/-- A marker that binds an immediate, when the immediate is already bound. -/
theorem matchExp_markPat_varBound {env : Env} {ρ : VarEnv} {op : MixopS} {l : IL.Id}
    {w : Value} (hl : ρ.findVal? l = some w) :
    MatchExp env ρ (markPat (.caseE op (.varE l))) (.list [.case op w]) ρ :=
  Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
    Validation.matchExp_case_iff.2 ⟨w, rfl, (matchExp_boundVar_iff hl).2 ⟨rfl, rfl⟩⟩⟩⟩

/-- A nullary marker, such as `RETURN` or `TRAP`. -/
theorem matchExp_markPat_nil {env : Env} {ρ : VarEnv} {op : MixopS} :
    MatchExp env ρ (markPat (.caseE op (.tupE []))) (.list [caseNilV op]) ρ :=
  Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
    matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩

/-- A marker fails definitely on a one-element list whose element is not that
injection. -/
theorem matchFails_markPat {env : Env} {ρ : VarEnv} {op : MixopS} {me : Exp} {w : Value}
    (h : ∀ u, w ≠ .case op u) : MatchFails env ρ (markPat (.caseE op me)) (.list [w]) :=
  matchFails_listE_one (matchFails_caseE h)

/-- The last element of a non-empty list, as the tail of a `drop`. -/
theorem drop_length_sub_one {us : List Value} (h : us ≠ []) :
    us.drop (us.length - 1) = [us[us.length - 1]'(by cases us <;> simp_all)] := by
  have hlen : 0 < us.length := by cases us <;> simp_all
  rw [List.drop_eq_getElem_cons (by omega)]
  have : us.length - 1 + 1 = us.length := by omega
  rw [this, List.drop_length]

/-- **`val* <marker>` fails definitely on a prefix that contains no marker.**
Either the prefix is empty — too short for the marker — or its last element
is not the marker. -/
theorem matchFails_valsMark {env : Env} {ρ : VarEnv} {x y : IL.Id} {op : MixopS}
    {me : Exp} {us : List Value} (hx : ρ.findVal? x = none) (hx' : x ≠ "_")
    (hy : ρ.findVal? y = none) (hnone : ∀ w ∈ us, ∀ u, w ≠ .case op u) :
    MatchFails env ρ (.catE (valsPat x y) (markPat (.caseE op me))) (.list us) := by
  refine matchFails_catE_ofRight (noPatLen_valsPat hy) patLen_markPat ?_
  by_cases hus : us = []
  · exact Or.inl (by simp [hus])
  · refine Or.inr (Or.inr ⟨ρ.bindVal y (.list (us.take (us.length - 1))), ?_, ?_⟩)
    · exact matchExp_valsPat_fresh hx hx' hy _
    · rw [drop_length_sub_one hus]
      exact matchFails_markPat (hnone _ (List.getElem_mem _))

/-- **`val'* val^n <marker>` fails definitely on a prefix that contains no
marker**, for the same two reasons plus a third: the prefix may be shorter
than the `^n` iteration needs. -/
theorem matchFails_valsValsNMark {env : Env} {ρ : VarEnv} {op : MixopS} {me : Exp}
    {nn : Nat} {us : List Value}
    (hval' : ρ.findVal? "val'" = none) (hvals' : ρ.findVal? "val'*" = none)
    (hval : ρ.findVal? "val" = none) (hvals : ρ.findVal? "val*" = none)
    (hn : ρ.findVal? "n" = some (.num (.natN nn)))
    (hnone : ∀ w ∈ us, ∀ u, w ≠ .case op u) :
    MatchFails env ρ
      (.catE (.catE (valsPat "val'" "val'*") (valsNPat "val" "val*" "n"))
        (markPat (.caseE op me))) (.list us) := by
  have hinner : NoPatLen env ρ (.catE (valsPat "val'" "val'*") (valsNPat "val" "val*" "n")) :=
    noPatLen_catE_left (noPatLen_valsPat hvals')
  refine matchFails_catE_ofRight hinner patLen_markPat ?_
  by_cases hus : us = []
  · exact Or.inl (by simp [hus])
  · set us' := us.take (us.length - 1) with hus'
    by_cases hlt : us'.length < nn
    · refine Or.inr (Or.inl ?_)
      refine matchFails_catE_ofRight (noPatLen_valsPat hvals')
        (patLen_iterE_listN_var hn) (Or.inl hlt)
    · refine Or.inr (Or.inr ⟨(ρ.bindVal "val'*" (.list (us'.take (us'.length - nn)))).bindVal
        "val*" (.list (us'.drop (us'.length - nn))), ?_, ?_⟩)
      · refine matchExp_catE_ofRight (noPatLen_valsPat hvals')
          (patLen_iterE_listN_var hn) (by omega)
          (matchExp_valsPat_fresh hval' (by decide) hvals' _) ?_
        refine matchExp_valsNPat (by simp [hval]) (by decide) (by simp [hvals]) ?_
        have : (us'.drop (us'.length - nn)).length = nn := by
          simp only [List.length_drop]; omega
        simp [this, hn]
      · rw [drop_length_sub_one hus]
        exact matchFails_markPat (hnone _ (List.getElem_mem _))

/-! ### The three concatenation shapes, matched

The reduction rules use three shapes: `val* M instr*` (four rules),
`val'* val^n M instr*` (two) and `val* (M instr*)` (`trap-instrs`).  Each is
matched by `matchExp_catE_ofSplit` at the first occurrence of the marker. -/

/-- Rewriting the list a split sees. -/
theorem take_append_of_le {ws : List Value} {w : Value} {is : List Value} {i : Nat}
    (hi : i ≤ ws.length) : (ws ++ w :: is).take i = ws.take i := by
  rw [List.take_append]
  simp [Nat.sub_eq_zero_of_le hi]


/-- The split the search finds: everything up to and including the marker. -/
theorem take_append_succ {ws : List Value} {w : Value} {is : List Value} :
    (ws ++ w :: is).take (ws.length + 1) = ws ++ [w] := by
  rw [List.take_append]
  simp

/-- …and what is left of it. -/
theorem drop_append_succ {ws : List Value} {w : Value} {is : List Value} :
    (ws ++ w :: is).drop (ws.length + 1) = is := by
  simp

/-- **`val* M instr*` against `ws M is`.**  The search passes over every
split inside `ws`, because no element of `ws` matches the marker, and stops
at the marker itself. -/
theorem matchExp_shapeA {env : Env} {ρ ρ' : VarEnv} {x y : IL.Id} {op : MixopS}
    {me : Exp} {ws is : List Value} {w : Value}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") (hy : ρ.findVal? y = none)
    (hinstrs : ρ.findVal? "instr*" = none)
    (hnone : ∀ u ∈ ws, ∀ q, u ≠ .case op q)
    (hmk : MatchExp env (ρ.bindVal y (.list ws)) (markPat (.caseE op me)) (.list [w]) ρ')
    (hi : ρ'.findVal? "instr" = none) (his : ρ'.findVal? "instr*" = none) :
    MatchExp env ρ
      (.catE (.catE (valsPat x y) (markPat (.caseE op me))) (iterPat "instr" "instr*"))
      (.list (ws ++ w :: is)) (ρ'.bindVal "instr*" (.list is)) := by
  refine matchExp_catE_ofSplit (k := ws.length + 1) (σ := ρ')
    (noPatLen_catE_left (noPatLen_valsPat hy)) (noPatLen_iterPat hinstrs)
    (by simp) (fun i hi' => ?_) ?_ ?_
  · refine splitFails_left ?_
    rw [take_append_of_le (by omega)]
    exact matchFails_valsMark hx hx' hy fun u hu => hnone u (List.mem_of_mem_take hu)
  · rw [take_append_succ]
    refine matchExp_catE_ofRight (σ := ρ.bindVal y (.list ws))
      (noPatLen_valsPat hy) patLen_markPat (by simp) ?_ ?_
    · simpa using matchExp_valsPat_fresh hx hx' hy ws
    · simpa using hmk
  · rw [drop_append_succ]
    exact matchExp_iterPat_fresh hi (by decide) his is

/-- **`val'* val^n M instr*` against `ws' ws M is`** with `ws` of length
`n`. -/
theorem matchExp_shapeB {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {me : Exp}
    {ws' ws is : List Value} {w : Value}
    (hval' : ρ.findVal? "val'" = none) (hvals' : ρ.findVal? "val'*" = none)
    (hval : ρ.findVal? "val" = none) (hvals : ρ.findVal? "val*" = none)
    (hn : ρ.findVal? "n" = some (.num (.natN ws.length)))
    (hinstrs : ρ.findVal? "instr*" = none)
    (hnone : ∀ u ∈ ws' ++ ws, ∀ q, u ≠ .case op q)
    (hmk : MatchExp env
      ((ρ.bindVal "val'*" (.list ws')).bindVal "val*" (.list ws))
      (markPat (.caseE op me)) (.list [w]) ρ')
    (hi : ρ'.findVal? "instr" = none) (his : ρ'.findVal? "instr*" = none) :
    MatchExp env ρ
      (.catE (.catE (.catE (valsPat "val'" "val'*") (valsNPat "val" "val*" "n"))
        (markPat (.caseE op me))) (iterPat "instr" "instr*"))
      (.list (ws' ++ ws ++ w :: is)) (ρ'.bindVal "instr*" (.list is)) := by
  refine matchExp_catE_ofSplit (k := (ws' ++ ws).length + 1) (σ := ρ')
    (noPatLen_catE_left (noPatLen_catE_left (noPatLen_valsPat hvals')))
    (noPatLen_iterPat hinstrs) (by simp; omega) (fun i hi' => ?_) ?_ ?_
  · refine splitFails_left ?_
    rw [take_append_of_le (by omega)]
    exact matchFails_valsValsNMark hval' hvals' hval hvals hn
      fun u hu => hnone u (List.mem_of_mem_take hu)
  · rw [take_append_succ]
    refine matchExp_catE_ofRight
      (σ := (ρ.bindVal "val'*" (.list ws')).bindVal "val*" (.list ws))
      (noPatLen_catE_left (noPatLen_valsPat hvals')) patLen_markPat (by simp; omega) ?_ ?_
    · have h1 : ((ws' ++ ws) ++ [w]).length - 1 = ws'.length + ws.length := by simp
      rw [h1]
      have h2 : ((ws' ++ ws) ++ [w]).take (ws'.length + ws.length) = ws' ++ ws := by
        simp [List.take_append]
      rw [h2]
      refine matchExp_catE_ofRight (σ := ρ.bindVal "val'*" (.list ws'))
        (noPatLen_valsPat hvals') (patLen_iterE_listN_var hn) (by simp) ?_ ?_
      · have h3 : (ws' ++ ws).take ((ws' ++ ws).length - ws.length) = ws' := by
          simp
        rw [h3]
        exact matchExp_valsPat_fresh hval' (by decide) hvals' ws'
      · have h4 : (ws' ++ ws).drop ((ws' ++ ws).length - ws.length) = ws := by
          simp
        rw [h4]
        refine matchExp_valsNPat (by simp [hval]) (by decide) (by simp [hvals]) ?_
        simpa using hn
    · have h1 : ((ws' ++ ws) ++ [w]).length - 1 = ws'.length + ws.length := by simp
      rw [h1]
      have h2 : ((ws' ++ ws) ++ [w]).drop (ws'.length + ws.length) = [w] := by
        simp [List.drop_append]
      rw [h2]
      exact hmk
  · rw [drop_append_succ]
    exact matchExp_iterPat_fresh hi (by decide) his is

/-- **`val* (M instr*)` against `ws M is`**: `trap-instrs`, whose left
component is parenthesised the other way. -/
theorem matchExp_shapeC {env : Env} {ρ : VarEnv} {x y : IL.Id} {op : MixopS}
    {ws is : List Value}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") (hy : ρ.findVal? y = none)
    (hinstr : (ρ.bindVal y (.list ws)).findVal? "instr" = none)
    (hinstrs0 : ρ.findVal? "instr*" = none)
    (hinstrs : (ρ.bindVal y (.list ws)).findVal? "instr*" = none)
    (hnone : ∀ u ∈ ws, ∀ q, u ≠ .case op q) :
    MatchExp env ρ
      (.catE (valsPat x y)
        (.catE (markPat (.caseE op (.tupE []))) (iterPat "instr" "instr*")))
      (.list (ws ++ caseNilV op :: is))
      ((ρ.bindVal y (.list ws)).bindVal "instr*" (.list is)) := by
  refine matchExp_catE_ofSplit (k := ws.length) (σ := ρ.bindVal y (.list ws))
    (noPatLen_valsPat hy)
    (noPatLen_catE_right patLen_markPat (noPatLen_iterPat hinstrs0))
    (by simp) (fun i hi' => ?_) ?_ ?_
  · refine splitFails_right (matchExp_valsPat_fresh hx hx' hy _) ?_
    refine matchFails_catE_ofLeft patLen_markPat (Or.inr (Or.inl ?_))
    have hd : (ws ++ caseNilV op :: is).drop i = ws.drop i ++ caseNilV op :: is := by
      rw [List.drop_append]
      simp [Nat.sub_eq_zero_of_le (show i ≤ ws.length by omega)]
    have hne : ws.drop i ≠ [] := by
      intro hc
      have := List.length_drop (l := ws) (i := i)
      rw [hc] at this
      simp at this
      omega
    obtain ⟨a, l, hal⟩ : ∃ a l, ws.drop i = a :: l := by
      cases hcc : ws.drop i with
      | nil => exact absurd hcc hne
      | cons a l => exact ⟨a, l, rfl⟩
    have htake : ((a :: l) ++ caseNilV op :: is).take 1 = [a] := by simp
    rw [hd, hal, htake]
    exact matchFails_markPat (hnone a (List.mem_of_mem_drop (by rw [hal]; simp)))
  · rw [List.take_append]
    simp only [List.take_length, Nat.sub_self, List.take_zero, List.append_nil]
    exact matchExp_valsPat_fresh hx hx' hy ws
  · rw [List.drop_append]
    simp only [List.drop_length, Nat.sub_self, List.drop_zero, List.nil_append]
    refine matchExp_catE_ofLeft (σ := ρ.bindVal y (.list ws)) patLen_markPat (by simp) ?_ ?_
    · simpa using matchExp_markPat_nil
    · simpa using matchExp_iterPat_fresh hinstr (by decide) hinstrs is


/-- `uN(N)`, `iN(N)`, `vN(N)` and every index type are one-case variants whose
mixop renders as `%` (`1.1:10-15,75-76,100-113`).  The `BR` rules need it
here; the bridge below uses it too. -/
def pctV (n : Nat) : Value := .case "%" (.tuple [.num (.natN n)])

/-! ### The right-hand sides, and the arithmetic of `br-label-succ`

Once the left component has matched, every variable a right component
mentions is bound, so `patLen` computes and no further search happens. -/

/-- A `val^n` whose domain is already bound tests instead of binding. -/
theorem matchExp_valsNPat_bound {env : Env} {ρ : VarEnv} {x y z : IL.Id}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") {vs : List Value}
    (hy : ρ.findVal? y = some (.list vs))
    (hz : ρ.findVal? z = some (.num (.natN vs.length))) :
    MatchExp env ρ (valsNPat x y z) (.list vs) ρ :=
  matchExp_iterE_listN_iff.2 ⟨vs, ρ, rfl, (matchExp_boundVar_iff hz).2 ⟨rfl, rfl⟩,
    (matchIterList_single_iff (bindsVar_subVar x _ _) hx hx').2
      ((matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩)⟩

/-- A plain `*` iteration whose domain is already bound tests instead of
binding. -/
theorem matchExp_iterPat_bound {env : Env} {ρ : VarEnv} {x y : IL.Id}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") {vs : List Value}
    (hy : ρ.findVal? y = some (.list vs)) :
    MatchExp env ρ (iterPat x y) (.list vs) ρ :=
  (matchExp_iterE_list_iff (bindsVar_varE x) hx hx').2
    ⟨vs, rfl, (matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩⟩

/-- `val* <marker>` with `val*` already bound: the left operand now *has* a
`patLen`, so `matchExp` splits without searching. -/
theorem matchExp_valsMarkBound {env : Env} {ρ : VarEnv} {x y : IL.Id} {me : Exp}
    {op : MixopS} {ws : List Value} {w : Value}
    (hx : ρ.findVal? x = none) (hx' : x ≠ "_") (hy : ρ.findVal? y = some (.list ws))
    (hmk : MatchExp env ρ (markPat (.caseE op me)) (.list [w]) ρ) :
    MatchExp env ρ (.catE (valsPat x y) (markPat (.caseE op me)))
      (.list (ws ++ [w])) ρ := by
  obtain ⟨m, hm⟩ := patLen_valsPat_bound (env := env) hx' hy
  refine matchExp_catE_ofLeft (σ := ρ) hm (by simp) ?_ ?_
  · simpa using matchExp_valsPat_bound hx hx' hy
  · simpa using hmk

/-- `val^n instr'*` with everything bound: the right-hand side of
`br-label-zero`. -/
theorem matchExp_valsNIterBound {env : Env} {ρ : VarEnv} {ws cont : List Value}
    (hval : ρ.findVal? "val" = none) (hvals : ρ.findVal? "val*" = some (.list ws))
    (hn : ρ.findVal? "n" = some (.num (.natN ws.length)))
    (hi : ρ.findVal? "instr'" = none)
    (his : ρ.findVal? "instr'*" = some (.list cont)) :
    MatchExp env ρ (.catE (valsNPat "val" "val*" "n") (iterPat "instr'" "instr'*"))
      (.list (ws ++ cont)) ρ := by
  refine matchExp_catE_ofLeft (σ := ρ) (patLen_iterE_listN_var hn) (by simp) ?_ ?_
  · simpa using matchExp_valsNPat_bound hval (by decide) hvals hn
  · simpa using matchExp_iterPat_bound hi (by decide) his

/-- A `CvtE` *pattern* converts the matched numeral back along its **source**
type and matches the operand against the result (`Sem/Eval.lean`'s `CvtE`
clause of `matchExp`, `eval.ml:905-909`). -/
theorem matchExp_cvtE_num {env : Env} {ρ ρ' : VarEnv} {e : Exp} {t₁ t₂ : NumTyp}
    {m m' : Num} (hc : Num.cvt t₁ m = some m')
    (h : MatchExp env ρ e (.num m') ρ') : MatchExp env ρ (.cvtE e t₁ t₂) (.num m) ρ' := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by simp [matchExp, hc, hn, Res.ofOption, Bind.bind, Except.bind]⟩

/-- An arithmetic expression is not a pattern: `matchExp` evaluates it and
compares (`matchDefault`, `eval.ml:885`). -/
theorem matchExp_binE_of_eval {env : Env} {ρ : VarEnv} {op : BinOp} {t : OpTyp}
    {e₁ e₂ : Exp} {v : Value} (h : EvalExp env ρ (.binE op t e₁ e₂) v) :
    MatchExp env ρ (.binE op t e₁ e₂) v ρ := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 2, by simp [matchExp, matchDefault, hn, Bind.bind, Except.bind, Res.assert]⟩

/-- **`BR (l - 1)`, as `br-label-succ` writes it.**  The elaborated index is
`$(l!%.0 - 1 : int)` coerced back to `nat`, and `matchExp` undoes the outer
coercion with `Num.cvt` and then *evaluates* the subtraction. -/
theorem matchExp_brSucc {env : Env} {ρ : VarEnv} {j : Nat} (hj : 0 < j)
    (hl : ρ.findVal? "l" = some (pctV j)) :
    MatchExp env ρ
      (markPat (.caseE "BR" (.caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
        (.cvtE (.projE (.uncaseE (.varE "l") "%") 0) .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT]))))
      (.list [brV (pctV (j - 1))]) ρ := by
  refine Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl, ?_⟩⟩
  refine Validation.matchExp_case_iff.2 ⟨_, rfl, ?_⟩
  refine Validation.matchExp_case_iff.2 ⟨_, rfl, ?_⟩
  refine Validation.matchExp_tup_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl, ?_⟩⟩
  refine matchExp_cvtE_num (m' := .intN ((j - 1 : Nat) : Int)) rfl ?_
  refine matchExp_binE_of_eval (evalExp_binE_iff.2 ⟨.num (.intN (j : Int)), ?_, Or.inr ⟨rfl, ?_⟩⟩)
  · exact evalExp_cvtE_iff.2 ⟨.natN j, .intN (j : Int),
      (evalExp_imm_iff hl).2 ⟨[], rfl⟩, rfl, rfl⟩
  · refine ⟨.num (.intN ((1 : Nat) : Int)), evalExp_cvtE_iff.2 ⟨.natN 1, .intN ((1 : Nat) : Int),
      evalExp_numE_iff.2 rfl, rfl, rfl⟩, ?_⟩
    have harith : ((j : Int) - 1) = ((j - 1 : Nat) : Int) := by omega
    simp [binValues, Num.bin, harith]

/-- The side condition `l!%.0 > 0` of `br-label-succ` (`4.3:106`). -/
theorem premsHold_immGt {env : Env} {ρ : VarEnv} {x : IL.Id} {j : Nat} (hj : 0 < j)
    (hx : ρ.findVal? x = some (pctV j)) :
    PremsHold env ρ
      [.ifPr (.cmpE .gtOp (.numT .natT) (.projE (.uncaseE (.varE x) "%") 0)
        (.numE (.natN 0)))] ρ :=
  Validation.premsHold_cons_iff.2 ⟨ρ, Validation.premHolds_if_iff.2 ⟨rfl,
    evalExp_cmpE_iff.2 ⟨.num (.natN j), .num (.natN 0), (evalExp_imm_iff hx).2 ⟨[], rfl⟩,
      evalExp_numE_iff.2 rfl, by simp [cmpValues, Num.cmp, hj]⟩⟩,
    Validation.premsHold_nil_iff.2 rfl⟩

/-- The left component of every `LABEL_`, `HANDLER_` and `FRAME_` rule: a
one-element instruction sequence holding a three-component injection. -/
theorem matchExp_list_case3 {env : Env} {ρ σ τ ρ' : VarEnv} {op : MixopS}
    {e₀ e₁ e₂ : Exp} {a b c : Value}
    (h₀ : MatchExp env ρ e₀ a σ) (h₁ : MatchExp env σ e₁ b τ)
    (h₂ : MatchExp env τ e₂ c ρ') :
    MatchExp env ρ (.listE [.caseE op (.tupE [e₀, e₁, e₂])])
      (.list [.case op (.tuple [a, b, c])]) ρ' :=
  Validation.matchExp_list_iff.2 ⟨_, rfl, matchExps_one_iff.2 ⟨_, rfl,
    Validation.matchExp_case_iff.2 ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_three_iff.2 ⟨a, b, c, σ, τ, rfl, h₀, h₁, h₂⟩⟩⟩⟩⟩

/-! ### The seven rules, firing -/

/-- **`Step_pure/br-handler` (`4.3:109-110`) fires.**
`(HANDLER_ n {catch*} (val* (BR l) instr*)) ~> val* (BR l)`, for an
arbitrary arity, catch-clause list, label index and trailing code, provided
no element of `val*` is itself a `BR` — which is what makes the first split
the intended one. -/
theorem ruleFires_brHandler {env : Env} {n l : Value} {cs ws is : List Value}
    (hws : ∀ u ∈ ws, ∀ q, u ≠ .case "BR" q) :
    RuleFires env "%~>%" [] []
      (stepV [handlerV n cs (ws ++ brV l :: is)] (ws ++ [brV l])) brHandlerRule := by
  unfold brHandlerRule
  rw [ruleFires_nil_iff]
  simp only [stepV, handlerV, brV]
  exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
    matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
      (matchExp_iterPat_fresh (by simp) (by decide) (by simp) cs)
      (matchExp_shapeA (by simp) (by decide) (by simp) (by simp) hws
        (matchExp_markPat_var (by simp) l) (by simp) (by simp)),
    matchExp_valsMarkBound (by simp) (by decide) (by simp)
      (matchExp_markPat_varBound (by simp))⟩, premsHold_nil⟩

/-- **`Step_pure/return-handler` (`4.3:236-237`) fires.**
`(HANDLER_ n {catch*} (val* RETURN instr*)) ~> val* RETURN`. -/
theorem ruleFires_returnHandler {env : Env} {n : Value} {cs ws is : List Value}
    (hws : ∀ u ∈ ws, ∀ q, u ≠ .case "RETURN" q) :
    RuleFires env "%~>%" [] []
      (stepV [handlerV n cs (ws ++ returnV :: is)] (ws ++ [returnV]))
      returnHandlerRule := by
  unfold returnHandlerRule
  rw [ruleFires_nil_iff]
  simp only [stepV, handlerV, returnV, caseNilV]
  exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
    matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
      (matchExp_iterPat_fresh (by simp) (by decide) (by simp) cs)
      (matchExp_shapeA (by simp) (by decide) (by simp) (by simp) hws
        matchExp_markPat_nil (by simp) (by simp)),
    matchExp_valsMarkBound (by simp) (by decide) (by simp) matchExp_markPat_nil⟩,
    premsHold_nil⟩

/-- **`Step_pure/return-label` (`4.3:233-234`) fires.**
`(LABEL_ n {instr'*} (val* RETURN instr*)) ~> val* RETURN`. -/
theorem ruleFires_returnLabel {env : Env} {n : Value} {cont ws is : List Value}
    (hws : ∀ u ∈ ws, ∀ q, u ≠ .case "RETURN" q) :
    RuleFires env "%~>%" [] []
      (stepV [labelV n cont (ws ++ returnV :: is)] (ws ++ [returnV]))
      returnLabelRule := by
  unfold returnLabelRule
  rw [ruleFires_nil_iff]
  simp only [stepV, labelV, returnV, caseNilV]
  exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
    matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
      (matchExp_iterPat_fresh (by simp) (by decide) (by simp) cont)
      (matchExp_shapeA (by simp) (by decide) (by simp) (by simp) hws
        matchExp_markPat_nil (by simp) (by simp)),
    matchExp_valsMarkBound (by simp) (by decide) (by simp) matchExp_markPat_nil⟩,
    premsHold_nil⟩

/-- **`Step_pure/br-label-succ` (`4.3:105-107`) fires.**
`(LABEL_ n {instr'*} (val* (BR l+1) instr*)) ~> val* (BR l)`; the index is
decremented by the elaborated `nat`-`int`-`nat` round trip. -/
theorem ruleFires_brLabelSucc {env : Env} {n : Value} {cont ws is : List Value}
    {j : Nat} (hj : 0 < j) (hws : ∀ u ∈ ws, ∀ q, u ≠ .case "BR" q) :
    RuleFires env "%~>%" [] []
      (stepV [labelV n cont (ws ++ brV (pctV j) :: is)] (ws ++ [brV (pctV (j - 1))]))
      brLabelSuccRule := by
  unfold brLabelSuccRule
  rw [ruleFires_nil_iff]
  simp only [stepV, labelV, brV]
  exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
    matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
      (matchExp_iterPat_fresh (by simp) (by decide) (by simp) cont)
      (matchExp_shapeA (by simp) (by decide) (by simp) (by simp) hws
        (matchExp_markPat_var (by simp) (pctV j)) (by simp) (by simp)),
    matchExp_valsMarkBound (by simp) (by decide) (by simp)
      (matchExp_brSucc hj (by simp))⟩, premsHold_immGt hj (by simp)⟩

/-- **`Step_pure/br-label-zero` (`4.3:101-103`) fires.**
`(LABEL_ n {instr'*} (val'* val^n (BR 0) instr*)) ~> val^n instr'*`.  The
arity is forced: the `^n` iteration reads it back off the matched list. -/
theorem ruleFires_brLabelZero {env : Env} {cont ws' ws is : List Value}
    (hws : ∀ u ∈ ws' ++ ws, ∀ q, u ≠ .case "BR" q) :
    RuleFires env "%~>%" [] []
      (stepV [labelV (.num (.natN ws.length)) cont (ws' ++ ws ++ brV (pctV 0) :: is)]
        (ws ++ cont)) brLabelZeroRule := by
  unfold brLabelZeroRule
  rw [ruleFires_nil_iff]
  simp only [stepV, labelV, brV]
  exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
    matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
      (matchExp_iterPat_fresh (by simp) (by decide) (by simp) cont)
      (matchExp_shapeB (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hws
        (matchExp_markPat_var (by simp) (pctV 0)) (by simp) (by simp)),
    matchExp_valsNIterBound (by simp) (by simp) (by simp) (by simp) (by simp)⟩,
    (premsHold_immEq_iff (c := pctV 0) (by simp)).2 ⟨rfl, [], rfl⟩⟩

/-- **`Step_pure/return-frame` (`4.3:230-231`) fires.**
`(FRAME_ n {f} (val'* val^n RETURN instr*)) ~> val^n`. -/
theorem ruleFires_returnFrame {env : Env} {f : Value} {ws' ws is : List Value}
    (hws : ∀ u ∈ ws' ++ ws, ∀ q, u ≠ .case "RETURN" q) :
    RuleFires env "%~>%" [] []
      (stepV [frameV (.num (.natN ws.length)) f (ws' ++ ws ++ returnV :: is)] ws)
      returnFrameRule := by
  unfold returnFrameRule
  rw [ruleFires_nil_iff]
  simp only [stepV, frameV, returnV, caseNilV]
  exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
    matchExp_list_case3 ((matchExp_freshVar_iff (by simp)).2 rfl)
      ((matchExp_freshVar_iff (by simp)).2 rfl)
      (matchExp_shapeB (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hws
        matchExp_markPat_nil (by simp) (by simp)),
    matchExp_valsNPat_bound (by simp) (by decide) (by simp) (by simp)⟩, premsHold_nil⟩

/-- **`Step_pure/trap-instrs` (`4.3:300-302`) fires.**
`val* TRAP instr* ~> TRAP` whenever there is something to discard, provided
no element of `val*` is itself a `TRAP`. -/
theorem ruleFires_trapInstrs {env : Env} {ws is : List Value}
    (hws : ∀ u ∈ ws, ∀ q, u ≠ .case "TRAP" q) (hne : ws ≠ [] ∨ is ≠ []) :
    RuleFires env "%~>%" [] [] (stepV (ws ++ trapV :: is) [trapV]) trapInstrsRule := by
  unfold trapInstrsRule
  rw [ruleFires_nil_iff]
  simp only [stepV, trapV, caseNilV]
  refine ⟨(VarEnv.empty.bindVal "val*" (Value.list ws)).bindVal "instr*" (Value.list is),
    (VarEnv.empty.bindVal "val*" (Value.list ws)).bindVal "instr*" (Value.list is),
    matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_shapeC (x := "val") (y := "val*") (by simp) (by decide) (by simp)
        (by simp) (by simp) (by simp) hws,
      matchExp_markPat_nil⟩, ?_⟩
  refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
    Validation.premsHold_nil_iff.2 rfl⟩
  have hvals : EvalExp env
      ((VarEnv.empty.bindVal "val*" (Value.list ws)).bindVal "instr*" (Value.list is))
      (iterPat "val" "val*") (.list ws) :=
    evalExp_iterPat (by decide) (by simp)
  have hinstrs : EvalExp env
      ((VarEnv.empty.bindVal "val*" (Value.list ws)).bindVal "instr*" (Value.list is))
      (iterPat "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) (by simp)
  have hnil : ∀ (σ : VarEnv), EvalExp env σ (.listE []) (.list []) :=
    fun σ => evalExp_listE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩
  by_cases hw : ws = []
  · subst hw
    have his : is ≠ [] := by
      rcases hne with h | h
      · exact absurd rfl h
      · exact h
    refine evalExp_binE_iff.2 ⟨.bool false, ?_, Or.inr ⟨rfl, .bool true, ?_, ?_⟩⟩
    · exact evalExp_cmpE_iff.2 ⟨.list [], .list [], hvals, hnil _, by simp [cmpValues]⟩
    · exact evalExp_cmpE_iff.2 ⟨.list is, .list [], hinstrs, hnil _,
        by simp [cmpValues, his]⟩
    · simp [binValues, boolBin]
  · refine evalExp_binE_iff.2 ⟨.bool true, ?_, Or.inl rfl⟩
    exact evalExp_cmpE_iff.2 ⟨.list ws, .list [], hvals, hnil _, by simp [cmpValues, hw]⟩

/-! ## The bridge to Silmaril's `Admin`

`Silmaril/Wasm/Execution/Core/Runtime.lean`'s `Admin` is `instr` extended with
the administrative forms of `4.0-execution.configurations.spectec`.  The
encoder below is **partial** and covers exactly the instructions the rules
above mention, plus every reference value; everything else — floats
(`fN(N)` is `POS/NEG fNmag(N)`, not a bit pattern), memory, table, GC and
vector instructions, calls, and the three administrative forms that carry an
unbridged component (`LABEL_`'s continuation, `FRAME_`'s frame, `HANDLER_`'s
catch clauses) — is `none`.  Partiality is the honest option here: a total
encoder would need a bridge for `blocktype`, `moduleinst` and `catch`, which
this file does not build. -/

/-- `numtype` restricted to the integer types. -/
def intTypeV : Wasm.IntType → Value
  | .i32 => i32V
  | .i64 => caseNilV "I64"

/-- `ref` (`4.0:35-43`). -/
def refV : Wasm.Execution.Core.Ref → Value
  | .i31 b => .case "REF.I31_NUM" (pctV b.toNat)
  | .null => caseNilV "REF.NULL_ADDR"
  | .struct a => .case "REF.STRUCT_ADDR" (.num (.natN a))
  | .array a => .case "REF.ARRAY_ADDR" (.num (.natN a))
  | .func a => .case "REF.FUNC_ADDR" (.num (.natN a))
  | .exn a => .case "REF.EXN_ADDR" (.num (.natN a))
  | .host a => .case "REF.HOST_ADDR" (.num (.natN a))
  | .extern r => .case "REF.EXTERN" (refV r)

/-- The source instructions this file bridges. -/
def instrV? : Wasm.Instr → Option Value
  | .nop => some nopV
  | .unreachable => some unreachableV
  | .drop => some dropV
  | .select none => some (selectV (.opt none))
  | .br l => some (brV (pctV l.toNat))
  | .brIf l => some (brIfV (pctV l.toNat))
  | .localTee x => some (localTeeV (pctV x.toNat))
  | .localSet x => some (localSetV (pctV x.toNat))
  | .intConst t b => some (constV (intTypeV t) (pctV b.toNat))
  | .vecConst b => some (.case "VCONST" (.tuple [caseNilV "V128", pctV b.toNat]))
  | _ => none

/-- One administrative instruction. -/
def adminV? : Wasm.Execution.Core.Admin → Option Value
  | .plain i => instrV? i
  | .ref r => some (refV r)
  | .trap => some trapV
  | _ => none

/-- A sequence of administrative instructions. -/
def adminsV? : List Wasm.Execution.Core.Admin → Option (List Value)
  | [] => some []
  | a :: tl => do
      let w ← adminV? a
      let ws ← adminsV? tl
      some (w :: ws)

/-- `v` is the SpecTec image of the Silmaril reduction step `is ~> js`. -/
def StepImage (is js : List Wasm.Execution.Core.Admin) (v : Value) : Prop :=
  ∃ ws ws', adminsV? is = some ws ∧ adminsV? js = some ws' ∧ v = stepV ws ws'

/-! ### Silmaril's steps, inside SpecTec

Each theorem below turns a Silmaril reduction into a `Step_pure` derivation.
They are unconditional: `derives` over-approximates the relation a `RelD`
denotes (`Equiv/Validation.lean`'s finding), so this is the direction that is
safe.  The converse holds for `nop` and `unreachable`, where the rule's
firing set is exactly the image of one Silmaril step; the next section says
why it fails for the rest. -/

/-- A non-zero bit pattern encodes to a non-zero numeral. -/
theorem num_toNat_ne_zero {n : Nat} {c : BitVec n} (hc : c ≠ 0) :
    (Value.num (.natN c.toNat)) ≠ Value.num (.natN 0) := by
  simp only [ne_eq, Value.num.injEq, Num.natN.injEq]
  intro hz
  exact hc (by simpa using BitVec.eq_of_toNat_eq (by simpa using hz))

/-- The image of `[NOP] ~> eps`. -/
theorem stepImage_nop {v : Value} :
    StepImage [.plain .nop] [] v ↔ v = stepV [nopV] [] := by
  simp [StepImage, adminsV?, adminV?, instrV?, eq_comm]

/-- The image of `[UNREACHABLE] ~> [TRAP]`. -/
theorem stepImage_unreachable {v : Value} :
    StepImage [.plain .unreachable] [.trap] v ↔ v = stepV [unreachableV] [trapV] := by
  simp [StepImage, adminsV?, adminV?, instrV?, eq_comm]

/-- The image of `val DROP ~> eps`. -/
theorem stepImage_drop {u : Wasm.Execution.Core.Val} {w v : Value}
    (hu : adminV? u.toAdmin = some w) :
    StepImage [u.toAdmin, .plain .drop] [] v ↔ v = stepV [w, dropV] [] := by
  simp only [StepImage, adminsV?, hu]
  simp [adminV?, instrV?, eq_comm]

/-- The image of `val (LOCAL.TEE x) ~> val val (LOCAL.SET x)`. -/
theorem stepImage_localTee {u : Wasm.Execution.Core.Val} {w v : Value} {x : Wasm.LocalIdx}
    (hu : adminV? u.toAdmin = some w) :
    StepImage [u.toAdmin, .plain (.localTee x)] [u.toAdmin, u.toAdmin, .plain (.localSet x)] v ↔
      v = stepV [w, localTeeV (pctV x.toNat)] [w, w, localSetV (pctV x.toNat)] := by
  simp only [StepImage, adminsV?, hu]
  simp [adminV?, instrV?, eq_comm]

/-- The image of `(CONST I32 c) (BR_IF l) ~> (BR l)`. -/
theorem stepImage_brIf {c : BitVec 32} {l : Wasm.LabelIdx} {v : Value} :
    StepImage [Wasm.Execution.Core.constI32 c, .plain (.brIf l)] [.plain (.br l)] v ↔
      v = stepV [constV i32V (pctV c.toNat), brIfV (pctV l.toNat)] [brV (pctV l.toNat)] := by
  simp [StepImage, adminsV?, adminV?, instrV?, Wasm.Execution.Core.constI32,
    Wasm.Execution.Core.Val.toAdmin, Wasm.Execution.Core.Val.i32, intTypeV, eq_comm]
  rfl

/-- The image of `(CONST I32 c) (BR_IF l) ~> eps`. -/
theorem stepImage_brIfNil {c : BitVec 32} {l : Wasm.LabelIdx} {v : Value} :
    StepImage [Wasm.Execution.Core.constI32 c, .plain (.brIf l)] [] v ↔
      v = stepV [constV i32V (pctV c.toNat), brIfV (pctV l.toNat)] [] := by
  simp [StepImage, adminsV?, adminV?, instrV?, Wasm.Execution.Core.constI32,
    Wasm.Execution.Core.Val.toAdmin, Wasm.Execution.Core.Val.i32, intTypeV, eq_comm]
  rfl

/-- The image of `val_1 val_2 (CONST I32 c) (SELECT) ~> val_i`. -/
theorem stepImage_select {u₁ u₂ u : Wasm.Execution.Core.Val} {w₁ w₂ w v : Value}
    {c : BitVec 32} (h₁ : adminV? u₁.toAdmin = some w₁) (h₂ : adminV? u₂.toAdmin = some w₂)
    (h : adminV? u.toAdmin = some w) :
    StepImage [u₁.toAdmin, u₂.toAdmin, Wasm.Execution.Core.constI32 c,
        .plain (.select none)] [u.toAdmin] v ↔
      v = stepV [w₁, w₂, constV i32V (pctV c.toNat), selectV (.opt none)] [w] := by
  simp only [StepImage, adminsV?, h₁, h₂, h]
  simp [adminV?, instrV?, Wasm.Execution.Core.constI32,
    Wasm.Execution.Core.Val.toAdmin, Wasm.Execution.Core.Val.i32, intTypeV, eq_comm]
  rfl

/-! #### The derivations -/

/-- **`Step_pure/nop` *is* `ParametricStep.nop`**, in both directions. -/
theorem ruleFires_nop_iff_image {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v nopRule ↔ StepImage [.plain .nop] [] v := by
  rw [ruleFires_nop_iff, stepImage_nop]

/-- **`Step_pure/unreachable` *is* `ParametricStep.unreachable`**, in both
directions.  This is the trapping step that *does* agree exactly. -/
theorem ruleFires_unreachable_iff_image {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v unreachableRule ↔
      StepImage [.plain .unreachable] [.trap] v := by
  rw [ruleFires_unreachable_iff, stepImage_unreachable]

/-- `ParametricStep.nop` is a `Step_pure` derivation. -/
theorem derives_nop {env : Env} (h : HasStepRules env) {v : Value}
    (hv : StepImage [.plain .nop] [] v) : Derives env "Step_pure" "%~>%" [] v :=
  derives_of_ruleAt h.nop (ruleFires_nop_iff.2 (stepImage_nop.1 hv))

/-- `ParametricStep.unreachable` is a `Step_pure` derivation. -/
theorem derives_unreachable {env : Env} (h : HasStepRules env) {v : Value}
    (hv : StepImage [.plain .unreachable] [.trap] v) :
    Derives env "Step_pure" "%~>%" [] v :=
  derives_of_ruleAt h.unreachable (ruleFires_unreachable_iff.2 (stepImage_unreachable.1 hv))

/-- `ParametricStep.drop` is a `Step_pure` derivation. -/
theorem derives_drop {env : Env} (h : HasStepRules env) {u : Wasm.Execution.Core.Val}
    {w v : Value} (hu : adminV? u.toAdmin = some w)
    (hv : StepImage [u.toAdmin, .plain .drop] [] v) : Derives env "Step_pure" "%~>%" [] v :=
  derives_of_ruleAt h.drop (ruleFires_drop_iff.2 ⟨w, (stepImage_drop hu).1 hv⟩)

/-- `VariableStep.localTee` is a `Step_pure` derivation. -/
theorem derives_localTee {env : Env} (h : HasStepRules env) {u : Wasm.Execution.Core.Val}
    {w v : Value} {x : Wasm.LocalIdx} (hu : adminV? u.toAdmin = some w)
    (hv : StepImage [u.toAdmin, .plain (.localTee x)]
      [u.toAdmin, u.toAdmin, .plain (.localSet x)] v) :
    Derives env "Step_pure" "%~>%" [] v :=
  derives_of_ruleAt h.localTee
    (ruleFires_localTee_iff.2 ⟨w, pctV x.toNat, (stepImage_localTee hu).1 hv⟩)

/-- `Step.brIfTrue` is a `Step_pure` derivation. -/
theorem derives_brIfTrue {env : Env} (h : HasStepRules env) {c : BitVec 32}
    {l : Wasm.LabelIdx} {v : Value} (hc : c ≠ 0)
    (hv : StepImage [Wasm.Execution.Core.constI32 c, .plain (.brIf l)] [.plain (.br l)] v) :
    Derives env "Step_pure" "%~>%" [] v :=
  derives_of_ruleAt h.brIfTrue (ruleFires_brIfTrue_iff.2
    ⟨.num (.natN c.toNat), [], pctV l.toNat, stepImage_brIf.1 hv, num_toNat_ne_zero hc⟩)

/-- `Step.brIfFalse` is a `Step_pure` derivation. -/
theorem derives_brIfFalse {env : Env} (h : HasStepRules env) {l : Wasm.LabelIdx} {v : Value}
    (hv : StepImage [Wasm.Execution.Core.constI32 0, .plain (.brIf l)] [] v) :
    Derives env "Step_pure" "%~>%" [] v :=
  derives_of_ruleAt h.brIfFalse
    (ruleFires_brIfFalse_iff.2 ⟨[], pctV l.toNat, by simpa [pctV] using stepImage_brIfNil.1 hv⟩)

/-- `ParametricStep.selectTrue` is a `Step_pure` derivation. -/
theorem derives_selectTrue {env : Env} (h : HasStepRules env)
    {u₁ u₂ : Wasm.Execution.Core.Val} {w₁ w₂ v : Value} {c : BitVec 32} (hc : c ≠ 0)
    (h₁ : adminV? u₁.toAdmin = some w₁) (h₂ : adminV? u₂.toAdmin = some w₂)
    (hv : StepImage [u₁.toAdmin, u₂.toAdmin, Wasm.Execution.Core.constI32 c,
      .plain (.select none)] [u₁.toAdmin] v) :
    Derives env "Step_pure" "%~>%" [] v :=
  derives_of_ruleAt h.selectTrue (ruleFires_selectTrue_iff.2
    ⟨w₁, w₂, .num (.natN c.toNat), [], .opt none,
      (stepImage_select h₁ h₂ h₁).1 hv, num_toNat_ne_zero hc, Or.inl rfl⟩)

/-- `ParametricStep.selectFalse` is a `Step_pure` derivation. -/
theorem derives_selectFalse {env : Env} (h : HasStepRules env)
    {u₁ u₂ : Wasm.Execution.Core.Val} {w₁ w₂ v : Value}
    (h₁ : adminV? u₁.toAdmin = some w₁) (h₂ : adminV? u₂.toAdmin = some w₂)
    (hv : StepImage [u₁.toAdmin, u₂.toAdmin, Wasm.Execution.Core.constI32 0,
      .plain (.select none)] [u₂.toAdmin] v) :
    Derives env "Step_pure" "%~>%" [] v :=
  derives_of_ruleAt h.selectFalse (ruleFires_selectFalse_iff.2
    ⟨w₁, w₂, [], .opt none, by simpa [pctV] using (stepImage_select h₁ h₂ h₂).1 hv, Or.inl rfl⟩)

/-! #### The administrative steps

`LABEL_`'s continuation, `HANDLER_`'s catch clauses and `FRAME_`'s frame are
*not* bridged (`adminV?` is `none` there), so these are stated for an
arbitrary value in that position — which is strictly stronger than any
particular encoding of them, since the rules never look inside. -/

/-- `Step.trapLabel`, for every arity and continuation value. -/
theorem derives_trapLabel {env : Env} (h : HasStepRules env) (n : Value) (cs : List Value) :
    Derives env "Step_pure" "%~>%" [] (stepV [labelV n cs [trapV]] [trapV]) :=
  derives_of_ruleAt h.trapLabel (ruleFires_trapLabel_iff.2 ⟨n, cs, rfl⟩)

/-- `Step.trapHandler`, for every arity and catch-clause value. -/
theorem derives_trapHandler {env : Env} (h : HasStepRules env) (n : Value) (cs : List Value) :
    Derives env "Step_pure" "%~>%" [] (stepV [handlerV n cs [trapV]] [trapV]) :=
  derives_of_ruleAt h.trapHandler (ruleFires_trapHandler_iff.2 ⟨n, cs, rfl⟩)

/-- `Step.trapFrame`, for every arity and frame value. -/
theorem derives_trapFrame {env : Env} (h : HasStepRules env) (n f : Value) :
    Derives env "Step_pure" "%~>%" [] (stepV [frameV n f [trapV]] [trapV]) :=
  derives_of_ruleAt h.trapFrame (ruleFires_trapFrame_iff.2 ⟨n, f, rfl⟩)

/-- `Step.labelVals`, for every arity, continuation and body. -/
theorem derives_labelVals {env : Env} (h : HasStepRules env) (n : Value)
    (cs ws : List Value) :
    Derives env "Step_pure" "%~>%" [] (stepV [labelV n cs ws] ws) :=
  derives_of_ruleAt h.labelVals (ruleFires_labelVals_iff.2 ⟨n, cs, ws, rfl⟩)

/-- `Step.handlerVals`, for every arity, catch clauses and body. -/
theorem derives_handlerVals {env : Env} (h : HasStepRules env) (n : Value)
    (cs ws : List Value) :
    Derives env "Step_pure" "%~>%" [] (stepV [handlerV n cs ws] ws) :=
  derives_of_ruleAt h.handlerVals (ruleFires_handlerVals_iff.2 ⟨n, cs, ws, rfl⟩)

/-- `Step.frameVals`; the `^n` iteration *does* force the arity. -/
theorem derives_frameVals {env : Env} (h : HasStepRules env) (f : Value) (ws : List Value) :
    Derives env "Step_pure" "%~>%" []
      (stepV [frameV (.num (.natN ws.length)) f ws] ws) :=
  derives_of_ruleAt h.frameVals (ruleFires_frameVals_iff.2 ⟨f, ws, rfl⟩)

/-- `Step.ifTrue`, for every block type and pair of branch bodies. -/
theorem derives_ifTrue {env : Env} (h : HasStepRules env) {c : BitVec 32} (hc : c ≠ 0)
    (bt : Value) (is js : List Value) :
    Derives env "Step_pure" "%~>%" []
      (stepV [constV i32V (pctV c.toNat), ifV bt is js] [blockV bt is]) :=
  derives_of_ruleAt h.ifTrue (ruleFires_ifTrue_iff.2
    ⟨.num (.natN c.toNat), [], bt, is, js, rfl, num_toNat_ne_zero hc⟩)

/-- `Step.ifFalse`. -/
theorem derives_ifFalse {env : Env} (h : HasStepRules env) (bt : Value) (is js : List Value) :
    Derives env "Step_pure" "%~>%" []
      (stepV [constV i32V (pctV 0), ifV bt is js] [blockV bt js]) :=
  derives_of_ruleAt h.ifFalse (ruleFires_ifFalse_iff.2 ⟨[], bt, is, js, rfl⟩)

/-! ## The findings, as theorems

Three distinct gaps, each with a witness.  None of them is a defect of the
*specification*: all three are defects of `Sem/Eval.lean`'s denotation of a
`RelD`, which is where they should be repaired. -/

/-- Reading a cons apart. -/
theorem adminsV?_cons_iff {a : Wasm.Execution.Core.Admin}
    {tl : List Wasm.Execution.Core.Admin} {r : List Value} :
    adminsV? (a :: tl) = some r ↔
      ∃ w ws, adminV? a = some w ∧ adminsV? tl = some ws ∧ r = w :: ws := by
  have e : adminsV? (a :: tl) =
      (adminV? a).bind (fun w => (adminsV? tl).bind (fun ws => some (w :: ws))) := rfl
  constructor
  · intro h
    cases hw : adminV? a with
    | none => rw [e, hw] at h; simp at h
    | some w =>
        cases hws : adminsV? tl with
        | none => rw [e, hw, hws] at h; simp at h
        | some ws =>
            rw [e, hw, hws] at h
            simp only [Option.bind, Option.some.injEq] at h
            exact ⟨w, ws, rfl, rfl, h.symm⟩
  · rintro ⟨w, ws, hw, hws, rfl⟩
    rw [e, hw, hws]
    rfl

/-- `NOP` is not the encoding of any Wasm value. -/
theorem adminV?_toAdmin_ne_nop (u : Wasm.Execution.Core.Val) :
    adminV? u.toAdmin ≠ some nopV := by
  cases u with
  | num nv =>
      obtain ⟨t, b⟩ := nv
      cases t with
      | int t => simp [Wasm.Execution.Core.Val.toAdmin, adminV?, instrV?, nopV, constV, caseNilV]
      | float t => simp [Wasm.Execution.Core.Val.toAdmin, adminV?, instrV?]
  | vec b => simp [Wasm.Execution.Core.Val.toAdmin, adminV?, instrV?, nopV, caseNilV]
  | ref r =>
      cases r <;>
        simp [Wasm.Execution.Core.Val.toAdmin, adminV?, refV, nopV, caseNilV]

/-- Hence `[NOP]` is not the encoding of any Wasm value sequence. -/
theorem not_adminsV?_vals_nop (vs : List Wasm.Execution.Core.Val) :
    adminsV? (Wasm.Execution.Core.vals vs) ≠ some [nopV] := by
  cases vs with
  | nil => simp [Wasm.Execution.Core.vals, adminsV?]
  | cons u us =>
      intro h
      simp only [Wasm.Execution.Core.vals, List.map_cons] at h
      rw [adminsV?_cons_iff] at h
      obtain ⟨w, ws, hw, -, hr⟩ := h
      injection hr with hr _
      exact adminV?_toAdmin_ne_nop u (hw.trans (congrArg some hr.symm))

/-! ### The `CatE` search, and what it assumes

`matchExp`'s `CatE` clause splits the matched list at a length obtained from
`patLen`, which is defined for a `ListE`, for a `CatE` of two such, and for a
`^n` iteration whose counter is known — and otherwise *evaluates* the
pattern.  A `*` iteration over a domain the pattern is about to bind
evaluates to nothing, so a `CatE` of two of those has no length at all, and
every one of the seven structural rules is such a concatenation.

`Sem/Eval.lean` therefore **searches**: it tries the `n + 1` splits of the
matched list in increasing order and takes the first that matches.  That is
a deliberate strengthening of `spectec/src/il/eval.ml:923-932`, whose two
`CatE` clauses require one operand to be a literal `ListE` and which
consequently matches none of these rules either.  SpecTec does not execute a
rule through `il/eval.ml` — the frontend goes through `il2al`, whose
`translate.ml` gives `CatE` its own treatment — so the search is a choice
about *our* denotation, not a claim about the specification.

Being first-match, the search is still a function of its inputs, so
`MatchExp.unique` and every determinism result are untouched.  What it does
not give is a *characterisation*: the split it finds is the first one that
matches, and the seven theorems above therefore carry the hypothesis that no
value in front of the marker is itself a `BR`, a `RETURN` or a `TRAP`.  That
hypothesis holds of every genuine `val*` — no value is an administrative
instruction — and it is exactly the condition under which the
specification's own reading of `val* (BR l) instr*`, with `val*` a maximal
run of values, picks the same split.  A rule firing at a pair *outside* that
hypothesis is neither proved nor refuted here.

`ruleFires_trapInstrs_concrete` is the pair the old vacuity result used as
its witness; it now derives. -/

/-- A concrete pair `Step_pure/trap-instrs` derives:
`(CONST I32 0) TRAP ~> TRAP`. -/
theorem ruleFires_trapInstrs_concrete {env : Env} :
    RuleFires env "%~>%" [] [] (stepV [constV i32V (pctV 0), trapV] [trapV])
      trapInstrsRule := by
  have h := ruleFires_trapInstrs (env := env) (ws := [constV i32V (pctV 0)]) (is := [])
    (by
      intro u hu q
      simp only [List.mem_singleton] at hu
      subst hu
      simp [constV])
    (Or.inl (by simp))
  simpa using h

/-! ### Finding 1: the dropped quantifiers reach the reduction relation

`Equiv/Validation.lean` records that `anyRule` ignores a `RuleD`'s `quant
list` (`spectec/src/il/ast.ml:146,129,124`) and never consults
`Sem/Type.lean`'s `HasTyp`.  In the typing group that made the
well-formedness judgments trivial.  In the reduction group it is worse: the
quantifier `val* : val*` is the **only** thing that says a label body is a
sequence of *values*, so without it `Step_pure/label-vals` pops a label whose
body is arbitrary code. -/

/-- `Step_pure/label-vals` fires at a label whose arity is the *boolean*
`true` and whose body is `[NOP]`. -/
theorem ruleFires_labelVals_nonvalue {env : Env} :
    RuleFires env "%~>%" [] [] (stepV [labelV (.bool true) [] [nopV]] [nopV]) labelValsRule :=
  ruleFires_labelVals_iff.2 ⟨.bool true, [], [nopV], rfl⟩

/-- …and `not_adminsV?_vals_nop` says `[NOP]` is not the encoding of any
`vals vs`, so the *result* of that derivation is not a value sequence.
`Step.labelVals` pops exactly the label's value body, so no instance of it
has this pair as its image.  (The statement cannot be phrased with
`StepImage`, because `adminV?` does not bridge `LABEL_` at all; the content
is `not_adminsV?_vals_nop`.) -/
theorem ruleFires_labelVals_nonvalue_result (vs : List Wasm.Execution.Core.Val) :
    adminsV? (Wasm.Execution.Core.vals vs) ≠ some [nopV] :=
  not_adminsV?_vals_nop vs

/-- `Step_pure/drop` fires on `NOP`, which is not a value. -/
theorem ruleFires_drop_nonvalue {env : Env} :
    RuleFires env "%~>%" [] [] (stepV [nopV, dropV] []) dropRule :=
  ruleFires_drop_iff.2 ⟨nopV, rfl⟩

/-- …and that pair is not the image of any `ParametricStep.drop`. -/
theorem drop_not_image (u : Wasm.Execution.Core.Val) :
    ¬ StepImage [u.toAdmin, .plain .drop] [] (stepV [nopV, dropV] []) := by
  rintro ⟨ws, ws', h1, h2, hv⟩
  rw [adminsV?_cons_iff] at h1
  obtain ⟨w, ws₁, hw, h1, rfl⟩ := h1
  rw [adminsV?_cons_iff] at h1
  obtain ⟨d, ws₂, -, h1, rfl⟩ := h1
  simp only [adminsV?, Option.some.injEq] at h1
  subst h1
  simp only [stepV, Value.tuple.injEq, Value.list.injEq, List.cons.injEq] at hv
  exact adminV?_toAdmin_ne_nop u (hw.trans (congrArg some hv.1.1.symm))

/-! ### Finding 2: `c =/= 0` does not say `c` is a numeral

`SELECT`, `IF` and `BR_IF` branch on `c : num_(I32)` with the elaborated side
condition `c!%.0 =/= 0`, and `cmpValues` settles `=/=` by *structural
inequality of values* (`eval.ml:260-263`).  Nothing checks that the projected
component is a `nat`. -/

/-- `Step_pure/br_if-true` fires when the `I32` immediate is the boolean
`true`. -/
theorem ruleFires_brIfTrue_nonNumeral {env : Env} (l : Value) :
    RuleFires env "%~>%" [] []
      (stepV [constV i32V (.case "%" (.tuple [.bool true])), brIfV l] [brV l]) brIfTrueRule :=
  ruleFires_brIfTrue_iff.2 ⟨.bool true, [], l, rfl, by simp⟩

/-- `Step_pure/br_if-true` also fires when the label index is a `text`. -/
theorem ruleFires_brIfTrue_textLabel {env : Env} :
    RuleFires env "%~>%" [] []
      (stepV [constV i32V (pctV 1), brIfV (.text "l")] [brV (.text "l")]) brIfTrueRule :=
  ruleFires_brIfTrue_iff.2 ⟨.num (.natN 1), [], .text "l", rfl, by simp⟩

/-! ## What is not reached

Stated precisely, because the theorems above are deliberately narrow.

* **`Step`, `Step_read` and `Steps` (`4.3:5,7,8`).**  Untouched.  Their
  arguments are `config = state; instr*` with `state = store; frame`, and a
  bridge for `store` and `moduleinst` — thirteen and eight fields of
  instances — is not built here.  Everything that needs the store is
  therefore out of scope: `local.get`/`local.set`/`global.*` (`4.3:316-336`),
  `block` and `loop` (`4.3:77-83`, which read `$blocktype_`), all of
  `table.*`, `memory.*`, the loads and stores, every call, and `try_table`
  and the exception rules.  The task's priority-1 item "`local.get` /
  `local.set`" is `Step_read`/`Step`, not `Step_pure`, and is **not** proved.

* **`Step_pure` as a relation.**  Only 23 of its 79 rules are reached, and
  only as `RuleFires` characterisations: "`Derives env "Step_pure" … v`
  implies *this* Silmaril step" would have to rule out the other 56 rules at
  every value, which needs all 79 of them — 46 000 characters — as a Lean
  term.
  `derives_of_ruleAt` gives the other direction unconditionally, and that is
  what every `derives_*` theorem above uses.

* **The 56 rules not transcribed.**  `call_indirect`,
  `return_call_indirect`, the reference and `i31` rules, `array.new`,
  `extern.convert_any`/`any.convert_extern`, and the whole numeric and
  vector block (`unop-val`, `unop-trap`, `binop-val`, `binop-trap`,
  `testop`, `relop`, `cvtop-val`, `cvtop-trap`, and 25 vector rules).  The
  numeric ones are within reach of this file's machinery — their premises
  are a `MemE` or a `CmpE` against `$unop_`/`$binop_`/`$testop_`/`$relop_`
  — but relating them to `Silmaril/Wasm/Execution/Core/Step/Numeric.lean`
  needs `Equiv/Numerics.lean`'s function-level results, and nothing here
  does that.  **The trapping numeric steps `binop-trap` and `cvtop-trap`,
  which the task singles out, are not proved**; of the trapping rules
  `unreachable`, `trap-label`, `trap-handler`, `trap-frame` and
  `trap-instrs` are.

* **`block`, `loop` and `br_table`.**  `block` and `loop` are `Step_read`
  (they call `$blocktype_`), so they are out of scope above.  `br_table`
  (`4.3:122-128`) *is* `Step_pure` and is not transcribed: its conclusion
  indexes an iteration with `l*[i]`, which needs `matchDefault` and an
  `IdxE` evaluation lemma this file does not build.

* **The bridge is partial, and not proved injective.**  `adminV?` is `none`
  on floats (`fN(N)` is `POS/NEG fNmag(N)` — a structured magnitude, not a
  bit pattern, so a float bridge needs
  `Silmaril/Wasm/SpecTec/FloatBits.lean`), on annotated `select`, on
  `LABEL_`/`HANDLER_`/`FRAME_`, and on every instruction outside the list in
  `instrV?`.  `adminV?_toAdmin_ne_nop` is the only injectivity-flavoured
  fact proved; a general `adminV?`-injectivity, and a decoder with
  round-trip laws, are not.

* **Nothing here is a statement about `Sem/Type.lean`'s `HasTyp`.**  Finding
  1 says that is exactly what is missing from `anyRule`, and repairing it is
  upstream work.

* **The seven structural rules are fired, not characterised.**  Each
  `ruleFires_br*`/`ruleFires_return*`/`ruleFires_trapInstrs` is a
  construction at a pair whose `val*` prefix contains no marker, and none of
  them has a converse: "`Step_pure/br-handler` derives *exactly* these
  pairs" would have to invert `matchExp`'s first-match search over splits,
  and that inversion is not built.  Nor is any of the seven related to the
  corresponding Silmaril step: `adminV?` does not bridge `LABEL_`,
  `HANDLER_` or `FRAME_`, so there is no `StepImage` statement for them, and
  `derives_brHandler` and friends do not exist.

* **The search is ours, not the specification's.**  `matchExp`'s third
  `CatE` branch is strictly stronger than `spectec/src/il/eval.ml:923-932`.
  It says nothing about the WebAssembly specification, whose declarative
  reading of those rules is the intended one, and nothing about the
  reference interpreter, which does not use `il/eval.ml` to reduce.
-/


end Silmaril.SpecTec.Equiv.Execution
