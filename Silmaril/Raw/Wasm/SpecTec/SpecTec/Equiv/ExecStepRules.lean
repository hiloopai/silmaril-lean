module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecRead
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecReadControl
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecReadTable
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecReadAggregate
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Unbind
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `Step`, transcribed

All 36 rules of the top-level reduction relation `Step`, with their index in
the pinned stream, and the single `rfl` that ties the transcription to
`Silmaril.SpecTec.Specs.wasm30`.

`Step` is where the specification actually *writes*: every rule here either
lifts a read-only step (`pure`, `read`), propagates one through an
administrative context (`ctxt-instrs`, `ctxt-label`, `ctxt-handler`,
`ctxt-frame`), or updates the state (`local.set`, `global.set`, the `.set`,
`.store`, `.grow` and `.drop` families, and the aggregate allocators).  The
first two are already characterised in `Equiv/ExecStep.lean`; the rest are
the half of execution that `Step_read` cannot express.

`Equiv/ExecStep.lean`'s `ruleFires_stepPure_iff` and `ruleFires_stepRead_iff`
cover rules 0 and 1; `pureRule_eq` and `readRule_eq` below record that this
independently generated transcription agrees with the hand-written one there,
which is a check on the generator.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecStepRules

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution
open Silmaril.SpecTec.Equiv.Unbind

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## The 36 rules, as the pinned stream records them -/

/-- `Step/pure`, rule 0 of the pinned stream. -/
def pureRule : Rule :=
  (.ruleD "pure" [(.expP "z" (.varT "state" [])), (.expP "instr*" (.iterT (.varT "instr" []) .list)), (.expP "instr'*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))])), (.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))]) [(.rulePr "Step_pure" [] "%~>%" (.tupE [(.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))])

/-- `Step/read`, rule 1 of the pinned stream. -/
def readRule : Rule :=
  (.ruleD "read" [(.expP "z" (.varT "state" [])), (.expP "instr*" (.iterT (.varT "instr" []) .list)), (.expP "instr'*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))])), (.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))]) [(.rulePr "Step_read" [] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))])), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))])

/-- `Step/ctxt-instrs`, rule 2 of the pinned stream. -/
def ctxtInstrsRule : Rule :=
  (.ruleD "ctxt-instrs" [(.expP "z" (.varT "state" [])), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "instr*" (.iterT (.varT "instr" []) .list)), (.expP "instr_1*" (.iterT (.varT "instr" []) .list)), (.expP "z'" (.varT "state" [])), (.expP "instr'*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.catE (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])) (.iterE (.varE "instr_1") (.mk .list [(.mk "instr_1" (.varE "instr_1*"))]))))])), (.caseE "%;%" (.tupE [(.varE "z'"), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.catE (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))])) (.iterE (.varE "instr_1") (.mk .list [(.mk "instr_1" (.varE "instr_1*"))]))))]))]) [(.rulePr "Step" [] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))])), (.caseE "%;%" (.tupE [(.varE "z'"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))])), (.ifPr (.binE .orOp .boolT (.cmpE .neOp .boolT (.iterE (.varE "val") (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [])) (.cmpE .neOp .boolT (.iterE (.varE "instr_1") (.mk .list [(.mk "instr_1" (.varE "instr_1*"))])) (.listE []))))])

/-- `Step/ctxt-label`, rule 3 of the pinned stream. -/
def ctxtLabelRule : Rule :=
  (.ruleD "ctxt-label" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])), (.expP "instr_0*" (.iterT (.varT "instr" []) .list)), (.expP "instr*" (.iterT (.varT "instr" []) .list)), (.expP "z'" (.varT "state" [])), (.expP "instr'*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "LABEL_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "instr_0") (.mk .list [(.mk "instr_0" (.varE "instr_0*"))])), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))]))])])), (.caseE "%;%" (.tupE [(.varE "z'"), (.listE [(.caseE "LABEL_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "instr_0") (.mk .list [(.mk "instr_0" (.varE "instr_0*"))])), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))])]))]) [(.rulePr "Step" [] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))])), (.caseE "%;%" (.tupE [(.varE "z'"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))]))])

/-- `Step/ctxt-handler`, rule 4 of the pinned stream. -/
def ctxtHandlerRule : Rule :=
  (.ruleD "ctxt-handler" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])), (.expP "catch*" (.iterT (.varT "catch" []) .list)), (.expP "instr*" (.iterT (.varT "instr" []) .list)), (.expP "z'" (.varT "state" [])), (.expP "instr'*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "catch") (.mk .list [(.mk "catch" (.varE "catch*"))])), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))]))])])), (.caseE "%;%" (.tupE [(.varE "z'"), (.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "catch") (.mk .list [(.mk "catch" (.varE "catch*"))])), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))])]))]) [(.rulePr "Step" [] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))])), (.caseE "%;%" (.tupE [(.varE "z'"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))]))])

/-- `Step/ctxt-frame`, rule 5 of the pinned stream. -/
def ctxtFrameRule : Rule :=
  (.ruleD "ctxt-frame" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame" [])), (.expP "n" (.varT "n" [])), (.expP "f'" (.varT "frame" [])), (.expP "instr*" (.iterT (.varT "instr" []) .list)), (.expP "s'" (.varT "store" [])), (.expP "f''" (.varT "frame" [])), (.expP "instr'*" (.iterT (.varT "instr" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.caseE "FRAME_%{%}%" (.tupE [(.varE "n"), (.varE "f'"), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))]))])])), (.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s'"), (.varE "f")])), (.listE [(.caseE "FRAME_%{%}%" (.tupE [(.varE "n"), (.varE "f''"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))])]))]) [(.rulePr "Step" [] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f'")])), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))])), (.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s'"), (.varE "f''")])), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))]))]))]))])

/-- `Step/call_ref-null`, rule 6 of the pinned stream. -/
def callRefNullRule : Rule :=
  (.ruleD "call_ref-null" [(.expP "z" (.varT "state" [])), (.expP "yy" (.varT "typeuse" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.NULL_ADDR" (.tupE [])), (.caseE "CALL_REF" (.varE "yy"))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [])

/-- `Step/call_ref-func`, rule 7 of the pinned stream. -/
def callRefFuncRule : Rule :=
  (.ruleD "call_ref-func" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "a" (.varT "addr" [])), (.expP "yy" (.varT "typeuse" [])), (.expP "m" (.varT "m" [])), (.expP "f" (.varT "frame" [])), (.expP "instr*" (.iterT (.varT "instr" []) .list)), (.expP "fi" (.varT "funcinst" [])), (.expP "t_1*" (.iterT (.varT "valtype" []) .list)), (.expP "t_2*" (.iterT (.varT "valtype" []) .list)), (.expP "x" (.varT "idx" [])), (.expP "t*" (.iterT (.varT "valtype" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "REF.FUNC_ADDR" (.varE "a")), (.caseE "CALL_REF" (.varE "yy"))]))])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "FRAME_%{%}%" (.tupE [(.varE "m"), (.varE "f"), (.listE [(.caseE "LABEL_%{%}%" (.tupE [(.varE "m"), (.listE []), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))]))])]))])]))]) [(.ifPr (.cmpE .eqOp .boolT (.idxE (.callE "funcinst" [(.expA (.varE "z"))]) (.varE "a")) (.varE "fi"))), (.rulePr "Expand" [] "%~~%" (.tupE [(.dotE (.varE "fi") "TYPE"), (.caseE "FUNC%->%" (.tupE [(.caseE "%" (.tupE [(.iterE (.varE "t_1") (.mk (.listN (.varE "n") none) [(.mk "t_1" (.varE "t_1*"))]))])), (.caseE "%" (.tupE [(.iterE (.varE "t_2") (.mk (.listN (.varE "m") none) [(.mk "t_2" (.varE "t_2*"))]))]))]))])), (.ifPr (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE") (.caseE "FUNC" (.tupE [(.varE "x"), (.iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [(.mk "t" (.varE "t*"))])), (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))]))])))), (.ifPr (.cmpE .eqOp .boolT (.varE "f") (.strE [(.mk "LOCALS" (.catE (.iterE (.optE (some (.varE "val"))) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.iterE (.callE "default_" [(.expA (.varE "t"))]) (.mk .list [(.mk "t" (.varE "t*"))])))), (.mk "MODULE" (.dotE (.varE "fi") "MODULE"))])))])

/-- `Step/call_ref-hostfunc-res`, rule 8 of the pinned stream. -/
def callRefHostfuncResRule : Rule :=
  (.ruleD "call_ref-hostfunc-res" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame" [])), (.expP "n" (.varT "n" [])), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "a" (.varT "addr" [])), (.expP "yy" (.varT "typeuse" [])), (.expP "s'" (.varT "store" [])), (.expP "result" (.varT "result" [])), (.expP "fi" (.varT "funcinst" [])), (.expP "t_1*" (.iterT (.varT "valtype" []) .list)), (.expP "m" (.varT "m" [])), (.expP "t_2*" (.iterT (.varT "valtype" []) .list)), (.expP "hf" .textT)] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "REF.FUNC_ADDR" (.varE "a")), (.caseE "CALL_REF" (.varE "yy"))]))])), (.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s'"), (.varE "f")])), (.callE "lift_result" [(.expA (.varE "result"))])]))]) [(.ifPr (.cmpE .eqOp .boolT (.idxE (.callE "funcinst" [(.expA (.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])))]) (.varE "a")) (.varE "fi"))), (.rulePr "Expand" [] "%~~%" (.tupE [(.dotE (.varE "fi") "TYPE"), (.caseE "FUNC%->%" (.tupE [(.caseE "%" (.tupE [(.iterE (.varE "t_1") (.mk (.listN (.varE "n") none) [(.mk "t_1" (.varE "t_1*"))]))])), (.caseE "%" (.tupE [(.iterE (.varE "t_2") (.mk (.listN (.varE "m") none) [(.mk "t_2" (.varE "t_2*"))]))]))]))])), (.ifPr (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE") (.caseE "_HOSTFUNC" (.varE "hf")))), (.ifPr (.memE (.caseE "RES" (.tupE [(.varE "s'"), (.varE "result")])) (.callE "hostcall" [(.expA (.caseE "_HOSTFUNC" (.varE "hf"))), (.expA (.varE "s")), (.expA (.iterE (.varE "val") (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])))])))])

/-- `Step/call_ref-hostfunc-div`, rule 9 of the pinned stream. -/
def callRefHostfuncDivRule : Rule :=
  (.ruleD "call_ref-hostfunc-div" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame" [])), (.expP "n" (.varT "n" [])), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "a" (.varT "addr" [])), (.expP "yy" (.varT "typeuse" [])), (.expP "fi" (.varT "funcinst" [])), (.expP "t_1*" (.iterT (.varT "valtype" []) .list)), (.expP "m" (.varT "m" [])), (.expP "t_2*" (.iterT (.varT "valtype" []) .list)), (.expP "hf" .textT)] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "REF.FUNC_ADDR" (.varE "a")), (.caseE "CALL_REF" (.varE "yy"))]))])), (.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "REF.FUNC_ADDR" (.varE "a")), (.caseE "CALL_REF" (.varE "yy"))]))]))]) [(.ifPr (.cmpE .eqOp .boolT (.idxE (.callE "funcinst" [(.expA (.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])))]) (.varE "a")) (.varE "fi"))), (.rulePr "Expand" [] "%~~%" (.tupE [(.dotE (.varE "fi") "TYPE"), (.caseE "FUNC%->%" (.tupE [(.caseE "%" (.tupE [(.iterE (.varE "t_1") (.mk (.listN (.varE "n") none) [(.mk "t_1" (.varE "t_1*"))]))])), (.caseE "%" (.tupE [(.iterE (.varE "t_2") (.mk (.listN (.varE "m") none) [(.mk "t_2" (.varE "t_2*"))]))]))]))])), (.ifPr (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE") (.caseE "_HOSTFUNC" (.varE "hf")))), (.ifPr (.memE (.caseE "BOT" (.tupE [])) (.callE "hostcall" [(.expA (.caseE "_HOSTFUNC" (.varE "hf"))), (.expA (.varE "s")), (.expA (.iterE (.varE "val") (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])))])))])

/-- `Step/throw`, rule 10 of the pinned stream. -/
def throwRule : Rule :=
  (.ruleD "throw" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "x" (.varT "idx" [])), (.expP "exn" (.varT "exninst" [])), (.expP "a" (.varT "addr" [])), (.expP "t*" (.iterT (.varT "valtype" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "THROW" (.varE "x"))]))])), (.caseE "%;%" (.tupE [(.callE "add_exninst" [(.expA (.varE "z")), (.expA (.listE [(.varE "exn")]))]), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE []))])]))]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "as_deftype" [(.expA (.dotE (.callE "tag" [(.expA (.varE "z")), (.expA (.varE "x"))]) "TYPE"))]), (.caseE "FUNC%->%" (.tupE [(.caseE "%" (.tupE [(.iterE (.varE "t") (.mk (.listN (.varE "n") none) [(.mk "t" (.varE "t*"))]))])), (.caseE "%" (.tupE [(.listE [])]))]))])), (.ifPr (.cmpE .eqOp .boolT (.varE "a") (.lenE (.callE "exninst" [(.expA (.varE "z"))])))), (.ifPr (.cmpE .eqOp .boolT (.varE "exn") (.strE [(.mk "TAG" (.idxE (.callE "tagaddr" [(.expA (.varE "z"))]) (.projE (.uncaseE (.varE "x") "%") (0)))), (.mk "FIELDS" (.iterE (.varE "val") (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])))])))])

/-- `Step/local.set`, rule 11 of the pinned stream. -/
def localSetRule : Rule :=
  (.ruleD "local.set" [(.expP "z" (.varT "state" [])), (.expP "val" (.varT "val" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "LOCAL.SET" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.callE "with_local" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.varE "val"))]), (.listE [])]))]) [])

/-- `Step/global.set`, rule 12 of the pinned stream. -/
def globalSetRule : Rule :=
  (.ruleD "global.set" [(.expP "z" (.varT "state" [])), (.expP "val" (.varT "val" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "GLOBAL.SET" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.callE "with_global" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.varE "val"))]), (.listE [])]))]) [])

/-- `Step/table.set-oob`, rule 13 of the pinned stream. -/
def tableSetOobRule : Rule :=
  (.ruleD "table.set-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "ref" (.varT "ref" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "TABLE.SET" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [(.ifPr (.cmpE .geOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.lenE (.dotE (.callE "table" [(.expA (.varE "z")), (.expA (.varE "x"))]) "REFS"))))])

/-- `Step/table.set-val`, rule 14 of the pinned stream. -/
def tableSetValRule : Rule :=
  (.ruleD "table.set-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "ref" (.varT "ref" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "TABLE.SET" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.callE "with_table" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.projE (.uncaseE (.varE "i") "%") (0))), (.expA (.varE "ref"))]), (.listE [])]))]) [(.ifPr (.cmpE .ltOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.lenE (.dotE (.callE "table" [(.expA (.varE "z")), (.expA (.varE "x"))]) "REFS"))))])

/-- `Step/table.grow-succeed`, rule 15 of the pinned stream. -/
def tableGrowSucceedRule : Rule :=
  (.ruleD "table.grow-succeed" [(.expP "z" (.varT "state" [])), (.expP "ref" (.varT "ref" [])), (.expP "at" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "ti" (.varT "tableinst" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "TABLE.GROW" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.callE "with_tableinst" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.varE "ti"))]), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.lenE (.dotE (.callE "table" [(.expA (.varE "z")), (.expA (.varE "x"))]) "REFS"))]))]))])]))]) [(.ifPr (.cmpE .eqOp .boolT (.varE "ti") (.callE "growtable" [(.expA (.callE "table" [(.expA (.varE "z")), (.expA (.varE "x"))])), (.expA (.varE "n")), (.expA (.varE "ref"))])))])

/-- `Step/table.grow-fail`, rule 16 of the pinned stream. -/
def tableGrowFailRule : Rule :=
  (.ruleD "table.grow-fail" [(.expP "z" (.varT "state" [])), (.expP "ref" (.varT "ref" [])), (.expP "at" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "TABLE.GROW" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.callE "inv_signed_" [(.expA (.callE "size" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expA (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)))])]))]))])]))]) [])

/-- `Step/elem.drop`, rule 17 of the pinned stream. -/
def elemDropRule : Rule :=
  (.ruleD "elem.drop" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "ELEM.DROP" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.callE "with_elem" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.listE []))]), (.listE [])]))]) [])

/-- `Step/store-num-oob`, rule 18 of the pinned stream. -/
def storeNumOobRule : Rule :=
  (.ruleD "store-num-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "nt" (.varT "numtype" [])), (.expP "c" (.varT "num_" [(.expA (.varE "nt"))])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.varE "nt"), (.varE "c")])), (.caseE "STORE" (.tupE [(.varE "nt"), (.optE none), (.varE "x"), (.varE "ao")]))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [(.expA (.varE "nt"))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step/store-num-val`, rule 19 of the pinned stream. -/
def storeNumValRule : Rule :=
  (.ruleD "store-num-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "nt" (.varT "numtype" [])), (.expP "c" (.varT "num_" [(.expA (.varE "nt"))])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" [])), (.expP "b*" (.iterT (.varT "byte" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.varE "nt"), (.varE "c")])), (.caseE "STORE" (.tupE [(.varE "nt"), (.optE none), (.varE "x"), (.varE "ao")]))])])), (.caseE "%;%" (.tupE [(.callE "with_mem" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0)))), (.expA (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [(.expA (.varE "nt"))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)), (.expA (.iterE (.varE "b") (.mk .list [(.mk "b" (.varE "b*"))])))]), (.listE [])]))]) [(.ifPr (.cmpE .eqOp .boolT (.iterE (.varE "b") (.mk .list [(.mk "b" (.varE "b*"))])) (.callE "nbytes_" [(.expA (.varE "nt")), (.expA (.varE "c"))])))])

/-- `Step/store-pack-oob`, rule 20 of the pinned stream. -/
def storePackOobRule : Rule :=
  (.ruleD "store-pack-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "Inn" (.varT "Inn" [])), (.expP "c" (.varT "num_" [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])), (.varE "c")])), (.caseE "STORE" (.tupE [(.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])), (.optE (some (.caseE "%" (.tupE [(.caseE "%" (.tupE [(.varE "n")]))])))), (.varE "x"), (.varE "ao")]))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "n") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step/store-pack-val`, rule 21 of the pinned stream. -/
def storePackValRule : Rule :=
  (.ruleD "store-pack-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "Inn" (.varT "Inn" [])), (.expP "c" (.varT "num_" [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" [])), (.expP "b*" (.iterT (.varT "byte" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])), (.varE "c")])), (.caseE "STORE" (.tupE [(.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])), (.optE (some (.caseE "%" (.tupE [(.caseE "%" (.tupE [(.varE "n")]))])))), (.varE "x"), (.varE "ao")]))])])), (.caseE "%;%" (.tupE [(.callE "with_mem" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0)))), (.expA (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "n") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)), (.expA (.iterE (.varE "b") (.mk .list [(.mk "b" (.varE "b*"))])))]), (.listE [])]))]) [(.ifPr (.cmpE .eqOp .boolT (.iterE (.varE "b") (.mk .list [(.mk "b" (.varE "b*"))])) (.callE "ibytes_" [(.expA (.varE "n")), (.expA (.callE "wrap__" [(.expA (.callE "size" [(.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])))])), (.expA (.varE "n")), (.expA (.varE "c"))]))])))])

/-- `Step/vstore-oob`, rule 22 of the pinned stream. -/
def vstoreOobRule : Rule :=
  (.ruleD "vstore-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")])), (.caseE "VSTORE" (.tupE [(.caseE "V128" (.tupE [])), (.varE "x"), (.varE "ao")]))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "vsize" [(.expA (.caseE "V128" (.tupE [])))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step/vstore-val`, rule 23 of the pinned stream. -/
def vstoreValRule : Rule :=
  (.ruleD "vstore-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" [])), (.expP "b*" (.iterT (.varT "byte" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")])), (.caseE "VSTORE" (.tupE [(.caseE "V128" (.tupE [])), (.varE "x"), (.varE "ao")]))])])), (.caseE "%;%" (.tupE [(.callE "with_mem" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0)))), (.expA (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "vsize" [(.expA (.caseE "V128" (.tupE [])))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)), (.expA (.iterE (.varE "b") (.mk .list [(.mk "b" (.varE "b*"))])))]), (.listE [])]))]) [(.ifPr (.cmpE .eqOp .boolT (.iterE (.varE "b") (.mk .list [(.mk "b" (.varE "b*"))])) (.callE "vbytes_" [(.expA (.caseE "V128" (.tupE []))), (.expA (.varE "c"))])))])

/-- `Step/vstore_lane-oob`, rule 24 of the pinned stream. -/
def vstoreLaneOobRule : Rule :=
  (.ruleD "vstore_lane-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "N" (.varT "N" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" [])), (.expP "j" (.varT "laneidx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")])), (.caseE "VSTORE_LANE" (.tupE [(.caseE "V128" (.tupE [])), (.caseE "%" (.tupE [(.varE "N")])), (.varE "x"), (.varE "ao"), (.varE "j")]))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "N") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step/vstore_lane-val`, rule 25 of the pinned stream. -/
def vstoreLaneValRule : Rule :=
  (.ruleD "vstore_lane-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "N" (.varT "N" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" [])), (.expP "j" (.varT "laneidx" [])), (.expP "b*" (.iterT (.varT "byte" []) .list)), (.expP "Jnn" (.varT "Jnn" [])), (.expP "M" (.varT "M" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")])), (.caseE "VSTORE_LANE" (.tupE [(.caseE "V128" (.tupE [])), (.caseE "%" (.tupE [(.varE "N")])), (.varE "x"), (.varE "ao"), (.varE "j")]))])])), (.caseE "%;%" (.tupE [(.callE "with_mem" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0)))), (.expA (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "N") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)), (.expA (.iterE (.varE "b") (.mk .list [(.mk "b" (.varE "b*"))])))]), (.listE [])]))]) [(.ifPr (.cmpE .eqOp .boolT (.varE "N") (.callE "jsize" [(.expA (.varE "Jnn"))]))), (.ifPr (.cmpE .eqOp .boolT (.cvtE (.projE (.uncaseE (.varE "M") "%") (0)) .natT .ratT) (.binE .divOp (.numT .ratT) (.cvtE (.numE (.natN 128)) .natT .ratT) (.cvtE (.varE "N") .natT .ratT)))), (.ifPr (.cmpE .eqOp .boolT (.iterE (.varE "b") (.mk .list [(.mk "b" (.varE "b*"))])) (.callE "ibytes_" [(.expA (.varE "N")), (.expA (.caseE "%" (.tupE [(.projE (.uncaseE (.idxE (.callE "lanes_" [(.expA (.caseE "%X%" (.tupE [(.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" [])), (.varE "M")]))), (.expA (.varE "c"))]) (.projE (.uncaseE (.varE "j") "%") (0))) "%") (0))])))])))])

/-- `Step/memory.grow-succeed`, rule 26 of the pinned stream. -/
def memoryGrowSucceedRule : Rule :=
  (.ruleD "memory.grow-succeed" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "mi" (.varT "meminst" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "MEMORY.GROW" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.callE "with_meminst" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.varE "mi"))]), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES")) .natT .ratT) (.cvtE (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])) .natT .ratT)) .ratT .natT)]))]))])]))]) [(.ifPr (.cmpE .eqOp .boolT (.varE "mi") (.callE "growmem" [(.expA (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))])), (.expA (.varE "n"))])))])

/-- `Step/memory.grow-fail`, rule 27 of the pinned stream. -/
def memoryGrowFailRule : Rule :=
  (.ruleD "memory.grow-fail" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "MEMORY.GROW" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.callE "inv_signed_" [(.expA (.callE "size" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])))])), (.expA (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)))])]))]))])]))]) [])

/-- `Step/data.drop`, rule 28 of the pinned stream. -/
def dataDropRule : Rule :=
  (.ruleD "data.drop" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "DATA.DROP" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.callE "with_data" [(.expA (.varE "z")), (.expA (.varE "x")), (.expA (.listE []))]), (.listE [])]))]) [])

/-- `Step/struct.new`, rule 29 of the pinned stream. -/
def structNewRule : Rule :=
  (.ruleD "struct.new" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "x" (.varT "idx" [])), (.expP "si" (.varT "structinst" [])), (.expP "a" (.varT "addr" [])), (.expP "mut?*" (.iterT (.iterT (.varT "mut" []) .opt) .list)), (.expP "zt*" (.iterT (.varT "storagetype" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "STRUCT.NEW" (.varE "x"))]))])), (.caseE "%;%" (.tupE [(.callE "add_structinst" [(.expA (.varE "z")), (.expA (.listE [(.varE "si")]))]), (.listE [(.caseE "REF.STRUCT_ADDR" (.varE "a"))])]))]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")), (.expA (.varE "x"))]), (.caseE "STRUCT" (.caseE "%" (.tupE [(.iterE (.caseE "%%" (.tupE [(.iterE (.varE "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])) (.mk (.listN (.varE "n") none) [(.mk "mut?" (.varE "mut?*")), (.mk "zt" (.varE "zt*"))]))])))])), (.ifPr (.cmpE .eqOp .boolT (.varE "a") (.lenE (.callE "structinst" [(.expA (.varE "z"))])))), (.ifPr (.cmpE .eqOp .boolT (.varE "si") (.strE [(.mk "TYPE" (.callE "type" [(.expA (.varE "z")), (.expA (.varE "x"))])), (.mk "FIELDS" (.iterE (.callE "packfield_" [(.expA (.varE "zt")), (.expA (.varE "val"))]) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*")), (.mk "zt" (.varE "zt*"))])))])))])

/-- `Step/struct.set-null`, rule 30 of the pinned stream. -/
def structSetNullRule : Rule :=
  (.ruleD "struct.set-null" [(.expP "z" (.varT "state" [])), (.expP "val" (.varT "val" [])), (.expP "x" (.varT "idx" [])), (.expP "i" (.varT "fieldidx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.NULL_ADDR" (.tupE [])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "STRUCT.SET" (.tupE [(.varE "x"), (.varE "i")]))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [])

/-- `Step/struct.set-struct`, rule 31 of the pinned stream. -/
def structSetStructRule : Rule :=
  (.ruleD "struct.set-struct" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" [])), (.expP "val" (.varT "val" [])), (.expP "x" (.varT "idx" [])), (.expP "i" (.varT "fieldidx" [])), (.expP "zt*" (.iterT (.varT "storagetype" []) .list)), (.expP "mut?*" (.iterT (.iterT (.varT "mut" []) .opt) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.STRUCT_ADDR" (.varE "a")), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "STRUCT.SET" (.tupE [(.varE "x"), (.varE "i")]))])])), (.caseE "%;%" (.tupE [(.callE "with_struct" [(.expA (.varE "z")), (.expA (.varE "a")), (.expA (.projE (.uncaseE (.varE "i") "%") (0))), (.expA (.callE "packfield_" [(.expA (.idxE (.iterE (.varE "zt") (.mk .list [(.mk "zt" (.varE "zt*"))])) (.projE (.uncaseE (.varE "i") "%") (0)))), (.expA (.varE "val"))]))]), (.listE [])]))]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")), (.expA (.varE "x"))]), (.caseE "STRUCT" (.caseE "%" (.tupE [(.iterE (.caseE "%%" (.tupE [(.iterE (.varE "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])) (.mk .list [(.mk "mut?" (.varE "mut?*")), (.mk "zt" (.varE "zt*"))]))])))]))])

/-- `Step/array.new_fixed`, rule 32 of the pinned stream. -/
def arrayNewFixedRule : Rule :=
  (.ruleD "array.new_fixed" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "x" (.varT "idx" [])), (.expP "ai" (.varT "arrayinst" [])), (.expP "a" (.varT "addr" [])), (.expP "mut?" (.iterT (.varT "mut" []) .opt)), (.expP "zt" (.varT "storagetype" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "ARRAY.NEW_FIXED" (.tupE [(.varE "x"), (.caseE "%" (.tupE [(.varE "n")]))]))]))])), (.caseE "%;%" (.tupE [(.callE "add_arrayinst" [(.expA (.varE "z")), (.expA (.listE [(.varE "ai")]))]), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a"))])]))]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")), (.expA (.varE "x"))]), (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE (.varE "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])))])), (.ifPr (.binE .andOp .boolT (.cmpE .eqOp .boolT (.varE "a") (.lenE (.callE "arrayinst" [(.expA (.varE "z"))]))) (.cmpE .eqOp .boolT (.varE "ai") (.strE [(.mk "TYPE" (.callE "type" [(.expA (.varE "z")), (.expA (.varE "x"))])), (.mk "FIELDS" (.iterE (.callE "packfield_" [(.expA (.varE "zt")), (.expA (.varE "val"))]) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])))]))))])

/-- `Step/array.set-null`, rule 33 of the pinned stream. -/
def arraySetNullRule : Rule :=
  (.ruleD "array.set-null" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "val" (.varT "val" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.NULL_ADDR" (.tupE [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "ARRAY.SET" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [])

/-- `Step/array.set-oob`, rule 34 of the pinned stream. -/
def arraySetOobRule : Rule :=
  (.ruleD "array.set-oob" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "val" (.varT "val" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "ARRAY.SET" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "TRAP" (.tupE []))])]))]) [(.ifPr (.cmpE .geOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.lenE (.dotE (.idxE (.callE "arrayinst" [(.expA (.varE "z"))]) (.varE "a")) "FIELDS"))))])

/-- `Step/array.set-array`, rule 35 of the pinned stream. -/
def arraySetArrayRule : Rule :=
  (.ruleD "array.set-array" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "val" (.varT "val" [])), (.expP "x" (.varT "idx" [])), (.expP "zt" (.varT "storagetype" [])), (.expP "mut?" (.iterT (.varT "mut" []) .opt))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "ARRAY.SET" (.varE "x"))])])), (.caseE "%;%" (.tupE [(.callE "with_array" [(.expA (.varE "z")), (.expA (.varE "a")), (.expA (.projE (.uncaseE (.varE "i") "%") (0))), (.expA (.callE "packfield_" [(.expA (.varE "zt")), (.expA (.varE "val"))]))]), (.listE [])]))]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")), (.expA (.varE "x"))]), (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE (.varE "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])))]))])


/-- The provenance of all 36 `Step` rules, as one structure. -/
structure HasStepRules (env : Env) : Prop where
  /-- `Step/pure`, rule 0. -/
  pure : HasRuleAt env "Step" "%~>%" 0 pureRule
  /-- `Step/read`, rule 1. -/
  read : HasRuleAt env "Step" "%~>%" 1 readRule
  /-- `Step/ctxt-instrs`, rule 2. -/
  ctxtInstrs : HasRuleAt env "Step" "%~>%" 2 ctxtInstrsRule
  /-- `Step/ctxt-label`, rule 3. -/
  ctxtLabel : HasRuleAt env "Step" "%~>%" 3 ctxtLabelRule
  /-- `Step/ctxt-handler`, rule 4. -/
  ctxtHandler : HasRuleAt env "Step" "%~>%" 4 ctxtHandlerRule
  /-- `Step/ctxt-frame`, rule 5. -/
  ctxtFrame : HasRuleAt env "Step" "%~>%" 5 ctxtFrameRule
  /-- `Step/call_ref-null`, rule 6. -/
  callRefNull : HasRuleAt env "Step" "%~>%" 6 callRefNullRule
  /-- `Step/call_ref-func`, rule 7. -/
  callRefFunc : HasRuleAt env "Step" "%~>%" 7 callRefFuncRule
  /-- `Step/call_ref-hostfunc-res`, rule 8. -/
  callRefHostfuncRes : HasRuleAt env "Step" "%~>%" 8 callRefHostfuncResRule
  /-- `Step/call_ref-hostfunc-div`, rule 9. -/
  callRefHostfuncDiv : HasRuleAt env "Step" "%~>%" 9 callRefHostfuncDivRule
  /-- `Step/throw`, rule 10. -/
  throw : HasRuleAt env "Step" "%~>%" 10 throwRule
  /-- `Step/local.set`, rule 11. -/
  localSet : HasRuleAt env "Step" "%~>%" 11 localSetRule
  /-- `Step/global.set`, rule 12. -/
  globalSet : HasRuleAt env "Step" "%~>%" 12 globalSetRule
  /-- `Step/table.set-oob`, rule 13. -/
  tableSetOob : HasRuleAt env "Step" "%~>%" 13 tableSetOobRule
  /-- `Step/table.set-val`, rule 14. -/
  tableSetVal : HasRuleAt env "Step" "%~>%" 14 tableSetValRule
  /-- `Step/table.grow-succeed`, rule 15. -/
  tableGrowSucceed : HasRuleAt env "Step" "%~>%" 15 tableGrowSucceedRule
  /-- `Step/table.grow-fail`, rule 16. -/
  tableGrowFail : HasRuleAt env "Step" "%~>%" 16 tableGrowFailRule
  /-- `Step/elem.drop`, rule 17. -/
  elemDrop : HasRuleAt env "Step" "%~>%" 17 elemDropRule
  /-- `Step/store-num-oob`, rule 18. -/
  storeNumOob : HasRuleAt env "Step" "%~>%" 18 storeNumOobRule
  /-- `Step/store-num-val`, rule 19. -/
  storeNumVal : HasRuleAt env "Step" "%~>%" 19 storeNumValRule
  /-- `Step/store-pack-oob`, rule 20. -/
  storePackOob : HasRuleAt env "Step" "%~>%" 20 storePackOobRule
  /-- `Step/store-pack-val`, rule 21. -/
  storePackVal : HasRuleAt env "Step" "%~>%" 21 storePackValRule
  /-- `Step/vstore-oob`, rule 22. -/
  vstoreOob : HasRuleAt env "Step" "%~>%" 22 vstoreOobRule
  /-- `Step/vstore-val`, rule 23. -/
  vstoreVal : HasRuleAt env "Step" "%~>%" 23 vstoreValRule
  /-- `Step/vstore_lane-oob`, rule 24. -/
  vstoreLaneOob : HasRuleAt env "Step" "%~>%" 24 vstoreLaneOobRule
  /-- `Step/vstore_lane-val`, rule 25. -/
  vstoreLaneVal : HasRuleAt env "Step" "%~>%" 25 vstoreLaneValRule
  /-- `Step/memory.grow-succeed`, rule 26. -/
  memoryGrowSucceed : HasRuleAt env "Step" "%~>%" 26 memoryGrowSucceedRule
  /-- `Step/memory.grow-fail`, rule 27. -/
  memoryGrowFail : HasRuleAt env "Step" "%~>%" 27 memoryGrowFailRule
  /-- `Step/data.drop`, rule 28. -/
  dataDrop : HasRuleAt env "Step" "%~>%" 28 dataDropRule
  /-- `Step/struct.new`, rule 29. -/
  structNew : HasRuleAt env "Step" "%~>%" 29 structNewRule
  /-- `Step/struct.set-null`, rule 30. -/
  structSetNull : HasRuleAt env "Step" "%~>%" 30 structSetNullRule
  /-- `Step/struct.set-struct`, rule 31. -/
  structSetStruct : HasRuleAt env "Step" "%~>%" 31 structSetStructRule
  /-- `Step/array.new_fixed`, rule 32. -/
  arrayNewFixed : HasRuleAt env "Step" "%~>%" 32 arrayNewFixedRule
  /-- `Step/array.set-null`, rule 33. -/
  arraySetNull : HasRuleAt env "Step" "%~>%" 33 arraySetNullRule
  /-- `Step/array.set-oob`, rule 34. -/
  arraySetOob : HasRuleAt env "Step" "%~>%" 34 arraySetOobRule
  /-- `Step/array.set-array`, rule 35. -/
  arraySetArray : HasRuleAt env "Step" "%~>%" 35 arraySetArrayRule

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- Discharged by `rfl` against the pinned stream. -/
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

/-! ## Agreement with the hand-written transcription

`Equiv/ExecStep.lean` transcribed rules 0 and 1 by hand before this file
existed.  That these are `rfl` is a check on the generator: two independent
transcriptions of the same pinned term agree definitionally. -/

/-- The generated `Step/pure` is the hand-written one. -/
theorem pureRule_eq : pureRule = ExecStep.stepPureRule := rfl

/-- The generated `Step/read` is the hand-written one. -/
theorem readRule_eq : readRule = ExecStep.stepReadRule := rfl

/-! ## The state-update rules, characterised

Four rules of `Step` are premise-free state updates with a uniform shape: a
one- or two-instruction left-hand side, and a right-hand side that is a call
to one of the `$with_*` functions applied to the state.  Nothing about the
state is inspected — the `$with_*` function is kept abstract through
`ExecNumeric.Applies`, exactly as the `Step_read` characterisations keep
`$local` and `$global` abstract.  The runtime bridge is what will later say
that `$with_local` at an encoded state is `Frame.locals` update; it is not
needed to say *when the rule fires*.

The two shapes are shared by pairs of rules, so each is proved once. -/

open Silmaril.SpecTec.Equiv.ExecStep (configV)

/-- The `.drop` conclusion shape: `(z; [OP x]) ~> ($f(z, x, ε); ε)`. -/
theorem matchExp_dropConcl_iff {env : Env} {ρ' : VarEnv} {v : Value}
    {op : MixopS} {f : IL.Id} :
    MatchExp env VarEnv.empty
      (.tupE
        [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE op (.varE "x")]]),
         .caseE "%;%" (.tupE [.callE f [.expA (.varE "z"), .expA (.varE "x"),
           .expA (.listE [])], .listE []])])
      v ρ' ↔
      ∃ z x z', v = .tuple [configV z [.case op x], configV z' []] ∧
        ρ' = (VarEnv.empty.bindVal "z" z).bindVal "x" x ∧
        ExecNumeric.Applies env f [.val z, .val x, .val (.list [])] z' := by
  have hargs : ∀ z x : Value,
      EvalArgs env ((VarEnv.empty.bindVal "z" z).bindVal "x" x)
        [.expA (.varE "z"), .expA (.varE "x"), .expA (.listE [])]
        [.val z, .val x, .val (.list [])] :=
    fun z x => evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (evalArgs_cons (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) evalArgs_nil))
  constructor
  · rintro h
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 h
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨z, iv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 hi
    obtain ⟨ie, rfl, hie⟩ := matchExps_one_iff.1 hivs
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hie
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨z', nil, υ, rfl, hz', hnil⟩ := matchExps_two_iff.1 hbvs
    rw [ExecDefault.matchExp_callE_iff] at hz'
    obtain ⟨hcall, rfl⟩ := hz'
    rw [Execution.matchExp_listNil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    exact ⟨z, x, z', rfl, rfl,
      (ExecNumeric.applies_iff_callDef rfl (hargs z x)).2 hcall⟩
  · rintro ⟨z, x, z', rfl, rfl, happ⟩
    refine matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl, ?_,
          Execution.matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩
    exact ExecDefault.matchExp_callE_iff.2
      ⟨(ExecNumeric.applies_iff_callDef rfl (hargs z x)).1 happ, rfl⟩

/-- **`Step/elem.drop`, characterised exactly.** -/
theorem ruleFires_elemDrop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v elemDropRule ↔
      ∃ z x z', v = .tuple [configV z [.case "ELEM.DROP" x], configV z' []] ∧
        ExecNumeric.Applies env "with_elem" [.val z, .val x, .val (.list [])] z' := by
  unfold elemDropRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, x, z', rfl, rfl, happ⟩ := matchExp_dropConcl_iff.1 hm
    obtain rfl := Validation.premsHold_nil_iff.1 hp
    exact ⟨z, x, z', rfl, happ⟩
  · rintro ⟨z, x, z', rfl, happ⟩
    exact ⟨_, _, matchExp_dropConcl_iff.2 ⟨z, x, z', rfl, rfl, happ⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step/data.drop`, characterised exactly.**  The same shape as
`elem.drop`, with `$with_data` for `$with_elem`. -/
theorem ruleFires_dataDrop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v dataDropRule ↔
      ∃ z x z', v = .tuple [configV z [.case "DATA.DROP" x], configV z' []] ∧
        ExecNumeric.Applies env "with_data" [.val z, .val x, .val (.list [])] z' := by
  unfold dataDropRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, x, z', rfl, rfl, happ⟩ := matchExp_dropConcl_iff.1 hm
    obtain rfl := Validation.premsHold_nil_iff.1 hp
    exact ⟨z, x, z', rfl, happ⟩
  · rintro ⟨z, x, z', rfl, happ⟩
    exact ⟨_, _, matchExp_dropConcl_iff.2 ⟨z, x, z', rfl, rfl, happ⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- The `.set` conclusion shape: `(z; [val, OP x]) ~> ($f(z, x, val); ε)`. -/
theorem matchExp_setConcl_iff {env : Env} {ρ' : VarEnv} {v : Value}
    {op : MixopS} {f : IL.Id} :
    MatchExp env VarEnv.empty
      (.tupE
        [.caseE "%;%" (.tupE [.varE "z",
          .listE [.subE (.varE "val") (.varT "val" []) (.varT "instr" []),
                  .caseE op (.varE "x")]]),
         .caseE "%;%" (.tupE [.callE f [.expA (.varE "z"), .expA (.varE "x"),
           .expA (.varE "val")], .listE []])])
      v ρ' ↔
      ∃ z val x z', v = .tuple [configV z [val, .case op x], configV z' []] ∧
        ρ' = ((VarEnv.empty.bindVal "z" z).bindVal "val" val).bindVal "x" x ∧
        ExecNumeric.Applies env f [.val z, .val x, .val val] z' := by
  have hargs : ∀ z val x : Value,
      EvalArgs env (((VarEnv.empty.bindVal "z" z).bindVal "val" val).bindVal "x" x)
        [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "val")]
        [.val z, .val x, .val val] :=
    fun _ _ _ => evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))
  constructor
  · rintro h
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 h
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨z, iv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 hi
    obtain ⟨val, ie, τ', rfl, hval, hie⟩ := matchExps_two_iff.1 hivs
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hval
    subst hval
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hie
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨z', nil, υ, rfl, hz', hnil⟩ := matchExps_two_iff.1 hbvs
    rw [ExecDefault.matchExp_callE_iff] at hz'
    obtain ⟨hcall, rfl⟩ := hz'
    rw [Execution.matchExp_listNil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    exact ⟨z, val, x, z', rfl, rfl,
      (ExecNumeric.applies_iff_callDef rfl (hargs z val x)).2 hcall⟩
  · rintro ⟨z, val, x, z', rfl, rfl, happ⟩
    refine matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                Validation.matchExp_sub_iff.2
                  ((matchExp_freshVar_iff (by simp)).2 rfl),
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl, ?_,
          Execution.matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩
    exact ExecDefault.matchExp_callE_iff.2
      ⟨(ExecNumeric.applies_iff_callDef rfl (hargs z val x)).1 happ, rfl⟩

/-- **`Step/local.set`, characterised exactly.** -/
theorem ruleFires_localSet_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v localSetRule ↔
      ∃ z val x z', v = .tuple [configV z [val, .case "LOCAL.SET" x], configV z' []] ∧
        ExecNumeric.Applies env "with_local" [.val z, .val x, .val val] z' := by
  unfold localSetRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, val, x, z', rfl, rfl, happ⟩ := matchExp_setConcl_iff.1 hm
    obtain rfl := Validation.premsHold_nil_iff.1 hp
    exact ⟨z, val, x, z', rfl, happ⟩
  · rintro ⟨z, val, x, z', rfl, happ⟩
    exact ⟨_, _, matchExp_setConcl_iff.2 ⟨z, val, x, z', rfl, rfl, happ⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step/global.set`, characterised exactly.**  The same shape as
`local.set`, with `$with_global` for `$with_local`. -/
theorem ruleFires_globalSet_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v globalSetRule ↔
      ∃ z val x z', v = .tuple [configV z [val, .case "GLOBAL.SET" x], configV z' []] ∧
        ExecNumeric.Applies env "with_global" [.val z, .val x, .val val] z' := by
  unfold globalSetRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, val, x, z', rfl, rfl, happ⟩ := matchExp_setConcl_iff.1 hm
    obtain rfl := Validation.premsHold_nil_iff.1 hp
    exact ⟨z, val, x, z', rfl, happ⟩
  · rintro ⟨z, val, x, z', rfl, happ⟩
    exact ⟨_, _, matchExp_setConcl_iff.2 ⟨z, val, x, z', rfl, rfl, happ⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-! ## The bounds-checked pairs

`table.set`, the four `store` families and the three aggregate `.set`
families each split into an `-oob` rule and a `-val` rule.  Unlike the
`else`-based families of `Step_pure` and `Step_read`, which overlap because
`else` is vacuous in a `RelD`, these pairs are guarded by an explicit `≥` and
an explicit `<` on the *same* two quantities, so they are genuinely
exclusive.  `not_both_tableSet` records that.

The guard reads `$table(z, x).REFS`, so these are the first `Step` rules that
look *inside* the state.  They still do not need the runtime bridge: what the
rule requires is that the field exists and has a given length, which
`TableRefsLen` says without committing to a representation. -/

/-- `$table(z, x)` denotes a record whose `REFS` field has `n` entries. -/
def TableRefsLen (env : Env) (z x : Value) (n : Nat) : Prop :=
  ∃ tab refs, ExecNumeric.Applies env "table" [.val z, .val x] tab ∧
    tab.field? "REFS" = some (.list refs) ∧ refs.length = n

/-- An address immediate `%(k)` carries the natural number `k`.  The pinned
rules reach it as `(i : num_(at))!` projected at 0, which is why this is a
projection out of a tuple rather than an equation on `i`. -/
def AddrNat (i : Value) (k : Nat) : Prop :=
  ∃ vs, i = .case "%" (.tuple vs) ∧ vs[0]? = some (.num (.natN k))

theorem cmpValues_geOp_natN_true_iff {a b : Nat} :
    Sem.cmpValues .geOp (.num (.natN a)) (.num (.natN b)) = .ok (.bool true) ↔ b ≤ a := by
  simp [Sem.cmpValues, Sem.Num.cmp, Res.ofOption]

theorem cmpValues_ltOp_natN_true_iff {a b : Nat} :
    Sem.cmpValues .ltOp (.num (.natN a)) (.num (.natN b)) = .ok (.bool true) ↔ a < b := by
  simp [Sem.cmpValues, Sem.Num.cmp, Res.ofOption]

/-- The left-hand side shared by `table.set-oob` and `table.set-val`:
`z; [CONST at i, ref, TABLE.SET x]`. -/
theorem matchExp_constRefOpLhs_iff {env : Env} {ρ' : VarEnv} {v : Value} {op : MixopS} :
    MatchExp env VarEnv.empty
      (.caseE "%;%" (.tupE [.varE "z",
        .listE [.caseE "CONST" (.tupE
                  [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
                   .varE "i"]),
                .subE (.varE "ref") (.varT "ref" []) (.varT "instr" []),
                .caseE op (.varE "x")]]))
      v ρ' ↔
      ∃ z atv i ref x,
        v = configV z [Execution.constV atv i, ref, .case op x] ∧
        ρ' = ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "ref" ref).bindVal "x" x := by
  constructor
  · rintro h
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 h
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨z, iv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 hi
    obtain ⟨c, ref, x', τ₁, τ₂, rfl, hc, hr, hx'⟩ := matchExps_three_iff.1 hivs
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨atv, i, τ₃, rfl, hat, hi'⟩ := matchExps_two_iff.1 hcvs
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
    subst hat
    rw [matchExp_freshVar_iff (by simp)] at hi'
    subst hi'
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hr
    subst hr
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hx'
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    exact ⟨z, atv, i, ref, x, rfl, rfl⟩
  · rintro ⟨z, atv, i, ref, x, rfl, rfl⟩
    exact Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_two_iff.2 ⟨_, _, _, rfl,
                    Validation.matchExp_sub_iff.2
                      ((matchExp_freshVar_iff (by simp)).2 rfl),
                    (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
              Validation.matchExp_sub_iff.2
                ((matchExp_freshVar_iff (by simp)).2 rfl),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩

/-- The guard shared by the pair, as a premise.  Restricted to the two
orderings the rules actually use: for `eqOp` and `neOp` the statement is
**false**, because `cmpValues` settles those by structural equality
(`eval.ml:260-263`) without requiring either side to be a number, so the
premise can hold with an index that is not an address at all: `(i!)_0 ⋈ |$table(z,x).REFS|`.
Stated for an arbitrary comparison so both rules can use it. -/
theorem premsHold_tableGuard_iff {env : Env} {ρ' : VarEnv} {op : CmpOp}
    {z atv i ref x : Value} (hop : op = .geOp ∨ op = .ltOp) :
    PremsHold env
      (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
        "ref" ref).bindVal "x" x)
      [.ifPr (.cmpE op (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS")))]
      ρ' ↔
      ρ' = ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
        "ref" ref).bindVal "x" x ∧
      ∃ k n, AddrNat i k ∧ TableRefsLen env z x n ∧
        Sem.cmpValues op (.num (.natN k)) (.num (.natN n)) = .ok (.bool true) := by
  have hargs : EvalArgs env
      (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
        "ref" ref).bindVal "x" x)
      [.expA (.varE "z"), .expA (.varE "x")] [.val z, .val x] :=
    evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)
  constructor
  · rintro h
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 h
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨rfl, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨vs, huc, -, hidx⟩ := evalExp_projE_iff.1 hv₁
    rw [evalExp_uncaseE_iff, evalExp_varE_iff] at huc
    simp at huc
    obtain ⟨refs, hlen, rfl⟩ := evalExp_lenE_iff.1 hv₂
    obtain ⟨tab, htab, hfield⟩ := evalExp_dotE_iff.1 hlen
    rw [evalExp_callE_iff] at htab
    refine ⟨rfl, ?_⟩
    cases v₁ with
    | num m =>
      cases m with
      | natN k =>
        exact ⟨k, refs.length, ⟨vs, huc, hidx⟩,
          ⟨tab, refs, (ExecNumeric.applies_iff_callDef rfl hargs).2 htab, hfield, rfl⟩, hcmp⟩
      | _ => rcases hop with rfl | rfl <;>
               simp [Sem.cmpValues, Sem.Num.cmp, Res.ofOption] at hcmp
    | _ => rcases hop with rfl | rfl <;> simp [Sem.cmpValues] at hcmp
  · rintro ⟨rfl, k, n, ⟨vs, rfl, hidx⟩, ⟨tab, refs, happ, hfield, rfl⟩, hcmp⟩
    refine Validation.premsHold_cons_iff.2 ⟨_,
      Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩, Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.num (.natN k), .num (.natN refs.length), ?_, ?_, hcmp⟩
    · exact evalExp_projE_iff.2 ⟨vs,
        evalExp_uncaseE_iff.2 (evalExp_varE_iff.2 (by simp)), by omega, hidx⟩
    · exact evalExp_lenE_iff.2 ⟨refs, evalExp_dotE_iff.2 ⟨tab,
        evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef rfl hargs).1 happ), hfield⟩, rfl⟩

/-- **`Step/table.set-oob`, characterised exactly.**  The index is at or past
the end of the table, and the configuration traps with the state unchanged. -/
theorem ruleFires_tableSetOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableSetOobRule ↔
      ∃ z atv i ref x k n,
        v = .tuple [configV z [Execution.constV atv i, ref, .case "TABLE.SET" x],
                    configV z [Execution.trapV]] ∧
        AddrNat i k ∧ TableRefsLen env z x n ∧ n ≤ k := by
  unfold tableSetOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, atv, i, ref, x, rfl, rfl⟩ := matchExp_constRefOpLhs_iff.1 hl
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨z', trs, υ, rfl, hz', htrs⟩ := matchExps_two_iff.1 hbvs
    rw [matchExp_boundVar_iff (w := z) (by simp)] at hz'
    obtain ⟨rfl, rfl⟩ := hz'
    obtain ⟨tvs, rfl, htvs⟩ := Validation.matchExp_list_iff.1 htrs
    obtain ⟨t, rfl, ht⟩ := matchExps_one_iff.1 htvs
    rw [Execution.matchExp_caseNil_iff] at ht
    obtain ⟨rfl, rfl⟩ := ht
    obtain ⟨rfl, k, n, haddr, hlen, hcmp⟩ := (premsHold_tableGuard_iff (Or.inl rfl)).1 hp
    exact ⟨z', atv, i, ref, x, k, n, rfl, haddr, hlen,
      cmpValues_geOp_natN_true_iff.1 hcmp⟩
  · rintro ⟨z, atv, i, ref, x, k, n, rfl, haddr, hlen, hle⟩
    refine ⟨(((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
      "ref" ref).bindVal "x" x), (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
      "ref" ref).bindVal "x" x), matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_constRefOpLhs_iff.2 ⟨z, atv, i, ref, x, rfl, rfl⟩, ?_⟩,
      (premsHold_tableGuard_iff (Or.inl rfl)).2 ⟨rfl, k, n, haddr, hlen,
        cmpValues_geOp_natN_true_iff.2 hle⟩⟩
    exact Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_boundVar_iff (w := z) (by simp)).2 ⟨rfl, rfl⟩,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl,
              Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩

/-- **`Step/table.set-val`, characterised exactly.**  The index is inside the
table, and the state is replaced by `$with_table(z, x, i, ref)`. -/
theorem ruleFires_tableSetVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableSetValRule ↔
      ∃ z atv i ref x k n z',
        v = .tuple [configV z [Execution.constV atv i, ref, .case "TABLE.SET" x],
                    configV z' []] ∧
        AddrNat i k ∧ TableRefsLen env z x n ∧ k < n ∧
        ExecNumeric.Applies env "with_table"
          [.val z, .val x, .val (.num (.natN k)), .val ref] z' := by
  have hargs : ∀ z atv i ref x : Value, ∀ k : Nat, AddrNat i k →
      EvalArgs env
        (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "ref" ref).bindVal "x" x)
        [.expA (.varE "z"), .expA (.varE "x"),
         .expA (.projE (.uncaseE (.varE "i") "%") 0), .expA (.varE "ref")]
        [.val z, .val x, .val (.num (.natN k)), .val ref] := by
    rintro z atv i ref x k ⟨vs, rfl, hidx⟩
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (evalArgs_cons (evalExp_projE_iff.2 ⟨vs,
            evalExp_uncaseE_iff.2 (evalExp_varE_iff.2 (by simp)), by omega, hidx⟩)
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)))
  unfold tableSetValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨z, atv, i, ref, x, rfl, rfl⟩ := matchExp_constRefOpLhs_iff.1 hl
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨z', nil, υ, rfl, hz', hnil⟩ := matchExps_two_iff.1 hbvs
    rw [ExecDefault.matchExp_callE_iff] at hz'
    obtain ⟨hcall, rfl⟩ := hz'
    rw [Execution.matchExp_listNil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    obtain ⟨rfl, k, n, haddr, hlen, hcmp⟩ :=
      (premsHold_tableGuard_iff (Or.inr rfl)).1 hp
    exact ⟨z, atv, i, ref, x, k, n, z', rfl, haddr, hlen,
      cmpValues_ltOp_natN_true_iff.1 hcmp,
      (ExecNumeric.applies_iff_callDef rfl (hargs z atv i ref x k haddr)).2 hcall⟩
  · rintro ⟨z, atv, i, ref, x, k, n, z', rfl, haddr, hlen, hlt, happ⟩
    refine ⟨(((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
      "ref" ref).bindVal "x" x),
      (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
        "ref" ref).bindVal "x" x),
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
        matchExp_constRefOpLhs_iff.2 ⟨z, atv, i, ref, x, rfl, rfl⟩, ?_⟩,
      (premsHold_tableGuard_iff (Or.inr rfl)).2 ⟨rfl, k, n, haddr, hlen,
        cmpValues_ltOp_natN_true_iff.2 hlt⟩⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl, ?_,
          Execution.matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩
    exact ExecDefault.matchExp_callE_iff.2
      ⟨(ExecNumeric.applies_iff_callDef rfl (hargs z atv i ref x k haddr)).1 happ, rfl⟩

/-- `TableRefsLen` is a function of `z` and `x`: `Applies` is deterministic
(`ExecNumeric.Applies.unique`) and `field?` is a function. -/
theorem TableRefsLen.unique {env : Env} {z x : Value} {n₁ n₂ : Nat}
    (h₁ : TableRefsLen env z x n₁) (h₂ : TableRefsLen env z x n₂) : n₁ = n₂ := by
  obtain ⟨tab₁, refs₁, ha₁, hf₁, rfl⟩ := h₁
  obtain ⟨tab₂, refs₂, ha₂, hf₂, rfl⟩ := h₂
  obtain rfl := ExecNumeric.Applies.unique ha₁ ha₂
  rw [hf₁] at hf₂
  obtain rfl := Value.list.inj (Option.some.inj hf₂)
  rfl

/-- **`table.set-oob` and `table.set-val` are exclusive.**  At most one of
them fires at any configuration.  This is what the `else`-based families of
`Step_pure` and `Step_read` do *not* enjoy: there the second rule is guarded
by `else`, which `premHolds` discharges unconditionally, so the two genuinely
overlap (`ExecRead.ruleFires_refTestFalse_onAnything`).  Here the guard is an
explicit `≥` against an explicit `<` on the same two quantities, and
`Applies` being deterministic turns that into real exclusion. -/
theorem not_ruleFires_tableSet_both {env : Env} {v : Value}
    (h₁ : RuleFires env "%~>%" [] [] v tableSetOobRule)
    (h₂ : RuleFires env "%~>%" [] [] v tableSetValRule) : False := by
  obtain ⟨z, atv, i, ref, x, k, n, hv, ⟨vs, rfl, hi⟩, hlen, hge⟩ :=
    ruleFires_tableSetOob_iff.1 h₁
  obtain ⟨z', atv', i', ref', x', k', n', w', hv', ⟨vs', hi'eq, hi'⟩, hlen', hlt, -⟩ :=
    ruleFires_tableSetVal_iff.1 h₂
  rw [hv] at hv'
  simp only [Value.tuple.injEq, List.cons.injEq, configV, Execution.constV,
    Value.case.injEq, Value.list.injEq, and_true, true_and] at hv'
  obtain ⟨⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩, -⟩ := hv'
  simp only [Value.case.injEq, Value.tuple.injEq, true_and] at hi'eq
  subst hi'eq
  rw [hi'] at hi
  simp only [Option.some.injEq, Value.num.injEq] at hi
  obtain rfl : k = k' := by cases hi; rfl
  have hn := TableRefsLen.unique hlen hlen'
  omega

/-! ## The `grow` pairs, and a second kind of overlap

`table.grow-fail` and `memory.grow-fail` have **no premises at all**.  They
fire at every `… GROW` configuration, including every one at which the
corresponding `-succeed` rule also fires.  That overlap is deliberate — it is
how the specification expresses that `grow` may fail for reasons outside the
model — and it is a *third* mechanism, distinct from the vacuous `else` of
`Step_pure`/`Step_read` and from the genuinely exclusive guards of
`table.set`.  `ruleFires_tableGrowFail_onAnything` records it: the rule fires
at an arbitrary state, reference and size.

Both rules return `$inv_signed_($size(at), -1)`, the all-ones address, which
is the only place in `Step` where a result is computed from the address type
alone. -/

/-- The right-hand side both `-fail` rules share: `z; [CONST at %(-1 : at)]`,
where `-1` is spelled `$inv_signed_($size(at), -1)`. -/
theorem matchExp_growFailRhs_iff {env : Env} {ρ ρ' : VarEnv} {v z atv : Value}
    (hz : ρ.findVal? "z" = some z) (hat : ρ.findVal? "at" = some atv)
    (hd₁ : ρ.findDef? "inv_signed_" = none) (hd₂ : ρ.findDef? "size" = none) :
    MatchExp env ρ
      (.caseE "%;%" (.tupE [.varE "z",
        .listE [.caseE "CONST" (.tupE
          [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
           .caseE "%" (.tupE
             [.callE "inv_signed_"
               [.expA (.callE "size" [.expA (.subE (.varE "at")
                 (.varT "addrtype" []) (.varT "numtype" []))]),
                .expA (.unE .minusOp (.numT .intT)
                  (.cvtE (.numE (.natN 1)) .natT .intT))]])])]]))
      v ρ' ↔
      ∃ k j, v = configV z [Execution.constV atv (.case "%" (.tuple [j]))] ∧ ρ' = ρ ∧
        ExecNumeric.Applies env "size" [.val atv] k ∧
        ExecNumeric.Applies env "inv_signed_"
          [.val k, .val (intV (-1))] j := by
  have hsize : ∀ k : Value, ExecNumeric.Applies env "size" [.val atv] k →
      EvalArgs env ρ
        [.expA (.callE "size" [.expA (.subE (.varE "at")
          (.varT "addrtype" []) (.varT "numtype" []))]),
         .expA (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))]
        [.val k, .val (intV (-1))] := by
    intro k hk
    refine evalArgs_cons (evalExp_callE_iff.2
      ((ExecNumeric.applies_iff_callDef hd₂ ?_).1 hk)) (evalArgs_cons ?_ evalArgs_nil)
    · exact evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 hat)) evalArgs_nil
    · exact evalExp_unE_iff.2 ⟨intV 1, evalExp_oneInt, rfl⟩
  constructor
  · rintro h
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 h
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z', is, τ, rfl, hz', his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_boundVar_iff (w := z) hz] at hz'
    obtain ⟨rfl, rfl⟩ := hz'
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hivs
    obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
    obtain ⟨atv', pc, τ', rfl, hatv, hpc⟩ := matchExps_two_iff.1 hcws
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := atv) hat] at hatv
    obtain ⟨rfl, rfl⟩ := hatv
    obtain ⟨pw, rfl, hpw⟩ := Validation.matchExp_case_iff.1 hpc
    obtain ⟨pws, rfl, hpws⟩ := Validation.matchExp_tup_iff.1 hpw
    obtain ⟨j, rfl, hj⟩ := matchExps_one_iff.1 hpws
    rw [ExecDefault.matchExp_callE_iff] at hj
    obtain ⟨hcall, rfl⟩ := hj
    rw [ExecNumeric.callDef_iff, hd₁, Option.getD_none] at hcall
    obtain ⟨ws, ps, t, cs, hargs, hfind, hbody⟩ := hcall
    -- the first argument is `$size(at)`, which must itself denote something
    obtain ⟨k, ws', rfl, hk, hrest⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
    rw [evalExp_callE_iff] at hk
    obtain ⟨m, ws'', rfl, hm, hnil⟩ := ExecRead.evalArgs_expA_cons_iff.1 hrest
    obtain rfl := Validation.evalArgs_nil_iff.1 hnil
    rw [evalExp_unE_iff] at hm
    obtain ⟨w, hw, hun⟩ := hm
    obtain rfl : w = intV 1 :=
      EvalExp.unique hw evalExp_oneInt
    obtain rfl : m = intV (-1) := by
      simpa [intV, Sem.unValue, Sem.Num.un] using hun.symm
    refine ⟨k, j, rfl, rfl, ?_, ⟨ps, t, cs, hfind, hbody⟩⟩
    refine (ExecNumeric.applies_iff_callDef hd₂ ?_).2 hk
    exact evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 hat)) evalArgs_nil
  · rintro ⟨k, j, rfl, rfl, hk, hj⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_boundVar_iff (w := z) hz).2 ⟨rfl, rfl⟩,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl, ?_⟩⟩⟩⟩⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2
            ((matchExp_boundVar_iff (w := atv) hat).2 ⟨rfl, rfl⟩), ?_⟩⟩⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, ?_⟩⟩⟩
    exact ExecDefault.matchExp_callE_iff.2
      ⟨(ExecNumeric.applies_iff_callDef hd₁ (hsize k hk)).1 hj, rfl⟩

/-- **`Step/memory.grow-fail`, characterised exactly.**  No premises: it fires
at every `MEMORY.GROW` configuration. -/
theorem ruleFires_memoryGrowFail_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryGrowFailRule ↔
      ∃ z atv n x k j,
        v = .tuple [configV z [Execution.constV atv (.case "%" (.tuple [n])),
                               .case "MEMORY.GROW" x],
                    configV z [Execution.constV atv (.case "%" (.tuple [j]))]] ∧
        ExecNumeric.Applies env "size" [.val atv] k ∧
        ExecNumeric.Applies env "inv_signed_" [.val k, .val (intV (-1))] j := by
  unfold memoryGrowFailRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨c, g, τ₁, rfl, hc, hg⟩ := matchExps_two_iff.1 hivs
    obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
    obtain ⟨atv, pc, τ₂, rfl, hat, hpc⟩ := matchExps_two_iff.1 hcws
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
    subst hat
    obtain ⟨pw, rfl, hpw⟩ := Validation.matchExp_case_iff.1 hpc
    obtain ⟨pws, rfl, hpws⟩ := Validation.matchExp_tup_iff.1 hpw
    obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hpws
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hg
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨k, j, rfl, rfl, hk, hj⟩ :=
      (matchExp_growFailRhs_iff (z := z) (atv := atv)
        (by simp) (by simp) rfl rfl).1 hr
    obtain rfl := Validation.premsHold_nil_iff.1 hp
    exact ⟨z, atv, n, x, k, j, rfl, hk, hj⟩
  · rintro ⟨z, atv, n, x, k, j, rfl, hk, hj⟩
    refine ⟨(((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "n" n).bindVal "x" x,
      (((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "n" n).bindVal "x" x,
      matchExp_concl_iff.2 ⟨_, _, _, rfl, ?_,
        (matchExp_growFailRhs_iff (z := z) (atv := atv)
          (by simp) (by simp) rfl rfl).2 ⟨k, j, rfl, rfl, hk, hj⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl, ?_,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩
    exact Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩

/-- **`Step/table.grow-fail`, characterised exactly.**  The same right-hand
side as `memory.grow-fail`, with a reference on the stack. -/
theorem ruleFires_tableGrowFail_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v tableGrowFailRule ↔
      ∃ z ref atv n x k j,
        v = .tuple [configV z [ref, Execution.constV atv (.case "%" (.tuple [n])),
                               .case "TABLE.GROW" x],
                    configV z [Execution.constV atv (.case "%" (.tuple [j]))]] ∧
        ExecNumeric.Applies env "size" [.val atv] k ∧
        ExecNumeric.Applies env "inv_signed_" [.val k, .val (intV (-1))] j := by
  unfold tableGrowFailRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨ref, c, g, τ₁, τ₂, rfl, href, hc, hg⟩ := matchExps_three_iff.1 hivs
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at href
    subst href
    obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
    obtain ⟨atv, pc, τ₃, rfl, hat, hpc⟩ := matchExps_two_iff.1 hcws
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
    subst hat
    obtain ⟨pw, rfl, hpw⟩ := Validation.matchExp_case_iff.1 hpc
    obtain ⟨pws, rfl, hpws⟩ := Validation.matchExp_tup_iff.1 hpw
    obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hpws
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hg
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨k, j, rfl, rfl, hk, hj⟩ :=
      (matchExp_growFailRhs_iff (z := z) (atv := atv)
        (by simp) (by simp) rfl rfl).1 hr
    obtain rfl := Validation.premsHold_nil_iff.1 hp
    exact ⟨z, ref, atv, n, x, k, j, rfl, hk, hj⟩
  · rintro ⟨z, ref, atv, n, x, k, j, rfl, hk, hj⟩
    refine ⟨((((VarEnv.empty.bindVal "z" z).bindVal "ref" ref).bindVal "at" atv).bindVal
      "n" n).bindVal "x" x,
      ((((VarEnv.empty.bindVal "z" z).bindVal "ref" ref).bindVal "at" atv).bindVal
        "n" n).bindVal "x" x,
      matchExp_concl_iff.2 ⟨_, _, _, rfl, ?_,
        (matchExp_growFailRhs_iff (z := z) (atv := atv)
          (by simp) (by simp) rfl rfl).2 ⟨k, j, rfl, rfl, hk, hj⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
              Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
              ?_,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩
    exact Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩

/-- **`table.grow-fail` fires at an arbitrary state, reference and size.**  It
has no premises, so it overlaps `table.grow-succeed` everywhere the latter
fires.  That is deliberate — `grow` may fail for reasons outside the model —
and it is a third, distinct mechanism from the vacuous `else` of
`Step_pure`/`Step_read` and from the exclusive guards of `table.set`. -/
theorem ruleFires_tableGrowFail_onAnything {env : Env} {z ref atv n x k j : Value}
    (hk : ExecNumeric.Applies env "size" [.val atv] k)
    (hj : ExecNumeric.Applies env "inv_signed_" [.val k, .val (intV (-1))] j) :
    RuleFires env "%~>%" [] []
      (.tuple [configV z [ref, Execution.constV atv (.case "%" (.tuple [n])),
                          .case "TABLE.GROW" x],
               configV z [Execution.constV atv (.case "%" (.tuple [j]))]])
      tableGrowFailRule :=
  ruleFires_tableGrowFail_iff.2 ⟨z, ref, atv, n, x, k, j, rfl, hk, hj⟩

/-! ## The null traps

`call_ref-null`, `struct.set-null` and `array.set-null` are premise-free: a
null reference under the operands traps, whatever the state.  They share the
right-hand side `z; [TRAP]`, which `matchExp_trapRhs_iff` matches once.

None of them looks at the state, so all three are bridge-free. -/

/-- The right-hand side `z; [TRAP]`, for a `z` already bound in `ρ`. -/
theorem matchExp_trapRhs_iff {env : Env} {ρ ρ' : VarEnv} {v z : Value}
    (hz : ρ.findVal? "z" = some z) :
    MatchExp env ρ
      (.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "TRAP" (.tupE [])]])) v ρ' ↔
      v = configV z [Execution.trapV] ∧ ρ' = ρ := by
  constructor
  · rintro h
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 h
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z', is, τ, rfl, hz', his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_boundVar_iff (w := z) hz] at hz'
    obtain ⟨rfl, rfl⟩ := hz'
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨t, rfl, ht⟩ := matchExps_one_iff.1 hivs
    rw [Execution.matchExp_caseNil_iff] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_boundVar_iff (w := z) hz).2 ⟨rfl, rfl⟩,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl,
              Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩

/-- **`Step/call_ref-null`, characterised exactly.** -/
theorem ruleFires_callRefNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v callRefNullRule ↔
      ∃ z yy,
        v = .tuple [configV z [Execution.caseNilV "REF.NULL_ADDR",
                               .case "CALL_REF" yy],
                    configV z [Execution.trapV]] := by
  unfold callRefNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨nl, cr, τ₁, rfl, hnl, hcr⟩ := matchExps_two_iff.1 hivs
    rw [Execution.matchExp_caseNil_iff] at hnl
    obtain ⟨rfl, rfl⟩ := hnl
    obtain ⟨yy, rfl, hyy⟩ := Validation.matchExp_case_iff.1 hcr
    rw [matchExp_freshVar_iff (by simp)] at hyy
    subst hyy
    obtain ⟨rfl, rfl⟩ := (matchExp_trapRhs_iff (z := z) (by simp)).1 hr
    exact ⟨z, yy, rfl⟩
  · rintro ⟨z, yy, rfl⟩
    refine ⟨(VarEnv.empty.bindVal "z" z).bindVal "yy" yy,
      (VarEnv.empty.bindVal "z" z).bindVal "yy" yy,
      matchExp_concl_iff.2 ⟨_, _, _, rfl, ?_,
        (matchExp_trapRhs_iff (z := z) (by simp)).2 ⟨rfl, rfl⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    exact Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩

/-- **`Step/struct.set-null`, characterised exactly.** -/
theorem ruleFires_structSetNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v structSetNullRule ↔
      ∃ z val x i,
        v = .tuple [configV z [Execution.caseNilV "REF.NULL_ADDR", val,
                               .case "STRUCT.SET" (.tuple [x, i])],
                    configV z [Execution.trapV]] := by
  unfold structSetNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨nl, val, st, τ₁, τ₂, rfl, hnl, hval, hst⟩ := matchExps_three_iff.1 hivs
    rw [Execution.matchExp_caseNil_iff] at hnl
    obtain ⟨rfl, rfl⟩ := hnl
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hval
    subst hval
    obtain ⟨sw, rfl, hsw⟩ := Validation.matchExp_case_iff.1 hst
    obtain ⟨sws, rfl, hsws⟩ := Validation.matchExp_tup_iff.1 hsw
    obtain ⟨x, i, τ₃, rfl, hx, hi⟩ := matchExps_two_iff.1 hsws
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨rfl, rfl⟩ := (matchExp_trapRhs_iff (z := z) (by simp)).1 hr
    exact ⟨z, val, x, i, rfl⟩
  · rintro ⟨z, val, x, i, rfl⟩
    refine ⟨(((VarEnv.empty.bindVal "z" z).bindVal "val" val).bindVal "x" x).bindVal "i" i,
      (((VarEnv.empty.bindVal "z" z).bindVal "val" val).bindVal "x" x).bindVal "i" i,
      matchExp_concl_iff.2 ⟨_, _, _, rfl, ?_,
        (matchExp_trapRhs_iff (z := z) (by simp)).2 ⟨rfl, rfl⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    exact Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
              Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_two_iff.2 ⟨_, _, _, rfl,
                    (matchExp_freshVar_iff (by simp)).2 rfl,
                    (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩⟩

/-- **`Step/array.set-null`, characterised exactly.** -/
theorem ruleFires_arraySetNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arraySetNullRule ↔
      ∃ z i val x,
        v = .tuple [configV z [Execution.caseNilV "REF.NULL_ADDR",
                               Execution.constV Execution.i32V i, val,
                               .case "ARRAY.SET" x],
                    configV z [Execution.trapV]] := by
  unfold arraySetNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨nl, c, val, st, τ₁, τ₂, τ₃, rfl, hnl, hc, hval, hst⟩ :=
      matchExps_four_iff.1 hivs
    rw [Execution.matchExp_caseNil_iff] at hnl
    obtain ⟨rfl, rfl⟩ := hnl
    obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
    obtain ⟨nt, i, τ₄, rfl, hnt, hi⟩ := matchExps_two_iff.1 hcws
    rw [Execution.matchExp_caseNil_iff] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hval
    subst hval
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hst
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨rfl, rfl⟩ := (matchExp_trapRhs_iff (z := z) (by simp)).1 hr
    exact ⟨z, i, val, x, rfl⟩
  · rintro ⟨z, i, val, x, rfl⟩
    refine ⟨(((VarEnv.empty.bindVal "z" z).bindVal "i" i).bindVal "val" val).bindVal "x" x,
      (((VarEnv.empty.bindVal "z" z).bindVal "i" i).bindVal "val" val).bindVal "x" x,
      matchExp_concl_iff.2 ⟨_, _, _, rfl, ?_,
        (matchExp_trapRhs_iff (z := z) (by simp)).2 ⟨rfl, rfl⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
              Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩, ?_,
              Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩
    exact Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
          (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩

/-! ## `array.set`, and a bounds check that is not where you expect

`array.set-oob` is guarded exactly like `table.set-oob`: the index is at or
past the end of `$arrayinst(z)[a].FIELDS`.  Its partner `array.set-array`,
however, has **no bounds premise at all** — its only premise is an `Expand`
of the array's type.  So the pair is *not* exclusive the way `table.set` is:
whether the in-bounds case is really restricted to in-bounds indices rests
entirely on `$with_array` being undefined past the end, which is a property
of a function definition rather than a guard on the rule.

The same holds for the four `store` families: `store-num-oob` carries the
bounds check, and `store-num-val`'s only premise is the byte decomposition
`b* = $nbytes_(nt, c)`.

That is not necessarily a defect — a partial `$with_*` does restrict the
rule — but it means the exclusivity of these pairs cannot be read off the
rules, as it can for `table.set`, and `not_ruleFires_tableSet_both` has no
analogue here without unfolding `$with_array` and `$with_mem`. -/

/-- `$arrayinst(z)[a].FIELDS` has `n` entries. -/
def ArrayFieldsLen (env : Env) (z a : Value) (n : Nat) : Prop :=
  ∃ ais k arr fields, ExecNumeric.Applies env "arrayinst" [.val z] ais ∧
    a = .num (.natN k) ∧ ais.idx? k = some arr ∧
    arr.field? "FIELDS" = some (.list fields) ∧ fields.length = n

/-- **`Step/array.set-oob`, characterised exactly.** -/
theorem ruleFires_arraySetOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arraySetOobRule ↔
      ∃ z a i val x k n,
        v = .tuple [configV z [.case "REF.ARRAY_ADDR" a,
                               Execution.constV Execution.i32V i, val,
                               .case "ARRAY.SET" x],
                    configV z [Execution.trapV]] ∧
        AddrNat i k ∧ ArrayFieldsLen env z a n ∧ n ≤ k := by
  have hargs : ∀ z a i val x : Value,
      EvalArgs env
        (((((VarEnv.empty.bindVal "z" z).bindVal "a" a).bindVal "i" i).bindVal
          "val" val).bindVal "x" x)
        [.expA (.varE "z")] [.val z] :=
    fun _ _ _ _ _ => evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil
  unfold arraySetOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨c, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨ra, cn, val, st, τ₁, τ₂, τ₃, rfl, hra, hcn, hval, hst⟩ :=
      matchExps_four_iff.1 hivs
    obtain ⟨a, rfl, ha⟩ := Validation.matchExp_case_iff.1 hra
    rw [matchExp_freshVar_iff (by simp)] at ha
    subst ha
    obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hcn
    obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
    obtain ⟨nt, i, τ₄, rfl, hnt, hi⟩ := matchExps_two_iff.1 hcws
    rw [Execution.matchExp_caseNil_iff] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hval
    subst hval
    obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hst
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨rfl, rfl⟩ := (matchExp_trapRhs_iff (z := z) (by simp)).1 hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨rfl, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨vs, huc, -, hidx⟩ := evalExp_projE_iff.1 hv₁
    rw [evalExp_uncaseE_iff, evalExp_varE_iff] at huc
    simp at huc
    obtain ⟨fields, hlen, rfl⟩ := evalExp_lenE_iff.1 hv₂
    obtain ⟨arr, harr, hfield⟩ := evalExp_dotE_iff.1 hlen
    obtain ⟨ais, kk, hais, hkk, hidx'⟩ := evalExp_idxE_iff.1 harr
    rw [evalExp_callE_iff] at hais
    rw [evalExp_varE_iff] at hkk
    simp at hkk
    cases v₁ with
    | num m =>
      cases m with
      | natN k =>
        exact ⟨z, _, _, _, x, k, fields.length, rfl, ⟨vs, huc, hidx⟩,
          ⟨ais, kk, arr, fields,
            (ExecNumeric.applies_iff_callDef rfl (hargs _ _ _ _ _)).2 hais,
            hkk, hidx', hfield, rfl⟩,
          cmpValues_geOp_natN_true_iff.1 hcmp⟩
      | _ => simp [Sem.cmpValues, Sem.Num.cmp, Res.ofOption] at hcmp
    | _ => simp [Sem.cmpValues] at hcmp
  · rintro ⟨z, a, i, val, x, k, n, rfl, ⟨vs, rfl, hidx⟩,
      ⟨ais, kk, arr, fields, hais, rfl, hidx', hfield, rfl⟩, hle⟩
    refine ⟨((((VarEnv.empty.bindVal "z" z).bindVal "a" (.num (.natN kk))).bindVal
      "i" (.case "%" (.tuple vs))).bindVal "val" val).bindVal "x" x,
      ((((VarEnv.empty.bindVal "z" z).bindVal "a" (.num (.natN kk))).bindVal
        "i" (.case "%" (.tuple vs))).bindVal "val" val).bindVal "x" x,
      matchExp_concl_iff.2 ⟨_, _, _, rfl, ?_,
        (matchExp_trapRhs_iff (z := z) (by simp)).2 ⟨rfl, rfl⟩⟩, ?_⟩
    · refine Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩, ?_,
                Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩
      exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_,
        Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩, Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_cmpE_iff.2 ⟨.num (.natN k), .num (.natN fields.length), ?_, ?_,
        cmpValues_geOp_natN_true_iff.2 hle⟩
      · exact evalExp_projE_iff.2 ⟨vs,
          evalExp_uncaseE_iff.2 (evalExp_varE_iff.2 (by simp)), by omega, hidx⟩
      · exact evalExp_lenE_iff.2 ⟨fields, evalExp_dotE_iff.2 ⟨arr,
          evalExp_idxE_iff.2 ⟨ais, kk,
            evalExp_callE_iff.2
              ((ExecNumeric.applies_iff_callDef rfl (hargs _ _ _ _ _)).1 hais),
            evalExp_varE_iff.2 (by simp), hidx'⟩, hfield⟩, rfl⟩

/-! ## The administrative contexts

`ctxt-label`, `ctxt-handler` and `ctxt-frame` are the congruence rules: a
step inside an administrative instruction is a step of the whole
configuration, with the administrative wrapper carried through unchanged.
They are premise-for-premise identical except for the wrapper, so the three
are proved the same way.

Each has exactly one premise, a `rulePr` of `Step` itself, so the
characterisation is stated with `Derives env "Step"` — these are the rules
that make `Step` recursive. -/

/-- `LABEL_n{instr_0*} instr*`. -/
def labelV (n : Value) (i0s is : List Value) : Value :=
  .case "LABEL_%{%}%" (.tuple [n, .list i0s, .list is])

/-- **`Step/ctxt-label`, characterised exactly.**  A step of `instr*` is a
step of `LABEL_n{instr_0*} instr*`, with `n` and `instr_0*` unchanged and the
state threaded through. -/
theorem ruleFires_ctxtLabel_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v ctxtLabelRule ↔
      ∃ z n i0s is z' js,
        v = .tuple [configV z [labelV n i0s is], configV z' [labelV n i0s js]] ∧
        Derives env "Step" "%~>%" [] (.tuple [configV z is, configV z' js]) := by
  unfold ctxtLabelRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    -- left: `z; [LABEL_n{instr_0*} instr*]`
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨z, lv, τ, rfl, hz, hlv⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨lvs, rfl, hlvs⟩ := Validation.matchExp_list_iff.1 hlv
    obtain ⟨l, rfl, hl'⟩ := matchExps_one_iff.1 hlvs
    obtain ⟨lw, rfl, hlw⟩ := Validation.matchExp_case_iff.1 hl'
    obtain ⟨lws, rfl, hlws⟩ := Validation.matchExp_tup_iff.1 hlw
    obtain ⟨n, i0v, iv, τ₁, τ₂, rfl, hn, hi0, hi⟩ := matchExps_three_iff.1 hlws
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr_0") (by simp) (by simp)] at hi0
    obtain ⟨i0s, rfl, hi0s⟩ := hi0
    rw [matchExp_freshVar_iff (by simp)] at hi0s
    subst hi0s
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hi
    obtain ⟨is, rfl, his⟩ := hi
    rw [matchExp_freshVar_iff (by simp)] at his
    subst his
    -- right: `z'; [LABEL_n{instr_0*} instr'*]`, with `n` and `instr_0*` bound
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨z', lv', υ, rfl, hz', hlv'⟩ := matchExps_two_iff.1 hbvs
    rw [matchExp_freshVar_iff (by simp)] at hz'
    subst hz'
    obtain ⟨lvs', rfl, hlvs'⟩ := Validation.matchExp_list_iff.1 hlv'
    obtain ⟨l', rfl, hl''⟩ := matchExps_one_iff.1 hlvs'
    obtain ⟨lw', rfl, hlw'⟩ := Validation.matchExp_case_iff.1 hl''
    obtain ⟨lws', rfl, hlws'⟩ := Validation.matchExp_tup_iff.1 hlw'
    obtain ⟨n', i0v', jv, τ₃, τ₄, rfl, hn', hi0', hj⟩ := matchExps_three_iff.1 hlws'
    rw [matchExp_boundVar_iff (w := n) (by simp)] at hn'
    obtain ⟨rfl, rfl⟩ := hn'
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr_0") (by simp) (by simp)] at hi0'
    obtain ⟨i0s', rfl, hi0s'⟩ := hi0'
    rw [matchExp_boundVar_iff (w := Value.list i0s) (by simp)] at hi0s'
    obtain ⟨hi0eq, rfl⟩ := hi0s'
    obtain rfl := Value.list.inj hi0eq
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr'") (by simp) (by simp)] at hj
    obtain ⟨js, rfl, hjs⟩ := hj
    rw [matchExp_freshVar_iff (by simp)] at hjs
    subst hjs
    -- the premise
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, ws, w, hws, hw, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    refine ⟨z, n', i0s', is, z', js, rfl, ?_⟩
    obtain rfl : w = .tuple [configV z is, configV z' js] := by
      refine EvalExp.unique hw ?_
      refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
    exact hder
  · rintro ⟨z, n, i0s, is, z', js, rfl, hder⟩
    refine ⟨(((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal
        "instr_0*" (.list i0s)).bindVal "instr*" (.list is)).bindVal "z'" z').bindVal
        "instr'*" (.list js),
      (((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal
        "instr_0*" (.list i0s)).bindVal "instr*" (.list is)).bindVal "z'" z').bindVal
        "instr'*" (.list js),
      matchExp_concl_iff.2 ⟨_, _, (((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal
        "instr_0*" (.list i0s)).bindVal "instr*" (.list is), rfl, ?_, ?_⟩, ?_⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                      (matchExp_freshVar_iff (by simp)).2 rfl,
                      (matchExp_iterE_list_iff (bindsVar_varE "instr_0")
                        (by simp) (by simp)).2
                        ⟨i0s, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
                      (matchExp_iterE_list_iff (bindsVar_varE "instr")
                        (by simp) (by simp)).2
                        ⟨is, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                      (matchExp_boundVar_iff (w := n) (by simp)).2 ⟨rfl, rfl⟩,
                      (matchExp_iterE_list_iff (bindsVar_varE "instr_0")
                        (by simp) (by simp)).2
                        ⟨i0s, rfl,
                          (matchExp_boundVar_iff (w := Value.list i0s)
                            (by simp)).2 ⟨rfl, rfl⟩⟩,
                      (matchExp_iterE_list_iff (bindsVar_varE "instr'")
                        (by simp) (by simp)).2
                        ⟨js, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_rule_iff.2
        ⟨rfl, [], .tuple [configV z is, configV z' js],
          Validation.evalArgs_nil_iff.2 rfl, ?_, hder⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩

/-- `HANDLER_n{catch*} instr*`. -/
def handlerV (n : Value) (cs is : List Value) : Value :=
  .case "HANDLER_%{%}%" (.tuple [n, .list cs, .list is])

/-- **`Step/ctxt-handler`, characterised exactly.**  Identical to `ctxt-label`
but for the wrapper: a step of `instr*` is a step of `HANDLER_n{catch*}
instr*`, with `n` and `catch*` unchanged and the state threaded through. -/
theorem ruleFires_ctxtHandler_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v ctxtHandlerRule ↔
      ∃ z n cs is z' js,
        v = .tuple [configV z [handlerV n cs is], configV z' [handlerV n cs js]] ∧
        Derives env "Step" "%~>%" [] (.tuple [configV z is, configV z' js]) := by
  unfold ctxtHandlerRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    -- left: `z; [LABEL_n{instr_0*} instr*]`
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨z, lv, τ, rfl, hz, hlv⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨lvs, rfl, hlvs⟩ := Validation.matchExp_list_iff.1 hlv
    obtain ⟨l, rfl, hl'⟩ := matchExps_one_iff.1 hlvs
    obtain ⟨lw, rfl, hlw⟩ := Validation.matchExp_case_iff.1 hl'
    obtain ⟨lws, rfl, hlws⟩ := Validation.matchExp_tup_iff.1 hlw
    obtain ⟨n, cv0, iv, τ₁, τ₂, rfl, hn, hi0, hi⟩ := matchExps_three_iff.1 hlws
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch") (by simp) (by simp)] at hi0
    obtain ⟨cs, rfl, hcs⟩ := hi0
    rw [matchExp_freshVar_iff (by simp)] at hcs
    subst hcs
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hi
    obtain ⟨is, rfl, his⟩ := hi
    rw [matchExp_freshVar_iff (by simp)] at his
    subst his
    -- right: `z'; [LABEL_n{instr_0*} instr'*]`, with `n` and `instr_0*` bound
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨z', lv', υ, rfl, hz', hlv'⟩ := matchExps_two_iff.1 hbvs
    rw [matchExp_freshVar_iff (by simp)] at hz'
    subst hz'
    obtain ⟨lvs', rfl, hlvs'⟩ := Validation.matchExp_list_iff.1 hlv'
    obtain ⟨l', rfl, hl''⟩ := matchExps_one_iff.1 hlvs'
    obtain ⟨lw', rfl, hlw'⟩ := Validation.matchExp_case_iff.1 hl''
    obtain ⟨lws', rfl, hlws'⟩ := Validation.matchExp_tup_iff.1 hlw'
    obtain ⟨n', cv0', jv, τ₃, τ₄, rfl, hn', hi0', hj⟩ := matchExps_three_iff.1 hlws'
    rw [matchExp_boundVar_iff (w := n) (by simp)] at hn'
    obtain ⟨rfl, rfl⟩ := hn'
    rw [matchExp_iterE_list_iff (bindsVar_varE "catch") (by simp) (by simp)] at hi0'
    obtain ⟨cs', rfl, hcs'⟩ := hi0'
    rw [matchExp_boundVar_iff (w := Value.list cs) (by simp)] at hcs'
    obtain ⟨hi0eq, rfl⟩ := hcs'
    obtain rfl := Value.list.inj hi0eq
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr'") (by simp) (by simp)] at hj
    obtain ⟨js, rfl, hjs⟩ := hj
    rw [matchExp_freshVar_iff (by simp)] at hjs
    subst hjs
    -- the premise
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, ws, w, hws, hw, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    refine ⟨z, n', cs', is, z', js, rfl, ?_⟩
    obtain rfl : w = .tuple [configV z is, configV z' js] := by
      refine EvalExp.unique hw ?_
      refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
    exact hder
  · rintro ⟨z, n, cs, is, z', js, rfl, hder⟩
    refine ⟨(((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal
        "catch*" (.list cs)).bindVal "instr*" (.list is)).bindVal "z'" z').bindVal
        "instr'*" (.list js),
      (((((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal
        "catch*" (.list cs)).bindVal "instr*" (.list is)).bindVal "z'" z').bindVal
        "instr'*" (.list js),
      matchExp_concl_iff.2 ⟨_, _, (((VarEnv.empty.bindVal "z" z).bindVal "n" n).bindVal
        "catch*" (.list cs)).bindVal "instr*" (.list is), rfl, ?_, ?_⟩, ?_⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                      (matchExp_freshVar_iff (by simp)).2 rfl,
                      (matchExp_iterE_list_iff (bindsVar_varE "catch")
                        (by simp) (by simp)).2
                        ⟨cs, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
                      (matchExp_iterE_list_iff (bindsVar_varE "instr")
                        (by simp) (by simp)).2
                        ⟨is, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                      (matchExp_boundVar_iff (w := n) (by simp)).2 ⟨rfl, rfl⟩,
                      (matchExp_iterE_list_iff (bindsVar_varE "catch")
                        (by simp) (by simp)).2
                        ⟨cs, rfl,
                          (matchExp_boundVar_iff (w := Value.list cs)
                            (by simp)).2 ⟨rfl, rfl⟩⟩,
                      (matchExp_iterE_list_iff (bindsVar_varE "instr'")
                        (by simp) (by simp)).2
                        ⟨js, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_rule_iff.2
        ⟨rfl, [], .tuple [configV z is, configV z' js],
          Validation.evalArgs_nil_iff.2 rfl, ?_, hder⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩

/-- `s; f`, the state as a store/frame pair.  This is the shape the runtime
bridge encodes: `Equiv/RuntimeBridge/Instances.lean`'s `storeToValue` and
`frameToValue` are exactly the two components. -/
def stateV (s f : Value) : Value := .case "%;%" (.tuple [s, f])

/-- `FRAME_n{f} instr*`. -/
def frameV (n f : Value) (is : List Value) : Value :=
  .case "FRAME_%{%}%" (.tuple [n, f, .list is])

/-- **`Step/ctxt-frame`, characterised exactly.**  This is the only rule of
`Step` that takes the state apart, and it does so only to swap the frame: the
premise steps the body under the *inner* frame `f'`, and the conclusion puts
the resulting store `s'` back under the *outer* frame `f`, carrying the
stepped inner frame `f''` into the wrapper.  Nothing about either frame's
contents is inspected, so this is still bridge-free. -/
theorem ruleFires_ctxtFrame_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v ctxtFrameRule ↔
      ∃ s f n f' is s' f'' js,
        v = .tuple [configV (stateV s f) [frameV n f' is],
                    configV (stateV s' f) [frameV n f'' js]] ∧
        Derives env "Step" "%~>%" []
          (.tuple [configV (stateV s f') is, configV (stateV s' f'') js]) := by
  unfold ctxtFrameRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨zv, fv, τ, rfl, hz, hfv⟩ := matchExps_two_iff.1 havs
    obtain ⟨zw, rfl, hzw⟩ := Validation.matchExp_case_iff.1 hz
    obtain ⟨zws, rfl, hzws⟩ := Validation.matchExp_tup_iff.1 hzw
    obtain ⟨s, f, τ₀, rfl, hs, hf⟩ := matchExps_two_iff.1 hzws
    rw [matchExp_freshVar_iff (by simp)] at hs
    subst hs
    rw [matchExp_freshVar_iff (by simp)] at hf
    subst hf
    obtain ⟨fvs, rfl, hfvs⟩ := Validation.matchExp_list_iff.1 hfv
    obtain ⟨fr, rfl, hfr⟩ := matchExps_one_iff.1 hfvs
    obtain ⟨frw, rfl, hfrw⟩ := Validation.matchExp_case_iff.1 hfr
    obtain ⟨frws, rfl, hfrws⟩ := Validation.matchExp_tup_iff.1 hfrw
    obtain ⟨n, f', iv, τ₁, τ₂, rfl, hn, hf', hi⟩ := matchExps_three_iff.1 hfrws
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_freshVar_iff (by simp)] at hf'
    subst hf'
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr") (by simp) (by simp)] at hi
    obtain ⟨is, rfl, his⟩ := hi
    rw [matchExp_freshVar_iff (by simp)] at his
    subst his
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨zv', fv', υ, rfl, hz', hfv'⟩ := matchExps_two_iff.1 hbvs
    obtain ⟨zw', rfl, hzw'⟩ := Validation.matchExp_case_iff.1 hz'
    obtain ⟨zws', rfl, hzws'⟩ := Validation.matchExp_tup_iff.1 hzw'
    obtain ⟨s', f₂, υ₀, rfl, hs', hf₂⟩ := matchExps_two_iff.1 hzws'
    rw [matchExp_freshVar_iff (by simp)] at hs'
    subst hs'
    rw [matchExp_boundVar_iff (w := f) (by simp)] at hf₂
    obtain ⟨rfl, rfl⟩ := hf₂
    obtain ⟨fvs', rfl, hfvs'⟩ := Validation.matchExp_list_iff.1 hfv'
    obtain ⟨fr', rfl, hfr'⟩ := matchExps_one_iff.1 hfvs'
    obtain ⟨frw', rfl, hfrw'⟩ := Validation.matchExp_case_iff.1 hfr'
    obtain ⟨frws', rfl, hfrws'⟩ := Validation.matchExp_tup_iff.1 hfrw'
    obtain ⟨n₂, f'', jv, υ₁, υ₂, rfl, hn₂, hf'', hj⟩ := matchExps_three_iff.1 hfrws'
    rw [matchExp_boundVar_iff (w := n) (by simp)] at hn₂
    obtain ⟨rfl, rfl⟩ := hn₂
    rw [matchExp_freshVar_iff (by simp)] at hf''
    subst hf''
    rw [matchExp_iterE_list_iff (bindsVar_varE "instr'") (by simp) (by simp)] at hj
    obtain ⟨js, rfl, hjs⟩ := hj
    rw [matchExp_freshVar_iff (by simp)] at hjs
    subst hjs
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, ws, w, hws, hw, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    refine ⟨s, f₂, n₂, f', is, s', f'', js, rfl, ?_⟩
    obtain rfl : w = .tuple [configV (stateV s f') is, configV (stateV s' f'') js] := by
      refine EvalExp.unique hw ?_
      refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
            evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
              Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
                Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
                  evalExp_varE_iff.2 (by simp),
                  Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩,
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
            evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
              Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
                Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
                  evalExp_varE_iff.2 (by simp),
                  Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩,
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
    exact hder
  · rintro ⟨s, f, n, f', is, s', f'', js, rfl, hder⟩
    refine ⟨((((((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "n" n).bindVal
        "f'" f').bindVal "instr*" (.list is)).bindVal "s'" s').bindVal
        "f''" f'').bindVal "instr'*" (.list js)),
      ((((((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "n" n).bindVal
        "f'" f').bindVal "instr*" (.list is)).bindVal "s'" s').bindVal
        "f''" f'').bindVal "instr'*" (.list js)),
      matchExp_concl_iff.2 ⟨_, _,
        ((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "n" n).bindVal
          "f'" f').bindVal "instr*" (.list is), rfl, ?_, ?_⟩, ?_⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_two_iff.2 ⟨_, _, _, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                      (matchExp_freshVar_iff (by simp)).2 rfl,
                      (matchExp_freshVar_iff (by simp)).2 rfl,
                      (matchExp_iterE_list_iff (bindsVar_varE "instr")
                        (by simp) (by simp)).2
                        ⟨is, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_two_iff.2 ⟨_, _, _, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl,
                  (matchExp_boundVar_iff (w := f) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                      (matchExp_boundVar_iff (w := n) (by simp)).2 ⟨rfl, rfl⟩,
                      (matchExp_freshVar_iff (by simp)).2 rfl,
                      (matchExp_iterE_list_iff (bindsVar_varE "instr'")
                        (by simp) (by simp)).2
                        ⟨js, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_rule_iff.2
        ⟨rfl, [], .tuple [configV (stateV s f') is, configV (stateV s' f'') js],
          Validation.evalArgs_nil_iff.2 rfl, ?_, hder⟩,
        Validation.premsHold_nil_iff.2 rfl⟩
      refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
            evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
              Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
                Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
                  evalExp_varE_iff.2 (by simp),
                  Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩,
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
      · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
            evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
              Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
                Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
                  evalExp_varE_iff.2 (by simp),
                  Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩,
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
              ExecStep.evalExp_instrIter (by simp) (by simp),
              Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩

/-! ## `ctxt-instrs`, and what its concatenation pattern actually binds

`ctxt-instrs` is the congruence rule for instruction sequences:

    z; val* instr* instr_1*  ~>  z'; val* instr'* instr_1*
      -- if  z; instr* ~> z'; instr'*  and  (val* ≠ ε ∨ instr_1* ≠ ε)

Its left-hand side is a `CatE` of three `*` iterations over domains the
pattern is itself about to bind, so **neither operand has a length**
(`patLen` fails on both: evaluating `val*` needs `val*`).  `matchExp` then
searches the splits in increasing order and takes the first that matches.

The first split always matches: `val*` is fresh, so it matches the empty
list, and the inner concatenation then does the same for `instr*`.  So the
pattern binds `val* = ε` and `instr* = ε` however long the sequence is, and
`instr_1*` takes all of it — `matchExp_ctxtInstrsLhs` proves this, and
`MatchExp.unique` makes it the *only* binding.

The consequence is in `ruleFires_ctxtInstrs_iff`: the rule's premise is
always a step **from the empty instruction sequence**, which is not something
any other rule of `Step` or `Step_read` produces.  So `ctxt-instrs` does not
decompose instruction sequences the way the prose rule it transcribes does.

This is a property of *our* reading, not of SpecTec: `eval.ml:923-932` splits
a concatenation only when one operand is a literal `ListE`, so at the pin the
clause does not apply at all and `eval.ml` would simply fail here.  The
search is our deliberate strengthening (see `Sem/Eval.lean`'s `matchExp`
docstring), and it is what makes the other concatenation patterns of the
reduction relation — `Step_pure/br-handler` and friends — match.  Here the
strengthening is not enough: a first-match search cannot express "split
wherever the premise can be discharged". -/

/-- Neither operand of `ctxt-instrs`'s left-hand side has a length, and the
first split matches, so the pattern binds the empty prefix. -/
theorem matchExp_ctxtInstrsLhs {env : Env} {ρ : VarEnv} {vs : List Value}
    (hv : ρ.findVal? "val" = none) (hv' : ρ.findVal? "val*" = none)
    (hi : ρ.findVal? "instr" = none) (hi' : ρ.findVal? "instr*" = none)
    (hj : ρ.findVal? "instr_1" = none) (hj' : ρ.findVal? "instr_1*" = none) :
    MatchExp env ρ
      (.catE (Execution.valsPat "val" "val*")
        (.catE (Execution.iterPat "instr" "instr*")
          (Execution.iterPat "instr_1" "instr_1*")))
      (.list vs)
      (((ρ.bindVal "val*" (.list [])).bindVal "instr*" (.list [])).bindVal
        "instr_1*" (.list vs)) := by
  refine Execution.matchExp_catE_ofSplit (k := 0)
    (σ := ρ.bindVal "val*" (.list []))
    (Execution.noPatLen_valsPat hv')
    (Execution.noPatLen_catE_left (Execution.noPatLen_iterPat hi'))
    (Nat.zero_le _) (fun i hlt => absurd hlt (Nat.not_lt_zero i)) ?_ ?_
  · simpa using Execution.matchExp_valsPat_fresh hv (by simp) hv' []
  · simp only [List.drop_zero]
    refine Execution.matchExp_catE_ofSplit (k := 0)
      (σ := (ρ.bindVal "val*" (.list [])).bindVal "instr*" (.list []))
      (Execution.noPatLen_iterPat (by simp [hi']))
      (Execution.noPatLen_iterPat (by simp [hj']))
      (Nat.zero_le _) (fun i hlt => absurd hlt (Nat.not_lt_zero i)) ?_ ?_
    · simpa using Execution.matchExp_iterPat_fresh (by simp [hi]) (by simp)
        (by simp [hi']) []
    · simpa using Execution.matchExp_iterPat_fresh (by simp [hj]) (by simp)
        (by simp [hj']) vs

/-! ### Two general facts about matching, used to invert the concatenation

Both belong beside `MatchFails` in `Equiv/Execution.lean`; they are here
because `ctxt-instrs` is the first rule that needs them. -/

/-- A `CatE` pattern matches only a list: the clause begins with
`Value.asList?` (`Sem/Eval.lean`'s `matchExp`, `CatE` case). -/
theorem matchExp_catE_isList {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : MatchExp env ρ (.catE e₁ e₂) v ρ') : ∃ us, v = .list us := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [Sem.matchExp] at h
  | succ n =>
    cases v with
    | list us => exact ⟨us, rfl⟩
    | _ => simp [Sem.matchExp, Value.asList?, Res.ofOption] at h

/-- A match cannot both succeed and definitely fail. -/
theorem not_matchExp_of_matchFails {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h₁ : MatchExp env ρ e v ρ') (h₂ : Execution.MatchFails env ρ e v) : False := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e₁ := Sem.matchExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have e₂ := Sem.matchExp_undef_of_le (Nat.le_max_right n₁ n₂) h₂
  rw [e₁] at e₂
  simp at e₂

/-- `patLen` for a bound `*` iteration, the analogue of
`Execution.patLen_valsPat_bound`. -/
theorem patLen_iterPat_bound {env : Env} {ρ : VarEnv} {x y : IL.Id} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? y = some (.list vs)) :
    ∃ m, Sem.patLen m env ρ (Execution.iterPat x y) = .ok vs.length := by
  obtain ⟨n, hn⟩ := ExecStep.evalExp_instrIter (env := env) hx h
  refine ⟨n + 1, ?_⟩
  simp only [Execution.iterPat] at hn ⊢
  simp [Sem.patLen, hn, Res.ofOption, Bind.bind, Except.bind, Value.len?]

/-- **The `CatE` clause, inverted when the left operand has a length.**  The
converse of `Execution.matchExp_catE_ofLeft`: the split is *forced*, so the
match succeeds exactly when both halves do at that split. -/
theorem matchExp_catE_leftLen_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp}
    {us : List Value} {k m : Nat} (hk : Sem.patLen m env ρ e₁ = .ok k)
    (hle : k ≤ us.length) :
    MatchExp env ρ (.catE e₁ e₂) (.list us) ρ' ↔
      ∃ σ, MatchExp env ρ e₁ (.list (us.take k)) σ ∧
        MatchExp env σ e₂ (.list (us.drop k)) ρ' := by
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨N, hmN, hnN⟩ : ∃ N, m ≤ N ∧ n ≤ N := ⟨max m n, by omega, by omega⟩
    have h' : Sem.matchExp (N + 1) env ρ (.catE e₁ e₂) (.list us) = .ok ρ' :=
      Sem.matchExp_ok_of_le (by omega) h
    have hk' : Sem.patLen N env ρ e₁ = .ok k :=
      ((Sem.monoAt_of_le hmN).patLen env ρ e₁).ok hk
    rw [Sem.matchExp] at h'
    simp only [Value.asList?, Res.ofOption, hk', Res.elimUndef,
      Res.bind_eq_ok] at h'
    obtain ⟨vs, hvs, h'⟩ := h'
    obtain rfl : us = vs := by injection hvs
    rw [Res.assert_pos hle, Res.bind_eq_ok] at h'
    obtain ⟨σ, hσ, hρ'⟩ := h'
    exact ⟨σ, ⟨N, hσ⟩, ⟨N, hρ'⟩⟩
  · rintro ⟨σ, h₁, h₂⟩
    exact Execution.matchExp_catE_ofLeft hk hle h₁ h₂

/-- **The `CatE` clause, inverted when only the *right* operand has a
length.**  The converse of `Execution.matchExp_catE_ofRight`. -/
theorem matchExp_catE_rightLen_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp}
    {us : List Value} {k m : Nat} (h₀ : Execution.NoPatLen env ρ e₁)
    (hk : Sem.patLen m env ρ e₂ = .ok k) (hle : k ≤ us.length) :
    MatchExp env ρ (.catE e₁ e₂) (.list us) ρ' ↔
      ∃ σ, MatchExp env ρ e₁ (.list (us.take (us.length - k))) σ ∧
        MatchExp env σ e₂ (.list (us.drop (us.length - k))) ρ' := by
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨n₀, hn₀⟩ := h₀
    obtain ⟨N, h₀N, hmN, hnN⟩ : ∃ N, n₀ ≤ N ∧ m ≤ N ∧ n ≤ N :=
      ⟨max (max n₀ m) n, by omega, by omega, by omega⟩
    have h' : Sem.matchExp (N + 1) env ρ (.catE e₁ e₂) (.list us) = .ok ρ' :=
      Sem.matchExp_ok_of_le (by omega) h
    have e0 : Sem.patLen N env ρ e₁ = .error .undef :=
      Execution.patLen_undef_of_le h₀N hn₀
    have hk' : Sem.patLen N env ρ e₂ = .ok k :=
      ((Sem.monoAt_of_le hmN).patLen env ρ e₂).ok hk
    rw [Sem.matchExp] at h'
    simp only [Value.asList?, Res.ofOption, e0, hk', Res.elimUndef,
      Res.bind_eq_ok] at h'
    obtain ⟨vs, hvs, h'⟩ := h'
    obtain rfl : us = vs := by injection hvs
    rw [Res.assert_pos hle, Res.bind_eq_ok] at h'
    obtain ⟨σ, hσ, hρ'⟩ := h'
    exact ⟨σ, ⟨N, hσ⟩, ⟨N, hρ'⟩⟩
  · rintro ⟨σ, h₁, h₂⟩
    exact Execution.matchExp_catE_ofRight h₀ hk hle h₁ h₂

/-- The length side condition of `matchExp_catE_rightLen_iff` is not an extra
assumption: a match that succeeds has it. -/
theorem le_of_matchExp_catE_rightLen {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ : Exp}
    {us : List Value} {k m : Nat} (h₀ : Execution.NoPatLen env ρ e₁)
    (hk : Sem.patLen m env ρ e₂ = .ok k)
    (h : MatchExp env ρ (.catE e₁ e₂) (.list us) ρ') : k ≤ us.length := by
  by_contra hlt
  exact not_matchExp_of_matchFails h
    (Execution.matchFails_catE_ofRight h₀ hk (Or.inl (by omega)))

/-- The right-hand side of `ctxt-instrs`, inverted.  `val*` is bound to `ε`,
so the outer split is forced at `0`; `instr_1*` is bound to `is`, so the inner
split is forced at the end, and the sequence has to end with `is`. -/
theorem matchExp_ctxtInstrsRhs_iff {env : Env} {ρ ρ' : VarEnv} {us is : List Value}
    (hv : ρ.findVal? "val" = none) (hv' : ρ.findVal? "val*" = some (.list []))
    (hi : ρ.findVal? "instr'" = none) (hi' : ρ.findVal? "instr'*" = none)
    (hj : ρ.findVal? "instr_1" = none) (hj' : ρ.findVal? "instr_1*" = some (.list is)) :
    MatchExp env ρ
      (.catE (Execution.valsPat "val" "val*")
        (.catE (Execution.iterPat "instr'" "instr'*")
          (Execution.iterPat "instr_1" "instr_1*")))
      (.list us) ρ' ↔
      ∃ js, us = js ++ is ∧ ρ' = ρ.bindVal "instr'*" (.list js) := by
  obtain ⟨m₁, hm₁⟩ := Execution.patLen_valsPat_bound (env := env) (x := "val") (by simp) hv'
  obtain ⟨m₂, hm₂⟩ := patLen_iterPat_bound (env := env) (x := "instr_1") (by simp) hj'
  simp only [List.length_nil] at hm₁
  rw [matchExp_catE_leftLen_iff hm₁ (Nat.zero_le _)]
  constructor
  · rintro ⟨σ, h₁, h₂⟩
    obtain rfl : ρ = σ :=
      (MatchExp.unique h₁
        (by simpa using Execution.matchExp_valsPat_bound hv (by simp) hv')).symm
    simp only [List.drop_zero] at h₂
    have hle := le_of_matchExp_catE_rightLen
      (Execution.noPatLen_iterPat hi') hm₂ h₂
    rw [matchExp_catE_rightLen_iff (Execution.noPatLen_iterPat hi') hm₂ hle] at h₂
    obtain ⟨τ, h₃, h₄⟩ := h₂
    obtain rfl : τ = VarEnv.bindVal ρ "instr'*"
        (Value.list (us.take (us.length - is.length))) :=
      MatchExp.unique h₃ (Execution.matchExp_iterPat_fresh hi (by simp) hi' _)
    have hdrop : us.drop (us.length - is.length) = is := by
      rw [Execution.iterPat, matchExp_iterE_list_iff
        (bindsVar_varE "instr_1") (by simp [hj]) (by simp)] at h₄
      obtain ⟨ws, hws, hb⟩ := h₄
      rw [matchExp_boundVar_iff (w := Value.list is) (by simp [hj'])] at hb
      obtain ⟨heq, -⟩ := hb
      obtain rfl := Value.list.inj heq
      exact Value.list.inj hws
    rw [hdrop] at h₄
    obtain rfl : ρ' = VarEnv.bindVal ρ "instr'*"
        (Value.list (us.take (us.length - is.length))) :=
      MatchExp.unique h₄
        (Execution.matchExp_iterPat_bound (by simp [hj]) (by simp) (by simp [hj']))
    refine ⟨us.take (us.length - is.length), ?_, rfl⟩
    have hsplit : us = us.take (us.length - is.length) ++ us.drop (us.length - is.length) :=
      (List.take_append_drop _ _).symm
    rw [hdrop] at hsplit
    exact hsplit
  · rintro ⟨js, rfl, rfl⟩
    refine ⟨ρ, by simpa using Execution.matchExp_valsPat_bound hv (by simp) hv', ?_⟩
    simp only [List.drop_zero]
    refine Execution.matchExp_catE_ofRight (Execution.noPatLen_iterPat hi') hm₂
      (σ := ρ.bindVal "instr'*" (Value.list js)) (by simp) ?_ ?_
    · simpa using Execution.matchExp_iterPat_fresh hi (by simp) hi' _
    · simpa using Execution.matchExp_iterPat_bound
        (ρ := ρ.bindVal "instr'*" (.list js)) (by simp [hj]) (by simp) (by simp [hj'])

/-- **`Step/ctxt-instrs`, characterised exactly** — and the characterisation
is the finding.  The rule's premise is always a step **from the empty
instruction sequence**, because the concatenation pattern binds `val* = ε`
and `instr* = ε` (`matchExp_ctxtInstrsLhs`), and `MatchExp` is deterministic
so no other binding is available.

So `ctxt-instrs` does not decompose an instruction sequence the way the prose
rule it transcribes does: it cannot select an active sub-sequence in the
middle, only the whole tail, and the step it then requires is one no other
rule of `Step` or `Step_read` produces.

This is a property of our reading of `CatE` patterns, not of SpecTec: at the
pin, `eval.ml:923-932` splits a concatenation only when one operand is a
literal `ListE`, so it would not match here at all.  The first-match search in
`Sem/Eval.lean`'s `matchExp` is our strengthening, and it is what makes the
other concatenation patterns of the reduction relation match; here it is not
enough, because a first-match search cannot express "split wherever the
premise can be discharged". -/
theorem ruleFires_ctxtInstrs_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v ctxtInstrsRule ↔
      ∃ z is z' js,
        v = .tuple [configV z is, configV z' (js ++ is)] ∧ is ≠ [] ∧
        Derives env "Step" "%~>%" [] (.tuple [configV z [], configV z' js]) := by
  unfold ctxtInstrsRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    -- left
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨z, cv, τ, rfl, hz, hc⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨is, rfl⟩ := matchExp_catE_isList hc
    obtain rfl : σ = ((((VarEnv.empty.bindVal "z" z).bindVal "val*"
        (Value.list [])).bindVal "instr*"
        (Value.list [])).bindVal "instr_1*" (Value.list is)) :=
      MatchExp.unique hc (matchExp_ctxtInstrsLhs (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp))
    -- right
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨z', cv', υ, rfl, hz', hc'⟩ := matchExps_two_iff.1 hbvs
    rw [matchExp_freshVar_iff (by simp)] at hz'
    subst hz'
    obtain ⟨us, rfl⟩ := matchExp_catE_isList hc'
    obtain ⟨js, rfl, rfl⟩ := (matchExp_ctxtInstrsRhs_iff (is := is) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)).1 hc'
    -- premises
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain ⟨rfl, ws, w, hws, hw, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    obtain ⟨κ', hguard, hnil⟩ := Validation.premsHold_cons_iff.1 hrest
    obtain rfl := Validation.premsHold_nil_iff.1 hnil
    obtain ⟨rfl, hev⟩ := Validation.premHolds_if_iff.1 hguard
    refine ⟨z, is, z', js, rfl, ?_, ?_⟩
    · -- the guard: `val* ≠ ε ∨ instr_1* ≠ ε`, and `val*` is `ε`
      intro hnil'
      subst hnil'
      rw [evalExp_binE_iff] at hev
      obtain ⟨b₁, hb₁, hrest'⟩ := hev
      obtain ⟨u₁, u₂, hu₁, hu₂, hc₁⟩ := evalExp_cmpE_iff.1 hb₁
      obtain rfl : u₁ = Value.list [] := by
        refine EvalExp.unique hu₁ ?_
        exact ExecStep.evalExp_instrIter (by simp) (by simp)
      obtain rfl : u₂ = Value.list [] := by
        refine EvalExp.unique hu₂ ?_
        exact evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩
      -- `val* ≠ ε` is false, so the disjunction cannot short-circuit
      obtain rfl : b₁ = Value.bool false := by
        simpa [Sem.cmpValues] using hc₁.symm
      rcases hrest' with hshort | ⟨-, b₂, hb₂, hbin⟩
      · simp [Sem.boolShort] at hshort
      obtain ⟨w₁, w₂, hw₁, hw₂, hc₂⟩ := evalExp_cmpE_iff.1 hb₂
      obtain rfl : w₁ = Value.list [] := by
        refine EvalExp.unique hw₁ ?_
        exact ExecStep.evalExp_instrIter (by simp) (by simp)
      obtain rfl : w₂ = Value.list [] := by
        refine EvalExp.unique hw₂ ?_
        exact evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩
      obtain rfl : b₂ = Value.bool false := by
        simpa [Sem.cmpValues] using hc₂.symm
      simp [Sem.binValues, Sem.boolBin] at hbin
    · obtain rfl : w = .tuple [configV z [], configV z' js] := by
        refine EvalExp.unique hw ?_
        refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
            Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
        · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
              Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
                ExecStep.evalExp_instrIter (by simp) (by simp),
                Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
        · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
              Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
                ExecStep.evalExp_instrIter (by simp) (by simp),
                Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
      exact hder
  · rintro ⟨z, is, z', js, rfl, hne, hder⟩
    refine ⟨(((((VarEnv.empty.bindVal "z" z).bindVal "val*" (Value.list [])).bindVal
      "instr*" (Value.list [])).bindVal "instr_1*" (Value.list is)).bindVal
      "z'" z').bindVal "instr'*" (Value.list js),
      (((((VarEnv.empty.bindVal "z" z).bindVal "val*" (Value.list [])).bindVal
      "instr*" (Value.list [])).bindVal "instr_1*" (Value.list is)).bindVal
      "z'" z').bindVal "instr'*" (Value.list js),
      matchExp_concl_iff.2 ⟨_, _, (((VarEnv.empty.bindVal "z" z).bindVal "val*" (Value.list [])).bindVal
      "instr*" (Value.list [])).bindVal "instr_1*" (Value.list is), rfl, ?_, ?_⟩, ?_⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            matchExp_ctxtInstrsLhs (by simp) (by simp) (by simp) (by simp)
              (by simp) (by simp)⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_ctxtInstrsRhs_iff (is := is) (by simp) (by simp) (by simp)
              (by simp) (by simp) (by simp)).2 ⟨js, rfl, rfl⟩⟩⟩⟩
    · refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_rule_iff.2
        ⟨rfl, [], .tuple [configV z [], configV z' js],
          Validation.evalArgs_nil_iff.2 rfl, ?_, hder⟩, ?_⟩
      · refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
            Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩
        · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
              Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
                ExecStep.evalExp_instrIter (by simp) (by simp),
                Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
        · exact evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨_,
            Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
              Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
                ExecStep.evalExp_instrIter (by simp) (by simp),
                Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩
      · refine Validation.premsHold_cons_iff.2 ⟨_,
          Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩, Validation.premsHold_nil_iff.2 rfl⟩
        refine evalExp_binE_iff.2 ⟨Value.bool false, ?_,
          Or.inr ⟨by simp [Sem.boolShort], Value.bool true, ?_,
            by simp [Sem.binValues, Sem.boolBin]⟩⟩
        · exact evalExp_cmpE_iff.2 ⟨Value.list [], Value.list [],
            ExecStep.evalExp_instrIter (by simp) (by simp),
            evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩, by simp [Sem.cmpValues]⟩
        · refine evalExp_cmpE_iff.2 ⟨Value.list is, Value.list [],
            ExecStep.evalExp_instrIter (by simp) (by simp),
            evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩, ?_⟩
          simpa [Sem.cmpValues] using hne

/-! ## Rules that cannot fire: variables only a solver could bind

`RulePr` **binds nothing**.  `eval.ml:687` returns `Ok None` for a relational
premise — SpecTec's own evaluator never decides one — and our `premHolds`
decides it by *evaluating* the asserted instance and asking `derives`, which
also binds nothing (`Sem/Eval.lean`, `premHolds`).  `IfPr` likewise only
evaluates.  So the only variables a rule has are the ones its **conclusion**
binds, and the conclusion binds only in *pattern* position: a variable that
appears solely inside a `CallE` argument, or solely in a premise, is never
bound.

Several `Step` rules are written as if a premise bound its output:
`table.grow-succeed` introduces `ti` and constrains it with
`ti = $growtable($table(z, x), n, ref)`; `memory.grow-succeed` does the same
with `mi`.  In both, `ti`/`mi` appear in the conclusion only as an argument of
`$with_tableinst`/`$with_meminst`, which `matchExp` reaches through
`matchDefault` — it evaluates.  Evaluating an unbound variable is `undef`, so
the conclusion cannot match anything and the rule cannot fire.

This is a reading of the pinned IL, not a claim about the W3C document: the
frontend reduces a rule through `il2al`, whose `translate.ml` turns such a
premise into an assignment.  What it says is that the pinned `--ast` stream
does not carry enough information to run these rules directly, which is the
same conclusion #881 reached about `hint(builtin)`. -/

/-- A `CallE` whose argument list mentions an unbound variable matches
nothing: `matchDefault` evaluates it, and evaluating an unbound variable is
`undef`. -/
theorem not_matchExp_callE3_of_unbound {env : Env} {ρ ρ' : VarEnv} {f : IL.Id}
    {e₁ e₂ : Exp} {y : IL.Id} {w : Value} (hy : ρ.findVal? y = none) :
    ¬ MatchExp env ρ (.callE f [.expA e₁, .expA e₂, .expA (.varE y)]) w ρ' := by
  intro h
  rw [ExecDefault.matchExp_callE_iff] at h
  obtain ⟨hcall, rfl⟩ := h
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, ws₁, rfl, -, h₁⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨-, ws₂, rfl, -, h₂⟩ := ExecRead.evalArgs_expA_cons_iff.1 h₁
  obtain ⟨v, ws₃, rfl, hv, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h₂
  rw [evalExp_varE_iff, hy] at hv
  simp at hv

/-- **`Step/table.grow-succeed` cannot fire at the pin.**  Its conclusion's
right-hand side is `$with_tableinst(z, x, ti); …`, and `ti` is bound by
nothing: the left-hand side does not mention it, and the only premise is
`ti = $growtable(…)`, an `IfPr`, which evaluates rather than binds. -/
theorem not_ruleFires_tableGrowSucceed_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v tableGrowSucceedRule := by
  unfold tableGrowSucceedRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ, rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  -- the left-hand side binds `z`, `ref`, `at`, `n` and `x`, and nothing else
  obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
  obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
  obtain ⟨z, iv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 hcvs
  rw [matchExp_freshVar_iff (by simp)] at hz
  subst hz
  obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 hi
  obtain ⟨ref, c, g, τ₁, τ₂, rfl, href, hc, hg⟩ := matchExps_three_iff.1 hivs
  rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at href
  subst href
  obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hc
  obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
  obtain ⟨atv, pc, τ₃, rfl, hat, hpc⟩ := matchExps_two_iff.1 hcws
  rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
  subst hat
  obtain ⟨pw, rfl, hpw⟩ := Validation.matchExp_case_iff.1 hpc
  obtain ⟨pws, rfl, hpws⟩ := Validation.matchExp_tup_iff.1 hpw
  obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hpws
  rw [matchExp_freshVar_iff (by simp)] at hn
  subst hn
  obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hg
  rw [matchExp_freshVar_iff (by simp)] at hx
  subst hx
  exact not_matchExp_callE3_of_unbound (by simp) hw

/-- **`Step/memory.grow-succeed` cannot fire at the pin**, for the same
reason: `mi` appears only as the third argument of `$with_meminst`. -/
theorem not_ruleFires_memoryGrowSucceed_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v memoryGrowSucceedRule := by
  unfold memoryGrowSucceedRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ, rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
  obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
  obtain ⟨z, iv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 hcvs
  rw [matchExp_freshVar_iff (by simp)] at hz
  subst hz
  obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 hi
  obtain ⟨c, g, τ₁, rfl, hc, hg⟩ := matchExps_two_iff.1 hivs
  obtain ⟨cw, rfl, hcw⟩ := Validation.matchExp_case_iff.1 hc
  obtain ⟨cws, rfl, hcws⟩ := Validation.matchExp_tup_iff.1 hcw
  obtain ⟨atv, pc, τ₂, rfl, hat, hpc⟩ := matchExps_two_iff.1 hcws
  rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
  subst hat
  obtain ⟨pw, rfl, hpw⟩ := Validation.matchExp_case_iff.1 hpc
  obtain ⟨pws, rfl, hpws⟩ := Validation.matchExp_tup_iff.1 hpw
  obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hpws
  rw [matchExp_freshVar_iff (by simp)] at hn
  subst hn
  obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hg
  rw [matchExp_freshVar_iff (by simp)] at hx
  subst hx
  exact not_matchExp_callE3_of_unbound (by simp) hw

/-! `Unbinds` and its closure lemmas live in `Equiv/Unbind.lean`, shared with
`Equiv/ExecReadAggregate.lean`. -/


/-- A `CallE` one of whose arguments cannot be evaluated matches nothing. -/
theorem not_matchExp_callE_of_argUnevaluable {env : Env} {ρ ρ' : VarEnv} {f : IL.Id}
    {pre : List Exp} {e : Exp} {w : Value}
    (he : ∀ u, ¬ EvalExp env ρ e u) :
    ¬ MatchExp env ρ (.callE f ((pre.map Arg.expA) ++ [.expA e])) w ρ' := by
  intro h
  rw [ExecDefault.matchExp_callE_iff] at h
  obtain ⟨hcall, rfl⟩ := h
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  clear * - hargs he
  induction pre generalizing ws with
  | nil =>
    obtain ⟨u, -, -, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
    exact he u hu
  | cons a pre ih =>
    obtain ⟨-, ws', rfl, -, hrest⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
    exact ih _ hrest

/-! ### The ten rules whose conclusion evaluates an unbound variable

Each follows the same three steps: the conclusion splits into a left-hand
side and a right-hand side; `unbinds` shows the left-hand side does not bind
the variable in question; and the right-hand side's `CallE` then has an
argument that cannot be evaluated.  `scripts/spectec_unbound_vars.py Step`
lists them and says where each variable occurs. -/

/-- **`Step/store-num-val` cannot fire at the pin.**  Its conclusion writes
`$with_mem(…, b*)`, and `b*` is named only by the premise
`b* = $nbytes_(nt, c)`, an `IfPr`, which evaluates rather than binds. -/
theorem not_ruleFires_storeNumVal_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v storeNumValRule := by
  unfold storeNumValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hb : σ.findVal? "b*" = none :=
    (show Unbinds env _ "b*" by unbinds) _ _ _ (by simp) hl
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ, rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  exact not_matchExp_callE_of_argUnevaluable
    (pre := [.varE "z", .varE "x",
      .binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0),
      .cvtE (.binE .divOp (.numT .ratT)
        (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT])
    (fun _ => ExecReadControl.not_evalExp_iterE_of_unbound hb) hw

/-- **`Step/store-pack-val` cannot fire at the pin**, for the same reason as
`store-num-val`: the bytes it writes are named only by the premise. -/
theorem not_ruleFires_storePackVal_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v storePackValRule := by
  unfold storePackValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hb : σ.findVal? "b*" = none :=
    (show Unbinds env _ "b*" by unbinds) _ _ _ (by simp) hl
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ, rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, _, rfl, -, h1⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨-, _, rfl, -, h2⟩ := ExecRead.evalArgs_expA_cons_iff.1 h1
  obtain ⟨-, _, rfl, -, h3⟩ := ExecRead.evalArgs_expA_cons_iff.1 h2
  obtain ⟨-, _, rfl, -, h4⟩ := ExecRead.evalArgs_expA_cons_iff.1 h3
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h4
  exact ExecReadControl.not_evalExp_iterE_of_unbound hb hu

/-- **`Step/vstore-val` cannot fire at the pin**, for the same reason as
`store-num-val`: the bytes it writes are named only by the premise. -/
theorem not_ruleFires_vstoreVal_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v vstoreValRule := by
  unfold vstoreValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hb : σ.findVal? "b*" = none :=
    (show Unbinds env _ "b*" by unbinds) _ _ _ (by simp) hl
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ, rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, _, rfl, -, h1⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨-, _, rfl, -, h2⟩ := ExecRead.evalArgs_expA_cons_iff.1 h1
  obtain ⟨-, _, rfl, -, h3⟩ := ExecRead.evalArgs_expA_cons_iff.1 h2
  obtain ⟨-, _, rfl, -, h4⟩ := ExecRead.evalArgs_expA_cons_iff.1 h3
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h4
  exact ExecReadControl.not_evalExp_iterE_of_unbound hb hu

/-- **`Step/vstore_lane-val` cannot fire at the pin**, for the same reason as
`store-num-val`: the bytes it writes are named only by the premise. -/
theorem not_ruleFires_vstoreLaneVal_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v vstoreLaneValRule := by
  unfold vstoreLaneValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hb : σ.findVal? "b*" = none :=
    (show Unbinds env _ "b*" by unbinds) _ _ _ (by simp) hl
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ, rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, _, rfl, -, h1⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨-, _, rfl, -, h2⟩ := ExecRead.evalArgs_expA_cons_iff.1 h1
  obtain ⟨-, _, rfl, -, h3⟩ := ExecRead.evalArgs_expA_cons_iff.1 h2
  obtain ⟨-, _, rfl, -, h4⟩ := ExecRead.evalArgs_expA_cons_iff.1 h3
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h4
  exact ExecReadControl.not_evalExp_iterE_of_unbound hb hu

/-- **`Step/array.set-array` cannot fire at the pin.**  Its conclusion writes
`$packfield_(zt, …)`, and `zt` is named only by the `Expand` premise,
which — being a `RulePr` — evaluates rather than binds. -/
theorem not_ruleFires_arraySetArray_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arraySetArrayRule := by
  unfold arraySetArrayRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hb : σ.findVal? "zt" = none :=
    (show Unbinds env _ "zt" by unbinds) _ _ _ (by simp) hl
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ, rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, _, rfl, -, h1⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨-, _, rfl, -, h2⟩ := ExecRead.evalArgs_expA_cons_iff.1 h1
  obtain ⟨-, _, rfl, -, h3⟩ := ExecRead.evalArgs_expA_cons_iff.1 h2
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h3
  rw [evalExp_callE_iff, ExecNumeric.callDef_iff] at hu
  obtain ⟨ws', ps', t', cs', hargs', -, -⟩ := hu
  obtain ⟨u', _, rfl, hu', -⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs'
  rw [evalExp_varE_iff, hb] at hu'
  simp at hu'

/-- **`Step/struct.set-struct` cannot fire at the pin.**  Its conclusion writes
`$packfield_(zt*, …)`, and `zt*` is named only by the `Expand` premise,
which — being a `RulePr` — evaluates rather than binds. -/
theorem not_ruleFires_structSetStruct_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v structSetStructRule := by
  unfold structSetStructRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hb : σ.findVal? "zt*" = none :=
    (show Unbinds env _ "zt*" by unbinds) _ _ _ (by simp) hl
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ, rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, _, rfl, -, h1⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨-, _, rfl, -, h2⟩ := ExecRead.evalArgs_expA_cons_iff.1 h1
  obtain ⟨-, _, rfl, -, h3⟩ := ExecRead.evalArgs_expA_cons_iff.1 h2
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h3
  rw [evalExp_callE_iff, ExecNumeric.callDef_iff] at hu
  obtain ⟨ws', ps', t', cs', hargs', -, -⟩ := hu
  obtain ⟨u', _, rfl, hu', -⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs'
  rw [evalExp_idxE_iff] at hu'
  obtain ⟨_, _, hit, -, -⟩ := hu'
  exact ExecReadControl.not_evalExp_iterE_of_unbound hb hit

/-! ## The four `-oob` store rules

These are the only `Step` rules left that can fire.  Their guard is

    (i!)_0 + (ao.OFFSET!)_0 + $(⌊$size(nt)/8⌋ : nat)  >  |$mem(z, x).BYTES|

and the third summand is a **narrowing** `rat -> nat` — one of the 103 the
census counts (`docs/projects/spectec-divergences.md`).
`Num.cvt .natT (.ratN q)` is defined only when `q.den = 1 ∧ 0 ≤ q.num`, so
the guard — and with it the whole rule — is undefined unless `$size(nt)` is a
multiple of 8.  That is "safe by value" at the pin, since `$size` returns 32,
64 or 128, but it is a property of `$size`'s clauses, not of the rule, and
`SizeBytes` states it as such rather than assuming it. -/

/-- `$size(nt)/8`, narrowed back to `nat`, is `w`. -/
def SizeBytes (env : Env) (nt : Value) (w : Nat) : Prop :=
  ∃ sz : Num, ∃ q : Rat,
    ExecNumeric.Applies env "size" [.val nt] (.num sz) ∧
    Sem.Num.cvt .ratT sz = some (.ratN q) ∧
    Sem.Num.cvt .natT (.ratN (q / 8)) = some (.natN w)

/-- `$mem(z, x).BYTES` has `m` bytes. -/
def MemBytesLen (env : Env) (z x : Value) (m : Nat) : Prop :=
  ∃ mem bytes, ExecNumeric.Applies env "mem" [.val z, .val x] mem ∧
    mem.field? "BYTES" = some (.list bytes) ∧ bytes.length = m

/-- The static offset a `memarg` carries. -/
def OffsetNat (ao : Value) (off : Nat) : Prop :=
  ∃ o, ao.field? "OFFSET" = some o ∧ AddrNat o off

/-- **The guard the four `-oob` store rules share**, for an arbitrary scope and
an arbitrary expression naming the width.  The three facts that matter are
the same in all four: the index and the offset must be `%`-wrapped `nat`s, the
width must survive the narrowing `rat -> nat`, and the sum must exceed the
memory's length.  `SZ` abstracts over how the width is named — `$size(nt)` for
the two `store` rules, `$vsize(V128)` for `vstore`, a bound variable for
`store-pack` and `vstore_lane`. -/
theorem premsHold_storeGuard_iff {env : Env} {ρ ρ' : VarEnv} {esz : Exp}
    {SZ : Value → Prop} {z x i ao : Value}
    (hz : ρ.findVal? "z" = some z) (hx : ρ.findVal? "x" = some x)
    (hi : ρ.findVal? "i" = some i) (hao : ρ.findVal? "ao" = some ao)
    (hmd : ρ.findDef? "mem" = none)
    (hsz : ∀ u, EvalExp env ρ esz u ↔ SZ u) :
    PremsHold env ρ
      [.ifPr (.cmpE .gtOp (.numT .natT)
        (.binE .addOp (.numT .natT)
          (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
            (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
          (.cvtE (.binE .divOp (.numT .ratT) (.cvtE esz .natT .ratT)
            (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
        (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")])
          "BYTES")))]
      ρ' ↔
      ρ' = ρ ∧
      ∃ k off w m, AddrNat i k ∧ OffsetNat ao off ∧
        (∃ sz q, SZ (.num sz) ∧ Num.cvt .ratT sz = some (.ratN q) ∧
          Num.cvt .natT (.ratN (q / 8)) = some (.natN w)) ∧
        MemBytesLen env z x m ∧ m < k + off + w := by
  have hmem : EvalArgs env ρ [.expA (.varE "z"), .expA (.varE "x")] [.val z, .val x] :=
    evalArgs_cons (evalExp_varE_iff.2 hz)
      (evalArgs_cons (evalExp_varE_iff.2 hx) evalArgs_nil)
  constructor
  · rintro h
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 h
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨hκ, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨lhs, rhs, hl, hr, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨bytes, hbytes, rfl⟩ := evalExp_lenE_iff.1 hr
    obtain ⟨mem, hmemv, hfield⟩ := evalExp_dotE_iff.1 hbytes
    rw [evalExp_callE_iff] at hmemv
    obtain ⟨p, rfl⟩ : ∃ p : Nat, lhs = .num (.natN p) := by
      cases lhs with
      | num m =>
        cases m with
        | natN p => exact ⟨p, rfl⟩
        | _ => simp [Sem.cmpValues, Sem.Num.cmp, Res.ofOption] at hcmp
      | _ => simp [Sem.cmpValues] at hcmp
    rw [evalExp_binE_iff] at hl
    obtain ⟨s₁, hs₁, hrest₁⟩ := hl
    rcases hrest₁ with hshort | ⟨-, s₂, hs₂, hbin⟩
    · simp [ExecReadTable.boolShort_addOp] at hshort
    obtain ⟨sum, w, rfl, rfl, rfl⟩ := ExecReadTable.binValues_add_eq_natN hbin
    rw [evalExp_binE_iff] at hs₁
    obtain ⟨t₁, ht₁, hrest₂⟩ := hs₁
    rcases hrest₂ with hshort | ⟨-, t₂, ht₂, hbin'⟩
    · simp [ExecReadTable.boolShort_addOp] at hshort
    obtain ⟨k, off, rfl, rfl, rfl⟩ := ExecReadTable.binValues_add_eq_natN hbin'
    obtain ⟨vs, huc, -, hidx⟩ := evalExp_projE_iff.1 ht₁
    rw [evalExp_uncaseE_iff, evalExp_varE_iff, hi] at huc
    obtain rfl := Option.some.inj huc
    obtain ⟨vs', huc', -, hidx'⟩ := evalExp_projE_iff.1 ht₂
    rw [evalExp_uncaseE_iff] at huc'
    obtain ⟨o, ho, hofield⟩ := evalExp_dotE_iff.1 huc'
    rw [evalExp_varE_iff, hao] at ho
    obtain rfl := Option.some.inj ho
    obtain ⟨q, w', hq, hcvt, hw'⟩ := evalExp_cvtE_iff.1 hs₂
    obtain rfl : w' = .natN w := by simpa using hw'.symm
    rw [evalExp_binE_iff] at hq
    obtain ⟨r₁, hr₁, hrest₃⟩ := hq
    rcases hrest₃ with hshort | ⟨-, r₂, hr₂, hdiv⟩
    · simp [Sem.boolShort] at hshort
    obtain ⟨sz, sz', hszv, hszcvt, rfl⟩ := evalExp_cvtE_iff.1 hr₁
    obtain ⟨e₈, e₈', he₈, he₈cvt, rfl⟩ := evalExp_cvtE_iff.1 hr₂
    obtain rfl : e₈ = .natN 8 := by
      have h8 : EvalExp env ρ (.numE (.natN 8)) (.num (.natN 8)) := evalExp_num
      simpa using EvalExp.unique he₈ h8
    have hSZ := (hsz _).1 hszv
    obtain ⟨qs, rfl⟩ : ∃ qs : Rat, sz' = .ratN qs := by
      cases sz with
      | natN n => exact ⟨n, by simpa [Sem.Num.cvt] using hszcvt.symm⟩
      | intN n => exact ⟨n, by simpa [Sem.Num.cvt] using hszcvt.symm⟩
      | ratN n => exact ⟨n, by simpa [Sem.Num.cvt] using hszcvt.symm⟩
      | realN n => simp [Sem.Num.cvt] at hszcvt
    simp only [Sem.Num.cvt] at he₈cvt
    obtain rfl := Option.some.inj he₈cvt
    obtain rfl : q = .ratN (qs / 8) := by
      simpa [Sem.binValues, Sem.Num.bin, Res.ofOption,
        show ¬ ((8 : Nat) : Rat) = 0 by decide] using hdiv.symm
    refine ⟨hκ, k, off, w, bytes.length, ⟨vs, rfl, hidx⟩,
      ⟨_, hofield, vs', rfl, hidx'⟩, ⟨sz, qs, hSZ, hszcvt, by simpa using hcvt⟩,
      ⟨mem, bytes, (ExecNumeric.applies_iff_callDef hmd hmem).2 hmemv, hfield, rfl⟩, ?_⟩
    obtain ⟨pp, hpp, hlt⟩ := ExecReadAggregate.cmpValues_gtNat_true_iff.1 hcmp
    simp only [Value.num.injEq] at hpp
    obtain rfl : k + off + w = pp := by cases hpp; rfl
    omega
  · rintro ⟨rfl, k, off, w, m, ⟨vs, rfl, hidx⟩, ⟨o, hofield, vs', ho, hidx'⟩,
      ⟨szv, qs, hSZ, hszratcvt, hszcvt⟩,
      ⟨mem, bytes, hmemapp, hfield, rfl⟩, hlt⟩
    refine Validation.premsHold_cons_iff.2 ⟨_,
      Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩, Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.num (.natN (k + off + w)), .num (.natN bytes.length),
      ?_, ?_, ExecReadAggregate.cmpValues_gtNat_true_iff.2 ⟨_, rfl, hlt⟩⟩
    · refine evalExp_binE_iff.2 ⟨.num (.natN (k + off)), ?_,
        Or.inr ⟨by simp [Sem.boolShort], .num (.natN w), ?_,
          by simp [Sem.binValues, Sem.Num.bin, Res.ofOption]⟩⟩
      · refine evalExp_binE_iff.2 ⟨.num (.natN k), ?_,
          Or.inr ⟨by simp [Sem.boolShort], .num (.natN off), ?_,
            by simp [Sem.binValues, Sem.Num.bin, Res.ofOption]⟩⟩
        · exact evalExp_projE_iff.2 ⟨vs,
            evalExp_uncaseE_iff.2 (evalExp_varE_iff.2 hi), by omega, hidx⟩
        · refine evalExp_projE_iff.2 ⟨vs', ?_, by omega, hidx'⟩
          exact evalExp_uncaseE_iff.2 (evalExp_dotE_iff.2 ⟨ao,
            evalExp_varE_iff.2 hao, ho ▸ hofield⟩)
      · refine evalExp_cvtE_iff.2 ⟨.ratN (qs / 8), .natN w, ?_, hszcvt, rfl⟩
        refine evalExp_binE_iff.2 ⟨.num (.ratN qs), ?_,
          Or.inr ⟨by simp [Sem.boolShort], .num (.ratN ((8 : Nat) : Rat)), ?_, ?_⟩⟩
        · exact evalExp_cvtE_iff.2 ⟨szv, .ratN qs, (hsz _).2 hSZ, hszratcvt, rfl⟩
        · exact evalExp_cvtE_iff.2 ⟨.natN 8, .ratN ((8 : Nat) : Rat), evalExp_num,
            by simp [Sem.Num.cvt], rfl⟩
        · simp [Sem.binValues, Sem.Num.bin, Res.ofOption]
    · exact evalExp_lenE_iff.2 ⟨bytes, evalExp_dotE_iff.2 ⟨mem,
        evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef hmd hmem).1 hmemapp),
        hfield⟩, rfl⟩

/-- The guard of `store-num-oob`: `premsHold_storeGuard_iff` with `$size(nt)`
for the width. -/
theorem premsHold_storeNumGuard_iff {env : Env} {ρ' : VarEnv}
    {z atv i nt c x ao : Value} :
    PremsHold env
      (((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
      "nt" nt).bindVal "c" c).bindVal "x" x).bindVal "ao" ao)
      [.ifPr (.cmpE .gtOp (.numT .natT)
        (.binE .addOp (.numT .natT)
          (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
            (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
          (.cvtE (.binE .divOp (.numT .ratT)
            (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
            (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
        (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")])
          "BYTES")))]
      ρ' ↔
      ρ' = (((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
      "nt" nt).bindVal "c" c).bindVal "x" x).bindVal "ao" ao) ∧
      ∃ k off w m, AddrNat i k ∧ OffsetNat ao off ∧ SizeBytes env nt w ∧
        MemBytesLen env z x m ∧ m < k + off + w :=
  premsHold_storeGuard_iff (z := z) (x := x) (i := i) (ao := ao)
    (SZ := fun u => ExecNumeric.Applies env "size" [.val nt] u)
    (by simp) (by simp) (by simp) (by simp) rfl
    (fun u => by
      rw [evalExp_callE_iff]
      exact (ExecNumeric.applies_iff_callDef rfl
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).symm)

/-- **`Step/store-num-oob`, characterised exactly.**  The access is at or past
the end of the memory, and the configuration traps with the state unchanged.
Note what the guard *forces*: the index and the `memarg`'s offset must be a
`%` whose payload is a `nat`, and `$size(nt)` must be an eighth of a `nat`, or
the guard is undefined and the rule does not fire at all. -/
theorem ruleFires_storeNumOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v storeNumOobRule ↔
      ∃ z atv i nt c x ao k off w m,
        v = .tuple [configV z [Execution.constV atv i, Execution.constV nt c,
                      .case "STORE" (.tuple [nt, .opt none, x, ao])],
                    configV z [Execution.trapV]] ∧
        AddrNat i k ∧ OffsetNat ao off ∧ SizeBytes env nt w ∧
        MemBytesLen env z x m ∧ m < k + off + w := by
  unfold storeNumOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨c₁, c₂, st, τ₁, τ₂, rfl, h₁, h₂, hst⟩ := matchExps_three_iff.1 hivs
    obtain ⟨w₁, rfl, hw₁⟩ := Validation.matchExp_case_iff.1 h₁
    obtain ⟨ws₁, rfl, hws₁⟩ := Validation.matchExp_tup_iff.1 hw₁
    obtain ⟨atv, i, τ₃, rfl, hat, hi⟩ := matchExps_two_iff.1 hws₁
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
    subst hat
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨w₂, rfl, hw₂⟩ := Validation.matchExp_case_iff.1 h₂
    obtain ⟨ws₂, rfl, hws₂⟩ := Validation.matchExp_tup_iff.1 hw₂
    obtain ⟨nt, c, τ₄, rfl, hnt, hc⟩ := matchExps_two_iff.1 hws₂
    rw [matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨w₃, rfl, hw₃⟩ := Validation.matchExp_case_iff.1 hst
    obtain ⟨ws₃, rfl, hws₃⟩ := Validation.matchExp_tup_iff.1 hw₃
    obtain ⟨nt', opt, x, ao, τ₅, τ₆, τ₇, rfl, hnt', hopt, hx, hao⟩ :=
      matchExps_four_iff.1 hws₃
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt'
    obtain ⟨rfl, rfl⟩ := hnt'
    rw [Validation.matchExp_optNone_iff] at hopt
    obtain ⟨rfl, rfl⟩ := hopt
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    subst hao
    obtain ⟨rfl, rfl⟩ := (matchExp_trapRhs_iff (z := z) (by simp)).1 hr
    obtain ⟨rfl, k, off, w, m, haddr, hoff, hsize, hmem, hlt⟩ :=
      premsHold_storeNumGuard_iff.1 hp
    exact ⟨z, atv, i, nt', c, x, ao, k, off, w, m, rfl, haddr, hoff, hsize, hmem, hlt⟩
  · rintro ⟨z, atv, i, nt, c, x, ao, k, off, w, m, rfl, haddr, hoff, hsize, hmem, hlt⟩
    refine ⟨((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
      "nt" nt).bindVal "c" c).bindVal "x" x).bindVal "ao" ao, ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
      "nt" nt).bindVal "c" c).bindVal "x" x).bindVal "ao" ao,
      matchExp_concl_iff.2 ⟨_, _, ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
      "nt" nt).bindVal "c" c).bindVal "x" x).bindVal "ao" ao, rfl, ?_,
        (matchExp_trapRhs_iff (z := z) (by simp)).2 ⟨rfl, rfl⟩⟩,
      premsHold_storeNumGuard_iff.2
        ⟨rfl, k, off, w, m, haddr, hoff, hsize, hmem, hlt⟩⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, (VarEnv.empty.bindVal "z" z), rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨_, _, _, (((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i), (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "nt" nt).bindVal "c" c), rfl, ?_, ?_, ?_⟩⟩⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, ((VarEnv.empty.bindVal "z" z).bindVal "at" atv), rfl,
            Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "nt" nt), rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_four_iff.2 ⟨_, _, _, _, (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "nt" nt).bindVal "c" c), (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "nt" nt).bindVal "c" c), ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "nt" nt).bindVal "c" c).bindVal "x" x), rfl,
            (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
            Validation.matchExp_optNone_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩

/-- `$vsize(V128)/8`, narrowed back to `nat`, is `w` — the `vstore` analogue of
`SizeBytes`, with the same partial narrowing. -/
def VSizeBytes (env : Env) (w : Nat) : Prop :=
  ∃ sz q, ExecNumeric.Applies env "vsize"
      [.val (Execution.caseNilV "V128")] (.num sz) ∧
    Num.cvt .ratT sz = some (.ratN q) ∧
    Num.cvt .natT (.ratN (q / 8)) = some (.natN w)

/-- **`Step/vstore-oob`, characterised exactly.**  The same guard as
`store-num-oob`, with `$vsize(V128)` for `$size(nt)`. -/
theorem ruleFires_vstoreOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vstoreOobRule ↔
      ∃ z atv i c x ao k off w m,
        v = .tuple [configV z [Execution.constV atv i,
                      .case "VCONST" (.tuple [Execution.caseNilV "V128", c]),
                      .case "VSTORE" (.tuple [Execution.caseNilV "V128", x, ao])],
                    configV z [Execution.trapV]] ∧
        AddrNat i k ∧ OffsetNat ao off ∧ VSizeBytes env w ∧
        MemBytesLen env z x m ∧ m < k + off + w := by
  have hsz : ∀ (z atv i c x ao : Value) (u : Value),
      EvalExp env ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "x" x).bindVal "ao" ao) (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]) u ↔
        ExecNumeric.Applies env "vsize" [.val (Execution.caseNilV "V128")] u := by
    intro z atv i c x ao u
    rw [evalExp_callE_iff]
    exact (ExecNumeric.applies_iff_callDef rfl
      (evalArgs_cons (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2
        ⟨_, Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩) evalArgs_nil)).symm
  unfold vstoreOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨c₁, c₂, st, τ₁, τ₂, rfl, h₁, h₂, hst⟩ := matchExps_three_iff.1 hivs
    obtain ⟨w₁, rfl, hw₁⟩ := Validation.matchExp_case_iff.1 h₁
    obtain ⟨ws₁, rfl, hws₁⟩ := Validation.matchExp_tup_iff.1 hw₁
    obtain ⟨atv, i, τ₃, rfl, hat, hi⟩ := matchExps_two_iff.1 hws₁
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
    subst hat
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨w₂, rfl, hw₂⟩ := Validation.matchExp_case_iff.1 h₂
    obtain ⟨ws₂, rfl, hws₂⟩ := Validation.matchExp_tup_iff.1 hw₂
    obtain ⟨vt, c, τ₄, rfl, hvt, hc⟩ := matchExps_two_iff.1 hws₂
    rw [Execution.matchExp_caseNil_iff] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨w₃, rfl, hw₃⟩ := Validation.matchExp_case_iff.1 hst
    obtain ⟨ws₃, rfl, hws₃⟩ := Validation.matchExp_tup_iff.1 hw₃
    obtain ⟨vt', x, ao, τ₅, τ₆, rfl, hvt', hx, hao⟩ := matchExps_three_iff.1 hws₃
    rw [Execution.matchExp_caseNil_iff] at hvt'
    obtain ⟨rfl, rfl⟩ := hvt'
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    subst hao
    obtain ⟨rfl, rfl⟩ := (matchExp_trapRhs_iff (z := z) (by simp)).1 hr
    obtain ⟨rfl, k, off, w, m, haddr, hoff, hsize, hmem, hlt⟩ :=
      (premsHold_storeGuard_iff (z := z) (x := x) (i := i) (ao := ao)
        (SZ := fun u => ExecNumeric.Applies env "vsize"
          [.val (Execution.caseNilV "V128")] u)
        (by simp) (by simp) (by simp) (by simp) rfl (hsz z atv i c x ao)).1 hp
    exact ⟨z, atv, i, c, x, ao, k, off, w, m, rfl, haddr, hoff, hsize, hmem, hlt⟩
  · rintro ⟨z, atv, i, c, x, ao, k, off, w, m, rfl, haddr, hoff, hsize, hmem, hlt⟩
    refine ⟨((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "x" x).bindVal "ao" ao), ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "x" x).bindVal "ao" ao),
      matchExp_concl_iff.2 ⟨_, _, ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "x" x).bindVal "ao" ao), rfl, ?_,
        (matchExp_trapRhs_iff (z := z) (by simp)).2 ⟨rfl, rfl⟩⟩,
      (premsHold_storeGuard_iff (z := z) (x := x) (i := i) (ao := ao)
        (SZ := fun u => ExecNumeric.Applies env "vsize"
          [.val (Execution.caseNilV "V128")] u)
        (by simp) (by simp) (by simp) (by simp) rfl (hsz z atv i c x ao)).2
        ⟨rfl, k, off, w, m, haddr, hoff, hsize, hmem, hlt⟩⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, (VarEnv.empty.bindVal "z" z), rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨_, _, _, (((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i), ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c), rfl, ?_, ?_, ?_⟩⟩⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, ((VarEnv.empty.bindVal "z" z).bindVal "at" atv), rfl,
            Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, (((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i), rfl,
            Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_three_iff.2 ⟨_, _, _, ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c), (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "x" x), rfl,
            Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩

/-- `$(N/8 : nat)` is `w`, for a width the rule binds rather than computes. -/
def WidthBytes (nv : Value) (w : Nat) : Prop :=
  ∃ sz q, nv = .num sz ∧ Num.cvt .ratT sz = some (.ratN q) ∧
    Num.cvt .natT (.ratN (q / 8)) = some (.natN w)

/-- **`Step/vstore_lane-oob`, characterised exactly.**  The width is the `N`
the instruction carries, so the narrowing bites directly on it: the rule does
not fire unless `N` is a numeral that `rat -> nat` accepts after division. -/
theorem ruleFires_vstoreLaneOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vstoreLaneOobRule ↔
      ∃ z atv i c nv x ao j k off w m,
        v = .tuple [configV z [Execution.constV atv i,
                      .case "VCONST" (.tuple [Execution.caseNilV "V128", c]),
                      .case "VSTORE_LANE" (.tuple [Execution.caseNilV "V128",
                        .case "%" (.tuple [nv]), x, ao, j])],
                    configV z [Execution.trapV]] ∧
        AddrNat i k ∧ OffsetNat ao off ∧ WidthBytes nv w ∧
        MemBytesLen env z x m ∧ m < k + off + w := by
  unfold vstoreLaneOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨c₁, c₂, st, τ₁, τ₂, rfl, h₁, h₂, hst⟩ := matchExps_three_iff.1 hivs
    obtain ⟨w₁, rfl, hw₁⟩ := Validation.matchExp_case_iff.1 h₁
    obtain ⟨ws₁, rfl, hws₁⟩ := Validation.matchExp_tup_iff.1 hw₁
    obtain ⟨atv, i, τ₃, rfl, hat, hi⟩ := matchExps_two_iff.1 hws₁
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
    subst hat
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨w₂, rfl, hw₂⟩ := Validation.matchExp_case_iff.1 h₂
    obtain ⟨ws₂, rfl, hws₂⟩ := Validation.matchExp_tup_iff.1 hw₂
    obtain ⟨vt, c, τ₄, rfl, hvt, hc⟩ := matchExps_two_iff.1 hws₂
    rw [Execution.matchExp_caseNil_iff] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨w₃, rfl, hw₃⟩ := Validation.matchExp_case_iff.1 hst
    obtain ⟨ws₃, rfl, hws₃⟩ := Validation.matchExp_tup_iff.1 hw₃
    obtain ⟨vt', pn, x, ao, j, τ₅, τ₆, τ₇, τ₈, rfl, hvt', hpn, hx, hao, hj⟩ :=
      ExecReadAggregate.matchExps_five_iff.1 hws₃
    rw [Execution.matchExp_caseNil_iff] at hvt'
    obtain ⟨rfl, rfl⟩ := hvt'
    obtain ⟨pw, rfl, hpw⟩ := Validation.matchExp_case_iff.1 hpn
    obtain ⟨pws, rfl, hpws⟩ := Validation.matchExp_tup_iff.1 hpw
    obtain ⟨nv, rfl, hnv⟩ := matchExps_one_iff.1 hpws
    rw [matchExp_freshVar_iff (by simp)] at hnv
    subst hnv
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    subst hao
    rw [matchExp_freshVar_iff (by simp)] at hj
    subst hj
    obtain ⟨rfl, rfl⟩ := (matchExp_trapRhs_iff (z := z) (by simp)).1 hr
    obtain ⟨rfl, k, off, w, m, haddr, hoff, hsize, hmem, hlt⟩ :=
      (premsHold_storeGuard_iff (z := z) (x := x) (i := i) (ao := ao)
        (SZ := fun u => u = nv)
        (by simp) (by simp) (by simp) (by simp) rfl
        (fun u => by
          rw [evalExp_varE_iff]
          refine ⟨fun h => ?_, fun h => by simp [h]⟩
          simp at h
          exact h.symm)).1 hp
    exact ⟨z, atv, i, c, nv, x, ao, j, k, off, w, m, rfl, haddr, hoff,
      (by obtain ⟨sz, q, h₁, h₂, h₃⟩ := hsize; exact ⟨sz, q, h₁.symm, h₂, h₃⟩),
      hmem, hlt⟩
  · rintro ⟨z, atv, i, c, nv, x, ao, j, k, off, w, m, rfl, haddr, hoff, hsize,
      hmem, hlt⟩
    refine ⟨((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "N" nv).bindVal "x" x).bindVal "ao" ao).bindVal "j" j), ((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "N" nv).bindVal "x" x).bindVal "ao" ao).bindVal "j" j),
      matchExp_concl_iff.2 ⟨_, _, ((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "N" nv).bindVal "x" x).bindVal "ao" ao).bindVal "j" j), rfl, ?_,
        (matchExp_trapRhs_iff (z := z) (by simp)).2 ⟨rfl, rfl⟩⟩,
      (premsHold_storeGuard_iff (z := z) (x := x) (i := i) (ao := ao)
        (SZ := fun u => u = nv)
        (by simp) (by simp) (by simp) (by simp) rfl
        (fun u => by
          rw [evalExp_varE_iff]
          refine ⟨fun h => ?_, fun h => by simp [h]⟩
          simp at h
          exact h.symm)).2
        ⟨rfl, k, off, w, m, haddr, hoff,
          (by obtain ⟨sz, q, h₁, h₂, h₃⟩ := hsize; exact ⟨sz, q, h₁.symm, h₂, h₃⟩),
          hmem, hlt⟩⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, (VarEnv.empty.bindVal "z" z), rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨_, _, _, (((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i), ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c), rfl, ?_, ?_, ?_⟩⟩⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, ((VarEnv.empty.bindVal "z" z).bindVal "at" atv), rfl,
            Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, (((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i), rfl,
            Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          ExecReadAggregate.matchExps_five_iff.2
            ⟨_, _, _, _, _, ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c), (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "N" nv), ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "N" nv).bindVal "x" x), (((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "c" c).bindVal "N" nv).bindVal "x" x).bindVal "ao" ao), rfl,
              Execution.matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
              (matchExp_freshVar_iff (by simp)).2 rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩

/-- **`Step/store-pack-oob`, characterised exactly** — the last of the four.
Its width is the packing size the instruction carries, reached through a
doubly-wrapped `%(%(n))`. -/
theorem ruleFires_storePackOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v storePackOobRule ↔
      ∃ z atv i inn c nv x ao k off w m,
        v = .tuple [configV z [Execution.constV atv i, Execution.constV inn c,
                      .case "STORE" (.tuple [inn,
                        .opt (some (.case "%" (.tuple [.case "%" (.tuple [nv])]))),
                        x, ao])],
                    configV z [Execution.trapV]] ∧
        AddrNat i k ∧ OffsetNat ao off ∧ WidthBytes nv w ∧
        MemBytesLen env z x m ∧ m < k + off + w := by
  unfold storePackOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨z, is, τ, rfl, hz, his⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 his
    obtain ⟨c₁, c₂, st, τ₁, τ₂, rfl, h₁, h₂, hst⟩ := matchExps_three_iff.1 hivs
    obtain ⟨w₁, rfl, hw₁⟩ := Validation.matchExp_case_iff.1 h₁
    obtain ⟨ws₁, rfl, hws₁⟩ := Validation.matchExp_tup_iff.1 hw₁
    obtain ⟨atv, i, τ₃, rfl, hat, hi⟩ := matchExps_two_iff.1 hws₁
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
    subst hat
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨w₂, rfl, hw₂⟩ := Validation.matchExp_case_iff.1 h₂
    obtain ⟨ws₂, rfl, hws₂⟩ := Validation.matchExp_tup_iff.1 hw₂
    obtain ⟨inn, c, τ₄, rfl, hinn, hc⟩ := matchExps_two_iff.1 hws₂
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hinn
    subst hinn
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨w₃, rfl, hw₃⟩ := Validation.matchExp_case_iff.1 hst
    obtain ⟨ws₃, rfl, hws₃⟩ := Validation.matchExp_tup_iff.1 hw₃
    obtain ⟨inn', opt, x, ao, τ₅, τ₆, τ₇, rfl, hinn', hopt, hx, hao⟩ :=
      matchExps_four_iff.1 hws₃
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := inn) (by simp)] at hinn'
    obtain ⟨rfl, rfl⟩ := hinn'
    obtain ⟨ov, rfl, hov⟩ := Validation.matchExp_optSome_iff.1 hopt
    obtain ⟨ow, rfl, how⟩ := Validation.matchExp_case_iff.1 hov
    obtain ⟨ows, rfl, hows⟩ := Validation.matchExp_tup_iff.1 how
    obtain ⟨iw, rfl, hiw⟩ := matchExps_one_iff.1 hows
    obtain ⟨iws, rfl, hiws⟩ := Validation.matchExp_case_iff.1 hiw
    obtain ⟨iws', rfl, hiws'⟩ := Validation.matchExp_tup_iff.1 hiws
    obtain ⟨nv, rfl, hnv⟩ := matchExps_one_iff.1 hiws'
    rw [matchExp_freshVar_iff (by simp)] at hnv
    subst hnv
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    subst hao
    obtain ⟨rfl, rfl⟩ := (matchExp_trapRhs_iff (z := z) (by simp)).1 hr
    obtain ⟨rfl, k, off, w, m, haddr, hoff, hsize, hmem, hlt⟩ :=
      (premsHold_storeGuard_iff (z := z) (x := x) (i := i) (ao := ao)
        (SZ := fun u => u = nv)
        (by simp) (by simp) (by simp) (by simp) rfl
        (fun u => by
          rw [evalExp_varE_iff]
          refine ⟨fun h => ?_, fun h => by simp [h]⟩
          simp at h
          exact h.symm)).1 hp
    exact ⟨z, atv, i, inn', c, nv, x, ao, k, off, w, m, rfl, haddr, hoff,
      (by obtain ⟨sz, q, h₁, h₂, h₃⟩ := hsize; exact ⟨sz, q, h₁.symm, h₂, h₃⟩),
      hmem, hlt⟩
  · rintro ⟨z, atv, i, inn, c, nv, x, ao, k, off, w, m, rfl, haddr, hoff, hsize,
      hmem, hlt⟩
    refine ⟨((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "Inn" inn).bindVal "c" c).bindVal "n" nv).bindVal "x" x).bindVal "ao" ao), ((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "Inn" inn).bindVal "c" c).bindVal "n" nv).bindVal "x" x).bindVal "ao" ao),
      matchExp_concl_iff.2 ⟨_, _, ((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "Inn" inn).bindVal "c" c).bindVal "n" nv).bindVal "x" x).bindVal "ao" ao), rfl, ?_,
        (matchExp_trapRhs_iff (z := z) (by simp)).2 ⟨rfl, rfl⟩⟩,
      (premsHold_storeGuard_iff (z := z) (x := x) (i := i) (ao := ao)
        (SZ := fun u => u = nv)
        (by simp) (by simp) (by simp) (by simp) rfl
        (fun u => by
          rw [evalExp_varE_iff]
          refine ⟨fun h => ?_, fun h => by simp [h]⟩
          simp at h
          exact h.symm)).2
        ⟨rfl, k, off, w, m, haddr, hoff,
          (by obtain ⟨sz, q, h₁, h₂, h₃⟩ := hsize; exact ⟨sz, q, h₁.symm, h₂, h₃⟩),
          hmem, hlt⟩⟩
    refine Validation.matchExp_case_iff.2 ⟨_, rfl,
      Validation.matchExp_tup_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, (VarEnv.empty.bindVal "z" z), rfl,
          (matchExp_freshVar_iff (by simp)).2 rfl,
          Validation.matchExp_list_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨_, _, _, (((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i), (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "Inn" inn).bindVal "c" c), rfl, ?_, ?_, ?_⟩⟩⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, ((VarEnv.empty.bindVal "z" z).bindVal "at" atv), rfl,
            Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "Inn" inn), rfl,
            Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · refine Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_four_iff.2 ⟨_, _, _, _, (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "Inn" inn).bindVal "c" c), ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "Inn" inn).bindVal "c" c).bindVal "n" nv), (((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal "Inn" inn).bindVal "c" c).bindVal "n" nv).bindVal "x" x), rfl,
            Validation.matchExp_sub_iff.2
              ((matchExp_boundVar_iff (w := inn) (by simp)).2 ⟨rfl, rfl⟩), ?_,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
      exact Validation.matchExp_optSome_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩

/-! ### The `val^n`-headed left-hand sides

The four allocation rules — `throw`, `struct.new`, `array.new_fixed` and
`call_ref-hostfunc-res` — share a left-hand side `z; val^n instr*`.  It binds
`z`, `n`, `val*` and whatever the trailing literal list binds, and nothing
else; in particular it does not bind the `exn`/`si`/`ai`/`result` their
right-hand sides allocate. -/

/-- `val^n` binds only its counter and its domain. -/
theorem unbinds_valsNPat {env : Env} {ρ σ : VarEnv} {v : Value} {x d cnt y : IL.Id}
    (hx : x ≠ "_") (hd_ : d ≠ "_") (hc_ : cnt ≠ "_") (hcx : cnt ≠ x)
    (hdy : d ≠ y) (hcy : cnt ≠ y)
    (hxf : ρ.findVal? x = none) (hy : ρ.findVal? y = none)
    (hm : MatchExp env ρ (Execution.valsNPat x d cnt) v σ) : σ.findVal? y = none := by
  rw [Execution.valsNPat, matchExp_iterE_listN_iff] at hm
  obtain ⟨vs, τ, rfl, hcnt, hlist⟩ := hm
  have hτ : τ.findVal? y = none := unbinds_varE hc_ hcy _ _ _ hy hcnt
  have hτx : τ.findVal? x = none := by
    rcases Validation.matchExp_var_iff.1 hcnt with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · simpa [Execution.findVal?_bindVal_lit hc_, hcx] using hxf
    · exact hxf
  rw [matchIterList_single_iff (bindsVar_subVar x _ _) hτx hx] at hlist
  exact unbinds_varE hd_ hdy _ _ _ hτ hlist

/-- **`Step/throw` cannot fire at the pin.**  Its conclusion allocates
`exn`, which the left-hand side does not bind — `val^n` binds only `n` and
`val*` — and the `Expand` premise that names it binds nothing. -/
theorem not_ruleFires_throw_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v throwRule := by
  unfold throwRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
  obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
  obtain ⟨z, body, τ, rfl, hz, hbody⟩ := matchExps_two_iff.1 hcvs
  rw [matchExp_freshVar_iff (by simp)] at hz
  subst hz
  obtain ⟨vs, kk, υ, rfl, ha, hb⟩ := ExecReadControl.matchExp_catE_dest hbody
  have hυ : υ.findVal? "exn" = none :=
    unbinds_valsNPat (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp) (by simp) ha
  have hσ : σ.findVal? "exn" = none :=
    (show Unbinds env _ "exn" by unbinds) _ _ _ hυ hb
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ', rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, _, rfl, -, h1⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h1
  rw [evalExp_listE_iff] at hu
  obtain ⟨us, hus, -⟩ := hu
  obtain ⟨u', _, _, hu', -⟩ := Validation.evalExps_cons_iff.1 hus
  rw [evalExp_varE_iff, hσ] at hu'
  simp at hu'

/-- **`Step/struct.new` cannot fire at the pin.**  Its conclusion allocates
`si`, which the left-hand side does not bind — `val^n` binds only `n` and
`val*` — and the `Expand` premise that names it binds nothing. -/
theorem not_ruleFires_structNew_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v structNewRule := by
  unfold structNewRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
  obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
  obtain ⟨z, body, τ, rfl, hz, hbody⟩ := matchExps_two_iff.1 hcvs
  rw [matchExp_freshVar_iff (by simp)] at hz
  subst hz
  obtain ⟨vs, kk, υ, rfl, ha, hb⟩ := ExecReadControl.matchExp_catE_dest hbody
  have hυ : υ.findVal? "si" = none :=
    unbinds_valsNPat (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp) (by simp) ha
  have hσ : σ.findVal? "si" = none :=
    (show Unbinds env _ "si" by unbinds) _ _ _ hυ hb
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ', rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, _, rfl, -, h1⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h1
  rw [evalExp_listE_iff] at hu
  obtain ⟨us, hus, -⟩ := hu
  obtain ⟨u', _, _, hu', -⟩ := Validation.evalExps_cons_iff.1 hus
  rw [evalExp_varE_iff, hσ] at hu'
  simp at hu'

/-- **`Step/array.new_fixed` cannot fire at the pin.**  Its conclusion allocates
`ai`, which the left-hand side does not bind — `val^n` binds only `n` and
`val*` — and the `Expand` premise that names it binds nothing. -/
theorem not_ruleFires_arrayNewFixed_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayNewFixedRule := by
  unfold arrayNewFixedRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
  obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
  obtain ⟨z, body, τ, rfl, hz, hbody⟩ := matchExps_two_iff.1 hcvs
  rw [matchExp_freshVar_iff (by simp)] at hz
  subst hz
  obtain ⟨vs, kk, υ, rfl, ha, hb⟩ := ExecReadControl.matchExp_catE_dest hbody
  have hυ : υ.findVal? "ai" = none :=
    unbinds_valsNPat (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp) (by simp) ha
  have hσ : σ.findVal? "ai" = none :=
    (show Unbinds env _ "ai" by unbinds) _ _ _ hυ hb
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨w, is, υ', rfl, hw, -⟩ := matchExps_two_iff.1 hbvs
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨-, _, rfl, -, h1⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 h1
  rw [evalExp_listE_iff] at hu
  obtain ⟨us, hus, -⟩ := hu
  obtain ⟨u', _, _, hu', -⟩ := Validation.evalExps_cons_iff.1 hus
  rw [evalExp_varE_iff, hσ] at hu'
  simp at hu'

/-- **`Step/call_ref-hostfunc-res` cannot fire at the pin.**  Its right-hand
side is `$lift_result(result)`, and `result` is named only by the premise
`$hostfunc(…) = result`. -/
theorem not_ruleFires_callRefHostfuncRes_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v callRefHostfuncResRule := by
  unfold callRefHostfuncResRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
  obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
  obtain ⟨st, body, τ, rfl, hst, hbody⟩ := matchExps_two_iff.1 hcvs
  have hτ : τ.findVal? "result" = none :=
    (show Unbinds env _ "result" by unbinds) _ _ _ (by simp) hst
  obtain ⟨vs, kk, υ, rfl, ha, hb⟩ := ExecReadControl.matchExp_catE_dest hbody
  have hvalτ : τ.findVal? "val" = none :=
    (show Unbinds env _ "val" by unbinds) _ _ _ (by simp) hst
  have hυ : υ.findVal? "result" = none :=
    unbinds_valsNPat (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hvalτ hτ ha
  have hσ : σ.findVal? "result" = none :=
    (show Unbinds env _ "result" by unbinds) _ _ _ hυ hb
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨st', w, φ, rfl, hst', hw⟩ := matchExps_two_iff.1 hbvs
  have hφ : φ.findVal? "result" = none :=
    (show Unbinds env _ "result" by unbinds) _ _ _ hσ hst'
  rw [ExecDefault.matchExp_callE_iff] at hw
  obtain ⟨hcall, -⟩ := hw
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨u, _, rfl, hu, -⟩ := ExecRead.evalArgs_expA_cons_iff.1 hargs
  rw [evalExp_varE_iff, hφ] at hu
  simp at hu

/-! ### The two that fail at a premise rather than the conclusion

`call_ref-func` and `call_ref-hostfunc-div` have conclusions that match
perfectly well.  What they cannot do is discharge their *first* premise,
`$funcinst(z)[a] = fi`, because `fi` is bound by nothing: an `IfPr` evaluates,
and evaluating an unbound variable is `undef`.  The source writes a
destructuring equation; the elaborated IL keeps it a side condition. -/

/-- **`Step/call_ref-hostfunc-div` cannot fire at the pin.** -/
theorem not_ruleFires_callRefHostfuncDiv_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v callRefHostfuncDivRule := by
  unfold callRefHostfuncDivRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have key : ∀ (ρ ρ' : VarEnv) (w : Value), ρ.findVal? "fi" = none →
      ρ.findVal? "val" = none →
      MatchExp env ρ
        (.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE "s", .varE "f"]),
          .catE (Execution.valsNPat "val" "val*" "n")
            (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"),
              .caseE "CALL_REF" (.varE "yy")])])) w ρ' →
      ρ'.findVal? "fi" = none ∧ ρ'.findVal? "val" = none := by
    rintro ρ ρ' w hfi hval hmm
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hmm
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨st, body, τ, rfl, hst, hbody⟩ := matchExps_two_iff.1 hcvs
    have hτf : τ.findVal? "fi" = none :=
      (show Unbinds env _ "fi" by unbinds) _ _ _ hfi hst
    have hτv : τ.findVal? "val" = none :=
      (show Unbinds env _ "val" by unbinds) _ _ _ hval hst
    obtain ⟨vs, kk, υ, rfl, ha, hb⟩ := ExecReadControl.matchExp_catE_dest hbody
    have hυf : υ.findVal? "fi" = none :=
      unbinds_valsNPat (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hτv hτf ha
    have hυv : υ.findVal? "val" = none :=
      unbinds_valsNPat (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hτv hτv ha
    exact ⟨(show Unbinds env _ "fi" by unbinds) _ _ _ hυf hb,
      (show Unbinds env _ "val" by unbinds) _ _ _ hυv hb⟩
  obtain ⟨hσf, hσv⟩ := key _ _ _ (by simp) (by simp) hl
  obtain ⟨hρf, -⟩ := key _ _ _ hσf hσv hr
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
  obtain ⟨v₁, v₂, -, hv₂, -⟩ := evalExp_cmpE_iff.1 hev
  rw [evalExp_varE_iff, hρf] at hv₂
  simp at hv₂

/-- `instr*` binds only its domain. -/
theorem unbinds_iterPat_fresh {env : Env} {ρ σ : VarEnv} {v : Value} {x d y : IL.Id}
    (hx : x ≠ "_") (hd_ : d ≠ "_") (hdy : d ≠ y)
    (hxf : ρ.findVal? x = none) (hy : ρ.findVal? y = none)
    (hm : MatchExp env ρ (Execution.iterPat x d) v σ) : σ.findVal? y = none := by
  rw [Execution.iterPat, matchExp_iterE_list_iff (bindsVar_varE x) hxf hx] at hm
  obtain ⟨vs, rfl, hvs⟩ := hm
  exact unbinds_varE hd_ hdy _ _ _ hy hvs

/-- **`Step/call_ref-func` cannot fire at the pin**, for the same reason as
`call_ref-hostfunc-div`: its first premise is `$funcinst(z)[a] = fi`, and `fi`
is bound by nothing. -/
theorem not_ruleFires_callRefFunc_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v callRefFuncRule := by
  unfold callRefFuncRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  -- the left-hand side binds `z`, `n`, `val*`, `a` and `yy`
  have hσ : σ.findVal? "fi" = none ∧ σ.findVal? "instr" = none := by
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨zv, body, τ, rfl, hz, hbody⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨vs, kk, υ, rfl, ha, hb⟩ := ExecReadControl.matchExp_catE_dest hbody
    have hυf : υ.findVal? "fi" = none :=
      unbinds_valsNPat (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by simp) (by simp) ha
    have hυi : υ.findVal? "instr" = none :=
      unbinds_valsNPat (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by simp) (by simp) ha
    exact ⟨(show Unbinds env _ "fi" by unbinds) _ _ _ hυf hb,
      (show Unbinds env _ "instr" by unbinds) _ _ _ hυi hb⟩
  obtain ⟨hσf, hσi⟩ := hσ
  -- the right-hand side binds `m`, `f` and `instr*`
  obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
  obtain ⟨zv', fr, φ, rfl, hz', hfr⟩ := matchExps_two_iff.1 hbvs
  have hφf : φ.findVal? "fi" = none :=
    (show Unbinds env _ "fi" by unbinds) _ _ _ hσf hz'
  have hφi : φ.findVal? "instr" = none :=
    (show Unbinds env _ "instr" by unbinds) _ _ _ hσi hz'
  obtain ⟨frs, rfl, hfrs⟩ := Validation.matchExp_list_iff.1 hfr
  obtain ⟨fv, rfl, hfv⟩ := matchExps_one_iff.1 hfrs
  obtain ⟨fw, rfl, hfw⟩ := Validation.matchExp_case_iff.1 hfv
  obtain ⟨fws, rfl, hfws⟩ := Validation.matchExp_tup_iff.1 hfw
  obtain ⟨mv, fvv, ls, χ, ψ, rfl, hmv, hfvv, hls⟩ := matchExps_three_iff.1 hfws
  have hχf : χ.findVal? "fi" = none := unbinds_varE (by decide) (by decide) _ _ _ hφf hmv
  have hχi : χ.findVal? "instr" = none :=
    unbinds_varE (by decide) (by decide) _ _ _ hφi hmv
  have hψf : ψ.findVal? "fi" = none :=
    unbinds_varE (by decide) (by decide) _ _ _ hχf hfvv
  have hψi : ψ.findVal? "instr" = none :=
    unbinds_varE (by decide) (by decide) _ _ _ hχi hfvv
  obtain ⟨lss, rfl, hlss⟩ := Validation.matchExp_list_iff.1 hls
  obtain ⟨lv, rfl, hlv⟩ := matchExps_one_iff.1 hlss
  obtain ⟨lw, rfl, hlw⟩ := Validation.matchExp_case_iff.1 hlv
  obtain ⟨lws, rfl, hlws⟩ := Validation.matchExp_tup_iff.1 hlw
  obtain ⟨mv', nil, iter, ω₁, ω₂, rfl, hmv', hnil, hiter⟩ := matchExps_three_iff.1 hlws
  have hω₁f : ω₁.findVal? "fi" = none :=
    unbinds_varE (by decide) (by decide) _ _ _ hψf hmv'
  have hω₁i : ω₁.findVal? "instr" = none :=
    unbinds_varE (by decide) (by decide) _ _ _ hψi hmv'
  have hω₂f : ω₂.findVal? "fi" = none := unbinds_listE unbindsAll_nil _ _ _ hω₁f hnil
  have hω₂i : ω₂.findVal? "instr" = none := unbinds_listE unbindsAll_nil _ _ _ hω₁i hnil
  have hρf : ρ₁.findVal? "fi" = none :=
    unbinds_iterPat_fresh (by decide) (by decide) (by decide) hω₂i hω₂f hiter
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
  obtain ⟨v₁, v₂, -, hv₂, -⟩ := evalExp_cmpE_iff.1 hev
  rw [evalExp_varE_iff, hρf] at hv₂
  simp at hv₂

/-! ## One rule of `Step_pure` cannot fire either

`scripts/spectec_unbound_vars.py Step_pure` finds exactly one: `vtestop`.
Its lane vector `i*` occurs in neither half of the conclusion — only in its
two premises, the first of which is `i* = $lanes_(Jnn X M, c_1)`.  That is an
`IfPr`, which evaluates; an iteration over an unbound domain has no value; so
`ALL_TRUE` reduces nothing at the pin.

`vvtestop` next to it is fine — its operator component is a literal
`ANY_TRUE` and it binds everything it uses.  The asymmetry is worth noting:
the two rules are written the same way in the document. -/

/-- **`Step_pure/vtestop` cannot fire at the pin.** -/
theorem not_ruleFires_vtestop_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v ExecVector.vtestopRule := by
  unfold ExecVector.vtestopRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  have hρ : ρ₁.findVal? "i*" = none :=
    (show Unbinds env _ "i*" by unbinds) _ _ _ (by simp) hm
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
  obtain ⟨v₁, v₂, hv₁, -, -⟩ := evalExp_cmpE_iff.1 hev
  exact ExecReadControl.not_evalExp_iterE_of_unbound hρ hv₁

end Silmaril.SpecTec.Equiv.ExecStepRules
