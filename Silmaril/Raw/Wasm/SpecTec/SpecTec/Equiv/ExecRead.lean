module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecStep
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `Step_read`, transcribed

All 103 rules of `Step_read`, with their index in the pinned stream, and the
single `rfl` that ties the transcription to `Silmaril.SpecTec.Specs.wasm30`.

`Step_read` is the largest relation in the specification and the one the
runtime bridge gates: every rule reads `config = state; instr*`, so
characterising any of them needs a bridge for `store`, `frame` and
`moduleinst`, which `Equiv/RuntimeBridge/` is building.  Transcribing them is
independent of that, and it is worth doing first for two reasons: it is what
makes the provenance of all 103 a single kernel-checked fact, and it is what
lets a characterisation be written one rule at a time afterwards without
re-deriving the term.

`Equiv/ExecStep.lean`'s `ruleFires_stepRead_iff` already says how any
`Step_read` derivation becomes a `Step` derivation, for an arbitrary state, so
each rule characterised here will lift to the whole machine immediately.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecRead

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## The 103 rules, as the pinned stream records them -/

/-- `Step_read/block`, rule 0 of the pinned stream. -/
def blockRule : Rule :=
  (.ruleD "block" [(.expP "z" (.varT "state" [])), (.expP "m" (.varT "m" [])), (.expP "val*"
   (.iterT (.varT "val" []) .list)), (.expP "bt" (.varT "blocktype" [])), (.expP "instr*"
   (.iterT (.varT "instr" []) .list)), (.expP "n" (.varT "n" [])), (.expP "t_1*" (.iterT
   (.varT "valtype" []) .list)), (.expP "t_2*" (.iterT (.varT "valtype" []) .list))] "%~>%"
   (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.catE (.iterE (.subE (.varE "val") (.varT
   "val" []) (.varT "instr" [])) (.mk (.listN (.varE "m") none) [(.mk "val" (.varE
   "val*"))])) (.listE [(.caseE "BLOCK" (.tupE [(.varE "bt"), (.iterE (.varE "instr") (.mk
   .list [(.mk "instr" (.varE "instr*"))]))]))]))])), (.listE [(.caseE "LABEL_%{%}%" (.tupE
   [(.varE "n"), (.listE []), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])) (.mk (.listN (.varE "m") none) [(.mk "val" (.varE "val*"))])) (.iterE (.varE
   "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])))]))])]) [(.ifPr (.cmpE .eqOp
   .boolT (.callE "blocktype_" [(.expA (.varE "z")), (.expA (.varE "bt"))]) (.caseE "%->_%%"
   (.tupE [(.caseE "%" (.tupE [(.iterE (.varE "t_1") (.mk (.listN (.varE "m") none) [(.mk
   "t_1" (.varE "t_1*"))]))])), (.listE []), (.caseE "%" (.tupE [(.iterE (.varE "t_2") (.mk
   (.listN (.varE "n") none) [(.mk "t_2" (.varE "t_2*"))]))]))]))))])

/-- `Step_read/loop`, rule 1 of the pinned stream. -/
def loopRule : Rule :=
  (.ruleD "loop" [(.expP "z" (.varT "state" [])), (.expP "m" (.varT "m" [])), (.expP "val*"
   (.iterT (.varT "val" []) .list)), (.expP "bt" (.varT "blocktype" [])), (.expP "instr*"
   (.iterT (.varT "instr" []) .list)), (.expP "t_1*" (.iterT (.varT "valtype" []) .list)),
   (.expP "n" (.varT "n" [])), (.expP "t_2*" (.iterT (.varT "valtype" []) .list))] "%~>%"
   (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.catE (.iterE (.subE (.varE "val") (.varT
   "val" []) (.varT "instr" [])) (.mk (.listN (.varE "m") none) [(.mk "val" (.varE
   "val*"))])) (.listE [(.caseE "LOOP" (.tupE [(.varE "bt"), (.iterE (.varE "instr") (.mk
   .list [(.mk "instr" (.varE "instr*"))]))]))]))])), (.listE [(.caseE "LABEL_%{%}%" (.tupE
   [(.varE "m"), (.listE [(.caseE "LOOP" (.tupE [(.varE "bt"), (.iterE (.varE "instr") (.mk
   .list [(.mk "instr" (.varE "instr*"))]))]))]), (.catE (.iterE (.subE (.varE "val") (.varT
   "val" []) (.varT "instr" [])) (.mk (.listN (.varE "m") none) [(.mk "val" (.varE
   "val*"))])) (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])))]))])])
   [(.ifPr (.cmpE .eqOp .boolT (.callE "blocktype_" [(.expA (.varE "z")), (.expA (.varE
   "bt"))]) (.caseE "%->_%%" (.tupE [(.caseE "%" (.tupE [(.iterE (.varE "t_1") (.mk (.listN
   (.varE "m") none) [(.mk "t_1" (.varE "t_1*"))]))])), (.listE []), (.caseE "%" (.tupE
   [(.iterE (.varE "t_2") (.mk (.listN (.varE "n") none) [(.mk "t_2" (.varE
   "t_2*"))]))]))]))))])

/-- `Step_read/br_on_cast-succeed`, rule 2 of the pinned stream. -/
def brOnCastSucceedRule : Rule :=
  (.ruleD "br_on_cast-succeed" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame"
   [])), (.expP "ref" (.varT "ref" [])), (.expP "l" (.varT "labelidx" [])), (.expP "rt_1"
   (.varT "reftype" [])), (.expP "rt_2" (.varT "reftype" []))] "%~>%" (.tupE [(.caseE "%;%"
   (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.subE (.varE "ref")
   (.varT "ref" []) (.varT "instr" [])), (.caseE "BR_ON_CAST" (.tupE [(.varE "l"), (.varE
   "rt_1"), (.varE "rt_2")]))])])), (.listE [(.subE (.varE "ref") (.varT "ref" []) (.varT
   "instr" [])), (.caseE "BR" (.varE "l"))])]) [(.rulePr "Ref_ok" [] "%|-%:%" (.tupE [(.varE
   "s"), (.varE "ref"), (.callE "inst_reftype" [(.expA (.dotE (.varE "f") "MODULE")), (.expA
   (.varE "rt_2"))])]))])

/-- `Step_read/br_on_cast-fail`, rule 3 of the pinned stream. -/
def brOnCastFailRule : Rule :=
  (.ruleD "br_on_cast-fail" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame" [])),
   (.expP "ref" (.varT "ref" [])), (.expP "l" (.varT "labelidx" [])), (.expP "rt_1" (.varT
   "reftype" [])), (.expP "rt_2" (.varT "reftype" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.subE (.varE "ref") (.varT
   "ref" []) (.varT "instr" [])), (.caseE "BR_ON_CAST" (.tupE [(.varE "l"), (.varE "rt_1"),
   (.varE "rt_2")]))])])), (.listE [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr"
   []))])]) [.elsePr])

/-- `Step_read/br_on_cast_fail-succeed`, rule 4 of the pinned stream. -/
def brOnCastFailSucceedRule : Rule :=
  (.ruleD "br_on_cast_fail-succeed" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT
   "frame" [])), (.expP "ref" (.varT "ref" [])), (.expP "l" (.varT "labelidx" [])), (.expP
   "rt_1" (.varT "reftype" [])), (.expP "rt_2" (.varT "reftype" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.subE (.varE
   "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "BR_ON_CAST_FAIL" (.tupE [(.varE
   "l"), (.varE "rt_1"), (.varE "rt_2")]))])])), (.listE [(.subE (.varE "ref") (.varT "ref"
   []) (.varT "instr" []))])]) [(.rulePr "Ref_ok" [] "%|-%:%" (.tupE [(.varE "s"), (.varE
   "ref"), (.callE "inst_reftype" [(.expA (.dotE (.varE "f") "MODULE")), (.expA (.varE
   "rt_2"))])]))])

/-- `Step_read/br_on_cast_fail-fail`, rule 5 of the pinned stream. -/
def brOnCastFailFailRule : Rule :=
  (.ruleD "br_on_cast_fail-fail" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame"
   [])), (.expP "ref" (.varT "ref" [])), (.expP "l" (.varT "labelidx" [])), (.expP "rt_1"
   (.varT "reftype" [])), (.expP "rt_2" (.varT "reftype" []))] "%~>%" (.tupE [(.caseE "%;%"
   (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.subE (.varE "ref")
   (.varT "ref" []) (.varT "instr" [])), (.caseE "BR_ON_CAST_FAIL" (.tupE [(.varE "l"),
   (.varE "rt_1"), (.varE "rt_2")]))])])), (.listE [(.subE (.varE "ref") (.varT "ref" [])
   (.varT "instr" [])), (.caseE "BR" (.varE "l"))])]) [.elsePr])

/-- `Step_read/call`, rule 6 of the pinned stream. -/
def callRule : Rule :=
  (.ruleD "call" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" [])), (.expP "a"
   (.varT "addr" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CALL" (.varE "x"))])])), (.listE [(.caseE "REF.FUNC_ADDR" (.varE "a")), (.caseE
   "CALL_REF" (.subE (.dotE (.idxE (.callE "funcinst" [(.expA (.varE "z"))]) (.varE "a"))
   "TYPE") (.varT "deftype" []) (.varT "typeuse" [])))])]) [(.ifPr (.cmpE .eqOp .boolT
   (.idxE (.dotE (.callE "moduleinst" [(.expA (.varE "z"))]) "FUNCS") (.projE (.uncaseE
   (.varE "x") "%") (0))) (.varE "a")))])

/-- `Step_read/return_call`, rule 7 of the pinned stream. -/
def returnCallRule : Rule :=
  (.ruleD "return_call" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" [])),
   (.expP "a" (.varT "addr" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE
   [(.caseE "RETURN_CALL" (.varE "x"))])])), (.listE [(.caseE "REF.FUNC_ADDR" (.varE "a")),
   (.caseE "RETURN_CALL_REF" (.subE (.dotE (.idxE (.callE "funcinst" [(.expA (.varE "z"))])
   (.varE "a")) "TYPE") (.varT "deftype" []) (.varT "typeuse" [])))])]) [(.ifPr (.cmpE .eqOp
   .boolT (.idxE (.dotE (.callE "moduleinst" [(.expA (.varE "z"))]) "FUNCS") (.projE
   (.uncaseE (.varE "x") "%") (0))) (.varE "a")))])

/-- `Step_read/return_call_ref-label`, rule 8 of the pinned stream. -/
def returnCallRefLabelRule : Rule :=
  (.ruleD "return_call_ref-label" [(.expP "z" (.varT "state" [])), (.expP "k" (.varT "n"
   [])), (.expP "instr'*" (.iterT (.varT "instr" []) .list)), (.expP "val*" (.iterT (.varT
   "val" []) .list)), (.expP "yy" (.varT "typeuse" [])), (.expP "instr*" (.iterT (.varT
   "instr" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "LABEL_%{%}%" (.tupE [(.varE "k"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'"
   (.varE "instr'*"))])), (.catE (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "RETURN_CALL_REF"
   (.varE "yy"))])) (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE
   "instr*"))])))]))])])), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "RETURN_CALL_REF"
   (.varE "yy"))]))]) [])

/-- `Step_read/return_call_ref-handler`, rule 9 of the pinned stream. -/
def returnCallRefHandlerRule : Rule :=
  (.ruleD "return_call_ref-handler" [(.expP "z" (.varT "state" [])), (.expP "k" (.varT "n"
   [])), (.expP "catch*" (.iterT (.varT "catch" []) .list)), (.expP "val*" (.iterT (.varT
   "val" []) .list)), (.expP "yy" (.varT "typeuse" [])), (.expP "instr*" (.iterT (.varT
   "instr" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "HANDLER_%{%}%" (.tupE [(.varE "k"), (.iterE (.varE "catch") (.mk .list [(.mk "catch"
   (.varE "catch*"))])), (.catE (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "RETURN_CALL_REF"
   (.varE "yy"))])) (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE
   "instr*"))])))]))])])), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "RETURN_CALL_REF"
   (.varE "yy"))]))]) [])

/-- `Step_read/return_call_ref-frame-null`, rule 10 of the pinned stream. -/
def returnCallRefFrameNullRule : Rule :=
  (.ruleD "return_call_ref-frame-null" [(.expP "z" (.varT "state" [])), (.expP "k" (.varT
   "n" [])), (.expP "f" (.varT "frame" [])), (.expP "val*" (.iterT (.varT "val" []) .list)),
   (.expP "yy" (.varT "typeuse" [])), (.expP "instr*" (.iterT (.varT "instr" []) .list))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "FRAME_%{%}%" (.tupE
   [(.varE "k"), (.varE "f"), (.catE (.catE (.catE (.iterE (.subE (.varE "val") (.varT "val"
   []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE
   "REF.NULL_ADDR" (.tupE []))])) (.listE [(.caseE "RETURN_CALL_REF" (.varE "yy"))]))
   (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])))]))])])), (.listE
   [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_read/return_call_ref-frame-addr`, rule 11 of the pinned stream. -/
def returnCallRefFrameAddrRule : Rule :=
  (.ruleD "return_call_ref-frame-addr" [(.expP "z" (.varT "state" [])), (.expP "k" (.varT
   "n" [])), (.expP "f" (.varT "frame" [])), (.expP "val'*" (.iterT (.varT "val" [])
   .list)), (.expP "n" (.varT "n" [])), (.expP "val*" (.iterT (.varT "val" []) .list)),
   (.expP "a" (.varT "addr" [])), (.expP "yy" (.varT "typeuse" [])), (.expP "instr*" (.iterT
   (.varT "instr" []) .list)), (.expP "t_1*" (.iterT (.varT "valtype" []) .list)), (.expP
   "m" (.varT "m" [])), (.expP "t_2*" (.iterT (.varT "valtype" []) .list))] "%~>%" (.tupE
   [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "FRAME_%{%}%" (.tupE [(.varE "k"),
   (.varE "f"), (.catE (.catE (.catE (.catE (.iterE (.subE (.varE "val'") (.varT "val" [])
   (.varT "instr" [])) (.mk .list [(.mk "val'" (.varE "val'*"))])) (.iterE (.subE (.varE
   "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val"
   (.varE "val*"))]))) (.listE [(.caseE "REF.FUNC_ADDR" (.varE "a"))])) (.listE [(.caseE
   "RETURN_CALL_REF" (.varE "yy"))])) (.iterE (.varE "instr") (.mk .list [(.mk "instr"
   (.varE "instr*"))])))]))])])), (.catE (.iterE (.subE (.varE "val") (.varT "val" [])
   (.varT "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "val" (.varE "val*"))])) (.listE
   [(.caseE "REF.FUNC_ADDR" (.varE "a")), (.caseE "CALL_REF" (.varE "yy"))]))]) [(.rulePr
   "Expand" [] "%~~%" (.tupE [(.dotE (.idxE (.callE "funcinst" [(.expA (.varE "z"))]) (.varE
   "a")) "TYPE"), (.caseE "FUNC%->%" (.tupE [(.caseE "%" (.tupE [(.iterE (.varE "t_1") (.mk
   (.listN (.varE "n") none) [(.mk "t_1" (.varE "t_1*"))]))])), (.caseE "%" (.tupE [(.iterE
   (.varE "t_2") (.mk (.listN (.varE "m") none) [(.mk "t_2" (.varE "t_2*"))]))]))]))]))])

/-- `Step_read/throw_ref-null`, rule 12 of the pinned stream. -/
def throwRefNullRule : Rule :=
  (.ruleD "throw_ref-null" [(.expP "z" (.varT "state" []))] "%~>%" (.tupE [(.caseE "%;%"
   (.tupE [(.varE "z"), (.listE [(.caseE "REF.NULL_ADDR" (.tupE [])), (.caseE "THROW_REF"
   (.tupE []))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_read/throw_ref-instrs`, rule 13 of the pinned stream. -/
def throwRefInstrsRule : Rule :=
  (.ruleD "throw_ref-instrs" [(.expP "z" (.varT "state" [])), (.expP "val*" (.iterT (.varT
   "val" []) .list)), (.expP "a" (.varT "addr" [])), (.expP "instr*" (.iterT (.varT "instr"
   []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.catE (.iterE (.subE
   (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE
   "val*"))])) (.catE (.listE [(.caseE "REF.EXN_ADDR" (.varE "a"))]) (.catE (.listE [(.caseE
   "THROW_REF" (.tupE []))]) (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE
   "instr*"))])))))])), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF"
   (.tupE []))])]) [(.ifPr (.binE .orOp .boolT (.cmpE .neOp .boolT (.iterE (.varE "val")
   (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [])) (.cmpE .neOp .boolT (.iterE (.varE
   "instr") (.mk .list [(.mk "instr" (.varE "instr*"))])) (.listE []))))])

/-- `Step_read/throw_ref-label`, rule 14 of the pinned stream. -/
def throwRefLabelRule : Rule :=
  (.ruleD "throw_ref-label" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])),
   (.expP "instr'*" (.iterT (.varT "instr" []) .list)), (.expP "a" (.varT "addr" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "LABEL_%{%}%" (.tupE
   [(.varE "n"), (.iterE (.varE "instr'") (.mk .list [(.mk "instr'" (.varE "instr'*"))])),
   (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE []))])]))])])),
   (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE []))])]) [])

/-- `Step_read/throw_ref-frame`, rule 15 of the pinned stream. -/
def throwRefFrameRule : Rule :=
  (.ruleD "throw_ref-frame" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])),
   (.expP "f" (.varT "frame" [])), (.expP "a" (.varT "addr" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "FRAME_%{%}%" (.tupE [(.varE "n"), (.varE
   "f"), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE
   []))])]))])])), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE
   []))])]) [])

/-- `Step_read/throw_ref-handler-empty`, rule 16 of the pinned stream. -/
def throwRefHandlerEmptyRule : Rule :=
  (.ruleD "throw_ref-handler-empty" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n"
   [])), (.expP "a" (.varT "addr" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.listE []), (.listE [(.caseE
   "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE []))])]))])])), (.listE [(.caseE
   "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE []))])]) [])

/-- `Step_read/throw_ref-handler-catch`, rule 17 of the pinned stream. -/
def throwRefHandlerCatchRule : Rule :=
  (.ruleD "throw_ref-handler-catch" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n"
   [])), (.expP "x" (.varT "idx" [])), (.expP "l" (.varT "labelidx" [])), (.expP "catch'*"
   (.iterT (.varT "catch" []) .list)), (.expP "a" (.varT "addr" [])), (.expP "val*" (.iterT
   (.varT "val" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE
   [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.catE (.listE [(.caseE "CATCH" (.tupE
   [(.varE "x"), (.varE "l")]))]) (.iterE (.varE "catch'") (.mk .list [(.mk "catch'" (.varE
   "catch'*"))]))), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE
   []))])]))])])), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
   (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "BR" (.varE "l"))]))]) [(.ifPr
   (.cmpE .eqOp .boolT (.dotE (.idxE (.callE "exninst" [(.expA (.varE "z"))]) (.varE "a"))
   "TAG") (.idxE (.callE "tagaddr" [(.expA (.varE "z"))]) (.projE (.uncaseE (.varE "x") "%")
   (0))))), (.ifPr (.cmpE .eqOp .boolT (.iterE (.varE "val") (.mk .list [(.mk "val" (.varE
   "val*"))])) (.dotE (.idxE (.callE "exninst" [(.expA (.varE "z"))]) (.varE "a"))
   "FIELDS")))])

/-- `Step_read/throw_ref-handler-catch_ref`, rule 18 of the pinned stream. -/
def throwRefHandlerCatchRefRule : Rule :=
  (.ruleD "throw_ref-handler-catch_ref" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT
   "n" [])), (.expP "x" (.varT "idx" [])), (.expP "l" (.varT "labelidx" [])), (.expP
   "catch'*" (.iterT (.varT "catch" []) .list)), (.expP "a" (.varT "addr" [])), (.expP
   "val*" (.iterT (.varT "val" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.catE (.listE [(.caseE
   "CATCH_REF" (.tupE [(.varE "x"), (.varE "l")]))]) (.iterE (.varE "catch'") (.mk .list
   [(.mk "catch'" (.varE "catch'*"))]))), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")),
   (.caseE "THROW_REF" (.tupE []))])]))])])), (.catE (.iterE (.subE (.varE "val") (.varT
   "val" []) (.varT "instr" [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE
   "REF.EXN_ADDR" (.varE "a")), (.caseE "BR" (.varE "l"))]))]) [(.ifPr (.cmpE .eqOp .boolT
   (.dotE (.idxE (.callE "exninst" [(.expA (.varE "z"))]) (.varE "a")) "TAG") (.idxE (.callE
   "tagaddr" [(.expA (.varE "z"))]) (.projE (.uncaseE (.varE "x") "%") (0))))), (.ifPr
   (.cmpE .eqOp .boolT (.iterE (.varE "val") (.mk .list [(.mk "val" (.varE "val*"))]))
   (.dotE (.idxE (.callE "exninst" [(.expA (.varE "z"))]) (.varE "a")) "FIELDS")))])

/-- `Step_read/throw_ref-handler-catch_all`, rule 19 of the pinned stream. -/
def throwRefHandlerCatchAllRule : Rule :=
  (.ruleD "throw_ref-handler-catch_all" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT
   "n" [])), (.expP "l" (.varT "labelidx" [])), (.expP "catch'*" (.iterT (.varT "catch" [])
   .list)), (.expP "a" (.varT "addr" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.catE (.listE [(.caseE "CATCH_ALL"
   (.varE "l"))]) (.iterE (.varE "catch'") (.mk .list [(.mk "catch'" (.varE "catch'*"))]))),
   (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE []))])]))])])),
   (.listE [(.caseE "BR" (.varE "l"))])]) [])

/-- `Step_read/throw_ref-handler-catch_all_ref`, rule 20 of the pinned stream. -/
def throwRefHandlerCatchAllRefRule : Rule :=
  (.ruleD "throw_ref-handler-catch_all_ref" [(.expP "z" (.varT "state" [])), (.expP "n"
   (.varT "n" [])), (.expP "l" (.varT "labelidx" [])), (.expP "catch'*" (.iterT (.varT
   "catch" []) .list)), (.expP "a" (.varT "addr" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.catE (.listE
   [(.caseE "CATCH_ALL_REF" (.varE "l"))]) (.iterE (.varE "catch'") (.mk .list [(.mk
   "catch'" (.varE "catch'*"))]))), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE
   "THROW_REF" (.tupE []))])]))])])), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE
   "BR" (.varE "l"))])]) [])

/-- `Step_read/throw_ref-handler-next`, rule 21 of the pinned stream. -/
def throwRefHandlerNextRule : Rule :=
  (.ruleD "throw_ref-handler-next" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n"
   [])), (.expP "catch" (.varT "catch" [])), (.expP "catch'*" (.iterT (.varT "catch" [])
   .list)), (.expP "a" (.varT "addr" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.catE (.listE [(.varE "catch")])
   (.iterE (.varE "catch'") (.mk .list [(.mk "catch'" (.varE "catch'*"))]))), (.listE
   [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE "THROW_REF" (.tupE []))])]))])])), (.listE
   [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"), (.iterE (.varE "catch'") (.mk .list [(.mk
   "catch'" (.varE "catch'*"))])), (.listE [(.caseE "REF.EXN_ADDR" (.varE "a")), (.caseE
   "THROW_REF" (.tupE []))])]))])]) [.elsePr])

/-- `Step_read/try_table`, rule 22 of the pinned stream. -/
def tryTableRule : Rule :=
  (.ruleD "try_table" [(.expP "z" (.varT "state" [])), (.expP "m" (.varT "m" [])), (.expP
   "val*" (.iterT (.varT "val" []) .list)), (.expP "bt" (.varT "blocktype" [])), (.expP
   "catch*" (.iterT (.varT "catch" []) .list)), (.expP "instr*" (.iterT (.varT "instr" [])
   .list)), (.expP "n" (.varT "n" [])), (.expP "t_1*" (.iterT (.varT "valtype" []) .list)),
   (.expP "t_2*" (.iterT (.varT "valtype" []) .list))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
   (.mk (.listN (.varE "m") none) [(.mk "val" (.varE "val*"))])) (.listE [(.caseE
   "TRY_TABLE" (.tupE [(.varE "bt"), (.caseE "%" (.tupE [(.iterE (.varE "catch") (.mk .list
   [(.mk "catch" (.varE "catch*"))]))])), (.iterE (.varE "instr") (.mk .list [(.mk "instr"
   (.varE "instr*"))]))]))]))])), (.listE [(.caseE "HANDLER_%{%}%" (.tupE [(.varE "n"),
   (.iterE (.varE "catch") (.mk .list [(.mk "catch" (.varE "catch*"))])), (.listE [(.caseE
   "LABEL_%{%}%" (.tupE [(.varE "n"), (.listE []), (.catE (.iterE (.subE (.varE "val")
   (.varT "val" []) (.varT "instr" [])) (.mk (.listN (.varE "m") none) [(.mk "val" (.varE
   "val*"))])) (.iterE (.varE "instr") (.mk .list [(.mk "instr" (.varE
   "instr*"))])))]))])]))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE "blocktype_" [(.expA
   (.varE "z")), (.expA (.varE "bt"))]) (.caseE "%->_%%" (.tupE [(.caseE "%" (.tupE [(.iterE
   (.varE "t_1") (.mk (.listN (.varE "m") none) [(.mk "t_1" (.varE "t_1*"))]))])), (.listE
   []), (.caseE "%" (.tupE [(.iterE (.varE "t_2") (.mk (.listN (.varE "n") none) [(.mk "t_2"
   (.varE "t_2*"))]))]))]))))])

/-- `Step_read/local.get`, rule 23 of the pinned stream. -/
def localGetRule : Rule :=
  (.ruleD "local.get" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" [])), (.expP
   "val" (.varT "val" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE
   [(.caseE "LOCAL.GET" (.varE "x"))])])), (.listE [(.subE (.varE "val") (.varT "val" [])
   (.varT "instr" []))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE "local" [(.expA (.varE "z")),
   (.expA (.varE "x"))]) (.optE (some (.varE "val")))))])

/-- `Step_read/global.get`, rule 24 of the pinned stream. -/
def globalGetRule : Rule :=
  (.ruleD "global.get" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" [])), (.expP
   "val" (.varT "val" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE
   [(.caseE "GLOBAL.GET" (.varE "x"))])])), (.listE [(.subE (.varE "val") (.varT "val" [])
   (.varT "instr" []))])]) [(.ifPr (.cmpE .eqOp .boolT (.dotE (.callE "global" [(.expA
   (.varE "z")), (.expA (.varE "x"))]) "VALUE") (.varE "val")))])

/-- `Step_read/table.get-oob`, rule 25 of the pinned stream. -/
def tableGetOobRule : Rule :=
  (.ruleD "table.get-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" [])
   (.varT "numtype" [])), (.varE "i")])), (.caseE "TABLE.GET" (.varE "x"))])])), (.listE
   [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .geOp (.numT .natT) (.projE (.uncaseE
   (.varE "i") "%") (0)) (.lenE (.dotE (.callE "table" [(.expA (.varE "z")), (.expA (.varE
   "x"))]) "REFS"))))])

/-- `Step_read/table.get-val`, rule 26 of the pinned stream. -/
def tableGetValRule : Rule :=
  (.ruleD "table.get-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" [])
   (.varT "numtype" [])), (.varE "i")])), (.caseE "TABLE.GET" (.varE "x"))])])), (.listE
   [(.subE (.idxE (.dotE (.callE "table" [(.expA (.varE "z")), (.expA (.varE "x"))]) "REFS")
   (.projE (.uncaseE (.varE "i") "%") (0))) (.varT "ref" []) (.varT "instr" []))])]) [(.ifPr
   (.cmpE .ltOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.lenE (.dotE (.callE
   "table" [(.expA (.varE "z")), (.expA (.varE "x"))]) "REFS"))))])

/-- `Step_read/table.size`, rule 27 of the pinned stream. -/
def tableSizeRule : Rule :=
  (.ruleD "table.size" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" [])), (.expP
   "at" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "lim" (.varT "limits"
   [])), (.expP "rt" (.varT "reftype" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "TABLE.SIZE" (.varE "x"))])])), (.listE [(.caseE "CONST" (.tupE
   [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE
   [(.varE "n")]))]))])]) [(.ifPr (.cmpE .eqOp .boolT (.lenE (.dotE (.callE "table" [(.expA
   (.varE "z")), (.expA (.varE "x"))]) "REFS")) (.varE "n"))), (.ifPr (.cmpE .eqOp .boolT
   (.dotE (.callE "table" [(.expA (.varE "z")), (.expA (.varE "x"))]) "TYPE") (.caseE "%%%"
   (.tupE [(.varE "at"), (.varE "lim"), (.varE "rt")]))))])

/-- `Step_read/table.fill-oob`, rule 28 of the pinned stream. -/
def tableFillOobRule : Rule :=
  (.ruleD "table.fill-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "val" (.varT "val" [])), (.expP "n" (.varT "n" [])), (.expP
   "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "TABLE.FILL" (.varE "x"))])])), (.listE [(.caseE
   "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT)
   (.projE (.uncaseE (.varE "i") "%") (0)) (.varE "n")) (.lenE (.dotE (.callE "table"
   [(.expA (.varE "z")), (.expA (.varE "x"))]) "REFS"))))])

/-- `Step_read/table.fill-zero`, rule 29 of the pinned stream. -/
def tableFillZeroRule : Rule :=
  (.ruleD "table.fill-zero" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "val" (.varT "val" [])), (.expP "n" (.varT "n" [])), (.expP
   "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "TABLE.FILL" (.varE "x"))])])), (.listE [])])
   [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0))))])

/-- `Step_read/table.fill-succ`, rule 30 of the pinned stream. -/
def tableFillSuccRule : Rule :=
  (.ruleD "table.fill-succ" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "val" (.varT "val" [])), (.expP "n" (.varT "n" [])), (.expP
   "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "TABLE.FILL" (.varE "x"))])])), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "TABLE.SET"
   (.varE "x")), (.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE
   "i") "%") (0)) (.numE (.natN 1)))]))])), (.subE (.varE "val") (.varT "val" []) (.varT
   "instr" [])), (.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n")
   .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE
   "TABLE.FILL" (.varE "x"))])]) [.elsePr])

/-- `Step_read/table.copy-oob`, rule 31 of the pinned stream. -/
def tableCopyOobRule : Rule :=
  (.ruleD "table.copy-oob" [(.expP "z" (.varT "state" [])), (.expP "at_1" (.varT "addrtype"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE "at_1") (.varT "addrtype" [])
   (.varT "numtype" [])))])), (.expP "at_2" (.varT "addrtype" [])), (.expP "i_2" (.varT
   "num_" [(.expA (.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])))])),
   (.expP "at'" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x_1" (.varT
   "idx" [])), (.expP "x_2" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.subE
   (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE
   "n")]))])), (.caseE "TABLE.COPY" (.tupE [(.varE "x_1"), (.varE "x_2")]))])])), (.listE
   [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.binE .orOp .boolT (.cmpE .gtOp (.numT .natT)
   (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") (0)) (.varE "n")) (.lenE
   (.dotE (.callE "table" [(.expA (.varE "z")), (.expA (.varE "x_1"))]) "REFS"))) (.cmpE
   .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") (0))
   (.varE "n")) (.lenE (.dotE (.callE "table" [(.expA (.varE "z")), (.expA (.varE "x_2"))])
   "REFS")))))])

/-- `Step_read/table.copy-zero`, rule 32 of the pinned stream. -/
def tableCopyZeroRule : Rule :=
  (.ruleD "table.copy-zero" [(.expP "z" (.varT "state" [])), (.expP "at_1" (.varT "addrtype"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE "at_1") (.varT "addrtype" [])
   (.varT "numtype" [])))])), (.expP "at_2" (.varT "addrtype" [])), (.expP "i_2" (.varT
   "num_" [(.expA (.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])))])),
   (.expP "at'" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx"
   [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.subE
   (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE
   "n")]))])), (.caseE "TABLE.COPY" (.tupE [(.varE "x"), (.varE "y")]))])])), (.listE [])])
   [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0))))])

/-- `Step_read/table.copy-le`, rule 33 of the pinned stream. -/
def tableCopyLeRule : Rule :=
  (.ruleD "table.copy-le" [(.expP "z" (.varT "state" [])), (.expP "at_1" (.varT "addrtype"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE "at_1") (.varT "addrtype" [])
   (.varT "numtype" [])))])), (.expP "at_2" (.varT "addrtype" [])), (.expP "i_2" (.varT
   "num_" [(.expA (.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])))])),
   (.expP "at'" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx"
   [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.subE
   (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE
   "n")]))])), (.caseE "TABLE.COPY" (.tupE [(.varE "x"), (.varE "y")]))])])), (.listE
   [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype"
   [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT "addrtype"
   []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "TABLE.GET" (.varE "y")), (.caseE
   "TABLE.SET" (.varE "x")), (.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype"
   []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE
   (.uncaseE (.varE "i_1") "%") (0)) (.numE (.natN 1)))]))])), (.caseE "CONST" (.tupE
   [(.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE
   [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") (0)) (.numE (.natN
   1)))]))])), (.caseE "CONST" (.tupE [(.subE (.varE "at'") (.varT "addrtype" []) (.varT
   "numtype" [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n")
   .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE
   "TABLE.COPY" (.tupE [(.varE "x"), (.varE "y")]))])]) [.elsePr, (.ifPr (.cmpE .leOp (.numT
   .natT) (.projE (.uncaseE (.varE "i_1") "%") (0)) (.projE (.uncaseE (.varE "i_2") "%")
   (0))))])

/-- `Step_read/table.copy-gt`, rule 34 of the pinned stream. -/
def tableCopyGtRule : Rule :=
  (.ruleD "table.copy-gt" [(.expP "z" (.varT "state" [])), (.expP "at_1" (.varT "addrtype"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE "at_1") (.varT "addrtype" [])
   (.varT "numtype" [])))])), (.expP "at_2" (.varT "addrtype" [])), (.expP "i_2" (.varT
   "num_" [(.expA (.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])))])),
   (.expP "at'" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx"
   [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.subE
   (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE
   "n")]))])), (.caseE "TABLE.COPY" (.tupE [(.varE "x"), (.varE "y")]))])])), (.listE
   [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype"
   [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.binE .addOp (.numT
   .natT) (.projE (.uncaseE (.varE "i_1") "%") (0)) (.varE "n")) .natT .intT) (.cvtE (.numE
   (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE "CONST" (.tupE [(.subE (.varE
   "at_2") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.cvtE (.binE
   .subOp (.numT .intT) (.cvtE (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2")
   "%") (0)) (.varE "n")) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT
   .natT)]))])), (.caseE "TABLE.GET" (.varE "y")), (.caseE "TABLE.SET" (.varE "x")), (.caseE
   "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.subE (.varE "at'") (.varT
   "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT
   .intT) (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT
   .natT)]))])), (.caseE "TABLE.COPY" (.tupE [(.varE "x"), (.varE "y")]))])]) [.elsePr])

/-- `Step_read/table.init-oob`, rule 35 of the pinned stream. -/
def tableInitOobRule : Rule :=
  (.ruleD "table.init-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "j" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "y" (.varT "idx" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST"
   (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "TABLE.INIT" (.tupE [(.varE
   "x"), (.varE "y")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.binE .orOp
   .boolT (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE
   "i") "%") (0)) (.varE "n")) (.lenE (.dotE (.callE "table" [(.expA (.varE "z")), (.expA
   (.varE "x"))]) "REFS"))) (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE
   (.uncaseE (.varE "j") "%") (0)) (.varE "n")) (.lenE (.dotE (.callE "elem" [(.expA (.varE
   "z")), (.expA (.varE "y"))]) "REFS")))))])

/-- `Step_read/table.init-zero`, rule 36 of the pinned stream. -/
def tableInitZeroRule : Rule :=
  (.ruleD "table.init-zero" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "j" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "y" (.varT "idx" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST"
   (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "TABLE.INIT" (.tupE [(.varE
   "x"), (.varE "y")]))])])), (.listE [])]) [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n")
   (.numE (.natN 0))))])

/-- `Step_read/table.init-succ`, rule 37 of the pinned stream. -/
def tableInitSuccRule : Rule :=
  (.ruleD "table.init-succ" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "j" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "y" (.varT "idx" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST"
   (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "TABLE.INIT" (.tupE [(.varE
   "x"), (.varE "y")]))])])), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.subE (.idxE (.dotE (.callE "elem"
   [(.expA (.varE "z")), (.expA (.varE "y"))]) "REFS") (.projE (.uncaseE (.varE "j") "%")
   (0))) (.varT "ref" []) (.varT "instr" [])), (.caseE "TABLE.SET" (.varE "x")), (.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE
   "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.numE
   (.natN 1)))]))])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE
   [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "j") "%") (0)) (.numE (.natN
   1)))]))])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.cvtE
   (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1))
   .natT .intT)) .intT .natT)]))])), (.caseE "TABLE.INIT" (.tupE [(.varE "x"), (.varE
   "y")]))])]) [.elsePr])

/-- `Step_read/load-num-oob`, rule 38 of the pinned stream. -/
def loadNumOobRule : Rule :=
  (.ruleD "load-num-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "nt" (.varT "numtype" [])), (.expP "x" (.varT "idx" [])),
   (.expP "ao" (.varT "memarg" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i")])), (.caseE "LOAD" (.tupE [(.varE "nt"), (.optE none), (.varE
   "x"), (.varE "ao")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp
   (.numT .natT) (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE
   (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE
   (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [(.expA (.varE "nt"))]) .natT .ratT)
   (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE (.callE "mem" [(.expA
   (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step_read/load-num-val`, rule 39 of the pinned stream. -/
def loadNumValRule : Rule :=
  (.ruleD "load-num-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "nt" (.varT "numtype" [])), (.expP "x" (.varT "idx" [])),
   (.expP "ao" (.varT "memarg" [])), (.expP "c" (.varT "num_" [(.expA (.varE "nt"))]))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "LOAD"
   (.tupE [(.varE "nt"), (.optE none), (.varE "x"), (.varE "ao")]))])])), (.listE [(.caseE
   "CONST" (.tupE [(.varE "nt"), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE
   "nbytes_" [(.expA (.varE "nt")), (.expA (.varE "c"))]) (.sliceE (.dotE (.callE "mem"
   [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES") (.binE .addOp (.numT .natT) (.projE
   (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%")
   (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [(.expA (.varE "nt"))])
   .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))))])

/-- `Step_read/load-pack-oob`, rule 40 of the pinned stream. -/
def loadPackOobRule : Rule :=
  (.ruleD "load-pack-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "Inn" (.varT "Inn" [])), (.expP "n" (.varT "n" [])), (.expP
   "sx" (.varT "sx" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "LOAD"
   (.tupE [(.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])), (.optE (some (.caseE
   "%_%" (.tupE [(.caseE "%" (.tupE [(.varE "n")])), (.varE "sx")])))), (.varE "x"), (.varE
   "ao")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT)
   (.binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i")
   "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp
   (.numT .ratT) (.cvtE (.varE "n") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT))
   .ratT .natT)) (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))])
   "BYTES"))))])

/-- `Step_read/load-pack-val`, rule 41 of the pinned stream. -/
def loadPackValRule : Rule :=
  (.ruleD "load-pack-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "Inn" (.varT "Inn" [])), (.expP "n" (.varT "n" [])), (.expP
   "sx" (.varT "sx" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" [])),
   (.expP "c" (.varT "iN" [(.expA (.varE "n"))]))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" [])
   (.varT "numtype" [])), (.varE "i")])), (.caseE "LOAD" (.tupE [(.subE (.varE "Inn") (.varT
   "Inn" []) (.varT "numtype" [])), (.optE (some (.caseE "%_%" (.tupE [(.caseE "%" (.tupE
   [(.varE "n")])), (.varE "sx")])))), (.varE "x"), (.varE "ao")]))])])), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])), (.callE
   "extend__" [(.expA (.varE "n")), (.expA (.callE "size" [(.expA (.subE (.varE "Inn")
   (.varT "Inn" []) (.varT "numtype" [])))])), (.expA (.varE "sx")), (.expA (.varE
   "c"))])]))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE "ibytes_" [(.expA (.varE "n")), (.expA
   (.varE "c"))]) (.sliceE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))])
   "BYTES") (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE
   (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT)
   (.cvtE (.varE "n") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))))])

/-- `Step_read/vload-num-oob`, rule 42 of the pinned stream. -/
def vloadNumOobRule : Rule :=
  (.ruleD "vload-num-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "VLOAD"
   (.tupE [(.caseE "V128" (.tupE [])), (.optE none), (.varE "x"), (.varE "ao")]))])])),
   (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp
   (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE
   (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT)
   (.cvtE (.callE "vsize" [(.expA (.caseE "V128" (.tupE [])))]) .natT .ratT) (.cvtE (.numE
   (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")),
   (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step_read/vload-num-val`, rule 43 of the pinned stream. -/
def vloadNumValRule : Rule :=
  (.ruleD "vload-num-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" [])),
   (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "VLOAD" (.tupE [(.caseE
   "V128" (.tupE [])), (.optE none), (.varE "x"), (.varE "ao")]))])])), (.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp
   .boolT (.callE "vbytes_" [(.expA (.caseE "V128" (.tupE []))), (.expA (.varE "c"))])
   (.sliceE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES") (.binE
   .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE
   (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE
   "vsize" [(.expA (.caseE "V128" (.tupE [])))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT
   .ratT)) .ratT .natT))))])

/-- `Step_read/vload-pack-oob`, rule 44 of the pinned stream. -/
def vloadPackOobRule : Rule :=
  (.ruleD "vload-pack-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "K" (.varT "K" [])), (.expP "M" (.varT "M" [])), (.expP "sx"
   (.varT "sx" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" []))] "%~>%"
   (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE
   "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "VLOAD" (.tupE
   [(.caseE "V128" (.tupE [])), (.optE (some (.caseE "SHAPE%X%_%" (.tupE [(.caseE "%" (.tupE
   [(.varE "K")])), (.varE "M"), (.varE "sx")])))), (.varE "x"), (.varE "ao")]))])])),
   (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp
   (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE
   (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT)
   (.cvtE (.binE .mulOp (.numT .natT) (.varE "K") (.projE (.uncaseE (.varE "M") "%") (0)))
   .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE (.callE
   "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step_read/vload-pack-val`, rule 45 of the pinned stream. -/
def vloadPackValRule : Rule :=
  (.ruleD "vload-pack-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "K" (.varT "K" [])), (.expP "M" (.varT "M" [])), (.expP "sx"
   (.varT "sx" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg" [])), (.expP
   "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "j*" (.iterT (.varT "iN"
   [(.expA (.varE "K"))]) .list)), (.expP "Jnn" (.varT "Jnn" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "VLOAD" (.tupE [(.caseE
   "V128" (.tupE [])), (.optE (some (.caseE "SHAPE%X%_%" (.tupE [(.caseE "%" (.tupE [(.varE
   "K")])), (.varE "M"), (.varE "sx")])))), (.varE "x"), (.varE "ao")]))])])), (.listE
   [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.iterPr (.ifPr
   (.cmpE .eqOp .boolT (.callE "ibytes_" [(.expA (.varE "K")), (.expA (.varE "j"))])
   (.sliceE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES") (.binE
   .addOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0))
   (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT
   .ratT) (.cvtE (.binE .mulOp (.numT .natT) (.varE "k") (.varE "K")) .natT .ratT) (.cvtE
   (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE
   (.varE "K") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)))) (.mk
   (.listN (.projE (.uncaseE (.varE "M") "%") (0)) (some "k")) [(.mk "j" (.varE "j*"))])),
   (.ifPr (.binE .andOp .boolT (.cmpE .eqOp .boolT (.varE "c") (.callE "inv_lanes_" [(.expA
   (.caseE "%X%" (.tupE [(.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" [])),
   (.varE "M")]))), (.expA (.iterE (.callE "extend__" [(.expA (.varE "K")), (.expA (.callE
   "jsizenn" [(.expA (.varE "Jnn"))])), (.expA (.varE "sx")), (.expA (.varE "j"))]) (.mk
   (.listN (.projE (.uncaseE (.varE "M") "%") (0)) none) [(.mk "j" (.varE "j*"))])))]))
   (.cmpE .eqOp .boolT (.callE "jsizenn" [(.expA (.varE "Jnn"))]) (.binE .mulOp (.numT
   .natT) (.varE "K") (.numE (.natN 2))))))])

/-- `Step_read/vload-splat-oob`, rule 46 of the pinned stream. -/
def vloadSplatOobRule : Rule :=
  (.ruleD "vload-splat-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "N" (.varT "N" [])), (.expP "x" (.varT "idx" [])), (.expP "ao"
   (.varT "memarg" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.caseE "VLOAD" (.tupE [(.caseE "V128" (.tupE [])), (.optE (some (.caseE "SPLAT"
   (.caseE "%" (.tupE [(.varE "N")]))))), (.varE "x"), (.varE "ao")]))])])), (.listE
   [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT
   .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE
   (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT)
   (.cvtE (.varE "N") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
   (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step_read/vload-splat-val`, rule 47 of the pinned stream. -/
def vloadSplatValRule : Rule :=
  (.ruleD "vload-splat-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "N" (.varT "N" [])), (.expP "x" (.varT "idx" [])), (.expP "ao"
   (.varT "memarg" [])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "j" (.varT "iN" [(.expA (.varE "N"))])), (.expP "Jnn" (.varT "Jnn" [])), (.expP
   "M" (.varT "M" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.caseE "VLOAD" (.tupE [(.caseE "V128" (.tupE [])), (.optE (some (.caseE "SPLAT"
   (.caseE "%" (.tupE [(.varE "N")]))))), (.varE "x"), (.varE "ao")]))])])), (.listE
   [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE
   .eqOp .boolT (.callE "ibytes_" [(.expA (.varE "N")), (.expA (.varE "j"))]) (.sliceE
   (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES") (.binE .addOp
   (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE
   "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "N") .natT
   .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)))), (.ifPr (.cmpE .eqOp .boolT
   (.varE "N") (.callE "jsize" [(.expA (.varE "Jnn"))]))), (.ifPr (.cmpE .eqOp .boolT (.cvtE
   (.projE (.uncaseE (.varE "M") "%") (0)) .natT .ratT) (.binE .divOp (.numT .ratT) (.cvtE
   (.numE (.natN 128)) .natT .ratT) (.cvtE (.varE "N") .natT .ratT)))), (.ifPr (.cmpE .eqOp
   .boolT (.varE "c") (.callE "inv_lanes_" [(.expA (.caseE "%X%" (.tupE [(.subE (.varE
   "Jnn") (.varT "Jnn" []) (.varT "lanetype" [])), (.varE "M")]))), (.expA (.iterE (.caseE
   "%" (.tupE [(.projE (.uncaseE (.varE "j") "%") (0))])) (.mk (.listN (.projE (.uncaseE
   (.varE "M") "%") (0)) none) [])))])))])

/-- `Step_read/vload-zero-oob`, rule 48 of the pinned stream. -/
def vloadZeroOobRule : Rule :=
  (.ruleD "vload-zero-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "N" (.varT "N" [])), (.expP "x" (.varT "idx" [])), (.expP "ao"
   (.varT "memarg" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.caseE "VLOAD" (.tupE [(.caseE "V128" (.tupE [])), (.optE (some (.caseE "ZERO"
   (.tupE [(.caseE "%" (.tupE [(.varE "N")]))])))), (.varE "x"), (.varE "ao")]))])])),
   (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp
   (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE
   (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT)
   (.cvtE (.varE "N") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
   (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step_read/vload-zero-val`, rule 49 of the pinned stream. -/
def vloadZeroValRule : Rule :=
  (.ruleD "vload-zero-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "N" (.varT "N" [])), (.expP "x" (.varT "idx" [])), (.expP "ao"
   (.varT "memarg" [])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "j" (.varT "iN" [(.expA (.varE "N"))]))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" [])
   (.varT "numtype" [])), (.varE "i")])), (.caseE "VLOAD" (.tupE [(.caseE "V128" (.tupE
   [])), (.optE (some (.caseE "ZERO" (.tupE [(.caseE "%" (.tupE [(.varE "N")]))])))), (.varE
   "x"), (.varE "ao")]))])])), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])),
   (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE "ibytes_" [(.expA (.varE "N")),
   (.expA (.varE "j"))]) (.sliceE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE
   "x"))]) "BYTES") (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0))
   (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT
   .ratT) (.cvtE (.varE "N") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT
   .natT)))), (.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE "extend__" [(.expA (.varE
   "N")), (.expA (.numE (.natN 128))), (.expA (.caseE "U" (.tupE []))), (.expA (.varE
   "j"))])))])

/-- `Step_read/vload_lane-oob`, rule 50 of the pinned stream. -/
def vloadLaneOobRule : Rule :=
  (.ruleD "vload_lane-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "N" (.varT "N" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg"
   [])), (.expP "j" (.varT "laneidx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])),
   (.varE "c_1")])), (.caseE "VLOAD_LANE" (.tupE [(.caseE "V128" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "N")])), (.varE "x"), (.varE "ao"), (.varE "j")]))])])), (.listE [(.caseE
   "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT)
   (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE
   (.dotE (.varE "ao") "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE
   "N") .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE
   (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step_read/vload_lane-val`, rule 51 of the pinned stream. -/
def vloadLaneValRule : Rule :=
  (.ruleD "vload_lane-val" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "N" (.varT "N" [])), (.expP "x" (.varT "idx" [])), (.expP "ao" (.varT "memarg"
   [])), (.expP "j" (.varT "laneidx" [])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128"
   (.tupE [])))])), (.expP "k" (.varT "iN" [(.expA (.varE "N"))])), (.expP "Jnn" (.varT
   "Jnn" [])), (.expP "M" (.varT "M" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])),
   (.varE "c_1")])), (.caseE "VLOAD_LANE" (.tupE [(.caseE "V128" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "N")])), (.varE "x"), (.varE "ao"), (.varE "j")]))])])), (.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp
   .boolT (.callE "ibytes_" [(.expA (.varE "N")), (.expA (.varE "k"))]) (.sliceE (.dotE
   (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x"))]) "BYTES") (.binE .addOp (.numT
   .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.projE (.uncaseE (.dotE (.varE "ao")
   "OFFSET") "%") (0))) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.varE "N") .natT .ratT)
   (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)))), (.ifPr (.cmpE .eqOp .boolT (.varE
   "N") (.callE "jsize" [(.expA (.varE "Jnn"))]))), (.ifPr (.cmpE .eqOp .boolT (.cvtE
   (.projE (.uncaseE (.varE "M") "%") (0)) .natT .ratT) (.binE .divOp (.numT .ratT) (.cvtE
   (.callE "vsize" [(.expA (.caseE "V128" (.tupE [])))]) .natT .ratT) (.cvtE (.varE "N")
   .natT .ratT)))), (.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE "inv_lanes_" [(.expA
   (.caseE "%X%" (.tupE [(.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" [])),
   (.varE "M")]))), (.expA (.updE (.callE "lanes_" [(.expA (.caseE "%X%" (.tupE [(.subE
   (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" [])), (.varE "M")]))), (.expA (.varE
   "c_1"))]) (.idxP .rootP (.projE (.uncaseE (.varE "j") "%") (0))) (.caseE "%" (.tupE
   [(.projE (.uncaseE (.varE "k") "%") (0))]))))])))])

/-- `Step_read/memory.size`, rule 52 of the pinned stream. -/
def memorySizeRule : Rule :=
  (.ruleD "memory.size" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" [])),
   (.expP "at" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "lim" (.varT
   "limits" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "MEMORY.SIZE" (.varE "x"))])])), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at")
   (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE "n")]))]))])])
   [(.ifPr (.cmpE .eqOp .boolT (.binE .mulOp (.numT .natT) (.varE "n") (.binE .mulOp (.numT
   .natT) (.numE (.natN 64)) (.callE "Ki" []))) (.lenE (.dotE (.callE "mem" [(.expA (.varE
   "z")), (.expA (.varE "x"))]) "BYTES")))), (.ifPr (.cmpE .eqOp .boolT (.dotE (.callE "mem"
   [(.expA (.varE "z")), (.expA (.varE "x"))]) "TYPE") (.caseE "%%PAGE" (.tupE [(.varE
   "at"), (.varE "lim")]))))])

/-- `Step_read/memory.fill-oob`, rule 53 of the pinned stream. -/
def memoryFillOobRule : Rule :=
  (.ruleD "memory.fill-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "val" (.varT "val" [])), (.expP "n" (.varT "n" [])), (.expP
   "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "MEMORY.FILL" (.varE "x"))])])), (.listE [(.caseE
   "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT)
   (.projE (.uncaseE (.varE "i") "%") (0)) (.varE "n")) (.lenE (.dotE (.callE "mem" [(.expA
   (.varE "z")), (.expA (.varE "x"))]) "BYTES"))))])

/-- `Step_read/memory.fill-zero`, rule 54 of the pinned stream. -/
def memoryFillZeroRule : Rule :=
  (.ruleD "memory.fill-zero" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "val" (.varT "val" [])), (.expP "n" (.varT "n" [])), (.expP
   "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "MEMORY.FILL" (.varE "x"))])])), (.listE [])])
   [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0))))])

/-- `Step_read/memory.fill-succ`, rule 55 of the pinned stream. -/
def memoryFillSuccRule : Rule :=
  (.ruleD "memory.fill-succ" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "val" (.varT "val" [])), (.expP "n" (.varT "n" [])), (.expP
   "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "MEMORY.FILL" (.varE "x"))])])), (.listE [(.caseE
   "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "STORE"
   (.tupE [(.caseE "I32" (.tupE [])), (.optE (some (.caseE "%" (.tupE [(.caseE "%" (.tupE
   [(.numE (.natN 8))]))])))), (.varE "x"), (.callE "memarg0" [])])), (.caseE "CONST" (.tupE
   [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE
   [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.numE (.natN
   1)))]))])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE
   (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE "MEMORY.FILL" (.varE "x"))])])
   [.elsePr])

/-- `Step_read/memory.copy-oob`, rule 56 of the pinned stream. -/
def memoryCopyOobRule : Rule :=
  (.ruleD "memory.copy-oob" [(.expP "z" (.varT "state" [])), (.expP "at_1" (.varT "addrtype"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE "at_1") (.varT "addrtype" [])
   (.varT "numtype" [])))])), (.expP "at_2" (.varT "addrtype" [])), (.expP "i_2" (.varT
   "num_" [(.expA (.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])))])),
   (.expP "at'" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x_1" (.varT
   "idx" [])), (.expP "x_2" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.subE
   (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE
   "n")]))])), (.caseE "MEMORY.COPY" (.tupE [(.varE "x_1"), (.varE "x_2")]))])])), (.listE
   [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.binE .orOp .boolT (.cmpE .gtOp (.numT .natT)
   (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") (0)) (.varE "n")) (.lenE
   (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x_1"))]) "BYTES"))) (.cmpE
   .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") (0))
   (.varE "n")) (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA (.varE "x_2"))])
   "BYTES")))))])

/-- `Step_read/memory.copy-zero`, rule 57 of the pinned stream. -/
def memoryCopyZeroRule : Rule :=
  (.ruleD "memory.copy-zero" [(.expP "z" (.varT "state" [])), (.expP "at_1" (.varT
   "addrtype" [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE "at_1") (.varT
   "addrtype" []) (.varT "numtype" [])))])), (.expP "at_2" (.varT "addrtype" [])), (.expP
   "i_2" (.varT "num_" [(.expA (.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype"
   [])))])), (.expP "at'" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x_1"
   (.varT "idx" [])), (.expP "x_2" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype"
   []) (.varT "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE
   "at_2") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "MEMORY.COPY" (.tupE [(.varE "x_1"), (.varE
   "x_2")]))])])), (.listE [])]) [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE
   (.natN 0))))])

/-- `Step_read/memory.copy-le`, rule 58 of the pinned stream. -/
def memoryCopyLeRule : Rule :=
  (.ruleD "memory.copy-le" [(.expP "z" (.varT "state" [])), (.expP "at_1" (.varT "addrtype"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE "at_1") (.varT "addrtype" [])
   (.varT "numtype" [])))])), (.expP "at_2" (.varT "addrtype" [])), (.expP "i_2" (.varT
   "num_" [(.expA (.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])))])),
   (.expP "at'" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x_1" (.varT
   "idx" [])), (.expP "x_2" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.subE
   (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE
   "n")]))])), (.caseE "MEMORY.COPY" (.tupE [(.varE "x_1"), (.varE "x_2")]))])])), (.listE
   [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype"
   [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT "addrtype"
   []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "LOAD" (.tupE [(.caseE "I32" (.tupE
   [])), (.optE (some (.caseE "%_%" (.tupE [(.caseE "%" (.tupE [(.numE (.natN 8))])),
   (.caseE "U" (.tupE []))])))), (.varE "x_2"), (.callE "memarg0" [])])), (.caseE "STORE"
   (.tupE [(.caseE "I32" (.tupE [])), (.optE (some (.caseE "%" (.tupE [(.caseE "%" (.tupE
   [(.numE (.natN 8))]))])))), (.varE "x_1"), (.callE "memarg0" [])])), (.caseE "CONST"
   (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%"
   (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") (0)) (.numE
   (.natN 1)))]))])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT "addrtype" [])
   (.varT "numtype" [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE
   (.varE "i_2") "%") (0)) (.numE (.natN 1)))]))])), (.caseE "CONST" (.tupE [(.subE (.varE
   "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.cvtE (.binE
   .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT
   .intT)) .intT .natT)]))])), (.caseE "MEMORY.COPY" (.tupE [(.varE "x_1"), (.varE
   "x_2")]))])]) [.elsePr, (.ifPr (.cmpE .leOp (.numT .natT) (.projE (.uncaseE (.varE "i_1")
   "%") (0)) (.projE (.uncaseE (.varE "i_2") "%") (0))))])

/-- `Step_read/memory.copy-gt`, rule 59 of the pinned stream. -/
def memoryCopyGtRule : Rule :=
  (.ruleD "memory.copy-gt" [(.expP "z" (.varT "state" [])), (.expP "at_1" (.varT "addrtype"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.subE (.varE "at_1") (.varT "addrtype" [])
   (.varT "numtype" [])))])), (.expP "at_2" (.varT "addrtype" [])), (.expP "i_2" (.varT
   "num_" [(.expA (.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])))])),
   (.expP "at'" (.varT "addrtype" [])), (.expP "n" (.varT "n" [])), (.expP "x_1" (.varT
   "idx" [])), (.expP "x_2" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT
   "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE [(.subE (.varE "at_2") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.subE
   (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.varE
   "n")]))])), (.caseE "MEMORY.COPY" (.tupE [(.varE "x_1"), (.varE "x_2")]))])])), (.listE
   [(.caseE "CONST" (.tupE [(.subE (.varE "at_1") (.varT "addrtype" []) (.varT "numtype"
   [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.binE .addOp (.numT
   .natT) (.projE (.uncaseE (.varE "i_1") "%") (0)) (.varE "n")) .natT .intT) (.cvtE (.numE
   (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE "CONST" (.tupE [(.subE (.varE
   "at_2") (.varT "addrtype" []) (.varT "numtype" [])), (.caseE "%" (.tupE [(.cvtE (.binE
   .subOp (.numT .intT) (.cvtE (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2")
   "%") (0)) (.varE "n")) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT
   .natT)]))])), (.caseE "LOAD" (.tupE [(.caseE "I32" (.tupE [])), (.optE (some (.caseE
   "%_%" (.tupE [(.caseE "%" (.tupE [(.numE (.natN 8))])), (.caseE "U" (.tupE []))])))),
   (.varE "x_2"), (.callE "memarg0" [])])), (.caseE "STORE" (.tupE [(.caseE "I32" (.tupE
   [])), (.optE (some (.caseE "%" (.tupE [(.caseE "%" (.tupE [(.numE (.natN 8))]))])))),
   (.varE "x_1"), (.callE "memarg0" [])])), (.caseE "CONST" (.tupE [(.subE (.varE "at_1")
   (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i_1")])), (.caseE "CONST" (.tupE
   [(.subE (.varE "at_2") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i_2")])),
   (.caseE "CONST" (.tupE [(.subE (.varE "at'") (.varT "addrtype" []) (.varT "numtype" [])),
   (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT)
   (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE "MEMORY.COPY" (.tupE
   [(.varE "x_1"), (.varE "x_2")]))])]) [.elsePr])

/-- `Step_read/memory.init-oob`, rule 60 of the pinned stream. -/
def memoryInitOobRule : Rule :=
  (.ruleD "memory.init-oob" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "j" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "y" (.varT "idx" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST"
   (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "MEMORY.INIT" (.tupE [(.varE
   "x"), (.varE "y")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.binE .orOp
   .boolT (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE
   "i") "%") (0)) (.varE "n")) (.lenE (.dotE (.callE "mem" [(.expA (.varE "z")), (.expA
   (.varE "x"))]) "BYTES"))) (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE
   (.uncaseE (.varE "j") "%") (0)) (.varE "n")) (.lenE (.dotE (.callE "data" [(.expA (.varE
   "z")), (.expA (.varE "y"))]) "BYTES")))))])

/-- `Step_read/memory.init-zero`, rule 61 of the pinned stream. -/
def memoryInitZeroRule : Rule :=
  (.ruleD "memory.init-zero" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "j" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "y" (.varT "idx" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST"
   (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "MEMORY.INIT" (.tupE [(.varE
   "x"), (.varE "y")]))])])), (.listE [])]) [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n")
   (.numE (.natN 0))))])

/-- `Step_read/memory.init-succ`, rule 62 of the pinned stream. -/
def memoryInitSuccRule : Rule :=
  (.ruleD "memory.init-succ" [(.expP "z" (.varT "state" [])), (.expP "at" (.varT "addrtype"
   [])), (.expP "i" (.varT "num_" [(.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT
   "numtype" [])))])), (.expP "j" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "y" (.varT "idx" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.subE
   (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST"
   (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "MEMORY.INIT" (.tupE [(.varE
   "x"), (.varE "y")]))])])), (.listE [(.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT
   "addrtype" []) (.varT "numtype" [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.caseE
   "I32" (.tupE [])), (.caseE "%" (.tupE [(.projE (.uncaseE (.idxE (.dotE (.callE "data"
   [(.expA (.varE "z")), (.expA (.varE "y"))]) "BYTES") (.projE (.uncaseE (.varE "j") "%")
   (0))) "%") (0))]))])), (.caseE "STORE" (.tupE [(.caseE "I32" (.tupE [])), (.optE (some
   (.caseE "%" (.tupE [(.caseE "%" (.tupE [(.numE (.natN 8))]))])))), (.varE "x"), (.callE
   "memarg0" [])])), (.caseE "CONST" (.tupE [(.subE (.varE "at") (.varT "addrtype" [])
   (.varT "numtype" [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE
   (.varE "i") "%") (0)) (.numE (.natN 1)))]))])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE
   "j") "%") (0)) (.numE (.natN 1)))]))])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT
   .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE "MEMORY.INIT"
   (.tupE [(.varE "x"), (.varE "y")]))])]) [.elsePr])

/-- `Step_read/ref.null`, rule 63 of the pinned stream. -/
def refNullRule : Rule :=
  (.ruleD "ref.null" [(.expP "z" (.varT "state" [])), (.expP "ht" (.varT "heaptype" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.NULL" (.varE
   "ht"))])])), (.listE [(.caseE "REF.NULL_ADDR" (.tupE []))])]) [])

/-- `Step_read/ref.func`, rule 64 of the pinned stream. -/
def refFuncRule : Rule :=
  (.ruleD "ref.func" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx" []))] "%~>%"
   (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.FUNC" (.varE "x"))])])),
   (.listE [(.caseE "REF.FUNC_ADDR" (.idxE (.dotE (.callE "moduleinst" [(.expA (.varE
   "z"))]) "FUNCS") (.projE (.uncaseE (.varE "x") "%") (0))))])]) [])

/-- `Step_read/ref.test-true`, rule 65 of the pinned stream. -/
def refTestTrueRule : Rule :=
  (.ruleD "ref.test-true" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame" [])),
   (.expP "ref" (.varT "ref" [])), (.expP "rt" (.varT "reftype" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.subE (.varE
   "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.TEST" (.varE "rt"))])])),
   (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.numE
   (.natN 1))]))]))])]) [(.rulePr "Ref_ok" [] "%|-%:%" (.tupE [(.varE "s"), (.varE "ref"),
   (.callE "inst_reftype" [(.expA (.dotE (.varE "f") "MODULE")), (.expA (.varE "rt"))])]))])

/-- `Step_read/ref.test-false`, rule 66 of the pinned stream. -/
def refTestFalseRule : Rule :=
  (.ruleD "ref.test-false" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame" [])),
   (.expP "ref" (.varT "ref" [])), (.expP "rt" (.varT "reftype" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.subE (.varE
   "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.TEST" (.varE "rt"))])])),
   (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.numE
   (.natN 0))]))]))])]) [.elsePr])

/-- `Step_read/ref.cast-succeed`, rule 67 of the pinned stream. -/
def refCastSucceedRule : Rule :=
  (.ruleD "ref.cast-succeed" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame"
   [])), (.expP "ref" (.varT "ref" [])), (.expP "rt" (.varT "reftype" []))] "%~>%" (.tupE
   [(.caseE "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.subE
   (.varE "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.CAST" (.varE
   "rt"))])])), (.listE [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" []))])])
   [(.rulePr "Ref_ok" [] "%|-%:%" (.tupE [(.varE "s"), (.varE "ref"), (.callE "inst_reftype"
   [(.expA (.dotE (.varE "f") "MODULE")), (.expA (.varE "rt"))])]))])

/-- `Step_read/ref.cast-fail`, rule 68 of the pinned stream. -/
def refCastFailRule : Rule :=
  (.ruleD "ref.cast-fail" [(.expP "s" (.varT "store" [])), (.expP "f" (.varT "frame" [])),
   (.expP "ref" (.varT "ref" [])), (.expP "rt" (.varT "reftype" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.caseE "%;%" (.tupE [(.varE "s"), (.varE "f")])), (.listE [(.subE (.varE
   "ref") (.varT "ref" []) (.varT "instr" [])), (.caseE "REF.CAST" (.varE "rt"))])])),
   (.listE [(.caseE "TRAP" (.tupE []))])]) [.elsePr])

/-- `Step_read/struct.new_default`, rule 69 of the pinned stream. -/
def structNewDefaultRule : Rule :=
  (.ruleD "struct.new_default" [(.expP "z" (.varT "state" [])), (.expP "x" (.varT "idx"
   [])), (.expP "val*" (.iterT (.varT "val" []) .list)), (.expP "mut?*" (.iterT (.iterT
   (.varT "mut" []) .opt) .list)), (.expP "zt*" (.iterT (.varT "storagetype" []) .list))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "STRUCT.NEW_DEFAULT"
   (.varE "x"))])])), (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr"
   [])) (.mk .list [(.mk "val" (.varE "val*"))])) (.listE [(.caseE "STRUCT.NEW" (.varE
   "x"))]))]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")),
   (.expA (.varE "x"))]), (.caseE "STRUCT" (.caseE "%" (.tupE [(.iterE (.caseE "%%" (.tupE
   [(.iterE (.varE "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])) (.mk
   .list [(.mk "mut?" (.varE "mut?*")), (.mk "zt" (.varE "zt*"))]))])))])), (.iterPr (.ifPr
   (.cmpE .eqOp .boolT (.callE "default_" [(.expA (.callE "unpack" [(.expA (.varE
   "zt"))]))]) (.optE (some (.varE "val"))))) (.mk .list [(.mk "val" (.varE "val*")), (.mk
   "zt" (.varE "zt*"))]))])

/-- `Step_read/struct.get-null`, rule 70 of the pinned stream. -/
def structGetNullRule : Rule :=
  (.ruleD "struct.get-null" [(.expP "z" (.varT "state" [])), (.expP "sx?" (.iterT (.varT
   "sx" []) .opt)), (.expP "x" (.varT "idx" [])), (.expP "i" (.varT "fieldidx" []))] "%~>%"
   (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.NULL_ADDR" (.tupE [])),
   (.caseE "STRUCT.GET" (.tupE [(.iterE (.varE "sx") (.mk .opt [(.mk "sx" (.varE "sx?"))])),
   (.varE "x"), (.varE "i")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_read/struct.get-struct`, rule 71 of the pinned stream. -/
def structGetStructRule : Rule :=
  (.ruleD "struct.get-struct" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "sx?" (.iterT (.varT "sx" []) .opt)), (.expP "x" (.varT "idx" [])), (.expP
   "i" (.varT "fieldidx" [])), (.expP "zt*" (.iterT (.varT "storagetype" []) .list)), (.expP
   "mut?*" (.iterT (.iterT (.varT "mut" []) .opt) .list))] "%~>%" (.tupE [(.caseE "%;%"
   (.tupE [(.varE "z"), (.listE [(.caseE "REF.STRUCT_ADDR" (.varE "a")), (.caseE
   "STRUCT.GET" (.tupE [(.iterE (.varE "sx") (.mk .opt [(.mk "sx" (.varE "sx?"))])), (.varE
   "x"), (.varE "i")]))])])), (.listE [(.subE (.callE "unpackfield_" [(.expA (.idxE (.iterE
   (.varE "zt") (.mk .list [(.mk "zt" (.varE "zt*"))])) (.projE (.uncaseE (.varE "i") "%")
   (0)))), (.expA (.iterE (.varE "sx") (.mk .opt [(.mk "sx" (.varE "sx?"))]))), (.expA
   (.idxE (.dotE (.idxE (.callE "structinst" [(.expA (.varE "z"))]) (.varE "a")) "FIELDS")
   (.projE (.uncaseE (.varE "i") "%") (0))))]) (.varT "val" []) (.varT "instr" []))])])
   [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")), (.expA (.varE
   "x"))]), (.caseE "STRUCT" (.caseE "%" (.tupE [(.iterE (.caseE "%%" (.tupE [(.iterE (.varE
   "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])) (.mk .list [(.mk "mut?"
   (.varE "mut?*")), (.mk "zt" (.varE "zt*"))]))])))]))])

/-- `Step_read/array.new_default`, rule 72 of the pinned stream. -/
def arrayNewDefaultRule : Rule :=
  (.ruleD "array.new_default" [(.expP "z" (.varT "state" [])), (.expP "n" (.varT "n" [])),
   (.expP "x" (.varT "idx" [])), (.expP "val" (.varT "val" [])), (.expP "mut?" (.iterT
   (.varT "mut" []) .opt)), (.expP "zt" (.varT "storagetype" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])),
   (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.NEW_DEFAULT" (.varE "x"))])])),
   (.catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (.mk (.listN
   (.varE "n") none) [])) (.listE [(.caseE "ARRAY.NEW_FIXED" (.tupE [(.varE "x"), (.caseE
   "%" (.tupE [(.varE "n")]))]))]))]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type"
   [(.expA (.varE "z")), (.expA (.varE "x"))]), (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE
   (.varE "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])))])), (.ifPr
   (.cmpE .eqOp .boolT (.callE "default_" [(.expA (.callE "unpack" [(.expA (.varE
   "zt"))]))]) (.optE (some (.varE "val")))))])

/-- `Step_read/array.new_elem-oob`, rule 73 of the pinned stream. -/
def arrayNewElemOobRule : Rule :=
  (.ruleD "array.new_elem-oob" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT
   "idx" [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE
   "ARRAY.NEW_ELEM" (.tupE [(.varE "x"), (.varE "y")]))])])), (.listE [(.caseE "TRAP" (.tupE
   []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE
   (.varE "i") "%") (0)) (.varE "n")) (.lenE (.dotE (.callE "elem" [(.expA (.varE "z")),
   (.expA (.varE "y"))]) "REFS"))))])

/-- `Step_read/array.new_elem-alloc`, rule 74 of the pinned stream. -/
def arrayNewElemAllocRule : Rule :=
  (.ruleD "array.new_elem-alloc" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT
   "idx" [])), (.expP "y" (.varT "idx" [])), (.expP "ref*" (.iterT (.varT "ref" []) .list))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.NEW_ELEM" (.tupE [(.varE
   "x"), (.varE "y")]))])])), (.catE (.iterE (.subE (.varE "ref") (.varT "ref" []) (.varT
   "instr" [])) (.mk (.listN (.varE "n") none) [(.mk "ref" (.varE "ref*"))])) (.listE
   [(.caseE "ARRAY.NEW_FIXED" (.tupE [(.varE "x"), (.caseE "%" (.tupE [(.varE
   "n")]))]))]))]) [(.ifPr (.cmpE .eqOp .boolT (.iterE (.varE "ref") (.mk (.listN (.varE
   "n") none) [(.mk "ref" (.varE "ref*"))])) (.sliceE (.dotE (.callE "elem" [(.expA (.varE
   "z")), (.expA (.varE "y"))]) "REFS") (.projE (.uncaseE (.varE "i") "%") (0)) (.varE
   "n"))))])

/-- `Step_read/array.new_data-oob`, rule 75 of the pinned stream. -/
def arrayNewDataOobRule : Rule :=
  (.ruleD "array.new_data-oob" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT
   "idx" [])), (.expP "y" (.varT "idx" [])), (.expP "mut?" (.iterT (.varT "mut" []) .opt)),
   (.expP "zt" (.varT "storagetype" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE
   "ARRAY.NEW_DATA" (.tupE [(.varE "x"), (.varE "y")]))])])), (.listE [(.caseE "TRAP" (.tupE
   []))])]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")), (.expA
   (.varE "x"))]), (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE (.varE "mut") (.mk .opt
   [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])))])), (.ifPr (.cmpE .gtOp (.numT .natT)
   (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.cvtE (.binE .divOp
   (.numT .ratT) (.cvtE (.binE .mulOp (.numT .natT) (.varE "n") (.callE "zsize" [(.expA
   (.varE "zt"))])) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE
   (.dotE (.callE "data" [(.expA (.varE "z")), (.expA (.varE "y"))]) "BYTES"))))])

/-- `Step_read/array.new_data-num`, rule 76 of the pinned stream. -/
def arrayNewDataNumRule : Rule :=
  (.ruleD "array.new_data-num" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT
   "idx" [])), (.expP "y" (.varT "idx" [])), (.expP "zt" (.varT "storagetype" [])), (.expP
   "c*" (.iterT (.varT "lit_" [(.expA (.varE "zt"))]) .list)), (.expP "mut?" (.iterT (.varT
   "mut" []) .opt))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE
   "ARRAY.NEW_DATA" (.tupE [(.varE "x"), (.varE "y")]))])])), (.catE (.iterE (.callE "const"
   [(.expA (.callE "cunpack" [(.expA (.varE "zt"))])), (.expA (.callE "cunpacknum_" [(.expA
   (.varE "zt")), (.expA (.varE "c"))]))]) (.mk (.listN (.varE "n") none) [(.mk "c" (.varE
   "c*"))])) (.listE [(.caseE "ARRAY.NEW_FIXED" (.tupE [(.varE "x"), (.caseE "%" (.tupE
   [(.varE "n")]))]))]))]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA
   (.varE "z")), (.expA (.varE "x"))]), (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE (.varE
   "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])))])), (.ifPr (.cmpE .eqOp
   .boolT (.callE "concatn_" [(.typA (.varT "byte" [])), (.expA (.iterE (.callE "zbytes_"
   [(.expA (.varE "zt")), (.expA (.varE "c"))]) (.mk (.listN (.varE "n") none) [(.mk "c"
   (.varE "c*"))]))), (.expA (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize"
   [(.expA (.varE "zt"))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT
   .natT))]) (.sliceE (.dotE (.callE "data" [(.expA (.varE "z")), (.expA (.varE "y"))])
   "BYTES") (.projE (.uncaseE (.varE "i") "%") (0)) (.cvtE (.binE .divOp (.numT .ratT)
   (.cvtE (.binE .mulOp (.numT .natT) (.varE "n") (.callE "zsize" [(.expA (.varE "zt"))]))
   .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))))])

/-- `Step_read/array.get-null`, rule 77 of the pinned stream. -/
def arrayGetNullRule : Rule :=
  (.ruleD "array.get-null" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_" [(.expA
   (.caseE "I32" (.tupE [])))])), (.expP "sx?" (.iterT (.varT "sx" []) .opt)), (.expP "x"
   (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "REF.NULL_ADDR" (.tupE [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i")])), (.caseE "ARRAY.GET" (.tupE [(.iterE (.varE "sx") (.mk .opt [(.mk "sx" (.varE
   "sx?"))])), (.varE "x")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_read/array.get-oob`, rule 78 of the pinned stream. -/
def arrayGetOobRule : Rule :=
  (.ruleD "array.get-oob" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" [])),
   (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "sx?" (.iterT
   (.varT "sx" []) .opt)), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "ARRAY.GET" (.tupE [(.iterE (.varE
   "sx") (.mk .opt [(.mk "sx" (.varE "sx?"))])), (.varE "x")]))])])), (.listE [(.caseE
   "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .geOp (.numT .natT) (.projE (.uncaseE (.varE "i")
   "%") (0)) (.lenE (.dotE (.idxE (.callE "arrayinst" [(.expA (.varE "z"))]) (.varE "a"))
   "FIELDS"))))])

/-- `Step_read/array.get-array`, rule 79 of the pinned stream. -/
def arrayGetArrayRule : Rule :=
  (.ruleD "array.get-array" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" [])),
   (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "sx?" (.iterT
   (.varT "sx" []) .opt)), (.expP "x" (.varT "idx" [])), (.expP "zt" (.varT "storagetype"
   [])), (.expP "mut?" (.iterT (.varT "mut" []) .opt))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "ARRAY.GET" (.tupE [(.iterE (.varE
   "sx") (.mk .opt [(.mk "sx" (.varE "sx?"))])), (.varE "x")]))])])), (.listE [(.subE
   (.callE "unpackfield_" [(.expA (.varE "zt")), (.expA (.iterE (.varE "sx") (.mk .opt [(.mk
   "sx" (.varE "sx?"))]))), (.expA (.idxE (.dotE (.idxE (.callE "arrayinst" [(.expA (.varE
   "z"))]) (.varE "a")) "FIELDS") (.projE (.uncaseE (.varE "i") "%") (0))))]) (.varT "val"
   []) (.varT "instr" []))])]) [(.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA
   (.varE "z")), (.expA (.varE "x"))]), (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE (.varE
   "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])))]))])

/-- `Step_read/array.len-null`, rule 80 of the pinned stream. -/
def arrayLenNullRule : Rule :=
  (.ruleD "array.len-null" [(.expP "z" (.varT "state" []))] "%~>%" (.tupE [(.caseE "%;%"
   (.tupE [(.varE "z"), (.listE [(.caseE "REF.NULL_ADDR" (.tupE [])), (.caseE "ARRAY.LEN"
   (.tupE []))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_read/array.len-array`, rule 81 of the pinned stream. -/
def arrayLenArrayRule : Rule :=
  (.ruleD "array.len-array" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" []))]
   "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR"
   (.varE "a")), (.caseE "ARRAY.LEN" (.tupE []))])])), (.listE [(.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.lenE (.dotE (.idxE (.callE "arrayinst"
   [(.expA (.varE "z"))]) (.varE "a")) "FIELDS"))]))]))])]) [])

/-- `Step_read/array.fill-null`, rule 82 of the pinned stream. -/
def arrayFillNullRule : Rule :=
  (.ruleD "array.fill-null" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "val" (.varT "val" [])), (.expP "n" (.varT
   "n" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"),
   (.listE [(.caseE "REF.NULL_ADDR" (.tupE [])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.varE "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])),
   (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])),
   (.caseE "ARRAY.FILL" (.varE "x"))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_read/array.fill-oob`, rule 83 of the pinned stream. -/
def arrayFillOobRule : Rule :=
  (.ruleD "array.fill-oob" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" [])),
   (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "val" (.varT "val"
   [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.subE (.varE "val") (.varT
   "val" []) (.varT "instr" [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE
   "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.FILL" (.varE "x"))])])), (.listE [(.caseE
   "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT)
   (.projE (.uncaseE (.varE "i") "%") (0)) (.varE "n")) (.lenE (.dotE (.idxE (.callE
   "arrayinst" [(.expA (.varE "z"))]) (.varE "a")) "FIELDS"))))])

/-- `Step_read/array.fill-zero`, rule 84 of the pinned stream. -/
def arrayFillZeroRule : Rule :=
  (.ruleD "array.fill-zero" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" [])),
   (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "val" (.varT "val"
   [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.subE (.varE "val") (.varT
   "val" []) (.varT "instr" [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE
   "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.FILL" (.varE "x"))])])), (.listE [])])
   [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0))))])

/-- `Step_read/array.fill-succ`, rule 85 of the pinned stream. -/
def arrayFillSuccRule : Rule :=
  (.ruleD "array.fill-succ" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr" [])),
   (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "val" (.varT "val"
   [])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" []))] "%~>%" (.tupE [(.caseE
   "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.subE (.varE "val") (.varT
   "val" []) (.varT "instr" [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE
   "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.FILL" (.varE "x"))])])), (.listE [(.caseE
   "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i")])), (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])), (.caseE "ARRAY.SET"
   (.varE "x")), (.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE [(.caseE
   "I32" (.tupE [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE
   (.varE "i") "%") (0)) (.numE (.natN 1)))]))])), (.subE (.varE "val") (.varT "val" [])
   (.varT "instr" [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE
   (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE "ARRAY.FILL" (.varE "x"))])])
   [.elsePr])

/-- `Step_read/array.copy-null1`, rule 86 of the pinned stream. -/
def arrayCopyNull1Rule : Rule :=
  (.ruleD "array.copy-null1" [(.expP "z" (.varT "state" [])), (.expP "i_1" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "ref" (.varT "ref" [])), (.expP "i_2"
   (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP
   "x_1" (.varT "idx" [])), (.expP "x_2" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%"
   (.tupE [(.varE "z"), (.listE [(.caseE "REF.NULL_ADDR" (.tupE [])), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i_1")])), (.subE (.varE "ref") (.varT "ref" [])
   (.varT "instr" [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_2")])),
   (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])),
   (.caseE "ARRAY.COPY" (.tupE [(.varE "x_1"), (.varE "x_2")]))])])), (.listE [(.caseE
   "TRAP" (.tupE []))])]) [])

/-- `Step_read/array.copy-null2`, rule 87 of the pinned stream. -/
def arrayCopyNull2Rule : Rule :=
  (.ruleD "array.copy-null2" [(.expP "z" (.varT "state" [])), (.expP "ref" (.varT "ref"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "i_2"
   (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP
   "x_1" (.varT "idx" [])), (.expP "x_2" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%"
   (.tupE [(.varE "z"), (.listE [(.subE (.varE "ref") (.varT "ref" []) (.varT "instr" [])),
   (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_1")])), (.caseE
   "REF.NULL_ADDR" (.tupE [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i_2")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE
   "n")]))])), (.caseE "ARRAY.COPY" (.tupE [(.varE "x_1"), (.varE "x_2")]))])])), (.listE
   [(.caseE "TRAP" (.tupE []))])]) [])

/-- `Step_read/array.copy-oob1`, rule 88 of the pinned stream. -/
def arrayCopyOob1Rule : Rule :=
  (.ruleD "array.copy-oob1" [(.expP "z" (.varT "state" [])), (.expP "a_1" (.varT "addr"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "a_2"
   (.varT "addr" [])), (.expP "i_2" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x_1" (.varT "idx" [])), (.expP "x_2" (.varT "idx"
   []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR"
   (.varE "a_1")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_1")])),
   (.caseE "REF.ARRAY_ADDR" (.varE "a_2")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.COPY" (.tupE [(.varE "x_1"), (.varE
   "x_2")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT
   .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") (0)) (.varE "n"))
   (.lenE (.dotE (.idxE (.callE "arrayinst" [(.expA (.varE "z"))]) (.varE "a_1"))
   "FIELDS"))))])

/-- `Step_read/array.copy-oob2`, rule 89 of the pinned stream. -/
def arrayCopyOob2Rule : Rule :=
  (.ruleD "array.copy-oob2" [(.expP "z" (.varT "state" [])), (.expP "a_1" (.varT "addr"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "a_2"
   (.varT "addr" [])), (.expP "i_2" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x_1" (.varT "idx" [])), (.expP "x_2" (.varT "idx"
   []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR"
   (.varE "a_1")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_1")])),
   (.caseE "REF.ARRAY_ADDR" (.varE "a_2")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.COPY" (.tupE [(.varE "x_1"), (.varE
   "x_2")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT
   .natT) (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") (0)) (.varE "n"))
   (.lenE (.dotE (.idxE (.callE "arrayinst" [(.expA (.varE "z"))]) (.varE "a_2"))
   "FIELDS"))))])

/-- `Step_read/array.copy-zero`, rule 90 of the pinned stream. -/
def arrayCopyZeroRule : Rule :=
  (.ruleD "array.copy-zero" [(.expP "z" (.varT "state" [])), (.expP "a_1" (.varT "addr"
   [])), (.expP "i_1" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "a_2"
   (.varT "addr" [])), (.expP "i_2" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])),
   (.expP "n" (.varT "n" [])), (.expP "x_1" (.varT "idx" [])), (.expP "x_2" (.varT "idx"
   []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR"
   (.varE "a_1")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_1")])),
   (.caseE "REF.ARRAY_ADDR" (.varE "a_2")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "i_2")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.COPY" (.tupE [(.varE "x_1"), (.varE
   "x_2")]))])])), (.listE [])]) [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE
   (.natN 0))))])

/-- `Step_read/array.copy-le`, rule 91 of the pinned stream. -/
def arrayCopyLeRule : Rule :=
  (.ruleD "array.copy-le" [(.expP "z" (.varT "state" [])), (.expP "a_1" (.varT "addr" [])),
   (.expP "i_1" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "a_2" (.varT
   "addr" [])), (.expP "i_2" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n"
   (.varT "n" [])), (.expP "x_1" (.varT "idx" [])), (.expP "x_2" (.varT "idx" [])), (.expP
   "sx?" (.iterT (.varT "sx" []) .opt)), (.expP "mut?" (.iterT (.varT "mut" []) .opt)),
   (.expP "zt_2" (.varT "storagetype" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a_1")), (.caseE "CONST" (.tupE [(.caseE
   "I32" (.tupE [])), (.varE "i_1")])), (.caseE "REF.ARRAY_ADDR" (.varE "a_2")), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_2")])), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.COPY"
   (.tupE [(.varE "x_1"), (.varE "x_2")]))])])), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE
   "a_1")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_1")])), (.caseE
   "REF.ARRAY_ADDR" (.varE "a_2")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])),
   (.varE "i_2")])), (.caseE "ARRAY.GET" (.tupE [(.iterE (.varE "sx") (.mk .opt [(.mk "sx"
   (.varE "sx?"))])), (.varE "x_2")])), (.caseE "ARRAY.SET" (.varE "x_1")), (.caseE
   "REF.ARRAY_ADDR" (.varE "a_1")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])),
   (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") (0))
   (.numE (.natN 1)))]))])), (.caseE "REF.ARRAY_ADDR" (.varE "a_2")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE
   (.uncaseE (.varE "i_2") "%") (0)) (.numE (.natN 1)))]))])), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE
   (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)]))])),
   (.caseE "ARRAY.COPY" (.tupE [(.varE "x_1"), (.varE "x_2")]))])]) [.elsePr, (.rulePr
   "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")), (.expA (.varE "x_2"))]),
   (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE (.varE "mut") (.mk .opt [(.mk "mut" (.varE
   "mut?"))])), (.varE "zt_2")])))])), (.ifPr (.binE .andOp .boolT (.cmpE .leOp (.numT
   .natT) (.projE (.uncaseE (.varE "i_1") "%") (0)) (.projE (.uncaseE (.varE "i_2") "%")
   (0))) (.cmpE .eqOp .boolT (.iterE (.varE "sx") (.mk .opt [(.mk "sx" (.varE "sx?"))]))
   (.callE "sx" [(.expA (.varE "zt_2"))]))))])

/-- `Step_read/array.copy-gt`, rule 92 of the pinned stream. -/
def arrayCopyGtRule : Rule :=
  (.ruleD "array.copy-gt" [(.expP "z" (.varT "state" [])), (.expP "a_1" (.varT "addr" [])),
   (.expP "i_1" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "a_2" (.varT
   "addr" [])), (.expP "i_2" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n"
   (.varT "n" [])), (.expP "x_1" (.varT "idx" [])), (.expP "x_2" (.varT "idx" [])), (.expP
   "sx?" (.iterT (.varT "sx" []) .opt)), (.expP "mut?" (.iterT (.varT "mut" []) .opt)),
   (.expP "zt_2" (.varT "storagetype" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE
   "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a_1")), (.caseE "CONST" (.tupE [(.caseE
   "I32" (.tupE [])), (.varE "i_1")])), (.caseE "REF.ARRAY_ADDR" (.varE "a_2")), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_2")])), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.COPY"
   (.tupE [(.varE "x_1"), (.varE "x_2")]))])])), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE
   "a_1")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.cvtE
   (.binE .subOp (.numT .intT) (.cvtE (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE
   "i_1") "%") (0)) (.varE "n")) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT
   .natT)]))])), (.caseE "REF.ARRAY_ADDR" (.varE "a_2")), (.caseE "CONST" (.tupE [(.caseE
   "I32" (.tupE [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp (.numT .intT) (.cvtE (.binE
   .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") (0)) (.varE "n")) .natT .intT)
   (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)]))])), (.caseE "ARRAY.GET" (.tupE
   [(.iterE (.varE "sx") (.mk .opt [(.mk "sx" (.varE "sx?"))])), (.varE "x_2")])), (.caseE
   "ARRAY.SET" (.varE "x_1")), (.caseE "REF.ARRAY_ADDR" (.varE "a_1")), (.caseE "CONST"
   (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_1")])), (.caseE "REF.ARRAY_ADDR" (.varE
   "a_2")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i_2")])), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.cvtE (.binE .subOp
   (.numT .intT) (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
   .intT .natT)]))])), (.caseE "ARRAY.COPY" (.tupE [(.varE "x_1"), (.varE "x_2")]))])])
   [.elsePr, (.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE "z")), (.expA
   (.varE "x_2"))]), (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE (.varE "mut") (.mk .opt
   [(.mk "mut" (.varE "mut?"))])), (.varE "zt_2")])))])), (.ifPr (.cmpE .eqOp .boolT (.iterE
   (.varE "sx") (.mk .opt [(.mk "sx" (.varE "sx?"))])) (.callE "sx" [(.expA (.varE
   "zt_2"))])))])

/-- `Step_read/array.init_elem-null`, rule 93 of the pinned stream. -/
def arrayInitElemNullRule : Rule :=
  (.ruleD "array.init_elem-null" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT "num_" [(.expA (.caseE "I32"
   (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "y"
   (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "REF.NULL_ADDR" (.tupE [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE
   "ARRAY.INIT_ELEM" (.tupE [(.varE "x"), (.varE "y")]))])])), (.listE [(.caseE "TRAP"
   (.tupE []))])]) [])

/-- `Step_read/array.init_elem-oob1`, rule 94 of the pinned stream. -/
def arrayInitElemOob1Rule : Rule :=
  (.ruleD "array.init_elem-oob1" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT
   "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x"
   (.varT "idx" [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.INIT_ELEM" (.tupE [(.varE "x"), (.varE
   "y")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT)
   (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.varE "n")) (.lenE
   (.dotE (.idxE (.callE "arrayinst" [(.expA (.varE "z"))]) (.varE "a")) "FIELDS"))))])

/-- `Step_read/array.init_elem-oob2`, rule 95 of the pinned stream. -/
def arrayInitElemOob2Rule : Rule :=
  (.ruleD "array.init_elem-oob2" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT
   "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x"
   (.varT "idx" [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.INIT_ELEM" (.tupE [(.varE "x"), (.varE
   "y")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT)
   (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "j") "%") (0)) (.varE "n")) (.lenE
   (.dotE (.callE "elem" [(.expA (.varE "z")), (.expA (.varE "y"))]) "REFS"))))])

/-- `Step_read/array.init_elem-zero`, rule 96 of the pinned stream. -/
def arrayInitElemZeroRule : Rule :=
  (.ruleD "array.init_elem-zero" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT
   "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x"
   (.varT "idx" [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.INIT_ELEM" (.tupE [(.varE "x"), (.varE
   "y")]))])])), (.listE [])]) [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE
   (.natN 0))))])

/-- `Step_read/array.init_elem-succ`, rule 97 of the pinned stream. -/
def arrayInitElemSuccRule : Rule :=
  (.ruleD "array.init_elem-succ" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT
   "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x"
   (.varT "idx" [])), (.expP "y" (.varT "idx" [])), (.expP "ref" (.varT "ref" []))] "%~>%"
   (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE
   "a")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST"
   (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32"
   (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE "ARRAY.INIT_ELEM" (.tupE
   [(.varE "x"), (.varE "y")]))])])), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")),
   (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "i")])), (.subE (.varE "ref")
   (.varT "ref" []) (.varT "instr" [])), (.caseE "ARRAY.SET" (.varE "x")), (.caseE
   "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE
   "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.numE
   (.natN 1)))]))])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE
   [(.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "j") "%") (0)) (.numE (.natN
   1)))]))])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.cvtE
   (.binE .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1))
   .natT .intT)) .intT .natT)]))])), (.caseE "ARRAY.INIT_ELEM" (.tupE [(.varE "x"), (.varE
   "y")]))])]) [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "ref") (.idxE (.dotE (.callE
   "elem" [(.expA (.varE "z")), (.expA (.varE "y"))]) "REFS") (.projE (.uncaseE (.varE "j")
   "%") (0)))))])

/-- `Step_read/array.init_data-null`, rule 98 of the pinned stream. -/
def arrayInitDataNullRule : Rule :=
  (.ruleD "array.init_data-null" [(.expP "z" (.varT "state" [])), (.expP "i" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT "num_" [(.expA (.caseE "I32"
   (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x" (.varT "idx" [])), (.expP "y"
   (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "REF.NULL_ADDR" (.tupE [])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE
   "ARRAY.INIT_DATA" (.tupE [(.varE "x"), (.varE "y")]))])])), (.listE [(.caseE "TRAP"
   (.tupE []))])]) [])

/-- `Step_read/array.init_data-oob1`, rule 99 of the pinned stream. -/
def arrayInitDataOob1Rule : Rule :=
  (.ruleD "array.init_data-oob1" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT
   "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x"
   (.varT "idx" [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.INIT_DATA" (.tupE [(.varE "x"), (.varE
   "y")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .gtOp (.numT .natT)
   (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") (0)) (.varE "n")) (.lenE
   (.dotE (.idxE (.callE "arrayinst" [(.expA (.varE "z"))]) (.varE "a")) "FIELDS"))))])

/-- `Step_read/array.init_data-oob2`, rule 100 of the pinned stream. -/
def arrayInitDataOob2Rule : Rule :=
  (.ruleD "array.init_data-oob2" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT
   "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x"
   (.varT "idx" [])), (.expP "y" (.varT "idx" [])), (.expP "mut?" (.iterT (.varT "mut" [])
   .opt)), (.expP "zt" (.varT "storagetype" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.INIT_DATA" (.tupE [(.varE "x"), (.varE
   "y")]))])])), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.rulePr "Expand" [] "%~~%" (.tupE
   [(.callE "type" [(.expA (.varE "z")), (.expA (.varE "x"))]), (.caseE "ARRAY" (.caseE "%%"
   (.tupE [(.iterE (.varE "mut") (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE
   "zt")])))])), (.ifPr (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) (.projE
   (.uncaseE (.varE "j") "%") (0)) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.binE .mulOp
   (.numT .natT) (.varE "n") (.callE "zsize" [(.expA (.varE "zt"))])) .natT .ratT) (.cvtE
   (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) (.lenE (.dotE (.callE "data" [(.expA (.varE
   "z")), (.expA (.varE "y"))]) "BYTES"))))])

/-- `Step_read/array.init_data-zero`, rule 101 of the pinned stream. -/
def arrayInitDataZeroRule : Rule :=
  (.ruleD "array.init_data-zero" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT
   "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x"
   (.varT "idx" [])), (.expP "y" (.varT "idx" []))] "%~>%" (.tupE [(.caseE "%;%" (.tupE
   [(.varE "z"), (.listE [(.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE
   [])), (.varE "j")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%"
   (.tupE [(.varE "n")]))])), (.caseE "ARRAY.INIT_DATA" (.tupE [(.varE "x"), (.varE
   "y")]))])])), (.listE [])]) [.elsePr, (.ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE
   (.natN 0))))])

/-- `Step_read/array.init_data-num`, rule 102 of the pinned stream. -/
def arrayInitDataNumRule : Rule :=
  (.ruleD "array.init_data-num" [(.expP "z" (.varT "state" [])), (.expP "a" (.varT "addr"
   [])), (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "j" (.varT
   "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "n" (.varT "n" [])), (.expP "x"
   (.varT "idx" [])), (.expP "y" (.varT "idx" [])), (.expP "zt" (.varT "storagetype" [])),
   (.expP "c" (.varT "lit_" [(.expA (.varE "zt"))])), (.expP "mut?" (.iterT (.varT "mut" [])
   .opt))] "%~>%" (.tupE [(.caseE "%;%" (.tupE [(.varE "z"), (.listE [(.caseE
   "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i")])), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "j")])), (.caseE
   "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.varE "n")]))])), (.caseE
   "ARRAY.INIT_DATA" (.tupE [(.varE "x"), (.varE "y")]))])])), (.listE [(.caseE
   "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE
   "i")])), (.callE "const" [(.expA (.callE "cunpack" [(.expA (.varE "zt"))])), (.expA
   (.callE "cunpacknum_" [(.expA (.varE "zt")), (.expA (.varE "c"))]))]), (.caseE
   "ARRAY.SET" (.varE "x")), (.caseE "REF.ARRAY_ADDR" (.varE "a")), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE
   (.uncaseE (.varE "i") "%") (0)) (.numE (.natN 1)))]))])), (.caseE "CONST" (.tupE [(.caseE
   "I32" (.tupE [])), (.caseE "%" (.tupE [(.binE .addOp (.numT .natT) (.projE (.uncaseE
   (.varE "j") "%") (0)) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [(.expA
   (.varE "zt"))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))]))])),
   (.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.caseE "%" (.tupE [(.cvtE (.binE
   .subOp (.numT .intT) (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT
   .intT)) .intT .natT)]))])), (.caseE "ARRAY.INIT_DATA" (.tupE [(.varE "x"), (.varE
   "y")]))])]) [.elsePr, (.rulePr "Expand" [] "%~~%" (.tupE [(.callE "type" [(.expA (.varE
   "z")), (.expA (.varE "x"))]), (.caseE "ARRAY" (.caseE "%%" (.tupE [(.iterE (.varE "mut")
   (.mk .opt [(.mk "mut" (.varE "mut?"))])), (.varE "zt")])))])), (.ifPr (.cmpE .eqOp .boolT
   (.callE "zbytes_" [(.expA (.varE "zt")), (.expA (.varE "c"))]) (.sliceE (.dotE (.callE
   "data" [(.expA (.varE "z")), (.expA (.varE "y"))]) "BYTES") (.projE (.uncaseE (.varE "j")
   "%") (0)) (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [(.expA (.varE
   "zt"))]) .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))))])

/-- The pinned wasm-3.0 specification has all 103 at those indices. -/
structure HasReadRules (env : Env) : Prop where
  /-- `Step_read/block`, rule 0. -/
  block : HasRuleAt env "Step_read" "%~>%" 0 blockRule
  /-- `Step_read/loop`, rule 1. -/
  loop : HasRuleAt env "Step_read" "%~>%" 1 loopRule
  /-- `Step_read/br_on_cast-succeed`, rule 2. -/
  brOnCastSucceed : HasRuleAt env "Step_read" "%~>%" 2 brOnCastSucceedRule
  /-- `Step_read/br_on_cast-fail`, rule 3. -/
  brOnCastFail : HasRuleAt env "Step_read" "%~>%" 3 brOnCastFailRule
  /-- `Step_read/br_on_cast_fail-succeed`, rule 4. -/
  brOnCastFailSucceed : HasRuleAt env "Step_read" "%~>%" 4 brOnCastFailSucceedRule
  /-- `Step_read/br_on_cast_fail-fail`, rule 5. -/
  brOnCastFailFail : HasRuleAt env "Step_read" "%~>%" 5 brOnCastFailFailRule
  /-- `Step_read/call`, rule 6. -/
  call : HasRuleAt env "Step_read" "%~>%" 6 callRule
  /-- `Step_read/return_call`, rule 7. -/
  returnCall : HasRuleAt env "Step_read" "%~>%" 7 returnCallRule
  /-- `Step_read/return_call_ref-label`, rule 8. -/
  returnCallRefLabel : HasRuleAt env "Step_read" "%~>%" 8 returnCallRefLabelRule
  /-- `Step_read/return_call_ref-handler`, rule 9. -/
  returnCallRefHandler : HasRuleAt env "Step_read" "%~>%" 9 returnCallRefHandlerRule
  /-- `Step_read/return_call_ref-frame-null`, rule 10. -/
  returnCallRefFrameNull : HasRuleAt env "Step_read" "%~>%" 10 returnCallRefFrameNullRule
  /-- `Step_read/return_call_ref-frame-addr`, rule 11. -/
  returnCallRefFrameAddr : HasRuleAt env "Step_read" "%~>%" 11 returnCallRefFrameAddrRule
  /-- `Step_read/throw_ref-null`, rule 12. -/
  throwRefNull : HasRuleAt env "Step_read" "%~>%" 12 throwRefNullRule
  /-- `Step_read/throw_ref-instrs`, rule 13. -/
  throwRefInstrs : HasRuleAt env "Step_read" "%~>%" 13 throwRefInstrsRule
  /-- `Step_read/throw_ref-label`, rule 14. -/
  throwRefLabel : HasRuleAt env "Step_read" "%~>%" 14 throwRefLabelRule
  /-- `Step_read/throw_ref-frame`, rule 15. -/
  throwRefFrame : HasRuleAt env "Step_read" "%~>%" 15 throwRefFrameRule
  /-- `Step_read/throw_ref-handler-empty`, rule 16. -/
  throwRefHandlerEmpty : HasRuleAt env "Step_read" "%~>%" 16 throwRefHandlerEmptyRule
  /-- `Step_read/throw_ref-handler-catch`, rule 17. -/
  throwRefHandlerCatch : HasRuleAt env "Step_read" "%~>%" 17 throwRefHandlerCatchRule
  /-- `Step_read/throw_ref-handler-catch_ref`, rule 18. -/
  throwRefHandlerCatchRef : HasRuleAt env "Step_read" "%~>%" 18 throwRefHandlerCatchRefRule
  /-- `Step_read/throw_ref-handler-catch_all`, rule 19. -/
  throwRefHandlerCatchAll : HasRuleAt env "Step_read" "%~>%" 19 throwRefHandlerCatchAllRule
  /-- `Step_read/throw_ref-handler-catch_all_ref`, rule 20. -/
  throwRefHandlerCatchAllRef : HasRuleAt env "Step_read" "%~>%" 20 throwRefHandlerCatchAllRefRule
  /-- `Step_read/throw_ref-handler-next`, rule 21. -/
  throwRefHandlerNext : HasRuleAt env "Step_read" "%~>%" 21 throwRefHandlerNextRule
  /-- `Step_read/try_table`, rule 22. -/
  tryTable : HasRuleAt env "Step_read" "%~>%" 22 tryTableRule
  /-- `Step_read/local.get`, rule 23. -/
  localGet : HasRuleAt env "Step_read" "%~>%" 23 localGetRule
  /-- `Step_read/global.get`, rule 24. -/
  globalGet : HasRuleAt env "Step_read" "%~>%" 24 globalGetRule
  /-- `Step_read/table.get-oob`, rule 25. -/
  tableGetOob : HasRuleAt env "Step_read" "%~>%" 25 tableGetOobRule
  /-- `Step_read/table.get-val`, rule 26. -/
  tableGetVal : HasRuleAt env "Step_read" "%~>%" 26 tableGetValRule
  /-- `Step_read/table.size`, rule 27. -/
  tableSize : HasRuleAt env "Step_read" "%~>%" 27 tableSizeRule
  /-- `Step_read/table.fill-oob`, rule 28. -/
  tableFillOob : HasRuleAt env "Step_read" "%~>%" 28 tableFillOobRule
  /-- `Step_read/table.fill-zero`, rule 29. -/
  tableFillZero : HasRuleAt env "Step_read" "%~>%" 29 tableFillZeroRule
  /-- `Step_read/table.fill-succ`, rule 30. -/
  tableFillSucc : HasRuleAt env "Step_read" "%~>%" 30 tableFillSuccRule
  /-- `Step_read/table.copy-oob`, rule 31. -/
  tableCopyOob : HasRuleAt env "Step_read" "%~>%" 31 tableCopyOobRule
  /-- `Step_read/table.copy-zero`, rule 32. -/
  tableCopyZero : HasRuleAt env "Step_read" "%~>%" 32 tableCopyZeroRule
  /-- `Step_read/table.copy-le`, rule 33. -/
  tableCopyLe : HasRuleAt env "Step_read" "%~>%" 33 tableCopyLeRule
  /-- `Step_read/table.copy-gt`, rule 34. -/
  tableCopyGt : HasRuleAt env "Step_read" "%~>%" 34 tableCopyGtRule
  /-- `Step_read/table.init-oob`, rule 35. -/
  tableInitOob : HasRuleAt env "Step_read" "%~>%" 35 tableInitOobRule
  /-- `Step_read/table.init-zero`, rule 36. -/
  tableInitZero : HasRuleAt env "Step_read" "%~>%" 36 tableInitZeroRule
  /-- `Step_read/table.init-succ`, rule 37. -/
  tableInitSucc : HasRuleAt env "Step_read" "%~>%" 37 tableInitSuccRule
  /-- `Step_read/load-num-oob`, rule 38. -/
  loadNumOob : HasRuleAt env "Step_read" "%~>%" 38 loadNumOobRule
  /-- `Step_read/load-num-val`, rule 39. -/
  loadNumVal : HasRuleAt env "Step_read" "%~>%" 39 loadNumValRule
  /-- `Step_read/load-pack-oob`, rule 40. -/
  loadPackOob : HasRuleAt env "Step_read" "%~>%" 40 loadPackOobRule
  /-- `Step_read/load-pack-val`, rule 41. -/
  loadPackVal : HasRuleAt env "Step_read" "%~>%" 41 loadPackValRule
  /-- `Step_read/vload-num-oob`, rule 42. -/
  vloadNumOob : HasRuleAt env "Step_read" "%~>%" 42 vloadNumOobRule
  /-- `Step_read/vload-num-val`, rule 43. -/
  vloadNumVal : HasRuleAt env "Step_read" "%~>%" 43 vloadNumValRule
  /-- `Step_read/vload-pack-oob`, rule 44. -/
  vloadPackOob : HasRuleAt env "Step_read" "%~>%" 44 vloadPackOobRule
  /-- `Step_read/vload-pack-val`, rule 45. -/
  vloadPackVal : HasRuleAt env "Step_read" "%~>%" 45 vloadPackValRule
  /-- `Step_read/vload-splat-oob`, rule 46. -/
  vloadSplatOob : HasRuleAt env "Step_read" "%~>%" 46 vloadSplatOobRule
  /-- `Step_read/vload-splat-val`, rule 47. -/
  vloadSplatVal : HasRuleAt env "Step_read" "%~>%" 47 vloadSplatValRule
  /-- `Step_read/vload-zero-oob`, rule 48. -/
  vloadZeroOob : HasRuleAt env "Step_read" "%~>%" 48 vloadZeroOobRule
  /-- `Step_read/vload-zero-val`, rule 49. -/
  vloadZeroVal : HasRuleAt env "Step_read" "%~>%" 49 vloadZeroValRule
  /-- `Step_read/vload_lane-oob`, rule 50. -/
  vloadLaneOob : HasRuleAt env "Step_read" "%~>%" 50 vloadLaneOobRule
  /-- `Step_read/vload_lane-val`, rule 51. -/
  vloadLaneVal : HasRuleAt env "Step_read" "%~>%" 51 vloadLaneValRule
  /-- `Step_read/memory.size`, rule 52. -/
  memorySize : HasRuleAt env "Step_read" "%~>%" 52 memorySizeRule
  /-- `Step_read/memory.fill-oob`, rule 53. -/
  memoryFillOob : HasRuleAt env "Step_read" "%~>%" 53 memoryFillOobRule
  /-- `Step_read/memory.fill-zero`, rule 54. -/
  memoryFillZero : HasRuleAt env "Step_read" "%~>%" 54 memoryFillZeroRule
  /-- `Step_read/memory.fill-succ`, rule 55. -/
  memoryFillSucc : HasRuleAt env "Step_read" "%~>%" 55 memoryFillSuccRule
  /-- `Step_read/memory.copy-oob`, rule 56. -/
  memoryCopyOob : HasRuleAt env "Step_read" "%~>%" 56 memoryCopyOobRule
  /-- `Step_read/memory.copy-zero`, rule 57. -/
  memoryCopyZero : HasRuleAt env "Step_read" "%~>%" 57 memoryCopyZeroRule
  /-- `Step_read/memory.copy-le`, rule 58. -/
  memoryCopyLe : HasRuleAt env "Step_read" "%~>%" 58 memoryCopyLeRule
  /-- `Step_read/memory.copy-gt`, rule 59. -/
  memoryCopyGt : HasRuleAt env "Step_read" "%~>%" 59 memoryCopyGtRule
  /-- `Step_read/memory.init-oob`, rule 60. -/
  memoryInitOob : HasRuleAt env "Step_read" "%~>%" 60 memoryInitOobRule
  /-- `Step_read/memory.init-zero`, rule 61. -/
  memoryInitZero : HasRuleAt env "Step_read" "%~>%" 61 memoryInitZeroRule
  /-- `Step_read/memory.init-succ`, rule 62. -/
  memoryInitSucc : HasRuleAt env "Step_read" "%~>%" 62 memoryInitSuccRule
  /-- `Step_read/ref.null`, rule 63. -/
  refNull : HasRuleAt env "Step_read" "%~>%" 63 refNullRule
  /-- `Step_read/ref.func`, rule 64. -/
  refFunc : HasRuleAt env "Step_read" "%~>%" 64 refFuncRule
  /-- `Step_read/ref.test-true`, rule 65. -/
  refTestTrue : HasRuleAt env "Step_read" "%~>%" 65 refTestTrueRule
  /-- `Step_read/ref.test-false`, rule 66. -/
  refTestFalse : HasRuleAt env "Step_read" "%~>%" 66 refTestFalseRule
  /-- `Step_read/ref.cast-succeed`, rule 67. -/
  refCastSucceed : HasRuleAt env "Step_read" "%~>%" 67 refCastSucceedRule
  /-- `Step_read/ref.cast-fail`, rule 68. -/
  refCastFail : HasRuleAt env "Step_read" "%~>%" 68 refCastFailRule
  /-- `Step_read/struct.new_default`, rule 69. -/
  structNewDefault : HasRuleAt env "Step_read" "%~>%" 69 structNewDefaultRule
  /-- `Step_read/struct.get-null`, rule 70. -/
  structGetNull : HasRuleAt env "Step_read" "%~>%" 70 structGetNullRule
  /-- `Step_read/struct.get-struct`, rule 71. -/
  structGetStruct : HasRuleAt env "Step_read" "%~>%" 71 structGetStructRule
  /-- `Step_read/array.new_default`, rule 72. -/
  arrayNewDefault : HasRuleAt env "Step_read" "%~>%" 72 arrayNewDefaultRule
  /-- `Step_read/array.new_elem-oob`, rule 73. -/
  arrayNewElemOob : HasRuleAt env "Step_read" "%~>%" 73 arrayNewElemOobRule
  /-- `Step_read/array.new_elem-alloc`, rule 74. -/
  arrayNewElemAlloc : HasRuleAt env "Step_read" "%~>%" 74 arrayNewElemAllocRule
  /-- `Step_read/array.new_data-oob`, rule 75. -/
  arrayNewDataOob : HasRuleAt env "Step_read" "%~>%" 75 arrayNewDataOobRule
  /-- `Step_read/array.new_data-num`, rule 76. -/
  arrayNewDataNum : HasRuleAt env "Step_read" "%~>%" 76 arrayNewDataNumRule
  /-- `Step_read/array.get-null`, rule 77. -/
  arrayGetNull : HasRuleAt env "Step_read" "%~>%" 77 arrayGetNullRule
  /-- `Step_read/array.get-oob`, rule 78. -/
  arrayGetOob : HasRuleAt env "Step_read" "%~>%" 78 arrayGetOobRule
  /-- `Step_read/array.get-array`, rule 79. -/
  arrayGetArray : HasRuleAt env "Step_read" "%~>%" 79 arrayGetArrayRule
  /-- `Step_read/array.len-null`, rule 80. -/
  arrayLenNull : HasRuleAt env "Step_read" "%~>%" 80 arrayLenNullRule
  /-- `Step_read/array.len-array`, rule 81. -/
  arrayLenArray : HasRuleAt env "Step_read" "%~>%" 81 arrayLenArrayRule
  /-- `Step_read/array.fill-null`, rule 82. -/
  arrayFillNull : HasRuleAt env "Step_read" "%~>%" 82 arrayFillNullRule
  /-- `Step_read/array.fill-oob`, rule 83. -/
  arrayFillOob : HasRuleAt env "Step_read" "%~>%" 83 arrayFillOobRule
  /-- `Step_read/array.fill-zero`, rule 84. -/
  arrayFillZero : HasRuleAt env "Step_read" "%~>%" 84 arrayFillZeroRule
  /-- `Step_read/array.fill-succ`, rule 85. -/
  arrayFillSucc : HasRuleAt env "Step_read" "%~>%" 85 arrayFillSuccRule
  /-- `Step_read/array.copy-null1`, rule 86. -/
  arrayCopyNull1 : HasRuleAt env "Step_read" "%~>%" 86 arrayCopyNull1Rule
  /-- `Step_read/array.copy-null2`, rule 87. -/
  arrayCopyNull2 : HasRuleAt env "Step_read" "%~>%" 87 arrayCopyNull2Rule
  /-- `Step_read/array.copy-oob1`, rule 88. -/
  arrayCopyOob1 : HasRuleAt env "Step_read" "%~>%" 88 arrayCopyOob1Rule
  /-- `Step_read/array.copy-oob2`, rule 89. -/
  arrayCopyOob2 : HasRuleAt env "Step_read" "%~>%" 89 arrayCopyOob2Rule
  /-- `Step_read/array.copy-zero`, rule 90. -/
  arrayCopyZero : HasRuleAt env "Step_read" "%~>%" 90 arrayCopyZeroRule
  /-- `Step_read/array.copy-le`, rule 91. -/
  arrayCopyLe : HasRuleAt env "Step_read" "%~>%" 91 arrayCopyLeRule
  /-- `Step_read/array.copy-gt`, rule 92. -/
  arrayCopyGt : HasRuleAt env "Step_read" "%~>%" 92 arrayCopyGtRule
  /-- `Step_read/array.init_elem-null`, rule 93. -/
  arrayInitElemNull : HasRuleAt env "Step_read" "%~>%" 93 arrayInitElemNullRule
  /-- `Step_read/array.init_elem-oob1`, rule 94. -/
  arrayInitElemOob1 : HasRuleAt env "Step_read" "%~>%" 94 arrayInitElemOob1Rule
  /-- `Step_read/array.init_elem-oob2`, rule 95. -/
  arrayInitElemOob2 : HasRuleAt env "Step_read" "%~>%" 95 arrayInitElemOob2Rule
  /-- `Step_read/array.init_elem-zero`, rule 96. -/
  arrayInitElemZero : HasRuleAt env "Step_read" "%~>%" 96 arrayInitElemZeroRule
  /-- `Step_read/array.init_elem-succ`, rule 97. -/
  arrayInitElemSucc : HasRuleAt env "Step_read" "%~>%" 97 arrayInitElemSuccRule
  /-- `Step_read/array.init_data-null`, rule 98. -/
  arrayInitDataNull : HasRuleAt env "Step_read" "%~>%" 98 arrayInitDataNullRule
  /-- `Step_read/array.init_data-oob1`, rule 99. -/
  arrayInitDataOob1 : HasRuleAt env "Step_read" "%~>%" 99 arrayInitDataOob1Rule
  /-- `Step_read/array.init_data-oob2`, rule 100. -/
  arrayInitDataOob2 : HasRuleAt env "Step_read" "%~>%" 100 arrayInitDataOob2Rule
  /-- `Step_read/array.init_data-zero`, rule 101. -/
  arrayInitDataZero : HasRuleAt env "Step_read" "%~>%" 101 arrayInitDataZeroRule
  /-- `Step_read/array.init_data-num`, rule 102. -/
  arrayInitDataNum : HasRuleAt env "Step_read" "%~>%" 102 arrayInitDataNumRule

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- Discharged by `rfl` against the pinned stream. -/
theorem hasReadRules_wasm30 : HasReadRules (envOfScript Specs.wasm30) :=
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

/-! ## The first two characterisations

`local.get` and `global.get` are the two simplest rules of `Step_read`, and
they show the shape the rest of the relation has.  Both keep the state
**abstract**: the rule names `z` in its premise — `$local(z, x)`,
`$global(z, x)` — but never destructures it.  So each is characterised in
terms of `Applies`, saying exactly what the rule derives *without* saying what
the accessor computes, which is the same separation that let
`Equiv/ExecNumeric.lean`'s eight theorems survive the builtin parameterisation.

The runtime bridge is what connects the other end: `$local` at an encoded
state is `Frame.locals`, `$global` is `Store.globals`.  That is the next step,
and it is what the bridge was built for; the characterisations below do not
wait for it.

`Equiv/Execution.lean` named `local.get`/`local.set` as the priority-1 item it
could not reach, "because its value bridge is a bridge for `instr` alone".
This is the first half of that. -/

/-- `(z; [LOCAL.GET x])`, the one-instruction configuration both rules use. -/
def readConfigV (z : Value) (i : Value) : Value := .case "%;%" (.tuple [z, .list [i]])

/-- The conclusion shape `(z; [OP x]) ~> [val]`, matched once. -/
theorem matchExp_readOne_iff {env : Env} {ρ' : VarEnv} {v : Value} {op : MixopS} :
    MatchExp env VarEnv.empty
      (.tupE
        [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE op (.varE "x")]]),
         .listE [.subE (.varE "val") (.varT "val" []) (.varT "instr" [])]])
      v ρ' ↔
      ∃ z x val, v = .tuple [readConfigV z (.case op x), .list [val]] ∧
        ρ' = ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "val" val := by
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
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨val, rfl, hval⟩ := matchExps_one_iff.1 hbvs
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hval
    subst hval
    exact ⟨z, x, val, rfl, rfl⟩
  · rintro ⟨z, x, val, rfl, rfl⟩
    exact matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl)⟩⟩⟩

/-- **`Step_read/local.get`, characterised exactly.**  It derives
`(z; [LOCAL.GET x]) ~> [val]` exactly when `$local(z, x)` denotes `?(val)`. -/
theorem ruleFires_localGet_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v localGetRule ↔
      ∃ z x val, v = .tuple [readConfigV z (.case "LOCAL.GET" x), .list [val]] ∧
        ExecNumeric.Applies env "local" [.val z, .val x] (.opt (some val)) := by
  unfold localGetRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, x, val, rfl, rfl⟩ := matchExp_readOne_iff.1 hm
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨w, hw, rfl⟩ := evalExp_optE_some_iff.1 hv₂
    rw [evalExp_varE_iff] at hw
    simp at hw
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    refine ⟨z, x, val, rfl, ?_⟩
    rw [hw]
    refine (ExecNumeric.applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "z" z).bindVal
      "x" x).bindVal "val" val) rfl ?_).mpr (evalExp_callE_iff.1 hv₁)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)
  · rintro ⟨z, x, val, rfl, happ⟩
    refine ⟨((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "val" val,
      ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "val" val,
      matchExp_readOne_iff.2 ⟨z, x, val, rfl, rfl⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.opt (some val), .opt (some val), ?_,
      evalExp_optE_some_iff.2 ⟨val, evalExp_varE_iff.2 (by simp), rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
      (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "val" val) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)

/-- **`Step_read/global.get`, characterised exactly.**  The premise projects
the `VALUE` field of `$global(z, x)`, so the statement names the whole global
instance `g` and the fact that its `VALUE` field is `val` — which is what the
runtime bridge will discharge, since `globalInstToValue` puts `VALUE` there by
construction. -/
theorem ruleFires_globalGet_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v globalGetRule ↔
      ∃ z x val g, v = .tuple [readConfigV z (.case "GLOBAL.GET" x), .list [val]] ∧
        ExecNumeric.Applies env "global" [.val z, .val x] g ∧
        g.field? "VALUE" = some val := by
  unfold globalGetRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, x, val, rfl, rfl⟩ := matchExp_readOne_iff.1 hm
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain ⟨g, hg, hfield⟩ := evalExp_dotE_iff.1 hv₁
    rw [evalExp_varE_iff] at hv₂
    simp at hv₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hv₂
    refine ⟨z, x, val, g, rfl, ?_, hfield⟩
    refine (ExecNumeric.applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "z" z).bindVal
      "x" x).bindVal "val" val) rfl ?_).mpr (evalExp_callE_iff.1 hg)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)
  · rintro ⟨z, x, val, g, rfl, happ, hfield⟩
    refine ⟨((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "val" val,
      ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "val" val,
      matchExp_readOne_iff.2 ⟨z, x, val, rfl, rfl⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨val, val, ?_, evalExp_varE_iff.2 (by simp),
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_dotE_iff.2 ⟨g, ?_, hfield⟩
    refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
      (ρ := ((VarEnv.empty.bindVal "z" z).bindVal "x" x).bindVal "val" val) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)

/-- Both lift to the whole machine: `Equiv/ExecStep.lean`'s
`derives_step_of_stepRead` turns any `Step_read` derivation into a `Step` one
at the state it read. -/
theorem derives_step_localGet {env : Env} (hr : HasReadRules env)
    (hs : ExecStep.HasStepLiftRules env) {z x val : Value}
    (h : ExecNumeric.Applies env "local" [.val z, .val x] (.opt (some val))) :
    Derives env "Step" "%~>%" []
      (.tuple [ExecStep.configV z [.case "LOCAL.GET" x], ExecStep.configV z [val]]) :=
  ExecStep.derives_step_of_stepRead hs
    (derives_of_ruleAt hr.localGet (ruleFires_localGet_iff.2 ⟨z, x, val, rfl, h⟩))

/-- **`Step_read/ref.null`, characterised exactly.**  No premise, and the
heap type is carried but never inspected, so the rule derives
`(z; [REF.NULL ht]) ~> [REF.NULL_ADDR]` for every state `z` and every `ht`. -/
theorem ruleFires_refNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refNullRule ↔
      ∃ z ht, v = .tuple [readConfigV z (.case "REF.NULL" ht),
        .list [Execution.caseNilV "REF.NULL_ADDR"]] := by
  unfold refNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨z, iv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨ivs, rfl, hivs⟩ := Validation.matchExp_list_iff.1 hi
    obtain ⟨ie, rfl, hie⟩ := matchExps_one_iff.1 hivs
    obtain ⟨ht, rfl, hht⟩ := Validation.matchExp_case_iff.1 hie
    rw [matchExp_freshVar_iff (by simp)] at hht
    subst hht
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact ⟨z, ht, rfl⟩
  · rintro ⟨z, ht, rfl⟩
    exact ⟨(VarEnv.empty.bindVal "z" z).bindVal "ht" ht,
      (VarEnv.empty.bindVal "z" z).bindVal "ht" ht,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl,
              matchExps_one_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-! ## The `ref.test` / `ref.cast` family

Four rules, one shape.  They are the first `Step_read` rules that destructure
the state — `((s; f); …)` — but they still never *inspect* it: `s` goes to the
`Ref_ok` premise and `f` only through `f.MODULE`.  So the characterisations
quantify over arbitrary `s` and `f`, exactly as everything before them.

`ref.test-false` and `ref.cast-fail` have `else` as their only premise, and
`Sem/Eval.lean` sends `.elsePr` to `.ok ρ` unconditionally.  For a `RelD` that
is vacuous — `anyRule` imposes no order — so the same overlap
`Equiv/ExecRef.lean` found in `Step_pure` is here too: a reference that *does*
have the tested type still steps to `0`, and one that does *not* still casts
successfully.  `ruleFires_refTestFalse_onAnything` exhibits it. -/

/-- `((s; f); [ref, OP rt])`, the left-hand side the four share. -/
theorem matchExp_stateRefOp_iff {env : Env} {ρ' : VarEnv} {op : MixopS} {v : Value} :
    MatchExp env VarEnv.empty
      (.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE "s", .varE "f"]),
        .listE [.subE (.varE "ref") (.varT "ref" []) (.varT "instr" []),
                .caseE op (.varE "rt")]]))
      v ρ' ↔
      ∃ s f ref rt,
        v = .case "%;%" (.tuple [.case "%;%" (.tuple [s, f]), .list [ref, .case op rt]]) ∧
        ρ' = (((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" ref).bindVal
          "rt" rt := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨sf, body, τ, rfl, hsf, hbody⟩ := matchExps_two_iff.1 hws
    obtain ⟨sfv, rfl, hsfv⟩ := Validation.matchExp_case_iff.1 hsf
    obtain ⟨sfvs, rfl, hsfvs⟩ := Validation.matchExp_tup_iff.1 hsfv
    obtain ⟨s, f, υ, rfl, hs, hf⟩ := matchExps_two_iff.1 hsfvs
    rw [matchExp_freshVar_iff (by simp)] at hs
    subst hs
    rw [matchExp_freshVar_iff (by simp)] at hf
    subst hf
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hbody
    obtain ⟨ref, opv, κ, rfl, href, hop⟩ := matchExps_two_iff.1 hbvs
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at href
    subst href
    obtain ⟨rt, rfl, hrt⟩ := Validation.matchExp_case_iff.1 hop
    rw [matchExp_freshVar_iff (by simp)] at hrt
    subst hrt
    exact ⟨s, f, ref, rt, rfl, rfl⟩
  · rintro ⟨s, f, ref, rt, rfl, rfl⟩
    refine ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, (VarEnv.empty.bindVal "s" s).bindVal "f" f, rfl, ?_, ?_⟩⟩⟩
    · exact Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩

/-- `(CONST I32 %(k))` as a pattern — `Equiv/ExecRef.lean` has the same lemma;
it is repeated here because that file is about `Step_pure`. -/
theorem matchExp_constI32k_iff {env : Env} {ρ ρ' : VarEnv} {k : Nat} {v : Value} :
    MatchExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
        .caseE "%" (.tupE [.numE (.natN k)])])) v ρ' ↔
      v = Execution.constV Execution.i32V (Execution.pctV k) ∧ ρ' = ρ :=
  ExecRef.matchExp_constI32_iff

/-- **`Step_read/ref.test-false`, characterised exactly.**  Its only premise is
`else`, so it fires on *every* reference and reference type. -/
theorem ruleFires_refTestFalse_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refTestFalseRule ↔
      ∃ s f ref rt,
        v = .tuple
          [.case "%;%" (.tuple [.case "%;%" (.tuple [s, f]),
             .list [ref, .case "REF.TEST" rt]]),
           .list [Execution.constV Execution.i32V (Execution.pctV 0)]] := by
  unfold refTestFalseRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨s, f, ref, rt, rfl, rfl⟩ := matchExp_stateRefOp_iff.1 hl
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_constI32k_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact ⟨s, f, ref, rt, rfl⟩
  · rintro ⟨s, f, ref, rt, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_stateRefOp_iff.2 ⟨s, f, ref, rt, rfl, rfl⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_constI32k_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      ExecRef.premsHold_else_iff.2 rfl⟩

/-- **The overlap, at `Step_read`.**  `ref.test-false` fires whatever the
reference's type, so `(REF.NULL_ADDR) (REF.TEST rt)` steps to `0` even when
`ref.test-true` also fires. -/
theorem ruleFires_refTestFalse_onAnything {env : Env} (s f ref rt : Value) :
    RuleFires env "%~>%" [] []
      (.tuple
        [.case "%;%" (.tuple [.case "%;%" (.tuple [s, f]),
           .list [ref, .case "REF.TEST" rt]]),
         .list [Execution.constV Execution.i32V (Execution.pctV 0)]]) refTestFalseRule :=
  ruleFires_refTestFalse_iff.2 ⟨s, f, ref, rt, rfl⟩

/-- **`Step_read/ref.cast-fail`, characterised exactly.**  Same `else`, so the
cast traps on every reference — including one that `ref.cast-succeed` accepts. -/
theorem ruleFires_refCastFail_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refCastFailRule ↔
      ∃ s f ref rt,
        v = .tuple
          [.case "%;%" (.tuple [.case "%;%" (.tuple [s, f]),
             .list [ref, .case "REF.CAST" rt]]),
           .list [Execution.trapV]] := by
  unfold refCastFailRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨s, f, ref, rt, rfl, rfl⟩ := matchExp_stateRefOp_iff.1 hl
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_caseNil_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact ⟨s, f, ref, rt, rfl⟩
  · rintro ⟨s, f, ref, rt, rfl⟩
    exact ⟨_, _, matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_stateRefOp_iff.2 ⟨s, f, ref, rt, rfl, rfl⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
      ExecRef.premsHold_else_iff.2 rfl⟩

/-! ## Inverting an argument list

`Equiv/Numerics.lean` has `evalArgs_cons`, which *builds* an `EvalArgs`.  Every
rule whose premise is a call with a non-variable argument needs the other
direction, and it did not exist.  `ref.test-true`'s premise is the first:
`$inst_reftype(f.MODULE, rt)` has a `DotE` where the earlier rules had plain
variables.

Specialised to `ExpA`, which is the only argument former that occurs in a
reduction rule's premises.  Like `callDef_iff` and `matchDefault_iff` before
it, this belongs in `Sem/Eval.lean`. -/

/-- An expression-argument list is evaluated head-first. -/
theorem evalArgs_expA_cons_iff {env : Env} {ρ : VarEnv} {e : Exp} {rest : List Arg}
    {ws : List ArgV} :
    EvalArgs env ρ (.expA e :: rest) ws ↔
      ∃ v ws', ws = .val v :: ws' ∧ EvalExp env ρ e v ∧ EvalArgs env ρ rest ws' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [evalArgs] at hn
    | succ m =>
        simp only [evalArgs, List.mapM_cons, Res.bind_eq_ok] at hn
        obtain ⟨w, hw, ws', hws, heq⟩ := hn
        obtain rfl : ws = w :: ws' := (Validation.okInj heq).symm
        cases m with
        | zero => simp [evalArg] at hw
        | succ k =>
            simp only [evalArg, Res.map_eq_ok] at hw
            obtain ⟨v, hv, rfl⟩ := hw
            exact ⟨v, ws', rfl, ⟨k, hv⟩, ⟨k + 2, by simpa only [evalArgs] using hws⟩⟩
  · rintro ⟨v, ws', rfl, hv, hws⟩
    exact evalArgs_cons hv hws


/-- The `Ref_ok` premise the two positive `ref.test`/`ref.cast` rules share:
the reference has the *instantiated* type.  `$inst_reftype(f.MODULE, rt)` is a
call, so it is stated with `Applies` — what the rule derives, without saying
what instantiation computes. -/
def RefOkPrem (env : Env) (s f ref rt : Value) : Prop :=
  ∃ m rtv, f.field? "MODULE" = some m ∧
    ExecNumeric.Applies env "inst_reftype" [.val m, .val rt] rtv ∧
    Derives env "Ref_ok" "%|-%:%" [] (.tuple [s, ref, rtv])

/-- **`Step_read/ref.test-true`, characterised exactly.** -/
theorem ruleFires_refTestTrue_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refTestTrueRule ↔
      ∃ s f ref rt,
        v = .tuple
          [.case "%;%" (.tuple [.case "%;%" (.tuple [s, f]),
             .list [ref, .case "REF.TEST" rt]]),
           .list [Execution.constV Execution.i32V (Execution.pctV 1)]] ∧
        RefOkPrem env s f ref rt := by
  unfold refTestTrueRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨s, f, ref, rt, rfl, rfl⟩ := matchExp_stateRefOp_iff.1 hl
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r0, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_constI32k_iff] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    refine ⟨s, f, ref, rt, rfl, ?_⟩
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, ws, w, hws, hw, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    obtain ⟨wvs, hwvs, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain ⟨p, ps, hp0, hp1, hq1⟩ := Validation.evalExps_cons_iff.1 hwvs
    obtain ⟨q, qs, hq0, hq2, hq3⟩ := Validation.evalExps_cons_iff.1 hq1
    obtain ⟨rr, rs, hr0, hr2, hr3⟩ := Validation.evalExps_cons_iff.1 hq3
    obtain rfl := Validation.evalExps_nil_iff.1 hr3
    rw [evalExp_varE_iff] at hp1 hq2
    simp at hp1 hq2
    subst hp1; subst hq2; subst hr0; subst hq0; subst hp0
    obtain ⟨ws2, ps2, t2, cs2, hargs, hfind, hbody⟩ :=
      ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hr2)
    obtain ⟨mv, ws3, rfl, hmv, hrest4⟩ := evalArgs_expA_cons_iff.1 hargs
    obtain ⟨rtv', ws4, rfl, hrt, hnil⟩ := evalArgs_expA_cons_iff.1 hrest4
    obtain rfl := Validation.evalArgs_nil_iff.1 hnil
    obtain ⟨fv, hfv, hfield⟩ := evalExp_dotE_iff.1 hmv
    rw [evalExp_varE_iff] at hfv hrt
    simp at hfv hrt
    subst hfv; subst hrt
    have hnd : ((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" ref).bindVal
        "rt" rt).findDef? "inst_reftype" = none := rfl
    rw [hnd, Option.getD_none] at hfind
    exact ⟨mv, rr, hfield, ⟨ps2, t2, cs2, hfind, hbody⟩, hder⟩
  · rintro ⟨s, f, ref, rt, rfl, mv, rtv, hfield, happ, hder⟩
    refine ⟨((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" ref).bindVal "rt" rt), ((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" ref).bindVal "rt" rt), matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_stateRefOp_iff.2 ⟨s, f, ref, rt, rfl, rfl⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_constI32k_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_rule_iff.2
      ⟨rfl, [], .tuple [s, ref, rtv], Validation.evalArgs_nil_iff.2 rfl, ?_, hder⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
      evalExp_varE_iff.2 (by simp),
      Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_nil_iff.2 rfl⟩⟩⟩, rfl⟩
    refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
      (ρ := (((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" ref).bindVal
        "rt" rt) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_dotE_iff.2 ⟨f, evalExp_varE_iff.2 (by simp), hfield⟩)
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)

/-- **`Step_read/ref.cast-succeed`, characterised exactly.  Same premise as
`ref.test-true`; the reference is passed through instead of a boolean.** -/
theorem ruleFires_refCastSucceed_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v refCastSucceedRule ↔
      ∃ s f ref rt,
        v = .tuple
          [.case "%;%" (.tuple [.case "%;%" (.tuple [s, f]),
             .list [ref, .case "REF.CAST" rt]]),
           .list [ref]] ∧
        RefOkPrem env s f ref rt := by
  unfold refCastSucceedRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨s, f, ref, rt, rfl, rfl⟩ := matchExp_stateRefOp_iff.1 hl
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r0, rfl, hrv⟩ := matchExps_one_iff.1 hbvs
    rw [Validation.matchExp_sub_iff,
      matchExp_boundVar_iff (w := ref) (by simp)] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    refine ⟨s, f, r0, rt, rfl, ?_⟩
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, ws, w, hws, hw, hder⟩ := Validation.premHolds_rule_iff.1 hpr
    obtain rfl := Validation.evalArgs_nil_iff.1 hws
    obtain ⟨wvs, hwvs, rfl⟩ := evalExp_tupE_iff.1 hw
    obtain ⟨p, ps, hp0, hp1, hq1⟩ := Validation.evalExps_cons_iff.1 hwvs
    obtain ⟨q, qs, hq0, hq2, hq3⟩ := Validation.evalExps_cons_iff.1 hq1
    obtain ⟨rr, rs, hr0, hr2, hr3⟩ := Validation.evalExps_cons_iff.1 hq3
    obtain rfl := Validation.evalExps_nil_iff.1 hr3
    rw [evalExp_varE_iff] at hp1 hq2
    simp at hp1 hq2
    subst hp1; subst hq2; subst hr0; subst hq0; subst hp0
    obtain ⟨ws2, ps2, t2, cs2, hargs, hfind, hbody⟩ :=
      ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hr2)
    obtain ⟨mv, ws3, rfl, hmv, hrest4⟩ := evalArgs_expA_cons_iff.1 hargs
    obtain ⟨rtv', ws4, rfl, hrt, hnil⟩ := evalArgs_expA_cons_iff.1 hrest4
    obtain rfl := Validation.evalArgs_nil_iff.1 hnil
    obtain ⟨fv, hfv, hfield⟩ := evalExp_dotE_iff.1 hmv
    rw [evalExp_varE_iff] at hfv hrt
    simp at hfv hrt
    subst hfv; subst hrt
    have hnd : ((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" r0).bindVal
        "rt" rt).findDef? "inst_reftype" = none := rfl
    rw [hnd, Option.getD_none] at hfind
    exact ⟨mv, rr, hfield, ⟨ps2, t2, cs2, hfind, hbody⟩, hder⟩
  · rintro ⟨s, f, ref, rt, rfl, mv, rtv, hfield, happ, hder⟩
    refine ⟨((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" ref).bindVal "rt" rt), ((((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" ref).bindVal "rt" rt), matchExp_concl_iff.2 ⟨_, _, _, rfl,
      matchExp_stateRefOp_iff.2 ⟨s, f, ref, rt, rfl, rfl⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_sub_iff.2
            ((matchExp_boundVar_iff (w := ref) (by simp)).2 ⟨rfl, rfl⟩)⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_rule_iff.2
      ⟨rfl, [], .tuple [s, ref, rtv], Validation.evalArgs_nil_iff.2 rfl, ?_, hder⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_tupE_iff.2 ⟨_, Validation.evalExps_cons_iff.2 ⟨_, _, rfl,
      evalExp_varE_iff.2 (by simp),
      Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_varE_iff.2 (by simp),
        Validation.evalExps_cons_iff.2 ⟨_, _, rfl, ?_,
          Validation.evalExps_nil_iff.2 rfl⟩⟩⟩, rfl⟩
    refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
      (ρ := (((VarEnv.empty.bindVal "s" s).bindVal "f" f).bindVal "ref" ref).bindVal
        "rt" rt) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_dotE_iff.2 ⟨f, evalExp_varE_iff.2 (by simp), hfield⟩)
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)

end Silmaril.SpecTec.Equiv.ExecRead
