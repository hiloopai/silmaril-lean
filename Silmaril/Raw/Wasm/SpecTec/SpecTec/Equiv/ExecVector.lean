module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecDefault
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `Step_pure`'s vector block

Phase 4, continued.  The last 25 rules of `Step_pure`: `vvunop` … `vcvtop`
(rules 54–78), the SIMD operators.

They need **nothing** from `3.2-numerics.vector.spectec`, which
`Equiv/Numerics.lean` leaves untouched, and that is the point.  Every one of
them has the same shape as a scalar numeric rule of `Equiv/ExecNumeric.lean`:
a few `VCONST`s and an operator instruction on the left, one instruction on
the right, and a single premise that is either

* `c <- $vvunop_(…)` — a `MemE` against the operator's result, which is a
  list, so the `-val`/`-trap` pair partitions it; or
* `c = $vrelop_(…)` — a plain equality, for the operators that are total.

A characterisation in terms of `Applies` therefore says exactly what the rule
derives *without* saying what the operator computes — the same separation that
let `Equiv/ExecNumeric.lean`'s eight theorems survive the builtin
parameterisation unchanged.  What the operators compute is a separate question
and is still open; see "What is not reached".

## What is proved

**Provenance.**  `HasVectorRules` lists all 25 with their index in the pinned
stream; `hasVectorRules_wasm30` discharges it by `rfl`.

**Twenty-two characterisations**, in both directions: `vvunop`, `vvbinop`,
`vvternop`, `vvtestop`, `vunop-val`, `vunop-trap`, `vbinop-val`, `vbinop-trap`,
`vternop-val`, `vternop-trap`, `vrelop`, `vshiftop`, `vbitmask`, `vswizzlop`,
`vshuffle`, `vextract_lane-num`, `vextract_lane-pack`, `vextunop`, `vextbinop`,
`vextternop`, `vnarrow` and `vcvtop`.  They are the proof of the claim above —
each is the scalar proof of `Equiv/ExecNumeric.lean` with `VCONST`/`V128` for
`CONST`/`nt`, and nothing about what any operator computes enters.

**Three rules cannot fire at the pin.**  `vtestop` names a variable nothing
binds (`Equiv/ExecStepRules.not_ruleFires_vtestop_pinned`); `vsplat` and
`vreplace_lane` put `$lunpack(Lnn)` in a *pattern* position with `Lnn` bound
only later in the same pattern, so `matchExp`'s default match evaluates an
unbound variable — see `not_ruleFires_vsplat_pinned` and
`not_ruleFires_vreplaceLane_pinned` below.  That is 25 = 22 + 3, the whole
block.

`matchExp_vconstFresh_iff`, `matchExp_vvop_iff`, `matchExp_vop_iff`,
`matchExp_litVarPat_iff`, `matchExp_caseVarPat_iff`, `matchExp_lit2Pat_iff`,
`matchExp_vop3_iff` and `matchExp_shapeSubPat_iff` factor out the eight
instruction patterns the whole block is built from.

## What is not reached

* **What the vector operators denote.**  `$vvunop_`, `$vunop_`, … are defined
  in `3.2-numerics.vector.spectec` in terms of the scalar operations, which
  `Equiv/Numerics.lean` shows are mostly `hint(builtin)`.  Relating them to
  `Silmaril/Wasm/Numerics` is the natural next step and is not done.
* **The narrowings the premises perform are recorded, not justified.**
  `vnarrow` passes `sh_1!`%`.0` rather than `sh_1`, and `vextract_lane` reads
  `i!`%`.0`; the characterisations say the rule fires exactly when those
  projections succeed, which is a statement about the *shape* of the values,
  not about the types that make them succeed.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecVector

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef applies_iff_callDef)

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## The twenty-five rules, as the pinned stream records them -/

/-- `Step_pure/vvunop`, rule 54 of the pinned stream. -/
def vvunopRule : Rule :=
  (.ruleD "vvunop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "vvunop" (.varT "vvunop" [])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128"
   (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE
   [])), (.varE "c_1")])), (.caseE "VVUNOP" (.tupE [(.caseE "V128" (.tupE [])), (.varE
   "vvunop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE
   "c")]))])]) [(.ifPr (.memE (.varE "c") (.callE "vvunop_" [(.expA (.caseE "V128" (.tupE
   []))), (.expA (.varE "vvunop")), (.expA (.varE "c_1"))])))])

/-- `Step_pure/vvbinop`, rule 55 of the pinned stream. -/
def vvbinopRule : Rule :=
  (.ruleD "vvbinop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "vvbinop"
   (.varT "vvbinop" [])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))]
   "%~>%" (.tupE [(.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE
   "c_1")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_2")])), (.caseE
   "VVBINOP" (.tupE [(.caseE "V128" (.tupE [])), (.varE "vvbinop")]))]), (.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.memE (.varE
   "c") (.callE "vvbinop_" [(.expA (.caseE "V128" (.tupE []))), (.expA (.varE "vvbinop")),
   (.expA (.varE "c_1")), (.expA (.varE "c_2"))])))])

/-- `Step_pure/vvternop`, rule 56 of the pinned stream. -/
def vvternopRule : Rule :=
  (.ruleD "vvternop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "c_3" (.varT
   "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "vvternop" (.varT "vvternop" [])),
   (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE
   [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST"
   (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_2")])), (.caseE "VCONST" (.tupE [(.caseE
   "V128" (.tupE [])), (.varE "c_3")])), (.caseE "VVTERNOP" (.tupE [(.caseE "V128" (.tupE
   [])), (.varE "vvternop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE
   [])), (.varE "c")]))])]) [(.ifPr (.memE (.varE "c") (.callE "vvternop_" [(.expA (.caseE
   "V128" (.tupE []))), (.expA (.varE "vvternop")), (.expA (.varE "c_1")), (.expA (.varE
   "c_2")), (.expA (.varE "c_3"))])))])

/-- `Step_pure/vvtestop`, rule 57 of the pinned stream. -/
def vvtestopRule : Rule :=
  (.ruleD "vvtestop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))]))] "%~>%" (.tupE [(.listE
   [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE
   "VVTESTOP" (.tupE [(.caseE "V128" (.tupE [])), (.caseE "ANY_TRUE" (.tupE []))]))]),
   (.listE [(.caseE "CONST" (.tupE [(.caseE "I32" (.tupE [])), (.varE "c")]))])]) [(.ifPr
   (.cmpE .eqOp .boolT (.varE "c") (.callE "inez_" [(.expA (.callE "vsize" [(.expA (.caseE
   "V128" (.tupE [])))])), (.expA (.varE "c_1"))])))])

/-- `Step_pure/vunop-val`, rule 58 of the pinned stream. -/
def vunopValRule : Rule :=
  (.ruleD "vunop-val" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "sh" (.varT "shape" [])), (.expP "vunop" (.varT "vunop_" [(.expA (.varE "sh"))])),
   (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE
   [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VUNOP"
   (.tupE [(.varE "sh"), (.varE "vunop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE
   "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.memE (.varE "c") (.callE "vunop_"
   [(.expA (.varE "sh")), (.expA (.varE "vunop")), (.expA (.varE "c_1"))])))])

/-- `Step_pure/vunop-trap`, rule 59 of the pinned stream. -/
def vunopTrapRule : Rule :=
  (.ruleD "vunop-trap" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "sh" (.varT "shape" [])), (.expP "vunop" (.varT "vunop_" [(.expA (.varE "sh"))]))]
   "%~>%" (.tupE [(.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE
   "c_1")])), (.caseE "VUNOP" (.tupE [(.varE "sh"), (.varE "vunop")]))]), (.listE [(.caseE
   "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE "vunop_" [(.expA (.varE
   "sh")), (.expA (.varE "vunop")), (.expA (.varE "c_1"))]) (.listE [])))])

/-- `Step_pure/vbinop-val`, rule 60 of the pinned stream. -/
def vbinopValRule : Rule :=
  (.ruleD "vbinop-val" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh" (.varT
   "shape" [])), (.expP "vbinop" (.varT "vbinop_" [(.expA (.varE "sh"))])), (.expP "c"
   (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE
   [(.caseE "V128" (.tupE [])), (.varE "c_2")])), (.caseE "VBINOP" (.tupE [(.varE "sh"),
   (.varE "vbinop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])),
   (.varE "c")]))])]) [(.ifPr (.memE (.varE "c") (.callE "vbinop_" [(.expA (.varE "sh")),
   (.expA (.varE "vbinop")), (.expA (.varE "c_1")), (.expA (.varE "c_2"))])))])

/-- `Step_pure/vbinop-trap`, rule 61 of the pinned stream. -/
def vbinopTrapRule : Rule :=
  (.ruleD "vbinop-trap" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh" (.varT
   "shape" [])), (.expP "vbinop" (.varT "vbinop_" [(.expA (.varE "sh"))]))] "%~>%" (.tupE
   [(.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_2")])), (.caseE "VBINOP" (.tupE
   [(.varE "sh"), (.varE "vbinop")]))]), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr
   (.cmpE .eqOp .boolT (.callE "vbinop_" [(.expA (.varE "sh")), (.expA (.varE "vbinop")),
   (.expA (.varE "c_1")), (.expA (.varE "c_2"))]) (.listE [])))])

/-- `Step_pure/vternop-val`, rule 62 of the pinned stream. -/
def vternopValRule : Rule :=
  (.ruleD "vternop-val" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "c_3" (.varT
   "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh" (.varT "shape" [])), (.expP
   "vternop" (.varT "vternop_" [(.expA (.varE "sh"))])), (.expP "c" (.varT "vec_" [(.expA
   (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST" (.tupE [(.caseE
   "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE
   [])), (.varE "c_2")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE
   "c_3")])), (.caseE "VTERNOP" (.tupE [(.varE "sh"), (.varE "vternop")]))]), (.listE
   [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.memE
   (.varE "c") (.callE "vternop_" [(.expA (.varE "sh")), (.expA (.varE "vternop")), (.expA
   (.varE "c_1")), (.expA (.varE "c_2")), (.expA (.varE "c_3"))])))])

/-- `Step_pure/vternop-trap`, rule 63 of the pinned stream. -/
def vternopTrapRule : Rule :=
  (.ruleD "vternop-trap" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "c_3" (.varT
   "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh" (.varT "shape" [])), (.expP
   "vternop" (.varT "vternop_" [(.expA (.varE "sh"))]))] "%~>%" (.tupE [(.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE
   [(.caseE "V128" (.tupE [])), (.varE "c_2")])), (.caseE "VCONST" (.tupE [(.caseE "V128"
   (.tupE [])), (.varE "c_3")])), (.caseE "VTERNOP" (.tupE [(.varE "sh"), (.varE
   "vternop")]))]), (.listE [(.caseE "TRAP" (.tupE []))])]) [(.ifPr (.cmpE .eqOp .boolT
   (.callE "vternop_" [(.expA (.varE "sh")), (.expA (.varE "vternop")), (.expA (.varE
   "c_1")), (.expA (.varE "c_2")), (.expA (.varE "c_3"))]) (.listE [])))])

/-- `Step_pure/vtestop`, rule 64 of the pinned stream. -/
def vtestopRule : Rule :=
  (.ruleD "vtestop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "Jnn" (.varT "Jnn" [])), (.expP "M" (.varT "M" [])), (.expP "c" (.varT "num_"
   [(.expA (.caseE "I32" (.tupE [])))])), (.expP "i*" (.iterT (.varT "lane_" [(.expA (.callE
   "lanetype" [(.expA (.caseE "%X%" (.tupE [(.subE (.varE "Jnn") (.varT "Jnn" []) (.varT
   "lanetype" [])), (.varE "M")])))]))]) .list))] "%~>%" (.tupE [(.listE [(.caseE "VCONST"
   (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VTESTOP" (.tupE [(.caseE
   "%X%" (.tupE [(.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" [])), (.varE
   "M")])), (.caseE "ALL_TRUE" (.tupE []))]))]), (.listE [(.caseE "CONST" (.tupE [(.caseE
   "I32" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.iterE (.varE "i")
   (.mk .list [(.mk "i" (.varE "i*"))])) (.callE "lanes_" [(.expA (.caseE "%X%" (.tupE
   [(.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" [])), (.varE "M")]))), (.expA
   (.varE "c_1"))]))), (.ifPr (.cmpE .eqOp .boolT (.projE (.uncaseE (.varE "c") "%") (0))
   (.callE "prod" [(.expA (.iterE (.projE (.uncaseE (.callE "inez_" [(.expA (.callE
   "jsizenn" [(.expA (.varE "Jnn"))])), (.expA (.varE "i"))]) "%") (0)) (.mk .list [(.mk "i"
   (.varE "i*"))])))])))])

/-- `Step_pure/vrelop`, rule 65 of the pinned stream. -/
def vrelopRule : Rule :=
  (.ruleD "vrelop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh" (.varT
   "shape" [])), (.expP "vrelop" (.varT "vrelop_" [(.expA (.varE "sh"))])), (.expP "c"
   (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE
   [(.caseE "V128" (.tupE [])), (.varE "c_2")])), (.caseE "VRELOP" (.tupE [(.varE "sh"),
   (.varE "vrelop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])),
   (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE "vrelop_" [(.expA
   (.varE "sh")), (.expA (.varE "vrelop")), (.expA (.varE "c_1")), (.expA (.varE
   "c_2"))])))])

/-- `Step_pure/vshiftop`, rule 66 of the pinned stream. -/
def vshiftopRule : Rule :=
  (.ruleD "vshiftop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "i" (.varT "num_" [(.expA (.caseE "I32" (.tupE [])))])), (.expP "sh" (.varT
   "ishape" [])), (.expP "vshiftop" (.varT "vshiftop_" [(.expA (.varE "sh"))])), (.expP "c"
   (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "i")])), (.caseE "VSHIFTOP" (.tupE [(.varE "sh"),
   (.varE "vshiftop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])),
   (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE "vshiftop_" [(.expA
   (.varE "sh")), (.expA (.varE "vshiftop")), (.expA (.varE "c_1")), (.expA (.varE
   "i"))])))])

/-- `Step_pure/vbitmask`, rule 67 of the pinned stream. -/
def vbitmaskRule : Rule :=
  (.ruleD "vbitmask" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "sh" (.varT "ishape" [])), (.expP "c" (.varT "num_" [(.expA (.caseE "I32" (.tupE
   [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])),
   (.varE "c_1")])), (.caseE "VBITMASK" (.varE "sh"))]), (.listE [(.caseE "CONST" (.tupE
   [(.caseE "I32" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c")
   (.callE "vbitmaskop_" [(.expA (.varE "sh")), (.expA (.varE "c_1"))])))])

/-- `Step_pure/vswizzlop`, rule 68 of the pinned stream. -/
def vswizzlopRule : Rule :=
  (.ruleD "vswizzlop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh" (.varT
   "bshape" [])), (.expP "swizzlop" (.varT "vswizzlop_" [(.expA (.varE "sh"))])), (.expP "c"
   (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE
   [(.caseE "V128" (.tupE [])), (.varE "c_2")])), (.caseE "VSWIZZLOP" (.tupE [(.varE "sh"),
   (.varE "swizzlop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])),
   (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE "vswizzlop_" [(.expA
   (.varE "sh")), (.expA (.varE "swizzlop")), (.expA (.varE "c_1")), (.expA (.varE
   "c_2"))])))])

/-- `Step_pure/vshuffle`, rule 69 of the pinned stream. -/
def vshuffleRule : Rule :=
  (.ruleD "vshuffle" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh" (.varT
   "bshape" [])), (.expP "i*" (.iterT (.varT "laneidx" []) .list)), (.expP "c" (.varT "vec_"
   [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST" (.tupE
   [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE [(.caseE "V128"
   (.tupE [])), (.varE "c_2")])), (.caseE "VSHUFFLE" (.tupE [(.varE "sh"), (.iterE (.varE
   "i") (.mk .list [(.mk "i" (.varE "i*"))]))]))]), (.listE [(.caseE "VCONST" (.tupE
   [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c")
   (.callE "vshufflop_" [(.expA (.varE "sh")), (.expA (.iterE (.varE "i") (.mk .list [(.mk
   "i" (.varE "i*"))]))), (.expA (.varE "c_1")), (.expA (.varE "c_2"))])))])

/-- `Step_pure/vsplat`, rule 70 of the pinned stream. -/
def vsplatRule : Rule :=
  (.ruleD "vsplat" [(.expP "Lnn" (.varT "Lnn" [])), (.expP "c_1" (.varT "num_" [(.expA
   (.callE "lunpack" [(.expA (.varE "Lnn"))]))])), (.expP "M" (.varT "M" [])), (.expP "c"
   (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE
   "CONST" (.tupE [(.callE "lunpack" [(.expA (.varE "Lnn"))]), (.varE "c_1")])), (.caseE
   "VSPLAT" (.caseE "%X%" (.tupE [(.varE "Lnn"), (.varE "M")])))]), (.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp
   .boolT (.varE "c") (.callE "inv_lanes_" [(.expA (.caseE "%X%" (.tupE [(.varE "Lnn"),
   (.varE "M")]))), (.expA (.iterE (.callE "lpacknum_" [(.expA (.varE "Lnn")), (.expA (.varE
   "c_1"))]) (.mk (.listN (.projE (.uncaseE (.varE "M") "%") (0)) none) [])))])))])

/-- `Step_pure/vextract_lane-num`, rule 71 of the pinned stream. -/
def vextractLaneNumRule : Rule :=
  (.ruleD "vextract_lane-num" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE
   [])))])), (.expP "nt" (.varT "numtype" [])), (.expP "M" (.varT "M" [])), (.expP "i"
   (.varT "laneidx" [])), (.expP "c_2" (.varT "num_" [(.expA (.varE "nt"))]))] "%~>%" (.tupE
   [(.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE
   "VEXTRACT_LANE" (.tupE [(.caseE "%X%" (.tupE [(.subE (.varE "nt") (.varT "numtype" [])
   (.varT "lanetype" [])), (.varE "M")])), (.optE none), (.varE "i")]))]), (.listE [(.caseE
   "CONST" (.tupE [(.varE "nt"), (.varE "c_2")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE
   "c_2") (.idxE (.callE "lanes_" [(.expA (.caseE "%X%" (.tupE [(.subE (.varE "nt") (.varT
   "numtype" []) (.varT "lanetype" [])), (.varE "M")]))), (.expA (.varE "c_1"))]) (.projE
   (.uncaseE (.varE "i") "%") (0)))))])

/-- `Step_pure/vextract_lane-pack`, rule 72 of the pinned stream. -/
def vextractLanePackRule : Rule :=
  (.ruleD "vextract_lane-pack" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE
   [])))])), (.expP "pt" (.varT "packtype" [])), (.expP "M" (.varT "M" [])), (.expP "sx"
   (.varT "sx" [])), (.expP "i" (.varT "laneidx" [])), (.expP "c_2" (.varT "num_" [(.expA
   (.caseE "I32" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST" (.tupE [(.caseE
   "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VEXTRACT_LANE" (.tupE [(.caseE "%X%"
   (.tupE [(.subE (.varE "pt") (.varT "packtype" []) (.varT "lanetype" [])), (.varE "M")])),
   (.optE (some (.varE "sx"))), (.varE "i")]))]), (.listE [(.caseE "CONST" (.tupE [(.caseE
   "I32" (.tupE [])), (.varE "c_2")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c_2") (.callE
   "extend__" [(.expA (.callE "psize" [(.expA (.varE "pt"))])), (.expA (.numE (.natN 32))),
   (.expA (.varE "sx")), (.expA (.idxE (.callE "lanes_" [(.expA (.caseE "%X%" (.tupE [(.subE
   (.varE "pt") (.varT "packtype" []) (.varT "lanetype" [])), (.varE "M")]))), (.expA (.varE
   "c_1"))]) (.projE (.uncaseE (.varE "i") "%") (0))))])))])

/-- `Step_pure/vreplace_lane`, rule 73 of the pinned stream. -/
def vreplaceLaneRule : Rule :=
  (.ruleD "vreplace_lane" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE
   [])))])), (.expP "Lnn" (.varT "Lnn" [])), (.expP "c_2" (.varT "num_" [(.expA (.callE
   "lunpack" [(.expA (.varE "Lnn"))]))])), (.expP "M" (.varT "M" [])), (.expP "i" (.varT
   "laneidx" [])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%"
   (.tupE [(.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])),
   (.caseE "CONST" (.tupE [(.callE "lunpack" [(.expA (.varE "Lnn"))]), (.varE "c_2")])),
   (.caseE "VREPLACE_LANE" (.tupE [(.caseE "%X%" (.tupE [(.varE "Lnn"), (.varE "M")])),
   (.varE "i")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE
   "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE "inv_lanes_" [(.expA (.caseE
   "%X%" (.tupE [(.varE "Lnn"), (.varE "M")]))), (.expA (.updE (.callE "lanes_" [(.expA
   (.caseE "%X%" (.tupE [(.varE "Lnn"), (.varE "M")]))), (.expA (.varE "c_1"))]) (.idxP
   .rootP (.projE (.uncaseE (.varE "i") "%") (0))) (.callE "lpacknum_" [(.expA (.varE
   "Lnn")), (.expA (.varE "c_2"))])))])))])

/-- `Step_pure/vextunop`, rule 74 of the pinned stream. -/
def vextunopRule : Rule :=
  (.ruleD "vextunop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "sh_2" (.varT "ishape" [])), (.expP "sh_1" (.varT "ishape" [])), (.expP "vextunop"
   (.varT "vextunop__" [(.expA (.varE "sh_1")), (.expA (.varE "sh_2"))])), (.expP "c" (.varT
   "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST"
   (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VEXTUNOP" (.tupE [(.varE
   "sh_2"), (.varE "sh_1"), (.varE "vextunop")]))]), (.listE [(.caseE "VCONST" (.tupE
   [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE
   "vextunop__" [(.expA (.varE "sh_1")), (.expA (.varE "sh_2")), (.expA (.varE "vextunop")),
   (.expA (.varE "c_1"))]) (.varE "c")))])

/-- `Step_pure/vextbinop`, rule 75 of the pinned stream. -/
def vextbinopRule : Rule :=
  (.ruleD "vextbinop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh_2" (.varT
   "ishape" [])), (.expP "sh_1" (.varT "ishape" [])), (.expP "vextbinop" (.varT
   "vextbinop__" [(.expA (.varE "sh_1")), (.expA (.varE "sh_2"))])), (.expP "c" (.varT
   "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST"
   (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE [(.caseE
   "V128" (.tupE [])), (.varE "c_2")])), (.caseE "VEXTBINOP" (.tupE [(.varE "sh_2"), (.varE
   "sh_1"), (.varE "vextbinop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128"
   (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.callE "vextbinop__" [(.expA
   (.varE "sh_1")), (.expA (.varE "sh_2")), (.expA (.varE "vextbinop")), (.expA (.varE
   "c_1")), (.expA (.varE "c_2"))]) (.varE "c")))])

/-- `Step_pure/vextternop`, rule 76 of the pinned stream. -/
def vextternopRule : Rule :=
  (.ruleD "vextternop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "c_3" (.varT
   "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh_2" (.varT "ishape" [])), (.expP
   "sh_1" (.varT "ishape" [])), (.expP "vextternop" (.varT "vextternop__" [(.expA (.varE
   "sh_1")), (.expA (.varE "sh_2"))])), (.expP "c" (.varT "vec_" [(.expA (.caseE "V128"
   (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE
   [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE
   "c_2")])), (.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_3")])), (.caseE
   "VEXTTERNOP" (.tupE [(.varE "sh_2"), (.varE "sh_1"), (.varE "vextternop")]))]), (.listE
   [(.caseE "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE
   .eqOp .boolT (.callE "vextternop__" [(.expA (.varE "sh_1")), (.expA (.varE "sh_2")),
   (.expA (.varE "vextternop")), (.expA (.varE "c_1")), (.expA (.varE "c_2")), (.expA (.varE
   "c_3"))]) (.varE "c")))])

/-- `Step_pure/vnarrow`, rule 77 of the pinned stream. -/
def vnarrowRule : Rule :=
  (.ruleD "vnarrow" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "c_2" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])), (.expP "sh_2" (.varT
   "ishape" [])), (.expP "sh_1" (.varT "ishape" [])), (.expP "sx" (.varT "sx" [])), (.expP
   "c" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE
   "VCONST" (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCONST" (.tupE
   [(.caseE "V128" (.tupE [])), (.varE "c_2")])), (.caseE "VNARROW" (.tupE [(.varE "sh_2"),
   (.varE "sh_1"), (.varE "sx")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE "V128"
   (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE
   "vnarrowop__" [(.expA (.projE (.uncaseE (.varE "sh_1") "%") (0))), (.expA (.projE
   (.uncaseE (.varE "sh_2") "%") (0))), (.expA (.varE "sx")), (.expA (.varE "c_1")), (.expA
   (.varE "c_2"))])))])

/-- `Step_pure/vcvtop`, rule 78 of the pinned stream. -/
def vcvtopRule : Rule :=
  (.ruleD "vcvtop" [(.expP "c_1" (.varT "vec_" [(.expA (.caseE "V128" (.tupE [])))])),
   (.expP "sh_2" (.varT "shape" [])), (.expP "sh_1" (.varT "shape" [])), (.expP "vcvtop"
   (.varT "vcvtop__" [(.expA (.varE "sh_1")), (.expA (.varE "sh_2"))])), (.expP "c" (.varT
   "vec_" [(.expA (.caseE "V128" (.tupE [])))]))] "%~>%" (.tupE [(.listE [(.caseE "VCONST"
   (.tupE [(.caseE "V128" (.tupE [])), (.varE "c_1")])), (.caseE "VCVTOP" (.tupE [(.varE
   "sh_2"), (.varE "sh_1"), (.varE "vcvtop")]))]), (.listE [(.caseE "VCONST" (.tupE [(.caseE
   "V128" (.tupE [])), (.varE "c")]))])]) [(.ifPr (.cmpE .eqOp .boolT (.varE "c") (.callE
   "vcvtop__" [(.expA (.varE "sh_1")), (.expA (.varE "sh_2")), (.expA (.varE "vcvtop")),
   (.expA (.varE "c_1"))])))])

/-- The pinned wasm-3.0 specification has all twenty-five at those indices
inside `Step_pure`. -/
structure HasVectorRules (env : Env) : Prop where
  /-- `Step_pure/vvunop`, rule 54. -/
  vvunop : HasRuleAt env "Step_pure" "%~>%" 54 vvunopRule
  /-- `Step_pure/vvbinop`, rule 55. -/
  vvbinop : HasRuleAt env "Step_pure" "%~>%" 55 vvbinopRule
  /-- `Step_pure/vvternop`, rule 56. -/
  vvternop : HasRuleAt env "Step_pure" "%~>%" 56 vvternopRule
  /-- `Step_pure/vvtestop`, rule 57. -/
  vvtestop : HasRuleAt env "Step_pure" "%~>%" 57 vvtestopRule
  /-- `Step_pure/vunop-val`, rule 58. -/
  vunopVal : HasRuleAt env "Step_pure" "%~>%" 58 vunopValRule
  /-- `Step_pure/vunop-trap`, rule 59. -/
  vunopTrap : HasRuleAt env "Step_pure" "%~>%" 59 vunopTrapRule
  /-- `Step_pure/vbinop-val`, rule 60. -/
  vbinopVal : HasRuleAt env "Step_pure" "%~>%" 60 vbinopValRule
  /-- `Step_pure/vbinop-trap`, rule 61. -/
  vbinopTrap : HasRuleAt env "Step_pure" "%~>%" 61 vbinopTrapRule
  /-- `Step_pure/vternop-val`, rule 62. -/
  vternopVal : HasRuleAt env "Step_pure" "%~>%" 62 vternopValRule
  /-- `Step_pure/vternop-trap`, rule 63. -/
  vternopTrap : HasRuleAt env "Step_pure" "%~>%" 63 vternopTrapRule
  /-- `Step_pure/vtestop`, rule 64. -/
  vtestop : HasRuleAt env "Step_pure" "%~>%" 64 vtestopRule
  /-- `Step_pure/vrelop`, rule 65. -/
  vrelop : HasRuleAt env "Step_pure" "%~>%" 65 vrelopRule
  /-- `Step_pure/vshiftop`, rule 66. -/
  vshiftop : HasRuleAt env "Step_pure" "%~>%" 66 vshiftopRule
  /-- `Step_pure/vbitmask`, rule 67. -/
  vbitmask : HasRuleAt env "Step_pure" "%~>%" 67 vbitmaskRule
  /-- `Step_pure/vswizzlop`, rule 68. -/
  vswizzlop : HasRuleAt env "Step_pure" "%~>%" 68 vswizzlopRule
  /-- `Step_pure/vshuffle`, rule 69. -/
  vshuffle : HasRuleAt env "Step_pure" "%~>%" 69 vshuffleRule
  /-- `Step_pure/vsplat`, rule 70. -/
  vsplat : HasRuleAt env "Step_pure" "%~>%" 70 vsplatRule
  /-- `Step_pure/vextract_lane-num`, rule 71. -/
  vextractLaneNum : HasRuleAt env "Step_pure" "%~>%" 71 vextractLaneNumRule
  /-- `Step_pure/vextract_lane-pack`, rule 72. -/
  vextractLanePack : HasRuleAt env "Step_pure" "%~>%" 72 vextractLanePackRule
  /-- `Step_pure/vreplace_lane`, rule 73. -/
  vreplaceLane : HasRuleAt env "Step_pure" "%~>%" 73 vreplaceLaneRule
  /-- `Step_pure/vextunop`, rule 74. -/
  vextunop : HasRuleAt env "Step_pure" "%~>%" 74 vextunopRule
  /-- `Step_pure/vextbinop`, rule 75. -/
  vextbinop : HasRuleAt env "Step_pure" "%~>%" 75 vextbinopRule
  /-- `Step_pure/vextternop`, rule 76. -/
  vextternop : HasRuleAt env "Step_pure" "%~>%" 76 vextternopRule
  /-- `Step_pure/vnarrow`, rule 77. -/
  vnarrow : HasRuleAt env "Step_pure" "%~>%" 77 vnarrowRule
  /-- `Step_pure/vcvtop`, rule 78. -/
  vcvtop : HasRuleAt env "Step_pure" "%~>%" 78 vcvtopRule

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- Discharged by `rfl` against the pinned stream. -/
theorem hasVectorRules_wasm30 : HasVectorRules (envOfScript Specs.wasm30) :=
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
   ⟨_, _, _, rfl, rfl, rfl⟩⟩

/-! ## The values the vector rules mention -/

/-- `V128`, the one vector type. -/
def v128V : Value := Execution.caseNilV "V128"

/-- `(VCONST V128 c)`. -/
def vconstV (c : Value) : Value := .case "VCONST" (.tuple [v128V, c])

/-- `(VVUNOP V128 op)` and its binary/ternary/test siblings. -/
def vvunopV (op : Value) : Value := .case "VVUNOP" (.tuple [v128V, op])

/-- `(VVBINOP V128 op)`. -/
def vvbinopV (op : Value) : Value := .case "VVBINOP" (.tuple [v128V, op])

/-- `(VUNOP sh op)`. -/
def vunopV (sh op : Value) : Value := .case "VUNOP" (.tuple [sh, op])

/-- `(VBINOP sh op)`. -/
def vbinopV (sh op : Value) : Value := .case "VBINOP" (.tuple [sh, op])

/-! ## The `V128` constant pattern, matched once

Every rule in this block opens with `(VCONST V128 c)`.  Matching that is the
same four steps each time, so they are done once. -/

/-- `(VCONST V128 c)` as a pattern: a fresh variable for the payload. -/
theorem matchExp_vconstFresh_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v : Value}
    (hx : ρ.findVal? x = none) :
    MatchExp env ρ (.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE x])) v ρ' ↔
      ∃ c, v = vconstV c ∧ ρ' = ρ.bindVal x c := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨tv, cv, υ, rfl, htv, hcv⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff hx] at hcv
    exact ⟨cv, rfl, hcv⟩
  · rintro ⟨c, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_freshVar_iff hx).2 rfl⟩⟩⟩

/-- `(OP V128 op)` as a pattern: the type is the literal `V128`, the operator a
fresh variable. -/
theorem matchExp_vvop_iff {env : Env} {ρ ρ' : VarEnv} {mo : MixopS} {x : IL.Id} {v : Value}
    (hx : ρ.findVal? x = none) :
    MatchExp env ρ (.caseE mo (.tupE [.caseE "V128" (.tupE []), .varE x])) v ρ' ↔
      ∃ op, v = .case mo (.tuple [v128V, op]) ∧ ρ' = ρ.bindVal x op := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨tv, cv, υ, rfl, htv, hcv⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff hx] at hcv
    exact ⟨cv, rfl, hcv⟩
  · rintro ⟨op, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_freshVar_iff hx).2 rfl⟩⟩⟩

/-- `(OP sh op)` as a pattern: both components fresh variables. -/
theorem matchExp_vop_iff {env : Env} {ρ ρ' : VarEnv} {mo : MixopS} {x y : IL.Id} {v : Value}
    (hx : ρ.findVal? x = none) (hy : ∀ w, (ρ.bindVal x w).findVal? y = none) :
    MatchExp env ρ (.caseE mo (.tupE [.varE x, .varE y])) v ρ' ↔
      ∃ sh op, v = .case mo (.tuple [sh, op]) ∧ ρ' = (ρ.bindVal x sh).bindVal y op := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨sv, ov, υ, rfl, hsv, hov⟩ := matchExps_two_iff.1 hws
    rw [matchExp_freshVar_iff hx] at hsv
    subst hsv
    rw [matchExp_freshVar_iff (hy sv)] at hov
    exact ⟨sv, ov, rfl, hov⟩
  · rintro ⟨sh, op, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, (matchExp_freshVar_iff hx).2 rfl,
        (matchExp_freshVar_iff (hy sh)).2 rfl⟩⟩⟩

/-! ## The `vv*` rules, characterised exactly -/

/-- `Step_pure/vvunop` (`4.3:435`): the bitwise vector unary operator.  As with
`unop-val`, the premise is a `MemE`, so `memValue` is left in the statement —
nothing in the IL forces `$vvunop_`'s result to be a list. -/
theorem ruleFires_vvunop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vvunopRule ↔
      ∃ c₁ op c w, v = Execution.stepV [vconstV c₁, vvunopV op] [vconstV c] ∧
        Applies env "vvunop_" [.val v128V, .val op, .val c₁] w ∧
        memValue c w = .ok (.bool true) := by
  unfold vvunopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vvop_iff (by simp)] at h2
    obtain ⟨op, rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨r, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    refine ⟨c₁, op, c, v₂, rfl, ?_, by rw [hv₁]; exact hmem⟩
    refine (applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "c_1" c₁).bindVal "vvunop"
      op).bindVal "c" c) rfl ?_).mpr (evalExp_callE_iff.1 hv₂)
    exact evalArgs_cons (evalExp_caseE_iff.2 ⟨_,
        evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩)
      (evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))
  · rintro ⟨c₁, op, c, w, rfl, happ, hmem⟩
    refine ⟨((VarEnv.empty.bindVal "c_1" c₁).bindVal "vvunop" op).bindVal "c" c,
      ((VarEnv.empty.bindVal "c_1" c₁).bindVal "vvunop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vvop_iff (by simp)).2 ⟨op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "vvunop" op).bindVal "c" c) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_caseE_iff.2 ⟨_,
        evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩)
      (evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))

/-- Five arguments, for `$vvternop_`. -/
theorem evalArgs_five {env : Env} {ρ : VarEnv} {a b c d e : Value} {e₁ : Exp}
    {w x y z : IL.Id} (h₁ : EvalExp env ρ e₁ a) (hw : ρ.findVal? w = some b)
    (hx : ρ.findVal? x = some c) (hy : ρ.findVal? y = some d)
    (hz : ρ.findVal? z = some e) :
    EvalArgs env ρ [.expA e₁, .expA (.varE w), .expA (.varE x), .expA (.varE y),
      .expA (.varE z)] [.val a, .val b, .val c, .val d, .val e] :=
  evalArgs_cons h₁ (evalArgs_cons (evalExp_varE_iff.2 hw)
    (evalArgs_cons (evalExp_varE_iff.2 hx)
      (evalArgs_cons (evalExp_varE_iff.2 hy)
        (evalArgs_cons (evalExp_varE_iff.2 hz) evalArgs_nil))))

/-- `V128` as an argument, which every `vv*` call leads with. -/
theorem evalExp_v128 {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "V128" (.tupE [])) v128V :=
  evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩

/-- `Step_pure/vvbinop` (`4.3:439`). -/
theorem ruleFires_vvbinop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vvbinopRule ↔
      ∃ c₁ c₂ op c w,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vvbinopV op] [vconstV c] ∧
        Applies env "vvbinop_" [.val v128V, .val op, .val c₁, .val c₂] w ∧
        memValue c w = .ok (.bool true) := by
  unfold vvbinopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vvop_iff (by simp)] at h3
    obtain ⟨op, rfl, rfl⟩ := h3
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    refine ⟨c₁, c₂, op, c, v₂, rfl, ?_, by rw [hv₁]; exact hmem⟩
    refine (applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "vvbinop" op).bindVal "c" c) rfl ?_).mpr (evalExp_callE_iff.1 hv₂)
    exact evalArgs_cons evalExp_v128
      (evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (evalArgs_cons (evalExp_varE_iff.2 (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)))
  · rintro ⟨c₁, c₂, op, c, w, rfl, happ, hmem⟩
    refine ⟨(((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "vvbinop"
        op).bindVal "c" c,
      (((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "vvbinop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vvop_iff (by simp)).2 ⟨op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "vvbinop" op).bindVal "c" c) rfl ?_).mp happ)
    exact evalArgs_cons evalExp_v128
      (evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (evalArgs_cons (evalExp_varE_iff.2 (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)))

/-- `Step_pure/vunop-val` (`4.3:451`): the shape-indexed unary operator. -/
theorem ruleFires_vunopVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vunopValRule ↔
      ∃ c₁ sh op c w, v = Execution.stepV [vconstV c₁, vunopV sh op] [vconstV c] ∧
        Applies env "vunop_" [.val sh, .val op, .val c₁] w ∧
        memValue c w = .ok (.bool true) := by
  unfold vunopValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h2
    obtain ⟨sh, op, rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    refine ⟨c₁, sh, op, c, v₂, rfl, ?_, by rw [hv₁]; exact hmem⟩
    refine (applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh"
      sh).bindVal "vunop" op).bindVal "c" c) rfl ?_).mpr (evalExp_callE_iff.1 hv₂)
    exact ExecNumeric.evalArgs_three (by simp) (by simp) (by simp)
  · rintro ⟨c₁, sh, op, c, w, rfl, happ, hmem⟩
    refine ⟨(((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh" sh).bindVal "vunop" op).bindVal
        "c" c,
      (((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh" sh).bindVal "vunop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "sh" sh).bindVal "vunop" op).bindVal "c" c) rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_three (by simp) (by simp) (by simp)

/-- `Step_pure/vunop-trap` (`4.3:455`): the companion trap rule. -/
theorem ruleFires_vunopTrap_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vunopTrapRule ↔
      ∃ c₁ sh op, v = Execution.stepV [vconstV c₁, vunopV sh op] [Execution.trapV] ∧
        Applies env "vunop_" [.val sh, .val op, .val c₁] (.list []) := by
  unfold vunopTrapRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h2
    obtain ⟨sh, op, rfl, rfl⟩ := h2
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
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    refine ⟨c₁, sh, op, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh"
      sh).bindVal "vunop" op) rfl ?_).mpr (evalExp_callE_iff.1 hv₁)
    exact ExecNumeric.evalArgs_three (by simp) (by simp) (by simp)
  · rintro ⟨c₁, sh, op, rfl, happ⟩
    refine ⟨((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh" sh).bindVal "vunop" op,
      ((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh" sh).bindVal "vunop" op,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.list [], .list [], ?_,
      evalExp_listE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "sh" sh).bindVal "vunop" op) rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_three (by simp) (by simp) (by simp)

/-- `Step_pure/vbinop-val` (`4.3:459`): the shape-indexed binary operator. -/
theorem ruleFires_vbinopVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vbinopValRule ↔
      ∃ c₁ c₂ sh op c w,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vbinopV sh op] [vconstV c] ∧
        Applies env "vbinop_" [.val sh, .val op, .val c₁, .val c₂] w ∧
        memValue c w = .ok (.bool true) := by
  unfold vbinopValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h3
    obtain ⟨sh, op, rfl, rfl⟩ := h3
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    refine ⟨c₁, c₂, sh, op, c, v₂, rfl, ?_, by rw [hv₁]; exact hmem⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh"
      sh).bindVal "vbinop" op).bindVal "c" c) rfl ?_).mpr (evalExp_callE_iff.1 hv₂)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, c₂, sh, op, c, w, rfl, happ, hmem⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "vbinop" op).bindVal
        "c" c,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "vbinop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "vbinop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/vbinop-trap` (`4.3:463`): the companion trap rule. -/
theorem ruleFires_vbinopTrap_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vbinopTrapRule ↔
      ∃ c₁ c₂ sh op,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vbinopV sh op] [Execution.trapV] ∧
        Applies env "vbinop_" [.val sh, .val op, .val c₁, .val c₂] (.list []) := by
  unfold vbinopTrapRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h3
    obtain ⟨sh, op, rfl, rfl⟩ := h3
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
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    refine ⟨c₁, c₂, sh, op, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh"
      sh).bindVal "vbinop" op) rfl ?_).mpr (evalExp_callE_iff.1 hv₁)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, c₂, sh, op, rfl, happ⟩
    refine ⟨(((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "vbinop" op,
      (((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "vbinop" op,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.list [], .list [], ?_,
      evalExp_listE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "vbinop" op) rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)


/-! ## Three more pattern lemmas

The block's instruction patterns come in six shapes.  `matchExp_vconstFresh_iff`,
`matchExp_vvop_iff` and `matchExp_vop_iff` cover three of them; these cover the
rest. -/

/-- `(OP ty x)` with `ty` a literal nullary injection and `x` a fresh variable.
This is `matchExp_vvop_iff` at an arbitrary type, which `CONST (I32 c)` — the
operand of `vshiftop`, and the result of `vbitmask` and `vvtestop` — needs. -/
theorem matchExp_litVarPat_iff {env : Env} {ρ ρ' : VarEnv} {mo ty : MixopS} {x : IL.Id}
    {v : Value} (hx : ρ.findVal? x = none) :
    MatchExp env ρ (.caseE mo (.tupE [.caseE ty (.tupE []), .varE x])) v ρ' ↔
      ∃ c, v = .case mo (.tuple [caseNilV ty, c]) ∧ ρ' = ρ.bindVal x c := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨tv, cv, υ, rfl, htv, hcv⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff hx] at hcv
    exact ⟨cv, rfl, hcv⟩
  · rintro ⟨c, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_freshVar_iff hx).2 rfl⟩⟩⟩

/-- `(OP x)` with a bare variable payload — the shape `VBITMASK` has, alone in
the block. -/
theorem matchExp_caseVarPat_iff {env : Env} {ρ ρ' : VarEnv} {mo : MixopS} {x : IL.Id}
    {v : Value} (hx : ρ.findVal? x = none) :
    MatchExp env ρ (.caseE mo (.varE x)) v ρ' ↔
      ∃ w, v = .case mo w ∧ ρ' = ρ.bindVal x w := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    rw [matchExp_freshVar_iff hx] at hw
    exact ⟨w, rfl, hw⟩
  · rintro ⟨w, rfl, rfl⟩
    exact ⟨w, rfl, (matchExp_freshVar_iff hx).2 rfl⟩

/-- `(OP x y z)`: three fresh variables, the shape of every `VEXT*OP`,
`VNARROW` and `VCVTOP`. -/
theorem matchExp_vop3_iff {env : Env} {ρ ρ' : VarEnv} {mo : MixopS} {x y z : IL.Id}
    {v : Value} (hx : ρ.findVal? x = none) (hy : ∀ w, (ρ.bindVal x w).findVal? y = none)
    (hz : ∀ w u, ((ρ.bindVal x w).bindVal y u).findVal? z = none) :
    MatchExp env ρ (.caseE mo (.tupE [.varE x, .varE y, .varE z])) v ρ' ↔
      ∃ a b c, v = .case mo (.tuple [a, b, c]) ∧
        ρ' = ((ρ.bindVal x a).bindVal y b).bindVal z c := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨a, b, c, σ, τ, rfl, ha, hb, hc⟩ := matchExps_three_iff.1 hws
    rw [matchExp_freshVar_iff hx] at ha
    subst ha
    rw [matchExp_freshVar_iff (hy a)] at hb
    subst hb
    rw [matchExp_freshVar_iff (hz a b)] at hc
    exact ⟨a, b, c, rfl, hc⟩
  · rintro ⟨a, b, c, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_three_iff.2 ⟨_, _, _, _, _, rfl, (matchExp_freshVar_iff hx).2 rfl,
        (matchExp_freshVar_iff (hy a)).2 rfl, (matchExp_freshVar_iff (hz a b)).2 rfl⟩⟩⟩

/-- Six arguments, for `$vextternop__`. -/
theorem evalArgs_six {env : Env} {ρ : VarEnv} {a b c d e f : Value}
    {u w x y z t : IL.Id} (hu : ρ.findVal? u = some a) (hw : ρ.findVal? w = some b)
    (hx : ρ.findVal? x = some c) (hy : ρ.findVal? y = some d)
    (hz : ρ.findVal? z = some e) (ht : ρ.findVal? t = some f) :
    EvalArgs env ρ [.expA (.varE u), .expA (.varE w), .expA (.varE x), .expA (.varE y),
      .expA (.varE z), .expA (.varE t)] [.val a, .val b, .val c, .val d, .val e, .val f] :=
  evalArgs_cons (evalExp_varE_iff.2 hu) (evalArgs_five (evalExp_varE_iff.2 hw) hx hy hz ht)

/-! ## The ternary operators -/

/-- `(VVTERNOP V128 op)`. -/
def vvternopV (op : Value) : Value := .case "VVTERNOP" (.tuple [v128V, op])

/-- `(VTERNOP sh op)`. -/
def vternopV (sh op : Value) : Value := .case "VTERNOP" (.tuple [sh, op])

/-- `Step_pure/vvternop` (`4.3:443`): the bitwise vector ternary operator,
`vvbinop` with one more operand. -/
theorem ruleFires_vvternop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vvternopRule ↔
      ∃ c₁ c₂ c₃ op c w,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vconstV c₃, vvternopV op] [vconstV c] ∧
        Applies env "vvternop_" [.val v128V, .val op, .val c₁, .val c₂, .val c₃] w ∧
        memValue c w = .ok (.bool true) := by
  unfold vvternopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, s, τ₁, τ₂, τ₃, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vconstFresh_iff (by simp)] at h3
    obtain ⟨c₃, rfl, rfl⟩ := h3
    rw [matchExp_vvop_iff (by simp)] at h4
    obtain ⟨op, rfl, rfl⟩ := h4
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    refine ⟨c₁, c₂, c₃, op, c, v₂, rfl, ?_, by rw [hv₁]; exact hmem⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "c_3" c₃).bindVal "vvternop" op).bindVal "c" c) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact evalArgs_five evalExp_v128 (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, c₂, c₃, op, c, w, rfl, happ, hmem⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "c_3"
        c₃).bindVal "vvternop" op).bindVal "c" c,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "c_3" c₃).bindVal
        "vvternop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₃, rfl, rfl⟩,
          (matchExp_vvop_iff (by simp)).2 ⟨op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "c_3" c₃).bindVal "vvternop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact evalArgs_five evalExp_v128 (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/vternop-val` (`4.3:467`): the shape-indexed ternary operator. -/
theorem ruleFires_vternopVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vternopValRule ↔
      ∃ c₁ c₂ c₃ sh op c w,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vconstV c₃, vternopV sh op]
          [vconstV c] ∧
        Applies env "vternop_" [.val sh, .val op, .val c₁, .val c₂, .val c₃] w ∧
        memValue c w = .ok (.bool true) := by
  unfold vternopValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, s, τ₁, τ₂, τ₃, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vconstFresh_iff (by simp)] at h3
    obtain ⟨c₃, rfl, rfl⟩ := h3
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h4
    obtain ⟨sh, op, rfl, rfl⟩ := h4
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hmem⟩ := evalExp_memE_iff.1 hev
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    refine ⟨c₁, c₂, c₃, sh, op, c, v₂, rfl, ?_, by rw [hv₁]; exact hmem⟩
    refine (applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "c_3" c₃).bindVal "sh" sh).bindVal "vternop" op).bindVal "c" c)
      rfl ?_).mpr (evalExp_callE_iff.1 hv₂)
    exact evalArgs_five (evalExp_varE_iff.2 (by simp)) (by simp) (by simp) (by simp)
      (by simp)
  · rintro ⟨c₁, c₂, c₃, sh, op, c, w, rfl, happ, hmem⟩
    refine ⟨(((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "c_3"
        c₃).bindVal "sh" sh).bindVal "vternop" op).bindVal "c" c,
      (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "c_3" c₃).bindVal
        "sh" sh).bindVal "vternop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₃, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_memE_iff.2 ⟨c, w, evalExp_varE_iff.2 (by simp), ?_, hmem⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "c_3" c₃).bindVal "sh" sh).bindVal "vternop"
      op).bindVal "c" c) rfl ?_).mp happ)
    exact evalArgs_five (evalExp_varE_iff.2 (by simp)) (by simp) (by simp) (by simp)
      (by simp)

/-- `Step_pure/vternop-trap` (`4.3:471`): the companion trap rule. -/
theorem ruleFires_vternopTrap_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vternopTrapRule ↔
      ∃ c₁ c₂ c₃ sh op,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vconstV c₃, vternopV sh op]
          [Execution.trapV] ∧
        Applies env "vternop_" [.val sh, .val op, .val c₁, .val c₂, .val c₃] (.list []) := by
  unfold vternopTrapRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, s, τ₁, τ₂, τ₃, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vconstFresh_iff (by simp)] at h3
    obtain ⟨c₃, rfl, rfl⟩ := h3
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h4
    obtain ⟨sh, op, rfl, rfl⟩ := h4
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
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    refine ⟨c₁, c₂, c₃, sh, op, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "c_3" c₃).bindVal "sh" sh).bindVal "vternop" op) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₁)
    exact evalArgs_five (evalExp_varE_iff.2 (by simp)) (by simp) (by simp) (by simp)
      (by simp)
  · rintro ⟨c₁, c₂, c₃, sh, op, rfl, happ⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "c_3"
        c₃).bindVal "sh" sh).bindVal "vternop" op,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "c_3" c₃).bindVal
        "sh" sh).bindVal "vternop" op,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₃, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨.list [], .list [], ?_,
      evalExp_listE_iff.2 ⟨[], Validation.evalExps_nil_iff.2 rfl, rfl⟩,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "c_3" c₃).bindVal "sh" sh).bindVal "vternop" op)
      rfl ?_).mp happ)
    exact evalArgs_five (evalExp_varE_iff.2 (by simp)) (by simp) (by simp) (by simp)
      (by simp)


/-! ## The operators whose premise is an equality

`vvunop` … `vternop` have a `MemE` premise, because their operator may trap and
so returns a list.  The remaining operators are total: their premise is a plain
`c = $f(…)`, and the characterisation names the result directly rather than
through `memValue`. -/

/-- `(VRELOP sh op)`. -/
def vrelopV (sh op : Value) : Value := .case "VRELOP" (.tuple [sh, op])

/-- `(VSWIZZLOP sh op)`. -/
def vswizzlopV (sh op : Value) : Value := .case "VSWIZZLOP" (.tuple [sh, op])

/-- `(VSHIFTOP sh op)`. -/
def vshiftopV (sh op : Value) : Value := .case "VSHIFTOP" (.tuple [sh, op])

/-- `(VBITMASK sh)` — the one instruction in the block whose payload is not a
tuple. -/
def vbitmaskV (sh : Value) : Value := .case "VBITMASK" sh

/-- `(VCVTOP sh_2 sh_1 op)`. -/
def vcvtopV (sh₂ sh₁ op : Value) : Value := .case "VCVTOP" (.tuple [sh₂, sh₁, op])

/-- `Step_pure/vrelop` (`4.3:479`): the shape-indexed comparison.  Like the
scalar `relop`, `$vrelop_` is total, so there is no trap rule. -/
theorem ruleFires_vrelop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vrelopRule ↔
      ∃ c₁ c₂ sh op c,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vrelopV sh op] [vconstV c] ∧
        Applies env "vrelop_" [.val sh, .val op, .val c₁, .val c₂] c := by
  unfold vrelopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h3
    obtain ⟨sh, op, rfl, rfl⟩ := h3
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    refine ⟨c₁, c₂, sh, op, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "sh" sh).bindVal "vrelop" op).bindVal "c" _) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, c₂, sh, op, c, rfl, happ⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh"
        sh).bindVal "vrelop" op).bindVal "c" c,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal
        "vrelop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "vrelop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/vswizzlop` (`4.3:495`): `vrelop`'s shape with a `bshape` and a
different operator. -/
theorem ruleFires_vswizzlop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vswizzlopRule ↔
      ∃ c₁ c₂ sh op c,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vswizzlopV sh op] [vconstV c] ∧
        Applies env "vswizzlop_" [.val sh, .val op, .val c₁, .val c₂] c := by
  unfold vswizzlopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h3
    obtain ⟨sh, op, rfl, rfl⟩ := h3
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    refine ⟨c₁, c₂, sh, op, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "sh" sh).bindVal "swizzlop" op).bindVal "c" _) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, c₂, sh, op, c, rfl, happ⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh"
        sh).bindVal "swizzlop" op).bindVal "c" c,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal
        "swizzlop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "swizzlop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/vshiftop` (`4.3:483`): the shift takes a *scalar* `I32` count,
so its second operand is a `CONST`, not a `VCONST`. -/
theorem ruleFires_vshiftop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vshiftopRule ↔
      ∃ c₁ i sh op c,
        v = Execution.stepV [vconstV c₁, Execution.constV Execution.i32V i,
          vshiftopV sh op] [vconstV c] ∧
        Applies env "vshiftop_" [.val sh, .val op, .val c₁, .val i] c := by
  unfold vshiftopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_litVarPat_iff (by simp)] at h2
    obtain ⟨i, rfl, rfl⟩ := h2
    rw [matchExp_vop_iff (by simp) (fun _ => by simp)] at h3
    obtain ⟨sh, op, rfl, rfl⟩ := h3
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    refine ⟨c₁, i, sh, op, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "i"
      i).bindVal "sh" sh).bindVal "vshiftop" op).bindVal "c" _) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, i, sh, op, c, rfl, happ⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "i" i).bindVal "sh"
        sh).bindVal "vshiftop" op).bindVal "c" c,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "i" i).bindVal "sh" sh).bindVal
        "vshiftop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_litVarPat_iff (by simp)).2 ⟨i, rfl, rfl⟩,
          (matchExp_vop_iff (by simp) (fun _ => by simp)).2 ⟨sh, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "i" i).bindVal "sh" sh).bindVal "vshiftop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/vbitmask` (`4.3:487`): one vector in, one `I32` out. -/
theorem ruleFires_vbitmask_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vbitmaskRule ↔
      ∃ c₁ sh c,
        v = Execution.stepV [vconstV c₁, vbitmaskV sh]
          [Execution.constV Execution.i32V c] ∧
        Applies env "vbitmaskop_" [.val sh, .val c₁] c := by
  unfold vbitmaskRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_caseVarPat_iff (by simp)] at h2
    obtain ⟨sh, rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_litVarPat_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    refine ⟨c₁, sh, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh"
      sh).bindVal "c" _) rfl ?_).mpr (evalExp_callE_iff.1 hv₂)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)
  · rintro ⟨c₁, sh, c, rfl, happ⟩
    refine ⟨((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh" sh).bindVal "c" c,
      ((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh" sh).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_caseVarPat_iff (by simp)).2 ⟨sh, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_litVarPat_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "sh" sh).bindVal "c" c) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)

/-- `Step_pure/vcvtop` (`4.3:519`): the instruction carries `(sh_2, sh_1)` —
target shape first — while `$vcvtop__` takes them the other way round.  The
characterisation keeps both orders exactly as the pin has them. -/
theorem ruleFires_vcvtop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vcvtopRule ↔
      ∃ c₁ sh₂ sh₁ op c,
        v = Execution.stepV [vconstV c₁, vcvtopV sh₂ sh₁ op] [vconstV c] ∧
        Applies env "vcvtop__" [.val sh₁, .val sh₂, .val op, .val c₁] c := by
  unfold vcvtopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vop3_iff (by simp) (fun _ => by simp) (fun _ _ => by simp)] at h2
    obtain ⟨sh₂, sh₁, op, rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    refine ⟨c₁, sh₂, sh₁, op, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh_2"
      sh₂).bindVal "sh_1" sh₁).bindVal "vcvtop" op).bindVal "c" _) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, sh₂, sh₁, op, c, rfl, happ⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh_2" sh₂).bindVal "sh_1"
        sh₁).bindVal "vcvtop" op).bindVal "c" c,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh_2" sh₂).bindVal "sh_1"
        sh₁).bindVal "vcvtop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vop3_iff (by simp) (fun _ => by simp)
            (fun _ _ => by simp)).2 ⟨sh₂, sh₁, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "sh_2" sh₂).bindVal "sh_1" sh₁).bindVal "vcvtop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)


/-! ## The extended operators

`vextunop`, `vextbinop` and `vextternop` state their premise the other way
round — `$vextunop__(…) = c` rather than `c = $…` — which changes nothing
semantically, `cmpValues` being symmetric at `=`, but does change which side of
the `CmpE` the characterisation reads. -/

/-- `(VEXTUNOP sh_2 sh_1 op)`. -/
def vextunopV (sh₂ sh₁ op : Value) : Value := .case "VEXTUNOP" (.tuple [sh₂, sh₁, op])

/-- `(VEXTBINOP sh_2 sh_1 op)`. -/
def vextbinopV (sh₂ sh₁ op : Value) : Value := .case "VEXTBINOP" (.tuple [sh₂, sh₁, op])

/-- `(VEXTTERNOP sh_2 sh_1 op)`. -/
def vextternopV (sh₂ sh₁ op : Value) : Value :=
  .case "VEXTTERNOP" (.tuple [sh₂, sh₁, op])

/-- `(VNARROW sh_2 sh_1 sx)`. -/
def vnarrowV (sh₂ sh₁ sx : Value) : Value := .case "VNARROW" (.tuple [sh₂, sh₁, sx])

/-- `Step_pure/vextunop` (`4.3:499`). -/
theorem ruleFires_vextunop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vextunopRule ↔
      ∃ c₁ sh₂ sh₁ op c,
        v = Execution.stepV [vconstV c₁, vextunopV sh₂ sh₁ op] [vconstV c] ∧
        Applies env "vextunop__" [.val sh₁, .val sh₂, .val op, .val c₁] c := by
  unfold vextunopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vop3_iff (by simp) (fun _ => by simp) (fun _ _ => by simp)] at h2
    obtain ⟨sh₂, sh₁, op, rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₂
    simp at hv₂
    subst hv₂
    refine ⟨c₁, sh₂, sh₁, op, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh_2"
      sh₂).bindVal "sh_1" sh₁).bindVal "vextunop" op).bindVal "c" _) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₁)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, sh₂, sh₁, op, c, rfl, happ⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh_2" sh₂).bindVal "sh_1"
        sh₁).bindVal "vextunop" op).bindVal "c" c,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "sh_2" sh₂).bindVal "sh_1"
        sh₁).bindVal "vextunop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vop3_iff (by simp) (fun _ => by simp)
            (fun _ _ => by simp)).2 ⟨sh₂, sh₁, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, ?_, evalExp_varE_iff.2 (by simp),
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "sh_2" sh₂).bindVal "sh_1" sh₁).bindVal "vextunop" op).bindVal "c" c)
      rfl ?_).mp happ)
    exact ExecNumeric.evalArgs_four (by simp) (by simp) (by simp) (by simp)

/-- `Step_pure/vextbinop` (`4.3:503`). -/
theorem ruleFires_vextbinop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vextbinopRule ↔
      ∃ c₁ c₂ sh₂ sh₁ op c,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vextbinopV sh₂ sh₁ op] [vconstV c] ∧
        Applies env "vextbinop__" [.val sh₁, .val sh₂, .val op, .val c₁, .val c₂] c := by
  unfold vextbinopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vop3_iff (by simp) (fun _ => by simp) (fun _ _ => by simp)] at h3
    obtain ⟨sh₂, sh₁, op, rfl, rfl⟩ := h3
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₂
    simp at hv₂
    subst hv₂
    refine ⟨c₁, c₂, sh₂, sh₁, op, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "sh_2" sh₂).bindVal "sh_1" sh₁).bindVal "vextbinop" op).bindVal "c" _)
      rfl ?_).mpr (evalExp_callE_iff.1 hv₁)
    exact evalArgs_five (evalExp_varE_iff.2 (by simp)) (by simp) (by simp) (by simp)
      (by simp)
  · rintro ⟨c₁, c₂, sh₂, sh₁, op, c, rfl, happ⟩
    refine ⟨(((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh_2"
        sh₂).bindVal "sh_1" sh₁).bindVal "vextbinop" op).bindVal "c" c,
      (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh_2"
        sh₂).bindVal "sh_1" sh₁).bindVal "vextbinop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vop3_iff (by simp) (fun _ => by simp)
            (fun _ _ => by simp)).2 ⟨sh₂, sh₁, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, ?_, evalExp_varE_iff.2 (by simp),
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "sh_2" sh₂).bindVal "sh_1" sh₁).bindVal "vextbinop"
      op).bindVal "c" c) rfl ?_).mp happ)
    exact evalArgs_five (evalExp_varE_iff.2 (by simp)) (by simp) (by simp) (by simp)
      (by simp)

/-- `Step_pure/vextternop` (`4.3:507`). -/
theorem ruleFires_vextternop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vextternopRule ↔
      ∃ c₁ c₂ c₃ sh₂ sh₁ op c,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vconstV c₃, vextternopV sh₂ sh₁ op]
          [vconstV c] ∧
        Applies env "vextternop__"
          [.val sh₁, .val sh₂, .val op, .val c₁, .val c₂, .val c₃] c := by
  unfold vextternopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, s, τ₁, τ₂, τ₃, rfl, h1, h2, h3, h4⟩ := matchExps_four_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vconstFresh_iff (by simp)] at h3
    obtain ⟨c₃, rfl, rfl⟩ := h3
    rw [matchExp_vop3_iff (by simp) (fun _ => by simp) (fun _ _ => by simp)] at h4
    obtain ⟨sh₂, sh₁, op, rfl, rfl⟩ := h4
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₂
    simp at hv₂
    subst hv₂
    refine ⟨c₁, c₂, c₃, sh₂, sh₁, op, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "c_3" c₃).bindVal "sh_2" sh₂).bindVal "sh_1" sh₁).bindVal "vextternop"
      op).bindVal "c" _) rfl ?_).mpr (evalExp_callE_iff.1 hv₁)
    exact evalArgs_six (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨c₁, c₂, c₃, sh₂, sh₁, op, c, rfl, happ⟩
    refine ⟨((((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "c_3"
        c₃).bindVal "sh_2" sh₂).bindVal "sh_1" sh₁).bindVal "vextternop" op).bindVal "c" c,
      ((((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "c_3"
        c₃).bindVal "sh_2" sh₂).bindVal "sh_1" sh₁).bindVal "vextternop" op).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₃, rfl, rfl⟩,
          (matchExp_vop3_iff (by simp) (fun _ => by simp)
            (fun _ _ => by simp)).2 ⟨sh₂, sh₁, op, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, ?_, evalExp_varE_iff.2 (by simp),
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "c_3" c₃).bindVal "sh_2" sh₂).bindVal "sh_1"
      sh₁).bindVal "vextternop" op).bindVal "c" c) rfl ?_).mp happ)
    exact evalArgs_six (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)


/-! ## Two more inversions

`vvtestop` and `vnarrow` pass something other than a variable to their
operator — a nested call in the first case, a projection out of a `%`
injection in the second — so their argument lists have to be inverted rather
than supplied. -/

/-- An expression-argument list is evaluated head-first.  This is
`ExecRead.evalArgs_expA_cons_iff`, which lives downstream of this file. -/
theorem evalArgs_expA_cons_iff {env : Env} {ρ : VarEnv} {e : Exp} {rest : List Arg}
    {ws : List ArgV} :
    EvalArgs env ρ (.expA e :: rest) ws ↔
      ∃ u ws', ws = .val u :: ws' ∧ EvalExp env ρ e u ∧ EvalArgs env ρ rest ws' := by
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
            obtain ⟨u, hu, rfl⟩ := hw
            exact ⟨u, ws', rfl, ⟨k, hu⟩, ⟨k + 2, by simpa only [evalArgs] using hws⟩⟩
  · rintro ⟨u, ws', rfl, hu, hws⟩
    exact evalArgs_cons hu hws

/-- `x!`%`.0` where `x` is bound to a `%`-injection: the projection reads the
first component and says nothing about the rest.  `ishape` and `bshape` are
exactly such injections — single-case variants over `shape` — so `vnarrow`'s
`sh_1!`%`.0` is how the pin spells "the shape underneath". -/
theorem evalExp_pctFst_iff {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value} :
    EvalExp env ρ (.projE (.uncaseE (.varE x) "%") 0) v ↔
      ∃ rest : List Value, ρ.findVal? x = some (.case "%" (.tuple (v :: rest))) := by
  rw [evalExp_projE_iff]
  constructor
  · rintro ⟨vs, hvs, -, hidx⟩
    rw [evalExp_uncaseE_iff, evalExp_varE_iff] at hvs
    cases vs with
    | nil => simp at hidx
    | cons w rest =>
        simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hidx
        subst hidx
        exact ⟨rest, hvs⟩
  · rintro ⟨rest, h⟩
    exact ⟨v :: rest, evalExp_uncaseE_iff.2 (evalExp_varE_iff.2 h), by omega, by simp⟩

/-- `(OP ty op)` with *both* components literal nullary injections — the shape
`VVTESTOP (V128 ANY_TRUE)` has, `ANY_TRUE` being the only `vvtestop` there
is. -/
theorem matchExp_lit2Pat_iff {env : Env} {ρ ρ' : VarEnv} {mo ty op : MixopS}
    {v : Value} :
    MatchExp env ρ (.caseE mo (.tupE [.caseE ty (.tupE []), .caseE op (.tupE [])])) v ρ' ↔
      v = .case mo (.tuple [caseNilV ty, caseNilV op]) ∧ ρ' = ρ := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨tv, ov, υ, rfl, htv, hov⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_caseNil_iff] at hov
    obtain ⟨rfl, rfl⟩ := hov
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩

/-- `(VVTESTOP V128 ANY_TRUE)`. -/
def vvtestopV : Value := .case "VVTESTOP" (.tuple [v128V, caseNilV "ANY_TRUE"])

/-- `Step_pure/vvtestop` (`4.3:447`): `ANY_TRUE` is a literal in the pinned
conclusion, not a variable, so the rule applies to that one operator only.  Its
premise nests two calls, `$inez_($vsize(V128), c_1)`, and both stay abstract. -/
theorem ruleFires_vvtestop_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vvtestopRule ↔
      ∃ c₁ s c,
        v = Execution.stepV [vconstV c₁, vvtestopV] [Execution.constV Execution.i32V c] ∧
        Applies env "vsize" [.val v128V] s ∧
        Applies env "inez_" [.val s, .val c₁] c := by
  unfold vvtestopRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_lit2Pat_iff] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_litVarPat_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    obtain ⟨ws, ps, t, cs, hargs, -, -⟩ :=
      ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hv₂)
    obtain ⟨s, ws₁, rfl, hs, h₁⟩ := evalArgs_expA_cons_iff.1 hargs
    obtain ⟨u, ws₂, rfl, hu, h₂⟩ := evalArgs_expA_cons_iff.1 h₁
    rw [evalExp_varE_iff] at hu
    simp at hu
    subst hu
    refine ⟨c₁, s, _, rfl, ?_, ?_⟩
    · exact (applies_iff_callDef (ρ := (VarEnv.empty.bindVal "c_1" c₁).bindVal "c" _)
        rfl (evalArgs_cons evalExp_v128 evalArgs_nil)).mpr (evalExp_callE_iff.1 hs)
    · exact (applies_iff_callDef (ρ := (VarEnv.empty.bindVal "c_1" c₁).bindVal "c" _)
        rfl (evalArgs_cons hs
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))).mpr
        (evalExp_callE_iff.1 hv₂)
  · rintro ⟨c₁, s, c, rfl, hsize, hinez⟩
    have hs : EvalExp env ((VarEnv.empty.bindVal "c_1" c₁).bindVal "c" c)
        (.callE "vsize" [.expA (.caseE "V128" (.tupE []))]) s :=
      evalExp_callE_iff.2 ((applies_iff_callDef
        (ρ := (VarEnv.empty.bindVal "c_1" c₁).bindVal "c" c) rfl
        (evalArgs_cons evalExp_v128 evalArgs_nil)).mp hsize)
    refine ⟨(VarEnv.empty.bindVal "c_1" c₁).bindVal "c" c,
      (VarEnv.empty.bindVal "c_1" c₁).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          matchExp_lit2Pat_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_litVarPat_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    exact evalExp_callE_iff.2 ((applies_iff_callDef
      (ρ := (VarEnv.empty.bindVal "c_1" c₁).bindVal "c" c) rfl
      (evalArgs_cons hs (evalArgs_cons (evalExp_varE_iff.2 (by simp))
        evalArgs_nil))).mp hinez)

/-- `Step_pure/vnarrow` (`4.3:511`).  `$vnarrowop__` is applied not to the two
shapes the instruction carries but to `sh_1!`%`.0` and `sh_2!`%`.0`: an
`ishape` is a one-case variant over `shape`, and the premise strips that
injection.  The characterisation says so — the rule fires exactly when both
shapes are `%`-injections of a tuple, and it is the *heads* of those tuples the
operator sees. -/
theorem ruleFires_vnarrow_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vnarrowRule ↔
      ∃ c₁ c₂ t₂ r₂ t₁ r₁ sx c,
        v = Execution.stepV [vconstV c₁, vconstV c₂,
            vnarrowV (.case "%" (.tuple (t₂ :: r₂))) (.case "%" (.tuple (t₁ :: r₁))) sx]
          [vconstV c] ∧
        Applies env "vnarrowop__" [.val t₁, .val t₂, .val sx, .val c₁, .val c₂] c := by
  unfold vnarrowRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    rw [matchExp_vop3_iff (by simp) (fun _ => by simp) (fun _ _ => by simp)] at h3
    obtain ⟨sh₂, sh₁, sx, rfl, rfl⟩ := h3
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    obtain ⟨ws, ps, t, cs, hargs, -, -⟩ :=
      ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hv₂)
    obtain ⟨t₁, ws₁, rfl, ht₁, g₁⟩ := evalArgs_expA_cons_iff.1 hargs
    obtain ⟨t₂, ws₂, rfl, ht₂, -⟩ := evalArgs_expA_cons_iff.1 g₁
    rw [evalExp_pctFst_iff] at ht₁ ht₂
    obtain ⟨r₁, hr₁⟩ := ht₁
    obtain ⟨r₂, hr₂⟩ := ht₂
    simp at hr₁ hr₂
    subst hr₁
    subst hr₂
    refine ⟨c₁, c₂, t₂, r₂, t₁, r₁, sx, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "sh_2" (.case "%" (.tuple (t₂ :: r₂)))).bindVal "sh_1"
      (.case "%" (.tuple (t₁ :: r₁)))).bindVal "sx" sx).bindVal "c" _) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact evalArgs_cons (evalExp_pctFst_iff.2 ⟨r₁, by simp⟩)
      (evalArgs_cons (evalExp_pctFst_iff.2 ⟨r₂, by simp⟩)
        (evalArgs_cons (evalExp_varE_iff.2 (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp))
            (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))))
  · rintro ⟨c₁, c₂, t₂, r₂, t₁, r₁, sx, c, rfl, happ⟩
    refine ⟨(((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh_2"
        (.case "%" (.tuple (t₂ :: r₂)))).bindVal "sh_1"
        (.case "%" (.tuple (t₁ :: r₁)))).bindVal "sx" sx).bindVal "c" c,
      (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh_2"
        (.case "%" (.tuple (t₂ :: r₂)))).bindVal "sh_1"
        (.case "%" (.tuple (t₁ :: r₁)))).bindVal "sx" sx).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          (matchExp_vop3_iff (by simp) (fun _ => by simp) (fun _ _ => by simp)).2
            ⟨_, _, _, rfl, rfl⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "sh_2" (.case "%" (.tuple (t₂ :: r₂)))).bindVal "sh_1"
      (.case "%" (.tuple (t₁ :: r₁)))).bindVal "sx" sx).bindVal "c" c) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_pctFst_iff.2 ⟨r₁, by simp⟩)
      (evalArgs_cons (evalExp_pctFst_iff.2 ⟨r₂, by simp⟩)
        (evalArgs_cons (evalExp_varE_iff.2 (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp))
            (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))))


/-! ## The lane instructions

`vshuffle`, `vextract_lane` and `vreplace_lane` reach inside the vector: they
mention a shape `(lt X M)`, a lane index `i` and, in `vshuffle`'s case, a whole
iteration of them.  None of that forces any of `$lanes_`, `$inv_lanes_` or
`$vshufflop_` to be unfolded. -/

/-- `(lt X M)`, the shape injection. -/
def shapeV (lt m : Value) : Value := .case "%X%" (.tuple [lt, m])

/-- `(VSHUFFLE sh i*)`. -/
def vshuffleV (sh ids : Value) : Value := .case "VSHUFFLE" (.tuple [sh, ids])

/-- `(VEXTRACT_LANE sh sx? i)`. -/
def vextractLaneV (sh o i : Value) : Value :=
  .case "VEXTRACT_LANE" (.tuple [sh, o, i])

/-- `(lt X M)` as a pattern, with the lane type under a subtype coercion —
which matching is transparent to. -/
theorem matchExp_shapeSubPat_iff {env : Env} {ρ ρ' : VarEnv} {x y : IL.Id}
    {t₁ t₂ : Typ} {v : Value} (hx : ρ.findVal? x = none)
    (hy : ∀ w, (ρ.bindVal x w).findVal? y = none) :
    MatchExp env ρ (.caseE "%X%" (.tupE [.subE (.varE x) t₁ t₂, .varE y])) v ρ' ↔
      ∃ lt m, v = shapeV lt m ∧ ρ' = (ρ.bindVal x lt).bindVal y m := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨lt, m, σ, rfl, hlt, hm⟩ := matchExps_two_iff.1 hws
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff hx] at hlt
    subst hlt
    rw [matchExp_freshVar_iff (hy lt)] at hm
    exact ⟨lt, m, rfl, hm⟩
  · rintro ⟨lt, m, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff hx).2 rfl),
        (matchExp_freshVar_iff (hy lt)).2 rfl⟩⟩⟩

/-- …and the same expression, evaluated. -/
theorem evalExp_shapeSub {env : Env} {ρ : VarEnv} {x y : IL.Id} {t₁ t₂ : Typ}
    {lt m : Value} (hx : ρ.findVal? x = some lt) (hy : ρ.findVal? y = some m) :
    EvalExp env ρ (.caseE "%X%" (.tupE [.subE (.varE x) t₁ t₂, .varE y])) (shapeV lt m) :=
  evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[lt, m],
    Validation.evalExps_cons_iff.2 ⟨lt, [m], rfl,
      evalExp_subE_iff.2 (evalExp_varE_iff.2 hx),
      Validation.evalExps_cons_iff.2 ⟨m, [], rfl, evalExp_varE_iff.2 hy,
        Validation.evalExps_nil_iff.2 rfl⟩⟩, rfl⟩, rfl⟩

/-- `Step_pure/vshuffle` (`4.3:491`): the lane permutation.  Its immediate is an
iteration `i*` over an *unbound* domain, so matching binds the whole list and
the premise passes it on; `$vshufflop_` stays abstract. -/
theorem ruleFires_vshuffle_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vshuffleRule ↔
      ∃ c₁ c₂ sh ids c,
        v = Execution.stepV [vconstV c₁, vconstV c₂, vshuffleV sh (.list ids)]
          [vconstV c] ∧
        Applies env "vshufflop_" [.val sh, .val (.list ids), .val c₁, .val c₂] c := by
  unfold vshuffleRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, h3⟩ := matchExps_three_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    rw [matchExp_vconstFresh_iff (by simp)] at h2
    obtain ⟨c₂, rfl, rfl⟩ := h2
    obtain ⟨sv, rfl, hsv⟩ := Validation.matchExp_case_iff.1 h3
    obtain ⟨svs, rfl, hsvs⟩ := Validation.matchExp_tup_iff.1 hsv
    obtain ⟨sh, idv, υ, rfl, hsh, hid⟩ := matchExps_two_iff.1 hsvs
    rw [matchExp_freshVar_iff (by simp)] at hsh
    subst hsh
    rw [matchExp_iterE_list_iff (bindsVar_varE "i") (by simp) (by decide)] at hid
    obtain ⟨ids, rfl, hids⟩ := hid
    rw [matchExp_freshVar_iff (by simp)] at hids
    subst hids
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_vconstFresh_iff (by simp)] at hrv
    obtain ⟨c, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    refine ⟨c₁, c₂, sh, ids, _, rfl, ?_⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2"
      c₂).bindVal "sh" sh).bindVal "i*" (.list ids)).bindVal "c" _) rfl ?_).mpr
      (evalExp_callE_iff.1 hv₂)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_iterPat (by decide) (by simp))
        (evalArgs_cons (evalExp_varE_iff.2 (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)))
  · rintro ⟨c₁, c₂, sh, ids, c, rfl, happ⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh"
        sh).bindVal "i*" (.list ids)).bindVal "c" c,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "c_2" c₂).bindVal "sh"
        sh).bindVal "i*" (.list ids)).bindVal "c" c,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₂, rfl, rfl⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_freshVar_iff (by simp)).2 rfl,
                (matchExp_iterE_list_iff (bindsVar_varE "i") (by simp) (by decide)).2
                  ⟨ids, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c, c, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "c_2" c₂).bindVal "sh" sh).bindVal "i*" (.list ids)).bindVal "c" c)
      rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
      (evalArgs_cons (evalExp_iterPat (by decide) (by simp))
        (evalArgs_cons (evalExp_varE_iff.2 (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)))

/-- `Step_pure/vextract_lane-num` (`4.3:515`): the unpacked lane read.  The
instruction's `sx?` is the literal empty option, and the index is a `%`
injection whose head is the lane number. -/
theorem ruleFires_vextractLaneNum_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vextractLaneNumRule ↔
      ∃ c₁ nt m k rest lanes c₂,
        v = Execution.stepV [vconstV c₁,
            vextractLaneV (shapeV nt m) (.opt none)
              (.case "%" (.tuple (.num (.natN k) :: rest)))]
          [Execution.constV nt c₂] ∧
        Applies env "lanes_" [.val (shapeV nt m), .val c₁] lanes ∧
        lanes.idx? k = some c₂ := by
  unfold vextractLaneNumRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨shv, ov, iv, υ₁, υ₂, rfl, hsh, ho, hi⟩ := matchExps_three_iff.1 hqvs
    rw [matchExp_shapeSubPat_iff (by simp) (fun _ => by simp)] at hsh
    obtain ⟨nt, m, rfl, rfl⟩ := hsh
    rw [Validation.matchExp_optNone_iff] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    obtain ⟨rv, rfl, hrvv⟩ := Validation.matchExp_case_iff.1 hrv
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrvv
    obtain ⟨ntv, c₂, υ, rfl, hnt, hc₂⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    rw [matchExp_freshVar_iff (by simp)] at hc₂
    subst hc₂
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    obtain ⟨lanes, k, hlanes, hk, hidx⟩ := evalExp_idxE_iff.1 hv₂
    rw [evalExp_pctFst_iff] at hk
    obtain ⟨rest, hrest'⟩ := hk
    simp at hrest'
    subst hrest'
    refine ⟨c₁, ntv, m, k, rest, lanes, _, rfl, ?_, hidx⟩
    refine (applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "nt"
      ntv).bindVal "M" m).bindVal "i" (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal
      "c_2" _) rfl ?_).mpr (evalExp_callE_iff.1 hlanes)
    exact evalArgs_cons (evalExp_shapeSub (by simp) (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)
  · rintro ⟨c₁, nt, m, k, rest, lanes, c₂, rfl, happ, hidx⟩
    refine ⟨((((VarEnv.empty.bindVal "c_1" c₁).bindVal "nt" nt).bindVal "M" m).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" c₂,
      ((((VarEnv.empty.bindVal "c_1" c₁).bindVal "nt" nt).bindVal "M" m).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" c₂,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                (matchExp_shapeSubPat_iff (by simp) (fun _ => by simp)).2
                  ⟨nt, m, rfl, rfl⟩,
                Validation.matchExp_optNone_iff.2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_two_iff.2 ⟨_, _, _, rfl,
                (matchExp_boundVar_iff (by simp)).2 ⟨rfl, rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c₂, c₂, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    refine evalExp_idxE_iff.2 ⟨lanes, k, ?_, evalExp_pctFst_iff.2 ⟨rest, by simp⟩, hidx⟩
    refine evalExp_callE_iff.2 ((applies_iff_callDef (ρ := ((((VarEnv.empty.bindVal "c_1"
      c₁).bindVal "nt" nt).bindVal "M" m).bindVal "i"
      (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" c₂) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_shapeSub (by simp) (by simp))
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)


/-- `Step_pure/vextract_lane-pack` (`4.3:515`): the packed lane read.  Three
calls nest in the one premise — `$psize`, `$lanes_` and `$extend__` — and the
characterisation names each of their results without computing any of them. -/
theorem ruleFires_vextractLanePack_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vextractLanePackRule ↔
      ∃ c₁ pt m sx k rest ps lanes lane c₂,
        v = Execution.stepV [vconstV c₁,
            vextractLaneV (shapeV pt m) (.opt (some sx))
              (.case "%" (.tuple (.num (.natN k) :: rest)))]
          [Execution.constV Execution.i32V c₂] ∧
        Applies env "psize" [.val pt] ps ∧
        Applies env "lanes_" [.val (shapeV pt m), .val c₁] lanes ∧
        lanes.idx? k = some lane ∧
        Applies env "extend__"
          [.val ps, .val (.num (.natN 32)), .val sx, .val lane] c₂ := by
  unfold vextractLanePackRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
    obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
    obtain ⟨p, q, τ, rfl, h1, h2⟩ := matchExps_two_iff.1 has
    rw [matchExp_vconstFresh_iff (by simp)] at h1
    obtain ⟨c₁, rfl, rfl⟩ := h1
    obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
    obtain ⟨shv, ov, iv, υ₁, υ₂, rfl, hsh, ho, hi⟩ := matchExps_three_iff.1 hqvs
    rw [matchExp_shapeSubPat_iff (by simp) (fun _ => by simp)] at hsh
    obtain ⟨pt, m, rfl, rfl⟩ := hsh
    rw [Validation.matchExp_optSome_iff] at ho
    obtain ⟨sx, rfl, hsx⟩ := ho
    rw [matchExp_freshVar_iff (by simp)] at hsx
    subst hsx
    rw [matchExp_freshVar_iff (by simp)] at hi
    subst hi
    obtain ⟨bvs, rfl, hbs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨rr, rfl, hrv⟩ := matchExps_one_iff.1 hbs
    rw [matchExp_litVarPat_iff (by simp)] at hrv
    obtain ⟨c₂, rfl, rfl⟩ := hrv
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨v₁, v₂, hv₁, hv₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_varE_iff] at hv₁
    simp at hv₁
    subst hv₁
    obtain ⟨ws, pps, t, cs, hargs, -, -⟩ :=
      ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hv₂)
    obtain ⟨ps, ws₁, rfl, hps, g₁⟩ := evalArgs_expA_cons_iff.1 hargs
    obtain ⟨n32, ws₂, rfl, hn32, g₂⟩ := evalArgs_expA_cons_iff.1 g₁
    obtain ⟨sxv, ws₃, rfl, hsxv, g₃⟩ := evalArgs_expA_cons_iff.1 g₂
    obtain ⟨lane, ws₄, rfl, hlane, -⟩ := evalArgs_expA_cons_iff.1 g₃
    rw [evalExp_numE_iff] at hn32
    subst hn32
    rw [evalExp_varE_iff] at hsxv
    simp at hsxv
    subst hsxv
    obtain ⟨lanes, k, hlanes, hk, hidx⟩ := evalExp_idxE_iff.1 hlane
    rw [evalExp_pctFst_iff] at hk
    obtain ⟨rest, hrest'⟩ := hk
    simp at hrest'
    subst hrest'
    refine ⟨c₁, pt, m, _, k, rest, ps, lanes, lane, _, rfl, ?_, ?_, hidx, ?_⟩
    · exact (applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "pt"
        pt).bindVal "M" m).bindVal "sx" _).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" _) rfl
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mpr
        (evalExp_callE_iff.1 hps)
    · exact (applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "pt"
        pt).bindVal "M" m).bindVal "sx" _).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" _) rfl
        (evalArgs_cons (evalExp_shapeSub (by simp) (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))).mpr
        (evalExp_callE_iff.1 hlanes)
    · exact (applies_iff_callDef (ρ := (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "pt"
        pt).bindVal "M" m).bindVal "sx" _).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" _) rfl
        (evalArgs_cons hps (evalArgs_cons (evalExp_numE_iff.2 rfl)
          (evalArgs_cons (evalExp_varE_iff.2 (by simp))
            (evalArgs_cons hlane evalArgs_nil))))).mpr (evalExp_callE_iff.1 hv₂)
  · rintro ⟨c₁, pt, m, sx, k, rest, ps, lanes, lane, c₂, rfl, hps, hlanes, hidx, hext⟩
    have hpsE : EvalExp env ((((((VarEnv.empty.bindVal "c_1" c₁).bindVal "pt"
        pt).bindVal "M" m).bindVal "sx" sx).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" c₂)
        (.callE "psize" [.expA (.varE "pt")]) ps :=
      evalExp_callE_iff.2 ((applies_iff_callDef rfl
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).mp hps)
    have hlanesE : EvalExp env ((((((VarEnv.empty.bindVal "c_1" c₁).bindVal "pt"
        pt).bindVal "M" m).bindVal "sx" sx).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" c₂)
        (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.subE (.varE "pt")
          (.varT "packtype" []) (.varT "lanetype" []), .varE "M"])),
          .expA (.varE "c_1")]) lanes :=
      evalExp_callE_iff.2 ((applies_iff_callDef rfl
        (evalArgs_cons (evalExp_shapeSub (by simp) (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))).mp hlanes)
    have hlaneE : EvalExp env ((((((VarEnv.empty.bindVal "c_1" c₁).bindVal "pt"
        pt).bindVal "M" m).bindVal "sx" sx).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" c₂)
        (.idxE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.subE (.varE "pt")
          (.varT "packtype" []) (.varT "lanetype" []), .varE "M"])),
          .expA (.varE "c_1")]) (.projE (.uncaseE (.varE "i") "%") 0)) lane :=
      evalExp_idxE_iff.2 ⟨lanes, k, hlanesE,
        evalExp_pctFst_iff.2 ⟨rest, by simp⟩, hidx⟩
    refine ⟨(((((VarEnv.empty.bindVal "c_1" c₁).bindVal "pt" pt).bindVal "M"
        m).bindVal "sx" sx).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" c₂,
      (((((VarEnv.empty.bindVal "c_1" c₁).bindVal "pt" pt).bindVal "M"
        m).bindVal "sx" sx).bindVal "i"
        (.case "%" (.tuple (.num (.natN k) :: rest)))).bindVal "c_2" c₂,
      matchExp_concl_iff.2 ⟨_, _, _, rfl,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_vconstFresh_iff (by simp)).2 ⟨c₁, rfl, rfl⟩,
          Validation.matchExp_case_iff.2 ⟨_, rfl,
            Validation.matchExp_tup_iff.2 ⟨_, rfl,
              matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                (matchExp_shapeSubPat_iff (by simp) (fun _ => by simp)).2
                  ⟨pt, m, rfl, rfl⟩,
                Validation.matchExp_optSome_iff.2
                  ⟨sx, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩,
                (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl,
          (matchExp_litVarPat_iff (by simp)).2 ⟨c₂, rfl, rfl⟩⟩⟩⟩, ?_⟩
    refine Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
      Validation.premsHold_nil_iff.2 rfl⟩
    refine evalExp_cmpE_iff.2 ⟨c₂, c₂, evalExp_varE_iff.2 (by simp), ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    exact evalExp_callE_iff.2 ((applies_iff_callDef rfl
      (evalArgs_cons hpsE (evalArgs_cons (evalExp_numE_iff.2 rfl)
        (evalArgs_cons (evalExp_varE_iff.2 (by simp))
          (evalArgs_cons hlaneE evalArgs_nil))))).mp hext)

/-! ## The two rules whose left-hand side evaluates an unbound variable

`vsplat` and `vreplace_lane` are the vector block's share of the phenomenon
`Equiv/ExecStepRules.lean` records for ten rules of `Step`: the pinned IL puts a
`CallE` in a *pattern* position, and `matchExp` at a `CallE` is the default
match — it **evaluates** the call and compares.  Both call `$lunpack(Lnn)`, and
in both the binding occurrence of `Lnn` comes later in the same pattern, so at
the moment the call is evaluated `Lnn` is unbound and evaluation is `undef`.

In the W3C document these rules read `(CONST $lunpack(Lnn) c_1) (VSPLAT (Lnn X
M))`, and `Lnn` is determined by the instruction, not by the operand's type;
the frontend's `il2al` pass reorders the two so that the instruction is read
first.  The pinned `--ast` stream keeps the source order, and the direct IL
semantics cannot run it. -/

/-- A one-argument `CallE` whose argument is unbound matches nothing.  This is
`ExecStepRules.not_matchExp_callE_of_argUnevaluable` at `pre = []`, which lives
downstream of this file. -/
theorem not_matchExp_callE1_of_unbound {env : Env} {ρ ρ' : VarEnv} {f y : IL.Id}
    {w : Value} (hy : ρ.findVal? y = none) :
    ¬ MatchExp env ρ (.callE f [.expA (.varE y)]) w ρ' := by
  intro h
  rw [ExecDefault.matchExp_callE_iff] at h
  obtain ⟨hcall, rfl⟩ := h
  rw [ExecNumeric.callDef_iff] at hcall
  obtain ⟨ws, ps, t, cs, hargs, -, -⟩ := hcall
  obtain ⟨u, -, -, hu, -⟩ := evalArgs_expA_cons_iff.1 hargs
  rw [evalExp_varE_iff, hy] at hu
  simp at hu

/-- **`Step_pure/vsplat` cannot fire at the pin.**  Its first operand pattern is
`(CONST $lunpack(Lnn) c_1)`, and `Lnn` is bound only by the *second* operand,
`(VSPLAT (Lnn X M))`. -/
theorem not_ruleFires_vsplat_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v vsplatRule := by
  unfold vsplatRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, -⟩ := matchExp_concl_iff.1 hm
  obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
  obtain ⟨p, q, τ, rfl, h1, -⟩ := matchExps_two_iff.1 has
  obtain ⟨pv, rfl, hpv⟩ := Validation.matchExp_case_iff.1 h1
  obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_tup_iff.1 hpv
  obtain ⟨lv, cv, υ, rfl, hlv, -⟩ := matchExps_two_iff.1 hpvs
  exact not_matchExp_callE1_of_unbound (by simp) hlv

/-- **`Step_pure/vreplace_lane` cannot fire at the pin**, for the same reason:
its *second* operand is `(CONST $lunpack(Lnn) c_2)` and `Lnn` is bound by the
third, `(VREPLACE_LANE ((Lnn X M), i))`. -/
theorem not_ruleFires_vreplaceLane_pinned {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v vreplaceLaneRule := by
  unfold vreplaceLaneRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨a, b, σ, rfl, hl, -⟩ := matchExp_concl_iff.1 hm
  obtain ⟨avs, rfl, has⟩ := Validation.matchExp_list_iff.1 hl
  obtain ⟨p, q, r, τ, τ₂, rfl, h1, h2, -⟩ := matchExps_three_iff.1 has
  rw [matchExp_vconstFresh_iff (by simp)] at h1
  obtain ⟨c₁, rfl, rfl⟩ := h1
  obtain ⟨qv, rfl, hqv⟩ := Validation.matchExp_case_iff.1 h2
  obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_tup_iff.1 hqv
  obtain ⟨lv, cv, υ, rfl, hlv, -⟩ := matchExps_two_iff.1 hqvs
  exact not_matchExp_callE1_of_unbound (by simp) hlv


end Silmaril.SpecTec.Equiv.ExecVector
