module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneFOp

/-!
# The vector operator rules of the 2.0 `Step_pure` (verbatim)

`vunop` (rule 34), `vbinop-val` (rule 36) and `vrelop` (rule 40).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- `vec_(V128)`. -/
abbrev vecT : Typ := .varT "vec_" [.expA (.caseE "V128" (.tupE []))]

/-- `VCONST V128 x`. -/
abbrev vconstE (x : IL.Id) : Exp := .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE x])

/-- `Step_pure/vunop`, rule 34 (verbatim). -/
def vunopRule : Rule :=
  .ruleD "vunop" [.expP "c_1" vecT, .expP "sh" (.varT "shape" []),
    .expP "vunop" (.varT "vunop_" [.expA (.varE "sh")]), .expP "c" vecT] "%~>%"
    (.tupE [.listE [vconstE "c_1", .caseE "VUNOP" (.tupE [.varE "sh", .varE "vunop"])],
      .listE [vconstE "c"]])
    [.ifPr (.memE (.varE "c") (.callE "vunop_" [.expA (.varE "sh"), .expA (.varE "vunop"),
      .expA (.varE "c_1")]))]

/-- `Step_pure/vbinop-val`, rule 36 (verbatim). -/
def vbinopRule : Rule :=
  .ruleD "vbinop-val" [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh" (.varT "shape" []),
    .expP "vbinop" (.varT "vbinop_" [.expA (.varE "sh")]), .expP "c" vecT] "%~>%"
    (.tupE [.listE [vconstE "c_1", vconstE "c_2", .caseE "VBINOP" (.tupE [.varE "sh", .varE "vbinop"])],
      .listE [vconstE "c"]])
    [.ifPr (.memE (.varE "c") (.callE "vbinop_" [.expA (.varE "sh"), .expA (.varE "vbinop"),
      .expA (.varE "c_1"), .expA (.varE "c_2")]))]

/-- `Step_pure/vrelop`, rule 40 (verbatim). -/
def vrelopRule : Rule :=
  .ruleD "vrelop" [.expP "c_1" vecT, .expP "c_2" vecT, .expP "sh" (.varT "shape" []),
    .expP "vrelop" (.varT "vrelop_" [.expA (.varE "sh")]), .expP "c" vecT] "%~>%"
    (.tupE [.listE [vconstE "c_1", vconstE "c_2", .caseE "VRELOP" (.tupE [.varE "sh", .varE "vrelop"])],
      .listE [vconstE "c"]])
    [.ifPr (.cmpE .eqOp .boolT (.callE "vrelop_" [.expA (.varE "sh"), .expA (.varE "vrelop"),
      .expA (.varE "c_1"), .expA (.varE "c_2")]) (.varE "c"))]

open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

set_option maxRecDepth 100000 in
theorem hasRuleAt_vunop20V (B : Builtins) :
    Equiv.Validation.HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 34 vunopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hasRuleAt_vbinop20V (B : Builtins) :
    Equiv.Validation.HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 36 vbinopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hasRuleAt_vrelop20V (B : Builtins) :
    Equiv.Validation.HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 40 vrelopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecLane
