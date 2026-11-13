module

public import Silmaril.Wasm.SpecTec.Institution.Instr30Y.Thms
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Instruction typing of the wasm-3.0 script, conversions (`Instr_ok/cvtop`)

`Instr_ok/cvtop` (rule 87) types `CVTOP(nt_1, nt_2, cvtop)` at `[nt_2] -> [nt_1]`, with `cvtop` of
sort `cvtop__(nt_2, nt_1)`, an operator sort that depends on two number types. Its rule has no
premise; it is located by a kernel `rfl` (`ruleAt_cvtop`).

* The operator sort: round 4's `Floats.typedDep2_cvtop` types every Core `ConvertOp` at
  `cvtop__(nt_1, nt_2)` with `nt_1` the source and `nt_2` the target. The rule names the source
  `nt_2` and the target `nt_1`. `Round5.Pos.hasTyp_varT_transfer` moves the typing across the
  renaming: a named type applied to arguments depends only on their values (`hasTyp_cvtopRule`).
* `dd_convert`: `Instr_ok/cvtop` fires at Core's typing `[op.source] -> [op.target]` of every
  conversion, in every typed context and under every reading of `otherwise`.
* `convert_preserves`, `numericZ_preserves`: with `Instr30Y.numeric_preserves`, every Core typing
  of a numeric instruction (integer and float, conversions included) is an `Instr_ok` fact.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV evalExp_nil)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (itLE evalExp_resLE evalExps_one)

variable {B : Builtins}

/-- `nt_i`, read as a value type. -/
def ntiSubE (x : IL.Id) : Exp := .subE (.varE x) (.varT "numtype" []) (.varT "valtype" [])

/-- `Instr_ok/cvtop`'s operator sort, `cvtop__(nt_2, nt_1)`. -/
abbrev cvtopRuleT : Typ := .varT "cvtop__" [.expA (.varE "nt_2"), .expA (.varE "nt_1")]

/-- `Instr_ok/cvtop` (definition 391, rule 87). -/
def cvtopRule : Rule :=
  .ruleD "cvtop" [ctxP, .expP "nt_1" (.varT "numtype" []), .expP "nt_2" (.varT "numtype" []),
      .expP "cvtop" cvtopRuleT] "%|-%:%"
    (.tupE [.varE "C", .caseE "CVTOP" (.tupE [.varE "nt_1", .varE "nt_2", .varE "cvtop"]),
      itLE [ntiSubE "nt_2"] [ntiSubE "nt_1"]]) []

set_option maxRecDepth 100000 in
/-- **`Instr_ok/cvtop`**, rule 87 of `simEnv B`. -/
theorem ruleAt_cvtop : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 87 cvtopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The scope of `Instr_ok/cvtop` at a conversion `op` in `c`. -/
def cvtσ (c : Value) (op : ConvertOp) : List (IL.Id × Value) :=
  [("C", c), ("nt_1", Vec.numTypeV op.target), ("nt_2", Vec.numTypeV op.source),
    ("cvtop", Vec.cvtOpV op)]

/-- **The operator of a conversion has the rule's sort** `cvtop__(nt_2, nt_1)`, with the source
bound to `nt_2` and the target to `nt_1`. -/
theorem hasTyp_cvtopRule (c : Value) (op : ConvertOp) :
    HasTyp (simEnv B) (VarEnv.empty.bindVals (cvtσ c op)) cvtopRuleT (Vec.cvtOpV op) := by
  let ρ' : VarEnv := VarEnv.empty.bindVals
    [("nt_1", Vec.numTypeV op.source), ("nt_2", Vec.numTypeV op.target)]
  have h : HasTyp (simEnv B) ρ' Vec.cvtopT (Vec.cvtOpV op) :=
    Floats.typedDep2_cvtop op ρ' (valsOnly_bind _) rfl rfl
  have ha : EvalArgs (simEnv B) ρ' [.expA (.varE "nt_1"), .expA (.varE "nt_2")]
      [.val (Vec.numTypeV op.source), .val (Vec.numTypeV op.target)] :=
    Equiv.evalArgs_cons (Sim.evalExp_var rfl) (Equiv.evalArgs_cons (Sim.evalExp_var rfl)
      Equiv.evalArgs_nil)
  have ha' : EvalArgs (simEnv B) (VarEnv.empty.bindVals (cvtσ c op))
      [.expA (.varE "nt_2"), .expA (.varE "nt_1")]
      [.val (Vec.numTypeV op.source), .val (Vec.numTypeV op.target)] :=
    Equiv.evalArgs_cons (Sim.evalExp_var rfl) (Equiv.evalArgs_cons (Sim.evalExp_var rfl)
      Equiv.evalArgs_nil)
  exact Round5.Pos.hasTyp_varT_transfer rfl rfl h ha ha'

/-- The image of a number type, read as a value type. -/
theorem tyV_num (t : NumType) : tyV (.num t) = Vec.numTypeV t := by
  rcases t with t | t <;> cases t <;> rfl

/-- **`Instr_ok/cvtop`** at Core's typing of a conversion, in every typed context. -/
theorem dd_convert (O : ElseI) {c : Value} (hc : CtxT B c) (op : ConvertOp) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.convert op), itV [tyV (.num op.source)] [] [tyV (.num op.target)]]) := by
  rw [tyV_num, tyV_num]
  have hρ := valsOnly_bind (cvtσ c op)
  exact dderivesB_of_ruleAt ruleAt_cvtop (self_mem_conclAlts _) (cvtσ c op)
    (QuantsOk.cons rfl (hc _ hρ) <| QuantsOk.cons rfl (Typing.hasTyp_numtype hρ _) <|
      QuantsOk.cons rfl (Typing.hasTyp_numtype hρ _) <|
      QuantsOk.cons rfl (hasTyp_cvtopRule c op) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl)
      (evalExp_case (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
        (Sim.evalExp_var rfl)))
      (evalExp_case (evalExp_tup3 (evalExp_resLE (evalExps_one (evalExp_subE_iff.2
        (Sim.evalExp_var rfl)))) evalExp_nil
        (evalExp_resLE (evalExps_one (evalExp_subE_iff.2 (Sim.evalExp_var rfl)))))))
    (fun _ h => absurd h List.not_mem_nil)

/-- **Every Core typing of a conversion is an `Instr_ok` fact**, in every typed context. -/
theorem convert_preserves (O : ElseI) {C : Context} {c : Value} (hc : CtxT B c) {op : ConvertOp}
    {it : InstrType} (h : NumericInstrOk C (.convert op) it) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.convert op), Silmaril.SpecTec.Equiv.Validation.instrtypeV it]) := by
  cases h
  exact dd_convert O hc op

/-- **Every Core typing of a numeric instruction is an `Instr_ok` fact**, conversions included,
in every typed context: `Instr30Y.numeric_preserves` and `convert_preserves`. -/
theorem numericAll_preserves (O : ElseI) {C : Context} {c : Value} (hc : CtxT B c) {i : Instr}
    {it : InstrType} (h : NumericInstrOk C i it) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV i, Silmaril.SpecTec.Equiv.Validation.instrtypeV it]) := by
  by_cases hn : Instr30Y.numY i = true
  · exact Instr30Y.numeric_preserves O hc hn h
  · cases h with
    | convert op => exact dd_convert O hc op
    | _ => simp [Instr30Y.numY] at hn

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
