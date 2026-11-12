module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureNum

/-!
# The numeric rules of 1.0 `Step_pure`, backwards at V1 code

For each of rules 20–27 of 1.0's `Step_pure`, a firing at the image of any V1 code is the image of
a V1 `PureStep`, given `NumAgree10` at the spec profile (`bwd10_unopVal` … `bwd10_cvtopTrap`, and
`bwd10_num` for all eight). The code is read back with `Sim10.Decode` (two or three elements, by
their heads), then the rule is inverted at those IL values (`Sim10.PureNum`), and the dispatcher's
result is compared with `NumAgree10`'s by `Applies.unique`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.V1.Execution (Admin PureStep value)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim (Fires)
open Silmaril.Wasm.SpecTec.Sim20 (numTypeV)
open Silmaril.Wasm.SpecTec.Sim20.Pure (memValue_list_iff)
open Silmaril.Wasm.SpecTec.Sim20.Whole (numTypeV_inj)

variable {B : Builtins}

/-! ## Reading the code back -/

/-- Close a head inversion at one instruction constructor. -/
macro "head_inst10" : tactic => `(tactic| first
  | exact fun _ => ⟨_, rfl⟩
  | exact fun _ => ⟨_, _, rfl⟩
  | exact fun _ => .inl ⟨_, _, rfl⟩
  | exact fun _ => .inr ⟨_, _, rfl⟩
  | simp [adminHead10, instrHead10])

theorem head10_const {a : Admin} (h : adminHead10 a = "CONST") : ∃ v, a = value v := by
  obtain ⟨u, hu⟩ := adminToV_case10' a
  rw [h] at hu
  exact admin_of_const10 hu

theorem head10_unop {a : Admin} (h : adminHead10 a = "UNOP") :
    (∃ t op, a = .source (.intUnOp t op)) ∨ (∃ t op, a = .source (.floatUnOp t op)) := by
  revert h
  cases a with
  | source i => cases i <;> head_inst10
  | _ => simp [adminHead10]

theorem head10_binop {a : Admin} (h : adminHead10 a = "BINOP") :
    (∃ t op, a = .source (.intBinOp t op)) ∨ (∃ t op, a = .source (.floatBinOp t op)) := by
  revert h
  cases a with
  | source i => cases i <;> head_inst10
  | _ => simp [adminHead10]

theorem head10_relop {a : Admin} (h : adminHead10 a = "RELOP") :
    (∃ t op, a = .source (.intRelOp t op)) ∨ (∃ t op, a = .source (.floatRelOp t op)) := by
  revert h
  cases a with
  | source i => cases i <;> head_inst10
  | _ => simp [adminHead10]

theorem head10_testop {a : Admin} (h : adminHead10 a = "TESTOP") :
    ∃ t op, a = .source (.intTestOp t op) := by
  revert h
  cases a with
  | source i => cases i <;> head_inst10
  | _ => simp [adminHead10]

theorem head10_cvtop {a : Admin} (h : adminHead10 a = "CVTOP") :
    ∃ op, a = .source (.convert op) := by
  revert h
  cases a with
  | source i => cases i <;> head_inst10
  | _ => simp [adminHead10]

/-- A firing rule with a two-element left-hand side `CONST …, o …`: the code is a value and an
instruction with head `o`. -/
theorem lhs2_10 {k : Nat} {nm : IL.Id} {qs : List Param} {e₁ e₂ rh : Exp} {o : MixopS}
    {prems : List Prem} {code : List Admin} {w : Value}
    (h : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.listE [.caseE "CONST" e₁, .caseE o e₂], rh]) prems))
    (hf : Fires (simEnv10 B) "Step_pure" k (.tuple [.list (adminsToV code), w])) :
    ∃ v a, code = [value v, a] ∧ adminHead10 a = o := by
  obtain ⟨σ, -, hes, -, -⟩ := firesPure10_inv h hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨v, rfl⟩ := head10_const (head10_of_caseE h₁)
  exact ⟨v, a₂, rfl, head10_of_caseE h₂⟩

/-- A firing rule with a three-element left-hand side `CONST …, CONST …, o …`. -/
theorem lhs3_10 {k : Nat} {nm : IL.Id} {qs : List Param} {e₁ e₂ e₃ rh : Exp} {o : MixopS}
    {prems : List Prem} {code : List Admin} {w : Value}
    (h : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" k
      (.ruleD nm qs "%~>%"
        (.tupE [.listE [.caseE "CONST" e₁, .caseE "CONST" e₂, .caseE o e₃], rh]) prems))
    (hf : Fires (simEnv10 B) "Step_pure" k (.tuple [.list (adminsToV code), w])) :
    ∃ v₁ v₂ a, code = [value v₁, value v₂, a] ∧ adminHead10 a = o := by
  obtain ⟨σ, -, hes, -, -⟩ := firesPure10_inv h hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes10_three hes
  obtain ⟨v₁, rfl⟩ := head10_const (head10_of_caseE h₁)
  obtain ⟨v₂, rfl⟩ := head10_const (head10_of_caseE h₂)
  exact ⟨v₁, v₂, a₃, rfl, head10_of_caseE h₃⟩

/-- The image of a value followed by an instruction. -/
theorem adminsToV_vi (v : Execution.Runtime.Value) (i : V1.Instr) :
    adminsToV [value v, .source i] = [valV v, instrToV i] := by
  simp only [adminsToV, adminToV, adminToV_value]

/-- The image of two values followed by an instruction. -/
theorem adminsToV_vvi (v₁ v₂ : Execution.Runtime.Value) (i : V1.Instr) :
    adminsToV [value v₁, value v₂, .source i] = [valV v₁, valV v₂, instrToV i] := by
  simp only [adminsToV, adminToV, adminToV_value]

/-- The image of one value. -/
theorem adminsToV_v (v : Execution.Runtime.Value) : adminsToV [value v] = [valV v] := by
  simp only [adminsToV, adminToV_value]

/-- A one-constant result list is the image of the value. -/
theorem w_of_const {w : List Value} {t : NumType} {z : BitVec t.width} {c : Value}
    (hw : Value.list w = .list [.case "CONST" (.tuple [numTypeV t, c])]) (hc : c = numV ⟨t, z⟩) :
    Value.list w = .list (adminsToV [value ⟨t, z⟩]) := by
  rw [hw, adminsToV_v, hc]
  rfl

/-! ## The rules -/

variable {nd : Bool} {r : RelaxedChoice}

/-- **`Step_pure/unop-val`, backwards**: V1's `intUnary` or `floatUnary`. -/
theorem bwd10_unopVal (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {code : List Admin}
    {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 20 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨⟨ty, b⟩, a, rfl, ha⟩ := lhs2_10 (hasRuleAt10_unopVal B) hf
  rcases head10_unop ha with ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩
  · rw [adminsToV_vi] at hf
    obtain ⟨e, c, v, hw, happ, hm⟩ := unopVal10_inv hf
    obtain rfl := numTypeV_inj e
    have hv := Applies.unique happ (A.intUnOp t op b)
    subst hv
    have hc := List.mem_singleton.1 (memValue_list_iff.1 hm)
    exact pureBwd10_of (w_of_const (t := .int t) hw (z := intUnOp t op.toCore b) hc)
      (.intUnary t op b)
  · rw [adminsToV_vi] at hf
    obtain ⟨e, c, v, hw, happ, hm⟩ := unopVal10_inv hf
    obtain rfl := numTypeV_inj e
    obtain ⟨vs, hvs, hmem⟩ := A.floatUnOp t op b
    have hv := Applies.unique happ hvs
    subst hv
    obtain ⟨z, hz, hc⟩ := (hmem c).1 (memValue_list_iff.1 hm)
    exact pureBwd10_of (w_of_const (t := .float t) hw (z := z) hc) (.floatUnary t op b z hz)

/-- **`Step_pure/unop-trap` never fires** at V1 code: the integer `$unop_` has a result, and the
profile always allows Core's own float result. -/
theorem bwd10_unopTrap (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {code : List Admin}
    {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 21 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨⟨ty, b⟩, a, rfl, ha⟩ := lhs2_10 (hasRuleAt10_unopTrap B) hf
  rcases head10_unop ha with ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩
  · rw [adminsToV_vi] at hf
    obtain ⟨e, happ⟩ := unopTrap10_inv hf
    obtain rfl := numTypeV_inj e
    exact absurd (Applies.unique happ (A.intUnOp t op b)) (by simp)
  · rw [adminsToV_vi] at hf
    obtain ⟨e, happ⟩ := unopTrap10_inv hf
    obtain rfl := numTypeV_inj e
    obtain ⟨vs, hvs, hmem⟩ := A.floatUnOp t op b
    have hv : Value.list [] = .list vs := Applies.unique happ hvs
    have hin : Sim.floatV t (floatUnOp t op b) ∈ vs :=
      (hmem _).2 ⟨_, floatUnOpRel_self t op b, rfl⟩
    rw [← Value.list.inj hv] at hin
    exact absurd hin (List.not_mem_nil)

/-- `binop-val` at an integer operator: V1's `intBinary`. -/
theorem bwd10_binopVal_int (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {t : IntType}
    {op : IntBinOp} {ty₁ ty₂ : NumType} {b₁ : BitVec ty₁.width} {b₂ : BitVec ty₂.width}
    {w : List Value} (hf : Fires (simEnv10 B) "Step_pure" 22 (.tuple [.list
      [valV ⟨ty₁, b₁⟩, valV ⟨ty₂, b₂⟩, instrToV (.intBinOp t op)], .list w])) :
    PureBwd10 [value ⟨ty₁, b₁⟩, value ⟨ty₂, b₂⟩, .source (.intBinOp t op)] w := by
  obtain ⟨e₂, e₃, c, v, hw, happ, hm⟩ := binopVal10_inv hf
  obtain rfl : ty₁ = .int t := (numTypeV_inj e₃).symm
  obtain rfl : ty₂ = .int t := (numTypeV_inj e₂).trans (numTypeV_inj e₃).symm
  obtain ⟨vs, hvs, hmem⟩ := A.intBinOp t op b₁ b₂
  have hv : v = .list vs := Applies.unique happ hvs
  obtain ⟨z, hz, hc⟩ := (hmem c).1 (memValue_list_iff.1 (hv ▸ hm))
  exact pureBwd10_of (w_of_const (t := .int t) hw (z := z) hc) (.intBinary t op b₁ b₂ z hz)

/-- `binop-val` at a float operator: V1's `floatBinary`. -/
theorem bwd10_binopVal_float (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {t : FloatType}
    {op : FloatBinOp} {ty₁ ty₂ : NumType} {b₁ : BitVec ty₁.width} {b₂ : BitVec ty₂.width}
    {w : List Value} (hf : Fires (simEnv10 B) "Step_pure" 22 (.tuple [.list
      [valV ⟨ty₁, b₁⟩, valV ⟨ty₂, b₂⟩, instrToV (.floatBinOp t op)], .list w])) :
    PureBwd10 [value ⟨ty₁, b₁⟩, value ⟨ty₂, b₂⟩, .source (.floatBinOp t op)] w := by
  obtain ⟨e₂, e₃, c, v, hw, happ, hm⟩ := binopVal10_inv hf
  obtain rfl : ty₁ = .float t := (numTypeV_inj e₃).symm
  obtain rfl : ty₂ = .float t := (numTypeV_inj e₂).trans (numTypeV_inj e₃).symm
  obtain ⟨vs, hvs, hmem⟩ := A.floatBinOp t op b₁ b₂
  have hv : v = .list vs := Applies.unique happ hvs
  obtain ⟨z, hz, hc⟩ := (hmem c).1 (memValue_list_iff.1 (hv ▸ hm))
  exact pureBwd10_of (w_of_const (t := .float t) hw (z := z) hc) (.floatBinary t op b₁ b₂ z hz)

/-- **`Step_pure/binop-val`, backwards**: V1's `intBinary` or `floatBinary`. -/
theorem bwd10_binopVal (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {code : List Admin}
    {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 22 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨⟨ty₁, b₁⟩, ⟨ty₂, b₂⟩, a, rfl, ha⟩ := lhs3_10 (hasRuleAt10_binopVal B) hf
  rcases head10_binop ha with ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩
  · exact bwd10_binopVal_int A (adminsToV_vvi _ _ _ ▸ hf)
  · exact bwd10_binopVal_float A (adminsToV_vvi _ _ _ ▸ hf)

/-- `binop-trap` at an integer operator: V1's `intBinaryTrap`. -/
theorem bwd10_binopTrap_int (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {t : IntType}
    {op : IntBinOp} {ty₁ ty₂ : NumType} {b₁ : BitVec ty₁.width} {b₂ : BitVec ty₂.width}
    {w : List Value} (hf : Fires (simEnv10 B) "Step_pure" 23 (.tuple [.list
      [valV ⟨ty₁, b₁⟩, valV ⟨ty₂, b₂⟩, instrToV (.intBinOp t op)], .list w])) :
    PureBwd10 [value ⟨ty₁, b₁⟩, value ⟨ty₂, b₂⟩, .source (.intBinOp t op)] w := by
  obtain ⟨e₂, e₃, hw, happ⟩ := binopTrap10_inv hf
  obtain rfl : ty₁ = .int t := (numTypeV_inj e₃).symm
  obtain rfl : ty₂ = .int t := (numTypeV_inj e₂).trans (numTypeV_inj e₃).symm
  obtain ⟨vs, hvs, hmem⟩ := A.intBinOp t op b₁ b₂
  have hv : Value.list [] = .list vs := Applies.unique happ hvs
  cases hr : intBinOp t op b₁ b₂ with
  | ok z =>
      have hin : pctV z.toNat ∈ vs := (hmem (pctV z.toNat)).2 ⟨z, hr, rfl⟩
      exact absurd ((Value.list.inj hv) ▸ hin) List.not_mem_nil
  | error err =>
      exact pureBwd10_of (code' := [.trap]) (Value.list.inj hw ▸ rfl)
        (.intBinaryTrap t op b₁ b₂ err hr)

/-- `binop-trap` never fires at a float operator. -/
theorem bwd10_binopTrap_float (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {t : FloatType}
    {op : FloatBinOp} {ty₁ ty₂ : NumType} {b₁ : BitVec ty₁.width} {b₂ : BitVec ty₂.width}
    {w : List Value} (hf : Fires (simEnv10 B) "Step_pure" 23 (.tuple [.list
      [valV ⟨ty₁, b₁⟩, valV ⟨ty₂, b₂⟩, instrToV (.floatBinOp t op)], .list w])) :
    PureBwd10 [value ⟨ty₁, b₁⟩, value ⟨ty₂, b₂⟩, .source (.floatBinOp t op)] w := by
  obtain ⟨e₂, e₃, -, happ⟩ := binopTrap10_inv hf
  obtain rfl : ty₁ = .float t := (numTypeV_inj e₃).symm
  obtain rfl : ty₂ = .float t := (numTypeV_inj e₂).trans (numTypeV_inj e₃).symm
  obtain ⟨vs, hvs, hmem⟩ := A.floatBinOp t op b₁ b₂
  have hv : Value.list [] = .list vs := Applies.unique happ hvs
  have hin : Sim.floatV t (floatBinOp t op b₁ b₂) ∈ vs :=
    (hmem _).2 ⟨_, floatBinOpRel_self t op b₁ b₂, rfl⟩
  exact absurd ((Value.list.inj hv) ▸ hin) List.not_mem_nil

/-- **`Step_pure/binop-trap`, backwards**: V1's `intBinaryTrap`; it never fires at a float type. -/
theorem bwd10_binopTrap (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {code : List Admin}
    {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 23 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨⟨ty₁, b₁⟩, ⟨ty₂, b₂⟩, a, rfl, ha⟩ := lhs3_10 (hasRuleAt10_binopTrap B) hf
  rcases head10_binop ha with ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩
  · exact bwd10_binopTrap_int A (adminsToV_vvi _ _ _ ▸ hf)
  · exact bwd10_binopTrap_float A (adminsToV_vvi _ _ _ ▸ hf)

/-- **`Step_pure/testop`, backwards**: V1's `intTest`. -/
theorem bwd10_testop (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {code : List Admin}
    {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 24 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨⟨ty, b⟩, a, rfl, ha⟩ := lhs2_10 (hasRuleAt10_testop B) hf
  obtain ⟨t, op, rfl⟩ := head10_testop ha
  rw [adminsToV_vi] at hf
  obtain ⟨e, c, hw, happ⟩ := testop10_inv hf
  obtain rfl := numTypeV_inj e
  have hc := Applies.unique happ (A.intTestOp t op b)
  exact pureBwd10_of (w_of_const (t := .int .i32) hw (z := intTestOp t op b) hc) (.intTest t op b)

/-- **`Step_pure/relop`, backwards**: V1's `intRel` or `floatRel`. -/
theorem bwd10_relop (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {code : List Admin}
    {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 25 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨⟨ty₁, b₁⟩, ⟨ty₂, b₂⟩, a, rfl, ha⟩ := lhs3_10 (hasRuleAt10_relop B) hf
  rcases head10_relop ha with ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩
  · rw [adminsToV_vvi] at hf
    obtain ⟨e₂, e₃, c, hw, happ⟩ := relop10_inv hf
    obtain rfl := numTypeV_inj e₃
    obtain rfl := numTypeV_inj e₂
    have hc := Applies.unique happ (A.intRelOp t op b₁ b₂)
    exact pureBwd10_of (w_of_const (t := .int .i32) hw (z := intRelOp t op b₁ b₂) hc)
      (.intRel t op b₁ b₂)
  · rw [adminsToV_vvi] at hf
    obtain ⟨e₂, e₃, c, hw, happ⟩ := relop10_inv hf
    obtain rfl := numTypeV_inj e₃
    obtain rfl := numTypeV_inj e₂
    have hc := Applies.unique happ (A.floatRelOp t op b₁ b₂)
    exact pureBwd10_of (w_of_const (t := .int .i32) hw (z := floatRelOp t op b₁ b₂) hc)
      (.floatRel t op b₁ b₂)

/-- The image of `CONST`, then `CVTOP`. -/
theorem adminsToV_cvt (v : Execution.Runtime.Value) (op : V1.ConvertOp) :
    adminsToV [value v, .source (.convert op)] =
      [.case "CONST" (.tuple [numTypeV v.type, numV v]),
        .case "CVTOP" (.tuple [numTypeV op.toCore.target, numTypeV op.toCore.source, cvtOpV op])] :=
    by
  simp only [adminsToV, adminToV, adminToV_value]
  rfl

/-- **`Step_pure/cvtop-val`, backwards**: V1's `convert`. -/
theorem bwd10_cvtopVal (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {code : List Admin}
    {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 26 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨⟨ty, b⟩, a, rfl, ha⟩ := lhs2_10 (hasRuleAt10_cvtopVal B) hf
  obtain ⟨op, rfl⟩ := head10_cvtop ha
  rw [adminsToV_cvt] at hf
  obtain ⟨e, c, v, hw, happ, hm⟩ := cvtopVal10_inv hf
  obtain rfl := numTypeV_inj e
  obtain ⟨vs, hvs, hmem, -⟩ := A.cvtOp op b
  have hv := Applies.unique happ hvs
  subst hv
  obtain ⟨z, hz, hc⟩ := (hmem c).1 (memValue_list_iff.1 hm)
  exact pureBwd10_of (w_of_const (t := op.toCore.target) hw (z := z) hc) (.convert op b z hz)

/-- **`Step_pure/cvtop-trap`, backwards**: V1's `convertTrap`. -/
theorem bwd10_cvtopTrap (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {code : List Admin}
    {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" 27 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  obtain ⟨⟨ty, b⟩, a, rfl, ha⟩ := lhs2_10 (hasRuleAt10_cvtopTrap B) hf
  obtain ⟨op, rfl⟩ := head10_cvtop ha
  rw [adminsToV_cvt] at hf
  obtain ⟨e, hw, happ⟩ := cvtopTrap10_inv hf
  obtain rfl := numTypeV_inj e
  obtain ⟨vs, hvs, -, hnil⟩ := A.cvtOp op b
  have hv : Value.list [] = .list vs := Applies.unique happ hvs
  obtain ⟨err, he⟩ := hnil.1 (Value.list.inj hv).symm
  exact pureBwd10_of (code' := [.trap]) (Value.list.inj hw ▸ rfl) (.convertTrap op b err he)

/-- **The numeric rules 20–27 of 1.0 `Step_pure`, backwards**, at every V1 code. -/
theorem bwd10_num (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) {i : Nat}
    (hi : i ∈ [20, 21, 22, 23, 24, 25, 26, 27]) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w])) :
    PureBwd10 code w := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bwd10_unopVal A hf
  · exact bwd10_unopTrap A hf
  · exact bwd10_binopVal A hf
  · exact bwd10_binopTrap A hf
  · exact bwd10_testop A hf
  · exact bwd10_relop A hf
  · exact bwd10_cvtopVal A hf
  · exact bwd10_cvtopTrap A hf

end Silmaril.Wasm.SpecTec.Sim10.Whole
