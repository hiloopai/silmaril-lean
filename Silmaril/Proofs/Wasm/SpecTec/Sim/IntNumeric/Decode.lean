module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Forward
public import Mathlib.Tactic.CasesM

/-!
# Decoding the images of the numeric and parametric instructions

`instrToV` is total, so the backward direction has to recover a Core instruction from the variant
case of its image. Each lemma here inverts one case tag: an `instr` whose image is `BINOP p` is
`intBinOp` (with `p` determined) or `floatBinOp`, and so on. The proofs split every instruction
constructor and every operator enumeration; the vector instructions, whose images go through
`encodeInstruction`, are told apart by their tags.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (bvV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- A schema constructor's image is a case with the constructor's tag. -/
theorem schemaInstrV_case (c : Silmaril.Wasm.SpecTecEnc.Constructor) :
    ∃ w, schemaInstrV c = .case c.tag w := by
  unfold schemaInstrV; split <;> exact ⟨_, rfl⟩

/-- A vector instruction's image carries its schema tag. -/
theorem vec_tag {i : Instr} {op : String} {p : Value}
    (h0 : instrToV i = schemaInstrV (Silmaril.Wasm.SpecTecEnc.encodeInstruction i))
    (h : instrToV i = .case op p) : (Silmaril.Wasm.SpecTecEnc.encodeInstruction i).tag = op := by
  obtain ⟨w, hw⟩ := schemaInstrV_case (Silmaril.Wasm.SpecTecEnc.encodeInstruction i)
  rw [h0, hw] at h
  injection h

/-- Split an instruction and every operator enumeration it carries; close the cases whose image
has another tag, and try `pos` on the others. -/
macro "int_numeric_decode" i:ident h:ident pos:tactic : tactic => `(tactic| (
  cases $i:ident
  all_goals (try cases_type* ConvertOp IntUnOp IntBinOp IntTestOp IntRelOp)
  all_goals (try cases_type* FloatUnOp FloatBinOp FloatRelOp)
  all_goals (try cases_type* IntType FloatType Signedness PackSize)
  all_goals (try cases_type* Option)
  all_goals first
    | (injection $h:ident with h1; exact absurd h1 (by decide))
    | ($pos:tactic)
    | (cases $h:ident; done)
    | (have h1 := vec_tag rfl $h:ident; rw [Silmaril.Wasm.SpecTecEnc.encodeInstruction] at h1;
       simp at h1)))

set_option maxHeartbeats 1000000 in
/-- `BINOP p` is an integer or a float binary operator. -/
theorem dec_binop {i : Instr} {p : Value} (h : instrToV i = .case "BINOP" p) :
    (∃ t op, i = .intBinOp t op ∧ p = .tuple [ntV t, ibinopV op]) ∨
      (∃ t op, i = .floatBinOp t op) := by
  int_numeric_decode i h (first
    | exact .inr ⟨_, _, rfl⟩
    | (injection h with _ h2; exact .inl ⟨_, _, rfl, h2.symm⟩))

set_option maxHeartbeats 1000000 in
/-- `UNOP p` is a valid integer or a float unary operator. -/
theorem dec_unop {i : Instr} {p : Value} (h : instrToV i = .case "UNOP" p) :
    (∃ t op, i = .intUnOp t op ∧ op.valid t = true ∧ p = .tuple [ntV t, iunopV op]) ∨
      (∃ t op, i = .floatUnOp t op) := by
  int_numeric_decode i h (first
    | exact .inr ⟨_, _, rfl⟩
    | (injection h with _ h2; exact .inl ⟨_, _, rfl, rfl, h2.symm⟩))

set_option maxHeartbeats 1000000 in
/-- `TESTOP p` is an integer test. -/
theorem dec_testop {i : Instr} {p : Value} (h : instrToV i = .case "TESTOP" p) :
    ∃ t op, i = .intTestOp t op ∧ p = .tuple [ntV t, itestopV op] := by
  int_numeric_decode i h (injection h with _ h2; exact ⟨_, _, rfl, h2.symm⟩)

set_option maxHeartbeats 1000000 in
/-- `RELOP p` is an integer or a float comparison. -/
theorem dec_relop {i : Instr} {p : Value} (h : instrToV i = .case "RELOP" p) :
    (∃ t op, i = .intRelOp t op ∧ p = .tuple [ntV t, irelopV op]) ∨
      (∃ t op, i = .floatRelOp t op) := by
  int_numeric_decode i h (first
    | exact .inr ⟨_, _, rfl⟩
    | (injection h with _ h2; exact .inl ⟨_, _, rfl, h2.symm⟩))

set_option maxHeartbeats 1000000 in
/-- `CONST p` is an integer or a float constant. -/
theorem dec_const {i : Instr} {p : Value} (h : instrToV i = .case "CONST" p) :
    (∃ t b, i = .intConst t b ∧ p = .tuple [ntV t, bvV b]) ∨ (∃ t b, i = .floatConst t b) := by
  int_numeric_decode i h (first
    | exact .inr ⟨_, _, rfl⟩
    | (injection h with _ h2; exact .inl ⟨_, _, rfl, h2.symm⟩))

set_option maxHeartbeats 1000000 in
/-- `SELECT p` is a `select`. -/
theorem dec_select {i : Instr} {p : Value} (h : instrToV i = .case "SELECT" p) :
    ∃ ts, i = .select ts ∧ p = .opt ((ts.map (·.map Encode.toValue)).map .list) := by
  int_numeric_decode i h (injection h with _ h2; exact ⟨_, rfl, h2.symm⟩)

set_option maxHeartbeats 1000000 in
/-- `UNREACHABLE` is `unreachable`. -/
theorem dec_unreachable {i : Instr} {p : Value} (h : instrToV i = .case "UNREACHABLE" p) :
    i = .unreachable := by
  int_numeric_decode i h rfl

set_option maxHeartbeats 1000000 in
/-- `NOP` is `nop`. -/
theorem dec_nop {i : Instr} {p : Value} (h : instrToV i = .case "NOP" p) : i = .nop := by
  int_numeric_decode i h rfl

set_option maxHeartbeats 1000000 in
/-- `DROP` is `drop`. -/
theorem dec_drop {i : Instr} {p : Value} (h : instrToV i = .case "DROP" p) : i = .drop := by
  int_numeric_decode i h rfl

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
