module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Vec
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.InstrV

/-!
# Round 7, encoder lemma: instructions are `EXPORTS`-free

`efB_instrToV`: every instruction image `instrToV i` passes `efB`. No instruction encoder builds a
record other than `memarg`, whose fields are `ALIGN` and `OFFSET`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim

@[simp] theorem efB_refToValue : ∀ r : Execution.Core.Ref,
    efB (Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue r) = true
  | .i31 _ => rfl
  | .null => rfl
  | .struct _ => rfl
  | .array _ => rfl
  | .func _ => rfl
  | .exn _ => rfl
  | .host _ => rfl
  | .extern r => efB_refToValue r

@[simp] theorem efB_floatV (t : FloatType) (b : BitVec t.width) : efB (floatV t b) = true := by
  simp only [floatV, efB_case]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

@[simp] theorem efB_numV (n : Execution.Core.NumVal) : efB (numV n) = true := by
  obtain ⟨t, b⟩ := n
  cases t with
  | int _ => rfl
  | float t => exact efB_floatV t b

@[simp] theorem efB_valV (v : Execution.Core.Val) : efB (valV v) = true := by
  cases v with
  | num n => simp [valV, efB_numType, efB_numV]
  | vec _ => rfl
  | ref r => exact efB_refToValue r

@[simp] theorem efB_memargV (a : MemArg) : efB (memargV a) = true := rfl

@[simp] theorem efB_simSxV (s : Signedness) : efB (Sim.sxV s) = true := by cases s <;> rfl

@[simp] theorem efB_schemaV (e : Silmaril.Formats.TExpr String Int) : efB (schemaV e) = true := by
  fun_induction schemaV e
  all_goals first
    | rfl
    | (simp only [efB_list, efB_case, efB_tuple, efB_opt_some, efBs_eq_all, List.all_eq_true,
        List.mem_ofFn]
       first
        | (rintro _ ⟨k, rfl⟩; simp_all)
        | simp_all)

@[simp] theorem efB_schemaInstrV (c : Silmaril.Wasm.SpecTecEnc.Constructor) : efB (schemaInstrV c) = true := by
  unfold schemaInstrV
  split
  · exact efB_schemaV _
  · simp [efBs_eq_all, efB_schemaV]

set_option linter.unusedTactic false in
theorem efB_vecInstrV? {i : Instr} {v : Value} (h : Vec.vecInstrV? i = some v) : efB v = true := by
  unfold Vec.vecInstrV? at h
  split at h <;> (try cases h) <;>
    simp [Vec.ishapeV, Vec.bshapeV, Vec.laneIdxV, efB_vvunopV, efB_vvbinopV, efB_vvternopV,
      efB_vvtestopV, efB_ishV, efB_fshV, efB_vIntUnOpV, efB_vFloatUnOpV, efB_vIntBinOpV,
      efB_vFloatBinOpV, efB_vIntTernOpV, efB_vFloatTernOpV, efB_vIntRelOpV, efB_vFloatRelOpV,
      efB_vShiftOpV, efB_vSwizzleOpV, efB_vExtUnOpV, efB_vExtBinOpV, efB_vExtTernOpV, efB_sxV,
      efB_vConvertOpV, efB_shapeV, Vec.vecTypeV, Silmaril.SpecTec.Equiv.Execution.pctV,
      Silmaril.SpecTec.Equiv.Execution.caseNilV]

@[simp] theorem efB_convertInstrV (op : ConvertOp) : efB (Vec.convertInstrV op) = true := by
  simp [Vec.convertInstrV, efB_numTypeV, efB_cvtOpV]

theorem efB_getD {o : Option Value} {d : Value} (ho : ∀ v, o = some v → efB v = true)
    (hd : efB d = true) : efB (o.getD d) = true := by
  cases o with
  | none => exact hd
  | some v => exact ho v rfl

mutual
@[simp] theorem efB_instrToV (i : Instr) : efB (instrToV i) = true := by
  cases i
  case block bt body => simp [instrToV, efB_instrsToV body]
  case loop bt body => simp [instrToV, efB_instrsToV body]
  case if_ bt b₁ b₂ => simp [instrToV, efB_instrsToV b₁, efB_instrsToV b₂]
  case tryTable bt cs body => simp [instrToV, efB_instrsToV body]
  case select ts =>
    cases ts with
    | none => exact efB_instrV _
    | some ts => simp [instrToV]
  all_goals first
    | rfl
    | (simp only [instrToV]
       first
        | exact efB_getD (fun _ h => efB_vecInstrV? h) (efB_schemaInstrV _)
        | simp [szV, Silmaril.SpecTec.Equiv.Execution.pctV])
termination_by sizeOf i

theorem efB_instrsToV : ∀ l : List Instr, efBs (instrsToV l) = true
  | [] => rfl
  | i :: l => by simp [instrsToV, efB_instrToV i, efB_instrsToV l]
termination_by l => sizeOf l
end

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
