module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.NxVec
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.NxInstrV

/-!
# Round 7, encoder lemma: instructions are free of `EXPORTS` records

`nxB_instrToV`: every instruction image `instrToV i` passes `nxB`. No instruction encoder builds a
record other than `memarg`, whose fields are `ALIGN` and `OFFSET`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim

@[simp] theorem nxB_refToValue : ∀ r : Execution.Core.Ref,
    nxB (Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue r) = true
  | .i31 _ => rfl
  | .null => rfl
  | .struct _ => rfl
  | .array _ => rfl
  | .func _ => rfl
  | .exn _ => rfl
  | .host _ => rfl
  | .extern r => nxB_refToValue r

@[simp] theorem nxB_floatV (t : FloatType) (b : BitVec t.width) : nxB (floatV t b) = true := by
  simp only [floatV, nxB_case]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

@[simp] theorem nxB_numV (n : Execution.Core.NumVal) : nxB (numV n) = true := by
  obtain ⟨t, b⟩ := n
  cases t with
  | int _ => rfl
  | float t => exact nxB_floatV t b

@[simp] theorem nxB_valV (v : Execution.Core.Val) : nxB (valV v) = true := by
  cases v with
  | num n => simp [valV, nxB_numType, nxB_numV]
  | vec _ => rfl
  | ref r => exact nxB_refToValue r

@[simp] theorem nxB_memargV (a : MemArg) : nxB (memargV a) = true := rfl

@[simp] theorem nxB_simSxV (s : Signedness) : nxB (Sim.sxV s) = true := by cases s <;> rfl

@[simp] theorem nxB_schemaV (e : Silmaril.Formats.TExpr String Int) : nxB (schemaV e) = true := by
  fun_induction schemaV e
  all_goals first
    | rfl
    | (simp only [nxB_list, nxB_case, nxB_tuple, nxB_opt_some, nxBs_eq_all, List.all_eq_true,
        List.mem_ofFn]
       first
        | (rintro _ ⟨k, rfl⟩; simp_all)
        | simp_all)

@[simp] theorem nxB_schemaInstrV (c : Silmaril.Wasm.SpecTecEnc.Constructor) : nxB (schemaInstrV c) = true := by
  unfold schemaInstrV
  split
  · exact nxB_schemaV _
  · simp [nxBs_eq_all, nxB_schemaV]

set_option linter.unusedTactic false in
theorem nxB_vecInstrV? {i : Instr} {v : Value} (h : Vec.vecInstrV? i = some v) : nxB v = true := by
  unfold Vec.vecInstrV? at h
  split at h <;> (try cases h) <;>
    simp [Vec.ishapeV, Vec.bshapeV, Vec.laneIdxV, nxB_vvunopV, nxB_vvbinopV, nxB_vvternopV,
      nxB_vvtestopV, nxB_ishV, nxB_fshV, nxB_vIntUnOpV, nxB_vFloatUnOpV, nxB_vIntBinOpV,
      nxB_vFloatBinOpV, nxB_vIntTernOpV, nxB_vFloatTernOpV, nxB_vIntRelOpV, nxB_vFloatRelOpV,
      nxB_vShiftOpV, nxB_vSwizzleOpV, nxB_vExtUnOpV, nxB_vExtBinOpV, nxB_vExtTernOpV, nxB_sxV,
      nxB_vConvertOpV, nxB_shapeV, Vec.vecTypeV, Silmaril.SpecTec.Equiv.Execution.pctV,
      Silmaril.SpecTec.Equiv.Execution.caseNilV]

@[simp] theorem nxB_convertInstrV (op : ConvertOp) : nxB (Vec.convertInstrV op) = true := by
  simp [Vec.convertInstrV, nxB_numTypeV, nxB_cvtOpV]

theorem nxB_getD {o : Option Value} {d : Value} (ho : ∀ v, o = some v → nxB v = true)
    (hd : nxB d = true) : nxB (o.getD d) = true := by
  cases o with
  | none => exact hd
  | some v => exact ho v rfl

mutual
@[simp] theorem nxB_instrToV (i : Instr) : nxB (instrToV i) = true := by
  cases i
  case block bt body => simp [instrToV, nxB_instrsToV body]
  case loop bt body => simp [instrToV, nxB_instrsToV body]
  case if_ bt b₁ b₂ => simp [instrToV, nxB_instrsToV b₁, nxB_instrsToV b₂]
  case tryTable bt cs body => simp [instrToV, nxB_instrsToV body]
  case select ts =>
    cases ts with
    | none => exact nxB_instrV _
    | some ts => simp [instrToV]
  all_goals first
    | rfl
    | (simp only [instrToV]
       first
        | exact nxB_getD (fun _ h => nxB_vecInstrV? h) (nxB_schemaInstrV _)
        | simp [szV, Silmaril.SpecTec.Equiv.Execution.pctV])
termination_by sizeOf i

theorem nxB_instrsToV : ∀ l : List Instr, nxBs (instrsToV l) = true
  | [] => rfl
  | i :: l => by simp [instrsToV, nxB_instrToV i, nxB_instrsToV l]
termination_by l => sizeOf l
end

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
