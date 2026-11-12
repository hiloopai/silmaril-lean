module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.NxVec
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.NxInstrV

/-!
# Round 8 (copy of round 7 for `CODE` fields), encoder lemma: instructions are free of `CODE` records

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

`ncB_instrToV`: every instruction image `instrToV i` passes `ncB`. No instruction encoder builds a
record other than `memarg`, whose fields are `ALIGN` and `OFFSET`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim

@[simp] theorem ncB_refToValue : ∀ r : Execution.Core.Ref,
    ncB (Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue r) = true
  | .i31 _ => rfl
  | .null => rfl
  | .struct _ => rfl
  | .array _ => rfl
  | .func _ => rfl
  | .exn _ => rfl
  | .host _ => rfl
  | .extern r => ncB_refToValue r

@[simp] theorem ncB_floatV (t : FloatType) (b : BitVec t.width) : ncB (floatV t b) = true := by
  simp only [floatV, ncB_case]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

@[simp] theorem ncB_numV (n : Execution.Core.NumVal) : ncB (numV n) = true := by
  obtain ⟨t, b⟩ := n
  cases t with
  | int _ => rfl
  | float t => exact ncB_floatV t b

@[simp] theorem ncB_valV (v : Execution.Core.Val) : ncB (valV v) = true := by
  cases v with
  | num n => simp [valV, ncB_numType, ncB_numV]
  | vec _ => rfl
  | ref r => exact ncB_refToValue r

@[simp] theorem ncB_memargV (a : MemArg) : ncB (memargV a) = true := rfl

@[simp] theorem ncB_simSxV (s : Signedness) : ncB (Sim.sxV s) = true := by cases s <;> rfl

@[simp] theorem ncB_schemaV (e : Silmaril.Formats.TExpr String Int) : ncB (schemaV e) = true := by
  fun_induction schemaV e
  all_goals first
    | rfl
    | (simp only [ncB_list, ncB_case, ncB_tuple, ncB_opt_some, ncBs_eq_all, List.all_eq_true,
        List.mem_ofFn]
       first
        | (rintro _ ⟨k, rfl⟩; simp_all)
        | simp_all)

@[simp] theorem ncB_schemaInstrV (c : Silmaril.Wasm.SpecTec.Constructor) : ncB (schemaInstrV c) = true := by
  unfold schemaInstrV
  split
  · exact ncB_schemaV _
  · simp [ncBs_eq_all, ncB_schemaV]

theorem ncB_vecInstrV? {i : Instr} {v : Value} (h : Vec.vecInstrV? i = some v) : ncB v = true := by
  unfold Vec.vecInstrV? at h
  split at h <;> (try cases h) <;>
    simp [Vec.ishapeV, Vec.bshapeV, Vec.laneIdxV, ncB_vvunopV, ncB_vvbinopV, ncB_vvternopV,
      ncB_vvtestopV, ncB_ishV, ncB_fshV, ncB_vIntUnOpV, ncB_vFloatUnOpV, ncB_vIntBinOpV,
      ncB_vFloatBinOpV, ncB_vIntTernOpV, ncB_vFloatTernOpV, ncB_vIntRelOpV, ncB_vFloatRelOpV,
      ncB_vShiftOpV, ncB_vSwizzleOpV, ncB_vExtUnOpV, ncB_vExtBinOpV, ncB_vExtTernOpV, ncB_sxV,
      ncB_vConvertOpV, ncB_shapeV, Vec.vecTypeV, Silmaril.SpecTec.Equiv.Execution.pctV,
      Silmaril.SpecTec.Equiv.Execution.caseNilV]

@[simp] theorem ncB_convertInstrV (op : ConvertOp) : ncB (Vec.convertInstrV op) = true := by
  simp [Vec.convertInstrV, ncB_numTypeV, ncB_cvtOpV]

theorem ncB_getD {o : Option Value} {d : Value} (ho : ∀ v, o = some v → ncB v = true)
    (hd : ncB d = true) : ncB (o.getD d) = true := by
  cases o with
  | none => exact hd
  | some v => exact ho v rfl

mutual
@[simp] theorem ncB_instrToV (i : Instr) : ncB (instrToV i) = true := by
  cases i
  case block bt body => simp [instrToV, ncB_instrsToV body]
  case loop bt body => simp [instrToV, ncB_instrsToV body]
  case if_ bt b₁ b₂ => simp [instrToV, ncB_instrsToV b₁, ncB_instrsToV b₂]
  case tryTable bt cs body => simp [instrToV, ncB_instrsToV body]
  case select ts =>
    cases ts with
    | none => exact ncB_instrV _
    | some ts => simp [instrToV]
  all_goals first
    | rfl
    | (simp only [instrToV]
       first
        | exact ncB_getD (fun _ h => ncB_vecInstrV? h) (ncB_schemaInstrV _)
        | simp [szV, Silmaril.SpecTec.Equiv.Execution.pctV])
termination_by sizeOf i

theorem ncB_instrsToV : ∀ l : List Instr, ncBs (instrsToV l) = true
  | [] => rfl
  | i :: l => by simp [instrsToV, ncB_instrToV i, ncB_instrsToV l]
termination_by l => sizeOf l
end

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
