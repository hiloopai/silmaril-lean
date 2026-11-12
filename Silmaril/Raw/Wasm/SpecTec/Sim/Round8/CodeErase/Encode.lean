module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.NxInstr

/-!
# Round 8, function code erasure: encoders build no `CODE` records (copied from round 7)

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

* `eraseC_of_ncB`: `eraseC` fixes values without `CODE` records;
* `ncB_*`: the leaf encoders, the module instance and frame images and the code images
  (`adminsToV`) have no `CODE` record, so `eraseC` fixes them (`eraseC_frameV`,
  `eraseCs_adminsToV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type}

/-! ## `eraseC` fixes values without `CODE` records -/

mutual
theorem eraseC_of_ncB : ∀ v : Value, ncB v = true → eraseC v = v
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple vs, h => by rw [eraseC_tuple, eraseCs_of_ncBs vs h]
  | .case _ w, h => by rw [eraseC_case, eraseC_of_ncB w h]
  | .struct gs, h => by rw [eraseC_struct, eraseCf_of_ncBf gs h]
  | .list vs, h => by rw [eraseC_list, eraseCs_of_ncBs vs h]
  | .opt none, _ => rfl
  | .opt (some w), h => by rw [eraseC_opt_some, eraseC_of_ncB w h]

theorem eraseCs_of_ncBs : ∀ vs : List Value, ncBs vs = true → eraseCs vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [ncBs, Bool.and_eq_true] at h
    simp only [eraseCs, eraseC_of_ncB v h.1, eraseCs_of_ncBs vs h.2]

theorem eraseCf_of_ncBf : ∀ gs : List (IL.AtomS × Value), ncBf gs = true → eraseCf gs = gs
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [ncBf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [eraseCf_cons, eraseCf_of_ncBf gs h.2, ite_eq_right h.1.2, eraseC_of_ncB v h.1.1]
end

/-! ## The leaves build no `CODE` records -/

@[simp] theorem ncB_bytesToValue (bs : ByteArray) : ncB (bytesToValue bs) = true := by
  simp only [bytesToValue, ncB_list, ncBs_map]
  exact List.all_eq_true.2 fun _ _ => rfl

@[simp] theorem ncB_cGlobalTypeV (g : Validation.CGlobalType) : ncB (cGlobalTypeV g) = true := by
  simp only [cGlobalTypeV, ncB_case, ncB_tuple, ncBs_cons, ncB_mutability, ncB_tyV, ncBs_nil,
    Bool.and_self]

@[simp] theorem ncB_cTableTypeV (t : Validation.CTableType) : ncB (cTableTypeV t) = true := by
  simp only [cTableTypeV, ncB_case, ncB_tuple, ncBs_cons, ncB_addrType, ncB_limits, ncB_tyV,
    ncBs_nil, Bool.and_self]

@[simp] theorem ncB_fieldValV (v : FieldVal) : ncB (fieldValV v) = true := by
  cases v <;> simp [fieldValV, Silmaril.SpecTec.Equiv.Execution.pctV]

@[simp] theorem ncB_exportInstToValue (e : ExportInst) : ncB (exportInstToValue e) = true := by
  obtain ⟨n, a⟩ := e
  cases a <;> simp [exportInstToValue, nameToValue, charToValue, externAddrToValue]

theorem ncB_locals (l : List (Option Val)) :
    ncB (.list (l.map fun o => .opt (o.map valV))) = true := by
  simp

theorem ncB_codeV (hn : H → String) (fi : FuncInst H) :
    ncB (match fi.code with
      | .wasm fn => .case "FUNC" (.tuple [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
          .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
          .list (instrsToV fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h))) = true := by
  split <;> simp [ncB_instrsToV, Silmaril.SpecTec.Equiv.Execution.pctV]

theorem ncB_storeRest (s : Store H) :
    ncB (.list (s.tags.map (tagInstToValue CT))) = true ∧
    ncB (.list (s.globals.map globalInstV)) = true ∧
    ncB (.list (s.mems.map memInstToValue)) = true ∧
    ncB (.list (s.tables.map (tableInstToValue CT))) = true ∧
    ncB (.list (s.datas.map dataInstToValue)) = true ∧
    ncB (.list (s.elems.map (elemInstToValue CT))) = true ∧
    ncB (.list (s.structs.map structInstV)) = true ∧
    ncB (.list (s.arrays.map arrayInstV)) = true ∧
    ncB (.list (s.exns.map exnInstV)) = true := by
  simp [tagInstToValue, globalInstV, memInstToValue, tableInstToValue, dataInstToValue,
    elemInstToValue, structInstV, arrayInstV, exnInstV, CT]

/-! ## The images without function code are fixed -/

@[simp] theorem ncB_moduleInstToValue (m : ModuleInst) : ncB (moduleInstToValue CT m) = true := by
  simp [moduleInstToValue, CT]

@[simp] theorem ncB_frameV (f : Frame) : ncB (frameV f) = true := by
  simp only [frameV, ncB_struct, ncBf_cons, ncBf_nil, ncB_moduleInstToValue, ncB_locals]
  decide

theorem eraseC_frameV (f : Frame) : eraseC (frameV f) = frameV f :=
  eraseC_of_ncB _ (ncB_frameV f)

mutual
theorem ncB_adminToV : ∀ a : Admin, ncB (adminToV a) = true
  | .plain i => ncB_instrToV i
  | .ref r => ncB_refToValue r
  | .callRefType d => by simp [adminToV, CT]
  | .returnCallRefType d => by simp [adminToV, CT]
  | .label n cont body => by
    simp only [adminToV, ncB_case, ncB_tuple, ncBs_cons, ncBs_nil, ncB_list, Bool.and_true]
    rw [ncBs_adminsToV body]
    simp [ncB_instrsToV cont]
  | .handler n cs body => by
    simp only [adminToV, ncB_case, ncB_tuple, ncBs_cons, ncBs_nil, ncB_list, Bool.and_true]
    rw [ncBs_adminsToV body]
    simp
  | .frame n f body => by
    simp only [adminToV, ncB_case, ncB_tuple, ncBs_cons, ncBs_nil, ncB_list, Bool.and_true,
      ncB_frameV]
    rw [ncBs_adminsToV body]
    rfl
  | .trap => rfl

theorem ncBs_adminsToV : ∀ l : List Admin, ncBs (adminsToV l) = true
  | [] => rfl
  | a :: l => by
    simp only [adminsToV, ncBs_cons, ncB_adminToV a, ncBs_adminsToV l, Bool.and_self]
end

theorem eraseCs_adminsToV (l : List Admin) : eraseCs (adminsToV l) = adminsToV l :=
  eraseCs_of_ncBs _ (ncBs_adminsToV l)

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
