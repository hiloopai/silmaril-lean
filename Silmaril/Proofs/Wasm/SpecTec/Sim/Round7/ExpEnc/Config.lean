module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Instr

/-!
# Round 7, encoder lemma: export-free configurations encode to `ExpFree` values

The only record with an `EXPORTS` field that `configV` builds is `moduleInstToValue`'s, and its
field is `.list (m.exports.map exportInstToValue)`. So a module instance with no exports encodes
to an `efB` value (`efB_moduleInstToValue`), and so do the frames, administrative instructions,
function instances and stores whose module instances have none (`efB_frameV`, `efB_adminsToV`,
`efB_funcInstV`, `efB_storeV`). Every other encoder builds records whose field names are fixed
and differ from `EXPORTS`.

* `efB_configV`, `expFree_configV`: `Round5.Pos.NoExports c → ExpFree (configV hn c)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round5.Pos (AdminNE AdminsNE StoreNE NoExports)

variable {H : Type}

@[simp] theorem efB_bytesToValue (bs : ByteArray) : efB (bytesToValue bs) = true := by
  simp only [bytesToValue, efB_list, efBs_map]
  exact List.all_eq_true.2 fun _ _ => rfl

@[simp] theorem efB_cGlobalTypeV (g : Validation.CGlobalType) : efB (cGlobalTypeV g) = true := by
  simp only [cGlobalTypeV, efB_case, efB_tuple, efBs_cons, efB_mutability, efB_tyV, efBs_nil,
    Bool.and_self]

@[simp] theorem efB_cTableTypeV (t : Validation.CTableType) : efB (cTableTypeV t) = true := by
  simp only [cTableTypeV, efB_case, efB_tuple, efBs_cons, efB_addrType, efB_limits, efB_tyV,
    efBs_nil, Bool.and_self]

@[simp] theorem efB_fieldValV (v : FieldVal) : efB (fieldValV v) = true := by
  cases v <;> simp [fieldValV, Silmaril.SpecTec.Equiv.Execution.pctV]

theorem efB_moduleInstToValue {m : ModuleInst} (h : m.exports = []) :
    efB (moduleInstToValue CT m) = true := by
  simp [moduleInstToValue, h, CT]

theorem efB_frameV {f : Frame} (h : f.module.exports = []) : efB (frameV f) = true := by
  have hm := efB_moduleInstToValue h
  simp only [frameV, efB_struct, efBf_cons, efBf_nil, hm, efB_list, efBs_map]
  simp

mutual
theorem efB_adminToV : ∀ a : Admin, AdminNE a → efB (adminToV a) = true
  | .plain i, _ => efB_instrToV i
  | .ref r, _ => efB_refToValue r
  | .callRefType d, _ => by simp [adminToV, CT]
  | .returnCallRefType d, _ => by simp [adminToV, CT]
  | .label n cont body, h => by
    simp [adminToV, efB_instrsToV cont, efB_adminsToV body h]
  | .handler n cs body, h => by
    simp [adminToV, efB_adminsToV body h]
  | .frame n f body, h => by
    simp [adminToV, efB_frameV h.1, efB_adminsToV body h.2]
  | .trap, _ => rfl

theorem efB_adminsToV : ∀ l : List Admin, AdminsNE l → efBs (adminsToV l) = true
  | [], _ => rfl
  | a :: l, h => by
    simp [adminsToV, efB_adminToV a h.1, efB_adminsToV l h.2]
end

theorem efB_funcInstV (hn : H → String) {fi : FuncInst H} (h : fi.module.exports = []) :
    efB (funcInstV hn fi) = true := by
  have hm := efB_moduleInstToValue h
  simp only [funcInstV, efB_struct, efBf_cons, efBf_nil, hm]
  split <;> simp [CT, efB_instrsToV, Silmaril.SpecTec.Equiv.Execution.pctV]

theorem efB_storeV (hn : H → String) {s : Store H} (h : StoreNE s) : efB (storeV hn s) = true := by
  have hf : (s.funcs.all fun fi => efB (funcInstV hn fi)) = true :=
    List.all_eq_true.2 fun fi hfi => efB_funcInstV hn (h fi hfi)
  simp [storeV, hf, tagInstToValue, globalInstV, memInstToValue, tableInstToValue,
    dataInstToValue, elemInstToValue, structInstV, arrayInstV, exnInstV, CT]

/-- **The encoder lemma**, as a boolean. -/
theorem efB_configV (hn : H → String) {c : Config H} (h : NoExports c) :
    efB (configV hn c) = true := by
  simp [configV, stateV, efB_storeV hn h.store, efB_frameV h.frame, efB_adminsToV _ h.code]

/-- **The encoder lemma**: the image of an export-free configuration is `ExpFree`. -/
theorem expFree_configV (hn : H → String) {c : Config H} (h : NoExports c) :
    TypAgree.ExpFree (configV hn c) :=
  expFree_of_efB _ (efB_configV hn h)

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
