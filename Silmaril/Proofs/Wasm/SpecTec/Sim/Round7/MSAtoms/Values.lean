module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.Types

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge: runtime values, instances and frames

The value encoders (`refToValue`, `valV`, `fieldValV`, byte strings, export instances) and the
instance records of the store other than function instances (`tagInstToValue`, `globalInstV`,
`memInstToValue`, `tableInstToValue`, `dataInstToValue`, `elemInstToValue`, `structInstV`,
`arrayInstV`, `exnInstV`), the module instance and the frame have no atom of `HStep.hAtoms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open HStep (hAtoms)

theorem nh_pctV (n : Nat) : NH (pctV n) := by
  simp only [pctV]; nh_close

theorem nh_caseNilV {a : MixopS} (ha : a ∉ hAtoms) : NH (caseNilV a) := by
  simp only [caseNilV]
  exact ⟨ha, trivial⟩

theorem nh_refToValue : ∀ r : Ref, NH (refToValue r)
  | .i31 b => by simp only [refToValue, percentV, caseV]; nh_close
  | .null => by simp only [refToValue]; nh_close
  | .struct a => by simp only [refToValue]; nh_close
  | .array a => by simp only [refToValue]; nh_close
  | .func a => by simp only [refToValue]; nh_close
  | .exn a => by simp only [refToValue]; nh_close
  | .host a => by simp only [refToValue]; nh_close
  | .extern r => by
      have h := nh_refToValue r
      simp only [refToValue]
      nh_close

theorem nh_sxV (s : Signedness) : NH (Sim.sxV s) := by
  cases s <;> simp only [Sim.sxV, caseNilV] <;> nh_close

theorem nh_szV (p : PackSize) : NH (Sim.szV p) := nh_pctV _

theorem nh_memargV (a : MemArg) : NH (Sim.memargV a) := by
  simp only [Sim.memargV, pctV]; nh_close

theorem nh_floatV (t : FloatType) (b : BitVec t.width) : NH (Sim.floatV t b) := by
  simp only [Sim.floatV, caseNilV]
  split_ifs <;> nh_close

theorem nh_numV (n : NumVal) : NH (Sim.numV n) := by
  rcases n with ⟨t | t, b⟩
  · exact nh_pctV _
  · exact nh_floatV t b

theorem nh_valV (v : Val) : NH (Sim.valV v) := by
  rcases v with n | b | r
  · have h₁ := nh_numType n.type
    have h₂ := nh_numV n
    simp only [Sim.valV]
    nh_close
  · simp only [Sim.valV, caseNilV, pctV]; nh_close
  · exact nh_refToValue r

theorem nh_fieldValV (v : FieldVal) : NH (Sim.fieldValV v) := by
  rcases v with v | ⟨p, b⟩
  · exact nh_valV v
  · have h := nh_packType p
    simp only [Sim.fieldValV, pctV]
    nh_close

theorem nh_bytes (bs : ByteArray) : NH (bytesToValue bs) := by
  simp only [bytesToValue]
  exact noAtoms_list_map fun _ _ => nh_pctNat _

theorem nh_externAddr (a : ExternAddr) : NH (externAddrToValue a) := by
  cases a <;> simp only [externAddrToValue] <;> nh_close

theorem nh_name (n : String) : NH (nameToValue n) := by
  have h : NH (.list (n.toList.map charToValue)) :=
    noAtoms_list_map fun c _ => by simp only [charToValue]; nh_close
  simp only [nameToValue]
  nh_close

theorem nh_exportInst (e : ExportInst) : NH (exportInstToValue e) := by
  have h₁ := nh_name e.name
  have h₂ := nh_externAddr e.addr
  simp only [exportInstToValue]
  nh_close

theorem nh_natList (l : List Nat) : NH (.list (l.map fun a => .num (.natN a))) :=
  noAtoms_list_map fun _ _ => trivial

theorem nh_moduleInst (m : ModuleInst) : NH (moduleInstToValue Sim.CT m) := by
  have h₁ : NH (.list (m.types.map Sim.CT.defType)) :=
    noAtoms_list_map fun d _ => nh_defType d
  have h₂ := nh_natList m.tags
  have h₃ := nh_natList m.globals
  have h₄ := nh_natList m.mems
  have h₅ := nh_natList m.tables
  have h₆ := nh_natList m.funcs
  have h₇ := nh_natList m.datas
  have h₈ := nh_natList m.elems
  have h₉ : NH (.list (m.exports.map exportInstToValue)) :=
    noAtoms_list_map fun e _ => nh_exportInst e
  simp only [moduleInstToValue]
  nh_close

theorem nh_frameV (f : Frame) : NH (Sim.frameV f) := by
  have h₁ : NH (.list (f.locals.map fun o => .opt (o.map Sim.valV))) :=
    noAtoms_list_map fun o _ => noAtoms_opt_map fun v _ => nh_valV v
  have h₂ := nh_moduleInst f.module
  simp only [Sim.frameV]
  nh_close

/-! ## The instance records of the store, other than function instances -/

theorem nh_tagInst (t : TagInst) : NH (tagInstToValue Sim.CT t) := by
  have h := nh_defType t.type
  simp only [tagInstToValue]
  nh_close

theorem nh_globalInst (g : GlobalInst) : NH (Sim.globalInstV g) := by
  have h₁ := nh_globalType g.type
  have h₂ := nh_valV g.value
  simp only [Sim.globalInstV]
  nh_close

theorem nh_memInst (m : MemInst) : NH (memInstToValue m) := by
  have h₁ := nh_memType m.type
  have h₂ := nh_bytes m.bytes
  simp only [memInstToValue]
  nh_close

theorem nh_tableInst (t : TableInst) : NH (tableInstToValue Sim.CT t) := by
  have h₁ := nh_tableType t.type
  have h₂ : NH (.list (t.refs.map refToValue)) := noAtoms_list_map fun r _ => nh_refToValue r
  simp only [tableInstToValue]
  nh_close

theorem nh_dataInst (d : DataInst) : NH (dataInstToValue d) := by
  have h := nh_bytes d.bytes
  simp only [dataInstToValue]
  nh_close

theorem nh_elemInst (e : ElemInst) : NH (elemInstToValue Sim.CT e) := by
  have h₁ := nh_elemType e.type
  have h₂ : NH (.list (e.refs.map refToValue)) := noAtoms_list_map fun r _ => nh_refToValue r
  simp only [elemInstToValue]
  nh_close

theorem nh_structInst (s : StructInst) : NH (Sim.structInstV s) := by
  have h₁ := nh_defType s.type
  have h₂ : NH (.list (s.fields.map Sim.fieldValV)) :=
    noAtoms_list_map fun v _ => nh_fieldValV v
  simp only [Sim.structInstV]
  nh_close

theorem nh_arrayInst (a : ArrayInst) : NH (Sim.arrayInstV a) := by
  have h₁ := nh_defType a.type
  have h₂ : NH (.list (a.fields.map Sim.fieldValV)) :=
    noAtoms_list_map fun v _ => nh_fieldValV v
  simp only [Sim.arrayInstV]
  nh_close

theorem nh_exnInst (e : ExnInst) : NH (Sim.exnInstV e) := by
  have h : NH (.list (e.fields.map Sim.valV)) := noAtoms_list_map fun v _ => nh_valV v
  simp only [Sim.exnInstV]
  nh_close

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
