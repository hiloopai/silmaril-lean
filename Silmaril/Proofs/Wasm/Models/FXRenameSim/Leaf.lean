module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.Store

/-!
# Exception renaming: the variable, reference, table and memory families

Each rule of `VariableStep`, `RefStep`, `TableStep P` and `MemoryStep P` is matched, under
`ExnRen n s t`, by the same rule on the renamed configuration `⟨t, rnFrame n f, rnAdmins n code⟩`,
reaching the renamed successor over an `ExnRen n` store:

* `variable_rn`: locals and globals hold renamed values;
* `reference_rn`: `ref.eq` uses that the renaming is injective, the casts and tests use
  `refOk_iff`;
* `table_rn'`: tables and element segments hold renamed references (growth through
  `grow?_rn`);
* `memory_rn`: memories and data segments are not renamed; `memory.fill` carries a renamed
  value.

The structure of the proofs follows `Silmaril.Proofs.Wasm.Game.SpecGlobals.Leaf`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename

variable {H : Type} {P : Profile} {n : Nat} {s t s' : Store H} {f f' : Frame}
  {code out : List Admin}

@[simp] theorem rnVal_num (v : NumVal) : rnVal n (.num v) = .num v := rfl
@[simp] theorem rnVal_vec (b : BitVec 128) : rnVal n (.vec b) = .vec b := rfl
@[simp] theorem rnAdmin_store8 (x : MemIdx) : rnAdmin n (store8 x) = store8 x := rfl
@[simp] theorem rnAdmin_load8u (x : MemIdx) : rnAdmin n (load8u x) = load8u x := rfl
@[simp] theorem rnAdmin_aconst (a : AddrType) (i : BitVec a.intType.width) :
    rnAdmin n (aconst a i) = aconst a i := rfl

/-- Normalise the renaming on the code shapes of the reduction rules. -/
macro "rn_simp" : tactic => `(tactic| (try simp only [rnAdmins_cons, rnAdmins_nil,
  rnAdmin_plain, rnAdmin_trap, rnAdmin_ref, rnAdmin_constI32, rnAdmin_toAdmin', rnAdmins_append',
  rnAdmins_vals', rnAdmins_expression', rnRef_null, rnRef_func, rnRef_struct, rnRef_array,
  rnRef_i31, rnRef_exn, rnRef_extern, rnAdmin_label, rnAdmin_handler, rnAdmin_frame,
  rnAdmin_callRefType, rnAdmin_returnCallRefType, rnVal_num, rnVal_vec, rnVal_ref,
  rnAdmin_store8, rnAdmin_load8u, rnAdmin_aconst, List.map_cons, List.map_nil]))

@[simp] theorem rnTable_refs_length (ti : TableInst) :
    (rnTable n ti).refs.length = ti.refs.length := by
  simp [rnTable]

@[simp] theorem rnElem_refs_length (ei : ElemInst) :
    (rnElem n ei).refs.length = ei.refs.length := by
  simp [rnElem]

@[simp] theorem rnTable_type (ti : TableInst) : (rnTable n ti).type = ti.type := rfl

theorem rnTable_refs_get {ti : TableInst} {i : Nat} {r : Ref} (h : ti.refs[i]? = some r) :
    (rnTable n ti).refs[i]? = some (rnRef n r) := by
  simp [rnTable, h]

theorem rnElem_refs_get {ei : ElemInst} {i : Nat} {r : Ref} (h : ei.refs[i]? = some r) :
    (rnElem n ei).refs[i]? = some (rnRef n r) := by
  simp [rnElem, h]

theorem grow?_rn (ti : TableInst) (k : Nat) (r : Ref) :
    (rnTable n ti).grow? k (rnRef n r) = (ti.grow? k r).map (rnTable n) := by
  unfold TableInst.grow?
  simp only [rnTable_refs_length, rnTable_type]
  split
  · simp [rnTable, List.map_replicate]
  · rfl

theorem rnTable_set (ti : TableInst) (i : Nat) (r : Ref) :
    rnTable n { ti with refs := ti.refs.set i r } =
      { rnTable n ti with refs := (rnTable n ti).refs.set i (rnRef n r) } := by
  simp [rnTable, List.map_set]

theorem tableSize_rn (h : ExnRen n s t) {x : TableIdx} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) :
    TableStep P ⟨t, rnFrame n f, rnAdmins n [.plain (.tableSize x)]⟩
      ⟨t, rnFrame n f, rnAdmins n [aconst ti.type.address (BitVec.ofNat _ ti.refs.length)]⟩ := by
  have hs := TableStep.size (P := P) (table_rn h ht)
  rn_simp
  simpa using hs

theorem tableGrowSucceed_rn (h : ExnRen n s t) {x : TableIdx} {a : AddrType}
    {k : BitVec a.intType.width} {r : Ref} {ta : Nat} {ti ti' : TableInst}
    (ht : s.table? f x = some (ta, ti)) (hg : ti.grow? k.toNat r = some ti')
    (hp : P.growMaySucceed .table ta ti.refs.length k.toNat) :
    TableStep P ⟨t, rnFrame n f, rnAdmins n [.ref r, aconst a k, .plain (.tableGrow x)]⟩
      ⟨t.setTable ta (rnTable n ti'), rnFrame n f,
        rnAdmins n [aconst a (BitVec.ofNat _ ti.refs.length)]⟩ := by
  have hs := TableStep.growSucceed (P := P) (table_rn h ht)
    (by rw [grow?_rn, hg]; rfl) (by simpa using hp)
  rn_simp
  simpa using hs

theorem tableGrowFail_rn (h : ExnRen n s t) {x : TableIdx} {a : AddrType}
    {k : BitVec a.intType.width} {r : Ref} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti))
    (hp : P.growMayFail .table ta ti.refs.length k.toNat ∨ ti.grow? k.toNat r = none) :
    TableStep P ⟨t, rnFrame n f, rnAdmins n [.ref r, aconst a k, .plain (.tableGrow x)]⟩
      ⟨t, rnFrame n f, rnAdmins n [aconst a (BitVec.allOnes _)]⟩ := by
  have hs := TableStep.growFail (P := P) (r := rnRef n r) (n := k) (table_rn h ht)
    (by rw [grow?_rn]; simpa using hp)
  rn_simp
  simpa using hs

/-! ## Variables -/

theorem variable_rn (h : ExnRen n s t) (step : VariableStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    ∃ t', VariableStep ⟨t, rnFrame n f, rnAdmins n code⟩ ⟨t', rnFrame n f', rnAdmins n out⟩ ∧
      ExnRen n s' t' := by
  cases step with
  | localGet hl =>
    refine ⟨t, ?_, h⟩
    rn_simp
    exact .localGet (by rw [rnFrame_local?, hl]; rfl)
  | localSet hx =>
    refine ⟨t, ?_, h⟩
    rn_simp
    rw [rnFrame_setLocal]
    exact .localSet (by rwa [rnFrame_locals_length])
  | localTee =>
    refine ⟨t, ?_, h⟩
    rn_simp
    exact .localTee
  | globalGet hl =>
    refine ⟨t, ?_, h⟩
    rn_simp
    exact .globalGet (global_rn h hl)
  | globalSet hl =>
    refine ⟨_, ?_, setGlobal_rn h _ _⟩
    rn_simp
    exact .globalSet (global_rn h hl)

/-! ## References -/

theorem reference_rn (h : ExnRen n s t) (step : RefStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    ∃ t', RefStep ⟨t, rnFrame n f, rnAdmins n code⟩ ⟨t', rnFrame n f', rnAdmins n out⟩ ∧
      ExnRen n s' t' := by
  refine ⟨t, ?_, ?_⟩
  · show RefStep ⟨t, rnFrame n f, rnAdmins n code⟩ ⟨t, rnFrame n f', rnAdmins n out⟩
    cases step with
    | refNull ht => exact .refNull ht
    | refFunc hf => exact .refFunc hf
    | refI31 i => exact .refI31 i
    | isNullTrue => exact .isNullTrue
    | isNullFalse hn => rn_simp; exact .isNullFalse (by rwa [Ne, rnRef_eq_null])
    | asNonNullNull => exact .asNonNullNull
    | asNonNullAddr hn => rn_simp; exact .asNonNullAddr (by rwa [Ne, rnRef_eq_null])
    | eqNull => exact .eqNull
    | eqTrue hn => rn_simp; exact .eqTrue (by rwa [Ne, rnRef_eq_null])
    | eqFalse hn => rn_simp; exact .eqFalse (fun he => hn (rnRef_injective n he))
    | testTrue hv => rn_simp; exact .testTrue (refOk_rn h hv)
    | testFalse hv => rn_simp; exact .testFalse (fun hv' => hv (refOk_rn_back h hv'))
    | castSucceed hv => rn_simp; exact .castSucceed (refOk_rn h hv)
    | castFail hv => rn_simp; exact .castFail (fun hv' => hv (refOk_rn_back h hv'))
    | i31GetNull sx => exact .i31GetNull sx
    | i31GetNum sx i => exact .i31GetNum sx i
    | externConvertNull => exact .externConvertNull
    | externConvertAddr hn => rn_simp; exact .externConvertAddr (by rwa [Ne, rnRef_eq_null])
    | anyConvertNull => exact .anyConvertNull
    | anyConvertAddr r => rn_simp; exact .anyConvertAddr _
  · cases step <;> exact h

/-! ## Tables -/

theorem table_rn' (h : ExnRen n s t) (step : TableStep P ⟨s, f, code⟩ ⟨s', f', out⟩) :
    ∃ t', TableStep P ⟨t, rnFrame n f, rnAdmins n code⟩ ⟨t', rnFrame n f', rnAdmins n out⟩ ∧
      ExnRen n s' t' := by
  cases step with
  | getOob ht hb => exact ⟨t, .getOob (table_rn h ht) (by simpa using hb), h⟩
  | getVal ht hr =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .getVal (table_rn h ht) (rnTable_refs_get hr)
  | setOob ht hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .setOob (table_rn h ht) (by simpa using hb)
  | setVal ht hb =>
    refine ⟨_, ?_, setTable_rn h _ _⟩; rn_simp
    rw [rnTable_set]
    exact .setVal (table_rn h ht) (by simpa using hb)
  | size ht => exact ⟨t, tableSize_rn h ht, h⟩
  | growSucceed ht hg hp => exact ⟨_, tableGrowSucceed_rn h ht hg hp, setTable_rn h _ _⟩
  | growFail ht hp => exact ⟨t, tableGrowFail_rn h ht hp, h⟩
  | fillOob ht hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .fillOob (table_rn h ht) (by simpa using hb)
  | fillZero ht hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .fillZero (table_rn h ht) (by simpa using hb)
  | fillSucc ht hb hn =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .fillSucc (table_rn h ht) (by simpa using hb) hn
  | copyOob h₁ h₂ hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .copyOob (table_rn h h₁) (table_rn h h₂) (by simpa using hb)
  | copyZero h₁ h₂ hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .copyZero (table_rn h h₁) (table_rn h h₂) (by simpa using hb)
  | copyLe h₁ h₂ hb hn hle =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .copyLe (table_rn h h₁) (table_rn h h₂) (by simpa using hb) hn hle
  | copyGt h₁ h₂ hb hn hgt =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .copyGt (table_rn h h₁) (table_rn h h₂) (by simpa using hb) hn hgt
  | initOob ht he hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .initOob (table_rn h ht) (elem_rn h he) (by simpa using hb)
  | initZero ht he hb =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .initZero (table_rn h ht) (elem_rn h he) (by simpa using hb)
  | initSucc ht he hb hn hr =>
    refine ⟨t, ?_, h⟩; rn_simp
    exact .initSucc (table_rn h ht) (elem_rn h he) (by simpa using hb) hn (rnElem_refs_get hr)
  | elemDrop he =>
    refine ⟨_, ?_, setElem_rn h _ []⟩
    exact .elemDrop (elem_rn h he)

/-! ## Memories -/

theorem memory_rn (h : ExnRen n s t) (step : MemoryStep P ⟨s, f, code⟩ ⟨s', f', out⟩) :
    ∃ t', MemoryStep P ⟨t, rnFrame n f, rnAdmins n code⟩ ⟨t', rnFrame n f', rnAdmins n out⟩ ∧
      ExnRen n s' t' := by
  cases step with
  | loadIntOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .loadIntOob (mem_rn h hm) hb
  | loadIntVal hm hl => refine ⟨t, ?_, h⟩; rn_simp; exact .loadIntVal (mem_rn h hm) hl
  | loadPackOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .loadPackOob (mem_rn h hm) hb
  | loadPackVal hm hl => refine ⟨t, ?_, h⟩; rn_simp; exact .loadPackVal (mem_rn h hm) hl
  | loadFloatOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .loadFloatOob (mem_rn h hm) hb
  | loadFloatVal hm hl => refine ⟨t, ?_, h⟩; rn_simp; exact .loadFloatVal (mem_rn h hm) hl
  | vecLoadOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .vecLoadOob (mem_rn h hm) hb
  | vecLoadVal hm hl => refine ⟨t, ?_, h⟩; rn_simp; exact .vecLoadVal (mem_rn h hm) hl
  | vecLoadLaneOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .vecLoadLaneOob (mem_rn h hm) hb
  | vecLoadLaneVal hm hl => refine ⟨t, ?_, h⟩; rn_simp; exact .vecLoadLaneVal (mem_rn h hm) hl
  | storeIntOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .storeIntOob (mem_rn h hm) hb
  | storeIntVal hm hs =>
    refine ⟨_, ?_, setMem_rn h _ _⟩; rn_simp; exact .storeIntVal (mem_rn h hm) hs
  | storePackOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .storePackOob (mem_rn h hm) hb
  | storePackVal hm hs =>
    refine ⟨_, ?_, setMem_rn h _ _⟩; rn_simp; exact .storePackVal (mem_rn h hm) hs
  | storeFloatOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .storeFloatOob (mem_rn h hm) hb
  | storeFloatVal hm hs =>
    refine ⟨_, ?_, setMem_rn h _ _⟩; rn_simp; exact .storeFloatVal (mem_rn h hm) hs
  | vecStoreOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .vecStoreOob (mem_rn h hm) hb
  | vecStoreVal hm hs =>
    refine ⟨_, ?_, setMem_rn h _ _⟩; rn_simp; exact .vecStoreVal (mem_rn h hm) hs
  | vecStoreLaneOob hm hb =>
    refine ⟨t, ?_, h⟩; rn_simp; exact .vecStoreLaneOob (mem_rn h hm) hb
  | vecStoreLaneVal hm hs =>
    refine ⟨_, ?_, setMem_rn h _ _⟩; rn_simp; exact .vecStoreLaneVal (mem_rn h hm) hs
  | size hm => refine ⟨t, ?_, h⟩; rn_simp; exact .size (mem_rn h hm)
  | growSucceed hm hg hp =>
    refine ⟨_, ?_, setMem_rn h _ _⟩; rn_simp; exact .growSucceed (mem_rn h hm) hg hp
  | growFail hm hp => refine ⟨t, ?_, h⟩; rn_simp; exact .growFail (mem_rn h hm) hp
  | fillOob hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .fillOob (mem_rn h hm) hb
  | fillZero hm hb => refine ⟨t, ?_, h⟩; rn_simp; exact .fillZero (mem_rn h hm) hb
  | fillSucc hm hb hn => refine ⟨t, ?_, h⟩; rn_simp; exact .fillSucc (mem_rn h hm) hb hn
  | copyOob h₁ h₂ hb =>
    refine ⟨t, ?_, h⟩; rn_simp; exact .copyOob (mem_rn h h₁) (mem_rn h h₂) hb
  | copyZero h₁ h₂ hb =>
    refine ⟨t, ?_, h⟩; rn_simp; exact .copyZero (mem_rn h h₁) (mem_rn h h₂) hb
  | copyLe h₁ h₂ hb hn hle =>
    refine ⟨t, ?_, h⟩; rn_simp; exact .copyLe (mem_rn h h₁) (mem_rn h h₂) hb hn hle
  | copyGt h₁ h₂ hb hn hgt =>
    refine ⟨t, ?_, h⟩; rn_simp; exact .copyGt (mem_rn h h₁) (mem_rn h h₂) hb hn hgt
  | initOob hm hd hb =>
    refine ⟨t, ?_, h⟩; rn_simp; exact .initOob (mem_rn h hm) (data_rn h hd) hb
  | initZero hm hd hb =>
    refine ⟨t, ?_, h⟩; rn_simp; exact .initZero (mem_rn h hm) (data_rn h hd) hb
  | initSucc hm hd hb hn hby =>
    refine ⟨t, ?_, h⟩; rn_simp; exact .initSucc (mem_rn h hm) (data_rn h hd) hb hn hby
  | dataDrop hd =>
    refine ⟨_, ?_, setData_rn h _ _⟩; rn_simp; exact .dataDrop (data_rn h hd)

end Silmaril.Proofs.Wasm.Models.FXRenameSim
