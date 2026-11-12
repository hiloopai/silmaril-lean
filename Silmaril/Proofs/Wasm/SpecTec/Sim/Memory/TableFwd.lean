module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Table

/-!
# The remaining table rules, at the Core encoding

Each `fwd_table*` has the type of the matching `TableStep` case of `Forward.table` at
`simEnv B`, plus, where Core's bit-vector arithmetic could wrap, the no-wrap hypothesis `hw`
(gap G1 of `docs/projects/spectec/README.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)

variable {H : Type}

/-! ## Encoding facts -/

/-- A forward obligation discharged by a `Step_read` step of the images, given the typed source
configuration. -/
theorem fwd_of_sread' {env : Env} {hn : H → String} (T : TypingFacts env hn)
    (hr : HasRuleAt env "Step" "%~>%" 1 Equiv.ExecStepRules.readRule) {s : Store H} {f : Frame}
    {is is' : List Admin}
    (hp : Typed env hn ⟨s, f, is⟩ → SRead env (configV hn ⟨s, f, is⟩) (adminsToV is')) :
    FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨-, hcode'⟩ := (T.config _).1 hc'
  exact sstep_read hr hst hcode hcode' (hp hc)

/-- The encoded element segment the module lists at `y`. -/
theorem elemAt_of_elem? (hn : H → String) {s : Store H} {f : Frame} {y : ElemIdx} {a : Nat}
    {e : ElemInst} (h : s.elem? f y = some (a, e)) :
    ElemAt (storeV hn s) (frameV f) y.toNat (elemInstToValue CT e) := by
  obtain ⟨ha, he⟩ := State.Store.elem?_eq_some h
  exact ⟨_, _, _, a, State.storeV_ELEMS hn s, State.frameV_MODULE f, State.moduleV_ELEMS _,
    State.getElem?_map_natN ha, by simp [he]⟩

@[simp] theorem elemInstV_REFS (e : ElemInst) :
    (elemInstToValue CT e).field? "REFS" = some (.list (e.refs.map refToValue)) := rfl

@[simp] theorem tableInstV_TYPE (t : TableInst) :
    (tableInstToValue CT t).field? "TYPE" = some (.case "%%%" (.tuple [
      Encode.toValue t.type.address, Encode.toValue t.type.limits,
      Silmaril.SpecTec.Equiv.Validation.tyV t.type.element])) := rfl

/-- An `i32` constant encodes as `CONST I32 (% j)`. -/
theorem adminToV_constI32 (j : BitVec 32) : adminToV (constI32 j) = aconstV i32V j.toNat := rfl

/-- `(P - 1 + (m + k)) mod P = m + k - 1` for `0 < k` and `m + k ≤ P`. -/
theorem mod_pred_aux {P m k : Nat} (hk : k ≠ 0) (hw : m + k ≤ P) :
    (P - 1 + (m + k)) % P = m + k - 1 := by
  rw [show P - 1 + (m + k) = (m + k - 1) + P by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- `i + ofNat n - 1` without wrap, as `table.copy-gt` and `memory.copy-gt` compute it. -/
theorem toNat_add_ofNat_sub_one {w : Nat} (i : BitVec w) {k : Nat} (hk : k ≠ 0)
    (hw : i.toNat + k ≤ 2 ^ w) : (i + BitVec.ofNat w k - 1).toNat = i.toNat + k - 1 := by
  have hi := i.isLt
  have h1 : (1 : BitVec w).toNat = 1 % 2 ^ w := BitVec.toNat_ofNat 1 w
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1, Nat.add_mod_mod]
  generalize 2 ^ w = P at *
  generalize i.toNat = m at *
  rcases Nat.lt_or_ge 1 P with hP | hP
  · rw [Nat.mod_eq_of_lt hP, ← Nat.add_assoc, Nat.add_mod_mod, Nat.add_assoc]
    exact mod_pred_aux hk hw
  · obtain rfl : P = 1 := by omega
    simp only [Nat.mod_one]
    omega

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B))
include T St

/-! ## `table.size` -/

/-- `TableStep.size`, forward, for a table shorter than `2 ^ |at|`. -/
theorem fwd_tableSize (M : MemTyping (simEnv B)) {s : Store H} {f : Frame} {x : TableIdx}
    {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
    (hw : ti.refs.length < 2 ^ ti.type.address.intType.width) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.tableSize x)]⟩
      ⟨s, f, [aconst ti.type.address (BitVec.ofNat _ ti.refs.length)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  obtain ⟨-, hti⟩ := State.Store.table?_eq_some ht
  obtain ⟨hL, hRT⟩ := M.tableType hn s f ti (List.mem_of_getElem? hti) (State.typedV_state T hc)
  have h := sread_tableSize (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableSize (State.typedV_state T hc) x.value.isLt hL hRT
    (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti) (tableInstV_TYPE ti)
  rw [List.length_map] at h
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    toNat_ofNat_of_lt hw]
  exact h

/-! ## `table.fill` -/

/-- `TableStep.fillZero`, forward. -/
theorem fwd_tableFillZero {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (h : i.toNat ≤ ti.refs.length) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a 0, .plain (.tableFill x)]⟩
      ⟨s, f, []⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hv := State.typedV_val_of_mem T hc (v := v) (by simp)
  have hs := sread_tableFillZero (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableFillZero (State.hasReadRules_simEnv B).tableFillOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x.value.isLt hv
    (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin]
  exact hs

/-- `TableStep.fillSucc`, forward, when `i + 1` does not wrap. -/
theorem fwd_tableFillSucc {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i n : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (h : i.toNat + n.toNat ≤ ti.refs.length) (hnz : n ≠ 0)
    (hw : i.toNat + 1 < 2 ^ a.intType.width) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.tableFill x)]⟩
      ⟨s, f, [aconst a i, v.toAdmin, .plain (.tableSet x),
        aconst a (i + 1), v.toAdmin, aconst a (n - 1), .plain (.tableFill x)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hv := State.typedV_val_of_mem T hc (v := v) (by simp)
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_tableFillSucc (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableFillSucc (State.hasReadRules_simEnv B).tableFillOob
    (State.hasReadRules_simEnv B).tableFillZero (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x.value.isLt hv (State.tableAt_of_table? hn ht)
    (State.tableInstV_REFS ti) (by simpa using h) hn0
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin, toNat_add_one hw, toNat_sub_one hnz]
  exact hs

/-! ## `table.copy` -/

/-- `TableStep.copyOob`, forward. -/
theorem fwd_tableCopyOob {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (h : ti₁.refs.length < i₁.toNat + n.toNat ∨ ti₂.refs.length < i₂.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩
      ⟨s, f, [.trap]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_tableCopyOob (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableCopyOob (State.typedV_state T hc) x₁.value.isLt
    x₂.value.isLt (State.tableAt_of_table? hn h₁) (State.tableInstV_REFS ti₁)
    (State.tableAt_of_table? hn h₂) (State.tableInstV_REFS ti₂) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `TableStep.copyZero`, forward. -/
theorem fwd_tableCopyZero {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width}
    {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (h : i₁.toNat ≤ ti₁.refs.length ∧ i₂.toNat ≤ ti₂.refs.length) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' 0, .plain (.tableCopy x₁ x₂)]⟩
      ⟨s, f, []⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_tableCopyZero (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableCopyZero (State.hasReadRules_simEnv B).tableCopyOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x₁.value.isLt
    x₂.value.isLt (State.tableAt_of_table? hn h₁) (State.tableInstV_REFS ti₁)
    (State.tableAt_of_table? hn h₂) (State.tableInstV_REFS ti₂) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `TableStep.copyLe`, forward, when neither `i₁ + 1` nor `i₂ + 1` wraps. -/
theorem fwd_tableCopyLe {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (h : i₁.toNat + n.toNat ≤ ti₁.refs.length ∧ i₂.toNat + n.toNat ≤ ti₂.refs.length)
    (hnz : n ≠ 0) (hle : i₁.toNat ≤ i₂.toNat)
    (hw : i₁.toNat + 1 < 2 ^ a₁.intType.width ∧ i₂.toNat + 1 < 2 ^ a₂.intType.width) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩
      ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, .plain (.tableGet x₂), .plain (.tableSet x₁),
        aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1), .plain (.tableCopy x₁ x₂)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_tableCopyLe (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableCopyLe (State.hasReadRules_simEnv B).tableCopyOob
    (State.hasReadRules_simEnv B).tableCopyZero (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x₁.value.isLt x₂.value.isLt (State.tableAt_of_table? hn h₁)
    (State.tableInstV_REFS ti₁) (State.tableAt_of_table? hn h₂) (State.tableInstV_REFS ti₂)
    (by simpa using h) hn0 hle
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    toNat_add_one hw.1, toNat_add_one hw.2, toNat_sub_one hnz]
  exact hs

/-- `TableStep.copyGt`, forward, when `i₁ + n - 1` and `i₂ + n - 1` do not wrap. -/
theorem fwd_tableCopyGt {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (h : i₁.toNat + n.toNat ≤ ti₁.refs.length ∧ i₂.toNat + n.toNat ≤ ti₂.refs.length)
    (hnz : n ≠ 0) (hgt : i₂.toNat < i₁.toNat)
    (hw : i₁.toNat + n.toNat ≤ 2 ^ a₁.intType.width ∧ i₂.toNat + n.toNat ≤ 2 ^ a₂.intType.width) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩
      ⟨s, f, [aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1), aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1),
        .plain (.tableGet x₂), .plain (.tableSet x₁),
        aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1), .plain (.tableCopy x₁ x₂)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_tableCopyGt (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableCopyGt (State.hasReadRules_simEnv B).tableCopyOob
    (State.hasReadRules_simEnv B).tableCopyZero (State.hasReadRules_simEnv B).tableCopyLe
    (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x₁.value.isLt x₂.value.isLt (State.tableAt_of_table? hn h₁)
    (State.tableInstV_REFS ti₁) (State.tableAt_of_table? hn h₂) (State.tableInstV_REFS ti₂)
    (by simpa using h) hn0 hgt
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    toNat_add_ofNat_sub_one i₁ hn0 hw.1, toNat_add_ofNat_sub_one i₂ hn0 hw.2,
    toNat_sub_one hnz]
  exact hs

/-! ## `table.init` -/

/-- `TableStep.initOob`, forward. -/
theorem fwd_tableInitOob {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
    (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
    (h : ti.refs.length < i.toNat + n.toNat ∨ ei.refs.length < j.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩
      ⟨s, f, [.trap]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_tableInitOob (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableInitOob (State.typedV_state T hc) x.value.isLt
    y.value.isLt (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti)
    (elemAt_of_elem? hn he) (elemInstV_REFS ei) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    adminToV_constI32]
  exact hs

/-- `TableStep.initZero`, forward. -/
theorem fwd_tableInitZero {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
    (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
    (h : i.toNat ≤ ti.refs.length ∧ j.toNat ≤ ei.refs.length) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 0, .plain (.tableInit x y)]⟩
      ⟨s, f, []⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_tableInitZero (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableInitZero (State.hasReadRules_simEnv B).tableInitOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x.value.isLt
    y.value.isLt (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti)
    (elemAt_of_elem? hn he) (elemInstV_REFS ei) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    adminToV_constI32]
  exact hs

/-- `TableStep.initSucc`, forward, when neither `i + 1` nor `j + 1` wraps. -/
theorem fwd_tableInitSucc {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
    {r : Ref}
    (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
    (h : i.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length)
    (hnz : n ≠ 0) (hr : ei.refs[j.toNat]? = some r)
    (hw : i.toNat + 1 < 2 ^ a.intType.width ∧ j.toNat + 1 < 2 ^ 32) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩
      ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x),
        aconst a (i + 1), constI32 (j + 1), constI32 (n - 1), .plain (.tableInit x y)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_tableInitSucc (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableInitSucc (State.hasReadRules_simEnv B).tableInitOob
    (State.hasReadRules_simEnv B).tableInitZero (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x.value.isLt y.value.isLt (State.tableAt_of_table? hn ht)
    (State.tableInstV_REFS ti) (elemAt_of_elem? hn he) (elemInstV_REFS ei) (by simpa using h)
    hn0 (R := refToValue r) (by simp [hr])
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    adminToV_constI32, State.adminToV_ref, toNat_add_one hw.1, toNat_add_one hw.2,
    toNat_sub_one hnz]
  exact hs

end Silmaril.Wasm.SpecTec.Sim.Memory
