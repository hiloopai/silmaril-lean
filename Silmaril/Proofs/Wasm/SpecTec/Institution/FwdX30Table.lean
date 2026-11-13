module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# The forward direction at wasm-3.0, extended: the table rules of `Step_read`

Every `TableStep` whose instruction is a `Step_read` instruction (`tableReadInstr`) is a
`Step_read` fact of the declarative reading, at a typed source configuration whose tables and
element segments have fewer than `2 ^ 32` entries (`Memory.TablesBounded`, part 's
`Bounded`).

The `sreadL_*` lemmas are the bodies of the memory forward leaves (`Memory.fwd_table*`,
`State.fwd_tableGet*`, `State.fwd_tableFillOob`), stopped before the leaf lifts the fact to
`Step` with `Step/read`. `sread_of_tableStep` is `Memory.fwd_table_bounded` with the `Step`
cases (`table.set`, `table.grow`, `elem.drop`) excluded by the instruction.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Memory
open State (aconstV idxV)

variable {H : Type}

/-- A code whose last instruction fails `p` is not `LastIs p`. -/
theorem not_lastIs {p : Instr → Bool} {is : List Admin} {j : Instr}
    (h : is.getLast? = some (.plain j)) (hj : p j = false) : ¬ LastIs p is := by
  rintro ⟨i, hi, hp⟩
  have hij : Admin.plain i = Admin.plain j := Option.some.inj (hi.symm.trans h)
  have hij' : i = j := Admin.plain.inj hij
  rw [hij', hj] at hp
  exact Bool.false_ne_true hp

section Leaves

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B))
include T St

/-- `State.fwd_tableGetOob`, before the lift. -/
theorem sreadL_tableGetOob {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
    (h : ti.refs.length ≤ i.toNat)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.tableGet x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.tableGet x)]⟩)
      (adminsToV [.trap]) := by
  have hs := State.sread_tableGetOob (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableGetOob (State.typedV_state T hc) x.value.isLt
    (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst, State.adminToV_trap]
  exact hs

/-- `State.fwd_tableGetVal`, before the lift. -/
theorem sreadL_tableGetVal {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {ti : TableInst} {r : Ref}
    (ht : s.table? f x = some (ta, ti)) (h : ti.refs[i.toNat]? = some r)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.tableGet x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.tableGet x)]⟩)
      (adminsToV [.ref r]) := by
  have hs := State.sread_tableGetVal (a := a) (i := i) (R := refToValue r)
    (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableGetVal (State.typedV_state T hc) x.value.isLt
    (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti) (by simp [h])
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst, State.adminToV_ref]
  exact hs

/-- `State.fwd_tableFillOob`, before the lift. -/
theorem sreadL_tableFillOob {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i n : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (h : ti.refs.length < i.toNat + n.toNat)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.tableFill x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.tableFill x)]⟩)
      (adminsToV [.trap]) := by
  have hv : TypedV (simEnv B) valT (valV v) := State.typedV_val_of_mem T hc (by simp)
  have hs := State.sread_tableFillOob (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableFillOob (State.typedV_state T hc) x.value.isLt hv
    (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin, State.adminToV_trap]
  exact hs

/-- `fwd_tableSize`, before the lift. -/
theorem sreadL_tableSize (M : MemTyping (simEnv B)) {s : Store H} {f : Frame} {x : TableIdx}
    {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
    (hw : ti.refs.length < 2 ^ ti.type.address.intType.width)
    (hc : Typed (simEnv B) hn ⟨s, f, [.plain (.tableSize x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [.plain (.tableSize x)]⟩)
      (adminsToV ([aconst ti.type.address (BitVec.ofNat _ ti.refs.length)])) := by
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

/-- `fwd_tableFillZero`, before the lift. -/
theorem sreadL_tableFillZero {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (h : i.toNat ≤ ti.refs.length)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a 0, .plain (.tableFill x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, v.toAdmin, aconst a 0, .plain (.tableFill x)]⟩)
      (adminsToV ([])) := by
  have hv := State.typedV_val_of_mem T hc (v := v) (by simp)
  have hs := sread_tableFillZero (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableFillZero (State.hasReadRules_simEnv B).tableFillOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x.value.isLt hv
    (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin]
  exact hs

/-- `fwd_tableFillSucc`, before the lift. -/
theorem sreadL_tableFillSucc {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
    {i n : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (h : i.toNat + n.toNat ≤ ti.refs.length) (hnz : n ≠ 0)
    (hw : i.toNat + 1 < 2 ^ a.intType.width)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.tableFill x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.tableFill x)]⟩)
      (adminsToV ([aconst a i, v.toAdmin, .plain (.tableSet x),
        aconst a (i + 1), v.toAdmin, aconst a (n - 1), .plain (.tableFill x)])) := by
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

/-- `fwd_tableCopyOob`, before the lift. -/
theorem sreadL_tableCopyOob {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (h : ti₁.refs.length < i₁.toNat + n.toNat ∨ ti₂.refs.length < i₂.toNat + n.toNat)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩)
      (adminsToV ([.trap])) := by
  have hs := sread_tableCopyOob (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableCopyOob (State.typedV_state T hc) x₁.value.isLt
    x₂.value.isLt (State.tableAt_of_table? hn h₁) (State.tableInstV_REFS ti₁)
    (State.tableAt_of_table? hn h₂) (State.tableInstV_REFS ti₂) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `fwd_tableCopyZero`, before the lift. -/
theorem sreadL_tableCopyZero {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width}
    {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (h : i₁.toNat ≤ ti₁.refs.length ∧ i₂.toNat ≤ ti₂.refs.length)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' 0, .plain (.tableCopy x₁ x₂)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' 0, .plain (.tableCopy x₁ x₂)]⟩)
      (adminsToV ([])) := by
  have hs := sread_tableCopyZero (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableCopyZero (State.hasReadRules_simEnv B).tableCopyOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x₁.value.isLt
    x₂.value.isLt (State.tableAt_of_table? hn h₁) (State.tableInstV_REFS ti₁)
    (State.tableAt_of_table? hn h₂) (State.tableInstV_REFS ti₂) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `fwd_tableCopyLe`, before the lift. -/
theorem sreadL_tableCopyLe {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (h : i₁.toNat + n.toNat ≤ ti₁.refs.length ∧ i₂.toNat + n.toNat ≤ ti₂.refs.length)
    (hnz : n ≠ 0) (hle : i₁.toNat ≤ i₂.toNat)
    (hw : i₁.toNat + 1 < 2 ^ a₁.intType.width ∧ i₂.toNat + 1 < 2 ^ a₂.intType.width)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩)
      (adminsToV ([aconst a₁ i₁, aconst a₂ i₂, .plain (.tableGet x₂), .plain (.tableSet x₁),
        aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1), .plain (.tableCopy x₁ x₂)])) := by
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

/-- `fwd_tableCopyGt`, before the lift. -/
theorem sreadL_tableCopyGt {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
    (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (h : i₁.toNat + n.toNat ≤ ti₁.refs.length ∧ i₂.toNat + n.toNat ≤ ti₂.refs.length)
    (hnz : n ≠ 0) (hgt : i₂.toNat < i₁.toNat)
    (hw : i₁.toNat + n.toNat ≤ 2 ^ a₁.intType.width ∧ i₂.toNat + n.toNat ≤ 2 ^ a₂.intType.width)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩)
      (adminsToV ([aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1), aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1),
        .plain (.tableGet x₂), .plain (.tableSet x₁),
        aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1), .plain (.tableCopy x₁ x₂)])) := by
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

/-- `fwd_tableInitOob`, before the lift. -/
theorem sreadL_tableInitOob {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
    (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
    (h : ti.refs.length < i.toNat + n.toNat ∨ ei.refs.length < j.toNat + n.toNat)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩)
      (adminsToV ([.trap])) := by
  have hs := sread_tableInitOob (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableInitOob (State.typedV_state T hc) x.value.isLt
    y.value.isLt (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti)
    (elemAt_of_elem? hn he) (elemInstV_REFS ei) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    Memory.adminToV_constI32]
  exact hs

/-- `fwd_tableInitZero`, before the lift. -/
theorem sreadL_tableInitZero {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
    (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
    (h : i.toNat ≤ ti.refs.length ∧ j.toNat ≤ ei.refs.length)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 0, .plain (.tableInit x y)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, constI32 j, constI32 0, .plain (.tableInit x y)]⟩)
      (adminsToV ([])) := by
  have hs := sread_tableInitZero (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableInitZero (State.hasReadRules_simEnv B).tableInitOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x.value.isLt
    y.value.isLt (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti)
    (elemAt_of_elem? hn he) (elemInstV_REFS ei) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    Memory.adminToV_constI32]
  exact hs

/-- `fwd_tableInitSucc`, before the lift. -/
theorem sreadL_tableInitSucc {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
    {r : Ref}
    (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
    (h : i.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length)
    (hnz : n ≠ 0) (hr : ei.refs[j.toNat]? = some r)
    (hw : i.toNat + 1 < 2 ^ a.intType.width ∧ j.toNat + 1 < 2 ^ 32)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩)
      (adminsToV ([aconst a i, .ref r, .plain (.tableSet x),
        aconst a (i + 1), constI32 (j + 1), constI32 (n - 1), .plain (.tableInit x y)])) := by
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_tableInitSucc (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).tableInitSucc (State.hasReadRules_simEnv B).tableInitOob
    (State.hasReadRules_simEnv B).tableInitZero (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x.value.isLt y.value.isLt (State.tableAt_of_table? hn ht)
    (State.tableInstV_REFS ti) (elemAt_of_elem? hn he) (elemInstV_REFS ei) (by simpa using h)
    hn0 (R := refToValue r) (by simp [hr])
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    Memory.adminToV_constI32, State.adminToV_ref, toNat_add_one hw.1, toNat_add_one hw.2,
    toNat_sub_one hnz]
  exact hs


/-- **The table rules of `Step_read`**: every `TableStep` whose instruction is a `Step_read`
instruction, from a typed configuration with bounded tables, is a `Step_read` fact
(`Memory.fwd_table_bounded` before the lift). -/
theorem sread_of_tableStep (M : MemTyping (simEnv B)) {P : Numerics.Profile} {c c' : Config H}
    (h : TableStep P c c') (hl : LastIs tableReadInstr c.code) (hb : TablesBounded c.store)
    (hc : Typed (simEnv B) hn c) :
    SRead (simEnv B) (configV hn c) (adminsToV c'.code) := by
  cases h with
  | getOob h₁ h₂ => exact sreadL_tableGetOob B T St h₁ h₂ hc
  | getVal h₁ h₂ => exact sreadL_tableGetVal B T St h₁ h₂ hc
  | setOob _ _ => exact absurd hl (not_lastIs rfl rfl)
  | setVal _ _ => exact absurd hl (not_lastIs rfl rfl)
  | size h₁ => exact sreadL_tableSize B T St M h₁ (table_lt hb h₁ _) hc
  | growSucceed _ _ _ => exact absurd hl (not_lastIs rfl rfl)
  | growFail _ _ => exact absurd hl (not_lastIs rfl rfl)
  | fillOob h₁ h₂ => exact sreadL_tableFillOob B T St h₁ h₂ hc
  | fillZero h₁ h₂ => exact sreadL_tableFillZero B T St h₁ h₂ hc
  | @fillSucc s f x a i n v ta ti h₁ h₂ h₃ =>
    have hn0 : n.toNat ≠ 0 := fun h' => h₃ (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact sreadL_tableFillSucc B T St h₁ h₂ h₃ (by have := table_lt hb h₁ a; omega) hc
  | copyOob h₁ h₂ h₃ => exact sreadL_tableCopyOob B T St h₁ h₂ h₃ hc
  | copyZero h₁ h₂ h₃ => exact sreadL_tableCopyZero B T St h₁ h₂ h₃ hc
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ta₁ ta₂ ti₁ ti₂ h₁ h₂ h₃ h₄ h₅ =>
    have hn0 : n.toNat ≠ 0 := fun h' => h₄ (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact sreadL_tableCopyLe B T St h₁ h₂ h₃ h₄ h₅
      ⟨by have := table_lt hb h₁ a₁; omega, by have := table_lt hb h₂ a₂; omega⟩ hc
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ta₁ ta₂ ti₁ ti₂ h₁ h₂ h₃ h₄ h₅ =>
    exact sreadL_tableCopyGt B T St h₁ h₂ h₃ h₄ h₅
      ⟨by have := table_lt hb h₁ a₁; omega, by have := table_lt hb h₂ a₂; omega⟩ hc
  | initOob h₁ h₂ h₃ => exact sreadL_tableInitOob B T St h₁ h₂ h₃ hc
  | initZero h₁ h₂ h₃ => exact sreadL_tableInitZero B T St h₁ h₂ h₃ hc
  | @initSucc s f x y a i j n ta ea ti ei r h₁ h₂ h₃ h₄ h₅ =>
    have hn0 : n.toNat ≠ 0 := fun h' => h₄ (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact sreadL_tableInitSucc B T St h₁ h₂ h₃ h₄ h₅
      ⟨by have := table_lt hb h₁ a; omega, by have := elem_lt hb h₂; omega⟩ hc
  | elemDrop _ => exact absurd hl (not_lastIs rfl rfl)

end Leaves

end Silmaril.Wasm.SpecTec.Institution.FwdX30
