module

public import Silmaril.Proofs.Wasm.Logic.Iris.Grow

/-!
# The Iris logic of Wasm Core 3.0: tables

`wp_tableGet` and `wp_tableSet`, at any table address type, through the cell of
the accessed entry (which proves the access in bounds).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head)
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The cells of a table entry access. -/
abbrev tabCells (f : Frame) (ta j : Nat) (r : Ref) : List (ILoc × ICell) :=
  [(.frame, .frame f), (.tableElem ta j, .ref r)]

theorem tableElem_of_cells {s : Store H} {f f' : Frame} {ta j : Nat} {r : Ref}
    (h : Cells (tabCells f ta j r) s f') : ∃ ti, s.tables[ta]? = some ti ∧ ti.refs[j]? = some r := by
  have h₁ : cellOf s f' (.tableElem ta j) = some (.ref r) := h (.tableElem ta j, .ref r) (by simp)
  rcases ht : s.tables[ta]? with _ | ti
  · simp [cellOf, ht] at h₁
  · exact ⟨ti, rfl, by simpa [cellOf, ht] using h₁⟩

theorem table?_eq {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (hx : f.module.tables[x.toNat]? = some ta) (ht : s.tables[ta]? = some ti) :
    s.table? f x = some (ta, ti) := by
  simp [Store.table?, hx, ht]

theorem tableGet_progress {vs : List Val} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {r : Ref} {f : Frame}
    (hx : f.module.tables[x.toNat]? = some ta) (s : Store H) (f' : Frame)
    (hc : Cells (tabCells f ta i.toNat r) s f') :
    ∃ (vs' args : List Val) (c₀ : Config H), vs ++ [.num ⟨.int a.intType, i⟩] = vs' ++ args ∧
      Head P s f' args (.plain (.tableGet x)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨ti, hti, hr⟩ := tableElem_of_cells hc
  exact ⟨vs, _, _, rfl, .table (.getVal (table?_eq (hf ▸ hx) hti) hr)⟩

theorem tableGet_inv {vs : List Val} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {r : Ref} {f : Frame} {rest : List Admin}
    (hx : f.module.tables[x.toNat]? = some ta) (s : Store H) (f' : Frame) (vs' args : List Val)
    (c₀ : Config H) (hc : Cells (tabCells f ta i.toNat r) s f')
    (hW : vs ++ [.num ⟨.int a.intType, i⟩] = vs' ++ args)
    (hh : Head P s f' args (.plain (.tableGet x)) c₀) :
    c₀.store = s ∧ c₀.frame = f' ∧ vals vs' ++ c₀.code ++ rest = vals (vs ++ [.ref r]) ++ rest := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨ti, hti, hr⟩ := tableElem_of_cells hc
  obtain ⟨a', i', ta', ti', rfl, ht', hres⟩ := head_tableGet hh
  obtain ⟨rfl, hv⟩ := Hoare.split_one hW
  obtain ⟨rfl, hi⟩ := Hoare.addr_arg_inj hv
  obtain rfl := eq_of_heq hi
  have htt : (ta', ti') = (ta, ti) := Option.some.inj (ht'.symm.trans (hf ▸ table?_eq hx hti))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj htt
  rcases hres with ⟨hlt, -⟩ | ⟨r', hr', rfl⟩
  · have := (List.getElem?_eq_some_iff.mp hr).1
    omega
  · obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
    simp [vals, Val.toAdmin]

theorem tableSet_change {s : Store H} {f : Frame} {ta j : Nat} {ti : TableInst} {r₀ r : Ref}
    (hti : s.tables[ta]? = some ti) (hj : j < ti.refs.length) :
    Change s f (s.setTable ta { ti with refs := ti.refs.set j r }) f (tabCells f ta j r₀)
      (tabCells f ta j r) [] := by
  refine ⟨rfl, by simp, by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rfl
    · exact cellOf_setTable_self hti hj
  · intro l c hl hlc
    have hne : l ≠ .tableElem ta j := fun he => hl (by simp [he])
    rw [cellOf_setTable_ne hti hne]
    exact hlc

theorem tableSet_progress {vs : List Val} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {r₀ r : Ref} {f : Frame}
    (hx : f.module.tables[x.toNat]? = some ta) (s : Store H) (f' : Frame)
    (hc : Cells (tabCells f ta i.toNat r₀) s f') :
    ∃ (vs' args : List Val) (c₀ : Config H),
      vs ++ [.num ⟨.int a.intType, i⟩, .ref r] = vs' ++ args ∧
      Head P s f' args (.plain (.tableSet x)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨ti, hti, hr⟩ := tableElem_of_cells hc
  exact ⟨vs, _, _, rfl,
    .table (.setVal (table?_eq (hf ▸ hx) hti) (List.getElem?_eq_some_iff.mp hr).1)⟩

theorem tableSet_inv {vs : List Val} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {r₀ r : Ref} {f : Frame} {rest : List Admin}
    (hx : f.module.tables[x.toNat]? = some ta) (s : Store H) (f' : Frame) (vs' args : List Val)
    (c₀ : Config H) (hc : Cells (tabCells f ta i.toNat r₀) s f')
    (hW : vs ++ [.num ⟨.int a.intType, i⟩, .ref r] = vs' ++ args)
    (hh : Head P s f' args (.plain (.tableSet x)) c₀) :
    vals vs' ++ c₀.code ++ rest = vals vs ++ rest ∧
      Change s f' c₀.store c₀.frame (tabCells f ta i.toNat r₀) (tabCells f ta i.toNat r) [] := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨ti, hti, hr⟩ := tableElem_of_cells hc
  obtain ⟨a', i', r', ta', ti', rfl, ht', hres⟩ := head_tableSet hh
  obtain ⟨rfl, hv, hv'⟩ := Hoare.split_two hW
  obtain ⟨rfl, hi⟩ := Hoare.addr_arg_inj hv
  obtain rfl := eq_of_heq hi
  obtain rfl : r' = r := by simpa using hv'
  have htt : (ta', ti') = (ta, ti) := Option.some.inj (ht'.symm.trans (hf ▸ table?_eq hx hti))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj htt
  have hj : i'.toNat < ti'.refs.length := (List.getElem?_eq_some_iff.mp hr).1
  rcases hres with ⟨hlt, -⟩ | ⟨-, rfl⟩
  · omega
  · exact ⟨by simp, hf ▸ tableSet_change hti hj⟩

section Rules

variable {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-- **`table.get`** (any table address type). -/
theorem wp_tableGet {E : CoPset} {vs : List Val} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {r : Ref} {rest : List Admin} {f : Frame}
    {Φ : Res H → IProp GF} (hx : f.module.tables[x.toNat]? = some ta) :
    ownFrame f ∗ ownTableElem ta i.toNat r ∗ ▷ (ownFrame f ∗ ownTableElem ta i.toNat r -∗
      WP (IExpr.run (vals (vs ++ [.ref r]) ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (vs ++ [.num ⟨.int a.intType, i⟩]) ++ .plain (.tableGet x) :: rest) :
        IExpr P host) @ E {{ Φ }} := by
  simpa only [tabCells, ownCells_two, sep_assoc.to_eq] using
    wp_head_read (P := P) (host := host) (E := E) (Φ := Φ) (tabCells f ta i.toNat r)
      ⟨rfl, by simp, rfl⟩ (tableGet_progress hx) (tableGet_inv hx)

/-- **`table.set`** (any table address type). -/
theorem wp_tableSet {E : CoPset} {vs : List Val} {x : TableIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {r₀ r : Ref} {rest : List Admin} {f : Frame}
    {Φ : Res H → IProp GF} (hx : f.module.tables[x.toNat]? = some ta) :
    ownFrame f ∗ ownTableElem ta i.toNat r₀ ∗ ▷ (ownFrame f ∗ ownTableElem ta i.toNat r -∗
      WP (IExpr.run (vals vs ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (vs ++ [.num ⟨.int a.intType, i⟩, .ref r]) ++ .plain (.tableSet x) ::
        rest) : IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hf, Ht, H⟩
  iapply wp_head_change (tabCells f ta i.toNat r₀) (tabCells f ta i.toNat r) (fun _ => [])
    (fun _ => vals vs ++ rest) ⟨rfl, by simp, rfl⟩ (tableSet_progress hx) (tableSet_inv hx)
  simp only [tabCells, ownCells_two, ownCells_nil]
  iframe Hf Ht
  iintro !> %_ Hc -
  iapply H $$ Hc

end Rules

end Silmaril.Wasm.Logic.IrisWasm
