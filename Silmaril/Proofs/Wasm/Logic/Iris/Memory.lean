module

public import Silmaril.Proofs.Wasm.Logic.Iris.Variable

/-!
# The Iris logic of Wasm Core 3.0: linear memory

`wp_intLoad` and `wp_intStore`: full-width integer loads and stores
(`i32.load`, `i64.load`, `i32.store`, `i64.store`) at any address type, so
memory64 memories too, through the byte cells of the accessed range. Owning the
bytes proves the access in bounds, so the trapping steps are excluded.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head)
open Silmaril.Wasm.Logic.Core (bytesAt leNat load_eq store_eq toList_writeBytes getElem?_splice
  storeLE size_store)
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Bytes of a memory -/

theorem intType_bytes_pos (t : IntType) : 0 < t.width / 8 := by
  cases t <;> simp [IntType.width]

theorem cells_tail {s : Store H} {f : Frame} {p : ILoc × ICell} {ps : List (ILoc × ICell)}
    (h : Cells (p :: ps) s f) : Cells ps s f :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem mem?_eq {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (hx : f.module.mems[x.toNat]? = some ma) (hm : s.mems[ma]? = some mi) :
    s.mem? f x = some (ma, mi) := by
  simp [Store.mem?, hx, hm]

/-- Owned bytes give an in-bounds load of their little-endian value. -/
theorem load_of_cells {s : Store H} {f : Frame} {ma p n : Nat} {bs : List UInt8}
    (hn : bs.length = n) (hpos : 0 < n) (h : Cells (idxCells (.byte ma) .byte p bs) s f) :
    ∃ mi, s.mems[ma]? = some mi ∧ p + n ≤ mi.bytes.size ∧
      Memory.load mi.bytes p n = some (BitVec.ofNat (8 * n) (leNat bs)) := by
  subst hn
  obtain ⟨mi, hmi, hb, hbs⟩ := bytes_of_cells (List.ne_nil_of_length_pos hpos) h
  exact ⟨mi, hmi, hb, by rw [load_eq hb, hbs]⟩

/-- The bytes after a store. -/
theorem getElem?_store {B B' : ByteArray} {p n : Nat} {w : BitVec (8 * n)}
    (h : Memory.store B p w = some B') (j : Nat) :
    B'.data.toList[j]? = if p ≤ j ∧ j < p + n then
      (Memory.encodeLE n w.toNat).data.toList[j - p]? else B.data.toList[j]? :=
  Silmaril.Wasm.Logic.Core.getElem?_store h j

/-! ## Loads -/

theorem intLoad_progress {vs : List Val} {t : IntType} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {bs : List UInt8} {f : Frame}
    (hx : f.module.mems[x.toNat]? = some ma) (hn : bs.length = t.width / 8) (s : Store H)
    (f' : Frame)
    (hc : Cells ((.frame, .frame f) :: idxCells (.byte ma) .byte (effAddr i.toNat arg) bs) s f') :
    ∃ (vs' args : List Val) (c₀ : Config H), vs ++ [.num ⟨.int a.intType, i⟩] = vs' ++ args ∧
      Head P s f' args (.plain (.intLoad t none x arg)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨mi, hmi, -, hl⟩ := load_of_cells hn (intType_bytes_pos t) (cells_tail hc)
  exact ⟨vs, _, _, rfl, .memory (.loadIntVal (mem?_eq (hf ▸ hx) hmi) hl)⟩

theorem intLoad_inv {vs : List Val} {t : IntType} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {bs : List UInt8} {f : Frame} {rest : List Admin}
    (hx : f.module.mems[x.toNat]? = some ma) (hn : bs.length = t.width / 8) (s : Store H)
    (f' : Frame) (vs' args : List Val) (c₀ : Config H)
    (hc : Cells ((.frame, .frame f) :: idxCells (.byte ma) .byte (effAddr i.toNat arg) bs) s f')
    (hW : vs ++ [.num ⟨.int a.intType, i⟩] = vs' ++ args)
    (hh : Head P s f' args (.plain (.intLoad t none x arg)) c₀) :
    c₀.store = s ∧ c₀.frame = f' ∧ vals vs' ++ c₀.code ++ rest =
      vals (vs ++ [.num ⟨.int t, (BitVec.ofNat (8 * (t.width / 8)) (leNat bs)).setWidth t.width⟩]) ++
        rest := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨mi, hmi, hb, hl⟩ := load_of_cells hn (intType_bytes_pos t) (cells_tail hc)
  obtain ⟨a', i', ma', mi', rfl, hm', hr⟩ := head_intLoad hh
  obtain ⟨rfl, hv⟩ := Hoare.split_one hW
  obtain ⟨rfl, hi⟩ := Hoare.addr_arg_inj hv
  obtain rfl := eq_of_heq hi
  have hmm : (ma', mi') = (ma, mi) := by rw [hf, mem?_eq hx hmi] at hm'; exact (Option.some.inj hm').symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmm
  rcases hr with ⟨hlt, -⟩ | ⟨c, hc', rfl⟩
  · omega
  · rw [hl] at hc'
    cases hc'
    simp [vals, Val.toAdmin]

/-! ## Stores -/

/-- The cells changed by a store. -/
abbrev storeCells (f : Frame) (ma p : Nat) (bs : List UInt8) : List (ILoc × ICell) :=
  (.frame, .frame f) :: idxCells (.byte ma) .byte p bs

theorem fst_storeCells_nodup (f : Frame) (ma p : Nat) (bs : List UInt8) :
    ((storeCells f ma p bs).map Prod.fst ++ ([] : List (ILoc × ICell)).map Prod.fst).Nodup := by
  have hb : ((idxCells (.byte ma) .byte p bs).map Prod.fst).Nodup :=
    nodup_idxCells (fun _ _ h => by injection h) p bs
  have hf : ILoc.frame ∉ (idxCells (.byte ma) .byte p bs).map Prod.fst := by
    rw [fst_idxCells]; simp
  simp only [storeCells, List.map_cons, List.map_nil, List.append_nil]
  exact List.nodup_cons.mpr ⟨hf, hb⟩

theorem byte_mem_fst {ma p j : Nat} {bs : List UInt8} (hj : p ≤ j ∧ j < p + bs.length) :
    ILoc.byte ma j ∈ (idxCells (.byte ma) .byte p bs).map Prod.fst := by
  rw [fst_idxCells]
  exact List.mem_map.mpr ⟨j, List.mem_range'_1.mpr hj, rfl⟩

/-- The new cells after a store. -/
theorem store_new {s : Store H} {f : Frame} {ma p n : Nat} {mi : MemInst} {B' : ByteArray}
    {w : BitVec (8 * n)} (hm : s.mems[ma]? = some mi) (hs : Memory.store mi.bytes p w = some B') :
    Cells (storeCells f ma p (Memory.encodeLE n w.toNat).data.toList ++ [])
      (s.setMem ma { mi with bytes := B' }) f := by
  intro q hq
  simp only [List.append_nil, List.mem_cons] at hq
  rcases hq with rfl | hq
  · rfl
  · obtain ⟨k, hk, rfl⟩ := mem_idxCells.mp hq
    have hlen : (Memory.encodeLE n w.toNat).data.toList.length = n := by simp
    have hj : p ≤ p + k ∧ p + k < p + n := ⟨by omega, by omega⟩
    show cellOf (s.setMem ma { mi with bytes := B' }) f (.byte ma (p + k)) = _
    rw [cellOf_setMem_byte hm, getElem?_store hs]
    simp only [hj.1, hj.2, and_self, ↓reduceIte, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hk]
    rfl

/-- The other cells after a store are kept. -/
theorem store_old {s : Store H} {f : Frame} {ma p n : Nat} {mi : MemInst} {B' : ByteArray}
    {bs : List UInt8} {w : BitVec (8 * n)} (hm : s.mems[ma]? = some mi) (hn : bs.length = n)
    (hs : Memory.store mi.bytes p w = some B') (l : ILoc) (c : ICell)
    (hl : l ∉ (storeCells f ma p bs).map Prod.fst) (hc : cellOf s f l = some c) :
    cellOf (s.setMem ma { mi with bytes := B' }) f l = some c := by
  by_cases hb : ∃ j, l = .byte ma j
  · obtain ⟨j, rfl⟩ := hb
    have hj : ¬ (p ≤ j ∧ j < p + n) := fun hj =>
      hl (List.mem_cons_of_mem _ (byte_mem_fst (hn ▸ hj)))
    have hold : cellOf s f (.byte ma j) = (mi.bytes.data.toList[j]?).map .byte := by
      simp [cellOf, hm, byteArray_getElem?]
    rw [cellOf_setMem_byte hm, getElem?_store hs, ← hc, hold]
    simp only [hj, ↓reduceIte]
  · have hb' : ∀ j, l ≠ .byte ma j := fun j he => hb ⟨j, he⟩
    by_cases hme : l = .mem ma
    · subst hme
      have hsz : B'.size = mi.bytes.size := size_store hs
      have hold : cellOf s f (.mem ma) = some (.mem mi.type mi.bytes.size) := by simp [cellOf, hm]
      rw [cellOf_setMem_mem hm, ← hc, hold, hsz]
    · rw [cellOf_setMem_other hb' hme]
      exact hc

theorem intStore_progress {vs : List Val} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {bs : List UInt8}
    {f : Frame} (hx : f.module.mems[x.toNat]? = some ma) (hn : bs.length = t.width / 8)
    (s : Store H) (f' : Frame) (hc : Cells (storeCells f ma (effAddr i.toNat arg) bs) s f') :
    ∃ (vs' args : List Val) (c₀ : Config H),
      vs ++ [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩] = vs' ++ args ∧
      Head P s f' args (.plain (.intStore t none x arg)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨mi, hmi, hb, -⟩ := load_of_cells hn (intType_bytes_pos t) (cells_tail hc)
  have hs := store_eq (c.setWidth (8 * (t.width / 8))) hb
  exact ⟨vs, _, _, rfl, .memory (.storeIntVal (mem?_eq (hf ▸ hx) hmi) hs)⟩

theorem intStore_inv {vs : List Val} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma : Nat} {bs : List UInt8}
    {f : Frame} {rest : List Admin} (hx : f.module.mems[x.toNat]? = some ma)
    (hn : bs.length = t.width / 8) (s : Store H) (f' : Frame) (vs' args : List Val) (c₀ : Config H)
    (hc : Cells (storeCells f ma (effAddr i.toNat arg) bs) s f')
    (hW : vs ++ [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩] = vs' ++ args)
    (hh : Head P s f' args (.plain (.intStore t none x arg)) c₀) :
    vals vs' ++ c₀.code ++ rest = vals vs ++ rest ∧
      Change s f' c₀.store c₀.frame (storeCells f ma (effAddr i.toNat arg) bs)
        (storeCells f ma (effAddr i.toNat arg)
          (Memory.encodeLE (t.width / 8) (c.setWidth (8 * (t.width / 8))).toNat).data.toList) [] := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨mi, hmi, hb, -⟩ := load_of_cells hn (intType_bytes_pos t) (cells_tail hc)
  obtain ⟨a', i', c', ma', mi', rfl, hm', hr⟩ := head_intStore hh
  obtain ⟨rfl, hv₁, hv₂⟩ := Hoare.split_two hW
  obtain ⟨rfl, hi⟩ := Hoare.addr_arg_inj hv₁
  obtain rfl := eq_of_heq hi
  obtain rfl : c' = c := Hoare.numVal_int_inj (Val.num.inj hv₂)
  have hmm : (ma', mi') = (ma, mi) := by rw [hf, mem?_eq hx hmi] at hm'; exact (Option.some.inj hm').symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmm
  subst hf
  rcases hr with ⟨hlt, -⟩ | ⟨B', hs, rfl⟩
  · omega
  · refine ⟨by simp, ?_, fst_storeCells_nodup .., by simp, store_new hmi hs,
      store_old hmi hn hs⟩
    simp only [List.map_cons, storeCells]
    exact congrArg (ILoc.frame :: ·) (idxCells_fst_eq _ _ _ _ (by simp [hn]))

section Rules

variable {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-- **Integer loads** (`i32.load`, `i64.load`; any address type, so memory64 too):
the bytes `bs` at the effective address `pa` are read as a little-endian integer. -/
theorem wp_intLoad {E : CoPset} {vs : List Val} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma pa : Nat} {bs : List UInt8}
    {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hx : f.module.mems[x.toNat]? = some ma) (hpa : effAddr i.toNat arg = pa)
    (hn : bs.length = t.width / 8) :
    ownFrame f ∗ ownBytes ma pa bs ∗
      ▷ (ownFrame f ∗ ownBytes ma pa bs -∗
        WP (IExpr.run (vals (vs ++ [.num ⟨.int t,
          (BitVec.ofNat (8 * (t.width / 8)) (leNat bs)).setWidth t.width⟩]) ++ rest) : IExpr P host)
          @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (vs ++ [.num ⟨.int a.intType, i⟩]) ++ .plain (.intLoad t none x arg) ::
        rest) : IExpr P host) @ E {{ Φ }} := by
  subst hpa
  simpa only [ownCells_cons, sep_assoc.to_eq] using
    wp_head_read (P := P) (host := host) (E := E) (Φ := Φ)
      (storeCells f ma (effAddr i.toNat arg) bs) ⟨rfl, by simp, rfl⟩ (intLoad_progress hx hn)
      (intLoad_inv hx hn)

/-- **Integer stores** (`i32.store`, `i64.store`; any address type): the bytes at the
effective address `pa` become the little-endian encoding of the value. -/
theorem wp_intStore {E : CoPset} {vs : List Val} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {c : BitVec t.width} {ma pa : Nat}
    {bs : List UInt8} {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hx : f.module.mems[x.toNat]? = some ma) (hpa : effAddr i.toNat arg = pa)
    (hn : bs.length = t.width / 8) :
    ownFrame f ∗ ownBytes ma pa bs ∗
      ▷ (ownFrame f ∗ ownBytes ma pa
          (Memory.encodeLE (t.width / 8) (c.setWidth (8 * (t.width / 8))).toNat).data.toList -∗
        WP (IExpr.run (vals vs ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (vs ++ [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩]) ++
        .plain (.intStore t none x arg) :: rest) : IExpr P host) @ E {{ Φ }} := by
  subst hpa
  iintro ⟨Hf, Hb, H⟩
  iapply wp_head_change (storeCells f ma (effAddr i.toNat arg) bs)
    (storeCells f ma (effAddr i.toNat arg)
      (Memory.encodeLE (t.width / 8) (c.setWidth (8 * (t.width / 8))).toNat).data.toList)
    (fun _ => []) (fun _ => vals vs ++ rest) ⟨rfl, by simp, rfl⟩ (intStore_progress hx hn)
    (intStore_inv hx hn)
  simp only [storeCells, ownCells_cons, ownCells_nil]
  iframe Hf Hb
  iintro !> %_ ⟨Hf, Hb⟩ -
  iapply H $$ [$Hf $Hb]

end Rules

end Silmaril.Wasm.Logic.IrisWasm
