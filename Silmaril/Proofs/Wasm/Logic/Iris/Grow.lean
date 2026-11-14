module

public import Silmaril.Proofs.Wasm.Logic.Iris.Memory
public import Silmaril.Wasm.Logic.Iris.Rules.Defs

/-!
# The Iris logic of Wasm Core 3.0: `memory.grow`

`wp_memoryGrow` covers both outcomes of `memory.grow`, in every profile: on
success the memory cell records the new type and size and the new zero bytes
are allocated as fresh byte cells; on failure (the profile may fail any growth,
and growth past the limits always fails) the result is `-1` and nothing changes.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head)
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The zero bytes added by growing by `n` pages. -/
abbrev growBytes (n : Nat) : ByteArray := ByteArray.mk (Array.replicate (n * Memory.pageSize) 0)

theorem size_growBytes (n : Nat) : (growBytes n).size = n * Memory.pageSize := by
  simp [ByteArray.size]

theorem grow?_of_ok {mi : MemInst} {n : Nat} (h : growOk mi.type mi.bytes.size n) :
    mi.grow? n = some ⟨growType mi.type mi.bytes.size n, mi.bytes ++ growBytes n⟩ := by
  dsimp only [MemInst.grow?]
  split
  · rfl
  · rename_i hc
    exact absurd h hc

theorem grow?_some_inv {mi mi' : MemInst} {n : Nat} (h : mi.grow? n = some mi') :
    growOk mi.type mi.bytes.size n ∧
      mi' = ⟨growType mi.type mi.bytes.size n, mi.bytes ++ growBytes n⟩ := by
  dsimp only [MemInst.grow?] at h
  split at h
  · rename_i hc
    exact ⟨hc, (Option.some.inj h).symm⟩
  · cases h

theorem grow?_none_of {mi : MemInst} {n : Nat} (h : ¬ growOk mi.type mi.bytes.size n) :
    mi.grow? n = none := by
  dsimp only [MemInst.grow?]
  split
  · rename_i hc
    exact absurd hc h
  · rfl

/-- The cells of the memory and the frame before `memory.grow`. -/
abbrev growCells (f : Frame) (ma : Nat) (t : MemoryType) (sz : Nat) : List (ILoc × ICell) :=
  [(.frame, .frame f), (.mem ma, .mem t sz)]

theorem mem_of_cells {s : Store H} {f f' : Frame} {ma : Nat} {t : MemoryType} {sz : Nat}
    (h : Cells (growCells f ma t sz) s f') :
    ∃ mi, s.mems[ma]? = some mi ∧ mi.type = t ∧ mi.bytes.size = sz :=
  cellOf_mem.mp (h (.mem ma, .mem t sz) (by simp))

theorem getElem?_grow_old {B : ByteArray} {n j : Nat} (hj : j < B.size) :
    (B ++ growBytes n).data.toList[j]? = B.data.toList[j]? := by
  simp only [ByteArray.toList_data_append]
  exact List.getElem?_append_left (by simpa using hj)

theorem getElem?_grow_new {B : ByteArray} {n k : Nat} (hk : k < n * Memory.pageSize) :
    (B ++ growBytes n).data.toList[B.size + k]? = some 0 := by
  simp only [ByteArray.toList_data_append]
  rw [List.getElem?_append_right (by simp)]
  simp [hk]

/-- The memory after a successful `memory.grow`. -/
abbrev grownMem (mi : MemInst) (n : Nat) : MemInst :=
  ⟨growType mi.type mi.bytes.size n, mi.bytes ++ growBytes n⟩

/-- The cells after a successful `memory.grow`. -/
abbrev grownCells (f : Frame) (ma : Nat) (mi : MemInst) (n : Nat) : List (ILoc × ICell) :=
  [(.frame, .frame f),
    (.mem ma, .mem (growType mi.type mi.bytes.size n) (mi.bytes.size + n * Memory.pageSize))]

/-- The bytes added by a successful `memory.grow`. -/
abbrev newByteCells (ma : Nat) (mi : MemInst) (n : Nat) : List (ILoc × ICell) :=
  idxCells (.byte ma) .byte mi.bytes.size (List.replicate (n * Memory.pageSize) 0)

theorem grow_nodup (f : Frame) (ma : Nat) (mi : MemInst) (n : Nat) :
    ((grownCells f ma mi n).map Prod.fst ++ (newByteCells ma mi n).map Prod.fst).Nodup := by
  have hnd : ((newByteCells ma mi n).map Prod.fst).Nodup :=
    nodup_idxCells (fun _ _ h => by injection h) _ _
  rw [fst_idxCells] at hnd ⊢
  simpa using hnd

theorem grow_fresh {s : Store H} {f : Frame} {ma n : Nat} {mi : MemInst}
    (hm : s.mems[ma]? = some mi) : ∀ q ∈ newByteCells ma mi n, cellOf s f q.1 = none := by
  intro q hq
  obtain ⟨k, -, rfl⟩ := mem_idxCells.mp hq
  simp [cellOf, hm, byteArray_getElem?]

theorem grow_new {s : Store H} {f : Frame} {ma n : Nat} {mi : MemInst}
    (hm : s.mems[ma]? = some mi) :
    Cells (grownCells f ma mi n ++ newByteCells ma mi n) (s.setMem ma (grownMem mi n)) f := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rfl
    · simp [cellOf_setMem_mem hm, ByteArray.size_append, size_growBytes]
  · obtain ⟨k, hk, rfl⟩ := mem_idxCells.mp hq
    have hk' : k < n * Memory.pageSize := by simpa using hk
    show cellOf _ f (.byte ma (mi.bytes.size + k)) = _
    rw [cellOf_setMem_byte hm, getElem?_grow_new hk']
    simp

theorem grow_old {s : Store H} {f : Frame} {ma n : Nat} {mi : MemInst}
    (hm : s.mems[ma]? = some mi) (l : ILoc) (c : ICell)
    (hl : l ∉ (growCells f ma mi.type mi.bytes.size).map Prod.fst) (hc : cellOf s f l = some c) :
    cellOf (s.setMem ma (grownMem mi n)) f l = some c := by
  by_cases hb : ∃ j, l = .byte ma j
  · obtain ⟨j, rfl⟩ := hb
    have hc' : (mi.bytes.data.toList[j]?).map ICell.byte = some c := by
      simpa [cellOf, hm, byteArray_getElem?] using hc
    obtain ⟨b, hb', -⟩ := Option.map_eq_some_iff.mp hc'
    have hj : j < mi.bytes.size := by simpa using (List.getElem?_eq_some_iff.mp hb').1
    rw [cellOf_setMem_byte hm, getElem?_grow_old hj]
    exact hc'
  · have hb' : ∀ j, l ≠ .byte ma j := fun j he => hb ⟨j, he⟩
    have hme : l ≠ .mem ma := fun he => hl (by simp [he])
    rw [cellOf_setMem_other hb' hme]
    exact hc

/-- The change of a successful `memory.grow`. -/
theorem grow_change {s : Store H} {f : Frame} {ma n : Nat} {mi : MemInst}
    (hm : s.mems[ma]? = some mi) :
    Change s f (s.setMem ma (grownMem mi n)) f (growCells f ma mi.type mi.bytes.size)
      (grownCells f ma mi n) (newByteCells ma mi n) :=
  ⟨rfl, grow_nodup f ma mi n, grow_fresh hm, grow_new hm, grow_old hm⟩

theorem memoryGrow_progress {vs : List Val} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {t : MemoryType} {sz : Nat} {f : Frame}
    (hx : f.module.mems[x.toNat]? = some ma)
    (hprog : (growOk t sz n.toNat ∧ P.growMaySucceed .memory ma (sz / Memory.pageSize) n.toNat) ∨
      (P.growMayFail .memory ma (sz / Memory.pageSize) n.toNat ∨ ¬ growOk t sz n.toNat))
    (s : Store H) (f' : Frame) (hc : Cells (growCells f ma t sz) s f') :
    ∃ (vs' args : List Val) (c₀ : Config H), vs ++ [.num ⟨.int a.intType, n⟩] = vs' ++ args ∧
      Head P s f' args (.plain (.memoryGrow x)) c₀ := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨mi, hmi, rfl, rfl⟩ := mem_of_cells hc
  have hm : s.mem? f' x = some (ma, mi) := mem?_eq (hf ▸ hx) hmi
  rcases hprog with ⟨hok, hs⟩ | hfail
  · exact ⟨vs, _, _, rfl, .memory (.growSucceed hm (grow?_of_ok hok) hs)⟩
  · exact ⟨vs, _, _, rfl, .memory (.growFail hm (hfail.imp_right grow?_none_of))⟩

/-- The head steps of `memory.grow` on owned cells. -/
theorem memoryGrow_inv {vs : List Val} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {t : MemoryType} {sz : Nat} {f : Frame}
    (hx : f.module.mems[x.toNat]? = some ma) (s : Store H) (f' : Frame) (vs' args : List Val)
    (c₀ : Config H) (hc : Cells (growCells f ma t sz) s f')
    (hW : vs ++ [.num ⟨.int a.intType, n⟩] = vs' ++ args)
    (hh : Head P s f' args (.plain (.memoryGrow x)) c₀) :
    vs' = vs ∧ ((growOk t sz n.toNat ∧ ∃ s', c₀ = ⟨s', f', [aconst a (BitVec.ofNat _
        (sz / Memory.pageSize))]⟩ ∧ Change s f' s' f' (growCells f ma t sz)
          [(.frame, .frame f), (.mem ma, .mem (growType t sz n.toNat)
            (sz + n.toNat * Memory.pageSize))]
          (idxCells (.byte ma) .byte sz (List.replicate (n.toNat * Memory.pageSize) 0))) ∨
      c₀ = ⟨s, f', [aconst a (BitVec.allOnes _)]⟩) := by
  have hf : f' = f := frame_of_cells hc
  obtain ⟨mi, hmi, rfl, rfl⟩ := mem_of_cells hc
  obtain ⟨a', n', ma', mi', rfl, hm', hr⟩ := Hoare.head_memoryGrow hh
  obtain ⟨rfl, hv⟩ := Hoare.split_one hW
  obtain ⟨rfl, hn⟩ := Hoare.addr_arg_inj hv
  obtain rfl := eq_of_heq hn
  have hmm : (ma', mi') = (ma, mi) := Option.some.inj (hm'.symm.trans (mem?_eq (hf ▸ hx) hmi))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmm
  subst hf
  rcases hr with ⟨mi'', hg, -, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨hok, rfl⟩ := grow?_some_inv hg
    exact ⟨rfl, .inl ⟨hok, _, rfl, grow_change hmi⟩⟩
  · exact ⟨rfl, .inr rfl⟩

section Rules

variable {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-- One change of the store, in a proof: the owned cells `ps` become `ps'` and the
cells `qs` are allocated. -/
theorem change_step {E : CoPset} {s s' : Store H} {f f' : Frame}
    {ps ps' qs : List (ILoc × ICell)} {A : IProp GF} (hch : Change s f s' f' ps ps' qs) :
    ⊢ wasmInterp (s, f) -∗ ownCells ps -∗ (ownCells ps' -∗ ownCells qs -∗ A) ={E}=∗
      wasmInterp (s', f') ∗ A := by
  iintro Hσ Hc H
  imod interp_change hch.fst hch.nodup hch.fresh hch.new hch.old $$ [$Hσ $Hc] with ⟨Hσ, Hc, Hq⟩
  imodintro
  iframe Hσ
  iapply H $$ Hc Hq

/-- **`memory.grow`**, in every profile (any address type, so memory64 too). Both
outcomes must be handled: success (the memory grows by `n` pages of zero bytes,
which are owned afterwards, and the old size in pages is returned) and failure
(`-1`, nothing changes). `hprog` says one of them is possible. -/
theorem wp_memoryGrow {E : CoPset} {vs : List Val} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {t : MemoryType} {sz : Nat} {rest : List Admin}
    {f : Frame} {Φ : Res H → IProp GF} (hx : f.module.mems[x.toNat]? = some ma)
    (hprog : (growOk t sz n.toNat ∧ P.growMaySucceed .memory ma (sz / Memory.pageSize) n.toNat) ∨
      (P.growMayFail .memory ma (sz / Memory.pageSize) n.toNat ∨ ¬ growOk t sz n.toNat)) :
    ownFrame f ∗ ownMem ma t sz ∗ ▷ (
      (⌜growOk t sz n.toNat⌝ -∗ ownFrame f -∗
        ownMem ma (growType t sz n.toNat) (sz + n.toNat * Memory.pageSize) -∗
        ownBytes ma sz (List.replicate (n.toNat * Memory.pageSize) 0) -∗
        WP (IExpr.run (vals vs ++ aconst a (BitVec.ofNat _ (sz / Memory.pageSize)) :: rest) :
          IExpr P host) @ E {{ Φ }}) ∧
      (ownFrame f -∗ ownMem ma t sz -∗
        WP (IExpr.run (vals vs ++ aconst a (BitVec.allOnes _) :: rest) : IExpr P host) @ E {{ Φ }}))
    ⊢ WP (IExpr.run (vals (vs ++ [.num ⟨.int a.intType, n⟩]) ++ .plain (.memoryGrow x) :: rest) :
        IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hf, Hm, H⟩
  iapply wp_head_cells (growCells f ma t sz) ⟨rfl, by simp, rfl⟩ (memoryGrow_progress hx hprog)
  isplitl [Hf Hm]
  · simp only [growCells, ownCells_two]
    iframe
  iintro !> %s %f' %vs' %args %c₀ %⟨hc, hW, hh⟩ Hσ Hc
  obtain ⟨hvs, hr⟩ := memoryGrow_inv hx s f' vs' args c₀ hc hW hh
  rw [hvs]
  rcases hr with ⟨hok, s', hc₀, hch⟩ | hc₀
  · rw [hc₀]
    simp only [List.append_assoc, List.singleton_append]
    iapply change_step hch $$ Hσ Hc
    icases H with ⟨H, -⟩
    simp only [ownCells_two]
    iintro ⟨Hf, Hm⟩ Hb
    iapply H $$ %hok Hf Hm Hb
  · rw [hc₀]
    simp only [List.append_assoc, List.singleton_append]
    simp only [growCells, ownCells_two]
    icases Hc with ⟨Hf, Hm⟩
    icases H with ⟨-, H⟩
    imodintro
    iframe Hσ
    iapply H $$ Hf Hm

end Rules

end Silmaril.Wasm.Logic.IrisWasm
