module

public import Silmaril.X86.SystemV.Call.Defs
public import Silmaril.Process.CLI.Loaded.Thms

/-!
# Proofs: a concrete System V call into a pinned image

The header is `Silmaril/X86/SystemV/Call/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SystemV.Call

open Silmaril.X86 (MState State Word Byte Reg)
open Silmaril.Process (Memory Region Access addressLimit)
open Silmaril.Process.CLI (Image Segment)
open Silmaril.X86.EntryState (Placement WF readWith_blob permitted_region)
open Silmaril.X86.SystemV.Call
open Silmaril.X86.SystemV.CallCtx

theorem bytes_length (F : Frame) : F.bytes.length = F.size + 8 := by
  simp [Frame.bytes]

theorem contents_length {s : Segment} (h : s.fileBytes.length ≤ s.memSize) :
    s.contents.length = s.memSize := by
  simp only [Segment.contents, List.length_append, List.length_replicate]
  omega

theorem of_check {F : Frame} {img : Image} (h : Layout.check F img = true) : Layout F img := by
  simp only [Layout.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hb, ha⟩, hs⟩, hsegs⟩, hd⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, fun s m => (hsegs s m).1.1.2, fun s m => (hsegs s m).1.2, ha, hb⟩
  · intro p hp bytes hbytes
    rcases List.mem_cons.1 hp with rfl | hp
    · cases hbytes; exact bytes_length F
    · obtain ⟨s, m, rfl⟩ := List.mem_map.1 hp
      cases hbytes; exact contents_length (hsegs s m).1.1.1
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hs
    · obtain ⟨s, m, rfl⟩ := List.mem_map.1 hp
      exact (hsegs s m).2
  · have e : (placements F img).map Placement.region = F.region :: img.segments.map Segment.region := by
      simp only [placements, List.map_cons, List.map_map]; rfl
    rw [e]; exact hd

theorem segment_mem {F : Frame} {img : Image} {s : Segment} (hs : s ∈ img.segments) :
    (⟨s.region, some s.contents⟩ : Placement) ∈ placements F img :=
  List.mem_cons_of_mem _ (List.mem_map.2 ⟨s, hs, rfl⟩)

theorem loaded {F : Frame} {img : Image} (h : Layout F img) : img.Loaded (memory F img) := by
  intro s hs _
  have member := segment_mem (F := F) hs
  have len : s.contents.length = s.memSize := h.wf.backing_length _ member _ rfl
  rw [len]
  exact ⟨fun hr => readWith_blob h.wf member rfl hr (h.positive s hs),
    fun hx => readWith_blob h.wf member rfl hx (h.positive s hs)⟩

theorem stack_read {F : Frame} {img : Image} (h : Layout F img) :
    (memory F img).readWith .read F.base (F.size + 8) = some F.bytes :=
  readWith_blob h.wf List.mem_cons_self rfl rfl (by show 0 < F.size + 8; omega)

theorem ret_read {F : Frame} {img : Image} (h : Layout F img) :
    (memory F img).readBytes F.sp 8 = some (Silmaril.Machine.LittleEndian.encodeWords [F.ret]) := by
  have := Memory.readWith_sub_range (stack_read h) (offset := F.size) (len := 8) (by omega)
    (by omega)
  have hlen : (Silmaril.Machine.LittleEndian.encodeWords [F.ret]).length = 8 := by simp
  unfold Memory.readBytes Frame.sp
  rw [this]
  simp [Frame.bytes, List.take_of_length_le, hlen]

theorem retOf {F : Frame} {img : Image} (h : Layout F img) {core : State}
    (hsp : (core.read .rsp).toNat = F.sp) :
    Silmaril.X86.FnContract.retOf core (memory F img) = F.ret := by
  unfold Silmaril.X86.FnContract.retOf
  rw [hsp, ret_read h]
  simp

theorem abi {F : Frame} {img : Image} (h : Layout F img) {core : State}
    (hsp : (core.read .rsp).toNat = F.sp) :
    Silmaril.X86.FnContract.AbiEntry core (memory F img) := by
  refine ⟨by rw [hsp]; exact h.aligned, ?_⟩
  rw [retOf h hsp, hsp]
  exact ret_read h

theorem stackOk {F : Frame} {img : Image} (h : Layout F img) {core : State}
    (hsp : (core.read .rsp).toNat = F.sp) :
    StackOk img F.size ⟨core, memory F img⟩ := by
  have read := stack_read h
  have rd := (Memory.checkSpan_iff ..).mp (Memory.readWith_permitted read)
  have wr : (memory F img).Permitted .write F.base (F.size + 8) :=
    permitted_region h.wf List.mem_cons_self rfl (by show 0 < F.size + 8; omega)
  have wp := (Memory.checkSpan_iff ..).mp wr
  unfold StackOk
  simp only [hsp, Frame.sp]
  refine ⟨by omega, fun i hi => ⟨by unfold addressLimit at rd; omega, ?_, ?_⟩,
    fun i hi => ⟨by unfold addressLimit at wp; omega, ?_⟩, fun s hs => ?_⟩
  · rw [show F.base + F.size - F.size + i = F.base + i by omega]; exact rd.2.2 i (by omega)
  · have hi' : i < F.bytes.length := by rw [bytes_length]; omega
    have b := Memory.readWith_get read i hi'
    rw [show F.base + F.size - F.size + i = F.base + i by omega]
    change ((memory F img).bytes.get? (F.base + i)).isSome = true
    rw [b]; rfl
  · rw [show F.base + F.size - F.size + i = F.base + i by omega]; exact wp.2.2 i (by omega)
  · have := h.above s hs
    unfold Silmaril.X86.Stencils.ByteLoop.Apart Frame.sp at *
    omega

theorem unmapped_below {F : Frame} {img : Image} (h : Layout F img) {a : Nat} (ha : a < F.base)
    (access : Access) : (memory F img).permits access a = false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  obtain ⟨region, hr, hhit⟩ := List.any_eq_true.mp hit
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have hbase : p.region.base ≤ a := (of_decide_eq_true (Bool.and_eq_true_iff.mp hhit).1).1
  rcases List.mem_cons.mp hp with rfl | hs
  · change F.base ≤ a at hbase
    omega
  · obtain ⟨s, hseg, heq⟩ := List.mem_map.mp hs
    subst p
    change s.vaddr ≤ a at hbase
    have := h.above s hseg
    unfold Frame.sp at this
    omega

theorem read_null {F : Frame} {img : Image} (h : Layout F img) {n : Nat} (hn : 0 < n) :
    (memory F img).readBytes 0 n = none := by
  unfold Memory.readBytes Memory.readWith
  split
  · rename_i ok
    have hit := ((Memory.checkSpan_iff ..).mp ok).2.2 0 hn
    rw [Nat.zero_add, unmapped_below h h.base_pos] at hit
    contradiction
  · rfl

theorem stack_write_same {F : Frame} {img : Image} (h : Layout F img) {mem : Memory}
    (hw : Memory.WritesWithin (memory F img) mem F.region.Contains) : img.Loaded mem := by
  intro s hs hwr
  have hl := loaded h s hs hwr
  have hout : ∀ offset < s.contents.length, ¬ F.region.Contains (s.vaddr + offset) := by
    intro offset _ hc
    have := h.above s hs
    unfold Region.Contains Frame.region Frame.sp at *
    simp only at hc
    omega
  exact ⟨fun hr => (hw.readBytes hout).trans (hl.1 hr),
    fun hx => (hw.fetchBytes hout).trans (hl.2 hx)⟩

theorem callCore_rsp_toNat {F : Frame} {img : Image} (h : Layout F img) (entry : Word)
    (args : List Word) : ((callCore F entry args).read .rsp).toNat = F.sp := by
  have := h.wf.noWrap _ (List.mem_cons_self (a := F.placement))
  change (BitVec.ofNat 64 F.sp).toNat = F.sp
  simp only [BitVec.toNat_ofNat]
  unfold Frame.sp
  unfold Frame.placement Frame.region addressLimit at this
  simp only at this
  omega

end Silmaril.Proofs.X86.SystemV.Call
