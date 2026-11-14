module

public import Silmaril.Problems.Models.ProcRegression.Defs
public import Silmaril.Problems.Models.Proc.Thms

/-! Proofs of `Problems.Models.ProcRegression.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Problems.Models.ProcRegression

open Silmaril.Process
open Silmaril.Process.CLI
open Silmaril.X86 (Word State)
open Silmaril.X86.EntryState (Placement WF region_mem blob_mem blobs_pairwise installAll_get
  readBytes_blob permitted_region memory_regions)
open Silmaril.Problems.Models.ProcRegression
open Silmaril.Problems.Models (Proc.Load Proc.LoadLoose)

theorem table_static : image.StaticTable table := by
  decide +kernel

theorem vectorBytes_length {auxv : List (Word × Word)} (h : auxv.length = 4) :
    (vectorBytes auxv).length = 112 := by
  simp [vectorBytes, X86Linux.vectorWords, h]

/-- The extras the tests use. -/
def Extra (extra : List Placement) : Prop := extra = [] ∨ extra = [extraCode]

set_option maxRecDepth 100000 in
theorem placements_wf {auxv : List (Word × Word)} (h : auxv.length = 4)
    {extra : List Placement} (hx : Extra extra) : WF (placements auxv extra) := by
  have hv := vectorBytes_length h
  rcases hx with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro p hp bs hb
      simp only [placements, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> cases hb
      · decide +kernel
      · decide +kernel
      · rfl
      · rfl
    · intro p hp
      simp only [placements, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · show sp + (vectorBytes auxv).length ≤ addressLimit
        rw [hv]; decide +kernel
      · decide +kernel
    · simp only [placements, List.append_nil, List.map_cons, List.map_nil, pVectors, hv]
      decide +kernel
  · refine ⟨?_, ?_, ?_⟩
    · intro p hp bs hb
      simp only [placements, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hb
      · decide +kernel
      · decide +kernel
      · rfl
      · rfl
      · rfl
    · intro p hp
      simp only [placements, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · show sp + (vectorBytes auxv).length ≤ addressLimit
        rw [hv]; decide +kernel
      · decide +kernel
      · decide +kernel
    · simp only [placements, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        pVectors, hv]
      decide +kernel

theorem rsp : (core.read .rsp).toNat = sp := by
  simp only [core, Silmaril.X86.State.read, Silmaril.X86.State.write]
  decide

theorem mem_placements {auxv : List (Word × Word)} {extra : List Placement} {p : Placement}
    (h : p ∈ [pSeg0, pSeg1, pRoom, pVectors auxv, pArg]) : p ∈ placements auxv extra :=
  List.mem_append_left _ h

theorem segment_mapped {placements : List Placement} (wf : WF placements) {segment : Segment}
    (member : (⟨segment.region, some segment.contents⟩ : Placement) ∈ placements) :
    segment.region ∈ (Silmaril.X86.EntryState.memory placements).regions ∧
      ∀ index (bound : index < segment.contents.length),
        (Silmaril.X86.EntryState.memory placements).bytes.get? (segment.vaddr + index) =
          some segment.contents[index] :=
  ⟨region_mem member, fun _ bound => installAll_get (blobs_pairwise wf) (blob_mem member rfl) bound⟩

theorem room_permitted {auxv : List (Word × Word)} {extra : List Placement}
    (wf : WF (placements auxv extra)) :
    (launchMemory auxv extra).Permitted .write pRoom.region.base pRoom.region.size :=
  permitted_region wf (mem_placements (p := pRoom) (by simp only [List.mem_cons, true_or, or_true]))
    (by decide) (by decide)

theorem vectors_read {auxv : List (Word × Word)} {extra : List Placement}
    (wf : WF (placements auxv extra)) (h : auxv.length = 4) :
    X86Linux.BytesAt (launchMemory auxv extra) sp (vectorBytes auxv) :=
  readBytes_blob wf (mem_placements (p := pVectors auxv)
    (by simp only [List.mem_cons, true_or, or_true])) rfl rfl
    (by show 0 < (vectorBytes auxv).length; rw [vectorBytes_length h]; decide)

theorem arg_read {auxv : List (Word × Word)} {extra : List Placement}
    (wf : WF (placements auxv extra)) :
    X86Linux.BytesAt (launchMemory auxv extra) argAddress [97, 0] :=
  readBytes_blob wf (mem_placements (p := pArg) (by simp only [List.mem_cons, true_or, or_true]))
    rfl rfl (by decide)

set_option maxRecDepth 100000 in
/-- Every test launch passes the loader before #70. -/
theorem loose {auxv : List (Word × Word)} (h : auxv.length = 4)
    (tags : ∀ entry ∈ auxv, entry.1 ≠ X86Linux.atNull ∧ entry.1 ≠ X86Linux.atRandom)
    {extra : List Placement} (hx : Extra extra) (stdin : List Byte) :
    Proc.LoadLoose image (input stdin) core (launchMemory auxv extra) := by
  have wf := placements_wf h hx
  refine ⟨⟨?_, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro segment member
    simp only [image, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact segment_mapped wf (mem_placements (p := pSeg0) List.mem_cons_self)
    · exact segment_mapped wf (mem_placements (p := pSeg1)
        (by simp only [List.mem_cons, true_or, or_true]))
  · rw [rsp]
    refine ⟨by decide, [BitVec.ofNat 64 argAddress], [], auxv, rfl, rfl, vectors_read wf h, ?_, ?_,
      ?_, ?_⟩
    · intro i hi _
      have : i = 0 := by simpa using hi
      subst i
      exact arg_read wf
    · intro i hi
      exact False.elim (Nat.not_lt_zero _ hi)
    · intro member
      exact (tags _ member).1 rfl
    · intro v member
      exact absurd rfl (tags _ member).2
  · rw [rsp]; decide
  · rw [rsp]
    exact room_permitted wf
  · decide
  · intro segment member
    rw [rsp]
    simp only [image, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel

/-- The ordinary reading of each test stack. -/
theorem vectors {auxv : List (Word × Word)} (h : auxv.length = 4)
    (tags : ∀ entry ∈ auxv, entry.1 ≠ X86Linux.atNull)
    {extra : List Placement} (hx : Extra extra) (stdin : List Byte) :
    X86Linux.StackVectors (input stdin) (launchMemory auxv extra) sp
      [BitVec.ofNat 64 argAddress] [] auxv :=
  ⟨rfl, rfl, vectors_read (placements_wf h hx) h, by simp, tags⟩

set_option maxRecDepth 100000 in
theorem ordinary_load (stdin : List Byte) :
    Proc.Load image (input stdin) core (launchMemory ordinary []) := by
  have hv := vectorBytes_length (show ordinary.length = 4 from rfl)
  refine ⟨loose rfl (by decide) (.inl rfl) stdin, ⟨?_, ?_, ?_⟩⟩
  · rw [rsp]
    exact ⟨table, table_static, _, _, _, vectors rfl (by decide) (.inl rfl) stdin, by decide⟩
  · unfold X86Linux.ExecFromImage
    simp only [launchMemory, memory_regions, placements, List.append_nil,
      List.map_cons, List.map_nil, pVectors, hv]
    decide +kernel
  · unfold X86Linux.NoAlias
    simp only [launchMemory, memory_regions, placements, List.append_nil,
      List.map_cons, List.map_nil, pVectors, hv]
    decide +kernel

/-- A launch whose stack reads as `auxv` is rejected unless `auxv` pins the table. -/
theorem rejected_of_auxv {auxv : List (Word × Word)} (h : auxv.length = 4)
    (tags : ∀ entry ∈ auxv, entry.1 ≠ X86Linux.atNull)
    {extra : List Placement} (hx : Extra extra) (stdin : List Byte)
    (bad : ¬ X86Linux.AuxvPinned table auxv) :
    ¬ Proc.Load image (input stdin) core (launchMemory auxv extra) := by
  intro load
  obtain ⟨t, static, argv, envp, auxv', vectors', pinned⟩ := load.2.table
  rw [rsp] at vectors'
  rw [Image.StaticTable.unique static table_static,
    ← (vectors h tags hx stdin).auxv_unique vectors'] at pinned
  exact bad pinned

theorem substitutedAddress_rejected (stdin : List Byte) :
    ¬ Proc.Load image (input stdin) core (launchMemory substitutedAddress []) :=
  rejected_of_auxv rfl (by decide) (.inl rfl) stdin (by decide)

theorem substitutedCount_rejected (stdin : List Byte) :
    ¬ Proc.Load image (input stdin) core (launchMemory substitutedCount []) :=
  rejected_of_auxv rfl (by decide) (.inl rfl) stdin (by decide)

theorem extraExec_rejected (stdin : List Byte) :
    ¬ Proc.Load image (input stdin) core (launchMemory ordinary [extraCode]) := by
  intro load
  have member : extraCode.region ∈ (launchMemory ordinary [extraCode]).regions :=
    region_mem (List.mem_append_right _ (by simp))
  have := load.2.exec _ member rfl
  revert this
  decide +kernel

end Silmaril.Proofs.Problems.Models.ProcRegression
