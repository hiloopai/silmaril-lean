module

public import Silmaril.Elf.Image.Defs

/-! # Proofs of `Silmaril.Elf.Image` -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Image

open Silmaril.Elf
open Silmaril.Elf.Image
open Silmaril.Elf.Staged (Layout phSpan)
open Silmaril.Formats.ELF (ProgramHeader)
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

theorem mem_origins {A : File} {v i : Nat} {o : Origin} :
    (i, o) ∈ A.origins v ↔ ∃ ph, A.phdrs[i]? = some ph ∧ segOrigin ph v = some o := by
  unfold File.origins
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨ph, j⟩, hm, hs⟩
    rw [List.mem_zipIdx_iff_getElem?] at hm
    simp only at hm hs
    cases h : segOrigin ph v with
    | none => rw [h] at hs; cases hs
    | some o' =>
      rw [h] at hs
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨ph, hm, h⟩
  · rintro ⟨ph, hp, hs⟩
    exact ⟨(ph, i), List.mem_zipIdx_iff_getElem?.mpr hp, by simp [hs]⟩

theorem origins_index_unique {A : File} {v i : Nat} {o₁ o₂ : Origin}
    (h₁ : (i, o₁) ∈ A.origins v) (h₂ : (i, o₂) ∈ A.origins v) : o₁ = o₂ := by
  obtain ⟨ph, hp, hs⟩ := mem_origins.mp h₁
  obtain ⟨ph', hp', hs'⟩ := mem_origins.mp h₂
  rw [hp] at hp'
  cases hp'
  rw [hs] at hs'
  exact Option.some_inj.mp hs'

theorem segOrigin_file {ph : ProgramHeader} {v : Nat} (hk : ph.kind = PT_LOAD)
    (hlo : ph.virtualAddress ≤ v) (hhi : v < ph.virtualAddress + ph.fileSize) :
    segOrigin ph v = some (.file (ph.offset + (v - ph.virtualAddress))) := by
  simp [segOrigin, hk, hlo, hhi]

theorem segOrigin_eq_file {ph : ProgramHeader} {v o : Nat} (h : segOrigin ph v = some (.file o)) :
    ph.kind = PT_LOAD ∧ ph.virtualAddress ≤ v ∧ v < ph.virtualAddress + ph.fileSize ∧
      o = ph.offset + (v - ph.virtualAddress) := by
  unfold segOrigin at h
  split_ifs at h with h₁ h₂ h₃
  · simp only [Option.some.injEq, Origin.file.injEq] at h
    exact ⟨h₁.1, h₁.2, h₂, h.symm⟩
  · cases h

theorem mapsFile_origins {A : File} {i v len o : Nat} (h : MapsFile A i v len o) {k : Nat}
    (hk : k < len) : (i, Origin.file (o + k)) ∈ A.origins (v + k) := by
  obtain ⟨ph, hp, hl, hlo, hhi, rfl⟩ := h
  refine mem_origins.mpr ⟨ph, hp, ?_⟩
  rw [segOrigin_file hl (by omega) (by omega)]
  congr 2
  omega

theorem offsetOf_origin {A : File} {v o : Nat} (h : A.layout.offsetOf v = some o) :
    ∃ i, (i, Origin.file o) ∈ A.origins v := by
  unfold Layout.offsetOf at h
  cases hf : List.find? (fun ph : ProgramHeader => ph.kind == PT_LOAD &&
      decide (ph.virtualAddress ≤ v) && decide (v < ph.virtualAddress + ph.fileSize))
      A.layout.phdrs with
  | none => rw [hf] at h; cases h
  | some ph =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    obtain ⟨⟨hk, hlo⟩, hhi⟩ := hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
    refine ⟨i, mem_origins.mpr ⟨ph, hi, ?_⟩⟩
    rw [segOrigin_file hk hlo hhi, ← h]
    congr 2
    omega

theorem offsetOf_of_unique {A : File} {v i o : Nat} (h : A.origins v = [(i, Origin.file o)]) :
    A.layout.offsetOf v = some o := by
  have hm : (i, Origin.file o) ∈ A.origins v := by rw [h]; exact List.mem_singleton_self _
  obtain ⟨ph, hp, hs⟩ := mem_origins.mp hm
  have hsome : (List.find? (fun ph : ProgramHeader => ph.kind == PT_LOAD &&
      decide (ph.virtualAddress ≤ v) && decide (v < ph.virtualAddress + ph.fileSize))
      A.layout.phdrs).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨ph, List.mem_iff_getElem?.mpr ⟨i, hp⟩, ?_⟩
    obtain ⟨hk, hlo, hhi, -⟩ := segOrigin_eq_file hs
    simp [hk, hlo, hhi]
  obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp
    (show (A.layout.offsetOf v).isSome = true by unfold Layout.offsetOf; simpa using hsome)
  obtain ⟨j, hj⟩ := offsetOf_origin ho'
  rw [h] at hj
  simp only [List.mem_singleton, Prod.mk.injEq, Origin.file.injEq] at hj
  rw [ho', hj.2]

theorem resolve_unique {A : File} {v i o : Nat} (h : A.resolve v = .unique i (.file o)) :
    A.layout.offsetOf v = some o := by
  apply offsetOf_of_unique (i := i)
  unfold File.resolve at h
  cases hA : A.origins v with
  | nil => rw [hA] at h; cases h
  | cons x xs =>
    cases xs with
    | nil =>
      obtain ⟨i', o'⟩ := x
      rw [hA] at h
      simp only [Resolution.unique.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | cons y ys => rw [hA] at h; cases h

theorem vaddrOf_origin {A : File} {o v : Nat} (h : A.layout.vaddrOf o = some v) :
    ∃ i, (i, Origin.file o) ∈ A.origins v := by
  unfold Layout.vaddrOf Layout.segmentOf at h
  cases hf : List.find? (fun ph : ProgramHeader => ph.kind == PT_LOAD &&
      decide ((phSpan ph).Contains (⟨o, 1⟩ : Span).off (⟨o, 1⟩ : Span).len)) A.layout.phdrs with
  | none => rw [hf] at h; cases h
  | some ph =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hp := List.find?_some hf
    rw [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨hk, hc⟩ := hp
    have hc' : (phSpan ph).Contains o 1 := of_decide_eq_true hc
    obtain ⟨hlo, hhi⟩ := hc'
    simp only [phSpan] at hlo hhi
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
    refine ⟨i, mem_origins.mpr ⟨ph, hi, ?_⟩⟩
    rw [segOrigin_file hk (by omega) (by omega)]
    congr 2
    omega

theorem codeAt_segBytes {F : Blob} {v : Nat} {code : List (BitVec 8)} (h : CodeAt F v code) :
    ∃ A, Parses F A ∧ ∃ i ph, A.phdrs[i]? = some ph ∧ codeSeg v code.length ph = true ∧
      SegBytes F A i v (ph.offset + (v - ph.virtualAddress)) code := by
  obtain ⟨A, hA, ph, hf, hr⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
  have hc := List.find?_some hf
  refine ⟨A, hA, i, ph, hi, hc, ⟨ph, hi, ?_, ?_, ?_, rfl⟩, hr⟩ <;>
    simp only [codeSeg, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc <;> omega

theorem codeAt_of_segBytes {F : Blob} {A : File} (hA : Parses F A) {i v o : Nat}
    {code : List (BitVec 8)} (h : SegBytes F A i v o code)
    (hf : A.phdrs.find? (codeSeg v code.length) = A.phdrs[i]?) : CodeAt F v code := by
  obtain ⟨⟨ph, hp, -, -, -, rfl⟩, hb⟩ := h
  exact ⟨A, hA, ph, hf.trans hp, hb⟩

end Silmaril.Proofs.Elf.Image
