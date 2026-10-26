module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.NonVacuity
public import Silmaril.Process.LPS.Problems.Sha256Cli.Fetchable

/-! # The entry instruction of `sha256sum-min` is fetchable; the GNU LPS target is not vacuous

`entryFetchable` (VERIFIED): the entry `xor %ebp,%ebp` (`31 ed`) at `0x401000` decodes in the
initial image memory. With `NonVacuity.admissible_exists` this makes the hypotheses of the
GNU `TotalGoal` satisfiable on every message for every flag oracle (`admissible`, VERIFIED).
The proof is `Sha256Cli.entryFetchable` at the GNU image (installer lemmas of
`Sha256Cli.LaunchFacts`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli.LaunchFacts

set_option maxRecDepth 200000

theorem loadHeaders_eq : ELFImage.loadHeaders records.programHeaders =
    [hdrHeader, textHeader, rodataHeader, dataHeader] := by
  decide

theorem segments_eq : (records.image file).segments =
    [ELFImage.segment file hdrHeader, ELFImage.segment file textHeader,
      ELFImage.segment file rodataHeader, ELFImage.segment file dataHeader] := by
  show (ELFImage.loadHeaders records.programHeaders).map (ELFImage.segment file) = _
  rw [loadHeaders_eq]; rfl

theorem text_executable : (ELFImage.segment file textHeader).executable = true := by
  have := ELFImage.segment_header_matches (file := file) (ph := textHeader) rfl (by decide)
  exact this.2.2.2.2.1.mp (by decide)

theorem text_shape : (ELFImage.segment file textHeader).base = 0x401000 ∧
    (ELFImage.segment file textHeader).size = 0x43cb := by
  have := ELFImage.segment_header_matches (file := file) (ph := textHeader) rfl (by decide)
  exact ⟨this.2.1.symm, this.2.2.1.symm⟩

theorem text_len : (ELFImage.segment file textHeader).bytes.length = 0x43cb := by
  decide +kernel

theorem entry_bytes (i : Nat) (h : i < 2) :
    (ELFImage.segment file textHeader).bytes[i]? = [0x31, 0xed][i]? := by
  interval_cases i <;> decide +kernel

theorem entry_decodes : Silmaril.X86.Ext.decode [0x31, 0xed] = some (.alu .d .xor (.reg .rbp) .rbp, 2) := by
  decide

theorem entryFetchable (oracle : Nat → X86FlagChoices.Choice) : EntryFetchable oracle := by
  have nowrap : ∀ s ∈ (records.image file).segments, s.base + s.bytes.length ≤ 2 ^ 64 := by
    intro s m
    have := List.mem_map_of_mem (f := fun s : Segment => (s.base, s.bytes.length)) m
    rw [segs_shape] at this
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at this
    omega
  have disjoint : (records.image file).segments.Pairwise
      (fun a b => a.base + a.bytes.length ≤ b.base ∨ b.base + b.bytes.length ≤ a.base) := by
    have h : (((records.image file).segments.map fun s : Segment => (s.base, s.bytes.length))).Pairwise
        (fun p q : Nat × Nat => p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1) := by
      rw [segs_shape]; decide
    exact List.pairwise_map.mp h
  have textMem : ELFImage.segment file textHeader ∈ (records.image file).segments := by
    rw [segments_eq]; simp
  obtain ⟨base, size⟩ := text_shape
  have intact : (initialMemory (records.image file).segments 0 []).fetchBytes 0x401000 2 =
      some [0x31, 0xed] := by
    unfold Silmaril.Process.Memory.fetchBytes
    refine Silmaril.X86.Memory.readWith_eq_some_iff.mpr ⟨rfl, ?_, fun i bound => ?_⟩
    · rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff]
      refine ⟨by simp [Silmaril.Process.addressLimit], by simp [Silmaril.Process.addressLimit],
        fun o ho => ?_⟩
      unfold Silmaril.Process.Memory.permits
      rw [List.any_eq_true]
      refine ⟨segmentRegion (ELFImage.segment file textHeader), ?_, ?_⟩
      · show _ ∈ (records.image file).segments.map segmentRegion ++ _
        exact List.mem_append_left _ (List.mem_map_of_mem textMem)
      · have c : (segmentRegion (ELFImage.segment file textHeader)).Contains (0x401000 + o) := by
          simp only [segmentRegion, Silmaril.Process.Region.Contains, base, size]; omega
        simp only [c, decide_true, Bool.true_and]
        simp [segmentRegion, segmentPermissions, Silmaril.Process.Permissions.allows,
          text_executable]
    · rw [initialMemory_zero_bytes]
      have := foldl_install_get _ ∅ nowrap disjoint _ textMem i
        (by rw [text_len]; simp at bound; omega)
      rw [base] at this
      rw [this]
      congr 1
      have e := entry_bytes i (by simpa using bound)
      rw [List.getElem?_eq_getElem (by rw [text_len]; simp at bound; omega),
        List.getElem?_eq_getElem bound] at e
      exact Option.some.inj e
  have fetched : Silmaril.X86.Ext.fetch (initialMemory (records.image file).segments 0 []) 0x401000 =
      .decoded (.alu .d .xor (.reg .rbp) .rbp) 2 :=
    Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨_, intact, entry_decodes⟩
  unfold EntryFetchable
  have pc : (records.image file).initPc = 0x401000 := initPc_eq
  rw [pc]
  show (match Silmaril.X86.Ext.fetch (initialMemory (records.image file).segments 0 []) 0x401000 with
    | .decoded _ _ => true
    | _ => (initialMemory (records.image file).segments 0 []).fetchBytes 0x401000 2 =
      some [0x0f, 0x05]) = true
  rw [fetched]

/-- **Non-vacuity (VERIFIED).** On every message and for every flag oracle there is an
admissible stdin-tier LPS launch of `sha256sum-min`. -/
theorem admissible (oracle : Nat → X86FlagChoices.Choice) (message : List Byte) :
    ∃ en inp, Admissible oracle en inp message :=
  admissible_exists oracle (entryFetchable oracle) message

end Silmaril.Process.LPS.Problems.GnuSha256sum
