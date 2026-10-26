module

public import Silmaril.Process.LPS.Problems.Sha256Cli.EndToEnd
public import Silmaril.Process.LPS.Problems.Sha256Cli.NonVacuity

/-! # The entry instruction is fetchable; the LPS target is not vacuous (VERIFIED)

`entryFetchable`: the entry `call 0x400100` (`e8 0b 00 00 00`) at `0x4000f0` decodes in the
initial image memory. With `NonVacuity.admissible_exists` this makes the hypotheses of
`TotalGoal` satisfiable on every message, for every flag oracle (`admissible`), and the
end-to-end theorem then yields the ideal trace for each of them (`ideal_trace_occurs`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open LaunchFacts

theorem loadHeaders_eq : ELFImage.loadHeaders records.programHeaders = [textHeader, bssHeader] := by
  decide

theorem segments_eq : (records.image file).segments =
    [ELFImage.segment file textHeader, ELFImage.segment file bssHeader] := by
  show (ELFImage.loadHeaders records.programHeaders).map (ELFImage.segment file) = _
  rw [loadHeaders_eq]; rfl

theorem text_executable : (ELFImage.segment file textHeader).executable = true := by
  have := ELFImage.segment_header_matches (file := file) (ph := textHeader) rfl (by decide)
  exact this.2.2.2.2.1.mp (by decide)

theorem text_shape : (ELFImage.segment file textHeader).base = 0x400000 ∧
    (ELFImage.segment file textHeader).size = 0x5c0 := by
  have := ELFImage.segment_header_matches (file := file) (ph := textHeader) rfl (by decide)
  exact ⟨this.2.1.symm, this.2.2.1.symm⟩

set_option maxRecDepth 100000 in
theorem text_bytes : (ELFImage.segment file textHeader).bytes = CLI.Sha256Cli.Binary.seg0.contents := by
  have h := segs_bytes
  have h2 : CLI.Sha256Cli.image.segments.map (fun s => (s.vaddr, s.contents)) =
      [(CLI.Sha256Cli.Binary.seg0.vaddr, CLI.Sha256Cli.Binary.seg0.contents),
        (CLI.Sha256Cli.Binary.seg1.vaddr, CLI.Sha256Cli.Binary.seg1.contents)] := rfl
  rw [segments_eq, h2] at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq] at h
  exact h.1.2

set_option maxRecDepth 100000 in
theorem entry_bytes (i : Nat) (h : i < 5) :
    CLI.Sha256Cli.Binary.seg0.contents[0xf0 + i]? = [0xe8, 0x0b, 0x00, 0x00, 0x00][i]? := by
  interval_cases i <;> decide +kernel

theorem entryFetchable (oracle : Nat → X86FlagChoices.Choice) : EntryFetchable oracle := by
  have nowrap : ∀ s ∈ (records.image file).segments, s.base + s.bytes.length ≤ 2 ^ 64 := by
    intro s m
    have := List.mem_map_of_mem (f := fun s : Segment => (s.base, s.bytes.length)) m
    rw [segs_shape] at this
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at this
    omega
  have disjoint : (records.image file).segments.Pairwise
      (fun a b => a.base + a.bytes.length ≤ b.base ∨ b.base + b.bytes.length ≤ a.base) := by
    have h := segs_shape
    rw [segments_eq] at h ⊢
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq] at h
    refine List.pairwise_pair.mpr (.inl ?_)
    omega
  have textMem : ELFImage.segment file textHeader ∈ (records.image file).segments := by
    rw [segments_eq]; simp
  obtain ⟨base, size⟩ := text_shape
  have len : (ELFImage.segment file textHeader).bytes.length = 0x5c0 := by
    rw [text_bytes]; set_option maxRecDepth 100000 in decide +kernel
  have intact : (initialMemory (records.image file).segments 0 []).fetchBytes 0x4000f0 5 =
      some [0xe8, 0x0b, 0x00, 0x00, 0x00] := by
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
      · have c : (segmentRegion (ELFImage.segment file textHeader)).Contains (0x4000f0 + o) := by
          simp only [segmentRegion, Silmaril.Process.Region.Contains, base, size]; omega
        simp only [c, decide_true, Bool.true_and]
        simp [segmentRegion, segmentPermissions, Silmaril.Process.Permissions.allows,
          text_executable]
    · rw [initialMemory_zero_bytes]
      have := foldl_install_get _ ∅ nowrap disjoint _ textMem (0xf0 + i) (by rw [len]; simp at bound; omega)
      rw [base, show 0x400000 + (0xf0 + i) = 0x4000f0 + i by omega] at this
      rw [this]
      congr 1
      have e := entry_bytes i (by simpa using bound)
      rw [← text_bytes] at e
      rw [List.getElem?_eq_getElem (by rw [len]; simp at bound; omega),
        List.getElem?_eq_getElem bound] at e
      exact Option.some.inj e
  have fetched : Silmaril.X86.Ext.fetch (initialMemory (records.image file).segments 0 []) 0x4000f0 =
      .decoded (.call 0xb) 5 :=
    Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨_, intact, CLI.Sha256Cli.Binary.ok_4000f0.1.1⟩
  unfold EntryFetchable
  have pc : (records.image file).initPc = 0x4000f0 := initPc_eq
  rw [pc]
  show (match Silmaril.X86.Ext.fetch (initialMemory (records.image file).segments 0 []) 0x4000f0 with
    | .decoded _ _ => true
    | _ => (initialMemory (records.image file).segments 0 []).fetchBytes 0x4000f0 2 =
      some [0x0f, 0x05]) = true
  rw [fetched]

/-- **Non-vacuity (VERIFIED).** On every message and for every flag oracle there is an
admissible LPS launch of the pinned ELF. -/
theorem admissible (oracle : Nat → X86FlagChoices.Choice) (message : List Byte) :
    ∃ en inp, Admissible oracle en inp message :=
  admissible_exists oracle (entryFetchable oracle) message

/-- **The conclusion is reached (VERIFIED).** For every flag oracle, refusal configuration,
budget and message, some admissible launch exists, and on it the complete ideal trace (read the
message, write `hex(SHA-256(message)) ++ "\n"` to fd 1, exit 0) is a trace of the binary. -/
theorem ideal_trace_occurs (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (limit : Int) (message : List Byte) :
    ∃ en inp, Admissible oracle en inp message ∧
      (behaviour oracle refusals limit en inp).traces (idealTrace message inp.fs) := by
  obtain ⟨en, inp, adm⟩ := admissible oracle message
  exact ⟨en, inp, adm, (sha256cli_lps_total oracle refusals limit en inp message trivial adm).complete⟩

end Silmaril.Process.LPS.Problems.Sha256Cli
