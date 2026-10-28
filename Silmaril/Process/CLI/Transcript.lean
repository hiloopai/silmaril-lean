module

public import Silmaril.Process.CLI.X86Linux

/-! # Transcriptions of machine code

A transcription is what an external lifter (Rust, `iced-x86`, or later a
decoder verified in Lean and executed by an external runtime) emits for a binary: one
entry per instruction, with its address, its exact bytes and its decoded form.
It is *data*, not trusted: `Entry.Decodes` is a decidable check that the
in-Lean decoder (`X86.Ext.decode`) gives the transcribed instruction from the
transcribed bytes, and `Transcript.Covers` (decidable) that the bytes are the
image's. Once an entry is checked, `step_of_entry` replaces the
fetch/decode of `X86Linux.step` by the transcribed instruction, so a program
proof works on the symbolic transcription and never decodes bytes.

This is the split that keeps proofs model-agnostic on the ISA axis:

* the program proof is about `Entry.denote` (instruction semantics only);
* the decoder agreement is `Entry.Decodes`, checked per entry by `decide`
  today, by a verified decoder later;
* a different x86 model (Sail-derived) needs only its own `step_of_entry`.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux

open Silmaril.Process.Syscall

/-- A transcribed instruction: an `X86.Ext` instruction or `syscall`. -/
inductive TInstr where
  | ext (instr : X86.Ext.Instr)
  | syscall

structure Entry where
  address : Nat
  bytes : List Byte
  instr : TInstr

/-- The transcribed bytes decode to the transcribed instruction, consuming all
of them, and an `ext` entry does not begin with the `syscall` bytes. -/
def Entry.Decodes (entry : Entry) : Prop :=
  match entry.instr with
  | .syscall => entry.bytes = syscallBytes
  | .ext instr => X86.Ext.decode entry.bytes = some (instr, entry.bytes.length) ∧
      entry.bytes.take 2 ≠ syscallBytes.take entry.bytes.length

instance (entry : Entry) : Decidable entry.Decodes := by
  unfold Entry.Decodes
  cases entry.instr <;> infer_instance

/-- The step a transcribed instruction takes. -/
def Entry.denote (entry : Entry) (core : Core) (memory : Memory) : Step Core :=
  match entry.instr with
  | .syscall => .syscall { core with rip := core.rip + 2 }
  | .ext instr => execResult (X86.Ext.exec instr core memory entry.bytes.length)

/-- At a checked entry with its bytes in executable memory, the machine takes the
transcribed instruction's step. -/
theorem step_of_entry {entry : Entry} (decodes : entry.Decodes) {core : Core} {memory : Memory}
    (pc : core.rip.toNat = entry.address)
    (intact : memory.fetchBytes entry.address entry.bytes.length = some entry.bytes) :
    step core memory = entry.denote core memory := by
  rw [← pc] at intact
  unfold Entry.Decodes at decodes
  unfold Entry.denote
  cases h : entry.instr with
  | syscall =>
    simp only [h] at decodes
    rw [decodes] at intact
    have trap : memory.fetchBytes core.rip.toNat 2 = some syscallBytes := intact
    simp only [step, trap, ↓reduceIte]
  | ext instr =>
    simp only [h] at decodes
    obtain ⟨decoded, notSyscall⟩ := decodes
    have positive := (X86.Ext.decode_length decoded).2.1
    have notTrap : memory.fetchBytes core.rip.toNat 2 ≠ some syscallBytes := by
      intro two
      apply notSyscall
      have short : min 2 entry.bytes.length ≤ 2 := Nat.min_le_left _ _
      have short' : min 2 entry.bytes.length ≤ entry.bytes.length := Nat.min_le_right _ _
      have fromTwo := Memory.readWith_sub_range two (offset := 0) (len := min 2 entry.bytes.length) (by omega) (by omega)
      have fromEntry := Memory.readWith_sub_range intact (offset := 0) (len := min 2 entry.bytes.length) (by omega) (by omega)
      rw [fromTwo] at fromEntry
      have same := (Option.some.inj fromEntry)
      simp only [List.drop_zero] at same
      rw [List.take_eq_take_iff.mpr (by omega :
        min 2 entry.bytes.length = min (min 2 entry.bytes.length) entry.bytes.length)]
      rw [← same]
      apply List.take_eq_take_iff.mpr
      simp only [syscallBytes, List.length_cons, List.length_nil]
      omega
    have fetched : X86.Ext.fetch memory core.rip.toNat = .decoded instr entry.bytes.length :=
      X86.Ext.fetch_eq_decoded_iff.mpr ⟨entry.bytes, intact, decoded⟩
    simp only [step, notTrap, fetched, ↓reduceIte]

abbrev Transcript := List Entry

/-- `bytes` is the content of an executable segment of `image` at `address`. -/
def _root_.Silmaril.Process.CLI.Image.CodeAt (image : Image) (address : Nat) (bytes : List Byte) : Prop :=
  ∃ segment ∈ image.segments, segment.permissions.execute = true ∧
    segment.vaddr ≤ address ∧ address + bytes.length ≤ segment.vaddr + segment.fileBytes.length ∧
    (segment.fileBytes.drop (address - segment.vaddr)).take bytes.length = bytes

/-- Code bytes of a well-formed image fetch back from any memory it is mapped in. -/
theorem fetch_of_codeAt {image : Image} (wf : image.WF) {memory : Memory}
    (mapped : image.Mapped memory) {address : Nat} {bytes : List Byte}
    (code : image.CodeAt address bytes) (nonempty : 0 < bytes.length) :
    memory.fetchBytes address bytes.length = some bytes := by
  obtain ⟨segment, member, executable, lower, upper, slice⟩ := code
  obtain ⟨fits, noWrap⟩ := wf segment member
  obtain ⟨region, backed⟩ := mapped segment member
  apply Memory.readWith_eq
  · exact Memory.permitted_of_region _ _ _ _ segment.region region executable
      (by omega) (by omega) lower (by simp only [Segment.region]; omega)
  · intro index bound
    have inside : address - segment.vaddr + index < segment.contents.length := by
      simp only [Segment.contents, List.length_append, List.length_replicate]
      omega
    have byte := backed (address - segment.vaddr + index) inside
    rw [show segment.vaddr + (address - segment.vaddr + index) = address + index by omega] at byte
    rw [byte, List.getElem_of_eq slice.symm bound]
    simp only [Segment.contents, List.getElem_take, List.getElem_drop]
    rw [List.getElem_append_left (by omega)]

/-- A checked entry is nonempty. -/
theorem Entry.Decodes.length_pos {entry : Entry} (decodes : entry.Decodes) :
    0 < entry.bytes.length := by
  unfold Entry.Decodes at decodes
  split at decodes
  · rw [decodes]; decide
  · exact (X86.Ext.decode_length decodes.1).2.1 |>.trans_le (X86.Ext.decode_length decodes.1).2.2.2

/-- Every entry is checked and its bytes are the image's. -/
def Transcript.Faithful (transcript : Transcript) (image : Image) : Prop :=
  ∀ entry ∈ transcript, entry.Decodes ∧ image.CodeAt entry.address entry.bytes

/-- The entry at an address, if any. -/
def Transcript.at? (transcript : Transcript) (address : Nat) : Option Entry :=
  transcript.find? fun entry => entry.address == address

/-- A faithful transcription of a well-formed image is fetchable in every loaded
memory, so `step_of_entry` applies at each of its addresses. -/
theorem Transcript.fetch {transcript : Transcript} {image : Image}
    (faithful : transcript.Faithful image) (wf : image.WF) {input : ProcInput} {core : Core}
    {memory : Memory} (loaded : Loaded image input core memory) {entry : Entry}
    (member : entry ∈ transcript) :
    memory.fetchBytes entry.address entry.bytes.length = some entry.bytes :=
  fetch_of_codeAt wf loaded.1 (faithful entry member).2 (faithful entry member).1.length_pos

/-- At a transcribed address of a loaded image, the machine takes the
transcribed step. Code is assumed unmodified since loading (`unchanged`). -/
theorem Transcript.step {transcript : Transcript} {image : Image}
    (faithful : transcript.Faithful image) (wf : image.WF) {input : ProcInput} {core₀ : Core}
    {memory₀ memory : Memory} (loaded : Loaded image input core₀ memory₀) {entry : Entry}
    (member : entry ∈ transcript)
    (unchanged : memory.fetchBytes entry.address entry.bytes.length =
      memory₀.fetchBytes entry.address entry.bytes.length)
    {core : Core} (pc : core.rip.toNat = entry.address) :
    step core memory = entry.denote core memory :=
  step_of_entry (faithful entry member).1 pc (unchanged.trans (transcript.fetch faithful wf loaded member))

end Silmaril.Process.CLI.X86Linux
