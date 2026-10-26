module

public import Silmaril.Process.CLI.Sha256Cli.Binary
public import Silmaril.Process.CLI.Sha256Cli.Driver
public import Silmaril.Process.CLI.Sha256
public import Silmaril.Process.CLI.Plan
public import Silmaril.X86.EntryState

/-! # The specification of the freestanding `sha256` filter

The end-to-end statement for the real binary of `apps/sha256-cli` (built by
`apps/sha256-cli/build.sh` with gcc 13.3.0, `-O2 -static -nostdlib`, and lifted
into `Sha256Cli.Binary`): on every standard input it writes the lowercase hex
SHA-256 digest and a newline and exits 0, with nothing on stderr, unless the
environment refuses a system call.

The specification is `CLI.Sha256.strict` (shared, model-agnostic): a safety
part (`Agrees`), a coverage part (`Covered`, no crash and nothing unmodeled)
and a budget part (`Bounded`), each stated at the model point where it is
meant to hold, as `Plan.Sha256Goal` packages them. The digest is
`Silmaril.Crypto.SHA256.digest`, the spec the #882 pilot proved the
compression function against; `apps/sha256-cli/src/sha256.c` calls exactly
the clang `-O2 sha256_compress` whose contract is
`Sha256O2.sha256_compress_O2`.

## What is proved here

* `image_faithful`, `image_wf` — the transcription is faithful to the loadable
  image, re-exported from `Binary` (closed there by `decide +kernel`, no
  `native decision tactic`), so `X86Linux.Transcript.step` applies at every transcribed
  address.
* `step_at` — at any transcribed address of a launched process, the machine
  takes the transcribed instruction's step. This is the bridge a functional
  proof walks along; it uses only `image_faithful`/`image_wf`.
* **Non-vacuity** (`init_exists`, `loaded`): an actual System V launch state
  satisfying the loader relation exists, so `Agrees`/`Covered`/`Bounded` for
  this image are not vacuously true for want of a starting state (the
  `Realisable`/`Live` obligation of the pilot). The launch has empty `argv` and
  `envp` and a chosen standard input; the stack has the psABI layout.

## What is stated, not proved

`goal` is `Plan.Sha256Goal image …`: the functional end-to-end theorem. It is
**not proved** here. Proving it needs the loop invariants for the read,
padding, hex and write loops and the bridge from `Sha256O2.sha256_compress_O2`
(a function-contract `Ext.Returns` run) to an event-free `X86Linux` retirement
sequence — the one lemma called out as open in `Plan.lean` (3) and the model
research note. See `/srv/scratch/campaigns/research/sha256-x86/cli.md`.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli

open Silmaril.Process.Syscall
open Silmaril.Process.CLI
open Silmaril.Process.CLI.X86Linux

/-- The image the loader maps: the two `PT_LOAD` segments of the executable. -/
abbrev image : Image := Binary.image

/-- The transcription is faithful to the image (checked in `Binary` by
`decide +kernel`). -/
theorem image_faithful : Binary.transcript.Faithful image := Binary.faithful

/-- The image is well formed. -/
theorem image_wf : image.WF := Binary.image_wf

/-- **The bridge.** At any transcribed address of a launched process, the
machine takes exactly the transcribed instruction's step. Every functional
proof over this binary reduces fetch and decode through this lemma, so it
never decodes a byte: the decoding was done once, in the kernel, by
`Binary.faithful`. -/
theorem step_at {input : ProcInput} {c₀ : Core} {m₀ : Memory}
    (loaded : Loaded image input c₀ m₀) {entry : Entry} (member : entry ∈ Binary.transcript)
    {c : Core} (pc : c.rip.toNat = entry.address) :
    X86Linux.step c m₀ = entry.denote c m₀ :=
  Transcript.step image_faithful image_wf loaded member rfl pc

/-- Continue using the checked byte transcription after data or stack writes.
The existing memory-frame lemma preserves fetch permissions and bytes outside
the footprint. Establishing each machine write's footprint is still required. -/
theorem step_at_of_frame {input : ProcInput} {c₀ : Core} {m₀ memory : Memory}
    (loaded : Loaded image input c₀ m₀) {entry : Entry} (member : entry ∈ Binary.transcript)
    {inside : Nat → Prop} (frame : Memory.WritesWithin m₀ memory inside)
    (outside : ∀ offset < entry.bytes.length, ¬ inside (entry.address + offset))
    {c : Core} (pc : c.rip.toNat = entry.address) :
    X86Linux.step c memory = entry.denote c memory :=
  Transcript.step image_faithful image_wf loaded member (frame.fetchBytes outside) pc

/-! ## The specification

The filter specification is `CLI.Sha256.strict`, reused unchanged. The
`Sha256Cli` binary never retries, so safety holds at the full `linux` model
(`Plan.Sha256GoalNoRetry`); the lenient-retry form is `Plan.Sha256Goal`. -/

/-- The end-to-end goal, as `Plan.Sha256Goal` packages it: `Agrees` at
`eintrClean`, `Covered` at `linux`, and a linear `Bounded` at `linux`. Stated,
not proved (see the module doc). -/
abbrev goal (base perByte perRefusal : Nat) : Prop :=
  Plan.Sha256Goal image base perByte perRefusal

/-- The strong form for a program, like this one, that exits on every I/O
error: safety at the full `linux` model. Stated, not proved. -/
abbrev goalNoRetry (base perByte perRefusal : Nat) : Prop :=
  Plan.Sha256GoalNoRetry image base perByte perRefusal

/-- Exact complete-input digest/newline on exit 0. No prefix or progress
guarantee; in particular a later failure may have emitted arbitrary output.
This is a target, not a theorem about the compiled driver. -/
abbrev completedGoal : Prop := Agrees X86Linux.linux image Sha256.completed

/-- Every emitted prefix is permitted, even on a run that later fails.
This is a target independent of completion and progress. -/
abbrev prefixGoal : Prop := Agrees X86Linux.linux image Sha256.prefixes

/-- Default safety target; no crash-freedom, coverage or budget prerequisite. -/
abbrev partialGoal : Prop := Agrees X86Linux.linux image Sha256.partialCorrect

theorem partialGoal_iff : partialGoal ↔ prefixGoal ∧ completedGoal :=
  Sha256.agrees_partial_iff

theorem partialGoal_of_goalNoRetry {base perByte perRefusal : Nat}
    (h : goalNoRetry base perByte perRefusal) : partialGoal :=
  h.1.weaken Sha256.strict_le_partial

/-! ## Non-vacuity: a launch state exists

The precondition of every statement above is a launched process. If no state
satisfied the loader relation, `Agrees`/`Covered`/`Bounded` would hold
vacuously — the failure mode #882 names. `init_exists` closes this: an actual
System V launch of this image exists, with the two segments mapped and backed,
the psABI initial stack, and the standard descriptors of a filter. -/

/-- The chosen entry stack pointer: 16-byte aligned, far above the data
segments, with room for the stack. -/
def sp : Nat := 0x7fff0000

/-- The initial stack bytes for an empty `argv`/`envp`: `argc = 0`, the two
NULL terminators and `(AT_NULL, 0)` — five words. -/
def stackVector : List Byte := Machine.LittleEndian.encodeWords (vectorWords [] [] [])

/-- The placements of the launch: the code segment (read/execute), the `.bss`
segment (read/write, zero-filled), the writable stack room, and the stack
vectors. -/
def placements : List Silmaril.X86.EntryState.Placement :=
  [⟨Binary.seg0.region, some Binary.seg0.fileBytes⟩,
   ⟨Binary.seg1.region, some (List.replicate 0xc0 0)⟩,
   ⟨⟨sp - stackRoom, stackRoom, ⟨true, true, false⟩⟩, none⟩,
   ⟨⟨sp, 40, ⟨true, true, false⟩⟩, some stackVector⟩]

set_option maxRecDepth 100000 in
theorem seg0_contents : Binary.seg0.contents = Binary.seg0.fileBytes := by
  show Binary.seg0.fileBytes ++ List.replicate (Binary.seg0.memSize - Binary.seg0.fileBytes.length) 0
    = Binary.seg0.fileBytes
  rw [show Binary.seg0.memSize - Binary.seg0.fileBytes.length = 0 by
    simp only [Binary.seg0, List.length_map]; rfl]
  simp

set_option maxRecDepth 100000 in
theorem seg1_contents : Binary.seg1.contents = List.replicate 0xc0 0 := by
  show Binary.seg1.fileBytes ++ List.replicate (Binary.seg1.memSize - Binary.seg1.fileBytes.length) 0
    = List.replicate 0xc0 0
  rw [show Binary.seg1.fileBytes = [] from rfl]
  rfl

set_option maxRecDepth 100000 in
theorem placements_wf : Silmaril.X86.EntryState.WF placements := by
  refine ⟨?_, ?_, ?_⟩
  · intro placement member bytes backed
    simp only [placements, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp only [Option.some.injEq, reduceCtorEq] at backed
    · subst backed
      show Binary.seg0.fileBytes.length = Binary.seg0.region.size
      simp only [Binary.seg0, Segment.region, List.length_map]; rfl
    · subst backed
      show (List.replicate 0xc0 0).length = Binary.seg1.region.size
      simp only [Binary.seg1, Segment.region, List.length_replicate]
    · subst backed; rfl
  · intro placement member
    simp only [placements, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · show Binary.seg0.region.base + Binary.seg0.region.size ≤ _
      simp only [Binary.seg0, Segment.region]; decide
    · show Binary.seg1.region.base + Binary.seg1.region.size ≤ _
      simp only [Binary.seg1, Segment.region]; decide
    · show sp - stackRoom + stackRoom ≤ _; simp [sp, stackRoom, Silmaril.Process.addressLimit]
    · show sp + 40 ≤ _; simp [sp, Silmaril.Process.addressLimit]
  · simp only [placements, List.map_cons, List.map_nil]
    show List.Pairwise Silmaril.Process.Region.Disjoint
      [Binary.seg0.region, Binary.seg1.region, _, _]
    simp only [Binary.seg0, Binary.seg1, Segment.region, sp, stackRoom]
    decide

def memory₀ : Memory := Silmaril.X86.EntryState.memory placements

/-- The register file at the entry: RIP at the entry point, RSP at `sp`, every
other register zero (in particular RDX = 0, as `ELF_PLAT_INIT` leaves it). -/
def core₀ : Core :=
  (Silmaril.X86.EntryState.blankCore (BitVec.ofNat 64 image.entry)).write .rsp (BitVec.ofNat 64 sp)

/-- An example input: empty `argv` and `envp`, and a chosen standard input. -/
def inputOf (stdin : List Byte) : ProcInput := ⟨[], [], .ofList stdin⟩

set_option maxRecDepth 100000 in
theorem loaded (stdin : List Byte) : Loaded image (inputOf stdin) core₀ memory₀ := by
  have rsp : (core₀.read .rsp).toNat = sp := by
    simp only [core₀, Silmaril.X86.State.read, Silmaril.X86.State.write]
    decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- image.Mapped
    intro segment member
    simp only [image, Binary.image, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · refine ⟨List.mem_map_of_mem (f := Silmaril.X86.EntryState.Placement.region)
        (a := ⟨Binary.seg0.region, some Binary.seg0.fileBytes⟩) (by simp [placements]), ?_⟩
      intro index bound
      simp only [seg0_contents] at bound ⊢
      exact Silmaril.X86.EntryState.installAll_get
        (Silmaril.X86.EntryState.blobs_pairwise placements_wf)
        (Silmaril.X86.EntryState.blob_mem (placement := ⟨Binary.seg0.region, some Binary.seg0.fileBytes⟩)
          (by simp [placements]) rfl) bound
    · refine ⟨List.mem_map_of_mem (f := Silmaril.X86.EntryState.Placement.region)
        (a := ⟨Binary.seg1.region, some (List.replicate 0xc0 0)⟩) (by simp [placements]), ?_⟩
      intro index bound
      simp only [seg1_contents] at bound ⊢
      exact Silmaril.X86.EntryState.installAll_get
        (Silmaril.X86.EntryState.blobs_pairwise placements_wf)
        (Silmaril.X86.EntryState.blob_mem (placement := ⟨Binary.seg1.region, some (List.replicate 0xc0 0)⟩)
          (by simp [placements]) rfl) bound
  · -- rip = entry
    simp only [core₀, Silmaril.X86.EntryState.blankCore, 
      Silmaril.X86.State.write, image, Binary.image]
    decide
  · -- StackLayout
    rw [rsp]
    refine ⟨by decide, [], [], [], rfl, rfl, ?_, nofun, nofun, by simp, by simp⟩
    exact Silmaril.X86.EntryState.readBytes_blob placements_wf
      (placement := ⟨⟨sp, 40, ⟨true, true, false⟩⟩, some stackVector⟩) (by simp [placements]) rfl
      rfl (by decide)
  · rw [rsp]; decide
  · rw [rsp]
    exact Silmaril.X86.EntryState.permitted placements_wf
      (placement := ⟨⟨sp - stackRoom, stackRoom, ⟨true, true, false⟩⟩, none⟩)
      (by simp [placements]) rfl (by simp) (by simp [sp, stackRoom]) (by simp)
  · -- rdx = 0
    simp only [core₀, Silmaril.X86.EntryState.blankCore, Silmaril.X86.State.read,
      Silmaril.X86.State.write, Machine.RegisterFile.write, reduceCtorEq, ite_false]

/-- **Non-vacuity.** The loader relation and the `linux` environment's initial
relation are satisfiable for this image, on any standard input. The statements
`goal`/`goalNoRetry` are therefore about actual launches. -/
theorem init_exists (stdin : List Byte) :
    ∃ x, X86Linux.linux.Init image (inputOf stdin) x :=
  ⟨⟨core₀, ⟨memory₀, fun fd =>
      if fd = 0 then some ⟨true, false, .ofList stdin, 0, []⟩
      else if fd = 1 ∨ fd = 2 then some ⟨false, true, .ofList [], 0, []⟩ else none, none⟩⟩,
    memory₀, loaded stdin, rfl, rfl, by simp [StdDescriptors, inputOf]⟩

end Silmaril.Process.CLI.Sha256Cli
