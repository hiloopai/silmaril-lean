module

public import Silmaril.Process.CLI.Sha256Cli.Binary
public import Silmaril.Apps.Sha256sum.Binary.CallEntry

/-! # The minimal filter's loaded SHA compression callee

The literal filter image contains the already proved clang `-O2` compression
routine, relocated to `0x4002e0`, and its exact K table at `0x4004c0`.
`loaded_code` and `loaded_kTable` establish these entry facts in every mapped
filter memory. `constants_of_loaded_writesWithin` retains them after driver
writes outside the two constant regions; it does not require mutable data to
retain their initial contents.

The compression contract is reused unchanged. These facts bind a particular
executable's bytes to the function proof; they do not prove the driver's input,
padding or output invariants. In particular `call_encoding` identifies the
single final padded-block call, rather than asserting that a launch reaches it.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Compress

open Silmaril.Process (Access Memory Region)
open Silmaril.X86 (Word MState)
open Silmaril.Crypto.X86.Sha256O2

/-- `sha256_compress` in the minimal filter. -/
def textBase : Word := 0x4002e0

/-- `sha256_compress_K` in the minimal filter. -/
def rodataBase : Word := 0x4004c0

/-- The already proved callee, returning to an arbitrary caller address. -/
def layout (exit : Word) : Layout := ⟨textBase, rodataBase, exit⟩

theorem layout_relocFits (exit : Word) : (layout exit).RelocFits := by
  unfold Layout.RelocFits Layout.relocValue layout textBase rodataBase
  simp only
  decide

/-- The final padded-block call, also used for empty input. -/
def callAddress : Nat := 0x400229

/-- The actual five-byte CALL's continuation. This is a function return,
not the process exit address. -/
def returnAddress : Word := 0x40022e

theorem call_encoding :
    Binary.i_400229.address = callAddress ∧
      Binary.i_400229.bytes = [0xe8, 0xb2, 0x00, 0x00, 0x00] ∧
      Binary.i_400229.bytes.length = 5 ∧
      Binary.i_400229.instr = .ext (.call 0xb2) ∧
      callAddress + 5 = returnAddress.toNat ∧
      returnAddress + 0xb2 = textBase := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem seg0_mem : Binary.seg0 ∈ Binary.image.segments := by simp [Binary.image]

set_option maxRecDepth 100000 in
/-- All 459 callee bytes, including the relocated PC32 field and RET, agree
with the image to which the SHA proof applies. -/
theorem seg0_compress :
    (Binary.seg0.contents.drop (0x4002e0 - 0x400000)).take 459 =
      image textBase rodataBase := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The filter's 256 K bytes are the existing SHA contract's exact table. -/
theorem seg0_kTable :
    (Binary.seg0.contents.drop (0x4004c0 - 0x400000)).take 256 = kBytes := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal-byte comparison rejects an off-by-one extraction. -/
theorem wrong_code_offset :
    (Binary.seg0.contents.drop (0x4002e1 - 0x400000)).take 459 ≠
      image textBase rodataBase := by
  decide +kernel

/-- Reading a shorter extraction cannot establish the 459-byte callee fact. -/
theorem wrong_code_length :
    (Binary.seg0.contents.drop (0x4002e0 - 0x400000)).take 458 ≠
      image textBase rodataBase := by
  intro h
  have lengths := congrArg List.length h
  rw [image_length] at lengths
  have short : ((Binary.seg0.contents.drop (0x4002e0 - 0x400000)).take 458).length ≤ 458 :=
    List.length_take_le _ _
  rw [lengths] at short
  simp only [size] at short
  omega

/-- Every mapped filter memory holds the exact executable compression image. -/
theorem loaded_code {memory : Memory} (mapped : Binary.image.Mapped memory) :
    memory.fetchBytes textBase.toNat size = some (image textBase rodataBase) := by
  have h := Silmaril.Apps.Sha256sum.Binary.readWith_segment mapped seg0_mem Binary.image_wf
    (acc := .execute) (by decide) (0x4002e0 - 0x400000) 459 (by decide) (by decide)
  rw [seg0_compress] at h
  exact h

/-- Every mapped filter memory holds the exact readable K table. -/
theorem loaded_kTable {memory : Memory} (mapped : Binary.image.Mapped memory) :
    memory.readBytes rodataBase.toNat kSize = some kBytes := by
  have h := Silmaril.Apps.Sha256sum.Binary.readWith_segment mapped seg0_mem Binary.image_wf
    (acc := .read) (by decide) (0x4004c0 - 0x400000) 256 (by decide) (by decide)
  rw [seg0_kTable] at h
  exact h

/-- Completed-result correctness of the exact callee linked into the filter. -/
theorem compress_contract (exit : Word) : Contract (layout exit) frameSize :=
  sha256_compress_O2 (layout exit)

theorem call_noWrap (exit : Word) :
    ∀ r ∈ regions (layout exit) 0x401660 0x401620 0x7ffeffd8 frameSize,
      r.base + r.size ≤ Silmaril.Process.addressLimit := by
  change ∀ r ∈ regions (layout 0) 0x401660 0x401620 0x7ffeffd8 frameSize,
    r.base + r.size ≤ Silmaril.Process.addressLimit
  decide

theorem call_disjoint (exit : Word) :
    (regions (layout exit) 0x401660 0x401620 0x7ffeffd8 frameSize).Pairwise Region.Disjoint := by
  change (regions (layout 0) 0x401660 0x401620 0x7ffeffd8 frameSize).Pairwise Region.Disjoint
  decide

/-- The filter's actual buffer addresses and a call stack derived from its
`0x7fff0000` launch stack admit a backed compression entry. This closes entry
non-vacuity at the concrete layout; it does not assert launch reachability or
identify the driver's state and padded block contents. -/
theorem call_realisable (exit : Word) :
    ∃ initial, SysVEntry (layout exit) 0x401660 0x401620 0x7ffeffd8 frameSize initial := by
  refine ⟨_, entryState_sysVEntry (L := layout exit)
    (state := 0x401660) (block := 0x401620) (rspEntry := 0x7ffeffd8)
    (frame := frameSize) (layout_relocFits exit) ?_ ?_ ?_ ?_ ?_⟩
  · rw [Silmaril.X86.sysv64_entryAligned_iff]; decide
  · decide
  · decide
  · exact call_noWrap exit
  · exact call_disjoint exit

/-- Driver writes preserve the two required constants when their footprint
excludes code and K. All other call-site hypotheses remain explicit. -/
theorem constants_of_loaded_writesWithin {loaded current : Memory} {inside : Nat → Prop}
    (mapped : Binary.image.Mapped loaded)
    (writes : Memory.WritesWithin loaded current inside)
    (codeOutside : ∀ address, (codeRegion (layout 0)).Contains address → ¬ inside address)
    (kTableOutside : ∀ address, (kTableRegion (layout 0)).Contains address → ¬ inside address) :
    current.fetchBytes textBase.toNat size = some (image textBase rodataBase) ∧
      current.readBytes rodataBase.toNat kSize = some kBytes := by
  constructor
  · rw [writes.fetchBytes ?_]
    · exact loaded_code mapped
    · intro offset hoffset
      exact codeOutside _ (by simp only [codeRegion, layout, Region.Contains]; omega)
  · rw [writes.readBytes ?_]
    · exact loaded_kTable mapped
    · intro offset hoffset
      exact kTableOutside _ (by simp only [kTableRegion, layout, Region.Contains]; omega)

/-- Reuse the generic frame theorem for every disjoint driver buffer. -/
theorem post_readBytes_region {state block rspEntry exit : Word} {initial final : MState}
    (post : Post (layout exit) state block rspEntry frameSize initial final) (buffer : Region)
    (stateDisjoint : Region.Disjoint buffer (stateRegion state))
    (frameDisjoint : Region.Disjoint buffer (frameRegion rspEntry frameSize)) :
    final.memory.readBytes buffer.base buffer.size = initial.memory.readBytes buffer.base buffer.size :=
  Silmaril.Apps.Sha256sum.Binary.post_readBytes_region post buffer stateDisjoint frameDisjoint

/-- The linked code survives a compression call. -/
theorem post_code {exit state block rspEntry : Word} {initial final : MState}
    (entry : SysVEntry (layout exit) state block rspEntry frameSize initial)
    (post : Post (layout exit) state block rspEntry frameSize initial final) :
    final.memory.fetchBytes textBase.toNat size = some (image textBase rodataBase) := by
  have stateDisjoint : Region.Disjoint (codeRegion (layout exit)) (stateRegion state) := by
    simpa only [Region.Disjoint, or_comm] using entry.state_disjoint_code
  exact (Silmaril.Apps.Sha256sum.Binary.post_fetchBytes_region post
    (codeRegion (layout exit)) stateDisjoint entry.code_disjoint_frame).trans entry.code

/-- The linked K table survives a compression call. -/
theorem post_kTable {exit state block rspEntry : Word} {initial final : MState}
    (entry : SysVEntry (layout exit) state block rspEntry frameSize initial)
    (post : Post (layout exit) state block rspEntry frameSize initial final) :
    final.memory.readBytes rodataBase.toNat kSize = some kBytes := by
  have stateDisjoint : Region.Disjoint (kTableRegion (layout exit)) (stateRegion state) := by
    simpa only [Region.Disjoint, or_comm] using entry.state_disjoint_kTable
  exact (Silmaril.Apps.Sha256sum.Binary.post_readBytes_region post
    (kTableRegion (layout exit)) stateDisjoint entry.kTable_disjoint_frame).trans entry.kTable

end Silmaril.Process.CLI.Sha256Cli.Compress
