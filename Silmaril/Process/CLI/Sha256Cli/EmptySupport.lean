module

public import Silmaril.Process.CLI.Sha256Cli.Spec
public import Silmaril.Apps.Sha256sum.Binary.Load
public import Silmaril.Crypto.X86.Sha256O2.Exec
public import Silmaril.Process.CLI.X86Linux.Silent

/-! # The minimal filter's linked compression call

This module binds the existing compression contract to the already transcribed
`apps/sha256-cli` image. The executable is distinct from `sha256sum-min`.
The generic silent-execution adapter is an explicit dependency on PR #3040;
the compression proof and adapter are reused, not reimplemented here.

The empty block and state facts are local driver refinement premises. They do
not assert that startup or the padding loop has established those bytes, or
that a whole Linux launch completes. In particular, `compress_cli_live` needs
every System V entry clause, including stack mapping and disjointness.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.EmptySupport

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.X86 (Word MState)
open Silmaril.Crypto.X86.Sha256O2

/-- The retained CLI's compression text and constants, at their actual addresses. -/
def layout (exit : Word) : Layout := ⟨0x4002e0, 0x4004c0, exit⟩

theorem layout_relocFits (exit : Word) : (layout exit).RelocFits := by
  unfold Layout.RelocFits Layout.relocValue layout
  simp only
  decide

set_option maxRecDepth 100000 in
/-- The embedded executable's actual relocated compression bytes. -/
theorem code_slice :
    (Binary.seg0.contents.drop (0x4002e0 - 0x400000)).take size =
      Silmaril.Crypto.X86.Sha256O2.image 0x4002e0 0x4004c0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kTable_slice :
    (Binary.seg0.contents.drop (0x4004c0 - 0x400000)).take kSize = kBytes := by
  decide +kernel

def hexDigits : List Byte :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
   0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66]

set_option maxRecDepth 100000 in
theorem hexTable_slice :
    (Binary.seg0.contents.drop (0x4004b0 - 0x400000)).take 16 = hexDigits := by
  decide +kernel

/-- The output loop's exact lowercase lookup bytes are present in the image. -/
theorem loaded_hexTable {memory : Memory} (mapped : Binary.image.Mapped memory) :
    memory.readBytes 0x4004b0 16 = some hexDigits := by
  have member : Binary.seg0 ∈ Binary.image.segments := by simp [Binary.image]
  have table := Silmaril.Apps.Sha256sum.Binary.readWith_segment mapped member
    Binary.image_wf (acc := .read) (by decide)
    (0x4004b0 - 0x400000) 16 (by decide) (by decide)
  rw [hexTable_slice] at table
  exact table

/-- Loading the minimal filter supplies the two immutable callee premises. -/
theorem loaded_constants {memory : Memory} (mapped : Binary.image.Mapped memory)
    (exit : Word) :
    memory.fetchBytes (layout exit).textBase.toNat size =
        some (Silmaril.Crypto.X86.Sha256O2.image 0x4002e0 0x4004c0) ∧
      memory.readBytes (layout exit).rodataBase.toNat kSize = some kBytes := by
  have member : Binary.seg0 ∈ Binary.image.segments := by simp [Binary.image]
  have code := Silmaril.Apps.Sha256sum.Binary.readWith_segment mapped member
    Binary.image_wf (acc := .execute) (by decide)
    (0x4002e0 - 0x400000) size (by decide) (by decide)
  have table := Silmaril.Apps.Sha256sum.Binary.readWith_segment mapped member
    Binary.image_wf (acc := .read) (by decide)
    (0x4004c0 - 0x400000) kSize (by decide) (by decide)
  rw [code_slice] at code
  rw [kTable_slice] at table
  exact ⟨code, table⟩

/-- Driver writes need only preserve these two spans, not the mutable BSS. -/
theorem constants_of_frame {loaded memory : Memory}
    (mapped : Binary.image.Mapped loaded) {inside : Nat → Prop}
    (frame : Memory.WritesWithin loaded memory inside)
    (codeOutside : ∀ offset < size, ¬ inside (0x4002e0 + offset))
    (tableOutside : ∀ offset < kSize, ¬ inside (0x4004c0 + offset)) (exit : Word) :
    memory.fetchBytes (layout exit).textBase.toNat size =
        some (Silmaril.Crypto.X86.Sha256O2.image 0x4002e0 0x4004c0) ∧
      memory.readBytes (layout exit).rodataBase.toNat kSize = some kBytes := by
  obtain ⟨code, table⟩ := loaded_constants mapped exit
  exact ⟨(frame.fetchBytes codeOutside).trans code,
    (frame.readBytes tableOutside).trans table⟩

private theorem returned_rip {exit : Word} {initial final : MState}
    (returned : Silmaril.X86.Ext.step exit initial = .returned final) :
    final.core.rip = exit := by
  cases fetched : Silmaril.X86.Ext.fetch initial.memory initial.core.rip.toNat with
  | undecodable => simp [Silmaril.X86.Ext.step, fetched] at returned
  | truncated => simp [Silmaril.X86.Ext.step, fetched] at returned
  | decoded instruction length =>
    cases executed : Silmaril.X86.Ext.exec instruction initial.core initial.memory with
    | ok core memory =>
      simp only [Silmaril.X86.Ext.step, fetched] at returned
      simp only [executed] at returned
      split_ifs at returned with condition
      cases returned
      exact condition.2
    | dataFault => simp [Silmaril.X86.Ext.step, fetched, executed] at returned
    | divideError => simp [Silmaril.X86.Ext.step, fetched, executed] at returned
    | undefinedCondition condition =>
      simp [Silmaril.X86.Ext.step, fetched, executed] at returned
    | trap => simp [Silmaril.X86.Ext.step, fetched, executed] at returned

/-- A completed Ext return includes a real final RET to the designated address. -/
theorem returns_rip {exit : Word} {initial final : MState}
    (returned : Silmaril.X86.Ext.Returns exit initial final) :
    final.core.rip = exit := by
  obtain ⟨_, _, _, returned⟩ := returned
  exact returned_rip returned

/-- A valid CLI compression entry has a real silent process execution. This
uses the existing local callee execution theorem, not driver totality. -/
theorem compress_cli_live {E : Env} (lens : E.MemoryLens)
    {exit state block rspEntry : Word} {core : Silmaril.X86.State} {s : E.State}
    (running : E.exited s = none)
    (entry : SysVEntry (layout exit) state block rspEntry frameSize ⟨core, E.memory s⟩) :
    ∃ final, Silmaril.X86.Ext.Returns exit ⟨core, E.memory s⟩ final ∧
      Proc.Runs X86Linux.isa E ⟨core, s⟩ []
        ⟨final.core, E.withMemory s final.memory⟩ ∧
      Post (layout exit) state block rspEntry frameSize ⟨core, E.memory s⟩ final ∧
      final.core.rip = exit := by
  obtain ⟨final, returned⟩ := sha256_compress_O2_live (layout exit) _ _ _ _ entry
  exact ⟨final, returned, X86Linux.runs_of_ext_returns lens running rfl returned,
    sha256_compress_O2 (layout exit) _ _ _ _ _ entry returned, returns_rip returned⟩

/-- Initial SHA words as the little-endian stores made by the C driver. -/
def initialStateBytes : List Byte :=
  [0x67, 0xe6, 0x09, 0x6a, 0x85, 0xae, 0x67, 0xbb,
   0x72, 0xf3, 0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5,
   0x7f, 0x52, 0x0e, 0x51, 0x8c, 0x68, 0x05, 0x9b,
   0xab, 0xd9, 0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b]

/-- Empty input pads to one block, including the zero 64-bit bit length. -/
def emptyBlock : List Byte := 0x80 :: List.replicate 63 0

theorem emptyBlock_padding :
    emptyBlock = (Silmaril.Crypto.paddingMD []).map UInt8.toBitVec := by decide

theorem initialStateBytes_state : stateOf initialStateBytes =
    ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩ := by decide

/-- The empty digest's words in the little-endian driver buffer. -/
def emptyStateBytes : List Byte :=
  [0x42, 0xc4, 0xb0, 0xe3, 0x14, 0x1c, 0xfc, 0x98,
   0xc8, 0xf4, 0xfb, 0x9a, 0x24, 0xb9, 0x6f, 0x99,
   0xe4, 0x41, 0xae, 0x27, 0x4c, 0x93, 0x9b, 0x64,
   0x1b, 0x99, 0x95, 0xa4, 0x55, 0xb8, 0x52, 0x78]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Closed value check only: the already proved callee theorem supplies the
execution; this identifies the resulting eight words at the empty call site. -/
theorem empty_compressed :
    compressBlock (stateOf initialStateBytes) emptyBlock = stateOf emptyStateBytes := by
  decide +kernel

/-- The callee's actual postcondition gives the empty digest words once the
driver has established its initialization and padding bytes. -/
theorem post_empty_state {exit state block rspEntry : Word} {initial final : MState}
    (post : Post (layout exit) state block rspEntry frameSize initial final)
    (initialBytes : initial.memory.readBytes state.toNat 32 = some initialStateBytes)
    (paddedBytes : initial.memory.readBytes block.toNat 64 = some emptyBlock) :
    StateHolds final.memory state (stateOf emptyStateBytes) := by
  simpa only [empty_compressed] using post.compressed _ _ initialBytes paddedBytes

/-- Eight little-endian words determine their complete 32-byte buffer. The
length premise matters: `stateOf` deliberately ignores bytes beyond index 31. -/
theorem stateOf_injective32 {first second : List Byte}
    (firstLength : first.length = 32) (secondLength : second.length = 32)
    (same : stateOf first = stateOf second) : first = second := by
  have words : ∀ t, t < 8 → leWordAt first t = leWordAt second t := by
    intro t bound
    have cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨
        t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Silmaril.Crypto.SHA256.Kernel.InitHash.h0 same
    · exact congrArg Silmaril.Crypto.SHA256.Kernel.InitHash.h1 same
    · exact congrArg Silmaril.Crypto.SHA256.Kernel.InitHash.h2 same
    · exact congrArg Silmaril.Crypto.SHA256.Kernel.InitHash.h3 same
    · exact congrArg Silmaril.Crypto.SHA256.Kernel.InitHash.h4 same
    · exact congrArg Silmaril.Crypto.SHA256.Kernel.InitHash.h5 same
    · exact congrArg Silmaril.Crypto.SHA256.Kernel.InitHash.h6 same
    · exact congrArg Silmaril.Crypto.SHA256.Kernel.InitHash.h7 same
  apply List.ext_getElem
  · omega
  · intro i firstBound secondBound
    have lane : i % 4 < 4 := Nat.mod_lt _ (by decide)
    have word : i / 4 < 8 := by omega
    have equalByte := congrArg
      (fun w : Silmaril.Crypto.SHA256.Kernel.Word =>
        Silmaril.Machine.LittleEndian.wordByte (w.setWidth 64) (i % 4))
      (words (i / 4) word)
    rw [wordByte_leWordAt first _ _ lane, wordByte_leWordAt second _ _ lane] at equalByte
    have index : 4 * (i / 4) + i % 4 = i := by omega
    simpa only [byteAt, index, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem firstBound, List.getElem?_eq_getElem secondBound,
      Option.getD_some] using equalByte

/-- Exposing the bytes used by the compiled hex loop requires no extra
compression computation and no assumption about arbitrary scratch registers. -/
theorem stateHolds_readBytes {memory : Memory} {state : Word} {bytes : List Byte}
    (held : StateHolds memory state (stateOf bytes)) (length : bytes.length = 32) :
    memory.readBytes state.toNat 32 = some bytes := by
  obtain ⟨observed, read, value⟩ := held
  have observedLength := Memory.readWith_length read
  have same := stateOf_injective32 observedLength length value
  exact same ▸ read

theorem post_empty_bytes {exit state block rspEntry : Word} {initial final : MState}
    (post : Post (layout exit) state block rspEntry frameSize initial final)
    (initialBytes : initial.memory.readBytes state.toNat 32 = some initialStateBytes)
    (paddedBytes : initial.memory.readBytes block.toNat 64 = some emptyBlock) :
    final.memory.readBytes state.toNat 32 = some emptyStateBytes :=
  stateHolds_readBytes (post_empty_state post initialBytes paddedBytes) (by decide)

end Silmaril.Process.CLI.Sha256Cli.EmptySupport
