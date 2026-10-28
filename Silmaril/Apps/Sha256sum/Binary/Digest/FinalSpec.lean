module

public import Silmaril.Apps.Sha256sum.Binary.Digest.Final
public import Silmaril.Apps.Sha256sum.Binary.Digest.Spec
public import Silmaril.Process.CLI.Sha256Cli.HexReference

/-! # `sha_final` against the SHA-256 specification

`Digest.Final.final_runs` leaves the digest of `Hfin = (blocks tail T).foldl compressBlock H`
in the caller's buffer. Here the context is instantiated from the read loop's cut point
`Digest.AtPad e consumed` (the struct has absorbed `consumed`: `H` is the fold of its full
blocks, `tail` the rest, `T = consumed.length`), and the 32 bytes are identified with
**`SHA256.digest` of the whole message**:

* `hfin_hash`: the padding blocks are the specification's (`TailPaddingReference.paddedBlocks`,
  covering both the one-block and the two-block case and the modular length): the fold of
  `blocks ++ TailPaddingReference.blocks tail T` from the initial value is `SHA256.hash`
  (`Driver.fold_paddedBlocks`, through `Digest.fold_toState`);
* `outBytes_digest`: the output loop's byte order is the specification's big-endian
  serialisation (`HexReference.permutation_reference`, `HexReference.sourceIndex_word_lane`).

`final_digest` (VERIFIED): from `AtPad e consumed`, with the caller's buffer `out` described by
`OutBuf`, the process reaches `AtOut e consumed out` (`0x40310a`) by retiring steps of the
`Ext8` machine. Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Crypto.X86.Sha256O2 (StateHolds compressBlock stateOf)
open Silmaril.Process.CLI.Sha256Cli

/-- The caller's digest buffer: its address at `[sp + 0x10]` (`digest_file`'s second
argument), 32 bytes readable and writable, above the image and apart from the frame. -/
structure OutBuf (m : Memory) (sp out : Word) : Prop where
  slot : loadN m (sp + 0x10#64) 8 = some out
  writable : m.Permitted .write out.toNat 32
  readable : m.Permitted .read out.toNat 32
  low : 0x420000 ≤ out.toNat
  high : out.toNat + 32 < 2 ^ 64
  apart : out.toNat + 32 ≤ sp.toNat - 400 ∨ sp.toNat + 152 ≤ out.toNat

/-- **The digest of the message read.** `0x40310a`, after `sha_final`: the 32 bytes at `out`
are `SHA256.digest consumed`; the frame registers, the compression code and table, and both
code regions of `digest_file` are kept. -/
structure AtOut (e : Loop) (consumed : List Byte) (out : Word) (s : XState) : Prop where
  rip : s.core.rip = Final.base + BitVec.ofNat 64 214
  rsp : s.core.read .rsp = e.sp
  rbp : s.core.read .rbp = e.rbp
  r13 : s.core.read .r13 = e.r13
  digest : s.memory.readBytes out.toNat 32 =
    some ((Silmaril.Crypto.SHA256.digest (consumed.map UInt8.ofBitVec)).map UInt8.toBitVec)
  ccode : s.memory.fetchBytes Binary.textBase.toNat Silmaril.Crypto.X86.Sha256O2.size =
    some (Silmaril.Crypto.X86.Sha256O2.image Binary.textBase Binary.rodataBase)
  kTable : s.memory.readBytes Binary.rodataBase.toNat Silmaril.Crypto.X86.Sha256O2.kSize =
    some Silmaril.Crypto.X86.Sha256O2.kBytes
  loopCode : Loaded s.memory base code
  finalCode : Loaded s.memory Final.base Final.code

theorem srcIdx_eq_sourceIndex (i : Fin 32) : Final.srcIdx i.val = HexLookup.sourceIndex i := by
  rw [HexReference.sourceIndex_word_lane]; rfl

/-- **VERIFIED. The output loop writes the digest.** -/
theorem outBytes_digest (sb message : List Byte)
    (value : (stateOf sb).toState = Silmaril.Crypto.SHA256.hash (message.map UInt8.ofBitVec)) :
    Final.outBytes sb =
      (Silmaril.Crypto.SHA256.digest (message.map UInt8.ofBitVec)).map UInt8.toBitVec := by
  rw [← HexReference.permutation_reference sb message value]
  simp only [List.map_map, Function.comp_def, Final.outBytes]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
  rw [← srcIdx_eq_sourceIndex]
  rfl

/-- **VERIFIED. The padding completes the hash.** -/
theorem hfin_hash {consumed tail : List Byte} {blocks : List (List Byte)}
    (hr : Driver.ReadInv consumed blocks tail) :
    ((TailPaddingReference.blocks tail (BitVec.ofNat 64 consumed.length)).foldl compressBlock
      (blocks.foldl compressBlock IV)).toState =
        Silmaril.Crypto.SHA256.hash (consumed.map UInt8.ofBitVec) := by
  rw [← List.foldl_append, fold_toState _ _ (fun b hb => by
    rcases List.mem_append.mp hb with h | h
    · exact hr.full b h
    · exact TailPaddingReference.full tail hr.room _ b h), IV_toState]
  have hp := TailPaddingReference.paddedBlocks blocks tail hr.full hr.room
  rw [← hr.bytes] at hp
  rw [← hp, Driver.fold_paddedBlocks]

set_option maxRecDepth 100000 in
/-- **VERIFIED. `sha_final`, from the read loop's padding cut point to the digest.** -/
theorem final_digest {e : Loop} {consumed : List Byte} {s : XState} {out : Word}
    (hlv : s.faulted = false) (hl : Loaded s.memory Final.base Final.code)
    (hl0 : Loaded s.memory base code) (h : AtPad e consumed s) (hout : OutBuf s.memory e.sp out) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep8 s t ∧ t.faulted = false ∧
      AtOut e consumed out t := by
  obtain ⟨hrip, hF, hdx, blocks, tail, hr, hb⟩ := h
  let c : Final.Ctx := ⟨e.sp, out, blocks.foldl compressBlock IV, tail,
    BitVec.ofNat 64 consumed.length, s.core.read, s.memory⟩
  have hg : Final.Geo c := ⟨hF.spAlign, hF.spLow, hF.spHigh, hF.stackW, hF.stackR, hF.code,
    hF.kTable, hl, hout.slot, hout.writable, hout.readable, hout.low, hout.high, hout.apart,
    hb.hRoom⟩
  have hpre : Final.pre c s :=
    ⟨⟨hF.rsp, rfl, rfl, Memory.WritesWithin.refl _ _⟩, rfl, hdx, hb.hState, hb.hTail,
      hb.hBlen⟩
  have hrip0 : s.core.rip = Final.base + BitVec.ofNat 64 0 := by rw [hrip]; rfl
  obtain ⟨t, hrun, hlv', hlt, hript, ⟨hFt, sb, hsb, hst, hdig⟩⟩ :=
    Final.final_runs c hg s hlv hl hrip0 hpre
  refine ⟨t, hrun, hlv', hript, hFt.rsp, hFt.rbp.trans hF.rbp, hFt.r13.trans hF.r13, ?_,
    Final.ccode_of_writes hg hFt.writes, Final.kTable_of_writes hg hFt.writes, ?_, hlt⟩
  · rw [hdig, outBytes_digest sb consumed (by rw [hst]; exact hfin_hash hr)]
  · unfold Loaded; rw [hFt.writes.fetchBytes]; · exact hl0
    intro o ho hin; have := hg.codeApart hin
    rw [Update.code_length] at ho; rw [Update.base_toNat] at this; omega

end Silmaril.Apps.Sha256sum.Binary.Digest
