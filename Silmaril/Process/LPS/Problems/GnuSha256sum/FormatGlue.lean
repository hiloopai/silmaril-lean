module

public import Silmaril.Apps.Sha256sum.Stdout.FmtPrefix
public import Silmaril.Apps.Sha256sum.Stdout.FormatSuffix

/-! # GNU `sha256sum`: the format segment's prefix as a `Seg`

`prefixSeg : Seg domain Wire.Digested HexEntryCutP`: from `Digested` (`0x40310a`, after
`sha_final`) every execution reaches the hex loop's entry `0x404541` (`Stdout.FmtPrefix`:
`pfx_ret`, `pfx_decide`, `pfx_scan`, retiring steps only, no system call) with

* `Stdout.HexEntry g.x d` for `d` the digest of the message (the precondition of
  `Stdout.hex_loop`), the stdout layer empty (`Obuf []`, nothing written: `Coalesced h [] []`),
* the registers the suffix reads after the loop (`ebx = needs_escape = 0`,
  `bpl = digest_delim = '\n'`, `r12 = "-"`, `r13d = binary = 0`) in the form of
  `Stdout.HexExitAt`, and `cmain`'s memory as `Stdout.SufMem` (`gnu-r3-fmtsuffix`),
* the answer: `hexLower d ++ recordTail` is `expected message`.

Status: **VERIFIED** (no `sorry`, standard axioms only).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum.FormatGlue

open Silmaril.Process.LPS.Problems.GnuSha256sum
open Silmaril.Process.LPS.Problems.GnuSha256sum.Wire
open Silmaril.Apps.Sha256sum.Stdout
open Silmaril.Apps.Sha256sum.X86Sys (XState ofU8)
open Silmaril.Apps.Sha256sum.Binary.Digest (Loop AtOut)
open Silmaril.X86 (Word)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- **At the hex loop's entry** `0x404541`, for the digest `d`, the buffer `buf` and the bytes
`emitted` so far: what `Stdout.hex_loop` needs, and what the suffix needs of the registers and
memory it inherits (`Stdout.HexExitAt`). -/
structure AtHexEntry (message : List Byte) (d buf emitted : Apps.Sha256sum.Bytes) (g : GS)
    (h : List Ev) : Prop where
  ok : Ok message g h
  rip : g.x.core.rip = 0x404541#64
  code : Apps.Sha256sum.Lift.Code g.x.memory
  fd0 : ∃ s, g.k.fds 0 = some s
  fd1 : g.k.fds 1 = some .stdout
  fd2 : ∃ s, g.k.fds 2 = some s
  entry : HexEntry g.x d
  rbx : (g.x.core.read .rbx).setWidth 32 = 0#32
  rbp : (g.x.core.read .rbp).setWidth 8 = 0x0a#8
  r12 : g.x.core.read .r12 = 0x406052#64
  r13 : (g.x.core.read .r13).setWidth 32 = 0#32
  mem : SufMem (g.x.core.read .rsp) g.x.memory
  obuf : Obuf g.x.memory buf
  co : Coalesced h buf emitted
  read : stdinRead h = message
  answer : (emitted ++ Apps.Sha256sum.hexLower d ++ recordTail).map UInt8.toBitVec =
    expected message

/-- The cut at the hex loop's entry. -/
def HexEntryCutP : Cut := fun _ message g h => ∃ d buf emitted, AtHexEntry message d buf emitted g h

theorem ofU8_eq : ofU8 = UInt8.toBitVec := by
  funext b; apply BitVec.eq_of_toNat_eq; simp [ofU8]

theorem record_answer (message : List Byte) :
    (([] : Apps.Sha256sum.Bytes) ++
        Apps.Sha256sum.hexLower (Silmaril.Crypto.SHA256.digest (message.map UInt8.ofBitVec)) ++
        recordTail).map UInt8.toBitVec = expected message := by
  rw [expected_eq_record]
  rfl

/-- A read outside the `prefix_tag` spill survives the prefix's only store. -/
theorem kr {m m' : Memory} {T : Nat} (hw : Memory.WritesWithin m m' (fun a => T ≤ a ∧ a < T + 4))
    {acc : Silmaril.Process.Access} {addr len : Nat} {v : Option (List Silmaril.X86.Byte)}
    (hd : addr + len ≤ T ∨ T + 4 ≤ addr) (h : m.readWith acc addr len = v) :
    m'.readWith acc addr len = v :=
  keep_read hw (fun o ho hin => by omega) h

set_option maxHeartbeats 1000000 in
/-- **The prefix of the format segment** (VERIFIED): `Digested → HexEntryCutP`. -/
theorem prefixSeg (domain : List Byte → Prop) : Seg domain Digested HexEntryCutP := by
  intro prog posix fs message g h _ hd
  obtain ⟨ok, hrd, hout, kt, e, -, hat, hcl⟩ := hd
  obtain ⟨x, k, ex⟩ := g
  have hex : ex = none := ok.1
  subst hex
  have hf : x.faulted = false := ok.2.2.2.2.2
  have hcm := hcl.cmain
  have hc : Apps.Sha256sum.Lift.Code x.memory := hcm.code
  have hrip : x.core.rip = 0x40310a#64 := by rw [hat.rip]; rfl
  have hdig := hat.digest
  have hdash := hcl.savedR12.2
  have hr13 : x.core.read .r13 = e.rbp := hat.r13.trans hcl.rbpR13.symm
  refine (pfx_ret hf hc hrip hat.rsp hat.rbp hr13 hcl).leads rfl ok fun t ht => ?_
  obtain ⟨hf1, hc1, hrip1, hrsp1, hrax1, hrbx1, hr121, hr141, hmem1⟩ := ht
  rw [← hmem1] at hcm hdig hdash
  refine (pfx_decide hf1 hc1 hrip1 hrsp1 hrax1 hrbx1 hr121 hr141 hcm).leads rfl
    (Ok.with_x ok hf1) fun u hu => ?_
  have hdash2 : u.memory.readWith .read 0x406052 2 = some [0x2d#8, 0#8] := by
    refine kr hu.foot ?_ hdash
    have := hcm.spBound
    have := hcl.spRange
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine (pfx_scan hu hdash2).leads rfl (Ok.with_x ok hu.faulted) fun v hv => ?_
  obtain ⟨hf3, hc3, hrip3, hrsp3, hrbx3, hrbp3, hr123, hr133, hr143, htag3, hfoot3⟩ := hv
  have hfoot : Memory.WritesWithin t.memory v.memory
      (fun a => (e.sp + 0xd0#64 + 0x10#64).toNat ≤ a ∧ a < (e.sp + 0xd0#64 + 0x10#64).toNat + 4) :=
    hfoot3
  clear hfoot3
  obtain ⟨_, htab, ⟨hb1, hb2⟩, hsr, hsw, hokf, ⟨hidx, hnop⟩, hhs, -, -, -, hee, hob⟩ := hcm
  generalize hsp : e.sp + 0xd0#64 = sp at *
  have e10 : (sp + 0x10#64).toNat = sp.toNat + 0x10 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e10] at hfoot
  have ex : ∀ c : Nat, c < 0x100 → (sp + BitVec.ofNat 64 c).toNat = sp.toNat + c := by
    intro c hc; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine .done ⟨Silmaril.Crypto.SHA256.digest (message.map UInt8.ofBitVec), [], [], ?_⟩
  refine ⟨Ok.with_x ok hf3, hrip3, hc3, ⟨_, kt.fd0⟩, kt.fd1, ⟨_, kt.fd2⟩, ?_, ?_, ?_, hr123, ?_,
    ?_, ?_, ?_, hrd, record_answer message⟩
  · -- `HexEntry`
    refine ⟨Silmaril.Crypto.SHA256.digest_length _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrsp3]; omega
    · rw [hrsp3, hfoot.permitted_iff]
      exact X86.Ext.Memory.Permitted.sub hsr (by omega) (by omega) (by omega)
    · rw [hrsp3, hfoot.permitted_iff]
      exact X86.Ext.Memory.Permitted.sub hsw (by omega) (by omega) (by omega)
    · rw [hr143, hrsp3]
    · rw [hrsp3, ofU8_eq]
      have hb : (bin e).toNat = sp.toNat + 0x70 := by
        unfold bin; rw [hsp]; exact ex 0x70 (by omega)
      unfold Memory.readBytes at hdig
      rw [hb] at hdig
      exact kr hfoot (by omega) hdig
    · exact kr hfoot (by omega) htab
  · rw [hrbx3]; rfl
  · rw [hrbp3]; rfl
  · rw [hr133]; rfl
  · -- `SufMem`
    rw [hrsp3]
    refine ⟨⟨hb1, hb2⟩, (hfoot.permitted_iff _ _ _).mpr hsr, (hfoot.permitted_iff _ _ _).mpr hsw,
      htag3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact kr hfoot (by rw [ex 0x2c (by omega)]; omega) hokf
    · exact kr hfoot (by rw [ex 0x8 (by omega)]; omega) hidx
    · exact kr hfoot (by rw [ex 0x50 (by omega)]; omega) hnop
    · exact kr hfoot (by omega) hhs
    · exact kr hfoot (by omega) hee
    · exact kr hfoot (by omega) hdash
  · exact Obuf.of_writes hob hfoot (fun a ha h => by omega)
  · show out h ++ [] = []
    rw [hout]; rfl

end Silmaril.Process.LPS.Problems.GnuSha256sum.FormatGlue
