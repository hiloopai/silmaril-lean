module

public import Silmaril.Apps.Sha256sum.Binary.Digest.CompressCall
public import Silmaril.X86.SegVC.Mem

/-! # Frame, struct and call facts for the `sha_update` segment

The memory reasoning `Digest.Update`'s VCs need, stated once:

* `sp`-relative addresses do not wrap (`toNat_sp_add`, `toNat_sp_sub`);
* the `struct sha` facts (`Buf`, in `Digest.Update`) survive any write outside the struct
  (`StateHolds.transfer`, `loadN_transfer`);
* **the `sha256_compress` call** at either site: the System V entry the pilot contract asks
  for (`compressPre_of`), from the caller's frame facts, and what its postcondition gives
  back (`compressPost_facts`): the new chaining value, the callee-saved registers, the stack
  pointer, and a write footprint inside `state[]` and the callee frame.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest

open Silmaril.X86 (State MState Word Byte sysv64)
open Silmaril.Process (Memory Region)
open Silmaril.X86.Ext
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Crypto.X86.Sha256O2
open Silmaril.Crypto.SHA256.Kernel (InitHash)

/-- An `sp`-relative address above `sp` does not wrap. -/
theorem toNat_sp_add {sp : Word} (h : sp.toNat + 0x1000 < 2 ^ 64) {n : Nat} (hn : n ≤ 0x1000) :
    (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- An `sp`-relative address below `sp` does not wrap. -/
theorem toNat_sp_sub {sp : Word} (h : 0x420000 ≤ sp.toNat) {n : Nat} (hn : n ≤ 0x420000) :
    (sp - BitVec.ofNat 64 n).toNat = sp.toNat - n := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- A chaining value survives writes that miss its 32 bytes. -/
theorem StateHolds.transfer {m m' : Memory} {a : Word} {H : InitHash} (h : StateHolds m a H)
    {P : Nat → Prop} (hw : Memory.WritesWithin m m' P) (hout : ∀ o < 32, ¬ P (a.toNat + o)) :
    StateHolds m' a H := by
  obtain ⟨bytes, hr, hs⟩ := h
  exact ⟨bytes, (hw.readBytes hout).trans hr, hs⟩

/-- A load survives writes that miss it. -/
theorem loadN_transfer {m m' : Memory} {a : Word} {k : Nat} {P : Nat → Prop}
    (hw : Memory.WritesWithin m m' P) (hout : ∀ o < k, ¬ P (a.toNat + o)) :
    loadN m' a k = loadN m a k := by
  simp only [loadN, hw.readBytes hout]

/-- The bytes at `[sp - 8, sp)` after the `call` pushed `ret` read back as `ret`. -/
theorem retOf_of {x : XState} {ret : Word}
    (h : x.memory.readBytes (x.core.read .rsp).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [ret])) :
    retOf (toExtState x) = ret := by
  simp [retOf, toExtState, h]

/-- The footprint of a `sha256_compress` call from `digest_file` (frame at `sp`): `state[]`
at `sp + 0x20`, and the callee frame with its red zone below the return slot. -/
def calleeSpan (sp : Word) (a : Nat) : Prop :=
  (sp.toNat - 352 ≤ a ∧ a < sp.toNat - 8) ∨ (sp.toNat + 0x20 ≤ a ∧ a < sp.toNat + 0x40)

/-- **The System V entry of `sha256_compress`** at a call site of `digest_file`: the state
right after the `call` (return address `ret` pushed at `sp - 8`), with `state[]` at
`sp + 0x20` and the block either in `.bss` above the K table (`iobuf`) or the struct's
own buffer at `sp + 0x40`. -/
theorem compressPre_of {x : XState} {sp blk ret : Word} {H : InitHash}
    (hrip : x.core.rip = textBase)
    (hdi : x.core.read .rdi = sp + 0x20#64) (hsi : x.core.read .rsi = blk)
    (hsp : x.core.read .rsp = sp - 8#64)
    (hret : x.memory.readBytes (sp - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [ret]))
    (hcode : x.memory.fetchBytes textBase.toNat size = some (image textBase rodataBase))
    (hk : x.memory.readBytes rodataBase.toNat kSize = some kBytes)
    (hst : StateHolds x.memory (sp + 0x20#64) H)
    (hblk : ∃ bs, x.memory.readBytes blk.toNat 64 = some bs)
    (hW : x.memory.Permitted .write (sp.toNat - 400) 552)
    (hR : x.memory.Permitted .read (sp.toNat - 400) 552)
    (spAlign : sp.toNat % 16 = 0) (spLow : 0x420000 ≤ sp.toNat)
    (spHigh : sp.toNat + 0x1000 < 2 ^ 64)
    (hgeo : (0x408010 ≤ blk.toNat ∧ blk.toNat + 64 ≤ 0x41f000) ∨ blk.toNat = sp.toNat + 0x40) :
    CompressPre (toExtState x) ∧ retOf (toExtState x) = ret := by
  have hret' : retOf (toExtState x) = ret := retOf_of (by rw [hsp]; exact hret)
  have e20 : (sp + 0x20#64).toNat = sp.toNat + 0x20 := toNat_sp_add spHigh (by decide)
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := toNat_sp_sub spLow (by decide)
  refine ⟨?_, hret'⟩
  simp only [CompressPre, toExtState] at hret' ⊢
  rw [hret', hdi, hsi, hsp]
  have hff : sysv64.frameFloor (sp - 8#64).toNat frameSize = sp.toNat - 8 - 344 := by
    rw [frameFloor_frameSize, e8]
  have hfe : sysv64.frameExtent frameSize = 344 := by
    simp [Silmaril.Machine.CallingConvention.frameExtent]
  obtain ⟨sb, hsb, _⟩ := hst
  refine ⟨hrip, hcode, layout_relocFits ret, hk, hdi, hsi, hsp, ?_, ?_, ⟨sb, hsb⟩, ?_, hblk,
    ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · show (sp - 8#64).toNat % 16 = 8
    rw [e8]; omega
  · show x.memory.readBytes (sp - 8#64).toNat 8 = some (leBytes ret 8)
    rw [leBytes_eight]; exact hret
  · rw [e20]; exact Memory.Permitted.sub hW (by omega) (by omega) (by omega)
  · rw [hff, hfe]; exact Memory.Permitted.sub hR (by omega) (by omega) (by omega)
  · rw [hff, hfe]; exact Memory.Permitted.sub hW (by omega) (by omega) (by omega)
  · rw [hfe, e8]; omega
  · intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [stateRegion, blockRegion, codeRegion, kTableRegion, frameRegion, returnSlot,
        layout, textBase, rodataBase, size, kSize, Silmaril.Process.addressLimit, e20, Silmaril.Machine.CallingConvention.frameFloor,
        Silmaril.Machine.CallingConvention.frameExtent,
        frameSize_eq, Silmaril.X86.sysv64_redZone,
        e8, BitVec.toNat_ofNat] <;> omega
  · simp only [regions, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, Region.Disjoint, stateRegion, blockRegion,
      codeRegion, kTableRegion, frameRegion, returnSlot, layout, textBase, rodataBase, size,
      kSize, e20, e8, Silmaril.Machine.CallingConvention.frameFloor, frameSize_eq,
      Silmaril.Machine.CallingConvention.frameExtent,
      Silmaril.X86.sysv64_redZone, BitVec.toNat_ofNat, IsEmpty.forall_iff, implies_true, and_true]
    omega
  · rw [e20]; omega

/-- **What a `sha256_compress` call from `digest_file` gives back.** -/
theorem compressPost_facts {x : XState} {fin : MState} {sp blk : Word} {H : InitHash}
    {bs : List Byte}
    (_hpre : CompressPre (toExtState x)) (hpost : CompressPost (toExtState x) fin)
    (hdi : x.core.read .rdi = sp + 0x20#64) (hsi : x.core.read .rsi = blk)
    (hsp : x.core.read .rsp = sp - 8#64)
    (hst : StateHolds x.memory (sp + 0x20#64) H)
    (hb : x.memory.readBytes blk.toNat 64 = some bs)
    (spLow : 0x420000 ≤ sp.toNat) (spHigh : sp.toNat + 0x1000 < 2 ^ 64) :
    StateHolds fin.memory (sp + 0x20#64) (compressBlock H bs) ∧
      fin.core.read .rsp = sp ∧
      (∀ r ∈ sysv64.calleeSaved, fin.core.read r = x.core.read r) ∧
      Memory.WritesWithin x.memory fin.memory (calleeSpan sp) ∧
      fin.core.rip = retOf (toExtState x) := by
  obtain ⟨P, hrip⟩ := hpost
  have e20 : (sp + 0x20#64).toNat = sp.toNat + 0x20 := toNat_sp_add spHigh (by decide)
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := toNat_sp_sub spLow (by decide)
  simp only [toExtState] at P
  rw [hdi, hsi, hsp] at P
  obtain ⟨sb, hsb, hsH⟩ := hst
  refine ⟨?_, ?_, fun r hr => P.saved r hr, ?_, hrip⟩
  · have := P.compressed sb bs hsb hb
    rwa [hsH] at this
  · rw [P.rsp]; bv_omega
  · refine P.untouched.mono fun a ha => ?_
    simp only [Footprint, stateRegion, frameRegion, Region.Contains] at ha
    rw [frameFloor_frameSize] at ha
    simp only [Silmaril.Machine.CallingConvention.frameExtent, frameSize_eq, Silmaril.X86.sysv64_redZone,
      e20, e8] at ha
    simp only [calleeSpan]
    omega

/-- **The `sha256_compress` call as a VC step** at a call site of `digest_file`: the callee's
precondition holds, and every state its postcondition allows satisfies `Q`, given that `Q`
holds of every return with the new chaining value, `rsp` back at `sp`, the callee-saved
registers kept, writes only inside `calleeSpan`, and `rip` at the return address. -/
theorem compress_vc (r11Of : Core → Word) {x : XState} {sp blk ret : Word} {H : InitHash}
    {bs : List Byte} {Q : XState → Prop}
    (hrip : x.core.rip = textBase)
    (hdi : x.core.read .rdi = sp + 0x20#64) (hsi : x.core.read .rsi = blk)
    (hsp : x.core.read .rsp = sp - 8#64)
    (hret : x.memory.readBytes (sp - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [ret]))
    (hcode : x.memory.fetchBytes textBase.toNat size = some (image textBase rodataBase))
    (hk : x.memory.readBytes rodataBase.toNat kSize = some kBytes)
    (hst : StateHolds x.memory (sp + 0x20#64) H)
    (hb : x.memory.readBytes blk.toNat 64 = some bs)
    (hW : x.memory.Permitted .write (sp.toNat - 400) 552)
    (hR : x.memory.Permitted .read (sp.toNat - 400) 552)
    (spAlign : sp.toNat % 16 = 0) (spLow : 0x420000 ≤ sp.toNat)
    (spHigh : sp.toNat + 0x1000 < 2 ^ 64)
    (hgeo : (0x408010 ≤ blk.toNat ∧ blk.toNat + 64 ≤ 0x41f000) ∨ blk.toNat = sp.toNat + 0x40)
    (hQ : ∀ fin : MState, StateHolds fin.memory (sp + 0x20#64) (compressBlock H bs) →
      fin.core.read .rsp = sp → (∀ r ∈ sysv64.calleeSaved, fin.core.read r = x.core.read r) →
      Memory.WritesWithin x.memory fin.memory (calleeSpan sp) → fin.core.rip = ret →
      Q (withExtState x fin)) :
    (compressCall r11Of).pre x ∧ ∀ t, (compressCall r11Of).post x t → Q t := by
  have hpre := compressPre_of hrip hdi hsi hsp hret hcode hk hst ⟨bs, hb⟩ hW hR spAlign spLow
    spHigh hgeo
  refine ⟨hpre.1, fun t ht => ?_⟩
  obtain ⟨fin, rfl, hpost⟩ := ht
  obtain ⟨h1, h2, h3, h4, h5⟩ := compressPost_facts hpre.1 hpost hdi hsi hsp hst hb spLow spHigh
  exact hQ fin h1 h2 h3 h4 (h5.trans hpre.2)

end Silmaril.Apps.Sha256sum.Binary.Digest
