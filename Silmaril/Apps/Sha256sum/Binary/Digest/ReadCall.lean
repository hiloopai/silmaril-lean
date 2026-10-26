module

public import Silmaril.Apps.Sha256sum.Binary.Digest.Spec
public import Silmaril.Apps.Sha256sum.Lift.Mem

/-! # The `read` call of `digest_file`'s loop, around the system call

At the loop head (`0x402ef0`) `digest_file` calls `sc3(0, fd, iobuf, 32768)` (the descriptor
is in its frame at `sp + 8`); `sc3` (`Binary.Sc3`, at `0x401010`) moves the arguments into
place and traps with `read(fd, iobuf, 32768)`; after the kernel's reply, `ret` returns to
`0x402f06`, the `AfterRead` cut point. This file proves the two silent halves, over
`X86Sys.Isa.sys` (retiring steps only, no `r11`):

* `head_runs`: from `AtHead`, the process reaches the `syscall` at `0x40101c` with
  `rax = 0`, `rdi = fd`, `rsi = iobuf`, `rdx = 32768`, the return address `0x402f06` pushed
  at `sp - 8`, nothing else written, and the callee-saved registers kept (`AtTrap`);
* `ret_runs`: from the state after the kernel's reply to that call (any `rcx`, `r11`, `rax`),
  `ret` reaches `0x402f06` with `rsp = sp` (`ret_runs`).

`afterRead_of_reply` (`ReadLoop`) then shows that a reply with data `b` lands in
`AfterRead consumed b`.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall

set_option maxRecDepth 100000

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Update (iobuf)

/-! ## Register reads with proofs

`seg_read`'s register lemmas are `rfl` lemmas, which `simp` applies without a proof, leaving
the kernel to check the rewritten goal by unfolding; on a state whose flags are a symbolic
`logicFlagsN` term that check recurses too deeply. These copies are not `rfl` lemmas, so `simp`
records them as rewrites. -/

theorem read_mk' (regs : Silmaril.Machine.RegisterFile Silmaril.X86.Reg Silmaril.X86.Word) (x : Silmaril.X86.Word)
    (f : Silmaril.X86.Flags) (fs : Silmaril.X86.Word) (q : Silmaril.X86.Reg) :
    (Silmaril.X86.State.mk regs x f fs).read q = regs q := Silmaril.X86.SegVC.read_mk regs x f fs q
theorem core_regs' (s : Silmaril.X86.State) (q : Silmaril.X86.Reg) : s.regs q = s.read q :=
  Silmaril.X86.SegVC.core_regs s q
theorem read_mk_regs' (s : Silmaril.X86.State) (r : Silmaril.X86.Word) (f : Silmaril.X86.Flags) (fs : Silmaril.X86.Word)
    (q : Silmaril.X86.Reg) : (Silmaril.X86.State.mk s.regs r f fs).read q = s.read q :=
  Silmaril.X86.Ext.read_mk_regs s r f fs q
theorem read_with_rip' (s : Silmaril.X86.State) (r : Silmaril.X86.Word) (q : Silmaril.X86.Reg) :
    ({ s with rip := r } : Silmaril.X86.State).read q = s.read q := Silmaril.X86.Ext.read_with_rip s r q

end Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall

/-- `seg_read` with lemmas that carry proofs (see `ReadCall.read_mk'`). -/
macro "xread " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (simp only [Silmaril.X86.State.read_write_same, Silmaril.X86.State.read_write_other, ne_eq,
      reduceCtorEq, not_false_eq_true,
      Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall.read_mk',
      Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall.core_regs',
      Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall.read_mk_regs',
      Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall.read_with_rip', $ls,*]))

namespace Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Update (iobuf)

/-- The return address `sc3` gets from the loop's `call`. -/
def retAddr : Word := 0x402f06#64

/-- The return address, as stored. -/
def retBytes : List Byte := Silmaril.Machine.LittleEndian.encodeWords [retAddr]

/-- At the `syscall` of `sc3` (`0x40101c`), for the loop's `read`, from the loop head `s0`:
the arguments in place, the return address pushed (the only write), the callee-saved
registers of `s0` kept. -/
structure AtTrap (e : Loop) (s0 t : XState) : Prop where
  rip : t.core.rip = 0x40101c#64
  rax : t.core.read .rax = 0#64
  rdi : t.core.read .rdi = e.fd
  rsi : t.core.read .rsi = iobuf
  rdx : t.core.read .rdx = 0x8000#64
  rsp : t.core.read .rsp = e.sp - 8#64
  rbx : t.core.read .rbx = s0.core.read .rbx
  rbp : t.core.read .rbp = s0.core.read .rbp
  r13 : t.core.read .r13 = s0.core.read .r13
  pushed : s0.memory.writeBytes (e.sp - 8#64).toNat retBytes = some t.memory

/-- The head's stop, at `sc3`'s entry. -/
def headStop (e : Loop) (s0 t : XState) : Prop :=
  t.core.read .rsp = e.sp - 8#64 ∧ t.core.read .rdi = 0#64 ∧ t.core.read .rsi = e.fd ∧
    t.core.read .rdx = iobuf ∧ t.core.read .rcx = 0x8000#64 ∧
    t.core.read .rbx = s0.core.read .rbx ∧ t.core.read .rbp = s0.core.read .rbp ∧
    t.core.read .r13 = s0.core.read .r13 ∧
    s0.memory.writeBytes (e.sp - 8#64).toNat retBytes = some t.memory

theorem xor32_self (x : Word) :
    BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x) = 0#64 := by simp

/-- `0x401010 - 0x402ef0`, as an offset from the loop head. -/
def scOff : Nat := 18446744073709543712

theorem vc_head (r11 : Core → Word) (e : Loop) (consumed : List Byte) (s0 : XState) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 0 → (s = s0 ∧ AtHead e consumed s0) →
      wpN (Isa.sys r11) code listing [] [(scOff, headStop e s0)] [] [] base none 6 0 s := by
  intro s hlv hl hrip ⟨rfl, hh⟩
  have hF := hh.2.1
  have hfd := hF.fdSlot
  rw [← hF.rsp] at hfd
  seg_vc [listing, scOff, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hfd]
  have hsp := hF.rsp
  have spL := hF.spLow
  have e8 : (e.sp - 8#64).toNat = e.sp.toNat - 8 := toNat_sp_sub spL (by decide)
  have hret : base + 22#64 = retAddr := rfl
  rw [hsp, e8, hret]
  refine ⟨Memory.Permitted.sub hF.stackW (by omega) (by omega) (by omega), fun after hw =>
    ⟨Loaded.of_stored hl (Stored.of_writeBytes hw) ?_, ?_⟩⟩
  · simp only [Update.code_length, Update.base_toNat, Silmaril.Machine.LittleEndian.encodeWords_length,
      List.length_cons, List.length_nil]; omega
  · refine ⟨by seg_read [hsp], by seg_read []; exact xor32_self _, by seg_read [], by seg_read []; rfl, by seg_read [],
      by xread [], by xread [], by xread [], ?_⟩
    rw [e8]; exact hw

/-- `sc3`'s stop, at the `syscall`: from the head's stop `q`. -/
def trapStop (e : Loop) (s0 q t : XState) : Prop :=
  t.core.read .rax = 0#64 ∧ t.core.read .rdi = e.fd ∧ t.core.read .rsi = iobuf ∧
    t.core.read .rdx = 0x8000#64 ∧ t.core.read .rsp = e.sp - 8#64 ∧
    t.core.read .rbx = s0.core.read .rbx ∧ t.core.read .rbp = s0.core.read .rbp ∧
    t.core.read .r13 = s0.core.read .r13 ∧ t.memory = q.memory

theorem vc_sc (r11 : Core → Word) (e : Loop) (s0 q : XState) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Sc3.base Sc3.code →
      s.core.rip = Sc3.base + BitVec.ofNat 64 0 → (s = q ∧ headStop e s0 q) →
      wpN (Isa.sys r11) Sc3.code Sc3.listing [] [(12, trapStop e s0 q)] [] [] Sc3.base none 5 0
        s := by
  intro s hlv hl hrip ⟨rfl, hsp, hdi, hsi, hdx, hcx, hbx, hbp, h13, _⟩
  seg_vc [Sc3.listing, hrip, hl]
  exact ⟨by xread [hdi], by xread [hsi], by xread [hdx], by xread [hcx], by xread [hsp],
    by xread [hbx], by xread [hbp], by xread [h13], rfl⟩

/-- `ret`'s stop, back in the loop at `0x402f06`: from the state `u` after the reply. -/
def retStop (e : Loop) (u t : XState) : Prop :=
  t.core.read .rsp = e.sp ∧ (∀ r, r ≠ .rsp → t.core.read r = u.core.read r) ∧
    t.memory = u.memory

/-- `0x402f06 - 0x401010`, as an offset from `sc3`. -/
def retOff : Nat := 7926

theorem vc_ret (r11 : Core → Word) (e : Loop) (u : XState) :
    ∀ s : XState, s.faulted = false → Loaded s.memory Sc3.base Sc3.code →
      s.core.rip = Sc3.base + BitVec.ofNat 64 14 →
      (s = u ∧ s.core.read .rsp = e.sp - 8#64 ∧ 0x420000 ≤ e.sp.toNat ∧
        s.memory.readBytes (e.sp - 8#64).toNat 8 = some retBytes) →
      wpN (Isa.sys r11) Sc3.code Sc3.listing [] [(retOff, retStop e u)] [] [] Sc3.base none 2 14
        s := by
  intro s hlv hl hrip ⟨rfl, hsp, spL, hrd⟩
  rw [← hsp] at hrd
  have hpop := Silmaril.X86.popWord_of_readBytes hrd
  have hoff : (retAddr - Sc3.base).toNat = 7926 := by decide
  seg_vc [Sc3.listing, retOff, hrip, hl, hpop, hoff]
  refine ⟨by xread [hsp]; exact BitVec.sub_add_cancel _ _, fun r hr => ?_, rfl⟩
  rw [Silmaril.X86.State.read_write_other _ _ _ _ hr]
  exact read_mk_regs' _ _ _ _ _

/-! ## The two silent halves -/

theorem retBytes_length : retBytes.length = 8 := rfl

/-- **VERIFIED. From the loop head to the `read` system call.** -/
theorem head_runs {e : Loop} {consumed : List Byte} {s : XState} (hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (h : AtHead e consumed s) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep s t ∧ t.faulted = false ∧
      Loaded t.memory base code ∧ Loaded t.memory Sc3.base Sc3.code ∧ AtTrap e s t := by
  have hF := h.2.1
  obtain ⟨t1, r1, hs1, hrip1, hl1, hlv1⟩ :=
    sound_one (I := Isa.sys (fun _ => 0)) listing_valid
      (pre := fun s' => s' = s ∧ AtHead e consumed s)
      ⟨vc_head (fun _ => 0) e consumed s, fun oc hoc => by simp at hoc⟩ s hlv hl h.1 ⟨rfl, h⟩
  obtain ⟨hsp1, hdi1, hsi1, hdx1, hcx1, hbx1, hbp1, h131, hpush⟩ := hs1
  have spL := hF.spLow
  have e8 : (e.sp - 8#64).toNat = e.sp.toNat - 8 := toNat_sp_sub spL (by decide)
  have hsc1 : Loaded t1.memory Sc3.base Sc3.code :=
    Loaded.of_stored hF.sc3 (Stored.of_writeBytes hpush) (by
      rw [e8, sc3_toNat, sc3_length, retBytes_length]; omega)
  have hrip1' : t1.core.rip = Sc3.base + BitVec.ofNat 64 0 := by
    change t1.core.rip = _ at hrip1; rw [hrip1]; decide
  obtain ⟨t2, r2, hs2, hrip2, hl2, hlv2⟩ :=
    sound_one (I := Isa.sys (fun _ => 0)) Sc3.listing_valid
      (pre := fun s' => s' = t1 ∧ headStop e s t1)
      ⟨vc_sc (fun _ => 0) e s t1, fun oc hoc => by simp at hoc⟩ t1 hlv1 hsc1 hrip1'
      ⟨rfl, hsp1, hdi1, hsi1, hdx1, hcx1, hbx1, hbp1, h131, hpush⟩
  obtain ⟨hax2, hdi2, hsi2, hdx2, hsp2, hbx2, hbp2, h132, hm2⟩ := hs2
  refine ⟨t2, r1.trans r2, hlv2, by rw [hm2]; exact hl1, hl2,
    ⟨?_, hax2, hdi2, hsi2, hdx2, hsp2, hbx2, hbp2, h132, by
      change t2.memory = _ at hm2; rw [hm2]; exact hpush⟩⟩
  change t2.core.rip = _ at hrip2; rw [hrip2]; decide

/-- **VERIFIED. From the reply of the `read` back into the loop** (`ret` to `0x402f06`). -/
theorem ret_runs {e : Loop} {u : XState} (hlv : u.faulted = false)
    (hl : Loaded u.memory Sc3.base Sc3.code) (hrip : u.core.rip = 0x40101e#64)
    (hsp : u.core.read .rsp = e.sp - 8#64) (spL : 0x420000 ≤ e.sp.toNat)
    (hrd : u.memory.readBytes (e.sp - 8#64).toNat 8 = some retBytes) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep u t ∧ t.faulted = false ∧
      t.core.rip = retAddr ∧ retStop e u t := by
  have hrip' : u.core.rip = Sc3.base + BitVec.ofNat 64 14 := by rw [hrip]; decide
  obtain ⟨t, r, hs, hrip2, _, hlv2⟩ :=
    sound_one (I := Isa.sys (fun _ => 0)) Sc3.listing_valid
      (pre := fun s' => s' = u ∧ s'.core.read .rsp = e.sp - 8#64 ∧ 0x420000 ≤ e.sp.toNat ∧
        s'.memory.readBytes (e.sp - 8#64).toNat 8 = some retBytes)
      ⟨vc_ret (fun _ => 0) e u, fun oc hoc => by simp at hoc⟩ u hlv hl hrip' ⟨rfl, hsp, spL, hrd⟩
  refine ⟨t, r, hlv2, ?_, hs⟩
  change t.core.rip = _ at hrip2; rw [hrip2]; decide

/-! ## Back at the cut point -/

/-- What the call writes, seen from the loop: the return slot below `sp`, and `iobuf`. -/
def callSpan (sp : Word) (a : Nat) : Prop :=
  (sp.toNat - 8 ≤ a ∧ a < sp.toNat) ∨ (iobuf.toNat ≤ a ∧ a < iobuf.toNat + 32768)

theorem callSpan_loopSpan {sp : Word} {a : Nat} (h : callSpan sp a) : loopSpan sp a := by
  unfold callSpan at h; unfold loopSpan Update.stackSpan
  rcases h with ⟨h1, h2⟩ | h
  · exact .inl (.inl ⟨by omega, h2⟩)
  · exact .inr h

/-- `LoopFrame` survives the call's writes. -/
theorem LoopFrame.transfer {e : Loop} {s t : XState} (h : LoopFrame e s)
    (hw : Memory.WritesWithin s.memory t.memory (callSpan e.sp))
    (hsp : t.core.read .rsp = e.sp) (hbx : t.core.read .rbx = s.core.read .rbx)
    (hbp : t.core.read .rbp = s.core.read .rbp) (h13 : t.core.read .r13 = s.core.read .r13) :
    LoopFrame e t := by
  have lo := h.spLow
  have hi := h.spHigh
  refine ⟨hsp, hbx.trans h.rbx, hbp.trans h.rbp, h13.trans h.r13, h.spAlign, lo, hi,
    (hw.permitted_iff _ _ _).mpr h.stackW, (hw.permitted_iff _ _ _).mpr h.stackR, ?_, ?_, ?_,
    (hw.permitted_iff _ _ _).mpr h.iobufW, (hw.permitted_iff _ _ _).mpr h.iobufR, ?_,
    h.keep.trans (hw.mono fun a ha => callSpan_loopSpan ha)⟩
  · rw [hw.fetchBytes]; · exact h.code
    intro off hoff hin
    simp only [callSpan, Binary.textBase, Silmaril.Crypto.X86.Sha256O2.size, iobuf] at hin hoff
    simp only [BitVec.toNat_ofNat] at hin; omega
  · rw [hw.readBytes]; · exact h.kTable
    intro off hoff hin
    simp only [callSpan, Binary.rodataBase, Silmaril.Crypto.X86.Sha256O2.kSize, iobuf] at hin hoff
    simp only [BitVec.toNat_ofNat] at hin; omega
  · rw [loadN_transfer hw]; · exact h.fdSlot
    intro o ho hin
    rw [toNat_sp_add hi (by decide)] at hin
    simp only [callSpan, iobuf, BitVec.toNat_ofNat] at hin; omega
  · unfold Loaded; rw [hw.fetchBytes]; · exact h.sc3
    intro o ho hin
    rw [sc3_length] at ho; rw [sc3_toNat] at hin
    simp only [callSpan, iobuf, BitVec.toNat_ofNat] at hin; omega

/-- The struct survives writes that miss it. -/
theorem Absorbed.transfer {m m' : Memory} {sp : Word} {consumed : List Byte} {P : Nat → Prop}
    (h : Absorbed m sp consumed) (hw : Memory.WritesWithin m m' P)
    (hout : ∀ a, sp.toNat + 0x20 ≤ a → a < sp.toNat + 0x90 → ¬ P a)
    (hi : sp.toNat + 0x1000 < 2 ^ 64) : Absorbed m' sp consumed := by
  obtain ⟨blocks, tail, hr, hb⟩ := h
  have e20 : (sp + 32#64).toNat = sp.toNat + 32 := toNat_sp_add hi (by decide)
  have e40 : (sp + 64#64).toNat = sp.toNat + 64 := toNat_sp_add hi (by decide)
  have e80 : (sp + 128#64).toNat = sp.toNat + 128 := toNat_sp_add hi (by decide)
  have e88 : (sp + 136#64).toNat = sp.toNat + 136 := toNat_sp_add hi (by decide)
  refine ⟨blocks, tail, hr, StateHolds.transfer hb.hState hw ?_, ?_, ?_, ?_, hb.hFull, hb.hRoom⟩
  · intro o ho; rw [e20]; exact hout _ (by omega) (by omega)
  · rw [hw.readBytes]; · exact hb.hTail
    intro o ho; have := hb.hRoom; rw [e40]; exact hout _ (by omega) (by omega)
  · rw [loadN_transfer hw]; · exact hb.hBlen
    intro o ho; rw [e80]; exact hout _ (by omega) (by omega)
  · rw [loadN_transfer hw]; · exact hb.hTotal
    intro o ho; rw [e88]; exact hout _ (by omega) (by omega)

/-- **VERIFIED. After the reply, back at `AfterRead`.** From the loop head `s` and the trap
state `t`, a state `u` after a reply that delivered `chunk` into `iobuf` (only `iobuf` written,
`rax` the count, `rip` past the `syscall`, the other registers the loop uses kept) returns, by
retiring steps, to `0x402f06` in `AfterRead consumed chunk`. -/
theorem afterRead_of_reply {e : Loop} {consumed chunk : List Byte} {s t u : XState}
    (hl : Loaded s.memory base code) (hh : AtHead e consumed s) (ht : AtTrap e s t)
    (hlv : u.faulted = false) (hsc : Loaded u.memory Sc3.base Sc3.code)
    (hw : Memory.WritesWithin t.memory u.memory
      (fun a => iobuf.toNat ≤ a ∧ a < iobuf.toNat + 32768))
    (hchunk : u.memory.readBytes iobuf.toNat chunk.length = some chunk)
    (hlen : chunk.length ≤ 32768)
    (hrip : u.core.rip = 0x40101e#64) (hax : u.core.read .rax = BitVec.ofNat 64 chunk.length)
    (hsp : u.core.read .rsp = t.core.read .rsp) (hbx : u.core.read .rbx = t.core.read .rbx)
    (hbp : u.core.read .rbp = t.core.read .rbp) (h13 : u.core.read .r13 = t.core.read .r13) :
    ∃ v, Silmaril.Machine.Execution.Reaches rStep u v ∧ v.faulted = false ∧
      Loaded v.memory base code ∧ AfterRead e consumed chunk v := by
  obtain ⟨_, hF, habs⟩ := hh
  have lo := hF.spLow
  have hi := hF.spHigh
  have e8 : (e.sp - 8#64).toNat = e.sp.toNat - 8 := toNat_sp_sub lo (by decide)
  have hpush := ht.pushed
  have hW1 : Memory.WritesWithin s.memory t.memory (callSpan e.sp) := by
    have := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp (Memory.writeBytes_writesOnly hpush)
    refine this.mono fun a ha => ?_
    rw [e8, retBytes_length] at ha; exact .inl ⟨ha.1, by omega⟩
  have hW : Memory.WritesWithin s.memory u.memory (callSpan e.sp) :=
    hW1.trans (hw.mono fun a ha => .inr ha)
  have hrd : u.memory.readBytes (e.sp - 8#64).toNat 8 = some retBytes := by
    rw [hw.readBytes]
    · rw [e8]
      have := Lift.readWith_wb_same (acc := .read) hpush (by
        rw [e8, retBytes_length]
        exact Memory.Permitted.sub hF.stackR (by omega) (by omega) (by omega))
      rw [e8, retBytes_length] at this; exact this
    · intro o ho hin; rw [e8] at hin; simp only [iobuf, BitVec.toNat_ofNat] at hin; omega
  obtain ⟨v, r, hlv', hrip', hvsp, hvr, hvm⟩ :=
    ret_runs hlv hsc hrip (hsp.trans ht.rsp) lo hrd
  have hWv : Memory.WritesWithin s.memory v.memory (callSpan e.sp) := by rw [hvm]; exact hW
  refine ⟨v, r, hlv', ?_, ⟨?_, ?_, ?_, hlen, ?_, ?_⟩⟩
  · unfold Loaded; rw [hWv.fetchBytes]; · exact hl
    intro o ho hin
    rw [Update.code_length] at ho; rw [Update.base_toNat] at hin
    simp only [callSpan, iobuf, BitVec.toNat_ofNat] at hin; omega
  · rw [hrip']; rfl
  · refine LoopFrame.transfer hF hWv hvsp ?_ ?_ ?_
    · rw [hvr _ (by decide), hbx, ht.rbx]
    · rw [hvr _ (by decide), hbp, ht.rbp]
    · rw [hvr _ (by decide), h13, ht.r13]
  · rw [hvm]; exact hchunk
  · rw [hvr _ (by decide), hax]
  · refine Absorbed.transfer habs hWv (fun a h1 h2 hin => ?_) hi
    simp only [callSpan, iobuf, BitVec.toNat_ofNat] at hin; omega

end Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall
