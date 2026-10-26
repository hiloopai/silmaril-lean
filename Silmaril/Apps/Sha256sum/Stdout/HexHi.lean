module

public import Silmaril.Apps.Sha256sum.Stdout.HexLo

/-! # The high-digit `out_putc` site of the hex loop (`0x4045c2 → 0x404578`)

```
4045c2: cmp $0x1000,%rax ; jne 404560          -- buffer not full
4045ca: call out_flush ; mov olen,%rax ; jmp 404560
404560: lea 1(%rax),%rdx ; mov %bpl,obuf(%rax) ; mov %rdx,olen
        cmp $0xa,%bpl ; je 4045f4 ; (404578)    -- not a newline (hiPre)
```

The mirror of `Stdout.HexLo` (`olen` in `rax` on entry, `rdx` on exit, the byte in `%bpl`):
`hi_append`, `hi_common`, `hi_call`, `hi_ret`; `hiSite_of` (from `FlushContract`, both
branches) and `hiSite_verified` (with `flushContract`).

Status: **VERIFIED** (no `sorry`, standard axioms only).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word State Reg)
open Silmaril.Process (Memory Byte)
open Silmaril.Machine.LittleEndian (encodeWords)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

set_option maxRecDepth 200000

def HiOut (s : XState) (buf' : Bytes) (t : XState) : Prop :=
  t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = 0x404578#64 ∧ Obuf t.memory buf' ∧
    hiPost buf' s t

/-- The append `0x404560 → 0x404578` from an entry state with `rax = olen < 4096`. -/
theorem hi_append {s0 s : XState} {buf : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404560#64) (hob : Obuf s.memory buf)
    (hrax : s.core.read .rax = BitVec.ofNat 64 buf.length)
    (hne : lowByte (s.core.read .rbp) ≠ 10) (hlt : buf.length < 4096)
    (hk : SiteKept s0 s) {c : UInt8} (hcv : lowByte (s.core.read .rbp) = c) :
    RunsTo (HiOut s0 (buf ++ [c])) s := by
  subst hcv
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  rstep [hrip, hrax]
  have hp1 : s.memory.Permitted .write (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufW (by omega) (by omega) (by omega)
  obtain ⟨m1, hw1⟩ : ∃ m', s.memory.writeBytes (0x412140 + buf.length)
      (X86.Ext.leBytes (((s.core.read .rbp).setWidth 8).setWidth 64) 1) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by rw [X86.Ext.length_leBytes]; exact hp1))
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_store_b_ok' (m' := m1) ?_]
  swap
  · simp only [State.read_write_other, ne_eq, reduceCtorEq, not_false_eq_true, Lift.read_mk,
      Lift.core_regs, hrax]
    convert hw1 using 2
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    show (buf.length % 2 ^ 64 + 0x412140) % 2 ^ 64 = _
    omega
  dsimp only
  intro hc1
  have holW1 : m1.Permitted .write 0x412130 8 := perm_wb hw1 hob.olenW
  obtain ⟨m2, hw2⟩ : ∃ m', m1.writeBytes 0x412130
      (X86.Ext.leBytes (BitVec.ofNat 64 buf.length + 1#64) 8) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by rw [X86.Ext.length_leBytes]; exact holW1))
  rstep [hw2]
  have hb : ((s.core.read .rbp).setWidth 8 == 10#8) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; apply hne; simp only [lowByte, e]; rfl
  rstep
  rstep [hb]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, kfoot⟩ := hk
  have hlen : (buf ++ [lowByte (s.core.read .rbp)]).length = buf.length + 1 := by simp
  have hv : BitVec.ofNat 64 buf.length + 1#64 =
      BitVec.ofNat 64 (buf ++ [lowByte (s.core.read .rbp)]).length := by
    rw [hlen, BitVec.ofNat_add]
  have holR : s.memory.Permitted .read 0x412130 8 := Memory.readWith_permitted hob.olen
  have hp1r : s.memory.Permitted .read (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufR (by omega) (by omega) (by omega)
  rw [leBytes_lowByte] at hw1
  have hrd1 := read_snoc hob.obuf hw1 hp1r
  refine RunsTo.done ⟨hf, by assumption, rfl, ⟨by rw [hlen]; omega, ?_, ?_, ?_,
    perm_wb hw2 (perm_wb hw1 hob.olenW), perm_wb hw2 (perm_wb hw1 hob.obufW),
    perm_wb hw2 (perm_wb hw1 hob.obufR)⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hv]
    exact rd_same' hw2 (by simp) (perm_wb hw1 holR)
  · rw [Lift.readWith_wb_disjoint hw2 (Or.inr (by simp)), hlen, List.map_append]
    exact hrd1
  · rw [Lift.readWith_wb_disjoint hw2 (Or.inl (by simp)),
      Lift.readWith_wb_disjoint hw1 (Or.inl (by simp; omega))]
    exact hob.outError
  all_goals try (simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs, k1, k2, k3, k4, k5, k6, k7]; done)
  · xfoot [SiteFoot]
  · simp only [State.read_write_same]
    exact hv

/-- The common path `0x4045c2 → 0x404578` (`olen < 4096`). -/
theorem hi_common {s : XState} {buf : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x4045c2#64) (hob : Obuf s.memory buf) (hpre : hiPre buf s)
    (hlt : buf.length < 4096) :
    RunsTo (HiOut s (buf ++ [lowByte (s.core.read .rbp)])) s := by
  obtain ⟨hrax, hne, hst⟩ := hpre
  have hz : (BitVec.ofNat 64 buf.length == 4096#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  rstep [hrip, hrax]
  rstep [hz]
  apply hi_append (buf := buf)
  case hf => exact hf
  case hc => assumption
  case hrip => rfl
  case hob => exact hob
  case hrax => exact hrax
  case hne => exact hne
  case hlt => exact hlt
  case hk => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Memory.WritesWithin.refl _ _⟩
  case hcv => rfl

/-- At the `out_flush` call of the buffer-full branch, entered from `s`. -/
structure HiCall (s : XState) (buf : Bytes) (t : XState) : Prop where
  entry : FlushEntry t buf 0x4045cf#64
  rsp : t.core.read .rsp = s.core.read .rsp - 8#64
  rbx : t.core.read .rbx = s.core.read .rbx
  rbp : t.core.read .rbp = s.core.read .rbp
  r12 : t.core.read .r12 = s.core.read .r12
  r13 : t.core.read .r13 = s.core.read .r13
  r14 : t.core.read .r14 = s.core.read .r14
  r15 : t.core.read .r15 = s.core.read .r15
  foot : Memory.WritesWithin s.memory t.memory (SiteFoot (s.core.read .rsp).toNat)
  outError : OutErrorZero t.memory

/-- The buffer-full branch `0x4045c2 → 0x401100` (`olen = 4096`: call `out_flush`). -/
theorem hi_call {s : XState} {buf : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x4045c2#64) (hob : Obuf s.memory buf) (hpre : hiPre buf s)
    (hlen : buf.length = 4096) : RunsTo (HiCall s buf) s := by
  obtain ⟨hrax, -, ⟨hsp, hfr, hfw⟩⟩ := hpre
  have hz : (BitVec.ofNat 64 buf.length == 4096#64) = true := by simp [hlen]
  have holW := hob.olenW
  have holen := hob.olen
  have hobuf := hob.obuf
  have hoe := hob.outError
  rstep [hrip, hrax]
  rstep [hz]
  rstep
  refine RunsTo.done ⟨⟨hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  rfin [hlen] [SiteFoot]
  all_goals simp only [State.read_write_same, OutErrorZero]
  · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · xperm
  · xperm
  · repeat rmem [Bool.false_eq_true]
  · repeat rmem [Bool.false_eq_true]

/-- Back from `out_flush` at `0x4045cf` with an empty buffer: reload `olen`, append. -/
theorem hi_ret {s0 u : XState} (hf : u.faulted = false) (hc : Lift.Code u.memory)
    (hrip : u.core.rip = 0x4045cf#64) (hob : Obuf u.memory [])
    (hne : lowByte (u.core.read .rbp) ≠ 10) (hk : SiteKept s0 u) :
    RunsTo (HiOut s0 ([] ++ [lowByte (u.core.read .rbp)])) u := by
  have holen := hob.olen
  rstep [hrip]
  rstep
  apply hi_append (buf := [])
  case hf => exact hf
  case hc => assumption
  case hrip => rfl
  case hob => exact hob
  case hrax => simp
  case hne => exact hne
  case hlt => simp
  case hk => exact ⟨hk.1, hk.2, hk.3, hk.4, hk.5, hk.6, hk.7, hk.8⟩
  case hcv => rfl

section Leads

open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev out stdinRead expected)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- **The high-digit site** `0x4045c2 → 0x404578` from the `out_flush` contract (VERIFIED). -/
theorem hiSite_of (hfc : FlushContract) :
    PutcSite 0x4045c2#64 0x404578#64 hiPre (fun s => lowByte (s.core.read .rbp)) hiPost := by
  intro w message K g h buf emitted hfull hfd hrip hcode hobuf hpre hco hok hrd hem k
  have hfa : g.x.faulted = false := hok.2.2.2.2.2
  have hne := hpre.2.1
  have hsp := hpre.2.2.sp
  by_cases hlen : buf.length = 4096
  · have hpb : Sys.IOLayer.putcBuf 4096 buf (lowByte (g.x.core.read .rbp)) =
        (buf, [] ++ [lowByte (g.x.core.read .rbp)]) := by
      simp [Sys.IOLayer.putcBuf, hlen, hne]
    simp only [hpb] at k
    refine (hi_call hfa hcode hrip hobuf hpre hlen).leads hok.1 hok fun t ht => ?_
    refine hfc w message K { g with x := t } h buf emitted 0x4045cf#64 hfull hfd ht.entry
      ht.outError hco (Stdout.Ok.with_x hok ht.entry.faulted) hrd
      (List.IsPrefix.trans (by simp [List.map_append]) hem) ?_
    intro g' h' hx hex hk' hoe' hco' hrd' hok'
    have hrsp8 : (t.core.read .rsp).toNat = (g.x.core.read .rsp).toNat - 8 := by
      rw [ht.rsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    have hfoot : Memory.WritesWithin g.x.memory g'.x.memory
        (SiteFoot (g.x.core.read .rsp).toNat) :=
      ht.foot.trans (hx.foot.mono fun a ha => by
        simp only [FlushFoot, hrsp8] at ha; simp only [SiteFoot]; omega)
    have hob' : Obuf g'.x.memory [] :=
      ⟨by simp, by simpa using hx.olen, readWith_zero _ _ (by norm_num), hoe',
        (hfoot.permitted_iff _ _ _).mpr hobuf.olenW, (hfoot.permitted_iff _ _ _).mpr hobuf.obufW,
        (hfoot.permitted_iff _ _ _).mpr hobuf.obufR⟩
    have hkept : SiteKept g.x g'.x :=
      ⟨by rw [hx.rsp, ht.rsp]; simp, by rw [hx.rbx, ht.rbx], by rw [hx.rbp, ht.rbp],
        by rw [hx.r12, ht.r12], by rw [hx.r13, ht.r13], by rw [hx.r14, ht.r14],
        by rw [hx.r15, ht.r15], hfoot⟩
    have hrbp : g'.x.core.read .rbp = g.x.core.read .rbp := by rw [hx.rbp, ht.rbp]
    refine (hi_ret hx.faulted hx.code hx.rip hob' (by rw [hrbp]; exact hne) hkept).leads hex hok'
      fun t' ht' => ?_
    rw [hrbp] at ht'
    obtain ⟨hf', hc', hrip', hob'', hpost⟩ := ht'
    refine k { g' with x := t' } h' hrip' hf' hex hk' hc' hob'' ?_ hrd'
      (Stdout.Ok.with_x hok' hf') hpost
    show out h' ++ ([] ++ [_]).map _ = (emitted ++ [_]).map _
    have : out h' ++ ([] : Bytes).map UInt8.toBitVec = emitted.map UInt8.toBitVec := hco'
    rw [List.map_append, ← List.map_append, List.map_append, List.map_nil, List.append_nil] at *
    simp only [List.nil_append, List.map_append, List.map_cons, List.map_nil] at this ⊢
    rw [← this]
  · have hlt : buf.length < 4096 := by have := hobuf.cap; omega
    have hpb : Sys.IOLayer.putcBuf 4096 buf (lowByte (g.x.core.read .rbp)) =
        ([], buf ++ [lowByte (g.x.core.read .rbp)]) := by
      simp [Sys.IOLayer.putcBuf, hlen, hne]
    simp only [hpb] at k
    refine (hi_common hfa hcode hrip hobuf hpre hlt).leads hok.1 hok fun t ht => ?_
    obtain ⟨hf', hc', hrip', hob', hpost⟩ := ht
    refine k { g with x := t } h hrip' hf' hok.1 rfl hc' hob' ?_ rfl (Stdout.Ok.with_x hok hf') hpost
    show out h ++ (buf ++ [_]).map _ = (emitted ++ [_]).map _
    have : out h ++ buf.map UInt8.toBitVec = emitted.map UInt8.toBitVec := hco
    rw [List.map_append, List.map_append, ← List.append_assoc, this]

/-- **The high-digit site of the hex loop** (VERIFIED): `hiSite_of` with `flushContract`. -/
theorem hiSite_verified :
    PutcSite 0x4045c2#64 0x404578#64 hiPre (fun s => lowByte (s.core.read .rbp)) hiPost :=
  hiSite_of flushContract

end Leads

end Silmaril.Apps.Sha256sum.Stdout
