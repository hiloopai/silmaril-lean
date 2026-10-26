module

public import Silmaril.Apps.Sha256sum.Stdout.PutcSite

/-! # The low-digit `out_putc` site of the hex loop (`0x404584 → 0x4045a5`)

```
404584: cmp $0x1000,%rdx ; je 4045e6          -- buffer full?
40458d: lea 1(%rdx),%rax ; mov %r15b,obuf(%rdx) ; mov %rax,olen
        cmp $0xa,%r15b ; je 4045d8 ; (4045a5)  -- not a newline (loPre)
4045e6: call out_flush ; mov olen,%rdx ; jmp 40458d
```

* `lo_append`: the append `0x40458d → 0x4045a5` (`obuf[olen] = c`, `olen + 1`, `rax = olen`).
* `lo_common`: `olen < 4096`, the append.
* `lo_call`, `lo_ret`: `olen = 4096`, up to the `out_flush` call (`FlushEntry`), and from its
  return (`FlushExit`, empty buffer) through the append.
* `flushContract`: `PutcSite.FlushContract` from the output prover's `flush_cps`.
* `loSite_of`: the site (`PutcSite … loPre … loPost`) from `FlushContract`, both branches;
  `loSite_verified`: with `flushContract`.

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

/-- A byte store `mov %src8, disp(%base)` into writable memory retires. -/
theorem exec_store_b_ok' {c : State} {mem m' : Memory} {len : Nat} {base src : Reg}
    {d : BitVec 32}
    (h : mem.writeBytes (c.read base + d.signExtend 64).toNat
      (X86.Ext.leBytes (((c.read src).setWidth 8).setWidth 64) 1) = some m') :
    X86.Ext8.exec (.base (.store .b (.mem (X86.Ext.Mem.ofReg base none d)) src)) c mem len =
      .ok { c with rip := c.rip + BitVec.ofNat 64 len } m' := by
  simp only [X86.Ext8.exec_base, X86.Ext.exec, X86.Ext.writeNarrow, X86.Ext.storeN,
    X86.Ext.Mem.addr, X86.Ext.Mem.ofReg]
  change X86.Ext.retire _ (Option.map _ (mem.writeBytes (c.read base + 0#64 + d.signExtend 64).toNat
    (X86.Ext.leBytes (((c.read src).setWidth 8).setWidth 64) 1))) = _
  rw [BitVec.add_zero, h]; rfl

theorem leBytes_lowByte (r : Word) :
    X86.Ext.leBytes ((r.setWidth 8).setWidth 64) 1 = [ofU8 (lowByte r)] := by
  simp only [X86.Ext.leBytes, List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
    Silmaril.Machine.LittleEndian.wordByte, ofU8, lowByte]
  simp
  apply BitVec.eq_of_toNat_eq
  simp

/-- The exit of the low-digit site with the new buffer `buf'`. -/
def LoOut (s : XState) (buf' : Bytes) (t : XState) : Prop :=
  t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = 0x4045a5#64 ∧ Obuf t.memory buf' ∧
    loPost buf' s t

/-- The append `0x40458d → 0x4045a5` from an entry state with `rdx = olen < 4096`. -/
theorem lo_append {s0 s : XState} {buf : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x40458d#64) (hob : Obuf s.memory buf)
    (hrdx : s.core.read .rdx = BitVec.ofNat 64 buf.length)
    (hne : lowByte (s.core.read .r15) ≠ 10) (hlt : buf.length < 4096)
    (hk : SiteKept s0 s) {c : UInt8} (hcv : lowByte (s.core.read .r15) = c) :
    RunsTo (LoOut s0 (buf ++ [c])) s := by
  subst hcv
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  rstep [hrip, hrdx]
  have hp1 : s.memory.Permitted .write (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufW (by omega) (by omega) (by omega)
  obtain ⟨m1, hw1⟩ : ∃ m', s.memory.writeBytes (0x412140 + buf.length)
      (X86.Ext.leBytes (((s.core.read .r15).setWidth 8).setWidth 64) 1) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by rw [X86.Ext.length_leBytes]; exact hp1))
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_store_b_ok' (m' := m1) ?_]
  swap
  · simp only [State.read_write_other, ne_eq, reduceCtorEq, not_false_eq_true, Lift.read_mk,
      Lift.core_regs, hrdx]
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
  have hb : ((s.core.read .r15).setWidth 8 == 10#8) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; apply hne; simp only [lowByte, e]; rfl
  rstep
  rstep [hb]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, kfoot⟩ := hk
  have hlen : (buf ++ [lowByte (s.core.read .r15)]).length = buf.length + 1 := by simp
  have hv : BitVec.ofNat 64 buf.length + 1#64 =
      BitVec.ofNat 64 (buf ++ [lowByte (s.core.read .r15)]).length := by
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

theorem readWith_zero (m : Memory) (a : Nat) (ha : a < 2 ^ 64) : m.readWith .read a 0 = some [] := by
  simp [Memory.readWith, Memory.checkSpan, Memory.readBacking, Silmaril.Process.addressLimit]
  omega

/-- The common path `0x404584 → 0x4045a5` (`olen < 4096`). -/
theorem lo_common {s : XState} {buf : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404584#64) (hob : Obuf s.memory buf) (hpre : loPre buf s)
    (hlt : buf.length < 4096) :
    RunsTo (LoOut s (buf ++ [lowByte (s.core.read .r15)])) s := by
  obtain ⟨hrdx, hne, hst⟩ := hpre
  have hz : (BitVec.ofNat 64 buf.length == 4096#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  rstep [hrip, hrdx]
  rstep [hz]
  apply lo_append (buf := buf)
  case hf => exact hf
  case hc => assumption
  case hrip => rfl
  case hob => exact hob
  case hrdx => exact hrdx
  case hne => exact hne
  case hlt => exact hlt
  case hk => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Memory.WritesWithin.refl _ _⟩
  case hcv => rfl

/-- At the `out_flush` call of the buffer-full branch, entered from `s`. -/
structure LoCall (s : XState) (buf : Bytes) (t : XState) : Prop where
  entry : FlushEntry t buf 0x4045eb#64
  rsp : t.core.read .rsp = s.core.read .rsp - 8#64
  rbx : t.core.read .rbx = s.core.read .rbx
  rbp : t.core.read .rbp = s.core.read .rbp
  r12 : t.core.read .r12 = s.core.read .r12
  r13 : t.core.read .r13 = s.core.read .r13
  r14 : t.core.read .r14 = s.core.read .r14
  r15 : t.core.read .r15 = s.core.read .r15
  foot : Memory.WritesWithin s.memory t.memory (SiteFoot (s.core.read .rsp).toNat)
  outError : OutErrorZero t.memory

/-- The buffer-full branch `0x404584 → 0x401100` (`olen = 4096`: call `out_flush`). -/
theorem lo_call {s : XState} {buf : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404584#64) (hob : Obuf s.memory buf) (hpre : loPre buf s)
    (hlen : buf.length = 4096) : RunsTo (LoCall s buf) s := by
  obtain ⟨hrdx, -, ⟨hsp, hfr, hfw⟩⟩ := hpre
  have hz : (BitVec.ofNat 64 buf.length == 4096#64) = true := by simp [hlen]
  have holW := hob.olenW
  have holen := hob.olen
  have hobuf := hob.obuf
  have hoe := hob.outError
  rstep [hrip, hrdx]
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

/-- Back from `out_flush` at `0x4045eb` with an empty buffer: reload `olen`, append. -/
theorem lo_ret {s0 u : XState} (hf : u.faulted = false) (hc : Lift.Code u.memory)
    (hrip : u.core.rip = 0x4045eb#64) (hob : Obuf u.memory [])
    (hne : lowByte (u.core.read .r15) ≠ 10) (hk : SiteKept s0 u) :
    RunsTo (LoOut s0 ([] ++ [lowByte (u.core.read .r15)])) u := by
  have holen := hob.olen
  rstep [hrip]
  rstep
  apply lo_append (buf := [])
  case hf => exact hf
  case hc => assumption
  case hrip => rfl
  case hob => exact hob
  case hrdx => simp
  case hne => exact hne
  case hlt => simp
  case hk => exact ⟨hk.1, hk.2, hk.3, hk.4, hk.5, hk.6, hk.7, hk.8⟩
  case hcv => rfl

section Leads

open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev out stdinRead expected)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- **`FlushContract` holds** (VERIFIED): it is `flush_cps`, the output prover's verified
`out_flush` contract (`Stdout.OutFlush`), with `OutErrorZero` and `Coalesced` unfolded. -/
theorem flushContract : FlushContract :=
  fun w message K g h buf emitted ra hw hfd he hoe hco ok hrd hem k =>
    flush_cps w message K g h buf emitted ra hw hfd he hoe hco ok hrd hem k

/-- **The low-digit site** `0x404584 → 0x4045a5` from the `out_flush` contract (VERIFIED). -/
theorem loSite_of (hfc : FlushContract) :
    PutcSite 0x404584#64 0x4045a5#64 loPre (fun s => lowByte (s.core.read .r15)) loPost := by
  intro w message K g h buf emitted hfull hfd hrip hcode hobuf hpre hco hok hrd hem k
  have hfa : g.x.faulted = false := hok.2.2.2.2.2
  have hne := hpre.2.1
  have hsp := hpre.2.2.sp
  by_cases hlen : buf.length = 4096
  · have hpb : Sys.IOLayer.putcBuf 4096 buf (lowByte (g.x.core.read .r15)) =
        (buf, [] ++ [lowByte (g.x.core.read .r15)]) := by
      simp [Sys.IOLayer.putcBuf, hlen, hne]
    simp only [hpb] at k
    refine (lo_call hfa hcode hrip hobuf hpre hlen).leads hok.1 hok fun t ht => ?_
    refine hfc w message K { g with x := t } h buf emitted 0x4045eb#64 hfull hfd ht.entry
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
    have hr15 : g'.x.core.read .r15 = g.x.core.read .r15 := by rw [hx.r15, ht.r15]
    refine (lo_ret hx.faulted hx.code hx.rip hob' (by rw [hr15]; exact hne) hkept).leads hex hok'
      fun t' ht' => ?_
    rw [hr15] at ht'
    obtain ⟨hf', hc', hrip', hob'', hpost⟩ := ht'
    refine k { g' with x := t' } h' hrip' hf' hex hk' hc' hob'' ?_ hrd'
      (Stdout.Ok.with_x hok' hf') hpost
    show out h' ++ ([] ++ [_]).map _ = (emitted ++ [_]).map _
    have : out h' ++ ([] : Bytes).map UInt8.toBitVec = emitted.map UInt8.toBitVec := hco'
    rw [List.map_append, ← List.map_append, List.map_append, List.map_nil, List.append_nil] at *
    simp only [List.nil_append, List.map_append, List.map_cons, List.map_nil] at this ⊢
    rw [← this]
  · have hlt : buf.length < 4096 := by have := hobuf.cap; omega
    have hpb : Sys.IOLayer.putcBuf 4096 buf (lowByte (g.x.core.read .r15)) =
        ([], buf ++ [lowByte (g.x.core.read .r15)]) := by
      simp [Sys.IOLayer.putcBuf, hlen, hne]
    simp only [hpb] at k
    refine (lo_common hfa hcode hrip hobuf hpre hlt).leads hok.1 hok fun t ht => ?_
    obtain ⟨hf', hc', hrip', hob', hpost⟩ := ht
    refine k { g with x := t } h hrip' hf' hok.1 rfl hc' hob' ?_ rfl (Stdout.Ok.with_x hok hf') hpost
    show out h ++ (buf ++ [_]).map _ = (emitted ++ [_]).map _
    have : out h ++ buf.map UInt8.toBitVec = emitted.map UInt8.toBitVec := hco
    rw [List.map_append, List.map_append, ← List.append_assoc, this]

/-- **The low-digit site of the hex loop** (VERIFIED): `loSite_of` with `flushContract`. -/
theorem loSite_verified :
    PutcSite 0x404584#64 0x4045a5#64 loPre (fun s => lowByte (s.core.read .r15)) loPost :=
  loSite_of flushContract

end Leads

end Silmaril.Apps.Sha256sum.Stdout
