module

public import Silmaril.Apps.Sha256sum.Stdout.HexLoop
public import Silmaril.Apps.Sha256sum.Stdout.Tail

/-! # The suffix of the format segment: from the hex loop's exit to `Formatted`

```
404605: cmpl $0,0x10(%rsp) ; mov 0x18(%rsp),%ebx ; movzbl 0x20(%rsp),%ebp ; je 404a3f
404a3f: out_putc(' ')        (olen in rax; full: 405094 call out_flush, jmp 404a4b)
404a64: test %r13d,%r13d ; je 404ca5 (mov $0x20,%eax ; jmp 404a72) ; 404a72: mov %eax,%r13d
404a75: out_putc(%r13b)      (olen in rdx; full: 40508a call out_flush, jmp 404a82)
404aa0: call print_filename("-", needs_escape = 0) ; jmp 404619
404619: out_putc(%bpl = '\n') (olen in memory; full: 404bcb) ; '\n': 404bdf call out_flush
40464d: (Formatted)
```

`HexExitCut` is the cut at `0x404605`, the exit of `Stdout.hex_loop`: it is stated over the
hex loop's entry state `s0` and `HexExit s0 g.x`, so that `hex_loop`'s continuation gives it
directly. `suffix : Seg _ HexExitCut FormattedCut` (`FormattedCut = Wire.Formatted`).

* `run_head`, `run_b`: the straight-line pieces (reload the spills; `r13d = 0` gives `' '`).
* `site_of_runs`: a `PutcSite` from its three runs (append; buffer-full call of `out_flush`;
  the run from its return), with `flushContract` (`Stdout.HexLo`).
* `s1Site` (`0x404a3f`, `olen` in `rax`), `s2Site` (`0x404a75`, `olen` in `rdx`), `pfSite`
  (the call of `print_filename("-", 0)`, an `out_putc` of `'-'` inside), `s4Site` (`0x404619`,
  `olen` in memory: the delimiter `'\n'`, whose `out_flush` empties the buffer, so the whole
  record is written).
* `suffix`: the four sites composed; `SufFoot` tracks the writes since the hex loop's entry.

Status: **VERIFIED** (no `sorry`, standard axioms only).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word State Reg)
open Silmaril.Process (Memory Byte)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev out stdinRead expected Cut Seg)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

set_option maxRecDepth 200000

/-- What the suffix needs of `cmain`'s memory at the hex loop's entry (`rsp = sp`): the stack
from `sp - 128` (the frames of `print_filename` and `out_flush`) to `sp + 0x98`, the
`prefix_tag` spill `0x10(%rsp) = 0`, `ok = 1`, the operand index `0` of `n_operands = 1`,
`have_read_stdin = 1`, `err_error = 0`, and the operand `"-"` at `0x406052`. -/
structure SufMem (sp : Word) (m : Memory) : Prop where
  spBound : 0x414100 ≤ sp.toNat ∧ sp.toNat + 0x100 < 2 ^ 47
  stackR : m.Permitted .read (sp.toNat - 128) (128 + 0x98)
  stackW : m.Permitted .write (sp.toNat - 128) (128 + 0x98)
  prefixTag : m.readWith .read (sp + 0x10#64).toNat 4 = some (X86.Ext.leBytes 0#64 4)
  okFlag : m.readWith .read (sp + 0x2c#64).toNat 4 = some (X86.Ext.leBytes 1#64 4)
  index : m.readWith .read (sp + 0x8#64).toNat 8 = some (X86.Ext.leBytes 0#64 8)
  nOps : m.readWith .read (sp + 0x50#64).toNat 4 = some (X86.Ext.leBytes 1#64 4)
  haveStdin : m.readWith .read 0x40a0a0 4 = some (X86.Ext.leBytes 1#64 4)
  errError : m.readWith .read 0x412128 4 = some (X86.Ext.leBytes 0#64 4)
  dash : m.readWith .read 0x406052 2 = some [0x2d#8, 0#8]

/-- The record's tail `"  -\n"` (two spaces, the operand `-`, the delimiter `'\n'`). -/
def recordTail : Bytes := [0x20, 0x20, 0x2d, 0x0a]

/-- **At the hex loop's exit** `0x404605`, for the hex loop's entry state `s0`, the buffer `buf`
and the bytes `e` emitted so far (`emitted ++ hexLower d` for `hex_loop`): `HexExit s0 g.x`;
`s0`'s registers (`ebx = needs_escape = 0`, `bpl = digest_delim = '\n'`, `r12 = "-"`,
`r13d = binary = 0`) and memory (`SufMem`); `rax = olen` (the low site's exit register, kept by
the loop control); the stdout layer (`Obuf`, `Coalesced`); the whole message read, and `e`
followed by `"  -\n"` is the answer. -/
structure HexExitAt (message : List Byte) (s0 : XState) (buf e : Bytes) (g : GS) (h : List Ev) :
    Prop where
  ok : Ok message g h
  rip : g.x.core.rip = 0x404605#64
  code : Lift.Code g.x.memory
  fd0 : ∃ s, g.k.fds 0 = some s
  fd1 : g.k.fds 1 = some .stdout
  fd2 : ∃ s, g.k.fds 2 = some s
  exit : HexExit s0 g.x
  rbx : (s0.core.read .rbx).setWidth 32 = 0#32
  rbp : (s0.core.read .rbp).setWidth 8 = 0x0a#8
  r12 : s0.core.read .r12 = 0x406052#64
  r13 : (s0.core.read .r13).setWidth 32 = 0#32
  mem : SufMem (s0.core.read .rsp) s0.memory
  rax : g.x.core.read .rax = BitVec.ofNat 64 buf.length
  obuf : Obuf g.x.memory buf
  co : Coalesced h buf e
  read : stdinRead h = message
  answer : (e ++ recordTail).map UInt8.toBitVec = expected message

/-- **The cut at the hex loop's exit** (`0x404605`). -/
def HexExitCut : Cut := fun _ message g h => ∃ s0 buf e, HexExitAt message s0 buf e g h

/-! ## `0x404605 → 0x404a3f`: reload the spills, the untagged branch -/

/-- At `0x404a3f` from `t`: `ebx = 0`, `ebp = '\n'`, the rest kept. -/
structure AtSp (t u : XState) : Prop where
  faulted : u.faulted = false
  code : Lift.Code u.memory
  rip : u.core.rip = 0x404a3f#64
  mem : u.memory = t.memory
  rsp : u.core.read .rsp = t.core.read .rsp
  rax : u.core.read .rax = t.core.read .rax
  r12 : u.core.read .r12 = t.core.read .r12
  r13 : u.core.read .r13 = t.core.read .r13
  rbx : u.core.read .rbx = 0#64
  rbp : u.core.read .rbp = 10#64

theorem run_head {t : XState} {sp : Word} (hf : t.faulted = false) (hc : Lift.Code t.memory)
    (hrip : t.core.rip = 0x404605#64) (hrsp : t.core.read .rsp = sp)
    (hpt : t.memory.readWith .read (sp + 0x10#64).toNat 4 = some (X86.Ext.leBytes 0#64 4))
    (hb : t.memory.readWith .read (sp + 0x18#64).toNat 4 = some (X86.Ext.leBytes 0#64 4))
    (hp : t.memory.readWith .read (sp + 0x20#64).toNat 1 = some [10#8]) :
    RunsTo (AtSp t) t := by
  rstep [hrip, hrsp]
  rstep [hrsp]
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_movzb_ok (b := 10#8) (by simpa [hrsp] using hp)]
  intro hc3
  rstep
  refine RunsTo.done ⟨hf, by assumption, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs]

/-! ## Inlined `out_putc` sites from their runs -/

/-- A constant byte store `movb $imm, disp(%base)` into writable memory retires. -/
theorem exec_movI8_ok {c : State} {mem m' : Memory} {len : Nat} {base : Reg} {d : BitVec 32}
    {v : BitVec 8}
    (h : mem.writeBytes (c.read base + d.signExtend 64).toNat (X86.Ext.leBytes (v.setWidth 64) 1) =
      some m') :
    X86.Ext8.exec (.base (.movI8 (.mem (X86.Ext.Mem.ofReg base none d)) v)) c mem len =
      .ok { c with rip := c.rip + BitVec.ofNat 64 len } m' := by
  simp only [X86.Ext8.exec_base, X86.Ext.exec, X86.Ext.writeRM8, X86.Ext.storeN,
    X86.Ext.Mem.addr, X86.Ext.Mem.ofReg]
  change X86.Ext.retire _ (Option.map _ (mem.writeBytes
    (c.read base + 0#64 + d.signExtend 64).toNat (X86.Ext.leBytes (v.setWidth 64) 1))) = _
  rw [BitVec.add_zero, h]; rfl

theorem obuf_nil_of {m m' : Memory} {buf : Bytes} {F : Nat → Prop} (hob : Obuf m buf)
    (hw : Memory.WritesWithin m m' F)
    (hol : m'.readWith .read 0x412130 8 = some (X86.Ext.leBytes 0#64 8))
    (hoe : OutErrorZero m') : Obuf m' [] :=
  ⟨by simp, by simpa using hol, readWith_zero _ _ (by norm_num), hoe,
    (hw.permitted_iff _ _ _).mpr hob.olenW, (hw.permitted_iff _ _ _).mpr hob.obufW,
    (hw.permitted_iff _ _ _).mpr hob.obufR⟩

theorem coalesced_snoc {h : List Ev} {buf e : Bytes} (hc : Coalesced h buf e) (c : UInt8) :
    Coalesced h (buf ++ [c]) (e ++ [c]) := by
  unfold Coalesced at *
  rw [List.map_append, List.map_append, ← List.append_assoc, hc]

/-- **The append** `obuf[olen] = c; olen += 1` keeps `Obuf`. -/
theorem obuf_append {m m1 m2 : Memory} {buf : Bytes} {c : UInt8} (hob : Obuf m buf)
    (hlt : buf.length < 4096)
    (hw1 : m.writeBytes (0x412140 + buf.length) [ofU8 c] = some m1)
    (hw2 : m1.writeBytes 0x412130 (X86.Ext.leBytes (BitVec.ofNat 64 buf.length + 1#64) 8) =
      some m2) : Obuf m2 (buf ++ [c]) := by
  have hlen : (buf ++ [c]).length = buf.length + 1 := by simp
  have hv : BitVec.ofNat 64 buf.length + 1#64 = BitVec.ofNat 64 (buf ++ [c]).length := by
    rw [hlen, BitVec.ofNat_add]
  have holR : m.Permitted .read 0x412130 8 := Memory.readWith_permitted hob.olen
  have hp1r : m.Permitted .read (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufR (by omega) (by omega) (by omega)
  have hrd1 := read_snoc hob.obuf hw1 hp1r
  refine ⟨by rw [hlen]; omega, ?_, ?_, ?_, perm_wb hw2 (perm_wb hw1 hob.olenW),
    perm_wb hw2 (perm_wb hw1 hob.obufW), perm_wb hw2 (perm_wb hw1 hob.obufR)⟩
  · rw [← hv]
    exact rd_same' hw2 (by simp) (perm_wb hw1 holR)
  · rw [Lift.readWith_wb_disjoint hw2 (Or.inr (by simp)), hlen, List.map_append]
    exact hrd1
  · rw [Lift.readWith_wb_disjoint hw2 (Or.inl (by simp)),
      Lift.readWith_wb_disjoint hw1 (Or.inl (by simp; omega))]
    exact hob.outError

/-- At an `out_flush` call made from a site entered at `s`: `rsp - 8`, the callee-saved
registers kept, writes in `SiteFoot`. -/
structure CallMid (s t : XState) : Prop where
  rsp : t.core.read .rsp = s.core.read .rsp - 8#64
  rbx : t.core.read .rbx = s.core.read .rbx
  rbp : t.core.read .rbp = s.core.read .rbp
  r12 : t.core.read .r12 = s.core.read .r12
  r13 : t.core.read .r13 = s.core.read .r13
  r14 : t.core.read .r14 = s.core.read .r14
  r15 : t.core.read .r15 = s.core.read .r15
  foot : Memory.WritesWithin s.memory t.memory (SiteFoot (s.core.read .rsp).toNat)

theorem kept_of_call {s t u : XState} {ra : Word} (hsp : 0x414028 ≤ (s.core.read .rsp).toNat)
    (hm : CallMid s t) (hx : FlushExit t ra u) : SiteKept s u := by
  have hrsp8 : (t.core.read .rsp).toNat = (s.core.read .rsp).toNat - 8 := by
    rw [hm.rsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  exact ⟨by rw [hx.rsp, hm.rsp]; simp, by rw [hx.rbx, hm.rbx], by rw [hx.rbp, hm.rbp],
    by rw [hx.r12, hm.r12], by rw [hx.r13, hm.r13], by rw [hx.r14, hm.r14],
    by rw [hx.r15, hm.r15], hm.foot.trans (hx.foot.mono fun a ha => by
      simp only [FlushFoot, hrsp8] at ha; simp only [SiteFoot]; omega)⟩

/-- **A site from its runs**: the append (`common`, `olen < 4096`), the buffer-full branch up
to the `out_flush` call (`call`), and the run from its return (`back`). -/
theorem site_of_runs (hfc : FlushContract) {entry exit ra : Word}
    {Pre : Bytes → XState → Prop} {byteOf : XState → UInt8}
    {Post : Bytes → XState → XState → Prop} {Mid : XState → XState → Prop}
    (hne : ∀ buf s, Pre buf s → byteOf s ≠ 10)
    (common : ∀ (s : XState) (buf : Bytes), s.faulted = false → Lift.Code s.memory →
      s.core.rip = entry → Obuf s.memory buf → Pre buf s → buf.length < 4096 →
      RunsTo (fun t => t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = exit ∧
        Obuf t.memory (buf ++ [byteOf s]) ∧ Post (buf ++ [byteOf s]) s t) s)
    (call : ∀ (s : XState) (buf : Bytes), s.faulted = false → Lift.Code s.memory →
      s.core.rip = entry → Obuf s.memory buf → Pre buf s → buf.length = 4096 →
      RunsTo (fun t => FlushEntry t buf ra ∧ OutErrorZero t.memory ∧
        (∃ F, Memory.WritesWithin s.memory t.memory F) ∧ Mid s t) s)
    (back : ∀ (s t u : XState) (buf : Bytes), Pre buf s → Mid s t → FlushExit t ra u →
      Obuf u.memory [] →
      RunsTo (fun v => v.faulted = false ∧ Lift.Code v.memory ∧ v.core.rip = exit ∧
        Obuf v.memory ([] ++ [byteOf s]) ∧ Post ([] ++ [byteOf s]) s v) u) :
    PutcSite entry exit Pre byteOf Post := by
  intro w message K g h buf emitted hfull hfd hrip hcode hobuf hpre hco hok hrd hem k
  have hfa : g.x.faulted = false := hok.2.2.2.2.2
  have hn := hne buf g.x hpre
  by_cases hlen : buf.length = 4096
  · have hpb : Sys.IOLayer.putcBuf 4096 buf (byteOf g.x) = (buf, [] ++ [byteOf g.x]) := by
      simp [Sys.IOLayer.putcBuf, hlen, hn]
    simp only [hpb] at k
    refine (call g.x buf hfa hcode hrip hobuf hpre hlen).leads hok.1 hok
      fun t ⟨he, hoe, ⟨F, hw⟩, hm⟩ => ?_
    refine hfc w message K { g with x := t } h buf emitted ra hfull hfd he hoe hco
      (Stdout.Ok.with_x hok he.faulted) hrd
      (List.IsPrefix.trans (by simp [List.map_append]) hem) ?_
    intro g' h' hx hex hk' hoe' hco' hrd' hok'
    have hob' : Obuf g'.x.memory [] :=
      obuf_nil_of hobuf ((hw.mono fun _ _ => trivial).trans
        (hx.foot.mono fun _ _ => (trivial : True))) hx.olen hoe'
    refine (back g.x t g'.x buf hpre hm hx hob').leads hex hok'
      fun v ⟨hf', hc', hrip', hob'', hpost⟩ => ?_
    exact k { g' with x := v } h' hrip' hf' hex hk' hc' hob'' (coalesced_snoc hco' _) hrd'
      (Stdout.Ok.with_x hok' hf') hpost
  · have hlt : buf.length < 4096 := by have := hobuf.cap; omega
    have hpb : Sys.IOLayer.putcBuf 4096 buf (byteOf g.x) = ([], buf ++ [byteOf g.x]) := by
      simp [Sys.IOLayer.putcBuf, hlen, hn]
    simp only [hpb] at k
    refine (common g.x buf hfa hcode hrip hobuf hpre hlt).leads hok.1 hok
      fun t ⟨hf', hc', hrip', hob', hpost⟩ => ?_
    exact k { g with x := t } h hrip' hf' hok.1 rfl hc' hob' (coalesced_snoc hco _) rfl
      (Stdout.Ok.with_x hok hf') hpost

/-! ## The first space: `0x404a3f → 0x404a64` (`olen` in `rax`) -/

def s1Pre (buf : Bytes) (s : XState) : Prop :=
  s.core.read .rax = BitVec.ofNat 64 buf.length ∧ SiteStack s

def s1Post (buf' : Bytes) (s s' : XState) : Prop :=
  SiteKept s s' ∧ s'.core.read .rdx = BitVec.ofNat 64 buf'.length

def S1Out (s : XState) (buf' : Bytes) (t : XState) : Prop :=
  t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = 0x404a64#64 ∧ Obuf t.memory buf' ∧
    s1Post buf' s t

/-- The append `0x404a4b → 0x404a64`. -/
theorem s1_append {s0 s : XState} {buf : Bytes} (hf : s.faulted = false)
    (hc : Lift.Code s.memory) (hrip : s.core.rip = 0x404a4b#64) (hob : Obuf s.memory buf)
    (hlt : buf.length < 4096) (hk : SiteKept s0 s) :
    RunsTo (S1Out s0 (buf ++ [0x20])) s := by
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  have holen := hob.olen
  rstep [hrip, hl]
  rstep
  have hp1 : s.memory.Permitted .write (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufW (by omega) (by omega) (by omega)
  obtain ⟨m1, hw1⟩ : ∃ m', s.memory.writeBytes (0x412140 + buf.length) [ofU8 0x20] = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by simpa using hp1))
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_movI8_ok (m' := m1) ?_]
  swap
  · simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true]
    convert hw1 using 2
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [BitVec.reduceSignExtend, BitVec.toNat_ofNat]
      omega
    · rfl
  dsimp only
  intro hc3
  obtain ⟨m2, hw2⟩ : ∃ m', m1.writeBytes 0x412130
      (X86.Ext.leBytes (BitVec.ofNat 64 buf.length + 1#64) 8) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by
      rw [X86.Ext.length_leBytes]; exact perm_wb hw1 hob.olenW))
  rstep [hw2]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, kfoot⟩ := hk
  refine RunsTo.done ⟨hf, by assumption, rfl, obuf_append hob hlt hw1 hw2,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals try (simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs, k1, k2, k3, k4, k5, k6, k7]; done)
  · xfoot [SiteFoot]
  · simp only [State.read_write_same, List.length_append, List.length_singleton]
    rw [BitVec.ofNat_add]

theorem ne_4096 {n : Nat} (h : n < 4096) : (BitVec.ofNat 64 n == 4096#64) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

theorem eq_4096 {n : Nat} (h : n = 4096) : (BitVec.ofNat 64 n == 4096#64) = true := by
  simp [h]

/-- The common path `0x404a3f → 0x404a64`. -/
theorem s1_common (s : XState) (buf : Bytes) (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404a3f#64) (hob : Obuf s.memory buf) (hpre : s1Pre buf s)
    (hlt : buf.length < 4096) :
    RunsTo (fun t => t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = 0x404a64#64 ∧
      Obuf t.memory (buf ++ [0x20]) ∧ s1Post (buf ++ [0x20]) s t) s := by
  obtain ⟨hrax, -⟩ := hpre
  rstep [hrip, hrax]
  rstep [ne_4096 hlt]
  exact s1_append hf (by assumption) rfl hob hlt
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Memory.WritesWithin.refl _ _⟩

/-- The buffer-full branch `0x404a3f → 0x401100`. -/
theorem s1_call (s : XState) (buf : Bytes) (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404a3f#64) (hob : Obuf s.memory buf) (hpre : s1Pre buf s)
    (hlen : buf.length = 4096) :
    RunsTo (fun t => FlushEntry t buf 0x405099#64 ∧ OutErrorZero t.memory ∧
      (∃ F, Memory.WritesWithin s.memory t.memory F) ∧ CallMid s t) s := by
  obtain ⟨hrax, ⟨hsp, hfr, hfw⟩⟩ := hpre
  have holW := hob.olenW
  have holen := hob.olen
  have hobuf := hob.obuf
  have hoe := hob.outError
  rstep [hrip, hrax]
  rstep [eq_4096 hlen]
  rstep
  refine RunsTo.done ⟨⟨hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩, ?_,
    ⟨SiteFoot (s.core.read .rsp).toNat, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  rfin [hlen] [SiteFoot]
  all_goals try simp only [State.read_write_same, OutErrorZero]
  all_goals first
    | (simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    | xperm
    | ((repeat rmem [Bool.false_eq_true]))

/-- Back from `out_flush` at `0x405099`: `jmp 0x404a4b`, the append. -/
theorem s1_back (s t u : XState) (buf : Bytes) (hpre : s1Pre buf s) (hm : CallMid s t)
    (hx : FlushExit t 0x405099#64 u) (hob : Obuf u.memory []) :
    RunsTo (fun v => v.faulted = false ∧ Lift.Code v.memory ∧ v.core.rip = 0x404a64#64 ∧
      Obuf v.memory ([] ++ [0x20]) ∧ s1Post ([] ++ [0x20]) s v) u := by
  have hf := hx.faulted
  have hc := hx.code
  have hrip : u.core.rip = 0x405099#64 := hx.rip
  have hk := kept_of_call (by have := hpre.2.sp; omega) hm hx
  rstep [hrip]
  exact s1_append hf (by assumption) rfl hob (by simp)
    ⟨hk.1, hk.2, hk.3, hk.4, hk.5, hk.6, hk.7, hk.8⟩

/-- **The first space** `0x404a3f → 0x404a64` (VERIFIED). -/
theorem s1Site : PutcSite 0x404a3f#64 0x404a64#64 s1Pre (fun _ => 0x20) s1Post :=
  site_of_runs flushContract (fun _ _ _ => by decide) s1_common s1_call s1_back

/-! ## `0x404a64 → 0x404a75`: the binary flag (`r13d = 0`: a space) -/

structure AtB (t u : XState) : Prop where
  faulted : u.faulted = false
  code : Lift.Code u.memory
  rip : u.core.rip = 0x404a75#64
  mem : u.memory = t.memory
  rsp : u.core.read .rsp = t.core.read .rsp
  rbx : u.core.read .rbx = t.core.read .rbx
  rbp : u.core.read .rbp = t.core.read .rbp
  r12 : u.core.read .r12 = t.core.read .r12
  rdx : u.core.read .rdx = t.core.read .rdx
  r13 : u.core.read .r13 = 0x20#64

theorem run_b {t : XState} (hf : t.faulted = false) (hc : Lift.Code t.memory)
    (hrip : t.core.rip = 0x404a64#64) (hr13 : (t.core.read .r13).setWidth 32 = 0#32) :
    RunsTo (AtB t) t := by
  rstep [hrip, hr13]
  rstep
  rstep
  rstep
  rstep
  refine RunsTo.done ⟨hf, by assumption, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs]

/-! ## The second space: `0x404a75 → 0x404aa0` (`olen` in `rdx`, the byte in `%r13b`) -/

def s2Pre (buf : Bytes) (s : XState) : Prop :=
  s.core.read .rdx = BitVec.ofNat 64 buf.length ∧ s.core.read .r13 = 0x20#64 ∧ SiteStack s

/-- The exit `0x404aa0` (the call of `print_filename`): `rdi = r12`, `esi = ebx`. -/
def s2Post (_buf' : Bytes) (s s' : XState) : Prop :=
  SiteKept s s' ∧ s'.core.read .rdi = s.core.read .r12 ∧
    s'.core.read .rsi = ((s.core.read .rbx).setWidth 32).setWidth 64

def S2Out (s : XState) (buf' : Bytes) (t : XState) : Prop :=
  t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = 0x404aa0#64 ∧ Obuf t.memory buf' ∧
    s2Post buf' s t

theorem leBytes_20 : X86.Ext.leBytes (((0x20#64 : Word).setWidth 8).setWidth 64) 1 = [ofU8 0x20] :=
  by decide

/-- The append `0x404a82 → 0x404aa0`. -/
theorem s2_append {s0 s : XState} {buf : Bytes} (hf : s.faulted = false)
    (hc : Lift.Code s.memory) (hrip : s.core.rip = 0x404a82#64) (hob : Obuf s.memory buf)
    (hlt : buf.length < 4096) (hk : SiteKept s0 s) (hr13 : s.core.read .r13 = 0x20#64) :
    RunsTo (S2Out s0 (buf ++ [0x20])) s := by
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  have holen := hob.olen
  rstep [hrip, hl]
  rstep
  rstep
  rstep
  have hp1 : s.memory.Permitted .write (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufW (by omega) (by omega) (by omega)
  obtain ⟨m1, hw1⟩ : ∃ m', s.memory.writeBytes (0x412140 + buf.length) [ofU8 0x20] = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by simpa using hp1))
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_store_b_ok' (m' := m1) ?_]
  swap
  · simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true]
    convert hw1 using 2
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [BitVec.reduceSignExtend, BitVec.toNat_ofNat]
      omega
    · show X86.Ext.leBytes (BitVec.setWidth 64 (BitVec.setWidth 8 (s.core.read .r13))) 1 = _
      rw [hr13]; rfl
  dsimp only
  intro hc3
  obtain ⟨m2, hw2⟩ : ∃ m', m1.writeBytes 0x412130
      (X86.Ext.leBytes (BitVec.ofNat 64 buf.length + 1#64) 8) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by
      rw [X86.Ext.length_leBytes]; exact perm_wb hw1 hob.olenW))
  rstep [hw2]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, kfoot⟩ := hk
  refine RunsTo.done ⟨hf, by assumption, rfl, obuf_append hob hlt hw1 hw2,
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  all_goals try (simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs, k1, k2, k3, k4, k5, k6, k7]; done)
  · xfoot [SiteFoot]

/-- The common path `0x404a75 → 0x404aa0`. -/
theorem s2_common (s : XState) (buf : Bytes) (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404a75#64) (hob : Obuf s.memory buf) (hpre : s2Pre buf s)
    (hlt : buf.length < 4096) :
    RunsTo (fun t => t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = 0x404aa0#64 ∧
      Obuf t.memory (buf ++ [0x20]) ∧ s2Post (buf ++ [0x20]) s t) s := by
  obtain ⟨hrdx, hr13, -⟩ := hpre
  rstep [hrip, hrdx]
  rstep [ne_4096 hlt]
  exact s2_append hf (by assumption) rfl hob hlt
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Memory.WritesWithin.refl _ _⟩ hr13

/-- The buffer-full branch `0x404a75 → 0x401100`. -/
theorem s2_call (s : XState) (buf : Bytes) (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404a75#64) (hob : Obuf s.memory buf) (hpre : s2Pre buf s)
    (hlen : buf.length = 4096) :
    RunsTo (fun t => FlushEntry t buf 0x40508f#64 ∧ OutErrorZero t.memory ∧
      (∃ F, Memory.WritesWithin s.memory t.memory F) ∧ CallMid s t) s := by
  obtain ⟨hrdx, -, ⟨hsp, hfr, hfw⟩⟩ := hpre
  have holW := hob.olenW
  have holen := hob.olen
  have hobuf := hob.obuf
  have hoe := hob.outError
  rstep [hrip, hrdx]
  rstep [eq_4096 hlen]
  rstep
  refine RunsTo.done ⟨⟨hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩, ?_,
    ⟨SiteFoot (s.core.read .rsp).toNat, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  rfin [hlen] [SiteFoot]
  all_goals try simp only [State.read_write_same, OutErrorZero]
  all_goals first
    | (simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    | xperm
    | ((repeat rmem [Bool.false_eq_true]))

/-- Back from `out_flush` at `0x40508f`: `jmp 0x404a82`, the append. -/
theorem s2_back (s t u : XState) (buf : Bytes) (hpre : s2Pre buf s) (hm : CallMid s t)
    (hx : FlushExit t 0x40508f#64 u) (hob : Obuf u.memory []) :
    RunsTo (fun v => v.faulted = false ∧ Lift.Code v.memory ∧ v.core.rip = 0x404aa0#64 ∧
      Obuf v.memory ([] ++ [0x20]) ∧ s2Post ([] ++ [0x20]) s v) u := by
  have hf := hx.faulted
  have hc := hx.code
  have hrip : u.core.rip = 0x40508f#64 := hx.rip
  have hk := kept_of_call (by have := hpre.2.2.sp; omega) hm hx
  have hr13 : u.core.read .r13 = 0x20#64 := by rw [hk.r13, hpre.2.1]
  rstep [hrip]
  exact s2_append hf (by assumption) rfl hob (by simp)
    ⟨hk.1, hk.2, hk.3, hk.4, hk.5, hk.6, hk.7, hk.8⟩ hr13

/-- **The second space** `0x404a75 → 0x404aa0` (VERIFIED). -/
theorem s2Site : PutcSite 0x404a75#64 0x404aa0#64 s2Pre (fun _ => 0x20) s2Post :=
  site_of_runs flushContract (fun _ _ _ => by decide) s2_common s2_call s2_back

/-! ## `print_filename("-", 0)`: `0x404aa0 → 0x404619`

```
404aa0: call 401270 ; (404aa5: jmp 404619)
401270: push %r12 ; push %rbp ; mov %rdi,%rbp ; push %rbx ; movzbl (%rdi),%ebx
        test %esi,%esi ; je 401418                 -- no escaping
401418: test %bl,%bl ; jne 401456
401456: mov olen,%rax ; add $1,%rbp ; cmp $0x1000,%rax ; jne 401434
        jmp 401428 (call out_flush ; mov olen,%rax)
401434: lea 1(%rax),%rdx ; mov %bl,obuf(%rax) ; mov %rdx,olen ; cmp $0xa,%bl ; je 401470
40144a: movzbl (%rbp),%ebx ; test %bl,%bl ; je 40132d
40132d: pop %rbx ; pop %rbp ; pop %r12 ; ret
```
-/

/-- What `print_filename` may write: its frame and `out_flush`'s below `rsp`, and the stdout
layer. -/
def PfFoot (sp : Nat) (a : Nat) : Prop :=
  (sp - 72 ≤ a ∧ a < sp) ∨ (0x41212c ≤ a ∧ a < 0x413140)

structure PfStack (s : XState) : Prop where
  sp : 0x414100 ≤ (s.core.read .rsp).toNat ∧ (s.core.read .rsp).toNat < 2 ^ 47
  frameR : s.memory.Permitted .read ((s.core.read .rsp).toNat - 72) 72
  frameW : s.memory.Permitted .write ((s.core.read .rsp).toNat - 72) 72

/-- The entry `0x404aa0`: `rdi = "-"`, `rsi = 0` (no escaping). -/
def pfPre (_buf : Bytes) (s : XState) : Prop :=
  s.core.read .rdi = 0x406052#64 ∧ s.core.read .rsi = 0#64 ∧
    s.memory.readWith .read 0x406052 2 = some [0x2d#8, 0#8] ∧ PfStack s

/-- What `print_filename` keeps. -/
structure PfKept (s s' : XState) : Prop where
  rsp : s'.core.read .rsp = s.core.read .rsp
  rbx : s'.core.read .rbx = s.core.read .rbx
  rbp : s'.core.read .rbp = s.core.read .rbp
  r12 : s'.core.read .r12 = s.core.read .r12
  r13 : s'.core.read .r13 = s.core.read .r13
  r14 : s'.core.read .r14 = s.core.read .r14
  r15 : s'.core.read .r15 = s.core.read .r15
  foot : Memory.WritesWithin s.memory s'.memory (PfFoot (s.core.read .rsp).toNat)

def pfPost (_buf' : Bytes) (s s' : XState) : Prop := PfKept s s'

/-- Inside `print_filename`, from the entry `s`: the saved registers and return address. -/
structure PfFrame (s t : XState) : Prop where
  sp : 0x414100 ≤ (s.core.read .rsp).toNat ∧ (s.core.read .rsp).toNat < 2 ^ 47
  frameR : t.memory.Permitted .read ((s.core.read .rsp).toNat - 72) 72
  frameW : t.memory.Permitted .write ((s.core.read .rsp).toNat - 72) 72
  rbx : t.core.read .rbx = 0x2d#64
  rbp : t.core.read .rbp = 0x406053#64
  r12 : t.core.read .r12 = s.core.read .r12
  r13 : t.core.read .r13 = s.core.read .r13
  r14 : t.core.read .r14 = s.core.read .r14
  r15 : t.core.read .r15 = s.core.read .r15
  sret : t.memory.readWith .read (s.core.read .rsp - 8#64).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [0x404aa5#64])
  sr12 : t.memory.readWith .read (s.core.read .rsp - 16#64).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.core.read .r12])
  srbp : t.memory.readWith .read (s.core.read .rsp - 24#64).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.core.read .rbp])
  srbx : t.memory.readWith .read (s.core.read .rsp - 32#64).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.core.read .rbx])
  nul : t.memory.readWith .read 0x406053 1 = some [0#8]
  foot : Memory.WritesWithin s.memory t.memory (PfFoot (s.core.read .rsp).toNat)

/-- `0x404aa0 → 0x401461`: the call, the prologue, the first byte `'-'`, `olen`. -/
theorem pf_pre (s : XState) (buf : Bytes) (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404aa0#64) (hob : Obuf s.memory buf) (hpre : pfPre buf s) :
    RunsTo (fun t => t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = 0x401461#64 ∧
      t.core.read .rsp = s.core.read .rsp - 32#64 ∧
      t.core.read .rax = BitVec.ofNat 64 buf.length ∧ PfFrame s t ∧ Obuf t.memory buf) s := by
  obtain ⟨hrdi, hrsi, hdash, ⟨hsp, hfr, hfw⟩⟩ := hpre
  have h0 : s.memory.readWith .read 0x406052 1 = some [0x2d#8] := by
    simpa using Memory.readWith_sub_range (offset := 0) (len := 1) hdash (by omega) (by omega)
  have h1 : s.memory.readWith .read 0x406053 1 = some [0#8] := by
    simpa using Memory.readWith_sub_range (offset := 1) (len := 1) hdash (by omega) (by omega)
  have hcap := hob.cap
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  have holen := hob.olen
  rstep [hrip]
  rstep
  rstep
  rstep [hrdi]
  rstep
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_movzb_ok (b := 0x2d#8) ?_]
  swap
  · simp only [State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, Lift.read_mk, Lift.core_regs, hrdi, BitVec.reduceSignExtend,
      BitVec.add_zero, BitVec.reduceToNat]
    repeat rmem [Bool.false_eq_true]
  intro hc5
  rstep [hrsi]
  rstep
  rstep
  rstep
  rstep [hl]
  rstep
  refine RunsTo.done ⟨hf, by assumption, rfl, ?_, ?_, ⟨⟨hsp.1, hsp.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  rfin [hrdi] [PfFoot]
  exact obuf_keep hob
    (F := fun a => (s.core.read .rsp).toNat - 32 ≤ a ∧ a < (s.core.read .rsp).toNat)
    (by xfoot [PfFoot]) (fun a ha => by omega)

theorem leBytes_2d : X86.Ext.leBytes (((0x2d#64 : Word).setWidth 8).setWidth 64) 1 = [ofU8 0x2d] :=
  by decide

/-- `0x401434 → 0x404619`: append `'-'`, the terminating `NUL`, the epilogue, the return. -/
theorem pf_tail {s t : XState} {buf : Bytes} (hf : t.faulted = false) (hc : Lift.Code t.memory)
    (hrip : t.core.rip = 0x401434#64) (hrsp : t.core.read .rsp = s.core.read .rsp - 32#64)
    (hrax : t.core.read .rax = BitVec.ofNat 64 buf.length) (hF : PfFrame s t)
    (hob : Obuf t.memory buf) (hlt : buf.length < 4096) :
    RunsTo (fun v => v.faulted = false ∧ Lift.Code v.memory ∧ v.core.rip = 0x404619#64 ∧
      Obuf v.memory (buf ++ [0x2d]) ∧ pfPost (buf ++ [0x2d]) s v) t := by
  obtain ⟨hsp, hfr, hfw, hrbx, hrbp, hr12, hr13, hr14, hr15, hsret, hsr12, hsrbp, hsrbx, hnul,
    hfoot⟩ := hF
  rstep [hrip, hrax]
  have hp1 : t.memory.Permitted .write (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufW (by omega) (by omega) (by omega)
  obtain ⟨m1, hw1⟩ : ∃ m', t.memory.writeBytes (0x412140 + buf.length) [ofU8 0x2d] = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by simpa using hp1))
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_store_b_ok' (m' := m1) ?_]
  swap
  · simp only [State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true]
    convert hw1 using 2
    · rw [BitVec.toNat_add]
      change (BitVec.toNat (t.core.read .rax) + _) % 2 ^ 64 = _
      rw [hrax]
      simp only [BitVec.reduceSignExtend, BitVec.toNat_ofNat]
      omega
    · show X86.Ext.leBytes (BitVec.setWidth 64 (BitVec.setWidth 8 (t.core.read .rbx))) 1 = _
      rw [hrbx]; rfl
  dsimp only
  intro hc2
  obtain ⟨m2, hw2⟩ : ∃ m', m1.writeBytes 0x412130
      (X86.Ext.leBytes (BitVec.ofNat 64 buf.length + 1#64) 8) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by
      rw [X86.Ext.length_leBytes]; exact perm_wb hw1 hob.olenW))
  rstep [hw2, hrax]
  rstep [hrbx]
  rstep [hrbx]
  refine run_instr' (by assumption) (by assumption) (by rfl) (by rfl) ?_
  rw [exec_movzb_ok (b := 0#8) ?_]
  swap
  · simp only [State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, Lift.read_mk, Lift.core_regs, BitVec.reduceSignExtend,
      BitVec.add_zero]
    rw [hrbp]
    simp only [BitVec.reduceToNat]
    repeat rmem [Bool.false_eq_true]
  intro hc5
  rstep
  rstep
  rstep [hrsp]
  rstep
  rstep
  rstep
  rstep
  refine RunsTo.done ⟨by assumption, by assumption, rfl, obuf_append hob hlt hw1 hw2,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  rfin [hrsp, hr12, hr13, hr14, hr15] [PfFoot]

/-- The common path `0x404aa0 → 0x404619` (`olen < 4096`). -/
theorem pf_common (s : XState) (buf : Bytes) (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404aa0#64) (hob : Obuf s.memory buf) (hpre : pfPre buf s)
    (hlt : buf.length < 4096) :
    RunsTo (fun t => t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = 0x404619#64 ∧
      Obuf t.memory (buf ++ [0x2d]) ∧ pfPost (buf ++ [0x2d]) s t) s := by
  refine (pf_pre s buf hf hc hrip hob hpre).bind fun t ⟨hf1, hc1, hrip1, hrsp1, hrax1, hF, hob1⟩ => ?_
  rstep [hrip1, hrax1]
  rstep [ne_4096 hlt]
  exact pf_tail hf1 (by assumption) rfl hrsp1 hrax1
    ⟨hF.1, hF.2, hF.3, hF.4, hF.5, hF.6, hF.7, hF.8, hF.9, hF.10, hF.11, hF.12, hF.13, hF.14,
      hF.15⟩ hob1 hlt

/-- The buffer-full branch `0x404aa0 → 0x401100`. -/
theorem pf_call (s : XState) (buf : Bytes) (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404aa0#64) (hob : Obuf s.memory buf) (hpre : pfPre buf s)
    (hlen : buf.length = 4096) :
    RunsTo (fun t => FlushEntry t buf 0x40142d#64 ∧ OutErrorZero t.memory ∧
      (∃ F, Memory.WritesWithin s.memory t.memory F) ∧
      (PfFrame s t ∧ t.core.read .rsp = s.core.read .rsp - 40#64)) s := by
  refine (pf_pre s buf hf hc hrip hob hpre).bind fun t ⟨hf1, hc1, hrip1, hrsp1, hrax1, hF, hob1⟩ => ?_
  obtain ⟨hsp, hfr, hfw, hrbx, hrbp, hr12, hr13, hr14, hr15, hsret, hsr12, hsrbp, hsrbx, hnul,
    hfoot⟩ := hF
  have holW := hob1.olenW
  have holen := hob1.olen
  have hobuf := hob1.obuf
  have hoe := hob1.outError
  rstep [hrip1, hrax1]
  rstep [eq_4096 hlen]
  rstep
  rstep [hrsp1]
  refine RunsTo.done ⟨⟨by assumption, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩, ?_,
    ⟨PfFoot (s.core.read .rsp).toNat, ?_⟩, ⟨⟨hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
  rfin [hlen, hrsp1, hrbx, hrbp, hr12, hr13, hr14, hr15] [PfFoot]
  all_goals try simp only [State.read_write_same, OutErrorZero]
  all_goals first
    | (simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    | xperm
    | (repeat rmem [Bool.false_eq_true])

/-- Back from `out_flush` at `0x40142d`: reload `olen`, then `pf_tail`. -/
theorem pf_back (s t u : XState) (buf : Bytes) (_hpre : pfPre buf s)
    (hm : PfFrame s t ∧ t.core.read .rsp = s.core.read .rsp - 40#64)
    (hx : FlushExit t 0x40142d#64 u) (hob : Obuf u.memory []) :
    RunsTo (fun v => v.faulted = false ∧ Lift.Code v.memory ∧ v.core.rip = 0x404619#64 ∧
      Obuf v.memory ([] ++ [0x2d]) ∧ pfPost ([] ++ [0x2d]) s v) u := by
  obtain ⟨⟨hsp, hfr, hfw, hrbx, hrbp, hr12, hr13, hr14, hr15, hsret, hsr12, hsrbp, hsrbx, hnul,
    hfoot⟩, hrsp⟩ := hm
  have hf := hx.faulted
  have hc := hx.code
  have hrip : u.core.rip = 0x40142d#64 := hx.rip
  have ht : (t.core.read .rsp).toNat = (s.core.read .rsp).toNat - 40 := by
    rw [hrsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hw := hx.foot
  rw [ht] at hw
  have e : ∀ k : Nat, k ≤ 32 → (s.core.read .rsp - BitVec.ofNat 64 k).toNat =
      (s.core.read .rsp).toNat - k := by
    intro k hk; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hF : PfFrame s u := by
    refine ⟨hsp, (hw.permitted_iff _ _ _).mpr hfr, (hw.permitted_iff _ _ _).mpr hfw,
      by rw [hx.rbx, hrbx], by rw [hx.rbp, hrbp], by rw [hx.r12, hr12], by rw [hx.r13, hr13],
      by rw [hx.r14, hr14], by rw [hx.r15, hr15], ?_, ?_, ?_, ?_, ?_,
      hfoot.trans (hw.mono fun a ha => by simp only [FlushFoot, PfFoot] at ha ⊢; omega)⟩
    · rw [hw.readWith fun o ho hin => by
        simp only [FlushFoot, e 8 (by omega)] at hin; omega]; exact hsret
    · rw [hw.readWith fun o ho hin => by
        simp only [FlushFoot, e 16 (by omega)] at hin; omega]; exact hsr12
    · rw [hw.readWith fun o ho hin => by
        simp only [FlushFoot, e 24 (by omega)] at hin; omega]; exact hsrbp
    · rw [hw.readWith fun o ho hin => by
        simp only [FlushFoot, e 32 (by omega)] at hin; omega]; exact hsrbx
    · rw [hw.readWith fun o ho hin => by simp only [FlushFoot] at hin; omega]; exact hnul
  have hrsp' : u.core.read .rsp = s.core.read .rsp - 32#64 := by
    rw [hx.rsp, hrsp]; exact bv_sub_add _ 40 8 (by omega)
  have holen := hob.olen
  rstep [hrip]
  exact pf_tail hf (by assumption) rfl hrsp' (by simp)
    ⟨hF.1, hF.2, hF.3, hF.4, hF.5, hF.6, hF.7, hF.8, hF.9, hF.10, hF.11, hF.12, hF.13, hF.14,
      hF.15⟩ hob (by simp)

/-- **`print_filename("-", 0)`** `0x404aa0 → 0x404619` (VERIFIED). -/
theorem pfSite : PutcSite 0x404aa0#64 0x404619#64 pfPre (fun _ => 0x2d) pfPost :=
  site_of_runs flushContract (fun _ _ _ => by decide) pf_common pf_call pf_back

/-! ## The delimiter: `0x404619 → 0x40464d` (`olen` in memory, `'\n'` flushes) -/

def s4Pre (_buf : Bytes) (s : XState) : Prop := s.core.read .rbp = 10#64 ∧ SiteStack s

def s4Post (_buf' : Bytes) (s s' : XState) : Prop := SiteKept s s'

theorem leBytes_0a : X86.Ext.leBytes (((10#64 : Word).setWidth 8).setWidth 64) 1 = [ofU8 10] :=
  by decide

/-- `0x40462a → 0x401100`: append `'\n'`, then the newline's `out_flush` call. -/
theorem s4_append {s0 s : XState} {buf : Bytes} (hf : s.faulted = false)
    (hc : Lift.Code s.memory) (hrip : s.core.rip = 0x40462a#64) (hob : Obuf s.memory buf)
    (hlt : buf.length < 4096) (hk : SiteKept s0 s) (hrbp : s.core.read .rbp = 10#64)
    (hst : SiteStack s0) :
    RunsTo (fun t => FlushEntry t (buf ++ [10]) 0x404be4#64 ∧ OutErrorZero t.memory ∧
      CallMid s0 t ∧ Obuf t.memory (buf ++ [10])) s := by
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  have holen := hob.olen
  obtain ⟨hsp, hfr, hfw⟩ := hst
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, kfoot⟩ := hk
  have hfr' := (kfoot.permitted_iff _ _ _).mpr hfr
  have hfw' := (kfoot.permitted_iff _ _ _).mpr hfw
  have hsp0 := hsp
  rw [← k1] at hfr' hfw' hsp
  rstep [hrip, hl]
  rstep
  have hp1 : s.memory.Permitted .write (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufW (by omega) (by omega) (by omega)
  obtain ⟨m1, hw1⟩ : ∃ m', s.memory.writeBytes (0x412140 + buf.length) [ofU8 10] = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by simpa using hp1))
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_store_b_ok' (m' := m1) ?_]
  swap
  · simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true]
    convert hw1 using 2
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [BitVec.reduceSignExtend, BitVec.toNat_ofNat]
      omega
    · show X86.Ext.leBytes (BitVec.setWidth 64 (BitVec.setWidth 8 (s.core.read .rbp))) 1 = _
      rw [hrbp]; rfl
  dsimp only
  intro hc3
  obtain ⟨m2, hw2⟩ : ∃ m', m1.writeBytes 0x412130
      (X86.Ext.leBytes (BitVec.ofNat 64 buf.length + 1#64) 8) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by
      rw [X86.Ext.length_leBytes]; exact perm_wb hw1 hob.olenW))
  rstep [hw2]
  have hob2 := obuf_append hob hlt hw1 hw2
  have holen2 := hob2.olen
  have hobuf2 := hob2.obuf
  have hoe2 := hob2.outError
  have holW2 := hob2.olenW
  rstep [hrbp]
  rstep [hrbp]
  rstep
  rename_i mm hmm hcm
  have hob3 : Obuf mm (buf ++ [10]) := obuf_keep hob2
    (F := fun a => (s.core.read .rsp).toNat - 8 ≤ a ∧ a < (s.core.read .rsp).toNat)
    (ww_store hmm (Memory.WritesWithin.refl _ _) fun x hx1 hx2 => by
      simp only [Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
        List.length_nil, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx1 hx2 ⊢
      omega)
    (fun a ha => by omega)
  refine RunsTo.done ⟨⟨by assumption, by assumption, rfl, ?_, ?_, ?_, hob3.olenW, ?_, hob3.olen,
    hob3.obuf, hob3.cap⟩, hob3.outError, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hob3⟩
  rfin [k2, k3, k4, k5, k6, k7] [SiteFoot]
  all_goals try simp only [State.read_write_same]
  all_goals first
    | (simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    | xperm
    | ((repeat rmem [Bool.false_eq_true]); done)
    | rw [k1]
    | xfoot [SiteFoot, k1]

/-- Back from the newline's `out_flush` at `0x404be4`: `jmp 0x40464d`. -/
theorem s4_done {s t u : XState} (hsp : 0x414028 ≤ (s.core.read .rsp).toNat) (hm : CallMid s t)
    (hx : FlushExit t 0x404be4#64 u) :
    RunsTo (fun v => v.faulted = false ∧ Lift.Code v.memory ∧ v.core.rip = 0x40464d#64 ∧
      v.memory = u.memory ∧ SiteKept s v) u := by
  have hf := hx.faulted
  have hc := hx.code
  have hrip : u.core.rip = 0x404be4#64 := hx.rip
  have hk := kept_of_call hsp hm hx
  rstep [hrip]
  exact RunsTo.done ⟨hf, by assumption, rfl, rfl, ⟨hk.1, hk.2, hk.3, hk.4, hk.5, hk.6, hk.7, hk.8⟩⟩

/-- The buffer-full branch `0x404619 → 0x401100`. -/
theorem s4_call {s : XState} {buf : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404619#64) (hob : Obuf s.memory buf) (hpre : s4Pre buf s)
    (hlen : buf.length = 4096) :
    RunsTo (fun t => FlushEntry t buf 0x404bd0#64 ∧ OutErrorZero t.memory ∧ CallMid s t ∧
      Obuf t.memory buf) s := by
  obtain ⟨-, ⟨hsp, hfr, hfw⟩⟩ := hpre
  have holW := hob.olenW
  have holen := hob.olen
  have hobuf := hob.obuf
  have hoe := hob.outError
  rstep [hrip, hlen]
  rstep [eq_4096 hlen]
  rstep
  rename_i mm hmm hcm
  have hob3 : Obuf mm buf := obuf_keep hob
    (F := fun a => (s.core.read .rsp).toNat - 8 ≤ a ∧ a < (s.core.read .rsp).toNat)
    (ww_store hmm (Memory.WritesWithin.refl _ _) fun x hx1 hx2 => by
      simp only [Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
        List.length_nil, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx1 hx2 ⊢
      omega)
    (fun a ha => by omega)
  refine RunsTo.done ⟨⟨by assumption, by assumption, rfl, ?_, ?_, ?_, hob3.olenW, ?_, hob3.olen,
    hob3.obuf, hob3.cap⟩, hob3.outError, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hob3⟩
  rfin [] [SiteFoot]
  all_goals try simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs]
  all_goals first
    | (simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
    | xperm
    | (repeat rmem [Bool.false_eq_true])

/-- Back from the buffer-full `out_flush` at `0x404bd0`: `jmp 0x40462a`, `s4_append`. -/
theorem s4_back1 {s t u : XState} {buf : Bytes} (hpre : s4Pre buf s) (hm : CallMid s t)
    (hx : FlushExit t 0x404bd0#64 u) (hob : Obuf u.memory []) :
    RunsTo (fun v => FlushEntry v ([] ++ [10]) 0x404be4#64 ∧ OutErrorZero v.memory ∧
      CallMid s v ∧ Obuf v.memory ([] ++ [10])) u := by
  have hf := hx.faulted
  have hc := hx.code
  have hrip : u.core.rip = 0x404bd0#64 := hx.rip
  have hk := kept_of_call (by have := hpre.2.sp; omega) hm hx
  have hrbp : u.core.read .rbp = 10#64 := by rw [hk.rbp, hpre.1]
  rstep [hrip]
  exact s4_append hf (by assumption) rfl hob (by simp)
    ⟨hk.1, hk.2, hk.3, hk.4, hk.5, hk.6, hk.7, hk.8⟩ hrbp hpre.2

/-- The common path `0x404619 → 0x401100` (`olen < 4096`). -/
theorem s4_common {s : XState} {buf : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404619#64) (hob : Obuf s.memory buf) (hpre : s4Pre buf s)
    (hlt : buf.length < 4096) :
    RunsTo (fun t => FlushEntry t (buf ++ [10]) 0x404be4#64 ∧ OutErrorZero t.memory ∧
      CallMid s t ∧ Obuf t.memory (buf ++ [10])) s := by
  have holen := hob.olen
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  rstep [hrip, hl]
  rstep [ne_4096 hlt]
  exact s4_append hf (by assumption) rfl hob hlt
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Memory.WritesWithin.refl _ _⟩ hpre.1 hpre.2

theorem putcBuf_nl_snd (buf : Bytes) : (Sys.IOLayer.putcBuf 4096 buf 10).2 = [] := by
  simp [Sys.IOLayer.putcBuf]

/-- **The delimiter** `0x404619 → 0x40464d` (VERIFIED): `'\n'` appended and flushed. -/
theorem s4Site : PutcSite 0x404619#64 0x40464d#64 s4Pre (fun _ => 10) s4Post := by
  intro w message K g h buf emitted hfull hfd hrip hcode hobuf hpre hco hok hrd hem k
  have hfa : g.x.faulted = false := hok.2.2.2.2.2
  have hsp := hpre.2.sp
  simp only [putcBuf_nl_snd] at k
  have fin : ∀ (t : XState) (g' : GS) (h' : List Ev) (bufp : Bytes), CallMid g.x t →
      Obuf t.memory bufp → FlushExit t 0x404be4#64 g'.x → g'.exited = none → g'.k = g.k →
      OutErrorZero g'.x.memory → Coalesced h' [] (emitted ++ [10]) →
      stdinRead h' = stdinRead h → Ok message g' h' → Leads (GStep w) (Ok message) K g' h' := by
    intro t g' h' bufp hm hobt hx hex hk' hoe' hco' hrd' hok'
    refine (s4_done (by omega) hm hx).leads hex hok' fun v ⟨hf', hc', hrip', hmem, hkept⟩ => ?_
    have hob' : Obuf v.memory [] := hmem ▸ obuf_nil_of hobt hx.foot hx.olen hoe'
    exact k { g' with x := v } h' hrip' hf' hex hk' hc' hob' hco' hrd'
      (Stdout.Ok.with_x hok' hf') hkept
  by_cases hlen : buf.length = 4096
  · refine (s4_call hfa hcode hrip hobuf hpre hlen).leads hok.1 hok
      fun t ⟨he, hoe, hm, hobt⟩ => ?_
    refine flushContract w message K { g with x := t } h buf emitted 0x404bd0#64 hfull hfd he hoe
      hco (Stdout.Ok.with_x hok he.faulted) hrd
      (List.IsPrefix.trans (by simp [List.map_append]) hem) ?_
    intro g1 h1 hx hex hk1 hoe1 hco1 hrd1 hok1
    have hob1 : Obuf g1.x.memory [] := obuf_nil_of hobt hx.foot hx.olen hoe1
    refine (s4_back1 hpre hm hx hob1).leads hex hok1 fun v ⟨he2, hoe2, hm2, hobv⟩ => ?_
    refine flushContract w message K { g1 with x := v } h1 ([] ++ [10]) (emitted ++ [10])
      0x404be4#64 hfull (by rw [show ({ g1 with x := v } : GS).k = g.k from hk1]; exact hfd)
      he2 hoe2 (coalesced_snoc hco1 10) (Stdout.Ok.with_x hok1 he2.faulted) (by rw [hrd1]; exact hrd)
      hem ?_
    intro g2 h2 hx2 hex2 hk2 hoe2' hco2 hrd2 hok2
    exact fin v g2 h2 _ hm2 hobv hx2 hex2 (hk2.trans hk1) hoe2' hco2 (by rw [hrd2, hrd1]) hok2
  · have hlt : buf.length < 4096 := by have := hobuf.cap; omega
    refine (s4_common hfa hcode hrip hobuf hpre hlt).leads hok.1 hok
      fun t ⟨he, hoe, hm, hobt⟩ => ?_
    refine flushContract w message K { g with x := t } h (buf ++ [10]) (emitted ++ [10])
      0x404be4#64 hfull hfd he hoe (coalesced_snoc hco 10) (Stdout.Ok.with_x hok he.faulted) hrd
      hem ?_
    intro g2 h2 hx2 hex2 hk2 hoe2' hco2 hrd2 hok2
    exact fin t g2 h2 _ hm hobt hx2 hex2 hk2 hoe2' hco2 hrd2 hok2

/-! ## The suffix -/

/-- Where the hex loop and the suffix may write, around `cmain`'s `rsp = sp`. -/
def SufFoot (sp : Nat) (a : Nat) : Prop :=
  (sp - 128 ≤ a ∧ a < sp) ∨ (0x41212c ≤ a ∧ a < 0x413140) ∨ (sp + 0x18 ≤ a ∧ a < sp + 0x1c) ∨
    a = sp + 0x20

theorem keepR {m m' : Memory} {F : Nat → Prop} (hw : Memory.WritesWithin m m' F) {a len : Nat}
    {v : Option (List Byte)} (hout : ∀ o < len, ¬ F (a + o)) (h : m.readWith .read a len = v) :
    m'.readWith .read a len = v :=
  (hw.readWith hout).trans h

theorem stacks_of {s0m : Memory} {x : XState} {sp : Word} (hM : SufMem sp s0m)
    (hw : Memory.WritesWithin s0m x.memory (SufFoot sp.toNat)) (hrsp : x.core.read .rsp = sp) :
    SiteStack x ∧ PfStack x := by
  have hb := hM.spBound
  have hR := (hw.permitted_iff _ _ _).mpr hM.stackR
  have hW := (hw.permitted_iff _ _ _).mpr hM.stackW
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> rw [hrsp]
  · omega
  · exact X86.Ext.Memory.Permitted.sub hR (by omega) (by omega) (by omega)
  · exact X86.Ext.Memory.Permitted.sub hW (by omega) (by omega) (by omega)
  · omega
  · exact X86.Ext.Memory.Permitted.sub hR (by omega) (by omega) (by omega)
  · exact X86.Ext.Memory.Permitted.sub hW (by omega) (by omega) (by omega)

theorem toNat_add_small {sp : Word} (k : Nat) (hk : k < 0x100) (hb : sp.toNat + 0x100 < 2 ^ 47) :
    (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem leBytes_10_8 : X86.Ext.leBytes ((10#8 : BitVec 8).setWidth 64) 1 = [10#8] := by decide

theorem prefix_of {e : Bytes} {message : List Byte} (xs ys : Bytes)
    (hxy : xs ++ ys = recordTail)
    (hans : (e ++ recordTail).map UInt8.toBitVec = expected message) :
    (e ++ xs).map UInt8.toBitVec <+: expected message :=
  ⟨ys.map UInt8.toBitVec, by rw [← hans, ← hxy]; simp⟩

/-- **The suffix of the format segment** `0x404605 → 0x40464d` (VERIFIED): `"  -"` through the
two space sites and `print_filename`, then the delimiter `'\n'`, whose `out_flush` writes the
rest of the record. -/
theorem suffix (domain : List Byte → Prop) : Seg domain HexExitCut FormattedCut := by
  intro prog posix fs message g h _ ⟨s0, buf, e, hat⟩
  obtain ⟨hok, hrip, hcode, hfd0, hfd1, hfd2, hE, hrbx0, hrbp0, hr120, hr130, hM, hrax, hobuf,
    hco, hrd, hans⟩ := hat
  have hfull : (Silmaril.Process.LPS.Problems.GnuSha256sum.world [prog] posix fs
      message).stdoutFull = false := rfl
  have hb := hM.spBound
  have hfa := hok.2.2.2.2.2
  have hgrsp : g.x.core.read .rsp = s0.core.read .rsp := hE.rsp
  have hW0 : Memory.WritesWithin s0.memory g.x.memory (SufFoot (s0.core.read .rsp).toNat) :=
    hE.foot.mono fun a ha => by
      simp only [HexFoot, SiteFoot] at ha; simp only [SufFoot]; omega
  have hpt1 := keepR hW0 (fun o ho => by
    rw [toNat_add_small 0x10 (by omega) hb.2]; simp only [SufFoot]; omega) hM.prefixTag
  have hsb : g.x.memory.readWith .read (s0.core.read .rsp + 0x18#64).toNat 4 =
      some (X86.Ext.leBytes 0#64 4) := by
    rw [toNat_add_small 0x18 (by omega) hb.2]; have := hE.spillB; rw [hrbx0] at this
    simpa using this
  have hsp : g.x.memory.readWith .read (s0.core.read .rsp + 0x20#64).toNat 1 = some [10#8] := by
    rw [toNat_add_small 0x20 (by omega) hb.2]; have := hE.spillP; rw [hrbp0, leBytes_10_8] at this
    exact this
  refine (run_head hfa hcode hrip hgrsp hpt1 hsb hsp).leads hok.1 hok fun u hu => ?_
  -- the first space
  have hursp : u.core.read .rsp = s0.core.read .rsp := hu.rsp.trans hgrsp
  have hWu : Memory.WritesWithin s0.memory u.memory (SufFoot (s0.core.read .rsp).toNat) :=
    hu.mem ▸ hW0
  refine s1Site _ message _ { g with x := u } h buf e hfull hfd1 hu.rip hu.code (hu.mem ▸ hobuf)
    ⟨by rw [hu.rax]; exact hrax, (stacks_of hM hWu hursp).1⟩ hco
    (Stdout.Ok.with_x hok hu.faulted) hrd (prefix_of [0x20] [0x20, 0x2d, 0x0a] rfl hans) ?_
  intro g1 h1 hrip1 hf1 hex1 hk1 hc1 hob1 hco1 hrd1 hok1 ⟨hkp1, hrdx1⟩
  have hrsp1 : g1.x.core.read .rsp = s0.core.read .rsp := hkp1.rsp.trans hursp
  have hW1 : Memory.WritesWithin s0.memory g1.x.memory (SufFoot (s0.core.read .rsp).toNat) :=
    hWu.trans (hkp1.foot.mono fun a ha => by
      rw [hursp] at ha; simp only [SiteFoot] at ha; simp only [SufFoot]; omega)
  -- the binary flag
  have hr13 : (g1.x.core.read .r13).setWidth 32 = 0#32 := by
    rw [hkp1.r13, hu.r13, hE.r13]; exact hr130
  refine (run_b hf1 hc1 hrip1 hr13).leads hex1 hok1 fun v hv => ?_
  have hvrsp : v.core.read .rsp = s0.core.read .rsp := hv.rsp.trans hrsp1
  have hWv : Memory.WritesWithin s0.memory v.memory (SufFoot (s0.core.read .rsp).toNat) :=
    hv.mem ▸ hW1
  -- the second space
  refine s2Site _ message _ { g1 with x := v } h1 _ (e ++ [0x20]) hfull (hk1 ▸ hfd1) hv.rip hv.code
    (hv.mem ▸ hob1) ⟨by rw [hv.rdx]; exact hrdx1, hv.r13, (stacks_of hM hWv hvrsp).1⟩ hco1
    (Stdout.Ok.with_x hok1 hv.faulted) (by rw [hrd1]; exact hrd)
    (by simpa using prefix_of [0x20, 0x20] [0x2d, 0x0a] rfl hans) ?_
  intro g2 h2 hrip2 hf2 hex2 hk2 hc2 hob2 hco2 hrd2 hok2 ⟨hkp2, hrdi2, hrsi2⟩
  have hrsp2 : g2.x.core.read .rsp = s0.core.read .rsp := hkp2.rsp.trans hvrsp
  have hW2 : Memory.WritesWithin s0.memory g2.x.memory (SufFoot (s0.core.read .rsp).toNat) :=
    hWv.trans (hkp2.foot.mono fun a ha => by
      rw [hvrsp] at ha; simp only [SiteFoot] at ha; simp only [SufFoot]; omega)
  -- print_filename
  have hrbx2 : v.core.read .rbx = 0#64 := by rw [hv.rbx, hkp1.rbx, hu.rbx]
  have hdash2 := keepR hW2 (fun o ho => by simp only [SufFoot]; omega) hM.dash
  refine pfSite _ message _ g2 h2 _ (e ++ [0x20] ++ [0x20]) hfull (hk2.trans hk1 ▸ hfd1) hrip2 hc2
    hob2 ⟨by rw [hrdi2, hv.r12, hkp1.r12, hu.r12, hE.r12, hr120],
      by rw [hrsi2, hrbx2]; rfl, hdash2, (stacks_of hM hW2 hrsp2).2⟩ hco2 hok2
    (by rw [hrd2, hrd1]; exact hrd)
    (by simpa using prefix_of [0x20, 0x20, 0x2d] [0x0a] rfl hans) ?_
  intro g3 h3 hrip3 hf3 hex3 hk3 hc3 hob3 hco3 hrd3 hok3 hkp3
  have hrsp3 : g3.x.core.read .rsp = s0.core.read .rsp := hkp3.rsp.trans hrsp2
  have hW3 : Memory.WritesWithin s0.memory g3.x.memory (SufFoot (s0.core.read .rsp).toNat) :=
    hW2.trans (hkp3.foot.mono fun a ha => by
      rw [hrsp2] at ha; simp only [PfFoot] at ha; simp only [SufFoot]; omega)
  -- the delimiter
  have hrbp3 : g3.x.core.read .rbp = 10#64 := by
    rw [hkp3.rbp, hkp2.rbp, hv.rbp, hkp1.rbp, hu.rbp]
  refine s4Site _ message _ g3 h3 _ (e ++ [0x20] ++ [0x20] ++ [0x2d]) hfull
    (hk3.trans (hk2.trans hk1) ▸ hfd1) hrip3 hc3 hob3 ⟨hrbp3, (stacks_of hM hW3 hrsp3).1⟩ hco3
    hok3 (by rw [hrd3, hrd2, hrd1]; exact hrd)
    (by simpa using prefix_of [0x20, 0x20, 0x2d, 0x0a] [] rfl hans) ?_
  intro g4 h4 hrip4 hf4 hex4 hk4 hc4 hob4 hco4 hrd4 hok4 hkp4
  simp only [putcBuf_nl_snd] at hob4 hco4
  have hrsp4 : g4.x.core.read .rsp = s0.core.read .rsp := hkp4.rsp.trans hrsp3
  have hW4 : Memory.WritesWithin s0.memory g4.x.memory (SufFoot (s0.core.read .rsp).toNat) :=
    hW3.trans (hkp4.foot.mono fun a ha => by
      rw [hrsp3] at ha; simp only [SiteFoot] at ha; simp only [SufFoot]; omega)
  have hk : g4.k = g.k := hk4.trans (hk3.trans (hk2.trans hk1))
  have hwr : out h4 = expected message := by
    rw [← hans]
    have := hco4
    simp only [Coalesced, List.map_nil, List.append_nil] at this
    rw [this]; simp [recordTail]
  have e8 := toNat_add_small (sp := s0.core.read .rsp) 8 (by omega) hb.2
  have e2c := toNat_add_small (sp := s0.core.read .rsp) 0x2c (by omega) hb.2
  have e50 := toNat_add_small (sp := s0.core.read .rsp) 0x50 (by omega) hb.2
  refine Leads.done ⟨hex4, ⟨hf4, OkH.of_ok hok4, by rw [hrd4, hrd3, hrd2, hrd1, hrd], hwr,
    ⟨hc4, ⟨by rw [hrsp4]; omega, by rw [hrsp4]; omega⟩, ?_, ?_, ?_, ?_, by simpa using hob4.olen,
      hob4.outError, ?_⟩⟩, hrip4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrsp4]
    exact X86.Ext.Memory.Permitted.sub ((hW4.permitted_iff _ _ _).mpr hM.stackR) (by omega)
      (by omega) (by omega)
  · rw [hrsp4]
    exact X86.Ext.Memory.Permitted.sub ((hW4.permitted_iff _ _ _).mpr hM.stackW) (by omega)
      (by omega) (by omega)
  · rw [hrsp4]
    exact keepR hW4 (fun o ho => by rw [e2c]; simp only [SufFoot]; omega) hM.okFlag
  · exact keepR hW4 (fun o ho => by simp only [SufFoot]; omega) hM.haveStdin
  · exact keepR hW4 (fun o ho => by simp only [SufFoot]; omega) hM.errError
  · rw [hrsp4]
    exact keepR hW4 (fun o ho => by rw [e8]; simp only [SufFoot]; omega) hM.index
  · rw [hrsp4]
    exact keepR hW4 (fun o ho => by rw [e50]; simp only [SufFoot]; omega) hM.nOps
  · rw [hk]; exact hfd0
  · rw [hk]; exact ⟨_, hfd1⟩
  · rw [hk]; exact hfd2

end Silmaril.Apps.Sha256sum.Stdout
