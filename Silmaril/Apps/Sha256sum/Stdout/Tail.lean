module

public import Silmaril.Apps.Sha256sum.Stdout.Sc3

/-! # The tail of `sha256sum-min`'s stdin run: `Formatted` to `Done`

Status: **VERIFIED** (no `sorry`, standard axioms only).

From `0x40464d` (back in `cmain` after `output_file`; the 68-byte record already flushed by the
delimiter's `out_putc`, so `olen = 0`) the binary leaves the operand loop, closes standard
input (`have_read_stdin`), calls `close_stdout` (nothing pending, no previous error:
`close(1)`, then `close(2)` with `err_error = 0`) and `sys_exit(!ok)` = `exit_group(0)`.

`exitSegment : ExitSegment domain FormattedCut` is that segment in the parametric form of
`GnuSha256sum.SysModel` (`Release.Open.exit`). It is proved block by block (`tail_loop`,
`tail_close0`, `tail_cs1a`, `tail_cs1b`, `tail_cs2`, `tail_cs3`, `tail_exit1`, `tail_exit2`),
each a symbolic run in a `Leads` goal (`Stdout.LeadsX`), with the three closes and the exit
through `sc3` (`Stdout.Sc3`). The blocks are short because a long run with several stores
builds a proof term the kernel rejects ("deep recursion").
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word State Reg)
open Silmaril.Process (Memory Byte)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev Done)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits

/-- What the tail needs of memory: the code, `cmain`'s frame at `sp` (the callee frames below
it), `ok = 1` (`0x2c(%rsp)`), `have_read_stdin = 1`, `olen = 0`, `out_error = 0`,
`err_error = 0`. -/
structure TM (sp : Word) (m : Memory) : Prop where
  code : Lift.Code m
  spBound : 0x414100 ≤ sp.toNat ∧ sp.toNat < 2 ^ 47
  stackR : m.Permitted .read (sp.toNat - 64) (64 + 0x58)
  stackW : m.Permitted .write (sp.toNat - 64) (64 + 0x58)
  okFlag : m.readWith .read (sp + 0x2c#64).toNat 4 = some (X86.Ext.leBytes 1#64 4)
  haveStdin : m.readWith .read 0x40a0a0 4 = some (X86.Ext.leBytes 1#64 4)
  olen : m.readWith .read 0x412130 8 = some (X86.Ext.leBytes 0#64 8)
  outError : m.readWith .read 0x41212c 4 = some (X86.Ext.leBytes 0#64 4)
  errError : m.readWith .read 0x412128 4 = some (X86.Ext.leBytes 0#64 4)

/-- The history and the program state along the tail: the whole message read, exactly the
answer written. -/
structure TI (message : List Byte) (sp : Word) (h : List Ev) (x : XState) : Prop where
  faulted : x.faulted = false
  okh : OkH message h
  read : Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead h = message
  written : Silmaril.Process.LPS.Problems.GnuSha256sum.out h =
    Silmaril.Process.LPS.Problems.GnuSha256sum.expected message
  tm : TM sp x.memory

/-- `sys_exit` at `0x40119c`: `exit_group(rbx = 0)`. -/
theorem tail_exit2 {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {sp : Word} (ht : TI message sp h x) (hrip : x.core.rip = 0x40119c#64)
    (hrsp : x.core.read .rsp = sp - 16#64) (hrbx : x.core.read .rbx = 0#64) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  obtain ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, -, -, -, -, -⟩ := ht
  lstep [hrip, hrbx, hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  exact sc3_exit hh hf (by assumption) rfl (by simp) (by simp) hrd hwr

/-- `0x4046a9`, back from `close_stdout`: `sys_exit(!ok)`. -/
theorem tail_exit1 {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {sp : Word} (ht : TI message sp h x) (hrip : x.core.rip = 0x4046a9#64)
    (hrsp : x.core.read .rsp = sp) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  obtain ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, hok, hhs, hol, hoe, hee⟩ := ht
  lstep [hrip, hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  refine tail_exit2 (sp := sp) ⟨hf, hh, hrd, hwr, by assumption, hspb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ rfl
    (by simp) (by simp)
  rfin [Bool.false_eq_true] [Bool.false_eq_true]

/-- `close_stdout`'s frame below `cmain`'s `sp`: the return address `0x4046a9` and the four
saved registers. -/
structure CSFrame (sp : Word) (m : Memory) : Prop where
  ret : m.readWith .read (sp - 8#64).toNat 8 = some (encodeWords [0x4046a9#64])
  s13 : ∃ v, m.readWith .read (sp - 16#64).toNat 8 = some (encodeWords [v])
  s12 : ∃ v, m.readWith .read (sp - 24#64).toNat 8 = some (encodeWords [v])
  sbp : ∃ v, m.readWith .read (sp - 32#64).toNat 8 = some (encodeWords [v])
  sbx : ∃ v, m.readWith .read (sp - 40#64).toNat 8 = some (encodeWords [v])

/-- `close_stdout` at `0x402b0f`, after `close(2)` returned `0`: `err_error = 0`, return. -/
theorem tail_cs3 {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {sp : Word} (ht : TI message sp h x) (hcs : CSFrame sp x.memory)
    (hrip : x.core.rip = 0x402b0f#64) (hrsp : x.core.read .rsp = sp - 48#64)
    (hrax : x.core.read .rax = 0#64) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  obtain ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, hok, hhs, hol, hoe, hee⟩ := ht
  obtain ⟨hra, ⟨v13, h13⟩, ⟨v12, h12⟩, ⟨vbp, hbp⟩, ⟨vbx, hbx⟩⟩ := hcs
  lstep [hrip, hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp, hrax]
  lstep [hrsp, hrax]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  exact tail_exit1 (sp := sp) ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, hok, hhs, hol, hoe, hee⟩ rfl
    (by simp)

/-- `close_stdout` at `0x402ae9`, after `close(1)` returned `0` (no pending bytes, no previous
error): `close(2)`. -/
theorem tail_cs2 {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {sp : Word} {src : Src} (ht : TI message sp h x) (hcs : CSFrame sp x.memory)
    (hk2 : k.fds 2 = some src)
    (hrip : x.core.rip = 0x402ae9#64) (hrsp : x.core.read .rsp = sp - 48#64)
    (hrax : x.core.read .rax = 0#64) (hr12 : x.core.read .r12 = 0#64)
    (hr13 : x.core.read .r13 = 0#64) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  obtain ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, hok, hhs, hol, hoe, hee⟩ := ht
  obtain ⟨hra, ⟨v13, h13⟩, ⟨v12, h12⟩, ⟨vbp, hbp⟩, ⟨vbx, hbx⟩⟩ := hcs
  lstep [hrip, hrsp, hrax]
  lstep [hrsp, hrax]
  lstep [hrsp, hr12]
  lstep [hrsp, hr12]
  lstep [hrsp, hr13]
  lstep [hrsp, hr13]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  refine sc3_close (fd := 2) hh hf (by assumption) rfl (by simp) (by simp) (by decide) hk2
    (by simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true]; repeat rmem [Bool.false_eq_true]) ?_
  intro y hfy hcy hmy hripy hrspy hraxy hregs
  have hh' := hh.close (by decide : 2 ≤ 2) (.ok 0)
  refine tail_cs3 (sp := sp) ⟨hfy, hh', by rw [in_close, hrd], by rw [out_close, hwr],
    hcy, hspb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩ hripy
    (by rw [hrspy]; simp [bv_sub_add]) hraxy
  all_goals try rw [hmy]
  rfin [Bool.false_eq_true] [Bool.false_eq_true]
  · exact ⟨v13, by (repeat rmem [Bool.false_eq_true])⟩
  · exact ⟨v12, by (repeat rmem [Bool.false_eq_true])⟩
  · exact ⟨vbp, by (repeat rmem [Bool.false_eq_true])⟩
  · exact ⟨vbx, by (repeat rmem [Bool.false_eq_true])⟩

/-- `close_stdout` at `0x402aba`, its frame pushed: `olen = 0` (no flush), `out_error = 0`,
`close(1)`. -/
theorem tail_cs1b {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {sp : Word} {src1 src2 : Src} (ht : TI message sp h x) (hcs : CSFrame sp x.memory)
    (hk1 : k.fds 1 = some src1) (hk2 : k.fds 2 = some src2)
    (hrip : x.core.rip = 0x402aba#64) (hrsp : x.core.read .rsp = sp - 48#64) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  obtain ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, hok, hhs, hol, hoe, hee⟩ := ht
  obtain ⟨hra, ⟨v13, h13⟩, ⟨v12, h12⟩, ⟨vbp, hbp⟩, ⟨vbx, hbx⟩⟩ := hcs
  lstep [hrip, hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  refine sc3_close (fd := 1) hh hf (by assumption) rfl (by simp) (by simp) (by decide) hk1
    (by simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true]; repeat rmem [Bool.false_eq_true]) ?_
  intro y hfy hcy hmy hripy hrspy hraxy hregs
  have hh' := hh.close (by decide : 1 ≤ 2) (.ok 0)
  refine tail_cs2 (sp := sp) (src := src2) ⟨hfy, hh', by rw [in_close, hrd], by rw [out_close, hwr],
    hcy, hspb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩
    (by simp [KState.set, hk2]) hripy (by rw [hrspy]; simp [bv_sub_add]) hraxy
    (by rw [hregs .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; simp)
    (by rw [hregs .r13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; simp)
  all_goals try rw [hmy]
  rfin [Bool.false_eq_true] [Bool.false_eq_true]
  · exact ⟨v13, by (repeat rmem [Bool.false_eq_true])⟩
  · exact ⟨v12, by (repeat rmem [Bool.false_eq_true])⟩
  · exact ⟨vbp, by (repeat rmem [Bool.false_eq_true])⟩
  · exact ⟨vbx, by (repeat rmem [Bool.false_eq_true])⟩

/-- `0x404baa`, after `close(0)` returned `0`: the call of `close_stdout` and its prologue. -/
theorem tail_cs1a {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {sp : Word} {src1 src2 : Src} (ht : TI message sp h x)
    (hk1 : k.fds 1 = some src1) (hk2 : k.fds 2 = some src2)
    (hrip : x.core.rip = 0x404baa#64) (hrsp : x.core.read .rsp = sp)
    (hrax : x.core.read .rax = 0#64) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  obtain ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, hok, hhs, hol, hoe, hee⟩ := ht
  lstep [hrip, hrsp, hrax]
  lstep [hrsp, hrax]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  refine tail_cs1b (sp := sp) (src1 := src1) (src2 := src2) ⟨hf, hh, hrd, hwr, by assumption, hspb,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ⟨x.core.read .r13, ?_⟩, ⟨x.core.read .r12, ?_⟩, ⟨x.core.read .rbp, ?_⟩,
      ⟨x.core.read .rbx, ?_⟩⟩ hk1 hk2 rfl (by simp)
  rfin [Bool.false_eq_true] [Bool.false_eq_true]

/-- `0x404697`: `have_read_stdin`, so `close(0)`. -/
theorem tail_close0 {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {sp : Word} {src0 src1 src2 : Src} (ht : TI message sp h x) (hk0 : k.fds 0 = some src0)
    (hk1 : k.fds 1 = some src1) (hk2 : k.fds 2 = some src2)
    (hrip : x.core.rip = 0x404697#64) (hrsp : x.core.read .rsp = sp) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  obtain ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, hok, hhs, hol, hoe, hee⟩ := ht
  lstep [hrip, hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  lstep [hrsp]
  refine sc3_close (fd := 0) hh hf (by assumption) rfl (by simp) (by simp) (by decide) hk0
    (by simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true]; repeat rmem [Bool.false_eq_true]) ?_
  intro y hfy hcy hmy hripy hrspy hraxy hregs
  have hh' := hh.close (by decide : 0 ≤ 2) (.ok 0)
  refine tail_cs1a (sp := sp) (src1 := src1) (src2 := src2) ⟨hfy, hh', by rw [in_close, hrd],
    by rw [out_close, hwr], hcy, hspb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by simp [KState.set, hk1]) (by simp [KState.set, hk2]) hripy
    (by rw [hrspy]; simp) hraxy
  all_goals try rw [hmy]
  rfin [Bool.false_eq_true] [Bool.false_eq_true]

/-- `0x40464d`, back in `cmain` after `output_file` (the record emitted and flushed): the
operand loop ends (`k + 1 = n_operands = 1`). -/
theorem tail_loop {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {sp : Word} {src0 src1 src2 : Src} (ht : TI message sp h x) (hk0 : k.fds 0 = some src0)
    (hk1 : k.fds 1 = some src1) (hk2 : k.fds 2 = some src2)
    (hrip : x.core.rip = 0x40464d#64) (hrsp : x.core.read .rsp = sp)
    (hidx : x.memory.readWith .read (sp + 0x8#64).toNat 8 = some (X86.Ext.leBytes 0#64 8))
    (hn : x.memory.readWith .read (sp + 0x50#64).toNat 4 = some (X86.Ext.leBytes 1#64 4)) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  obtain ⟨hf, hh, hrd, hwr, hc, hspb, hsr, hsw, hok, hhs, hol, hoe, hee⟩ := ht
  subst hrsp
  lstep [hrip]
  lstep
  lstep
  lstep
  lstep
  lstep
  lstep
  lstep
  lstep
  refine tail_close0 (src0 := src0) (src1 := src1) (src2 := src2) ⟨hf, hh, hrd, hwr, by assumption,
    hspb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hk0 hk1 hk2 rfl (by simp)
  rfin [Bool.false_eq_true] [Bool.false_eq_true]

/-- **The `Formatted` cut** (`0x40464d`): the whole message read, exactly the answer written,
the operand index `0` of `n_operands = 1`, `ok = 1`, `have_read_stdin = 1`, the stdout layer
empty without error (`olen = 0`, `out_error = 0`), `err_error = 0`, and descriptors 0, 1, 2
open. -/
structure AtFormatted (message : List Byte) (g : GS) (h : List Ev) : Prop where
  exited : g.exited = none
  ti : TI message (g.x.core.read .rsp) h g.x
  rip : g.x.core.rip = 0x40464d#64
  index : g.x.memory.readWith .read (g.x.core.read .rsp + 0x8#64).toNat 8 =
    some (X86.Ext.leBytes 0#64 8)
  nOps : g.x.memory.readWith .read (g.x.core.read .rsp + 0x50#64).toNat 4 =
    some (X86.Ext.leBytes 1#64 4)
  fd0 : ∃ s, g.k.fds 0 = some s
  fd1 : ∃ s, g.k.fds 1 = some s
  fd2 : ∃ s, g.k.fds 2 = some s

/-- `AtFormatted` as a cut predicate. -/
def FormattedCut : Silmaril.Process.LPS.Problems.GnuSha256sum.Cut :=
  fun _ message g h => AtFormatted message g h

/-- **The exit segment** (VERIFIED): from `Formatted`, `close(0)`, `close_stdout` (no pending
bytes: `close(1)`, `close(2)`) and `exit_group(0)`, on every stdin-tier world, whatever `r11`
the kernel leaves at each return. -/
theorem exitSegment (domain : List Byte → Prop) :
    Silmaril.Process.LPS.Problems.GnuSha256sum.ExitSegment domain FormattedCut := by
  intro prog posix fs message g h _ hat
  obtain ⟨hx, ht, hrip, hidx, hn, ⟨s0, h0⟩, ⟨s1, h1⟩, ⟨s2, h2⟩⟩ := hat
  obtain ⟨x, k, e⟩ := g
  simp only at hx; subst hx
  exact tail_loop ht h0 h1 h2 hrip rfl hidx hn

end Silmaril.Apps.Sha256sum.Stdout
