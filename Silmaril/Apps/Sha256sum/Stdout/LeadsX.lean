module

public import Silmaril.Apps.Sha256sum.Stdout.Run

/-! # Symbolic execution directly in `Leads` goals

Status: **VERIFIED** (lemmas: no `sorry`, standard axioms only).

A segment with system calls in the middle (`close(0)`, `close_stdout`, `exit_group`) is easiest
to prove in one symbolic run that crosses the calls. The goal is
`Leads (GStep w) (Ok message) Post ⟨x, k, none⟩ h`: the program state `x` is executed one
instruction at a time (`lstep`, the `rstep` of `Stdout.Run` over `leads_instr'`), and at the
`syscall` of `sc3` the call is a `Leads` step (`leadsX_call`, `leadsX_exit`) whose replies, for
every `r11`, continue the run. `OkH` is the part of `Ok` that only depends on the history; it
is constant along silent steps.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Process (Memory Byte)
open Silmaril.Machine.Execution (Reaches run run_succ)
open Silmaril.Process.LPS.Problems.GnuSha256sum (retStep GS GStep Ok Ev Allowed Done ReadBuf
  leads_seq leads_call leads_exit)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- The history half of `Ok`. -/
def OkH (message : List Byte) (h : List Ev) : Prop :=
  (∀ e ∈ h, Allowed e) ∧ Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead h <+: message ∧
    Silmaril.Process.LPS.Problems.GnuSha256sum.out h <+:
      Silmaril.Process.LPS.Problems.GnuSha256sum.expected message ∧
    (Silmaril.Process.LPS.Problems.GnuSha256sum.out h = [] ∨
      Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead h = message)

theorem OkH.ok {message : List Byte} {h : List Ev} (hh : OkH message h) {x : XState}
    (hf : x.faulted = false) (k : KState) : Ok message ⟨x, k, none⟩ h :=
  ⟨rfl, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, hf⟩

theorem OkH.of_ok {message : List Byte} {g : GS} {h : List Ev} (ok : Ok message g h) :
    OkH message h :=
  ⟨ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1⟩

/-- The retiring step of a listed instruction. -/
theorem retStep_instr {s : XState} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    {i : X86.Ext8.Instr} {n : Nat} (hl : Lift.instrAt s.core.rip.toNat = some (i, n))
    {c : Silmaril.X86.State} {m : Memory} (hx : X86.Ext8.exec i s.core s.memory n = .ok c m) :
    retStep s = some { s with core := c, memory := m } := by
  have e := Lift.instrAt_ok hl
  have hstep := hc.step e.inText rfl e.notSyscall e.decode e.pos e.le
  rw [hx] at hstep
  simp [retStep, hf, hstep, Silmaril.Process.CLI.X86Linux.execResult]

/-- **One instruction of a `Leads` goal**, retiring. -/
theorem leads_instr' {w : World} {message : List Byte} {Post : GS → List Ev → Prop} {k : KState}
    {h : List Ev} {x : XState} (hh : OkH message h) (hf : x.faulted = false)
    (hc : Lift.Code x.memory) {addr : Nat} (hrip : x.core.rip = BitVec.ofNat 64 addr)
    {i : X86.Ext8.Instr} {n : Nat} (hl : Lift.instrAt addr = some (i, n))
    (hn : match X86.Ext8.exec i x.core x.memory n with
      | .ok c m => Lift.Code m →
          Leads (GStep w) (Ok message) Post ⟨({ x with core := c, memory := m } : XState), k, none⟩ h
      | _ => False) :
    Leads (GStep w) (Ok message) Post ⟨x, k, none⟩ h := by
  have e := Lift.instrAt_ok hl
  have hb : addr < 2 ^ 64 := by
    have := e.inText.2; unfold Lift.textBase Lift.textSize Silmaril.X86.maxInstrLength at this
    omega
  have hl' : Lift.instrAt x.core.rip.toNat = some (i, n) := by
    rw [hrip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]; exact hl
  cases hx : X86.Ext8.exec i x.core x.memory n with
  | ok c m =>
    rw [hx] at hn
    have hs := retStep_instr hf hc hl' hx
    exact leads_seq (g := ⟨x, k, none⟩) ⟨1, by simp [hs]⟩ rfl (hh.ok hf k)
      (hn (hc.of_ro (X86.Ext8.exec8_ro hx)))
  | _ => rw [hx] at hn; exact hn.elim

/-- **The `syscall` of `sc3` as a `Leads` step.** -/
theorem leadsX_call {w : World} {message : List Byte} {Post : GS → List Ev → Prop} {k : KState}
    {h : List Ev} {x : XState} {c : Call} (hh : OkH message h) (hf : x.faulted = false)
    (hc : Lift.Code x.memory) (hrip : x.core.rip = 0x40101c#64)
    (decoded : decode { x.core with rip := 0x40101e#64 } x.memory = some (.call c))
    (buf : ReadBuf { x.core with rip := 0x40101e#64 } x.memory c)
    (answers : ∃ r k', WorldStep w k c r k')
    (next : ∀ (r : Ret) (k' : KState) (r11 : Silmaril.X86.Word), WorldStep w k c r k' →
      Leads (GStep w) (Ok message) Post
        ⟨resume (fun _ => r11) x { x.core with rip := 0x40101e#64 } c r, k', none⟩
        (h ++ [.sys c r])) :
    Leads (GStep w) (Ok message) Post ⟨x, k, none⟩ h := by
  have e : ({ x.core with rip := x.core.rip + 2 } : Core) = { x.core with rip := 0x40101e#64 } := by
    rw [hrip]; rfl
  refine leads_call (g := ⟨x, k, none⟩) (trap_sc3 hc hrip) rfl hf (hh.ok hf k) ?_ ?_ answers ?_
  · simp only [Silmaril.Process.LPS.Problems.GnuSha256sum.trapped]; rw [e]; exact decoded
  · simp only [Silmaril.Process.LPS.Problems.GnuSha256sum.trapped]; rw [e]; exact buf
  · simp only [Silmaril.Process.LPS.Problems.GnuSha256sum.trapped]; rw [e]; exact next

/-- **`exit_group(0)` at the `syscall` of `sc3`** reaches `Done`. -/
theorem leadsX_exit {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    {n : Nat} (hh : OkH message h) (hf : x.faulted = false) (hc : Lift.Code x.memory)
    (hrip : x.core.rip = 0x40101c#64)
    (decoded : decode { x.core with rip := 0x40101e#64 } x.memory = some (.exit n))
    (zero : n % 256 = 0)
    (read : Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead h = message)
    (written : Silmaril.Process.LPS.Problems.GnuSha256sum.out h =
      Silmaril.Process.LPS.Problems.GnuSha256sum.expected message) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  have e : ({ x.core with rip := x.core.rip + 2 } : Core) = { x.core with rip := 0x40101e#64 } := by
    rw [hrip]; rfl
  refine leads_exit (g := ⟨x, k, none⟩) (trap_sc3 hc hrip) rfl hf (hh.ok hf k) ?_ zero hh.1 read
    written
  simp only [Silmaril.Process.LPS.Problems.GnuSha256sum.trapped]; rw [e]; exact decoded

/-- The kernel's replies to `close(fd)` of an open descriptor. -/
theorem close_inv {w : World} {k : KState} {fd : Nat} {src : Src} (hfd : k.fds fd = some src)
    {r : Ret} {k' : KState} (h : WorldStep w k (.close fd) r k') :
    r = .ok 0 ∧ k' = k.set fd none := by
  cases h with
  | closeOk _ => exact ⟨rfl, rfl⟩
  | closeBad hb => rw [hfd] at hb; cases hb

/-- The resumed state after a reply that is not a `read`'s data. -/
theorem resume_close (r11 : Silmaril.X86.Word) (x : XState) (c : Core) (fd : Nat) (r : Ret) :
    resume (fun _ => r11) x c (.close fd) r = { x with core := returnCore (fun _ => r11) c (raxOf r) } :=
  rfl

/-- `OkH` after a `close` of a standard descriptor. -/
theorem OkH.close {message : List Byte} {h : List Ev} (hh : OkH message h) {fd : Nat} (hfd : fd ≤ 2)
    (r : Ret) : OkH message (h ++ [.sys (.close fd) r]) := by
  obtain ⟨ha, hi, ho, hr⟩ := hh
  have hi' : Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead (h ++ [.sys (.close fd) r]) =
      Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead h := by
    simp [Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead, List.flatMap_append,
      Silmaril.Process.LPS.Problems.GnuSha256sum.readBytes]
  have ho' : Silmaril.Process.LPS.Problems.GnuSha256sum.out (h ++ [.sys (.close fd) r]) =
      Silmaril.Process.LPS.Problems.GnuSha256sum.out h := by
    simp [Silmaril.Process.LPS.Problems.GnuSha256sum.out, List.flatMap_append,
      Silmaril.Process.LPS.Problems.GnuSha256sum.outBytes]
  refine ⟨fun e he => ?_, hi' ▸ hi, ho' ▸ ho, hi' ▸ ho' ▸ hr⟩
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · simp only [List.mem_singleton] at he; subst he; exact hfd

end Silmaril.Apps.Sha256sum.Stdout

/-- One retiring instruction of a `Leads` goal over `⟨x, k, none⟩`: `leads_instr'`, `x86_simp`,
`rmem`. -/
syntax "lstep" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| lstep) => `(tactic| lstep [Bool.false_eq_true])
  | `(tactic| lstep [$ls,*]) => `(tactic|
      (refine Silmaril.Apps.Sha256sum.Stdout.leads_instr' (by assumption) (by assumption)
          (by assumption) (by first | assumption | rfl) (by rfl) ?_
       x86_simp [$ls,*, Bool.false_eq_true, Silmaril.X86.popWord, Option.bind_eq_bind,
         Option.bind_some, Option.pure_def, Silmaril.X86.wordOfBytes?_encodeWords,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub, Silmaril.Apps.Sha256sum.Stdout.bv_sub_add,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero, Nat.reduceMul, BitVec.and_self,
         Silmaril.X86.SegVC.eval_logic_e, Silmaril.X86.SegVC.eval_logic_ne,
         Silmaril.X86.SegVC.eval_logic_s, Silmaril.X86.SegVC.eval_logic_ns,
         Silmaril.X86.SegVC.eval_sub_8, Silmaril.X86.SegVC.eval_sub_32,
         Silmaril.X86.SegVC.eval_sub_64, Silmaril.X86.Ext.Cond.afterCmp,
         Silmaril.X86.Ext.AluOp.flagsN]
       try dsimp only [Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.Sz.bytes]
       try x86_simp [$ls,*, Bool.false_eq_true, Silmaril.X86.popWord, Option.bind_eq_bind,
         Option.bind_some, Option.pure_def, Silmaril.X86.wordOfBytes?_encodeWords,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub, Silmaril.Apps.Sha256sum.Stdout.bv_sub_add,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero, Nat.reduceMul, BitVec.and_self,
         Silmaril.X86.SegVC.eval_logic_e, Silmaril.X86.SegVC.eval_logic_ne,
         Silmaril.X86.SegVC.eval_logic_s, Silmaril.X86.SegVC.eval_logic_ns,
         Silmaril.X86.SegVC.eval_sub_8, Silmaril.X86.SegVC.eval_sub_32,
         Silmaril.X86.SegVC.eval_sub_64, Silmaril.X86.Ext.Cond.afterCmp,
         Silmaril.X86.Ext.AluOp.flagsN]
       repeat rmem [$ls,*]
       try intro))
