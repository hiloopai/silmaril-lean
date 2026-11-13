module

public import Silmaril.Proofs.Libc.SysWrap.Sound
public import Silmaril.X86.Str9K.Thms

/-!
# System call wrappers on `Str9K`: the call through the kernel model

`step_syscall`: `Str9G` has no step on the bytes `0F 05` (`syscall`): every layer of its fetch
chain rejects them, whatever follows. So on `Str9K` (`Sys.isa Str9G.isa`) the step there is the
kernel's (`Sys.sysStep`), and `str9k` joins the two halves of `Spec` through it.
-/

@[expose] public section

namespace Silmaril.Proofs.Libc.SysWrap

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory)
open Silmaril.X86.Str9G (GState)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Libc.SysWrap

/-- **`Str9G` has no step at a `syscall`.** -/
theorem step_syscall {g : GState}
    (fetched : g.x.m.memory.fetchBytes g.x.m.core.rip.toNat 2 = some [0x0F, 0x05]) :
    Silmaril.X86.Str9G.step g = none := by
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched (by decide) (by decide) (by decide) (by decide)
  have hfn9 : Silmaril.X86.Ext9.fetchNew g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, Silmaril.X86.Str9.decodeNew_none_of_bad (by decide) more]
    rfl
  have hfs : Silmaril.X86.Str9.fetchStr g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9.fetchStr
    rw [hmore, Silmaril.X86.Str9Fs.decodeStr_none_of_strBad (by decide) more]
    rfl
  have hfn : Silmaril.X86.Str9Fs.fetchNew g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9Fs.fetchNew
    rw [hmore, Silmaril.X86.Str9FsX.str9fsNew_none (by decide) (by decide) more]
    rfl
  have hss : Silmaril.X86.Sse9.fetchSse g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Sse9.fetchSse
    rw [hmore, Silmaril.X86.Str9FsX.sse_none (by decide) more]
    rfl
  have hsd : Silmaril.X86.Str9FsX.fetchStosd g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9FsX.fetchStosd
    rw [hmore, Silmaril.X86.Str9G.stosd_none (by decide) more]
    rfl
  have hbad : Silmaril.X86.Str9G.pNew [0x0F, 0x05] = .bad := by rfl
  have hg : Silmaril.X86.Str9G.fetchNew g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9G.fetchNew Silmaril.X86.Str9G.decodeNew
    rw [hmore, Silmaril.X86.Str9G.good_pNew.bad hbad more]
    rfl
  simp only [Silmaril.X86.Str9G.step, hf8, hfn9, hfs, hfn, hss, hsd, hg]

/-- **The whole call on `Str9K`.** If the kernel model answers the request (every state that
makes it) with `(r, m', k')`, the wrapper returns with `r`'s result, the kernel state `k'` and
the answer stream advanced by one. -/
theorem str9k {code : List Byte} {d : Desc} (hs : Spec code d)
    (hsys : (code.drop d.sysOff).take 2 = [0x0F, 0x05]) (hfit : d.sysOff + 2 ≤ code.length)
    {A : Word} {x : Silmaril.X86.Str9K.KState} (he : Entry code d A x.s)
    {r : Word} {m' : Memory} {k' : Silmaril.X86.Sys.Kernel}
    (hcall : ∀ t, Request d A x.s t →
      Silmaril.X86.Sys.call t.x.m.core t.x.m.memory x.k (x.ans 0) = some (r, m', k'))
    {tls : Word} (hk : Kept code d A x.s m' tls) (herr : ErrnoOk code d A x.s r m' tls) :
    ∃ y, Reaches Silmaril.X86.Str9K.isa.step x y ∧ Returned d x.s r m' tls y.s ∧ y.k = k' ∧
      y.ans = fun n => x.ans (n + 1) := by
  obtain ⟨t, ht, hreq, hres⟩ := hs A x.s he
  obtain ⟨v, hv, hret⟩ := hres r (x.ans 0).r11 m' tls hk herr
  have r1 := Silmaril.X86.Str9K.extendsStr9G.reaches (x := x) ht
  have hfetch : t.x.m.memory.fetchBytes t.x.m.core.rip.toNat 2 = some [0x0F, 0x05] := by
    have hl : Loaded t.x.m.memory A code := by rw [hreq.mem]; exact he.loaded
    have hA : t.x.m.core.rip.toNat = A.toNat + d.sysOff := by
      rw [hreq.pc]; exact hl.toNat_add (by omega)
    rw [hA, ← hsys]; exact hl.fetchBytes_sub (by omega) hfit
  have hstep : Silmaril.X86.Str9K.isa.step { x with s := t } =
      some ⟨resume t r (x.ans 0).r11 m', k', fun n => x.ans (n + 1)⟩ := by
    simp only [Silmaril.X86.Sys.step, step_syscall hfetch,
      Silmaril.X86.Sys.sysStep, Silmaril.X86.Sys.atSyscall]
    simp only [hfetch, beq_self_eq_true, ↓reduceIte, hcall t hreq,
      Option.map_some]
    rfl
  have r3 := Silmaril.X86.Str9K.extendsStr9G.reaches
    (x := (⟨resume t r (x.ans 0).r11 m', k', fun n => x.ans (n + 1)⟩ : Silmaril.X86.Str9K.KState)) hv
  refine ⟨_, r1.trans ((Silmaril.X86.SegVC.reaches_head hstep).trans r3), hret, rfl, rfl⟩

end Silmaril.Proofs.Libc.SysWrap
