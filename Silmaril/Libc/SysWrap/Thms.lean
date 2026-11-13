module

public import Silmaril.Libc.SysWrap.Defs
public import Silmaril.X86.Str9K.Defs
import Silmaril.Proofs.Libc.SysWrap.Str9K

/-!
# System call wrappers: the checker is sound, the tactic, the call on `Str9K`

* `sound`: **`check w = true` implies `Spec w.code w.desc`**; `sound_code`: the same for
  `checkCode` (the layout found by decoding). Proofs: `Silmaril.Proofs.Libc.SysWrap.Sound`.
* `syscall_wrapper`: the tactic. On a goal `Spec code d` with `code` and `d` literals it is
  `exact sound_code (by decide +kernel)`: the kernel decodes the wrapper's bytes with the
  machine's own decoder (`Str9FsX.decode`), matches them against the templates and runs the
  instructions before the call symbolically. About 50 ms of kernel time per wrapper, all of it in
  the trusted kernel (no compiled evaluation).
* `str9k`: on `Str9K` (`Str9G` with Linux's memory calls, `Silmaril.X86.Sys`), the two halves
  join through the kernel's step: if the kernel model answers the request with `(r, m', k')`,
  the wrapper returns with `r`'s result, the kernel state `k'` and the answer stream advanced
  by one. The `syscall` is a boundary of `Str9G` (`step_syscall`: no layer of its fetch chain
  decodes `0F 05`).
-/

@[expose] public section

namespace Silmaril.Libc.SysWrap

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

/-- **The checker is sound.** -/
theorem sound {w : Wrapper} (h : check w = true) : Spec w.code w.desc :=
  Silmaril.Proofs.Libc.SysWrap.sound h

/-- **The checker on the code alone is sound.** -/
theorem sound_code {code : List Byte} {d : Desc} (h : checkCode code d = true) : Spec code d := by
  unfold checkCode at h
  split at h
  · exact sound (w := ⟨code, d, _, _⟩) h
  · cases h

/-- `syscall_wrapper` proves `Spec code d` for literal `code` and `d` by the kernel-evaluated
checker. -/
macro "syscall_wrapper" : tactic =>
  `(tactic| exact Silmaril.Libc.SysWrap.sound_code (by decide +kernel))

/-- A checked wrapper has its `syscall` at `d.sysOff`. -/
theorem checkCode_syscall {code : List Byte} {d : Desc} (h : checkCode code d = true) :
    (code.drop d.sysOff).take 2 = [0x0F, 0x05] ∧ d.sysOff + 2 ≤ code.length := by
  unfold checkCode at h
  split at h
  · unfold check at h
    split at h
    · cases h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h2 := h.2
      refine ⟨h2, ?_⟩
      have := congrArg List.length h2
      simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil] at this
      omega
  · cases h

/-- **The whole call on `Str9K`** (Linux's memory calls as the kernel model). -/
theorem str9k {code : List Byte} {d : Desc} (hc : checkCode code d = true)
    {A : Word} {x : Silmaril.X86.Str9K.KState} (he : Entry code d A x.s)
    {r : Word} {m' : Memory} {k' : Silmaril.X86.Sys.Kernel}
    (hcall : ∀ t, Request d A x.s t →
      Silmaril.X86.Sys.call t.x.m.core t.x.m.memory x.k (x.ans 0) = some (r, m', k'))
    {tls : Word} (hk : Kept code d A x.s m' tls) (herr : ErrnoOk code d A x.s r m' tls) :
    ∃ y, Reaches Silmaril.X86.Str9K.isa.step x y ∧ Returned d x.s r m' tls y.s ∧ y.k = k' ∧
      y.ans = fun n => x.ans (n + 1) :=
  Silmaril.Proofs.Libc.SysWrap.str9k (sound_code hc) (checkCode_syscall hc).1
    (checkCode_syscall hc).2 he hcall hk herr

end Silmaril.Libc.SysWrap
