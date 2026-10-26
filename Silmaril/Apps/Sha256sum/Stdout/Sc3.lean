module

public import Silmaril.Apps.Sha256sum.Stdout.LeadsX
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Syscalls

/-! # `sc3` calls of `close` and `exit_group` as `Leads` steps

Status: **VERIFIED** (no `sorry`, standard axioms only).

`sc3` (`0x401010`: `mov %rdi,%rax; mov %rsi,%rdi; mov %rdx,%rsi; mov %rcx,%rdx; syscall; ret`)
is the binary's only system-call stub. Entered past its first instruction (`0x401013`, `rax`
already the call number, `rsi` the first argument):

* `sc3_close`: `close(fd)` of an open standard descriptor returns `0` and continues at the
  return address, for every `r11`, with the descriptor closed and the event recorded;
* `sc3_exit`: `exit_group(0)` (`rax = 231`) reaches `Done` when the history has read the
  whole message and written exactly the answer.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word State Reg)
open Silmaril.Process (Memory Byte)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev Done decode_close decode_exit)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits

theorem out_close (h : List Ev) (fd : Nat) (r : Ret) :
    Silmaril.Process.LPS.Problems.GnuSha256sum.out (h ++ [.sys (.close fd) r]) =
      Silmaril.Process.LPS.Problems.GnuSha256sum.out h := by
  simp [Silmaril.Process.LPS.Problems.GnuSha256sum.out, List.flatMap_append,
    Silmaril.Process.LPS.Problems.GnuSha256sum.outBytes]

theorem in_close (h : List Ev) (fd : Nat) (r : Ret) :
    Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead (h ++ [.sys (.close fd) r]) =
      Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead h := by
  simp [Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead, List.flatMap_append,
    Silmaril.Process.LPS.Problems.GnuSha256sum.readBytes]

theorem fd32_small {fd : Nat} (h : fd ≤ 2) : fd32 (BitVec.ofNat 64 fd) = fd := by
  simp only [fd32]
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-- **`close(fd)` through `sc3`.** -/
theorem sc3_close {w : World} {message : List Byte} {Post : GS → List Ev → Prop} {k : KState}
    {h : List Ev} {x : XState} {fd : Nat} {src : Src} {ra : Word} (hh : OkH message h)
    (hf : x.faulted = false) (hc : Lift.Code x.memory) (hrip : x.core.rip = 0x401013#64)
    (hax : x.core.read .rax = 3#64) (hsi : x.core.read .rsi = BitVec.ofNat 64 fd) (hle : fd ≤ 2)
    (hfd : k.fds fd = some src)
    (hret : x.memory.readWith .read (x.core.read .rsp).toNat 8 = some (encodeWords [ra]))
    (K : ∀ y : XState, y.faulted = false → Lift.Code y.memory → y.memory = x.memory →
      y.core.rip = ra → y.core.read .rsp = x.core.read .rsp + 8#64 → y.core.read .rax = 0#64 →
      (∀ r : Reg, r ≠ .rax → r ≠ .rcx → r ≠ .r11 → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rsp →
        y.core.read r = x.core.read r) →
      Leads (GStep w) (Ok message) Post ⟨y, k.set fd none, none⟩ (h ++ [.sys (.close fd) (.ok 0)])) :
    Leads (GStep w) (Ok message) Post ⟨x, k, none⟩ h := by
  lstep [hrip]
  lstep
  lstep
  refine leadsX_call (c := .close fd) hh hf (by assumption) rfl ?_ trivial ⟨_, _, .closeOk hfd⟩ ?_
  · rw [decode_close _ _ (by simp [hax])]
    simp [hsi, fd32_small hle]
  · intro r k' r11 ws
    obtain ⟨rfl, rfl⟩ := close_inv hfd ws
    rw [resume_close]
    simp only [returnCore, raxOf]
    have hh' := hh.close hle (.ok 0)
    lstep [hret]
    refine K _ hf (by assumption) rfl rfl ?_ ?_ ?_
    · simp
    · simp
    · intro r h1 h2 h3 h4 h5 h6 h7
      simp [State.read_write_other, h1, h2, h3, h4, h5, h6, h7, Lift.read_mk, Lift.core_regs]

/-- **`exit_group(0)` through `sc3`.** -/
theorem sc3_exit {w : World} {message : List Byte} {k : KState} {h : List Ev} {x : XState}
    (hh : OkH message h) (hf : x.faulted = false) (hc : Lift.Code x.memory)
    (hrip : x.core.rip = 0x401013#64) (hax : x.core.read .rax = 231#64)
    (hsi : x.core.read .rsi = 0#64)
    (read : Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead h = message)
    (written : Silmaril.Process.LPS.Problems.GnuSha256sum.out h =
      Silmaril.Process.LPS.Problems.GnuSha256sum.expected message) :
    Leads (GStep w) (Ok message) (Done message) ⟨x, k, none⟩ h := by
  lstep [hrip]
  lstep
  lstep
  refine leadsX_exit (n := 0) hh hf (by assumption) rfl ?_ rfl read written
  rw [decode_exit _ _ (by simp [hax])]
  simp [hsi]

end Silmaril.Apps.Sha256sum.Stdout
