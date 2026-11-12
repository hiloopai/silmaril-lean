-- variant-of: glibc.cat-stdin.gcc | style: stdexe-at-main | see-also: Silmaril.Raw.Elf.Link.Dyn.Program.Examples.CatStdin
module

public import Silmaril.Elf.Link.Dyn.Program.StdExe.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Program.Examples.CatStdin

/-! # `cat` on stdin (`gcc -O2`) as a standard executable

The binary, specification and loop invariant of `Program.Examples.CatStdin` (`catStdinGcc`,
`catSpec`, `CatInv`), stated as a `StdExe` and proved from `main`'s first instruction:
`at_main` replaces the entry boilerplate (the intros, the facts, the guard word and the initial
frame bundle) and `main_returns` the return continuation's side conditions. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.Elf.Link.Dyn Silmaril.Elf.Link.Dyn.Program Silmaril.Elf.Link.Dyn.Proc
open Silmaril.X86.Ext (loadN)

/-- `cat-stdin-gcc` as a standard executable. -/
def catStdinGccStd : StdExe where
  bin := catStdinGcc
  sha256 := "98c62b5eeff52a6eb92dbe516de907c6f25fcad121788c2fed68c206ebba8759"
  spec := catSpec
  tier := Tier.stdinOnly

theorem catStdinGccStd_ok : catStdinGccStd.ok = true := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem catStdinGccStd_verified : catStdinGccStd.Verified := by
  at_main catStdinGccStd_ok
  -- the prologue block: push rbx, the guard into the canary slot, buf = rsp, jump to the loop
  mblock hg0
  on_goal 2 => exact ⟨guard, by mkept⟩
  mloadK hg0
  mname u0 hu0
  have K : Frm catStdinGcc (world catStdinGcc S w b lb gate (!w.stdoutFull) args fs) b lb t (catFL t guard)
      (catKL fs guard) u0.m.memory := by rw [hu0]; mstores K
  have O : Streams.StdoutIs S.E u0.m.memory (outSt 1) := by rw [hu0]; mstdout hstdout
  mloop (CatInv (world catStdinGcc S w b lb gate (!w.stdoutFull) args fs) S w b lb fs guard t)
  case init =>
    exact ⟨by mregs, by mfind, by mregs, by mregs, by mregs, K, ⟨outSt 1, O, rfl⟩, by mregs, by mregs,
      by mregs, by mregs; rw [entry.inp]⟩
  case body =>
    intro u ⟨hripu, hdu, hrspu, hrbxu, hfsu, Ku, ⟨st0, hst0, hbuf0⟩, hju, hau, heu, hio⟩
    -- read (0, buf, 1024)
    mblock
    mcallN u1
    · intro a h1 h2
      mnorm at h1 h2
      refine ⟨fun hp => ?_, (hroom.2.2 a (by omega) (by omega)).2.2⟩
      have := S.E.S.priv_lo _ a hp; omega
    rintro v ⟨kk, hk1, hk2, hk0, hlib, hoth, hrd, hgv, hrax⟩
    mregs at hk1 hk2 hk0 hlib hrd hgv hrax
    mret hlib
    have hstv := StdoutIs.call hoth (by simp) hst0 (by mnat)
    have hdv : v.g.done = none := by rw [hgv]; exact hdu
    mbranch hc
    · -- `read` returned 0: the end of the input; return 0
      rw [BitVec.setWidth_eq, hrax, cond_g_test _ (by rw [BitVec.msb_eq_decide]; simp; omega)] at hc
      have hk : kk = 0 := by
        simp at hc
        have := congrArg BitVec.toNat hc; simp at this; omega
      subst hk
      mcanary
      mblock
      all_goals try exact ⟨_, by mslot⟩
      mexit
      main_returns
      · obtain ⟨d, hd⟩ := hw.2.2
        have hinp : u.g.inp = [] := hk0.1 rfl
        refine ⟨st0, hstv, ?_⟩
        mregs
        rw [hbuf0, List.append_nil, ← List.append_nil u.g.out, ← hinp, ← hio]
        simp [catSpec, stdinBytes, hd]
      · mregs; rw [heu]; simp [catSpec, Streams.ofSpec]
      · simp [Silmaril.Elf.Link.Dyn.Proc.low32, catSpec]
    · -- `read` returned `kk > 0` bytes: write (1, buf, kk)
      rw [BitVec.setWidth_eq, hrax, cond_g_test _ (by rw [BitVec.msb_eq_decide]; simp; omega)] at hc
      have hk : kk ≠ 0 := by
        simp at hc; intro h; subst h; simp at hc
      have hrel : (world0 catStdinGcc b lb gate (!w.stdoutFull) args (libWords catStdinGcc lb fs)).reliable =
          true := by simp only [world0]; rw [hw.1]; rfl
      mblock
      mcallN u2
      · mregs
        exact ⟨u.g.inp.take kk, readBytes_push_of hrd (by mnat) (by mnat)⟩
      rintro v2 ⟨hlib2, hoth2, hw2⟩
      mregs at hlib2 hw2
      obtain ⟨hg2, -⟩ := hw2 (u.g.inp.take kk) (readBytes_push_of hrd (by mnat) (by mnat))
      have hg2' := (hg2 hrel).1
      mret hlib2
      have hstv2 := StdoutIs.call hoth2 (by simp) hstv (by mnat)
      mnext
      · exact ⟨by mregs, by mregs; exact hdu, by mregs, by mregs, by mregs, by mfind, ⟨st0, hstv2, hbuf0⟩,
          by mregs; exact hju, by mregs; exact hau, by mregs; exact heu, by mregs; rw [hio]; simp⟩
      · mregs; simp; omega

end Silmaril.Elf.Link.Dyn.Program.Examples
