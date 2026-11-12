-- variant-of: glibc.adder.gcc | style: stdexe-at-main | see-also: Silmaril.Raw.Elf.Link.Dyn.Small.AdderGccMain
module

public import Silmaril.Elf.Link.Dyn.Program.StdExe.Thms
public import Silmaril.Elf.Link.Dyn.Program.StdExe.Bins.AdderGcc
public import Silmaril.Elf.Link.Dyn.Program.StdExe.Bins.Glibc
public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangMain

/-! # The adder (`gcc -O2`) as a standard executable

`examples/dyn/adder/adder.c`: `if (scanf ("%d %d", &a, &b) != 2) return 1; printf ("%d\n", a + b);
return 0;` (gcc: `__printf_chk`, the stack protector). Against the formatted-I/O table
`libStdio` and the glibc pin `glibc239Stdio`, on stdin worlds where `scanf` is defined and the sum
is an `int`. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.Elf.Link.Dyn Silmaril.Elf.Link.Dyn.Program Silmaril.Elf.Link.Dyn.Proc
open Silmaril.X86.Ext (loadN)

/-- What the adder does: the sum of the two integers it reads, or status 1. -/
def adderSpec : Spec := fun w =>
  match Stdio.scanDD (stdinBytes w) with
  | .ok a b _ => { stdout := Streams.toSpec (Stdio.decStr (a + b) ++ [10]), stderr := [], status := 0 }
  | _ => { stdout := [], stderr := [], status := 1 }

/-- The adder's worlds: no operands, stdin a byte stream on which `scanf ("%d %d")` is defined,
and the sum is an `int`. -/
def Tier.adder : Tier := fun w => Tier.stdinOnly w ∧ Stdio.scanDD (stdinBytes w) ≠ .ub ∧
  ∀ a b r, Stdio.scanDD (stdinBytes w) = .ok a b r → Stdio.inInt32 (a + b) = true

/-- `adder-gcc` as a standard executable. -/
def adderGccStd : StdExe where
  bin := adderGccP
  sha256 := "f327e359e02f7de29329351cb48e55b3c3cccdfc7d45f5148ee0adbe742d5952"
  glibc := glibc239Stdio
  spec := adderSpec
  tier := Tier.adder
  L := libStdio

theorem adderGccStd_ok : adderGccStd.ok = true := by decide +kernel

/-- What `scanf` converted is an `int`. -/
theorem scanDD_ok_range {inp : List Silmaril.X86.Byte} {a b : Int} {r : List Silmaril.X86.Byte}
    (h : Stdio.scanDD inp = .ok a b r) : Stdio.inInt32 a = true ∧ Stdio.inInt32 b = true := by
  unfold Stdio.scanDD at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h; constructor <;> assumption
        · cases h
    · cases h

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Every run of `adder-gcc` on such a stdin prints the sum and exits 0, or exits 1.** -/
theorem adderGccStd_verified : adderGccStd.Verified := by
  at_main adderGccStd_ok
  mblock hg0
  on_goal 2 => exact ⟨guard, by mkept⟩
  mloadK hg0
  mname u0 hu0
  have K : Frm adderGccP (world adderGccP S w b lb gate (!w.stdoutFull) args fs libStdio) b lb t
      [((t.m.core.read .rsp - 16#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [guard])]
      (guardKL fs guard) u0.m.memory := by rw [hu0]; mstores K
  have O : Streams.StdoutIs S.E u0.m.memory (outSt 1) := by rw [hu0]; mstdout hstdout
  have I : S.E.S.file u0.m.memory S.stdinF (stdinSt w) := by rw [hu0]; mfile entry.stdin
  mcallNE u1
  · mregs
    refine ⟨Frm.str F X (by mfind) (by mnat) (by mnat) rfl, ⟨_, file_push I (by mnat)⟩, ?_, ?_, ?_, ?_,
      Or.inl (by mnat), ?_⟩
    all_goals try exact Fr.permitted (Frm.fr (by mfind)) (Or.inr rfl) (by mnat) (by mnat) X.sp2
    all_goals try exact Fr.permitted (Frm.fr (by mfind)) (Or.inl rfl) (by mnat) (by mnat) X.sp2
    intro a ha
    mnorm at ha
    refine ⟨fun hp => ?_, (entry.stack.2.2 a (by omega) (by omega)).2.2⟩
    have := S.E.S.priv_lo _ a hp; omega
  rintro v ⟨hlib, hgv, hoth, hso, hres⟩
  have Ov := hso _ ⟨file_push O.1 (by mnat), O.2⟩
  obtain ⟨d, hd⟩ := hw.1.2.2
  have hr := hres _ (file_push I (by mnat))
  rw [show (stdinSt w).rd = stdinBytes w by simp [stdinSt, stdinBytes, hd]] at hr
  mret hlib
  mghost hgv
  cases hsc : Stdio.scanDD (stdinBytes w) with
  | ub => exact absurd hsc hw.2.1
  | fail =>
    rw [hsc] at hr
    dsimp only at hr
    mbranch hc
    · -- `scanf` did not return 2: `return 1`
      mcanary
      mblock
      main_returns
      · exact ⟨outSt 1, Ov, by mregs; simp [adderSpec, hsc, outSt, Streams.ofSpec]⟩
      · mregs; simp [adderSpec, hsc, Streams.ofSpec]
      · simp [Proc.low32, adderSpec, hsc]
    · rw [cond_e_cmp] at hc
      simp [Proc.low32] at hc hr
      exact absurd hc hr
  | ok x y rest =>
    rw [hsc] at hr
    dsimp only at hr
    obtain ⟨-, h2, hra, hrb⟩ := hr
    mregs at hra hrb
    mbranch hc
    · rw [cond_e_cmp] at hc
      simp [Proc.low32] at hc h2
      exact absurd h2 hc
    -- `printf ("%d\n", a + b)`
    mblock hb ha
    all_goals try exact ⟨_, by mregs; exact Small.loadN_of_readBytes (by assumption)⟩
    mregs at ha hb
    rw [Small.loadN_of_readBytes hra, Option.some.injEq] at ha
    rw [Small.loadN_of_readBytes hrb, Option.some.injEq] at hb
    subst ha hb
    mcallNE u2
    · mregs; exact ⟨Frm.str F X (by mfind) (by mnat) (by mnat) rfl, ⟨_, file_push Ov.1 (by mnat), Ov.2⟩⟩
    rintro v2 ⟨hlib2, hout2, hoth2, happ2⟩
    obtain ⟨st2, hst2, -, -, -, hap2⟩ := happ2 _ ⟨file_push Ov.1 (by mnat), Ov.2⟩
    mghost hout2
    mret hlib2
    mblock
    mcanary
    mblock
    main_returns
    · refine ⟨st2, hst2, ?_⟩
      rcases hap2 with ⟨h1, -⟩ | ⟨h1, -⟩
      · mregs at h1
        rw [h1]
        obtain ⟨hx, hy⟩ := scanDD_ok_range hsc
        simp only [Proc.low32, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq,
          Small.le32_val, Small.int32_add (by rw [Int.add_comm]; exact hw.2.2 _ _ _ hsc) hy hx]
        simp [adderSpec, hsc, outSt, Streams.ofSpec, Streams.toSpec, Int.add_comm, Function.comp_def]
      · simp only [world0] at h1; rw [hrel] at h1; cases h1
    · mregs; simp [adderSpec, hsc, Streams.ofSpec]; mfind
    · simp [Proc.low32, adderSpec, hsc]

end Silmaril.Elf.Link.Dyn.Program.Examples
