-- variant-of: glibc.cat-stdin.gcc | style: program-api | see-also: Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.CatStdin
module

public import Silmaril.Elf.Link.Dyn.Program.Examples.CatStdinGccBin
public import Silmaril.Elf.Link.Dyn.Program.Glibc
public import Silmaril.Raw.Elf.Link.Dyn.Program.Call
public import Silmaril.Raw.Elf.Link.Dyn.Program.Exec

/-! # `cat` on stdin (`gcc -O2`, glibc 2.39), verified

`examples/dyn/ladder/cat-stdin.c`: `while ((n = read (0, buf, sizeof buf)) > 0) write (1, buf, n);
return 0;` (GNU cat's own read/write loop, with gcc's stack protector). The loop is proved with
the loop rule `must_loop`, measured by the unread input, against the invariant `CatInv`. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.Elf.Link.Dyn Silmaril.Elf.Link.Dyn.Program Silmaril.Elf.Link.Dyn.Proc
open Silmaril.X86.Ext (loadN)

/-- `cat` with no operands copies its standard input. -/
def catSpec : Spec := fun w => { stdout := (match w.stdin with | .bytes d => d | .dir => []), stderr := [], status := 0 }
/-- The per-binary check. -/
theorem catStdinGcc_ok : catStdinGcc.ok libc ld = true := by decide +kernel

/-- The words `main` saves in its frame: the canary and `rbx`. -/
abbrev catFL (t : PState) (g : Silmaril.X86.Word) : List (Nat × List Silmaril.X86.Byte) :=
  [((t.m.core.read .rsp - 16#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [g]),
   ((t.m.core.read .rsp - 8#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [t.m.core.read .rbx])]

/-- The library's word `main` reads: the guard. -/
abbrev catKL (fs g : Silmaril.X86.Word) : List (Nat × List Silmaril.X86.Byte) :=
  [((fs + 40#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [g])]

/-- The loop head of `cat-stdin` (`0x10d5`): what holds before each `read`. -/
structure CatInv (W : Proc.World) (S : Std) (w : Program.World) (b lb fs g : Silmaril.X86.Word) (t u : PState) :
    Prop where
  rip : u.m.core.rip = b + BitVec.ofNat 64 (catStdinGcc.layout.main + 53)
  done : u.g.done = none
  rsp : u.m.core.read .rsp = t.m.core.read .rsp - 1048#64
  rbx : u.m.core.read .rbx = t.m.core.read .rsp - 1048#64
  fsb : u.m.core.fsBase = t.m.core.fsBase
  frm : Frm catStdinGcc W b lb t (catFL t g) (catKL fs g) u.m.memory
  out : ∃ st, Streams.StdoutIs S.E u.m.memory st ∧ st.buf = []
  jobs : u.g.jobs = t.g.jobs
  atexit : u.g.atexit = t.g.atexit
  err : u.g.err = t.g.err
  io : t.g.out ++ stdinBytes w = u.g.out ++ u.g.inp

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem catMain : MainProof catStdinGcc catSpec Tier.stdinOnly := by
  intro w hw S b lb gate args fs argv P hfs henv Q t hd hrip hal hret hroom hm hx hat hpre hrdi hrsi k _kx
  have F := Bin.facts catStdinGcc_ok
  have X := Ctx.of F P hal hroom hat
  obtain ⟨hfsb, ⟨g, hgd⟩, -⟩ := hx.2.2
  have K0 : Frm catStdinGcc _ b lb t [] (catKL fs g) t.m.memory := Frm.entry (Fr.of ⟨hm, hx.1, hx.2.2.2.2⟩ hroom hret)
    (KSlots.word hgd fun k hk => Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  -- the prologue block: push rbx, the guard into the canary slot, buf = rsp, jump to the loop
  mblock hg0
  on_goal 2 => exact ⟨g, by mkept⟩
  mloadK hg0
  mname u0 hu0
  have K : Frm catStdinGcc (world catStdinGcc S w b lb gate (!w.stdoutFull) args fs) b lb t (catFL t g)
      (catKL fs g) u0.m.memory := by rw [hu0]; mstores K0
  have O : Streams.StdoutIs S.E u0.m.memory (outSt 1) := by rw [hu0]; mstdout hat.stdout
  mloop (CatInv (world catStdinGcc S w b lb gate (!w.stdoutFull) args fs) S w b lb fs g t)
  case init =>
    exact ⟨by mregs, by mfind, by mregs, by mregs, by mregs, K, ⟨outSt 1, O, rfl⟩, by mregs, by mregs,
      by mregs, by mregs; rw [hpre.1]⟩
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
      refine k _ rfl (by mregs; exact hju) (by mregs; exact hau) (by mregs; mfind) (Fr.code (by mfind)).1
        ⟨⟨st0, hstv, ?_⟩, ?_, ?_⟩
      · obtain ⟨d, hd⟩ := hw.2.2
        have hinp : u.g.inp = [] := hk0.1 rfl
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

/-- **Every run of `cat-stdin-gcc` copies stdin to stdout and exits 0.** -/
theorem catStdinGcc_verified : Verified catStdinGcc libc ld catSpec Tier.stdinOnly :=
  verified catStdinGcc_ok libc_ok ld_ok (fun _ h => h.1) catMain

end Silmaril.Elf.Link.Dyn.Program.Examples
