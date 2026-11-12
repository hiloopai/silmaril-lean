module

public import Silmaril.Elf.Link.Dyn.Program.Examples.CatFileGccBin
public import Silmaril.Elf.Link.Dyn.Program.Glibc
public import Silmaril.Raw.Elf.Link.Dyn.Program.Call
public import Silmaril.Raw.Elf.Link.Dyn.Program.Exec

/-! # `cat FILE` (`gcc -O2`, glibc 2.39), verified

`examples/dyn/ladder/cat-file.c`: with exactly one operand, `fopen` it; on failure
`error (1, errno, "%s", name)`; otherwise copy it to stdout with `fread`/`fwrite` and `fclose` it.
The program does not check `ferror`, so a read error ends the copy silently with status 0.

`catFileGcc_main` is `main`'s proof: the prologue, the argument count, `fopen`, the failure
path through `__errno_location` and `error` (which ends the process: `MainOk`'s exit
continuation), the `fread`/`fwrite` loop by the indexed loop rule (`mloopN`, measured by the
stream's unread bytes, invariant `CatFileInv`), `fclose`, the stack-protector check. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program.Examples

open Silmaril.Elf.Link.Dyn Silmaril.Elf.Link.Dyn.Program

/-- What `cat-file` does: one operand is copied (up to a read error), a failed open is reported
as `argv[0]: NAME: strerror` with status 1, any other argument count exits 2. -/
def catFileSpec : Spec := fun w =>
  match w.argv with
  | [a0, name] =>
    match w.fs name with
    | .ok d => { stdout := d, stderr := [], status := 0 }
    | .readErr _ pre => { stdout := pre, stderr := [], status := 0 }
    | .openErr e =>
      ⟨[], a0 ++ lit ": " ++ name ++ lit ": " ++ lit e.text ++ [10], 1⟩
  | _ => { stdout := [], stderr := [], status := 2 }

/-- The per-binary check. -/
theorem catFileGcc_ok : catFileGcc.ok libc ld = true := by decide +kernel

/-- The words `main` saves in its frame: the canary, `rbx`, `rbp`, `r12`. -/
abbrev catFileFL (t : Proc.PState) (g : Silmaril.X86.Word) : List (Nat × List Silmaril.X86.Byte) :=
  [((t.m.core.read .rsp - 32#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [g]),
   ((t.m.core.read .rsp - 24#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [t.m.core.read .rbx]),
   ((t.m.core.read .rsp - 16#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [t.m.core.read .rbp]),
   ((t.m.core.read .rsp - 8#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [t.m.core.read .r12])]

/-- The words the library keeps that `main` reads: the guard, `stdout`'s copy, `argv[1]`. -/
abbrev catFileKL (fs b argv p o g : Silmaril.X86.Word) (name : Silmaril.Apps.Sha256sum.Bytes) :
    List (Nat × List Silmaril.X86.Byte) :=
  [((fs + 40#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [g]),
   ((b + 16400#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [o]),
   ((argv + 8#64).toNat, Silmaril.Machine.LittleEndian.encodeWords [p]),
   (p.toNat, Streams.ofSpec name ++ [0])]

/-- The loop head of `cat-file` (`0x11a4`, before `fread`), at index `n` (the unread bytes of the
file): the frame, the stream `f` with `n` bytes unread, and everything handed to `stdout` so far
followed by the unread bytes is the file's contents `c`. -/
structure CatFileInv (W : Proc.World) (S : Std) (b lb f : Silmaril.X86.Word) (c : List Silmaril.X86.Byte)
    (FL KL : List (Nat × List Silmaril.X86.Byte)) (t : Proc.PState) (n : Nat) (s : Proc.PState) : Prop where
  rip : s.m.core.rip = b + BitVec.ofNat 64 (catFileGcc.layout.main + 132)
  done : s.g.done = none
  rsp : s.m.core.read .rsp = t.m.core.read .rsp - 1064#64
  rbx : s.m.core.read .rbx = t.m.core.read .rsp - 1064#64
  rbp : s.m.core.read .rbp = f
  fsb : s.m.core.fsBase = t.m.core.fsBase
  frm : Frm catFileGcc W b lb t FL KL s.m.memory
  file : ∃ st, S.E.S.file s.m.memory f st ∧ st.rd.length = n ∧ st.fd ≠ 1 ∧
    ∃ so, Streams.StdoutIs S.E s.m.memory so ∧ s.g.out ++ so.buf ++ st.rd = t.g.out ++ c
  jobs : s.g.jobs = t.g.jobs
  atexit : s.g.atexit = t.g.atexit
  err : s.g.err = t.g.err

open Silmaril.Elf.Link.Dyn.Proc in
open Silmaril.X86.Ext (loadN) in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `main` of `cat-file-gcc` meets `catFileSpec` on one operand when allocations succeed within the
library's bounds (`Std.allocates`: one stream may be open, files fit `maxFile`). -/
theorem catFileGcc_main : MainProof catFileGcc catFileSpec (Tier.operands 1) lib Std.allocates := by
  intro w hw S b lb gate args fs argv P hfs henv Q t hd hrip hal hret hroom hm hx hat hpre hrdi hrsi k kx
  have F := Bin.facts catFileGcc_ok
  have X := Ctx.of F P hal hroom hat
  have hb := P.hb
  obtain ⟨hfsb, ⟨g, hgd⟩, -⟩ := hx.2.2
  obtain ⟨hrel, hlen, -⟩ := hw
  obtain ⟨a0, name, hA⟩ : ∃ a0 name, w.argv = [a0, name] := by
    match h : w.argv, hlen with
    | [a0, name], _ => exact ⟨a0, name, rfl⟩
  -- the library's words `main` reads: the guard, `stdout`'s copy, `argv[1]` and its string
  obtain ⟨p, hcp, K1⟩ := hx.2.1.kslots (i := 1) (by simp [hA])
  simp only [hA, List.getElem_cons_succ, List.getElem_cons_zero] at hcp K1
  have hvar := hat.vars ⟨nm "stdout", 0x4010, 0x0, true⟩ (by simp [catFileGcc])
  simp only [Var.addr, ↓reduceIte] at hvar
  rw [ite_eq_right_of_eq_false _ _ (by decide)] at hvar
  have hsz : catFileGcc.layout.size = 0x4020 := rfl
  have e4010 : (b + 16400#64).toNat = b.toNat + 16400 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt] <;> simp; omega
  have K0 : Frm catFileGcc _ b lb t [] (catFileKL fs b argv p S.E.stdoutF g name) t.m.memory :=
    Frm.entry (Fr.of ⟨hm, hx.1, hx.2.2.2.2⟩ hroom hret)
      (((KSlots.word hgd fun k hk => Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))).append
        (KSlots.word hvar fun k hk => Or.inl ⟨by simp [world, world0]; omega,
          by simp [world, world0]; omega⟩)).append K1)
  -- the prologue: push r12, rbp, rbx, the guard into the canary slot; argc = 2
  mbranch hg0 hc0
  all_goals try exact ⟨g, by mkept K0⟩
  all_goals mloadK hg0 K0
  · simp only [Silmaril.X86.Ext.AluOp.flagsN, eval_e_sub, hrdi, hA] at hc0
    simp at hc0
  mname u0 hu0
  have K : Frm catFileGcc (world catFileGcc S w b lb gate (!w.stdoutFull) args fs) b lb t (catFileFL t g) (catFileKL fs b argv p S.E.stdoutF g name) u0.m.memory := by
    rw [hu0]; mstores K0
  have O : Streams.StdoutIs S.E u0.m.memory (outSt 1) := by rw [hu0]; mstdout hat.stdout
  clear hu0
  -- fopen (argv[1], "r")
  mblock hp0
  on_goal 2 => exact ⟨p, by mkept K⟩
  mloadK hp0 K
  mcallNE u
  · mregs
    exact ⟨⟨_, K.cstrK hroom (by mnat) (by mnat) (by mmem) hcp.1⟩, K.str F X (by mnat) (by mnat) rfl⟩
  rintro v ⟨⟨hlib, hgv, hoth, hres⟩, herrv, hres2⟩
  generalize v.g.files = nf at hgv
  mregs at hres hres2 hgv herrv
  have h1 := hres _ (K.cstrK hroom (by mnat) (by mnat) (by mmem) hcp.1)
  rw [hfs, toSpec_ofSpec] at h1
  -- `fopen` writes only its new stream, far below the stack and apart from the kept words
  mretK hlib (by
    intro x ⟨hnz, hx⟩
    cases hfn : w.fs name with
    | openErr e => simp only [hfn, Streams.openedSt] at h1; exact absurd h1.1 hnz
    | ok d =>
      simp only [hfn, Streams.openedSt] at h1
      rcases h1 with ⟨h0, -⟩ | ⟨fd, -, -, -, -, -, hfoot, -⟩
      · exact absurd h0 hnz
      · have h2 := hfoot x hx
        refine ⟨h2.1, ?_⟩
        have h3 := h2.2.1
        mnat at h3 ⊢
    | readErr e d =>
      simp only [hfn, Streams.openedSt] at h1
      rcases h1 with ⟨h0, -⟩ | ⟨fd, -, -, -, -, -, hfoot, -⟩
      · exact absurd h0 hnz
      · have h2 := hfoot x hx
        refine ⟨h2.1, ?_⟩
        have h3 := h2.2.1
        mnat at h3 ⊢)
  have Ov := StdoutIs.call hoth (by simp) O (by mnat)
  have hdv : v.g.done = none := by rw [hgv]; mfind
  -- the open succeeded: copy the stream
  have succ : ∀ (st0 : Streams.St) (c : Silmaril.Apps.Sha256sum.Bytes), (catFileSpec w).stdout = c →
      (catFileSpec w).stderr = [] → (catFileSpec w).status = 0 →
      st0.rd = Streams.ofSpec c → ∀ fd, S.E.S.file v.m.memory (v.m.core.read .rax) { st0 with fd := fd } →
      v.m.core.read .rax ≠ 0#64 → 3 ≤ fd → v.m.core.read .rax ≠ S.E.stdoutF →
      MustQ (world catFileGcc S w b lb gate (!w.stdoutFull) args fs) Q v := by
    intro st0 c hc hce hcs hrdc fd hf hne hfd3 hfo
    mbranch hnz
    · rw [BitVec.setWidth_eq, cond_ne_test] at hnz; simp [hne] at hnz
    mloopN (CatFileInv (world catFileGcc S w b lb gate (!w.stdoutFull) args fs) S b lb (v.m.core.read .rax)
      (Streams.ofSpec c) (catFileFL t g) (catFileKL fs b argv p S.E.stdoutF g name) t) st0.rd.length
    case init =>
      refine ⟨rfl, by mfind, by mregs, by mregs, by mregs, by mregs, by mfind,
        ⟨{ st0 with fd := fd }, hf, rfl, by simp only; omega, outSt 1, Ov, ?_⟩, ?_, ?_, ?_⟩
      all_goals mregs
      simp [outSt, hrdc]
    case body =>
      intro n s ⟨hrip, hd, hrsp, hrbx, hrbp, hfsb', K, ⟨st, hst, hlen, hfd1, so, hso, hout⟩, hjs, hats, hers⟩
      -- fread (buf, 1, 1024, f)
      mblock
      mcallNE s1
      · mregs
        refine ⟨⟨_, file_push hst (by mnat)⟩, K.fr.permitted (Or.inr rfl) (by mnat) (by mnat) X.sp2,
          by decide, K.fr.permitted (Or.inl rfl) (by mnat) (by mnat) X.sp2, fun a h1 h2 hp => ?_, by mnat⟩
        have := S.E.S.priv_lo _ a hp; mnorm at h1 h2; omega
      rintro v1 ⟨hrd, -⟩
      obtain ⟨d, st', htake, hrd', hfd', hdl, hlib1, hg1, hoth1, hf1, hbuf, hrax1⟩ :=
        fread_did hrd (by mregs; exact file_push hst (by mnat))
      mregs at htake hrd' hdl hlib1 hg1 hoth1 hf1 hbuf hrax1
      mret hlib1
      have O1 := StdoutIs.call hoth1 (by simp only [List.mem_singleton]; exact fun h => hfo h.symm) hso (by mnat)
      have hd1 : v1.g.done = none := by mregs; mfind
      mbranch hnz
      · -- `fread` returned 0: the end of the file; fclose (f)
        rw [BitVec.setWidth_eq, cond_ne_test, hrax1] at hnz
        have hd0 : d = [] := by
          simp at hnz
          have h := congrArg BitVec.toNat hnz
          simp at h
          exact List.eq_nil_of_length_eq_zero (by omega)
        have hrd0 : st.rd = [] := by
          have := htake; rw [hd0] at this
          rcases hst0 : st.rd with _ | ⟨x, l⟩
          · rfl
          · rw [hst0] at this; simp at this
        mblock
        mcallNE s3
        · mregs; exact ⟨_, file_push hf1 (by mnat)⟩
        rintro v3 ⟨⟨hlib3, hj3, ha3, hdn3, -, he3, -, -, -, hoth3, hcl⟩, -⟩
        mregs at hcl hj3 ha3 he3
        mret hlib3
        have hout3 := ((hcl st' (file_push hf1 (by mnat))).2 (by rw [hfd']; exact hfd1)).1
        have O3 := StdoutIs.call hoth3 (by simp only [List.mem_singleton]; mregs; exact fun h => hfo h.symm)
          O1 (by mnat)
        -- return 0: the canary check, the epilogue
        mblock
        mcanary
        mblock
        all_goals try exact ⟨_, by mslot⟩
        mexit
        refine k _ rfl (by rw [hj3]; exact hjs) (by rw [ha3]; exact hats) hdn3 (Fr.code (by mfind)).1
          ⟨⟨so, O3, ?_⟩, ?_, ?_⟩
        · rw [hout3, hc, ← hout, hrd0, List.append_nil]
        · rw [he3, hers, hce]; simp [Streams.ofSpec]
        · rw [hcs]; simp [low32]
      · -- `fread` returned `d`: fwrite (buf, 1, d, stdout)
        rw [BitVec.setWidth_eq, cond_ne_test, hrax1] at hnz
        have hdpos : 0 < d.length := by
          simp at hnz
          rcases Nat.eq_zero_or_pos d.length with h | h
          · rw [h] at hnz; simp at hnz
          · exact h
        have h4010 : catFileGcc.layout.main + 112 + 11904 = 16400 := rfl
        mblock hso1
        on_goal 2 => exact ⟨_, by rw [h4010]; mkept⟩
        rw [h4010] at hso1
        mloadK hso1
        mcallNE s2
        · mregs
          exact ⟨by simp, ⟨so, file_push O1.1 (by mnat), O1.2⟩, d, readBytes_push_of hbuf (by mnat) (by mnat)⟩
        rintro v2 ⟨⟨hlib2, ⟨hj2, ha2, hdn2, -, he2, -, -, -⟩, hoth2, happ⟩, -⟩
        mregs at happ hj2 ha2 he2
        mret hlib2
        obtain ⟨happ2, -⟩ := happ d (readBytes_push_of hbuf (by mnat) (by mnat))
        have hrel' : (world0 catFileGcc b lb gate (!w.stdoutFull) args (libWords catFileGcc lb fs)).reliable = true := by
          simp only [world0]; rw [hrel]; rfl
        obtain ⟨so', hso', -, -, -, hout' | ⟨hf, -⟩⟩ := happ2 so ⟨file_push O1.1 (by mnat), O1.2⟩
        swap
        · rw [hrel'] at hf; cases hf
        have hf2 := file_call hoth2 (by simp only [List.mem_singleton]; exact hfo) hf1 (by mnat)
        have hne' : st.rd ≠ [] := by
          intro h; have := htake; rw [h] at this; rw [this] at hdpos; simp at hdpos
        mnextN st'.rd.length
        · rw [hrd', List.length_drop, ← hlen]
          have := List.length_pos_iff.2 hne'
          omega
        refine ⟨by mregs, hdn2, by mregs, by mregs, by mregs, by mregs, by mfind,
          ⟨st', hf2, rfl, by rw [hfd']; exact hfd1, so', hso', ?_⟩, by rw [hj2]; exact hjs,
          by rw [ha2]; exact hats, by rw [he2]; exact hers⟩
        rw [hout'.1]; mregs
        rw [← hout, htake, hrd']
        simp only [List.append_assoc, List.take_append_drop]
  cases hfn : w.fs name with
  | openErr e =>
    simp only [hfn, Streams.openedSt] at h1
    have herr := hres2 _ (K.cstrK hroom (by mnat) (by mnat) (by mmem) hcp.1) e (by rw [hfs, toSpec_ofSpec, hfn])
    mbranch hz
    swap
    · rw [BitVec.setWidth_eq, cond_ne_test, h1.1] at hz; simp at hz
    -- the open failed: `error (1, errno, "%s", argv[1])`
    mblock
    mcallN u2
    rintro v2 ⟨hlib2, hgv2, hoth2, hrax2, herr2⟩
    mret hlib2
    have Ov2 := StdoutIs.call hoth2 (by simp) Ov (by mnat)
    have herrv2 := herr2.1 e (errno_push herr hat.errno (by mnat))
    have hdv2 : v2.g.done = none := by mregs; mfind
    mblock hp2 he2
    on_goal 3 => exact ⟨p, by mkept⟩
    on_goal 2 => exact ⟨_, herrv2.1⟩
    mloadK hp2
    have e := (Option.some.inj (he2.symm.trans (by mregs; exact herrv2.1))).symm; subst e
    have hcode : (low32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (Streams.errnoCode e))))).toNat =
        Streams.errnoCode e := by
      simp only [low32]; cases e <;> rfl
    mcallNE s4
    · mregs
      exact ⟨Frm.str F X (by mfind) (n := 0x2006) (by mnat) (by mnat) rfl,
        ⟨Streams.ofSpec name, Frm.cstrK (by mfind) hroom (by mnat) (by mnat) (by mmem) hcp.1⟩, ⟨e, hcode⟩⟩
    intro v3 h3
    have h3' := h3 (Streams.ofSpec name) e
      (by mregs; exact Frm.cstrK (by mfind) hroom (by mnat) (by mnat) (by mmem) hcp.1) (by mregs; exact hcode)
    mregs at h3'
    rw [ite_eq_right_of_eq_false _ _ (by decide)] at h3'
    obtain ⟨pend, hpend, ⟨hrip3, hk3, -⟩, hg3⟩ := h3'
    have hp0 : pend = [] := hpend _ ⟨by mregs; exact file_push Ov2.1 (by mnat), rfl⟩
    refine kx v3 1#64 hrip3 (by rw [hg3]) (by rw [hg3])
      (by rw [hg3]; mregs; mfind)
      ((Fr.push F X (by mfind) (by mnat) (by mnat)).code.keep F hb (Proc.keeps_img hk3)).1 ⟨?_, ?_, ?_⟩
    · rw [hg3]; simp [hp0, catFileSpec, hA, hfn, Streams.ofSpec]
    · rw [hg3]; simp [hpre.2.2.1, catFileSpec, hA, hfn, Streams.errorMsg, Streams.ofSpec,
        Silmaril.Apps.Sha256sum.World.argv0]
    · simp [catFileSpec, hA, hfn]
  | ok d =>
    simp only [hfn, Streams.openedSt] at h1
    obtain ⟨fd, hf, hne, hfd3, -, -, -, hnew⟩ := h1.resolve_left fun h => by
      -- `fopen` is called while `main` runs, with no stream open: it has room for one more
      obtain ⟨-, hno, -⟩ := h
      rcases hno with hno | hno
      · rw [henv.1] at hno; cases hno
      · refine hno ⟨⟨[], ?_⟩, ?_, ?_, henv.2.2 _ 3 _ (by rw [hfs, hfn]; rfl)⟩
        · simp only [Proc.callEntry_g]
          simp only [‹u.g = _›]; exact hpre.2.2.2.1
        · simp only [Proc.callEntry_rsp]; mregs; mnat
        · simp only [Proc.callEntry_g]
          simp only [‹u.g = _›, hpre.2.2.2.2.2.2]; exact henv.2.1
    exact succ ⟨3, true, Streams.ofSpec d, false, false, false, []⟩ d (by simp [catFileSpec, hA, hfn])
      (by simp [catFileSpec, hA, hfn]) (by simp [catFileSpec, hA, hfn]) rfl fd hf hne hfd3
      fun h => hnew _ (by rw [h]; exact file_push O.1 (by mnat))
  | readErr e pre =>
    simp only [hfn, Streams.openedSt] at h1
    obtain ⟨fd, hf, hne, hfd3, -, -, -, hnew⟩ := h1.resolve_left fun h => by
      -- `fopen` is called while `main` runs, with no stream open: it has room for one more
      obtain ⟨-, hno, -⟩ := h
      rcases hno with hno | hno
      · rw [henv.1] at hno; cases hno
      · refine hno ⟨⟨[], ?_⟩, ?_, ?_, henv.2.2 _ 3 _ (by rw [hfs, hfn]; rfl)⟩
        · simp only [Proc.callEntry_g]
          simp only [‹u.g = _›]; exact hpre.2.2.2.1
        · simp only [Proc.callEntry_rsp]; mregs; mnat
        · simp only [Proc.callEntry_g]
          simp only [‹u.g = _›, hpre.2.2.2.2.2.2]; exact henv.2.1
    exact succ ⟨3, true, Streams.ofSpec pre, true, false, false, []⟩ pre (by simp [catFileSpec, hA, hfn])
      (by simp [catFileSpec, hA, hfn]) (by simp [catFileSpec, hA, hfn]) rfl fd hf hne hfd3
      fun h => hnew _ (by rw [h]; exact file_push O.1 (by mnat))

/-- **Every run of `cat-file-gcc` on one operand** (writes to stdout succeed, allocations
succeed within the library's bounds, `Std.allocates`) copies the file to stdout and exits 0, or, when the open fails with `e`, writes
`argv[0]: NAME: strerror (e)` to stderr and exits 1. -/
theorem catFileGcc_verified : Verified catFileGcc libc ld catFileSpec (Tier.operands 1) lib Std.allocates :=
  verified catFileGcc_ok libc_ok ld_ok (fun _ h => h.1) catFileGcc_main

end Silmaril.Elf.Link.Dyn.Program.Examples
