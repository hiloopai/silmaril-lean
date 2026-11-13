module

public import Silmaril.Compiler.Core.Verified.TyRun.Defs
public import Silmaril.Compiler.Core.Verified.StateExitLink.Defs
/-! # The typed statement machine's result: termination flag, abort control word, exit value

`StateExitLink` for `TyRun.Out`: the entry block computes the termination flag `R.test` at run
time and branches on it; the abort block records `abort` in the control block and traps, the
return block computes `R`'s value and returns it. -/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.TyRunLink

open Silmaril.Machine
open Spec Backend
open TyRun (Out)

def entryOps (R : Out) : List (Lir.Op Mir.Reg) :=
  R.test.ops 6 ++ [.const 7 1, .binary (.cmp .eq) 8 6 7]

def retOps (R : Out) : List (Lir.Op Mir.Reg) := R.ops 11 ++ [.move 0 11]

def blocks (R : Out) : List (Lir.Block Mir.Reg) :=
  [⟨(entryOps R).map .op, .branch 8 2 1⟩, ⟨StateExitLink.abortOps.map .op, .trap⟩,
    ⟨(retOps R).map .op, .ret [.reg 0]⟩]

def link (R : Out) : Mir.Linked := LoopLink.link (blocks R)

theorem entry_exec {R : Out} (wf : Out.wf R = true) (fr0 : Lir.Frame Mir.Reg) (mem : Lir.Memory) :
    ∃ fr, Lir.execOps (entryOps R) fr0 mem = some (fr, mem) ∧
      fr.get 8 = some (Lir.ofBool (decide (R.test.val = 1))) := by
  obtain ⟨fr₂, hx₂, hg₂, -⟩ := Out.ops_exec R.test (Out.wf_test R wf) 6 fr0 mem
  refine ⟨(fr₂.set 7 1).set 8 (Lir.ofBool (BitVec.ofInt 64 R.test.val == 1)), ?_, ?_⟩
  · rw [entryOps, Lir.execOps_append, hx₂]
    simp [Lir.execOps, Lir.Op.exec, hg₂, Lir.Binop.eval, Lir.Cond.eval]
  · simp only [Lir.Frame.get_set, ↓reduceIte]
    exact congrArg (fun x => some (Lir.ofBool x)) (TyState.ofInt_eq_one (Out.test_val R))

theorem run_block {R : Out} {l : Nat} {ops : List (Lir.Op Mir.Reg)} {t : Lir.Term Mir.Reg}
    (hb : (link R).prog.block? 0 l = some ⟨ops.map .op, t⟩) {fr fr' : Lir.Frame Mir.Reg}
    {m m' : Lir.Memory} (hx : Lir.execOps ops fr m = some (fr', m')) :
    Lir.Steps (link R).prog ⟨⟨0, l, 0⟩, fr, [], m⟩ ⟨⟨0, l, ops.length⟩, fr', [], m'⟩ ∧
      (link R).prog.fetch ⟨0, l, ops.length⟩ = some (.term t) := by
  refine ⟨?_, Lir.Prog.fetch_eq_term (pt := ⟨0, l, ops.length⟩) hb (by simp)⟩
  have := Lir.steps_execOps (p := (link R).prog) (os := ops) (s := ⟨⟨0, l, 0⟩, fr, [], m⟩) (rest := []) hb
    (by rw [List.append_nil]; rfl) hx
  simpa using this

theorem block0 (R : Out) : (link R).prog.block? 0 0 = some ⟨(entryOps R).map .op, .branch 8 2 1⟩ := rfl
theorem block1 (R : Out) : (link R).prog.block? 0 1 = some ⟨StateExitLink.abortOps.map .op, .trap⟩ := rfl
theorem block2 (R : Out) : (link R).prog.block? 0 2 = some ⟨(retOps R).map .op, .ret [.reg 0]⟩ := rfl

/-- **The abort**: when the flag is not `1`, the run records `abort` and traps. -/
theorem abort_behaves {R : Out} (wf : Out.wf R = true) {a : Artifact} {args : List String}
    (size : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize) (ne : R.test.val ≠ 1) :
    ∃ m', (a.lmem args).store .b8 (ctlAddr + 40) (BitVec.ofNat 64 2) = some m' ∧
      Lir.Behaves (link R).prog (LoopLink.entryState a args) (.trapped m') := by
  obtain ⟨fr, hx, h8⟩ := entry_exec wf (LoopLink.entryState a args).frame (a.lmem args)
  simp only [ne, decide_false] at h8
  obtain ⟨s₀, hf₀⟩ := run_block (block0 R) hx
  obtain ⟨fr', m', hx', hst⟩ := StateExitLink.abort_exec fr (m := a.lmem args)
    (by simp [Artifact.lmem, size])
  obtain ⟨s₁, hf₁⟩ := run_block (block1 R) hx'
  refine ⟨m', hst, _, s₀.trans (Relation.ReflTransGen.head ?_ s₁), ?_⟩
  · show Lir.step _ _ = _
    simp [Lir.step, hf₀, h8, Lir.ofBool]
  · simp [Lir.step, hf₁]

/-- **The return**: when the flag is `1`, the run returns `R`'s value. -/
theorem ret_behaves {R : Out} (wf : Out.wf R = true) {a : Artifact} {args : List String}
    (eq : R.test.val = 1) :
    Lir.Behaves (link R).prog (LoopLink.entryState a args)
      (.returned [BitVec.ofInt 64 R.val] (a.lmem args)) := by
  obtain ⟨fr, hx, h8⟩ := entry_exec wf (LoopLink.entryState a args).frame (a.lmem args)
  simp only [eq, decide_true] at h8
  obtain ⟨s₀, hf₀⟩ := run_block (block0 R) hx
  obtain ⟨fr₂, hx₂, hg₂, -⟩ := Out.ops_exec R wf 11 fr (a.lmem args)
  have hx' : Lir.execOps (retOps R) fr (a.lmem args) =
      some (fr₂.set 0 (BitVec.ofInt 64 R.val), a.lmem args) := by
    rw [retOps, Lir.execOps_append, hx₂]
    simp [Lir.execOps, Lir.Op.exec, hg₂]
  obtain ⟨s₁, hf₁⟩ := run_block (block2 R) hx'
  refine ⟨_, s₀.trans (Relation.ReflTransGen.head ?_ s₁), ?_⟩
  · show Lir.step _ _ = _
    simp [Lir.step, hf₀, h8, Lir.ofBool]
  · simp [Lir.step, hf₁, Lir.Frame.readAll, Lir.Frame.read]

/-- **The link is correct**: every observation is exhaustion, `abort` with no output when the flag
is not `1`, or the exit with `R`'s value when it is. -/
theorem link_sound {R : Out} (wf : Out.wf R = true) {a : Artifact} (h : artifactOf (link R) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String}
    {o : Obs} (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨
      (R.test.val ≠ 1 → o = .abort []) ∧
        (R.test.val = 1 → o = .exit ((BitVec.ofInt 64 R.val).toNat % 256) []) := by
  obtain ⟨hbase, -, himg⟩ := ConstLink.artifact_layout h
  have size : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize := ArgvAbortLink.artifact_memSize h
  have img : a.image = .empty := by simpa [link, LoopLink.link] using himg
  have hzero (addr : Nat) (hi : addr + 8 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) : memWord (a.lmem args) addr = 0 := by
    apply ConstLink.memWord_zero
    intro i
    apply ConstLink.lmem_bytes_empty img
    rw [hbase]
    have := i.isLt
    omega
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link, LoopLink.link_funcs] at hstart
  cases hstart
  rw [link, LoopLink.link_start] at hs
  cases hs
  rcases ho with ho | hstuck | ⟨b, hb', hobs⟩
  · exact .inl ho
  · right
    refine ⟨fun ne => ?_, fun eq => ?_⟩
    · obtain ⟨m', -, hab⟩ := abort_behaves wf size ne
      cases Lir.Behaves.unique hstuck hab
    · cases Lir.Behaves.unique hstuck (ret_behaves wf eq)
  · right
    refine ⟨fun ne => ?_, fun eq => ?_⟩
    · obtain ⟨m', hst, hab⟩ := abort_behaves wf size ne
      cases Lir.Behaves.unique hb' hab
      obtain ⟨out, rfl, hout⟩ := hobs
      have h40 : memWord m' (ctlAddr + 40) = 2 := by
        rw [PrintLink.memWord_store hst]; rfl
      have h24 : memWord m' (ctlAddr + 24) = 0 := by
        rw [PrintLink.memWord_outside hst (by left; decide)]; exact hzero _ (by decide)
      have h48 : memWord m' (ctlAddr + 48) = 0 := by
        rw [PrintLink.memWord_outside hst (by right; decide)]; exact hzero _ (by decide)
      rw [ConstLink.stdoutOf_zero h24 h48 hout]
      simp [trapObs, h40]
    · cases Lir.Behaves.unique hb' (ret_behaves wf eq)
      exact LoopLink.exit_obs (blocks := blocks R) h hobs

end Silmaril.Compile.Core.Verified.TyRunLink
