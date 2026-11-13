module

public import Silmaril.Compiler.Core.Verified.StateExitResult.Defs
public import Silmaril.Compiler.Core.Verified.ArgvAbortLink.Defs

/-! # Runtime termination flag, abort control word, and exit value -/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.StateExitLink

open Silmaril.Machine
open Spec Backend
open IntExpr (Term)
open StateExit (Result)

abbrev Plan := Result

def entryOps (P : Plan) : List (Lir.Op Mir.Reg) :=
  [.const 3 0] ++ P.test.ops 6 ++
    [.const 7 1, .binary (.cmp .eq) 8 6 7]

def abortOps : List (Lir.Op Mir.Reg) := [.const 9 0, .const 10 2, .store .b8 9 (ctlAddr + 40) 10]

def retOps (P : Plan) : List (Lir.Op Mir.Reg) := P.ret.ops 11 ++ [.move 0 11]

def blocks (P : Plan) : List (Lir.Block Mir.Reg) :=
  [⟨(entryOps P).map .op, .branch 8 2 1⟩, ⟨abortOps.map .op, .trap⟩, ⟨(retOps P).map .op, .ret [.reg 0]⟩]

def link (P : Plan) : Mir.Linked := LoopLink.link (blocks P)

theorem entry_exec {P : Plan} {a : Artifact} {args : List String} :
    ∃ fr, Lir.execOps (entryOps P) (LoopLink.entryState a args).frame (a.lmem args) = some (fr, a.lmem args) ∧
      fr.get 3 = some 0 ∧
      (P.test.Ok 0 → fr.get 8 = some (Lir.ofBool (decide (P.test.val 0 = 1)))) := by
  let fr0 := ((LoopLink.entryState a args).frame).set 3 0
  obtain ⟨fr₂, w, hx₂, hg₂, hv₂, hbelow⟩ := Term.ops_exec (n := 0) P.test 6 (by decide)
    fr0 (a.lmem args) (by simp [fr0])
  refine ⟨(fr₂.set 7 1).set 8 (Lir.ofBool (w == 1)), ?_, ?_, fun ok => ?_⟩
  · rw [entryOps, Lir.execOps_append, Lir.execOps_append]
    simp only [Lir.execOps, Lir.Op.exec, Option.bind_some]
    change (Lir.execOps (P.test.ops 6) fr0 (a.lmem args) >>= _) = _
    rw [hx₂]
    simp [hg₂, Lir.Binop.eval, Lir.Cond.eval]
  · simp [hbelow 3 (by decide), fr0]
  · simp only [Lir.Frame.get_set, ↓reduceIte, hv₂ ok]
    exact congrArg (fun x => some (Lir.ofBool x))
      (ArgvAbortLink.ofInt_eq_one (Term.int_of_ok P.test ok))

theorem run_block {P : Plan} {l : Nat} {ops : List (Lir.Op Mir.Reg)} {t : Lir.Term Mir.Reg}
    (hb : (link P).prog.block? 0 l = some ⟨ops.map .op, t⟩) {fr fr' : Lir.Frame Mir.Reg}
    {m m' : Lir.Memory} (hx : Lir.execOps ops fr m = some (fr', m')) :
    Lir.Steps (link P).prog ⟨⟨0, l, 0⟩, fr, [], m⟩ ⟨⟨0, l, ops.length⟩, fr', [], m'⟩ ∧
      (link P).prog.fetch ⟨0, l, ops.length⟩ = some (.term t) := by
  refine ⟨?_, Lir.Prog.fetch_eq_term (pt := ⟨0, l, ops.length⟩) hb (by simp)⟩
  have := Lir.steps_execOps (p := (link P).prog) (os := ops) (s := ⟨⟨0, l, 0⟩, fr, [], m⟩) (rest := []) hb
    (by rw [List.append_nil]; rfl) hx
  simpa using this

/-- The abort store: control word 5 := 2. -/
theorem abort_exec (fr : Lir.Frame Mir.Reg) {m : Lir.Memory} (hm : m.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    ∃ fr' m', Lir.execOps abortOps fr m = some (fr', m') ∧
      m.store .b8 (ctlAddr + 40) (BitVec.ofNat 64 2) = some m' := by
  have hin : m.InBounds (ctlAddr + 40) .b8 := by
    simp only [Lir.Memory.InBounds, Lir.Width.bytes, hm]; decide
  refine ⟨(fr.set 9 0).set 10 2, _, ?_, by simp [Lir.Memory.store, hin]; rfl⟩
  simp [abortOps, Lir.execOps, Lir.Op.exec, Lir.Memory.store, hin]

theorem block0 (P : Plan) : (link P).prog.block? 0 0 = some ⟨(entryOps P).map .op, .branch 8 2 1⟩ := rfl
theorem block1 (P : Plan) : (link P).prog.block? 0 1 = some ⟨abortOps.map .op, .trap⟩ := rfl
theorem block2 (P : Plan) : (link P).prog.block? 0 2 = some ⟨(retOps P).map .op, .ret [.reg 0]⟩ := rfl

structure Setup (P : Plan) (a : Artifact) (args : List String) : Prop where
  size : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize

/-- **The abort**: when the test is in range and not `1`, the run records `abort` and traps. -/
theorem abort_behaves {P : Plan} {a : Artifact} {args : List String} (st : Setup P a args)
    (ok : P.test.Ok 0)
    (ne : P.test.val 0 ≠ 1) :
    ∃ m', (a.lmem args).store .b8 (ctlAddr + 40) (BitVec.ofNat 64 2) = some m' ∧
      Lir.Behaves (link P).prog (LoopLink.entryState a args) (.trapped m') := by
  obtain ⟨fr, hx, -, h8⟩ := entry_exec
  have h8 := h8 ok
  simp only [ne, decide_false] at h8
  obtain ⟨s₀, hf₀⟩ := run_block (block0 P) hx
  obtain ⟨fr', m', hx', hst⟩ := abort_exec fr (m := a.lmem args) (by simp [Artifact.lmem, st.size])
  obtain ⟨s₁, hf₁⟩ := run_block (block1 P) hx'
  refine ⟨m', hst, _, s₀.trans (Relation.ReflTransGen.head ?_ s₁), ?_⟩
  · show Lir.step _ _ = _
    simp [Lir.step, hf₀, h8, Lir.ofBool]
  · simp [Lir.step, hf₁]

/-- **The return**: when the test is `1` and the return expression is in range, the run returns
its value. -/
theorem ret_behaves {P : Plan} {a : Artifact} {args : List String} (ok : P.test.Ok 0)
    (eq : P.test.val 0 = 1)
    (okr : P.ret.Ok 0) :
    Lir.Behaves (link P).prog (LoopLink.entryState a args)
      (.returned [BitVec.ofInt 64 (P.ret.val 0)] (a.lmem args)) := by
  obtain ⟨fr, hx, h3, h8⟩ := entry_exec
  have h8 := h8 ok
  simp only [eq, decide_true] at h8
  obtain ⟨s₀, hf₀⟩ := run_block (block0 P) hx
  obtain ⟨fr₂, w, hx₂, hg₂, hv₂, -⟩ := Term.ops_exec (n := 0) P.ret 11 (by decide) fr (a.lmem args) (by simpa using h3)
  have hx' : Lir.execOps (retOps P) fr (a.lmem args) = some (fr₂.set 0 w, a.lmem args) := by
    rw [retOps, Lir.execOps_append, hx₂]
    simp [Lir.execOps, Lir.Op.exec, hg₂]
  obtain ⟨s₁, hf₁⟩ := run_block (block2 P) hx'
  refine ⟨_, s₀.trans (Relation.ReflTransGen.head ?_ s₁), ?_⟩
  · show Lir.step _ _ = _
    simp [Lir.step, hf₀, h8, Lir.ofBool]
  · simp [Lir.step, hf₁, Lir.Frame.readAll, Lir.Frame.read, hv₂ okr]

/-- **The link is correct**: every observation is exhaustion, `abort` with no output when the test
is in range and not `1`, or the exit with the return expression's value when the test is `1` and
the return expression is in range. -/
theorem link_sound {P : Plan} {a : Artifact} (h : artifactOf (link P) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String}
    {o : Obs} (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨
      ((P.test.Ok 0 →
          P.test.val 0 ≠ 1 → o = .abort []) ∧
        (P.test.Ok 0 →
          P.test.val 0 = 1 →
          P.ret.Ok 0 →
          o = .exit ((BitVec.ofInt 64 (P.ret.val 0)).toNat % 256) [])) := by
  obtain ⟨hbase, -, himg⟩ := ConstLink.artifact_layout h
  have st : Setup P a args := ⟨ArgvAbortLink.artifact_memSize h⟩
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
    refine ⟨fun ok ne => ?_, fun ok eq okr => ?_⟩
    · obtain ⟨m', -, hab⟩ := abort_behaves st ok ne
      cases Lir.Behaves.unique hstuck hab
    · cases Lir.Behaves.unique hstuck (ret_behaves ok eq okr)
  · right
    refine ⟨fun ok ne => ?_, fun ok eq okr => ?_⟩
    · obtain ⟨m', hst, hab⟩ := abort_behaves st ok ne
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
    · cases Lir.Behaves.unique hb' (ret_behaves ok eq okr)
      exact LoopLink.exit_obs (blocks := blocks P) h hobs

end Silmaril.Compile.Core.Verified.StateExitLink
