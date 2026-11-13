module

public import Silmaril.Compiler.Core.Verified.CallLink.Defs
public import Silmaril.Compiler.Core.Verified.CallArg.Defs
/-! # The link of a `main` that returns `g(n)`

`link n t` is the linked program of a C `main` that returns `g(n)` for a procedure `g` with
one `int` parameter returning the expression `t` of it. It has two Lir functions:
`__ccomp_start` (function 0), one block `r5 := n; call 1 (r5) → r0; ret r0`, and `g`
(function 1), whose parameter arrives in register 3, one block computing `t` from register 3
into register 0 (`IntExpr.Term.ops`), then `ret r0`. The control block and the initial image
are those of `ConstLink.link`.

`link_sound`: every observation of the artifact is exhaustion or the exit with the word of
`t.val n` mod 256.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CallArgLink

open Silmaril.Machine
open Spec Backend
open IntExpr (Term)

/-- `__ccomp_start(argc, argv)`: `r5 := n; call 1 (r5) → r0; ret r0`. -/
def startFunc (n : Int) : Lir.Func Mir.Reg :=
  { params := [.reg 1, .reg 2], entry := 0,
    blocks := [⟨[.op (.const 5 (BitVec.ofInt 64 n)), .call 1 [.reg 5] [.reg 0]], .ret [.reg 0]⟩] }

/-- The code of the callee: `t` from the parameter in register 3 into register 0. -/
def calleeOps (t : Term) : List (Lir.Op Mir.Reg) := t.ops 4 ++ [.move 0 4]

/-- The callee `g(x)`: `x` in register 3, `ret t`. -/
def calleeFunc (t : Term) : Lir.Func Mir.Reg :=
  { params := [.reg 3], entry := 0, blocks := [⟨(calleeOps t).map .op, .ret [.reg 0]⟩] }

/-- The linked program of a `main` that returns `g(n)`. -/
def link (n : Int) (t : Term) : Mir.Linked where
  prog := ⟨[startFunc n, calleeFunc t]⟩
  funcs := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.startSymbol 0
  data := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol ctlAddr
  dataBase := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  dataEnd := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  image := .empty

theorem link_funcs (n : Int) (t : Term) : (link n t).funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some 0 := by
  simp [link]

theorem calleeOps_exec {n : Int} {t : Term} (ok : t.Ok n) (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory)
    (h3 : fr.get 3 = some (BitVec.ofInt 64 n)) :
    ∃ fr', Lir.execOps (calleeOps t) fr mem = some (fr', mem) ∧
      fr'.get 0 = some (BitVec.ofInt 64 (t.val n)) := by
  obtain ⟨fr₁, w, x₁, g₁, v₁, -⟩ := Term.ops_exec (n := n) t 4 (Nat.le_refl 4) fr mem h3
  rw [v₁ ok] at g₁
  refine ⟨fr₁.set 0 (BitVec.ofInt 64 (t.val n)), ?_, by simp⟩
  simp only [calleeOps, Lir.execOps_append, x₁, Option.bind_some]
  simp [Lir.execOps, Lir.Op.exec, g₁]

/-- The run of `__ccomp_start` calls `g` with `n` and returns its result. -/
theorem link_returns {n : Int} {t : Term} (ok : t.Ok n) (argc argv : Lir.Word) (mem : Lir.Memory) :
    ∃ s, (link n t).prog.start 0 [argc, argv] mem = some s ∧
      Lir.Behaves (link n t).prog s (.returned [BitVec.ofInt 64 (t.val n)] mem) := by
  let w : Lir.Word := BitVec.ofInt 64 (t.val n)
  let fr0 : Lir.Frame Mir.Reg := (Lir.Frame.empty.set 1 argc).set 2 argv
  let fr1 := fr0.set 5 (BitVec.ofInt 64 n)
  let a : Lir.Activation Mir.Reg := ⟨⟨0, 0, 1⟩, fr1⟩
  let cfr0 : Lir.Frame Mir.Reg := Lir.Frame.empty.set 3 (BitVec.ofInt 64 n)
  refine ⟨⟨⟨0, 0, 0⟩, fr0, [], mem⟩, rfl, ?_⟩
  have s1 : Lir.Step (link n t).prog ⟨⟨0, 0, 0⟩, fr0, [], mem⟩ ⟨⟨0, 0, 1⟩, fr1, [], mem⟩ :=
    (Lir.Transition.op (s := ⟨⟨0, 0, 0⟩, fr0, [], mem⟩) rfl rfl).step_eq
  have hcall : (link n t).prog.fetch ⟨0, 0, 1⟩ = some (.instr (.call 1 [.reg 5] [.reg 0])) := rfl
  have s2 : Lir.Step (link n t).prog ⟨⟨0, 0, 1⟩, fr1, [], mem⟩ ⟨⟨1, 0, 0⟩, cfr0, [a], mem⟩ :=
    (Lir.Transition.call (s := ⟨⟨0, 0, 1⟩, fr1, [], mem⟩) (vals := [BitVec.ofInt 64 n]) hcall
      (by simp [fr1, Lir.Frame.readAll, Lir.Frame.read]) rfl).step_eq
  obtain ⟨cfr, hx, hr⟩ := calleeOps_exec ok cfr0 mem (by simp [cfr0])
  have s3 : Lir.Steps (link n t).prog ⟨⟨1, 0, 0⟩, cfr0, [a], mem⟩
      ⟨⟨1, 0, 0 + (calleeOps t).length⟩, cfr, [a], mem⟩ :=
    Lir.steps_execOps (b := ⟨(calleeOps t).map .op, .ret [.reg 0]⟩) (rest := []) rfl (by simp) hx
  have hret : (link n t).prog.fetch ⟨1, 0, 0 + (calleeOps t).length⟩ = some (.term (.ret [.reg 0])) :=
    Lir.Prog.fetch_eq_term (b := ⟨(calleeOps t).map .op, .ret [.reg 0]⟩) rfl (by simp)
  have hr' : cfr.regs 0 = some w := hr
  have s4 : Lir.Step (link n t).prog ⟨⟨1, 0, 0 + (calleeOps t).length⟩, cfr, [a], mem⟩
      ⟨⟨0, 0, 2⟩, fr1.set 0 w, [], mem⟩ :=
    (Lir.Transition.ret (s := ⟨⟨1, 0, 0 + (calleeOps t).length⟩, cfr, [a], mem⟩) (vals := [w])
      (fr := fr1.set 0 w) hret (by simp [Lir.Frame.readAll, Lir.Frame.read, hr']) rfl hcall
      rfl).step_eq
  refine ⟨_, Relation.ReflTransGen.head s1 (Relation.ReflTransGen.head s2
    (s3.trans (Relation.ReflTransGen.single s4))), ?_⟩
  have hf : (link n t).prog.fetch ⟨0, 0, 2⟩ = some (.term (.ret [.reg 0])) := rfl
  exact (Lir.Transition.halt (s := ⟨⟨0, 0, 2⟩, fr1.set 0 w, [], mem⟩) (vals := [w]) hf
    (by simp [Lir.Frame.readAll, Lir.Frame.read]) rfl).step_eq

theorem link_beh {n : Int} {t : Term} (ok : t.Ok n) {argc argv : Lir.Word} {mem : Lir.Memory}
    {s : Lir.State Mir.Reg} (hs : (link n t).prog.start 0 [argc, argv] mem = some s)
    {b : Lir.Behavior} (hb : Lir.Behaves (link n t).prog s b) :
    b = .returned [BitVec.ofInt 64 (t.val n)] mem := by
  obtain ⟨s', hs', hret⟩ := link_returns ok argc argv mem
  rw [hs] at hs'
  cases hs'
  exact Lir.Behaves.unique hb hret

/-- **The argument link is correct.** -/
theorem link_sound {n : Int} {t : Term} (ok : t.Ok n) {a : Artifact} (h : artifactOf (link n t) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit ((BitVec.ofInt 64 (t.val n)).toNat % 256) [] := by
  have himg : a.image = .empty := by
    rw [(ConstLink.artifact_layout h).2.2]; rfl
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link_funcs] at hstart
  cases hstart
  rcases ho with ho | hstuck | ⟨b, hb, hobs⟩
  · exact .inl ho
  · cases link_beh ok hs hstuck
  · right
    cases link_beh ok hs hb
    obtain ⟨k, out, rfl, hk, hout⟩ := hobs
    have hzero (addr : Nat) (hi : addr + 8 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) :
        memWord (a.lmem args) addr = 0 := by
      apply ConstLink.memWord_zero
      intro i
      apply ConstLink.lmem_bytes_empty himg
      rw [(ConstLink.artifact_layout h).1]
      have := i.isLt
      omega
    rw [hk _ rfl, ConstLink.stdoutOf_zero (hzero (ctlAddr + 24) (by decide))
      (hzero (ctlAddr + 48) (by decide)) hout]

end Silmaril.Compile.Core.Verified.CallArgLink
