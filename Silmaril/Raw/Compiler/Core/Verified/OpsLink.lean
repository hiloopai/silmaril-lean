module

public import Silmaril.Compiler.Core.Verified.ConstLink.Defs

/-! # The link of a straight-line `main`

`link ops r` is the whole linked program of a straight-line C `main`: one Lir function,
`__ccomp_start`, whose single block runs the register operations `ops` and returns register
`r`; it takes `argc` and `argv` in registers 1 and 2 and ignores them. The control block and
the initial image are those of `ConstLink.link`.

`link_sound`: when `ops` run from every frame without touching memory and leave the word `w`
in `r`, every observation of the artifact of `link ops r` is exhaustion or
`exit (w mod 256) []`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.OpsLink

open Silmaril.Machine
open Spec Backend

/-- `__ccomp_start(argc, argv)`: `ops; ret r`. -/
def startFunc (ops : List (Lir.Op Mir.Reg)) (r : Mir.Reg) : Lir.Func Mir.Reg :=
  { params := [.reg 1, .reg 2], entry := 0, blocks := [⟨ops.map .op, .ret [.reg r]⟩] }

/-- The linked program of a straight-line `main`. -/
def link (ops : List (Lir.Op Mir.Reg)) (r : Mir.Reg) : Mir.Linked where
  prog := ⟨[startFunc ops r]⟩
  funcs := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.startSymbol 0
  data := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol ctlAddr
  dataBase := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  dataEnd := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  image := .empty

theorem link_funcs (ops : List (Lir.Op Mir.Reg)) (r : Mir.Reg) :
    (link ops r).funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some 0 := by
  simp [link]

/-- The run of `__ccomp_start` executes `ops`, then returns `r`. -/
theorem link_returns {ops : List (Lir.Op Mir.Reg)} {r : Mir.Reg} {argc argv : Lir.Word}
    {mem : Lir.Memory} {fr : Lir.Frame Mir.Reg} {w : Lir.Word}
    (hx : Lir.execOps ops ((Lir.Frame.empty.set 1 argc).set 2 argv) mem = some (fr, mem))
    (hr : fr.get r = some w) :
    ∃ s, (link ops r).prog.start 0 [argc, argv] mem = some s ∧
      Lir.Behaves (link ops r).prog s (.returned [w] mem) := by
  refine ⟨⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩, rfl, ?_⟩
  have hb : (link ops r).prog.block? 0 0 = some ⟨ops.map .op, .ret [.reg r]⟩ := rfl
  have steps := Lir.steps_execOps (p := (link ops r).prog) (os := ops)
    (s := ⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩) (rest := []) hb
    (by rw [List.append_nil]; rfl) hx
  refine ⟨_, steps, ?_⟩
  have hf : (link ops r).prog.fetch ⟨0, 0, ops.length⟩ = some (.term (.ret [.reg r])) :=
    Lir.Prog.fetch_eq_term (pt := ⟨0, 0, ops.length⟩) hb (by simp)
  have hr' : fr.regs r = some w := hr
  simp [Lir.step, hf, Lir.Frame.readAll, Lir.Frame.read, hr']

theorem link_beh {ops : List (Lir.Op Mir.Reg)} {r : Mir.Reg} {argc argv : Lir.Word}
    {mem : Lir.Memory} {fr : Lir.Frame Mir.Reg} {w : Lir.Word}
    (hx : Lir.execOps ops ((Lir.Frame.empty.set 1 argc).set 2 argv) mem = some (fr, mem))
    (hr : fr.get r = some w)
    {s : Lir.State Mir.Reg} (hs : (link ops r).prog.start 0 [argc, argv] mem = some s)
    {b : Lir.Behavior}
    (hb : Lir.Behaves (link ops r).prog s b) : b = .returned [w] mem := by
  obtain ⟨s', hs', hret⟩ := link_returns hx hr
  rw [hs] at hs'
  cases hs'
  exact Lir.Behaves.unique hb hret

/-- **The straight-line link is correct.** -/
theorem link_sound {ops : List (Lir.Op Mir.Reg)} {r : Mir.Reg} {w : Lir.Word}
    (hx : ∀ fr0 mem, ∃ fr, Lir.execOps ops fr0 mem = some (fr, mem) ∧ fr.get r = some w)
    {a : Artifact} (h : artifactOf (link ops r) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit (w.toNat % 256) [] := by
  have himg : a.image = .empty := by
    rw [(ConstLink.artifact_layout h).2.2]; rfl
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link_funcs] at hstart
  cases hstart
  obtain ⟨fr, hx', hr⟩ := hx ((Lir.Frame.empty.set 1 (BitVec.ofNat 64 args.length)).set 2
    (BitVec.ofNat 64 a.argBase)) (a.lmem args)
  rcases ho with ho | hstuck | ⟨b, hb, hobs⟩
  · exact .inl ho
  · cases link_beh hx' hr hs hstuck
  · right
    cases link_beh hx' hr hs hb
    obtain ⟨k, out, rfl, hk, hout⟩ := hobs
    have hzero (addr : Nat) (hi : addr + 8 ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase) :
        memWord (a.lmem args) addr = 0 := by
      apply ConstLink.memWord_zero
      intro i
      apply ConstLink.lmem_bytes_empty himg
      rw [(ConstLink.artifact_layout h).1]
      have := i.isLt
      omega
    rw [hk w rfl, ConstLink.stdoutOf_zero (hzero (ctlAddr + 24) (by decide))
      (hzero (ctlAddr + 48) (by decide)) hout]

end Silmaril.Compile.Core.Verified.OpsLink
