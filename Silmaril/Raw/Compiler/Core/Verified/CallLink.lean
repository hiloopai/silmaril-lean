module

public import Silmaril.Compiler.Core.Verified.IntExprLir.Defs
public import Silmaril.Compiler.Core.Verified.Call.Defs
/-! # The link of a `main` that calls a procedure

`link results ops r cops rets` is the linked program of a C `main` that calls a procedure
without parameters, then runs the register operations `ops` and returns register `r`. It has
two Lir functions: `__ccomp_start` (function 0), one block `call 1 () → results; ops; ret r`,
and the callee (function 1), one block `cops; ret rets`. The control block and the initial
image are those of `ConstLink.link`.

`link_sound`: when the callee's operations return the words `vals` from the empty frame, and
the caller's operations, from every frame once `results` received `vals`, leave the word `w`
in `r`, every observation of the artifact is exhaustion or `exit (w mod 256) []`.

`planLink` is the translation of a `Call.Plan`: the callee computes its returned `int`
expression into register 0 and returns it (`void`: returns nothing); `main` receives it in
register 0 (`return g();`) or computes its own returned expression after the call.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CallLink

open Silmaril.Machine
open Spec Backend
open IntExpr (Term)

/-- `__ccomp_start(argc, argv)`: `call 1 () → results; ops; ret r`. -/
def startFunc (results : List (Lir.Loc Mir.Reg)) (ops : List (Lir.Op Mir.Reg)) (r : Mir.Reg) :
    Lir.Func Mir.Reg :=
  { params := [.reg 1, .reg 2], entry := 0,
    blocks := [⟨.call 1 [] results :: ops.map .op, .ret [.reg r]⟩] }

/-- The callee: `cops; ret rets`. -/
def calleeFunc (cops : List (Lir.Op Mir.Reg)) (rets : List (Lir.Loc Mir.Reg)) : Lir.Func Mir.Reg :=
  { params := [], entry := 0, blocks := [⟨cops.map .op, .ret rets⟩] }

/-- The linked program of a `main` that calls one procedure. -/
def link (results : List (Lir.Loc Mir.Reg)) (ops : List (Lir.Op Mir.Reg)) (r : Mir.Reg)
    (cops : List (Lir.Op Mir.Reg)) (rets : List (Lir.Loc Mir.Reg)) : Mir.Linked where
  prog := ⟨[startFunc results ops r, calleeFunc cops rets]⟩
  funcs := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.startSymbol 0
  data := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol ctlAddr
  dataBase := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  dataEnd := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  image := .empty

section
variable {results : List (Lir.Loc Mir.Reg)} {ops : List (Lir.Op Mir.Reg)} {r : Mir.Reg}
  {cops : List (Lir.Op Mir.Reg)} {rets : List (Lir.Loc Mir.Reg)}

theorem link_funcs : (link results ops r cops rets).funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some 0 := by
  simp [link]

/-- The run of `__ccomp_start` calls the callee, receives its words, runs `ops` and returns
`r`. -/
theorem link_returns {argc argv : Lir.Word} {mem : Lir.Memory} {vals : List Lir.Word}
    {cfr : Lir.Frame Mir.Reg} (hc : Lir.execOps cops Lir.Frame.empty mem = some (cfr, mem))
    (hv : cfr.readAll rets = some vals) {fr1 : Lir.Frame Mir.Reg}
    (hw : ((Lir.Frame.empty.set 1 argc).set 2 argv).writeAll results vals = some fr1)
    {fr2 : Lir.Frame Mir.Reg} {w : Lir.Word}
    (hx : Lir.execOps ops fr1 mem = some (fr2, mem)) (hr : fr2.get r = some w) :
    ∃ s, (link results ops r cops rets).prog.start 0 [argc, argv] mem = some s ∧
      Lir.Behaves (link results ops r cops rets).prog s (.returned [w] mem) := by
  let fr0 : Lir.Frame Mir.Reg := (Lir.Frame.empty.set 1 argc).set 2 argv
  let a : Lir.Activation Mir.Reg := ⟨⟨0, 0, 0⟩, fr0⟩
  refine ⟨⟨⟨0, 0, 0⟩, fr0, [], mem⟩, rfl, ?_⟩
  have hcall : (link results ops r cops rets).prog.fetch ⟨0, 0, 0⟩ =
      some (.instr (.call 1 [] results)) := rfl
  have s1 : Lir.Step (link results ops r cops rets).prog ⟨⟨0, 0, 0⟩, fr0, [], mem⟩
      ⟨⟨1, 0, 0⟩, Lir.Frame.empty, [a], mem⟩ :=
    (Lir.Transition.call (s := ⟨⟨0, 0, 0⟩, fr0, [], mem⟩) hcall rfl rfl).step_eq
  have s2 : Lir.Steps (link results ops r cops rets).prog ⟨⟨1, 0, 0⟩, Lir.Frame.empty, [a], mem⟩
      ⟨⟨1, 0, 0 + cops.length⟩, cfr, [a], mem⟩ :=
    Lir.steps_execOps (b := ⟨cops.map .op, .ret rets⟩) (rest := []) rfl (by simp) hc
  have hret : (link results ops r cops rets).prog.fetch ⟨1, 0, 0 + cops.length⟩ =
      some (.term (.ret rets)) :=
    Lir.Prog.fetch_eq_term (b := ⟨cops.map .op, .ret rets⟩) rfl (by simp)
  have s3 : Lir.Step (link results ops r cops rets).prog ⟨⟨1, 0, 0 + cops.length⟩, cfr, [a], mem⟩
      ⟨⟨0, 0, 1⟩, fr1, [], mem⟩ :=
    (Lir.Transition.ret (s := ⟨⟨1, 0, 0 + cops.length⟩, cfr, [a], mem⟩) hret hv rfl hcall hw).step_eq
  have s4 : Lir.Steps (link results ops r cops rets).prog ⟨⟨0, 0, 1⟩, fr1, [], mem⟩
      ⟨⟨0, 0, 1 + ops.length⟩, fr2, [], mem⟩ :=
    Lir.steps_execOps (b := ⟨.call 1 [] results :: ops.map .op, .ret [.reg r]⟩) (rest := []) rfl
      (by simp) hx
  refine ⟨_, Relation.ReflTransGen.head s1 (s2.trans (Relation.ReflTransGen.head s3 s4)), ?_⟩
  have hf : (link results ops r cops rets).prog.fetch ⟨0, 0, 1 + ops.length⟩ =
      some (.term (.ret [.reg r])) :=
    Lir.Prog.fetch_eq_term (b := ⟨.call 1 [] results :: ops.map .op, .ret [.reg r]⟩) rfl
      (by simp; omega)
  have hr' : fr2.regs r = some w := hr
  exact (Lir.Transition.halt (s := ⟨⟨0, 0, 1 + ops.length⟩, fr2, [], mem⟩) hf
    (by simp [Lir.Frame.readAll, Lir.Frame.read, hr']) rfl).step_eq

theorem link_beh {argc argv : Lir.Word} {mem : Lir.Memory} {vals : List Lir.Word}
    {cfr : Lir.Frame Mir.Reg} (hc : Lir.execOps cops Lir.Frame.empty mem = some (cfr, mem))
    (hv : cfr.readAll rets = some vals) {fr1 : Lir.Frame Mir.Reg}
    (hw : ((Lir.Frame.empty.set 1 argc).set 2 argv).writeAll results vals = some fr1)
    {fr2 : Lir.Frame Mir.Reg} {w : Lir.Word}
    (hx : Lir.execOps ops fr1 mem = some (fr2, mem)) (hr : fr2.get r = some w)
    {s : Lir.State Mir.Reg} (hs : (link results ops r cops rets).prog.start 0 [argc, argv] mem = some s)
    {b : Lir.Behavior} (hb : Lir.Behaves (link results ops r cops rets).prog s b) :
    b = .returned [w] mem := by
  obtain ⟨s', hs', hret⟩ := link_returns hc hv hw hx hr
  rw [hs] at hs'
  cases hs'
  exact Lir.Behaves.unique hb hret

/-- **The call link is correct.** -/
theorem link_sound {a : Artifact} {args : List String} {vals : List Lir.Word} {w : Lir.Word}
    (hc : ∃ cfr, Lir.execOps cops Lir.Frame.empty (a.lmem args) = some (cfr, a.lmem args) ∧
      cfr.readAll rets = some vals)
    (hx : ∀ (fr0 : Lir.Frame Mir.Reg), ∃ fr1, fr0.writeAll results vals = some fr1 ∧
      ∃ fr2, Lir.execOps ops fr1 (a.lmem args) = some (fr2, a.lmem args) ∧ fr2.get r = some w)
    (h : artifactOf (link results ops r cops rets) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit (w.toNat % 256) [] := by
  have himg : a.image = .empty := by
    rw [(ConstLink.artifact_layout h).2.2]; rfl
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link_funcs] at hstart
  cases hstart
  obtain ⟨cfr, hc', hv⟩ := hc
  obtain ⟨fr1, hw, fr2, hx', hr⟩ := hx ((Lir.Frame.empty.set 1 (BitVec.ofNat 64 args.length)).set 2
    (BitVec.ofNat 64 a.argBase))
  rcases ho with ho | hstuck | ⟨b, hb, hobs⟩
  · exact .inl ho
  · cases link_beh hc' hv hw hx' hr hs hstuck
  · right
    cases link_beh hc' hv hw hx' hr hs hb
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

end

/-! ## The translation of a call plan -/

/-- The callee's code: its returned expression into register 0 (nothing for `void`). -/
def calleeOps : Option Term → List (Lir.Op Mir.Reg)
  | some t => IntExpr.exprOps 0 t
  | none => []

/-- The callee's returned registers. -/
def calleeRets : Option Term → List (Lir.Loc Mir.Reg)
  | some _ => [.reg 0]
  | none => []

/-- The words the callee returns. -/
def calleeVals : Option Term → List Lir.Word
  | some t => [BitVec.ofInt 64 (t.val 0)]
  | none => []

theorem callee_exec (c : Option Term) (ok : ∀ t, c = some t → t.Ok 0) (mem : Lir.Memory) :
    ∃ cfr, Lir.execOps (calleeOps c) Lir.Frame.empty mem = some (cfr, mem) ∧
      cfr.readAll (calleeRets c) = some (calleeVals c) := by
  cases c with
  | none => exact ⟨Lir.Frame.empty, rfl, rfl⟩
  | some t =>
    obtain ⟨fr, hx, hr⟩ := IntExpr.exprOps_exec (ok t rfl) Lir.Frame.empty mem
    have hr' : fr.regs 0 = some (BitVec.ofInt 64 (t.val 0)) := hr
    exact ⟨fr, hx, by simp [calleeRets, calleeVals, Lir.Frame.readAll, Lir.Frame.read, hr']⟩

theorem callee_write (c : Option Term) (fr : Lir.Frame Mir.Reg) :
    ∃ fr1, fr.writeAll (calleeRets c) (calleeVals c) = some fr1 := by
  cases c <;> exact ⟨_, rfl⟩

/-- A discarded callee result still has a total register execution, even if an integer
intermediate is outside the source range. -/
theorem callee_exec_discard (c : Option Term) (mem : Lir.Memory) :
    ∃ vals, (∃ cfr, Lir.execOps (calleeOps c) Lir.Frame.empty mem = some (cfr, mem) ∧
      cfr.readAll (calleeRets c) = some vals) ∧
      ∀ fr : Lir.Frame Mir.Reg, ∃ fr1, fr.writeAll (calleeRets c) vals = some fr1 := by
  cases c with
  | none => exact ⟨[], ⟨Lir.Frame.empty, rfl, rfl⟩, fun fr => ⟨fr, rfl⟩⟩
  | some t =>
    obtain ⟨fr, w, hx, hr, -, -⟩ := Term.ops_exec (n := 0) t 4 (Nat.le_refl 4)
      (Lir.Frame.empty.set 3 (BitVec.ofInt 64 0)) mem (by simp)
    have ex : Lir.execOps (IntExpr.exprOps 0 t) Lir.Frame.empty mem =
        some (fr.set 0 w, mem) := by
      simp only [IntExpr.exprOps, List.cons_append, Lir.execOps_cons, Lir.Op.exec,
        Option.bind_some, Lir.execOps_append, hx]
      simp [Lir.execOps, hr]
    refine ⟨[w], ⟨fr.set 0 w, ex, ?_⟩, fun f => ⟨f.set 0 w, rfl⟩⟩
    simp [calleeRets, Lir.Frame.readAll, Lir.Frame.read]

/-- The Lir program of a recognised call plan. -/
def planLink : Call.Plan → Mir.Linked
  | .ret _ t => link [.reg 0] [] 0 (calleeOps (some t)) [.reg 0]
  | .stmt _ c t | .comma _ c t => link (calleeRets c) (IntExpr.exprOps 0 t) 0 (calleeOps c) (calleeRets c)

/-- **The translation of a call plan is correct**: every observation is exhaustion or the
exit with the word of `main`'s returned expression. -/
theorem planLink_sound (pl : Call.Plan) (ok : pl.result.Ok 0) {a : Artifact} (h : artifactOf (planLink pl) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit ((BitVec.ofInt 64 (pl.result.val 0)).toNat % 256) [] := by
  cases pl with
  | ret g t =>
    refine link_sound (vals := calleeVals (some t)) (callee_exec (some t) (by intro t' ht; cases ht; exact ok) _) ?_ h hl hb
    intro fr0
    exact ⟨fr0.set 0 (BitVec.ofInt 64 (t.val 0)), rfl, _, rfl, by simp [Call.Plan.result]⟩
  | stmt g c t | comma g c t =>
    obtain ⟨vals, hc, hw⟩ := callee_exec_discard c (a.lmem args)
    refine link_sound hc ?_ h hl hb
    intro fr0
    obtain ⟨fr1, hw⟩ := hw fr0
    exact ⟨fr1, hw, IntExpr.exprOps_exec ok fr1 (a.lmem args)⟩

end Silmaril.Compile.Core.Verified.CallLink
