module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Cases

/-!
# Calls and straight-line instructions of the top frame against Core

`call_case`: a call of a defined function pushes the callee's frame in both; the caller waits on
its results. `seg_next`: a straight-line step (`SegStep`); `seg_trapped`, `oob_trapped`: a trap
of the machine at a straight-line instruction, matched by a Core trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

variable {H : Type} {Pf : Profile} {host : HostSemantics H} {cap : Nat} {E : Env}
  {mi : ModuleInst} {c : Cfg} {s : Store H} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame}
  {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr} {rest : List CFr}

local notation "Steps" => Execution.Core.Steps Pf host

/-! ## Calls -/

/-- The frame shape of a callee. -/
def calleeFr (fn : FnDef) (args : List W) : CFr :=
  ⟨args ++ List.replicate fn.nlocals 0, fn.nres, ⟨[], [], fn.body⟩, []⟩

/-- The caller's frame shape while it waits. -/
def callerFr (fs : CFr) (n : Nat) (code : List Instr) : CFr :=
  { fs with l0 := ⟨fs.l0.ops.drop n, fs.l0.abs.drop n, code⟩ }

theorem callee_ok {fn : FnDef} {args : List W} (hE : EnvOk E) {j : Nat}
    (hj : E.fns[j]? = some fn) (ha : args.length = fn.nparams) : (calleeFr fn args).Ok E [] := by
  have hctx : (calleeFr fn args).ctx E = ⟨E, fn.nparams + fn.nlocals, fn.nres⟩ := by
    simp only [CFr.ctx, calleeFr, List.length_append, List.length_replicate, ha]
  refine ⟨.nil, ?_, trivial⟩
  rw [hctx]
  exact hE j fn hj

theorem stackC_consX (fs : CFr) (rest : List CFr) (X : List Admin) :
    stackC mi (fs :: rest) X = stackC mi rest [fs.admin mi X] := rfl

theorem call_steps {fn : FnDef} {f : FuncIdx} {code : List Instr} {n : Nat} (hH : HoldsProg s mi E)
    (hfn : E.fns[f.value.val - E.imps.length]? = some fn) (hf : E.imps.length ≤ f.value.val)
    (hn : n = fn.nparams) (hle : n ≤ fs.l0.ops.length) (h0 : fs.l0.code = .call f :: code) :
    Steps ⟨s, ⟨[], mi⟩, stackC mi (fs :: rest) []⟩ ⟨s, ⟨[], mi⟩,
      stackC mi (calleeFr fn (fs.l0.ops.take n).reverse :: callerFr fs n code :: rest) []⟩ := by
  have hcall := call_frame (Pf := Pf) (host := host) (f := localsF ⟨[], mi⟩ fs.locals) hH rfl hfn
    (x := f) (by simp only [Idx.toNat]; omega) (args := (fs.l0.ops.take n).reverse)
    (by rw [List.length_reverse, List.length_take]; omega)
  have h1 := steps_instrs ((fs.l0.ops.drop n).reverse.map Val.i32) (expression code) hcall
  rw [stackC_cons, stackC_cons, stackC_consX, admin_nil, h0, stackA_split n fs.l0.ops]
  have he : (calleeFr fn (fs.l0.ops.take n).reverse).admin mi [] = frameA mi fn.nres
      ((fs.l0.ops.take n).reverse ++ List.replicate fn.nlocals 0) (expression fn.body) := by
    simp only [CFr.admin, calleeFr, stackA, List.reverse_nil, List.map_nil, vals,
      List.nil_append, List.append_nil, wrapL]
  rw [he]
  refine steps_top rest fs.ls ?_ _
  simpa only [vals_append, List.map_reverse, CFr.admin, callerFr, stackA, List.append_assoc,
    List.singleton_append, expression, List.map_cons] using h1

theorem call_case (hT : Top cap E mi c s fr frs fs rest) {f : FuncIdx} {fn : FnDef}
    {code : List Instr} (h0 : fs.l0.code = .call f :: code) (hf : E.imps.length ≤ f.value.val)
    (hfn : E.fns[f.value.val - E.imps.length]? = some fn) (hn : fn.nparams ≤ fs.l0.abs.length)
    (hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) code
      (List.replicate fn.nres false ++ fs.l0.abs.drop fn.nparams)) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  have hcode := fr_code hT.2.1 h0
  have hle : fn.nparams ≤ fs.l0.ops.length := by rw [← absOk_length hT.2.2.2.1.1]; exact hn
  have hle' : fn.nparams ≤ (fs.l0.ops ++ fs.ls.flatMap Lvl.ops).length := by
    rw [List.length_append]; omega
  have hnimp : ¬ f.value.val < E.imps.length := by omega
  have hstep : stepB cap E c = .next (c.setTop
      (entry f.value.val fn (fs.l0.ops.take fn.nparams).reverse)
      ({ fr with ops := fs.l0.ops.drop fn.nparams ++ fs.ls.flatMap Lvl.ops
                 code := code ++ fs.ls.flatMap Lvl.code } :: frs)) := by
    rw [stepB_top hT.1 hcode (not_oob hT.1 hcode (by simp [accessAt]))]
    simp only [exec, ctlOf, hnimp, dite_false, hfn, fr_ops hT.2.1]
    rw [ite_eq_left_iff.2 (fun h => absurd hle' h), List.take_append_of_le_length hle,
      List.drop_append_of_le_length hle]
  rw [hstep]
  refine ⟨s, _, call_steps hT.2.2.2.2.2.1.1 hfn hf rfl hle h0, top_crel ⟨rfl, ?_, ?_,
    callee_ok hT.2.2.2.2.2.2 hfn (by rw [List.length_reverse, List.length_take]; omega),
    ⟨⟨List.forall₂_drop _ hT.2.2.2.1.1, hck, hT.2.2.2.1.2.2⟩, hT.2.2.2.2.1⟩,
    hT.2.2.2.2.2.1, hT.2.2.2.2.2.2⟩⟩
  · exact ⟨rfl, rfl, by simp [CFr.ops, calleeFr, entry], by simp [CFr.code, calleeFr, entry]⟩
  · exact .cons ⟨hT.2.1.1, hT.2.1.2.1, by simp [CFr.ops, callerFr],
      by simp [CFr.code, callerFr]⟩ hT.2.2.1

/-! ## Straight-line instructions -/

theorem seg_next (hT : Top cap E mi c s fr frs fs rest) {i : Instr} {code : List Instr}
    {a' : List Bool} (h0 : fs.l0.code = i :: code) (hctl : ctlOf i = none) (hoob : ¬ OOB cap c)
    (hS : SegStep Pf host cap E mi s fs.locals fs.l0.ops c.globals c.mem i a' (expression code))
    (hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) code a') :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  obtain ⟨ls', ops', gs', mem', s', hseg, hrun, hI', ha', hl'⟩ := hS
  have hcode := fr_code hT.2.1 h0
  have hstep : stepB cap E c = .next ⟨
      { fr with
        locals := ls'
        ops := ops' ++ fs.ls.flatMap Lvl.ops
        code := code ++ fs.ls.flatMap Lvl.code } :: frs, gs', mem'⟩ := by
    rw [stepB_top hT.1 hcode hoob]
    simp only [exec, hctl, Silmaril.Wasm.FX.Asyncify.Tool.Frame.ls, hT.2.1.1, fr_ops hT.2.1, hseg]
  have hctx : (⟨ls', fs.nres, ⟨ops', a', code⟩, fs.ls⟩ : CFr).ctx E = fs.ctx E := by
    simp only [CFr.ctx, hl']
  have hcore : Steps ⟨s, ⟨[], mi⟩, stackC mi (fs :: rest) []⟩
      ⟨s', ⟨[], mi⟩, stackC mi (⟨ls', fs.nres, ⟨ops', a', code⟩, fs.ls⟩ :: rest) []⟩ := by
    rw [stackC_cons, stackC_cons, admin_nil, admin_nil, h0]
    exact steps_top rest fs.ls hrun _
  rw [hstep]
  refine ⟨s', _, hcore, top_crel ⟨rfl, ⟨rfl, hT.2.1.2.1, rfl, rfl⟩, hT.2.2.1,
    ⟨ha', hctx ▸ hck, hctx ▸ hT.2.2.2.1.2.2⟩, hT.2.2.2.2.1, hI', hT.2.2.2.2.2.2⟩⟩

theorem seg_trapped (hT : Top cap E mi c s fr frs fs rest) {i : Instr} {code : List Instr}
    (h0 : fs.l0.code = i :: code) (hctl : ctlOf i = none) (hoob : ¬ OOB cap c)
    (hnone : segCore i ⟨fs.locals, fs.l0.ops ++ fs.ls.flatMap Lvl.ops, c.globals, c.mem⟩ = none)
    {ops : List W} {R : List Admin}
    (hcore : Steps ⟨s, localsF ⟨[], mi⟩ fs.locals, stackA fs.l0.ops ++ .plain i :: expression code⟩
      ⟨s, localsF ⟨[], mi⟩ fs.locals, stackA ops ++ .trap :: R⟩) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  have hcode := fr_code hT.2.1 h0
  have hstep : stepB cap E c = .trap := by
    rw [stepB_top hT.1 hcode hoob]
    simp only [exec, hctl, Silmaril.Wasm.FX.Asyncify.Tool.Frame.ls, hT.2.1.1, fr_ops hT.2.1, hnone]
  rw [hstep, stackC_cons, admin_nil, h0]
  exact ⟨_, (steps_top rest fs.ls (stackA_trap ops R ▸ hcore) _).trans (trap_top rest fs.ls _ R _),
    rfl⟩

theorem oob_trapped {i : Instr} {code : List Instr}
    (h0 : fs.l0.code = i :: code) (hoob : OOB cap c) {ops : List W} {R : List Admin}
    (hcore : Steps ⟨s, localsF ⟨[], mi⟩ fs.locals, stackA fs.l0.ops ++ .plain i :: expression code⟩
      ⟨s, localsF ⟨[], mi⟩ fs.locals, stackA ops ++ .trap :: R⟩) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  rw [stepB, ite_eq_left_iff.2 (fun h => absurd hoob h), stackC_cons, admin_nil, h0]
  exact ⟨_, (steps_top rest fs.ls (stackA_trap ops R ▸ hcore) _).trans (trap_top rest fs.ls _ R _),
    rfl⟩

/-- The access of the top frame's next instruction, from level 0's operands. -/
theorem access_l0 (hT : Top cap E mi c s fr frs fs rest) {i : Instr} {code : List Instr}
    (h0 : fs.l0.code = i :: code) : access c = accessAt i (fs.l0.ops ++ fs.ls.flatMap Lvl.ops) := by
  rw [access_top hT.1 (fr_code hT.2.1 h0), fr_ops hT.2.1]

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
