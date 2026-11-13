module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Calm.Basic

/-!
# Calm runs never call an import

From calm frames (`CalmCfg`), a machine step never asks the host (`calm_step`), and calmness is
kept (`calm_next`): a pure instruction moves along the body, a call statement of a calm function
calls a calm defined function (`calm_calls`) whose frame starts at its body, a return drops the
top frame. So a source run from calm frames never consults the host (`calm_runN`), and its
behaviours are the same under every host (`calm_beh_host`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- The top frame moved past instruction `i` of its body, with other locals and operands. -/
theorem calmCfg_top {P : Prog} {c : Cfg} {fr : Frame} {rest : List Frame} {i : Instr}
    {code : List Instr} (hc : CalmCfg P c) (hf : c.frames = fr :: rest)
    (hcode : fr.code = i :: code) (ls ops : List W) (gs : List W) (m : Nat → W) :
    CalmCfg P ⟨{ fr with locals := ls, ops := ops, code := code } :: rest, gs, m⟩ := by
  intro g hg
  simp only [List.mem_cons] at hg
  rcases hg with rfl | hg
  · obtain ⟨fn, h1, h2, h3, pre, h4⟩ := hc fr (by simp [hf])
    refine ⟨fn, h1, h2, h3, pre ++ [i], ?_⟩
    rw [← h4, hcode]; simp
  · exact hc g (by simp [hf, hg])

/-- What `calm_step` claims of a step result. -/
def CalmRes (P : Prog) (r : Res) : Prop :=
  (∀ f args c', r ≠ .ask f args c') ∧ (∀ c', r = .next c' → CalmCfg P c')

theorem calmRes_trap (P : Prog) : CalmRes P .trap :=
  ⟨fun _ _ _ h => (by cases h), fun _ h => (by cases h)⟩

theorem calm_step_pure {P : Prog} {c : Cfg} {fr : Frame} {rest : List Frame} {i : Instr}
    {code : List Instr} {S : Nat} (hc : CalmCfg P c) (hfr : c.frames = fr :: rest)
    (hcode : fr.code = i :: code) (hi : PureShape S i) : CalmRes P (step P.env c) := by
  have hctl : ctlOf i = none := ctlOf_pure hi
  cases hs : segStep i (fr.ls c) with
  | none => rw [step_trap_seg hfr hcode hctl hs]; exact calmRes_trap P
  | some s' =>
    rw [step_seg (E := P.env) hfr hcode hs]
    refine ⟨fun f args c' h => (by cases h), fun c' h => ?_⟩
    rw [← Res.next.inj h]
    exact calmCfg_top hc hfr hcode s'.locals s'.ops s'.globals s'.mem

/-- The frames after a calm call: the callee's entry frame and the caller past its `call`. -/
theorem calmCfg_call {P : Prog} {c : Cfg} {fr : Frame} {rest : List Frame} {g : FuncIdx}
    {code : List Instr} {fn' : FnSrc} (hc : CalmCfg P c) (hfr : c.frames = fr :: rest)
    (hcode : fr.code = .call g :: code) (hgc : mayS P g.value.val = false)
    (hfn' : P.fnAt g.value.val = some fn') (args ops : List W) :
    CalmCfg P ⟨entry g.value.val ⟨fn'.nparams, fn'.nlocals, fn'.nres, fn'.body⟩ args ::
      { fr with ops := ops, code := code } :: rest, c.globals, c.mem⟩ := by
  have hge : P.imps.length ≤ g.value.val := calm_defined hgc
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · have hfa : P.fns[g.value.val - P.imps.length]? = some fn' := by
      unfold Prog.fnAt at hfn'; simpa [hge] using hfn'
    exact ⟨fn', hge, hfa, hgc, [], by simp [entry, FnSrc.body]⟩
  · obtain ⟨fn0, h1, h2, h3, pre, h4⟩ := hc fr (by simp [hfr])
    exact ⟨fn0, h1, h2, h3, pre ++ [.call g], by rw [← h4, hcode]; simp⟩
  · exact hc x (by simp [hfr, hx])

theorem calm_step_call {P : Prog} {c : Cfg} {fr : Frame} {rest : List Frame}
    {g : FuncIdx} {code : List Instr} {fn : FnSrc} {as rs : List LocalIdx} (hc : CalmCfg P c)
    (hfr : c.frames = fr :: rest) (hcode : fr.code = .call g :: code) (hok : FnOk P fn)
    (hgc : mayS P g.value.val = false) (hg : Stmt.call g as rs ∈ fn.stmts) :
    CalmRes P (step P.env c) := by
  have hge : P.imps.length ≤ g.value.val := calm_defined hgc
  obtain ⟨hsig, -, -⟩ := Stmt.wf_call (hok.stmts _ hg)
  obtain ⟨fn', hfn', -, -⟩ := Prog.sig_fn hsig hge
  have himp : ¬ g.value.val < P.env.imps.length := Nat.not_lt.2 hge
  have hd := Prog.env_fn hfn'
  by_cases hn : fn'.nparams ≤ fr.ops.length
  · rw [step_call_def (E := P.env) hfr hcode himp hd hn]
    refine ⟨fun f args c' h => (by cases h), fun c' h => ?_⟩
    rw [← Res.next.inj h]
    exact calmCfg_call hc hfr hcode hgc hfn' _ _
  · have ht : step P.env c = .trap := by
      simp [step, hfr, hcode, exec, ctlOf, himp, hd, hn]
    rw [ht]; exact calmRes_trap P

theorem calm_step_ins {P : Prog} (hP : P.WF) {c : Cfg} {fr : Frame} {rest : List Frame}
    {i : Instr} {code : List Instr} (hc : CalmCfg P c) (hfr : c.frames = fr :: rest)
    (hcode : fr.code = i :: code) : CalmRes P (step P.env c) := by
  obtain ⟨fn, hge, hfn, hcalm, pre, hpre⟩ := hc fr (by simp [hfr])
  have hi : i ∈ fn.body := by rw [← hpre, hcode]; simp
  have hok := Prog.fnOk hP (calm_fnAt hge hfn)
  rcases body_shape hok hi with hp | ⟨g, as, rs, rfl, hg⟩
  · exact calm_step_pure hc hfr hcode (pureShape hp)
  · exact calm_step_call hc hfr hcode hok (calm_calls hcalm hfn hg) hg

theorem calm_step_ret {P : Prog} {c : Cfg} {fr : Frame} {rest : List Frame} (hc : CalmCfg P c)
    (hfr : c.frames = fr :: rest) (hcode : fr.code = []) : CalmRes P (step P.env c) := by
  rw [step_ret hfr hcode]
  refine ⟨fun f args c' h => ?_, fun c' h => calmCfg_ret hc hfr c' h⟩
  cases rest <;> cases h

/-- **One step from calm frames**: no import call, and the frames stay calm. -/
theorem calm_step {P : Prog} (hP : P.WF) {c : Cfg} (hc : CalmCfg P c) :
    CalmRes P (step P.env c) := by
  cases hfr : c.frames with
  | nil =>
    have ht : step P.env c = .trap := by simp [step, hfr]
    rw [ht]; exact calmRes_trap P
  | cons fr rest =>
    cases hcode : fr.code with
    | nil => exact calm_step_ret hc hfr hcode
    | cons i code => exact calm_step_ins hP hc hfr hcode

/-- A source step from calm frames does not depend on the host, and keeps the frames calm. -/
theorem calm_srcStep {P : Prog} (hP : P.WF) {c : Cfg} (hc : CalmCfg P c) (H H' : Host σ) (s : σ) :
    srcStep P.env H (c, s) = srcStep P.env H' (c, s) ∧
      ∀ y, srcStep P.env H (c, s) = .next y → y.2 = s ∧ CalmCfg P y.1 := by
  obtain ⟨hask, hnext⟩ := calm_step hP hc
  cases hs : step P.env c with
  | next c' =>
    refine ⟨by simp only [srcStep, hs], fun y hy => ?_⟩
    simp only [srcStep, hs] at hy
    rw [← SRes.next.inj hy]
    exact ⟨rfl, hnext c' hs⟩
  | done vs c' =>
    refine ⟨by simp only [srcStep, hs], fun y hy => ?_⟩
    simp only [srcStep, hs] at hy
    cases hy
  | trap =>
    refine ⟨by simp only [srcStep, hs], fun y hy => ?_⟩
    simp only [srcStep, hs] at hy
    cases hy
  | ask f args c' => exact absurd hs (hask f args c')

/-- **A source run from calm frames never consults the host**: the host state is unchanged and
the runs under any two hosts agree. -/
theorem calm_runN {P : Prog} (hP : P.WF) (H H' : Host σ) :
    ∀ (n : Nat) (c : Cfg) (s : σ), CalmCfg P c →
      runN (srcStep P.env H) n (c, s) = runN (srcStep P.env H') n (c, s) ∧
      ∀ y, runN (srcStep P.env H) n (c, s) = .next y → y.2 = s ∧ CalmCfg P y.1
  | 0, c, s, hc => ⟨rfl, fun y hy => by cases hy; exact ⟨rfl, hc⟩⟩
  | n + 1, c, s, hc => by
    obtain ⟨heq, hnx⟩ := calm_srcStep hP hc H H' s
    cases hs : srcStep P.env H (c, s) with
    | stop o =>
      refine ⟨by simp only [runN, hs, ← heq], fun y hy => ?_⟩
      simp only [runN, hs] at hy
      cases hy
    | next y =>
      obtain ⟨hy2, hy1⟩ := hnx y hs
      obtain ⟨c', s'⟩ := y
      simp only at hy2
      subst hy2
      obtain ⟨ih1, ih2⟩ := calm_runN hP H H' n c' s' hy1
      exact ⟨by simp only [runN, hs, ← heq, ih1], fun y hy => by
        simp only [runN, hs] at hy
        exact ih2 y hy⟩

end Silmaril.Wasm.FX.Asyncify.Tool
