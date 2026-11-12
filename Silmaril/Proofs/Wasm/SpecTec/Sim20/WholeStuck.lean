module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeTags
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureBasic

/-!
# The 2.0 whole-step target is false: `NOP NOP` is stuck in the wasm-2.0 script

The wasm-2.0 script has no `Step/ctxt-instrs` (V2's documented deviation 1,
`Silmaril.Wasm.V2.Execution.Step`): its only context rules are `ctxt-label` and `ctxt-frame`.
So an instruction sequence reduces in SpecTec 2.0 only when a single rule rewrites the whole
sequence. At `z; NOP NOP` no rule of `Step` applies:

* `Step/pure` needs a `Step_pure` step of `NOP NOP`; every `Step_pure` rule but `nop` forces a
  constructor other than `NOP`, and `nop` rewrites the one-element sequence `NOP`
  (`not_spure_nopNop`);
* `Step/read` needs a `Step_read` step, and every `Step_read` rule forces another constructor
  (`not_sread_nopNop`);
* rules 2–21 force another constructor.

Hence `stuck_nopNop : ¬ SStepB (simEnv20 B) (cfgV z [NOP, NOP]) w` for every state `z`, every
`w` and every primitives `B`. V2 reduces `nop nop` to `nop` (`step_nopNop`, by `Step.ctxtInstrs`),
at a configuration whose image is typed (`typed20_nopNop`), so the forward half of
`Sim20.Task.wholeStepValid` fails: `not_wholeStepValid`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm.SpecTec.Sim (RuleBody DDerives otherwise SStep PremW cfgV evalExp_tup2
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (LhsIn TagsIn)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

variable (B : Builtins)

set_option maxRecDepth 100000

/-! ## Evaluation helpers -/

/-- A pair, read back. -/
theorem evalExp_tup2_cases {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) :
    ∃ v₁ v₂, v = .tuple [v₁, v₂] ∧ EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, ws, rfl, h₁, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', rfl, h₂, hws'⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hws'
  exact ⟨w₁, w₂, rfl, h₁, h₂⟩

/-- The code of an evaluated `z; code` pattern. -/
theorem evalExp_cfg_code {env : Env} {ρ : VarEnv} {ez ec : Exp} {z : Value} {l : List Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [ez, ec])) (cfgV z l)) :
    EvalExp env ρ ec (.list l) := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  obtain ⟨v₁, v₂, rfl, -, h₂⟩ := evalExp_tup2_cases hu
  simp only [cfgV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at hcu
  rw [hcu.2.1]
  exact h₂

/-- A rule instance of a relation without parameters binds nothing but its quantifiers. -/
theorem bindParams_nil {ρ₀ : VarEnv} (h : bindParams VarEnv.empty [] [] = some ρ₀) :
    ρ₀ = VarEnv.empty :=
  (Option.some.inj h).symm

/-! ## `NOP NOP` -/

/-- The image of `nop`. -/
abbrev nopV : Value := caseNilV "NOP"

theorem instrToV_nop : instrToV .nop = nopV := rfl

/-- `NOP NOP` has its constructors among `NOP`. -/
theorem tagsIn_nopNop : TagsIn ["NOP"] [nopV, nopV] := by
  intro x hx op w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
  subst hx
  simp only [nopV, caseNilV, Value.case.injEq] at hxw
  simp [← hxw.1]

/-- `Step_pure/nop` rewrites the one-element sequence `NOP`, not `NOP NOP`. -/
theorem not_nopRule_nopNop {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop}
    {b : Value} :
    ¬ RuleBody env D els [] [] "%~>%" Pure.nopRule (.tuple [.list [nopV, nopV], b]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, -⟩
  have hn : EvalExp env (ρ₀.bindVals σ) (.tupE [.listE [.caseE "NOP" (.tupE [])], .listE []])
      (.tuple [.list [nopV], .list []]) :=
    evalExp_tup2 (evalExp_list1 Silmaril.Wasm.SpecTec.Sim20.Pure.evalExp_caseNil) Silmaril.Wasm.SpecTec.Sim20.Pure.evalExp_list0
  have hu := EvalExp.unique he hn
  simp at hu

/-- **`Step_pure` has no step from `NOP NOP`.** -/
theorem not_spure_nopNop (w : Value) :
    ¬ DDerives (simEnv20 B) (otherwise (simEnv20 B)) "Step_pure" "%~>%" []
      (.tuple [.list [nopV, nopV], w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, h1⟩ := Pure.hasRuleAt_nop B
  refine not_dderives_of_table hrel (T := pureTags20)
    (by rw [relRules_simEnv20]; exact pureTags20_eq) (S := ["NOP"]) (exc := [1]) (Or.inl ⟨_, rfl, tagsIn_nopNop⟩) (by decide) ?_
  intro i hi r hr
  obtain rfl : i = 1 := List.mem_singleton.1 hi
  rw [h1] at hr
  obtain rfl := (Option.some.inj hr).symm
  exact not_nopRule_nopNop

/-- **`Step_read` has no step from `z; NOP NOP`.** -/
theorem not_sread_nopNop (z w : Value) :
    ¬ DDerives (simEnv20 B) (otherwise (simEnv20 B)) "Step_read" "%~>%" []
      (.tuple [cfgV z [nopV, nopV], w]) := by
  obtain ⟨t, rules, hrel⟩ := findRel_read20 B
  exact not_dderives_of_table hrel (T := readTags20)
    (by rw [relRules_simEnv20]; exact readTags20_eq) (S := ["NOP"]) (exc := []) (Or.inr ⟨z, _, rfl, tagsIn_nopNop⟩) (by decide)
    (fun _ h => absurd h List.not_mem_nil)

/-- `Step/pure` does not fire at `z; NOP NOP`. -/
theorem not_stepPure_nopNop {els : Prop} (z w : Value) :
    ¬ RuleBody (simEnv20 B) (DDerives (simEnv20 B) (otherwise (simEnv20 B))) els [] [] "%~>%"
      stepPureRule20 (.tuple [cfgV z [nopV, nopV], w]) := by
  rintro ⟨-, ρ₀, σ, hps, -, he, hp⟩
  obtain ⟨v₁, v₂, hv, h₁, -⟩ := evalExp_tup2_cases he
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv
  rw [← hv.1] at h₁
  have hc := evalExp_cfg_code h₁
  cases hp _ (List.mem_singleton_self _) with
  | rulePr ha he' hd =>
    obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 ha
    obtain ⟨u₁, u₂, rfl, hu₁, -⟩ := evalExp_tup2_cases he'
    obtain rfl := EvalExp.unique hu₁ hc
    exact not_spure_nopNop B u₂ hd

/-- `Step/read` does not fire at `z; NOP NOP`. -/
theorem not_stepRead_nopNop {els : Prop} (z w : Value) :
    ¬ RuleBody (simEnv20 B) (DDerives (simEnv20 B) (otherwise (simEnv20 B))) els [] [] "%~>%"
      stepReadRule20 (.tuple [cfgV z [nopV, nopV], w]) := by
  rintro ⟨-, ρ₀, σ, hps, -, he, hp⟩
  obtain ⟨v₁, v₂, hv, h₁, -⟩ := evalExp_tup2_cases he
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv
  rw [← hv.1] at h₁
  cases hp _ (List.mem_singleton_self _) with
  | rulePr ha he' hd =>
    obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 ha
    obtain ⟨u₁, u₂, rfl, hu₁, -⟩ := evalExp_tup2_cases he'
    obtain rfl := EvalExp.unique hu₁ h₁
    exact not_sread_nopNop B z u₂ hd

/-- **`z; NOP NOP` is stuck in the wasm-2.0 script, declaratively.** -/
theorem not_sstep_nopNop (z w : Value) : ¬ SStep (simEnv20 B) (cfgV z [nopV, nopV]) w := by
  obtain ⟨ps, t, rules, hrel, rfl, h0⟩ := hasRuleAt_stepPure B
  have h1 := hasRuleAt_stepRead B
  obtain ⟨ps', t', rules', hrel', rfl, h1⟩ := h1
  rw [hrel] at hrel'
  obtain rfl : rules = rules' := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
    exact hrel'.2.2.2
  refine not_dderives_of_table hrel (T := stepTags20)
    (by rw [relRules_simEnv20]; exact stepTags20_eq) (S := ["NOP"]) (exc := [0, 1]) (Or.inr ⟨z, _, rfl, tagsIn_nopNop⟩) (by decide) ?_
  intro i hi r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · rw [h0] at hr
    obtain rfl := (Option.some.inj hr).symm
    exact not_stepPure_nopNop B z w
  · rw [h1] at hr
    obtain rfl := (Option.some.inj hr).symm
    exact not_stepRead_nopNop B z w

/-- **`z; NOP NOP` is stuck in the wasm-2.0 script, under the backend reading.** -/
theorem stuck_nopNop (z w : Value) : ¬ SStepB (simEnv20 B) (cfgV z [nopV, nopV]) w :=
  fun h => not_sstep_nopNop B z w ((sstepB20_iff B).1 h)

/-! ## V2 reduces `nop nop` -/

variable {H : Type}

/-- The image of a `nop nop` configuration. -/
theorem configV_nopNop (hn : H → String) (s : Store H) (f : Frame) :
    configV hn ⟨s, f, [.plain .nop, .plain .nop]⟩ = cfgV (stateV hn s f) [nopV, nopV] := rfl

/-- **V2 reduces `nop nop` to `nop`**, by `Step.ctxtInstrs` (deviation 1). -/
theorem step_nopNop (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) :
    Step P host ⟨s, f, [.plain .nop, .plain .nop]⟩ ⟨s, f, [.plain .nop]⟩ := by
  have h := Step.ctxtInstrs (vs := []) (rest := [.plain .nop]) (host := host)
    (Step.pure (s := s) (f := f) (PureStep.nop (P := P))) (Or.inr (by simp))
  simpa [vals] using h

set_option maxHeartbeats 4000000 in
/-- The image of `nop nop` in the empty store and frame is IL-typed. -/
theorem typed20_nopNop (hn : H → String) :
    Typed20 (simEnv20 B) hn ⟨{}, {}, [.plain .nop, .plain .nop]⟩ :=
  ⟨40, by with_unfolding_all rfl⟩

/-- **The 2.0 whole-step target, refuted**: V2 steps from `nop nop`, whose image is typed and
stuck, at every `B`. -/
theorem not_wholeStepValid : ¬ Task.wholeStepValid := by
  intro h
  obtain ⟨B, hf, -⟩ := h Empty Empty.elim (fun a => a.elim) (fun _ _ _ _ => False) false {}
  obtain ⟨c'', -, -, hs⟩ := hf _ _ (typed20_nopNop B Empty.elim)
    (step_nopNop _ _ {} {})
  exact stuck_nopNop B _ _ hs

end Silmaril.Wasm.SpecTec.Sim20.Whole
