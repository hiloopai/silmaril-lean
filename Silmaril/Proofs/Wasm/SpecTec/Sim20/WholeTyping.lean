module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeBwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureSplit

/-!
# The structural rules of wasm-2.0 `Step` never produce administrative instructions

`Step/pure` and `Step/read` of the wasm-2.0 script quantify both sides as `instr*`
(`stepPureRule20`, `stepReadRule20`), and wasm-2.0 keeps administrative instructions in a separate
type `admininstr ⊋ instr`. So a step through either rule rewrites `instr` code to `instr` code
(`inv_pure20`, `inv_read20` record the typing), and every rule whose right-hand side contains
`TRAP`, `LABEL_`, `FRAME_` or `CALL_ADDR` is unreachable from `Step`:

* `instrHead_of_typed`: a typed 2.0 `instr` is an injection whose constructor is one of
  `instr`'s cases (read off the script); `trap_not_instr` etc.: `TRAP`, `LABEL_`, `FRAME_`,
  `CALL_ADDR` are not among them.
* `stuck_unreachable`: `z; UNREACHABLE` has no step in the wasm-2.0 script (its only
  `Step_pure` successor is `TRAP`), while V2 traps (`step_unreachable`). So the forward half of
  `Task.wholeStepValid` fails even on a single instruction, independently of the missing
  `ctxt-instrs` (`not_fwd_unreachable`).
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
open Silmaril.Wasm.SpecTec.Sim (RuleBody DDerives otherwise SStep SPure SRead Fires PremW ValsOnly cfgV
  evalExp_tup2 evalExp_list1 dderives_iff_fires fires_body ruleBody_scope)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (LhsIn TagsIn)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

variable (B : Builtins)

set_option maxRecDepth 100000

/-! ## The constructors of wasm-2.0 `instr` -/

/-- The cases of wasm-2.0's `instr` (`Scripts.Wasm20.Original.d133`). -/
noncomputable def instrCases20 : List TypCase :=
  match Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d133 with
  | .recD (.typD _ _ [.instD _ _ (.variantT cs)] :: _) => cs
  | _ => []

/-- The constructor of a case. -/
def caseHead : TypCase → MixopS
  | .mk o _ _ _ => o

set_option maxRecDepth 8000000 in
/-- wasm-2.0's `instr`, as `simEnv20 B` finds it. -/
theorem findTyp_instr20 : (simEnv20 B).findTyp? "instr" =
    some ([], [.instD [] [] (.variantT instrCases20)]) := rfl

/-- **A typed wasm-2.0 `instr` is an injection named by one of `instr`'s cases.** -/
theorem instrHead_of_typed {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv20 B) ρ (.varT "instr" []) v) :
    ∃ op w, v = .case op w ∧ op ∈ instrCases20.map caseHead := by
  have hl : localTyp? ρ "instr" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_instr20] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
    exact ⟨op, w, rfl, List.mem_map_of_mem (f := caseHead) hm⟩
  · exact absurd hrest not_hasTypInsts_nil

set_option maxRecDepth 8000000 in
/-- The administrative constructors are not `instr` constructors. -/
theorem admin_not_instr :
    "TRAP" ∉ instrCases20.map caseHead ∧ "LABEL_%{%}%" ∉ instrCases20.map caseHead ∧
      "FRAME_%{%}%" ∉ instrCases20.map caseHead ∧ "CALL_ADDR" ∉ instrCases20.map caseHead := by
  decide +kernel

/-- Every element of a typed `instr*` is an `instr` injection. -/
theorem instrHeads_of_typed {B : Builtins} {l : List Value}
    (h : TypedSome (simEnv20 B) instrsT20 (.list l)) :
    ∀ u ∈ l, ∃ op w, u = .case op w ∧ op ∈ instrCases20.map caseHead := by
  obtain ⟨ρ, hρ, ht⟩ := h
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 ht
  obtain rfl := (Value.list.inj hvs).symm
  exact fun u hu => instrHead_of_typed hρ (hasTypList_iff.1 hl u hu)

/-- `TRAP` is not an element of a typed `instr*`. -/
theorem trap_not_mem {B : Builtins} {l : List Value}
    (h : TypedSome (simEnv20 B) instrsT20 (.list l)) : caseNilV "TRAP" ∉ l := by
  intro hm
  obtain ⟨op, w, he, hop⟩ := instrHeads_of_typed h _ hm
  simp only [caseNilV, Value.case.injEq] at he
  exact admin_not_instr.1 (he.1 ▸ hop)

/-! ## `UNREACHABLE` -/

/-- The image of `unreachable`. -/
abbrev unreachableV : Value := caseNilV "UNREACHABLE"

/-- `UNREACHABLE` has its constructors among `UNREACHABLE`. -/
theorem tagsIn_unreachable : TagsIn ["UNREACHABLE"] [unreachableV] := by
  intro x hx op w hxw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  simp only [unreachableV, caseNilV, Value.case.injEq] at hxw
  simp [← hxw.1]

/-- `Step_pure/unreachable` at `UNREACHABLE` rewrites to `TRAP`. -/
theorem unreachableRule_rhs {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop}
    {b : Value} (h : RuleBody env D els [] [] "%~>%" Pure.unreachableRule
      (.tuple [.list [unreachableV], b])) : b = .list [caseNilV "TRAP"] := by
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope h
  have hn : EvalExp env (VarEnv.empty.bindVals σ)
      (.tupE [.listE [.caseE "UNREACHABLE" (.tupE [])], .listE [.caseE "TRAP" (.tupE [])]])
      (.tuple [.list [unreachableV], .list [caseNilV "TRAP"]]) :=
    evalExp_tup2 (evalExp_list1 Silmaril.Wasm.SpecTec.Sim20.Pure.evalExp_caseNil)
      (evalExp_list1 Silmaril.Wasm.SpecTec.Sim20.Pure.evalExp_caseNil)
  have hu := EvalExp.unique he hn
  simp only [Value.tuple.injEq, List.cons.injEq, and_true, true_and] at hu
  exact hu

/-- **The only `Step_pure` successor of `UNREACHABLE` is `TRAP`.** -/
theorem spure_unreachable {js : List Value}
    (h : SPure (simEnv20 B) [unreachableV] js) : js = [caseNilV "TRAP"] := by
  obtain ⟨ps, t, rules, hrel, rfl, h0⟩ := Pure.hasRuleAt_unreachable B
  by_contra hne
  refine not_dderives_of_table hrel (T := pureTags20)
    (by rw [relRules_simEnv20]; exact pureTags20_eq) (S := ["UNREACHABLE"]) (exc := [0])
    (Or.inl ⟨_, rfl, tagsIn_unreachable⟩) (by decide) ?_ h
  intro i hi r hr hb
  obtain rfl : i = 0 := List.mem_singleton.1 hi
  rw [h0] at hr
  obtain rfl := (Option.some.inj hr).symm
  exact hne (Value.list.inj (unreachableRule_rhs hb))

/-- `Step_read` has no step from `z; UNREACHABLE`. -/
theorem not_sread_unreachable (z w : Value) :
    ¬ DDerives (simEnv20 B) (otherwise (simEnv20 B)) "Step_read" "%~>%" []
      (.tuple [cfgV z [unreachableV], w]) := by
  obtain ⟨t, rules, hrel⟩ := findRel_read20 B
  exact not_dderives_of_table hrel (T := readTags20)
    (by rw [relRules_simEnv20]; exact readTags20_eq) (S := ["UNREACHABLE"]) (exc := [])
    (Or.inr ⟨z, _, rfl, tagsIn_unreachable⟩) (by decide) (fun _ h => absurd h List.not_mem_nil)

/-- `Step/pure` does not fire at `z; UNREACHABLE`: its successor would have to be the
`instr*` sequence `TRAP`. -/
theorem not_fires_stepPure_unreachable (z w : Value) :
    ¬ Fires (simEnv20 B) "Step" 0 (.tuple [cfgV z [unreachableV], w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, -, tj, hp⟩ := inv_pure20 (hasRuleAt_stepPure B) hf
  have e₁ : [unreachableV] = is := (Silmaril.Wasm.SpecTec.Sim.Bwd.cfgV_inj h₁).2
  have hjs : js = [caseNilV "TRAP"] := spure_unreachable B (e₁ ▸ hp)
  exact trap_not_mem tj (hjs ▸ List.mem_singleton_self _)

/-- `Step/read` does not fire at `z; UNREACHABLE`. -/
theorem not_fires_stepRead_unreachable (z w : Value) :
    ¬ Fires (simEnv20 B) "Step" 1 (.tuple [cfgV z [unreachableV], w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, -, -, hp⟩ := inv_read20 (hasRuleAt_stepRead B) hf
  have hp' : SRead (simEnv20 B) (cfgV z [unreachableV]) js := h₁ ▸ hp
  exact not_sread_unreachable B z _ hp'

/-- The `Step` rules from `ctxt-label` on force a constructor other than `UNREACHABLE`. -/
theorem not_fires_step_tag_unreachable (k : Nat) (z w : Value) :
    ¬ Fires (simEnv20 B) "Step" (k + 2) (.tuple [cfgV z [unreachableV], w]) := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hT : rules.map Silmaril.Wasm.SpecTec.Sim.RefsGC.ruleTags = stepTags20 := by
    have h₀ := stepTags20_eq
    rw [← relRules_simEnv20 B] at h₀
    simpa [Silmaril.Wasm.SpecTec.Sim.RefsGC.relRules, hrel] using h₀
  have hlt : k + 2 < stepTags20.length := by
    rw [← hT, List.length_map]
    exact (List.getElem?_eq_some_iff.1 hr).1
  have htag : stepTags20[k + 2]?.getD [] = Silmaril.Wasm.SpecTec.Sim.RefsGC.ruleTags r := by
    rw [← hT, List.getElem?_map, hr]
    rfl
  obtain ⟨op, hop, hS⟩ : ∃ op ∈ stepTags20[k + 2]?.getD [], op ∉ ["UNREACHABLE"] :=
    Silmaril.Wasm.SpecTec.Sim.RefsGC.checkAvoid_sound (T := stepTags20) (i := stepTags20.length)
      (exc := [0, 1]) (S := ["UNREACHABLE"]) (by decide) hlt (by simp)
  exact Silmaril.Wasm.SpecTec.Sim.RefsGC.not_ruleBody_of_tags
    (Or.inr ⟨z, _, rfl, tagsIn_unreachable⟩) (htag ▸ hop) hS hb

/-- **`z; UNREACHABLE` is stuck in the wasm-2.0 script**: `Step/pure` would need `TRAP` to be an
`instr`. -/
theorem not_sstep_unreachable (z w : Value) :
    ¬ SStep (simEnv20 B) (cfgV z [unreachableV]) w := by
  intro hs
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_stepPure B
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf => exact not_fires_stepPure_unreachable B z w hf
  | 1, hf => exact not_fires_stepRead_unreachable B z w hf
  | k + 2, hf => exact not_fires_step_tag_unreachable B k z w hf

/-- `z; UNREACHABLE` is stuck under the backend reading. -/
theorem stuck_unreachable (z w : Value) : ¬ SStepB (simEnv20 B) (cfgV z [unreachableV]) w :=
  fun h => not_sstep_unreachable B z w ((sstepB20_iff B).1 h)

/-! ## V2 traps -/

variable {H : Type}

/-- **V2 reduces `unreachable` to `trap`.** -/
theorem step_unreachable (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) :
    Step P host ⟨s, f, [.plain .unreachable]⟩ ⟨s, f, [.trap]⟩ :=
  .pure .unreachable

set_option maxHeartbeats 4000000 in
/-- The image of `unreachable` in the empty store and frame is IL-typed. -/
theorem typed20_unreachable (hn : H → String) :
    Typed20 (simEnv20 B) hn ⟨{}, {}, [.plain .unreachable]⟩ :=
  ⟨40, by with_unfolding_all rfl⟩

/-- **The forward half fails on one instruction**: for every primitives `B`, `unreachable`
(typed image) has a V2 step and no wasm-2.0 step. -/
theorem not_fwd_unreachable {H : Type} (hn : H → String) (P : Profile)
    (host : HostSemantics H) :
    Typed20 (simEnv20 B) hn ⟨{}, {}, [.plain .unreachable]⟩ ∧
      Step P host ⟨{}, {}, [.plain .unreachable]⟩ ⟨{}, {}, [.trap]⟩ ∧
      ∀ w, ¬ SStepB (simEnv20 B) (configV hn ⟨{}, {}, [.plain .unreachable]⟩) w :=
  ⟨typed20_unreachable B hn, step_unreachable P host {} {}, fun w => stuck_unreachable B _ w⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
