module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMAtom.Sound
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMAtom.Check

/-!
# Round 9, rm: the flat rules are silent at memory SIMD code

* `adminsMS_of_atomCfg`, `adminsMS_of_atomPure`: a flat rule fires only at code without memory
  SIMD instructions;
* `read_adminsMS`, `step_adminsMS`, `pure_adminsMS`: the same for every rule of `Step_read`
  outside `structRead` and 42–51, of `Step` from 6 on outside 22–25, and of `Step_pure` outside
  `structPure` (kernel checks `readAtoms`, `stepAtoms`, `pureAtoms`);
* `restMSHCG_of_H`, `openRMRestDPG_of_H`, `wholeStepValidRM_of_restDPH`: so `RMCall.RestMSHCG`
  follows from `RestMSHCH`, whose `step` field is gone and whose `pure` and `read` fields are
  asked only at the 15 + 16 rules that are not flat.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminMS AdminsMS)
open Round7.MemSimd (configVD adminsToVD)

variable {H : Type} {B : Builtins}

/-- **A flat rule `z; ce ~> _` fires only at code without memory SIMD instructions.** -/
theorem adminsMS_of_atomCfg {D : Interp} {els : Prop} {hn : H → String} {r : Rule}
    (hr : atomCfg r = true) {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" r (.tuple [configVD hn c, w])) :
    AdminsMS c.code := by
  unfold atomCfg at hr
  split at hr
  · rename_i nm qs op ez ce er prems
    obtain ⟨σ, hq, he, -⟩ := ruleBody_scope hb
    have hl := (Exn.evalExp_tup2_inv he).1
    obtain ⟨u, hu, hc⟩ := evalExp_caseE_iff.1 hl
    have hu' : u = .tuple [Round7.MemSimd.stateVD hn c.store c.frame, .list (adminsToVD c.code)] :=
      (Value.case.inj hc).2.symm
    have hce : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) ce (.list (adminsToVD c.code)) :=
      (Exn.evalExp_tup2_inv (hu' ▸ hu)).2
    obtain ⟨l, hl', hall⟩ := atomCode_sound (valsOnly_bindVals σ) hq ce hr hce
    exact adminsMS_of_atoms ((Value.list.inj hl') ▸ hall)
  · cases hr

/-- **A flat rule `ce ~> _` fires only at code without memory SIMD instructions.** -/
theorem adminsMS_of_atomPure {D : Interp} {els : Prop} {r : Rule} (hr : atomPure r = true)
    {is : List Admin} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" r (.tuple [.list (adminsToVD is), w])) :
    AdminsMS is := by
  unfold atomPure at hr
  split at hr
  · rename_i nm qs op ce er prems
    obtain ⟨σ, hq, he, -⟩ := ruleBody_scope hb
    have hce : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) ce (.list (adminsToVD is)) :=
      (Exn.evalExp_tup2_inv he).1
    obtain ⟨l, hl', hall⟩ := atomCode_sound (valsOnly_bindVals σ) hq ce hr hce
    exact adminsMS_of_atoms ((Value.list.inj hl') ▸ hall)
  · cases hr

/-- An index outside `skip` of a rule list passing `allBut skip f` names a rule passing `f`. -/
theorem allBut_get {skip : List Nat} {f : Rule → Bool} {rules : List Rule} {i : Nat} {r : Rule}
    (h : allBut skip f rules = true) (hi : rules[i]? = some r) (hs : i ∉ skip) : f r = true := by
  have hlt : i < rules.length := (List.getElem?_eq_some_iff.1 hi).1
  have hall := List.all_eq_true.1 h i (List.mem_range.2 hlt)
  simp only [hi, Bool.or_eq_true, List.contains_iff_mem] at hall
  exact hall.resolve_left hs

/-- **A firing of a relation all of whose rules outside `skip` pass `f`**, at an index outside
`skip`, is the body of a rule passing `f`. -/
theorem fires_allBut {x : IL.Id} {i : Nat} {v : Value} {skip : List Nat} {f : Rule → Bool}
    (hchk : ∃ t rules, (simEnv B).findRel? x = some ([], "%~>%", t, rules) ∧
      allBut skip f rules = true)
    (hs : i ∉ skip) (hf : Fires (simEnv B) x i v) :
    ∃ r, f r = true ∧ RuleBody (simEnv B) (DDerives (simEnv B) (otherwise (simEnv B)))
      (otherwise (simEnv B) x [] i v) [] [] "%~>%" r v := by
  obtain ⟨t, rules, r, hrel, hri, hb⟩ := hf
  obtain ⟨t', rules', hrel', hall⟩ := hchk
  have e : rules' = rules := by
    rw [hrel] at hrel'
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hrel'
    exact hrel'.2.symm
  exact ⟨r, allBut_get (e ▸ hall) hri hs, hb⟩

/-- **`Step_read` outside `structRead` and 42–51 fires only at code without memory SIMD.** -/
theorem read_adminsMS {hn : H → String} {i : Nat} (h₁ : i ∉ structRead)
    (h₂ : i ∉ Round7.MemSimd.msReadRules) {c : Config H} {w : Value}
    (hf : Fires (simEnv B) "Step_read" i (.tuple [configVD hn c, w])) : AdminsMS c.code := by
  have hs : i ∉ structRead ++ Round7.MemSimd.msReadRules := by
    simp only [List.mem_append, not_or]; exact ⟨h₁, h₂⟩
  obtain ⟨r, hr, hb⟩ := fires_allBut (readAtoms B) hs hf
  exact adminsMS_of_atomCfg hr hb

/-- **`Step` from 6 on outside 22–25 fires only at code without memory SIMD.** -/
theorem step_adminsMS {hn : H → String} {i : Nat} (h₆ : 6 ≤ i)
    (h₂ : i ∉ Round7.MemSimd.stepMSRules) {c : Config H} {w : Value}
    (hf : Fires (simEnv B) "Step" i (.tuple [configVD hn c, w])) : AdminsMS c.code := by
  have hs : i ∉ [0, 1, 2, 3, 4, 5] ++ Round7.MemSimd.stepMSRules := by
    simp only [List.mem_append, not_or]
    refine ⟨fun hm => ?_, h₂⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  obtain ⟨r, hr, hb⟩ := fires_allBut (stepAtoms B) hs hf
  exact adminsMS_of_atomCfg hr hb

/-- **`Step_pure` outside `structPure` fires only at code without memory SIMD.** -/
theorem pure_adminsMS {i : Nat} (h₁ : i ∉ structPure) {is : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" i (.tuple [.list (adminsToVD is), w])) : AdminsMS is := by
  obtain ⟨r, hr, hb⟩ := fires_allBut (pureAtoms B) h₁ hf
  exact adminsMS_of_atomPure hr hb

/-! ## The reduction -/

variable {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`RestMSHCH` gives `RMCall.RestMSHCG`**: the flat rules cannot fire at code holding a
memory SIMD instruction. -/
theorem restMSHCG_of_H (h : RestMSHCH hn P host) : RMCall.RestMSHCG hn P host where
  pure := by
    intro i s f is w hms hv ht hf
    by_cases hi : i ∈ structPure
    · exact h.pure i hi s f is w hms hv ht hf
    · exact absurd (pure_adminsMS hi hf) hms
  read := by
    intro i hmr c w hms hv ht hf
    by_cases hi : i ∈ structRead
    · exact h.read i hi c w hms hv ht hf
    · exact absurd (read_adminsMS hi hmr hf) hms
  step := by
    intro i h6 hmr _ _ _ c w hms _ _ hf
    exact absurd (step_adminsMS h6 hmr hf) hms
  firesRead := h.firesRead

/-- **`OpenRMRestDPH` gives `RMCall.OpenRMRestDPG`.** -/
theorem openRMRestDPG_of_H (O : OpenRMRestDPH hn P host) : RMCall.OpenRMRestDPG hn P host :=
  ⟨O.forward, restMSHCG_of_H O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPH`.** -/
theorem wholeStepValidRM_of_restDPH
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPH hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMCall.wholeStepValidRM_of_restDPG fun H hn hinj host hf hh nd r =>
    openRMRestDPG_of_H (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom
