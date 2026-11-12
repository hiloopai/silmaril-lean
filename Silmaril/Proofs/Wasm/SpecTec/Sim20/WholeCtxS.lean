module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVStore
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StepFixRun

/-!
# Below the top of the code: the forward 2.0 half through the `Step` erratum

The forward fragments `TopStep20` … `TopVStep20` are top-level: the redex is the whole code. The
wasm-2.0 script cannot do better, since it has no `ctxt-instrs` rule and types the structural rules'
code `instr*` (`Whole.stuck_nopNop`, `Whole.not_fwd_noCtxt`). Pass 7's erratum `stepErratum20`
(`Sim20.StepFix.Defs`) adds `ctxt-instrs` and types the code `admininstr*`; its `Step` keeps rules
4–21 verbatim, shifted by one (the five structural rules come first). This module states and
proves the route from the top-level fragment to redexes under a value prefix and a suffix, in
`simEnv20S`:

* `fires_topVStep20`: every `TopVStep20` step fires one of `Step` 4–21 of the original script, at
  `GrowCalls20` builtins (the case analysis of `fwd_topVStep20`, keeping the rule index);
* `typedV_code_of_typed20`: the code of a typed configuration is a typed `admininstr*`;
* **`StepAgreeS B`, `TypAgreeS B`** (open hypotheses): rules 4–21 fire alike in `simEnv20 B` and,
  one index later, in `simEnv20S B`, and `state`, `admininstr*`, `val*` type alike. Both
  environments have the same type, definition and builtin tables. Only the relation `Step`
  differs, so this is a transfer lemma, but it is not proved: `EvalExp` and `HasTyp` can reach
  relations through `rulePr` premises of definitions, so it needs a reachability argument like
  round 7's `TypAgree`;
* **`fwd_ctxTop20S`** (proved, from the two hypotheses): a `TopVStep20` step under any value prefix
  `vals vs` and suffix `rest` is a step of the corrected script between the images
  (`StepFix.sstepS_ctxtInstrs` when the context is non-empty), if the inner configurations before
  and after are typed and the suffix is a typed `admininstr*`;
* `CtxTopStep20 P`: those V2 steps (`CtxTopStep20.step` embeds it in `Step` with
  `Step.ctxtInstrs`), and **`Task.wholeStepCtxS20`** (frozen, a forward-only target at `growB`),
  with **`wholeStepCtxS20_of_agree`**: it holds whenever `growB` satisfies the two hypotheses.

The successor's typing (`hc'`) is a hypothesis: subject reduction for the image is not proved.
The backward half in `simEnv20S` is out of scope here: at `floatIntB` it is refuted
(`StepFix.not_wholeStepValidS`, the `vtestop` edge), and at `growB` it is not attempted.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV stateT dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy valsTy sstepB20S_iff sstepS_ctxtInstrs
  hasRuleAt_pureFix)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The top-level fragment, with its rule indices -/

/-- Every growth step fires one of the original `Step` 4–21. -/
theorem firesK_growStep20 {P : Profile} (hG : GrowCalls20 B) {c c' : Config H}
    (hz : TypedV (simEnv20 B) stateT (stateV hn c.store c.frame)) (hw : WholePages c.store)
    (h : GrowStep20 P c c') :
    ∃ k, 4 ≤ k ∧ Fires (simEnv20 B) "Step" k (.tuple [configV hn c, configV hn c']) := by
  cases h with
  | tableGrowSucceed ha ht hg _ => exact ⟨8, by decide, fires_tableGrowSucceed hG hz ha ht hg⟩
  | tableGrowFail _ _ _ => exact ⟨9, by decide, fires_tableGrowFail hz⟩
  | memoryGrowSucceed ha hm hg _ =>
    exact ⟨19, by decide, fires_memGrowSucceed hG hz ha hm hg (hw _ (mem_of_memInst hm))⟩
  | memoryGrowFail _ _ _ => exact ⟨20, by decide, fires_memGrowFail hz⟩

/-- Every `TopStep20` step fires one of the original `Step` 4–21. -/
theorem firesK_topStep20 {P : Profile} (hG : GrowCalls20 B) {c c' : Config H}
    (hz : TypedV (simEnv20 B) stateT (stateV hn c.store c.frame)) (hw : WholePages c.store)
    (h : TopStep20 P c c') :
    ∃ k, 4 ≤ k ∧ Fires (simEnv20 B) "Step" k (.tuple [configV hn c, configV hn c']) := by
  cases h with
  | grow h => exact firesK_growStep20 hG hz hw h
  | tableSetTrap ha ht h => exact ⟨6, by decide, fires_tableSetTrap hz ha ht h⟩
  | tableSetVal ha ht h => exact ⟨7, by decide, fires_tableSetVal hz ha ht h⟩
  | elemDrop ha he => exact ⟨10, by decide, fires_elemDrop hz ha he⟩
  | dataDrop ha hd => exact ⟨21, by decide, fires_dataDrop hz ha hd⟩

/-- Every `TopVarStep20` step fires one of the original `Step` 4–21. -/
theorem firesK_topVarStep20 {P : Profile} (hG : GrowCalls20 B) {c c' : Config H}
    (hz : TypedV (simEnv20 B) stateT (stateV hn c.store c.frame)) (hw : WholePages c.store)
    (h : TopVarStep20 P c c') :
    ∃ k, 4 ≤ k ∧ Fires (simEnv20 B) "Step" k (.tuple [configV hn c, configV hn c']) := by
  cases h with
  | top h => exact firesK_topStep20 hG hz hw h
  | localSet hx => exact ⟨4, by decide, fires_localSet hz hx⟩
  | globalSet ha hg => exact ⟨5, by decide, fires_globalSet hz ha hg⟩

/-- **Every `TopVStep20` step fires one of the original `Step` 4–21.** -/
theorem fires_topVStep20 {P : Profile} (hG : GrowCalls20 B) {c c' : Config H}
    (hc : Typed20 (simEnv20 B) hn c) (hw : WholePages c.store) (h : TopVStep20 P c c') :
    ∃ k, 4 ≤ k ∧ Fires (simEnv20 B) "Step" k (.tuple [configV hn c, configV hn c']) := by
  have hz := typedV_state_of_typed20 hc
  cases h with
  | var h => exact firesK_topVarStep20 hG hz hw h
  | vecStoreOob ha hm h => exact ⟨15, by decide, fires_vstoreOob hz ha hm h⟩
  | vecStoreLaneOob ha hm h => exact ⟨17, by decide, fires_vstoreLaneOob hz ha hm h⟩

/-! ## The code of a typed configuration -/

/-- The payload of a typed configuration image is a typed `state admininstr*` pair. -/
theorem hasTyp_cfgTup_of_typed20 {c : Config H} (h : Typed20 (simEnv20 B) hn c) :
    HasTyp (simEnv20 B) VarEnv.empty (.tupT [.mk "state" (.varT "state" []),
      .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)])
      (.tuple [stateV hn c.store c.frame, .list (adminsToV c.code)]) := by
  have hl : localTyp? VarEnv.empty "config" [] = none := rfl
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_config20] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := Sim.IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨rfl, rfl⟩ : op = "%;%" ∧
        w = .tuple [stateV hn c.store c.frame, .list (adminsToV c.code)] := by
      simpa [configV] using he.symm
    exact ((hasTypCase_cons_hit_iff rfl).1 hc).1
  · exact absurd hrest not_hasTypInsts_nil

/-- **The code of a configuration whose image is typed is a typed `admininstr*`.** -/
theorem typedV_code_of_typed20 {c : Config H} (h : Typed20 (simEnv20 B) hn c) :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV c.code)) := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 (hasTyp_cfgTup_of_typed20 h)
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨-, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  obtain ⟨us, hus, hlist⟩ := hasTyp_iterT_list_iff.1 hy'
  obtain rfl := (Value.list.inj hus).symm
  exact Sim.typedV_list_iff.2 fun u hu ρ hρ =>
    Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ (hasTypList_iff.1 hlist u hu)

/-! ## The transfer hypotheses -/

/-- **Rules 4–21 fire alike in the corrected script** (open): a firing of the original `Step`
rule `k ≥ 4` is a firing of the corrected `Step` rule `k + 1`, the same rule. -/
def StepAgreeS (B : Builtins) : Prop :=
  ∀ k, 4 ≤ k → ∀ v, Fires (simEnv20 B) "Step" k v → Fires (simEnv20S B) "Step" (k + 1) v

/-- **The context quantifiers type alike in the corrected script** (open). -/
structure TypAgreeS (B : Builtins) : Prop where
  state : ∀ v, TypedV (simEnv20 B) stateT v → TypedV (simEnv20S B) stateT v
  admins : ∀ v, TypedV (simEnv20 B) adminsTy v → TypedV (simEnv20S B) adminsTy v
  vals : ∀ v, TypedV (simEnv20 B) valsTy v → TypedV (simEnv20S B) valsTy v

/-- A firing of the corrected `Step` is a step of the corrected script. -/
theorem sstepB20S_of_fires {k : Nat} {v w : Value}
    (hf : Fires (simEnv20S B) "Step" k (.tuple [v, w])) : SStepB (simEnv20S B) v w := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_pureFix B
  exact (sstepB20S_iff B).2 ((dderives_iff_fires hrel).2 ⟨k, hf⟩)

/-! ## The route -/

/-- **A top-level step under a value prefix and a suffix is a step of the corrected script**,
from the two transfer hypotheses. -/
theorem fwd_ctxTop20S {P : Profile} (hG : GrowCalls20 B) (A : StepAgreeS B) (T : TypAgreeS B)
    {s s' : Store H} {f f' : Frame} {code code' : List Admin} (vs : List Val) (rest : List Admin)
    (hc : Typed20 (simEnv20 B) hn ⟨s, f, code⟩) (hc' : Typed20 (simEnv20 B) hn ⟨s', f', code'⟩)
    (hrest : TypedV (simEnv20 B) adminsTy (.list (adminsToV rest))) (hw : WholePages s)
    (h : TopVStep20 P ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    SStepB (simEnv20S B) (configV hn ⟨s, f, vals vs ++ code ++ rest⟩)
      (configV hn ⟨s', f', vals vs ++ code' ++ rest⟩) := by
  obtain ⟨k, hk, hf⟩ := fires_topVStep20 hG hc hw h
  have hin : SStepB (simEnv20S B) (configV hn ⟨s, f, code⟩) (configV hn ⟨s', f', code'⟩) :=
    sstepB20S_of_fires (A k hk _ hf)
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · have hvs : TypedV (simEnv20S B) valsTy (.list (adminsToV (vals vs))) := by
      rw [Pure.adminsToV_vals]
      exact T.vals _ (typedV_vals20 vs)
    have hs := sstepS_ctxtInstrs (T.state _ (typedV_state_of_typed20 hc))
      (T.state _ (typedV_state_of_typed20 hc')) hvs (T.admins _ (typedV_code_of_typed20 hc))
      (T.admins _ (typedV_code_of_typed20 hc')) (T.admins _ hrest)
      (by simpa [Pure.adminsToV_eq_map, vals] using hne) ((sstepB20S_iff B).1 hin)
    refine (sstepB20S_iff B).2 ?_
    simpa only [configV, Pure.adminsToV_append] using hs
  · obtain ⟨rfl, rfl⟩ : vs = [] ∧ rest = [] := by simpa [not_or] using hne
    simpa [vals] using hin

/-! ## The V2 steps it covers, and the target -/

/-- **Top-level fragment steps under a context**: a `TopVStep20` step under a value prefix and a
suffix (`Step.ctxtInstrs` when they are not both empty). -/
inductive CtxTopStep20 (P : Profile) : Config H → Config H → Prop where
  | mk {s s' : Store H} {f f' : Frame} {code code' : List Admin} (vs : List Val)
      (rest : List Admin) (h : TopVStep20 P ⟨s, f, code⟩ ⟨s', f', code'⟩) :
      CtxTopStep20 P ⟨s, f, vals vs ++ code ++ rest⟩ ⟨s', f', vals vs ++ code' ++ rest⟩

/-- Every step of the fragment is a V2 step. -/
theorem CtxTopStep20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : CtxTopStep20 P c c') : Step P host c c' := by
  obtain ⟨vs, rest, h⟩ := h
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact .ctxtInstrs h.step hne
  · obtain ⟨rfl, rfl⟩ : vs = [] ∧ rest = [] := by simpa [not_or] using hne
    simpa [vals] using h.step

/-- **The forward 2.0 half below the top, through the erratum** (frozen, forward only): at `growB`,
every top-level fragment step under a context, with typed inner configurations and suffix and
whole pages, is a step of the corrected script between the images. -/
def Task.wholeStepCtxS20 : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : RelaxedChoice)
    (s s' : Store H) (f f' : Frame) (code code' : List Admin) (vs : List Val) (rest : List Admin),
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn ⟨s, f, code⟩ →
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn ⟨s', f', code'⟩ →
    TypedV (simEnv20 (growB (Profile.spec nd r))) adminsTy (.list (adminsToV rest)) →
    WholePages s → TopVStep20 (Profile.spec nd r) ⟨s, f, code⟩ ⟨s', f', code'⟩ →
    SStepB (simEnv20S (growB (Profile.spec nd r))) (configV hn ⟨s, f, vals vs ++ code ++ rest⟩)
      (configV hn ⟨s', f', vals vs ++ code' ++ rest⟩)

/-- **`Task.wholeStepCtxS20` holds wherever `growB` satisfies the transfer hypotheses.** -/
theorem wholeStepCtxS20_of_agree
    (h : ∀ P : Profile, StepAgreeS (growB P) ∧ TypAgreeS (growB P)) : Task.wholeStepCtxS20 :=
  fun _ _ _ _ _ _ _ _ _ _ vs rest hc hc' hrest hw hs =>
    fwd_ctxTop20S (growCalls20_growB _) (h _).1 (h _).2 vs rest hc hc' hrest hw hs

end Silmaril.Wasm.SpecTec.Sim20.Whole
