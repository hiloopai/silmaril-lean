module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreVal10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdNest

/-!
# The 1.0 structural rules in `simEnv10T`, and stores nested anywhere

The structural rules of the wasm-1.0 `Step` (`ctxt-instrs`, `ctxt-label`, `ctxt-frame`) quantify
their code as `admininstr*` and their state as `state`. In `simEnv10T` both admit `STORE`, so
round 3's lifts (`Whole.sstep10_ctxtInstrs`, …, `Whole.fwd10_nest`) are restated there, with the
same proofs (the evaluation lemmas are environment-generic; the rules are found through
`hasRuleAtT`):

* `findTyp_config10T`, `findTyp_state10T`, `findTyp_val10TF`, `findTyp_admininstr10TF`: the type
  table entries the lifts read. `admininstr`'s `CONST`, `LABEL_` and `FRAME_` cases are kept by
  `fixCase10` (`findCase_map_fixCase10`);
* `sstep10_ctxtInstrsT`, `sstep10_ctxtLabelT`, `sstep10_ctxtFrameT`, then `fwd10_contextT`,
  `fwd10_labelT`, `fwd10_frameT`, `FwdAt10T` and **`fwd10_nestT`**: the forward obligation in
  `simEnv10T` passes from the leaves to every nesting under V1's `context`, `label` and `frame`;
* `StoreLeaf10`: V1's six scalar store steps at the top of the code. Each is a step of
  `simEnv10T (bytesB10 P)` from a state typed there (`fwdAt10T_storeLeaf`, from `StoreTop10T`
  and `StoreVal10T`);
* **`fwd10T_storeNest`**: a V1 step that is a store nested under contexts, labels and frames, from
  and to configurations typed in `simEnv10T`, is a step of `simEnv10T (bytesB10 P)` between the
  images. Nothing else is assumed: the store may hold functions that contain stores, and the code
  around the store may contain stores.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T fixCase10 storeCaseFix10)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (repl find?_map_repl caseOp)

variable {B : Builtins}

/-! ## The type table entries the structural rules read -/

theorem findTyp?_simEnv10T_ne (B : Builtins) {y : IL.Id} (h₁ : y ≠ "instr")
    (h₂ : y ≠ "admininstr") : (simEnv10T B).findTyp? y = (simEnv10 B).findTyp? y := by
  have ht := (simEnv10T_tables B).1
  simp only [Env.findTyp?, ht, find?_map_repl, h₁, h₂, ↓reduceIte]

theorem findTyp_adminT (B : Builtins) : (simEnv10T B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT (adminCases10.map fixCase10))]) := by
  have ht := (simEnv10T_tables B).1
  have h := findTyp_admin10 B
  simp only [Env.findTyp?] at h
  simp only [Env.findTyp?, ht, find?_map_repl]
  simp [h]

/-- `fixCase10` keeps every case but `STORE`. -/
theorem findCase_map_fixCase10 (op : MixopS) (hop : op ≠ "STORE") : ∀ cs : List TypCase,
    Sim.IntNumeric.findCase (cs.map fixCase10) op = Sim.IntNumeric.findCase cs op
  | [] => rfl
  | c :: cs => by
    have ih := findCase_map_fixCase10 op hop cs
    by_cases hc : caseOp c = "STORE"
    · obtain ⟨o, t, qs, prems⟩ := c
      simp only [caseOp] at hc
      subst hc
      have hne : ¬ ("STORE" : MixopS) = op := fun h => hop h.symm
      simp only [List.map_cons, fixCase10, storeCaseFix10, Sim.IntNumeric.findCase, hne,
        ↓reduceIte, ih]
    · rw [List.map_cons, fixCase10_of_ne hc]
      obtain ⟨o, t, qs, prems⟩ := c
      simp only [Sim.IntNumeric.findCase, ih]

theorem findTyp_config10T : (simEnv10T B).findTyp? "config" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "state" (.varT "state" []),
      .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)]) [] []])]) :=
  (findTyp?_simEnv10T_ne B (by decide) (by decide)).trans Whole.findTyp_config10

theorem findTyp_state10T : (simEnv10T B).findTyp? "state" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "store" (.varT "store" []), .mk "frame" (.varT "frame" [])])
      [] []])]) :=
  (findTyp?_simEnv10T_ne B (by decide) (by decide)).trans Whole.findTyp_state10

theorem findTyp_val10TF : ∃ cs, (simEnv10T B).findTyp? "val" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
      Sim.IntNumeric.findCase cs "CONST" = some (Whole.constT10, []) :=
  let ⟨cs, h, hc⟩ := Whole.findTyp_val10F (B := B)
  ⟨cs, (findTyp?_simEnv10T_ne B (by decide) (by decide)).trans h, hc⟩

/-- 1.0's `admininstr` in `simEnv10T`, with its `CONST`, `LABEL_` and `FRAME_` cases. -/
theorem findTyp_admininstr10TF : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
      Sim.IntNumeric.findCase cs "CONST" = some (Whole.constT10, []) ∧
    Sim.IntNumeric.findCase cs "LABEL_%{%}%" = some (Whole.labelT10, []) ∧
    Sim.IntNumeric.findCase cs "FRAME_%{%}%" = some (Whole.frameCaseT10, []) := by
  obtain ⟨cs, h, h₁, h₂, h₃⟩ := Whole.findTyp_admininstr10F (B := B)
  rw [findTyp_admin10 B] at h
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Inst.instD.injEq, DefTyp.variantT.injEq,
    true_and, and_true] at h
  subst h
  exact ⟨_, findTyp_adminT B, (findCase_map_fixCase10 _ (by decide) _).trans h₁,
    (findCase_map_fixCase10 _ (by decide) _).trans h₂, (findCase_map_fixCase10 _ (by decide) _).trans h₃⟩

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat iterPat)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SStep SRead SPure cfgV stV TypedV ValsOnly stateT storeT
  frameT nT instrsT dderives_of_ruleAt evalExp_tup2 evalExp_tup3 evalExp_case evalExp_list1
  evalExp_cat evalExp_ne_nil evalExp_or prems_one prems_two typedV_list_iff typedV_list_append)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase hasTyp_of_hasTypCase matchArgs_nil_scope
  hasTyp_varT_nil_congr)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (findTyp_config10T findTyp_state10T findTyp_val10TF
  findTyp_admininstr10TF)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## The structural rules in `simEnv10T` -/

/-- **`Step/ctxt-instrs`** of the 1.0 script: a step under a value prefix `vs` and a suffix
`rest`, not both empty. -/
theorem sstep10_ctxtInstrsT {z z' : Value} {vs is is' rest : List Value}
    (hz : TypedV (simEnv10T B) stateT z) (hz' : TypedV (simEnv10T B) stateT z')
    (hvs : TypedV (simEnv10T B) valsTy10 (.list vs)) (his : TypedV (simEnv10T B) adminsT (.list is))
    (his' : TypedV (simEnv10T B) adminsT (.list is'))
    (hrest : TypedV (simEnv10T B) adminsT (.list rest)) (hne : vs ≠ [] ∨ rest ≠ [])
    (hs : SStep (simEnv10T B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv10T B) (cfgV z (vs ++ is ++ rest)) (cfgV z' (vs ++ is' ++ rest)) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("val*", .list vs), ("admininstr*", .list is),
    ("admininstr_1*", .list rest), ("z'", z'), ("admininstr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fv : ρ.findVal? "val*" = some (.list vs) := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fr : ρ.findVal? "admininstr_1*" = some (.list rest) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "admininstr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv10T B) ρ [.expP "z" stateT, .expP "val*" valsTy10,
      .expP "admininstr*" adminsT, .expP "admininstr_1*" adminsT, .expP "z'" stateT,
      .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fv (hvs ρ hρ)
      (QuantsOk.cons fi (his ρ hρ)
      (QuantsOk.cons fr (hrest ρ hρ)
      (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ev : EvalExp (simEnv10T B) ρ valsE10 (.list vs) := evalExp_subIterPat (by decide) fv
  have ev' : EvalExp (simEnv10T B) ρ (iterPat "val" "val*") (.list vs) :=
    evalExp_iterPat (by decide) fv
  have ei : EvalExp (simEnv10T B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv10T B) ρ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have er : EvalExp (simEnv10T B) ρ (iterPat "admininstr_1" "admininstr_1*") (.list rest) :=
    evalExp_iterPat (by decide) fr
  have hor : EvalExp (simEnv10T B) ρ (.binE .orOp .boolT
      (.cmpE .neOp .boolT (iterPat "val" "val*") (.listE []))
      (.cmpE .neOp .boolT (iterPat "admininstr_1" "admininstr_1*") (.listE [])))
      (.bool (decide (vs ≠ [] ∨ rest ≠ []))) :=
    evalExp_or (evalExp_ne_nil ev') (evalExp_ne_nil er)
  have hd : decide (vs ≠ [] ∨ rest ≠ []) = true := decide_eq_true hne
  have hg : SStep (simEnv10T B) (cfgV z (vs ++ (is ++ rest))) (cfgV z' (vs ++ (is' ++ rest))) :=
    dderives_of_ruleAt (StoreAgree.hasRuleAtT (hasRuleAt_ctxtInstrs10 B)) _ hq
      (evalExp_tup2
        (evalExp_case (op := "%;%")
          (evalExp_tup2 (evalExp_var fz) (evalExp_cat ev (evalExp_cat ei er))))
        (evalExp_case (op := "%;%")
          (evalExp_tup2 (evalExp_var fz') (evalExp_cat ev (evalExp_cat ei' er)))))
      (prems_two
        (.rulePr Equiv.evalArgs_nil
          (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
            (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs)
        (.ifPr (hd ▸ hor)))
  simpa only [List.append_assoc] using hg

/-- **`Step/ctxt-label`** of the 1.0 script: a step of `z; admininstr*` lifts under
`LABEL_ n {instr_0*}`. -/
theorem sstep10_ctxtLabelT {z z' n : Value} {cont is is' : List Value}
    (hz : TypedV (simEnv10T B) stateT z) (hz' : TypedV (simEnv10T B) stateT z')
    (hn : TypedV (simEnv10T B) nT n) (hc : TypedV (simEnv10T B) instrsT (.list cont))
    (his : TypedV (simEnv10T B) adminsT (.list is))
    (his' : TypedV (simEnv10T B) adminsT (.list is'))
    (hs : SStep (simEnv10T B) (cfgV z is) (cfgV z' is')) :
    SStep (simEnv10T B) (cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])])
      (cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("n", n), ("instr_0*", .list cont),
    ("admininstr*", .list is), ("z'", z'), ("admininstr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have fc : ρ.findVal? "instr_0*" = some (.list cont) := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fz' : ρ.findVal? "z'" = some z' := rfl
  have fi' : ρ.findVal? "admininstr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv10T B) ρ [.expP "z" stateT, .expP "n" nT, .expP "instr_0*" instrsT,
      .expP "admininstr*" adminsT, .expP "z'" stateT, .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fn (hn ρ hρ) (QuantsOk.cons fc (hc ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fz' (hz' ρ hρ)
      (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))
  have ec : EvalExp (simEnv10T B) ρ (iterPat "instr_0" "instr_0*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp (simEnv10T B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv10T B) ρ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  exact dderives_of_ruleAt (StoreAgree.hasRuleAtT (hasRuleAt_ctxtLabel10 B)) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') (evalExp_list1
        (evalExp_case (op := "LABEL_%{%}%") (evalExp_tup3 (evalExp_var fn) ec ei'))))))
    (prems_one (.rulePr Equiv.evalArgs_nil
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz') ei'))) hs))

/-- **`Step/ctxt-frame`** of the 1.0 script: a step of `s; f'; admininstr*` to
`s'; f''; admininstr'*` lifts under `FRAME_ n {f'}` at any outer frame `f`. -/
theorem sstep10_ctxtFrameT {s s' f fr fr' n : Value} {is is' : List Value}
    (hs₁ : TypedV (simEnv10T B) storeT s) (hs₂ : TypedV (simEnv10T B) storeT s')
    (hf : TypedV (simEnv10T B) frameT f) (hfr : TypedV (simEnv10T B) frameT fr)
    (hfr' : TypedV (simEnv10T B) frameT fr') (hn : TypedV (simEnv10T B) nT n)
    (his : TypedV (simEnv10T B) adminsT (.list is))
    (his' : TypedV (simEnv10T B) adminsT (.list is'))
    (hst : SStep (simEnv10T B) (cfgV (stV s fr) is) (cfgV (stV s' fr') is')) :
    SStep (simEnv10T B) (cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])])
      (cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr', .list is'])]) := by
  let ρ := VarEnv.empty.bindVals [("s", s), ("f", f), ("n", n), ("f'", fr),
    ("admininstr*", .list is), ("s'", s'), ("f''", fr'), ("admininstr'*", .list is')]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fs : ρ.findVal? "s" = some s := rfl
  have ff : ρ.findVal? "f" = some f := rfl
  have fn : ρ.findVal? "n" = some n := rfl
  have ffr : ρ.findVal? "f'" = some fr := rfl
  have fi : ρ.findVal? "admininstr*" = some (.list is) := rfl
  have fs' : ρ.findVal? "s'" = some s' := rfl
  have ffr' : ρ.findVal? "f''" = some fr' := rfl
  have fi' : ρ.findVal? "admininstr'*" = some (.list is') := rfl
  have hq : QuantsOk (simEnv10T B) ρ [.expP "s" storeT, .expP "f" frameT, .expP "n" nT,
      .expP "f'" frameT, .expP "admininstr*" adminsT, .expP "s'" storeT, .expP "f''" frameT,
      .expP "admininstr'*" adminsT] :=
    QuantsOk.cons fs (hs₁ ρ hρ) (QuantsOk.cons ff (hf ρ hρ) (QuantsOk.cons fn (hn ρ hρ)
      (QuantsOk.cons ffr (hfr ρ hρ) (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fs' (hs₂ ρ hρ)
      (QuantsOk.cons ffr' (hfr' ρ hρ) (QuantsOk.cons fi' (his' ρ hρ) QuantsOk.nil)))))))
  have ei : EvalExp (simEnv10T B) ρ (iterPat "admininstr" "admininstr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  have ei' : EvalExp (simEnv10T B) ρ (iterPat "admininstr'" "admininstr'*") (.list is') :=
    evalExp_iterPat (by decide) fi'
  have est : EvalExp (simEnv10T B) ρ (stE (.varE "s") (.varE "f")) (stV s f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff))
  have est' : EvalExp (simEnv10T B) ρ (stE (.varE "s'") (.varE "f")) (stV s' f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff))
  have ein : EvalExp (simEnv10T B) ρ (stE (.varE "s") (.varE "f'")) (stV s fr) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr))
  have ein' : EvalExp (simEnv10T B) ρ (stE (.varE "s'") (.varE "f''")) (stV s' fr') :=
    evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr'))
  exact dderives_of_ruleAt (StoreAgree.hasRuleAtT (hasRuleAt_ctxtFrame10 B)) _ hq
    (evalExp_tup2
      (evalExp_case (op := "%;%") (evalExp_tup2 est (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%") (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (op := "%;%") (evalExp_tup2 est' (evalExp_list1
        (evalExp_case (op := "FRAME_%{%}%")
          (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr') ei'))))))
    (prems_one (.rulePr Equiv.evalArgs_nil
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 ein ei))
        (evalExp_case (op := "%;%") (evalExp_tup2 ein' ei'))) hst))


/-! ## Configurations, states and nesting in `simEnv10T` -/

/-- The payload of a typed configuration image is a typed `state admininstr*` pair. -/
theorem hasTyp_cfgTup_of_typed10T {c : Config H}
    (h : Typed10 (simEnv10T B) hn c) :
    HasTyp (simEnv10T B) VarEnv.empty (.tupT [.mk "state" (.varT "state" []),
      .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)])
      (.tuple [stateV hn c.store c.frame, .list (adminsToV c.code)]) :=
  hasTyp_closedVariant_inv valsOnly_empty findTyp_config10T h rfl

/-- **The state of a typed configuration image is typed.** -/
theorem typedV_state_of_typed10T {c : Config H}
    (h : Typed10 (simEnv10T B) hn c) : TypedV (simEnv10T B) stateT (stateV hn c.store c.frame) := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 (hasTyp_cfgTup_of_typed10T h)
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, hy, -⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, -⟩ := List.cons.inj hys
  exact typedV_of_scope valsOnly_empty hy

/-- **The code of a typed configuration image is a typed `admininstr*`.** -/
theorem typedV_code_of_typed10T {c : Config H}
    (h : Typed10 (simEnv10T B) hn c) : TypedV (simEnv10T B) adminsT (.list (adminsToV c.code)) := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 (hasTyp_cfgTup_of_typed10T h)
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨-, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  exact typedV_list_of_scope ⟨rfl, rfl, rfl⟩ hy'

/-- **`state = store; frame` is typed exactly when both halves are.** -/
theorem typedV_stV_iff10T {s f : Value} :
    TypedV (simEnv10T B) stateT (stV s f) ↔
      TypedV (simEnv10T B) storeT s ∧ TypedV (simEnv10T B) frameT f := by
  constructor
  · intro h
    have hp := hasTyp_closedVariant_inv valsOnly_empty findTyp_state10T (h _ valsOnly_empty) rfl
    obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
    obtain rfl := (Value.tuple.inj hvs).symm
    obtain ⟨y, ys, hys, hy, htup'⟩ := hasTypTup_cons_iff.1 htup
    obtain ⟨rfl, rfl⟩ := List.cons.inj hys
    obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
    obtain ⟨rfl, -⟩ := List.cons.inj hys'
    exact ⟨typedV_of_scope valsOnly_empty hy, typedV_of_scope ⟨rfl, rfl, rfl⟩ hy'⟩
  · rintro ⟨hs, hf⟩
    exact Sim20.Pure.typedV_closedCase20 findTyp_state10T rfl
      (hasTyp_tup2G10 hs hf)



/-- **Inversion of `LABEL_`**: a typed label has a typed arity, continuation and body. -/
theorem label_inv10T {n : Value} {cont is : List Value}
    (h : TypedV (simEnv10T B) adminT10 (.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is]))) :
    TypedV (simEnv10T B) nT n ∧ TypedV (simEnv10T B) instrsT (.list cont) ∧
      TypedV (simEnv10T B) adminsT (.list is) := by
  obtain ⟨cs, htd, -, hl, -⟩ := findTyp_admininstr10TF (B := B)
  exact hasTyp_tup3_inv (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hl)
    (fun hρ hv => typedV_list_of_scope hρ hv)

/-- **Inversion of `FRAME_`**: a typed frame has a typed arity, frame and body. -/
theorem frame_inv10T {n fr : Value} {is : List Value}
    (h : TypedV (simEnv10T B) adminT10 (.case "FRAME_%{%}%" (.tuple [n, fr, .list is]))) :
    TypedV (simEnv10T B) nT n ∧ TypedV (simEnv10T B) frameT fr ∧
      TypedV (simEnv10T B) adminsT (.list is) := by
  obtain ⟨cs, htd, -, -, hf⟩ := findTyp_admininstr10TF (B := B)
  exact hasTyp_tup3_inv (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hf)
    (fun hρ hv => typedV_of_scope hρ hv)

/-- **A `CONST` typed as `admininstr` is typed as `val`.** -/
theorem typedV_val_of_admin10T {w : Value}
    (h : TypedV (simEnv10T B) adminT10 (.case "CONST" w)) :
    TypedV (simEnv10T B) (.varT "val" []) (.case "CONST" w) := by
  obtain ⟨cs, htd, hc, -, -⟩ := findTyp_admininstr10TF (B := B)
  obtain ⟨cs', htd', hc'⟩ := findTyp_val10TF (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd' hc'
    (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hc)

/-- **The images of V1 values typed as `admininstr*` are a typed `val*`.** -/
theorem typedV_vals_of_admins10T {us : List Execution.Runtime.Value}
    (h : TypedV (simEnv10T B) adminsT (.list (us.map valV))) :
    TypedV (simEnv10T B) valsTy10 (.list (us.map valV)) :=
  typedV_list_iff.2 fun u hu => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_val_of_admin10T (w := .tuple [valTypeV v.type, numV v]) (typedV_list_iff.1 h _ hu)


/-- **`Step/ctxt-instrs` forward on V1 images**: V1's `context`, with every typing read off the
codes and states. -/
theorem fwd10_contextT {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (vs : List Execution.Runtime.Value) (tail : List Admin)
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f))
    (hz' : TypedV (simEnv10T B) stateT (stateV hn s' f'))
    (hc : TypedV (simEnv10T B) adminsT (.list (adminsToV (values vs ++ before ++ tail))))
    (hc' : TypedV (simEnv10T B) adminsT (.list (adminsToV (values vs ++ after ++ tail))))
    (h : SStepB (simEnv10T B) (configV hn ⟨s, f, before⟩) (configV hn ⟨s', f', after⟩)) :
    SStepB (simEnv10T B) (configV hn ⟨s, f, values vs ++ before ++ tail⟩)
      (configV hn ⟨s', f', values vs ++ after ++ tail⟩) := by
  rw [adminsToV_append3, adminsToV_values] at hc hc'
  obtain ⟨hcv, hct⟩ := typedV_list_append.1 hc
  obtain ⟨hvs, hb⟩ := typedV_list_append.1 hcv
  obtain ⟨hcv', -⟩ := typedV_list_append.1 hc'
  obtain ⟨-, ha⟩ := typedV_list_append.1 hcv'
  by_cases hne : vs.map valV ≠ [] ∨ adminsToV tail ≠ []
  · have hs := sstep10_ctxtInstrsT hz hz' (typedV_vals_of_admins10T hvs) hb ha hct hne
      ((StoreFix.sstepB10T_iff B).1 h)
    refine (StoreFix.sstepB10T_iff B).2 ?_
    simpa only [configV_eq_cfgV10, adminsToV_append3, adminsToV_values] using hs
  · obtain ⟨h₁, h₂⟩ : vs.map valV = [] ∧ adminsToV tail = [] := by simpa [not_or] using hne
    obtain rfl : vs = [] := List.map_eq_nil_iff.1 h₁
    obtain rfl : tail = [] := by
      rw [adminsToV_map10] at h₂
      exact List.map_eq_nil_iff.1 h₂
    simpa [values] using h

/-- **`Step/ctxt-label` forward on V1 images**: V1's `label`. -/
theorem fwd10_labelT {s s' : Store H} {f f' : Frame} {before after : List Admin} (n : Nat)
    (cont : V1.Expr) (hz : TypedV (simEnv10T B) stateT (stateV hn s f))
    (hz' : TypedV (simEnv10T B) stateT (stateV hn s' f'))
    (hc : TypedV (simEnv10T B) adminsT (.list (adminsToV [.label n cont before])))
    (hc' : TypedV (simEnv10T B) adminsT (.list (adminsToV [.label n cont after])))
    (h : SStepB (simEnv10T B) (configV hn ⟨s, f, before⟩) (configV hn ⟨s', f', after⟩)) :
    SStepB (simEnv10T B) (configV hn ⟨s, f, [.label n cont before]⟩)
      (configV hn ⟨s', f', [.label n cont after]⟩) := by
  obtain ⟨hn', hcont, hb⟩ := label_inv10T (typedV_list_iff.1 hc _ (.head _))
  obtain ⟨-, -, ha⟩ := label_inv10T (typedV_list_iff.1 hc' _ (.head _))
  exact (StoreFix.sstepB10T_iff B).2 (sstep10_ctxtLabelT hz hz' hn' hcont hb ha ((StoreFix.sstepB10T_iff B).1 h))

/-- **`Step/ctxt-frame` forward on V1 images**: V1's `frame`, the inner frame changing. -/
theorem fwd10_frameT {s s' : Store H} {inner inner' outer : Frame} {before after : List Admin}
    (n : Nat) (hz : TypedV (simEnv10T B) stateT (stateV hn s outer))
    (hz' : TypedV (simEnv10T B) stateT (stateV hn s' outer))
    (hc : TypedV (simEnv10T B) adminsT (.list (adminsToV [.frame n inner before])))
    (hc' : TypedV (simEnv10T B) adminsT (.list (adminsToV [.frame n inner' after])))
    (h : SStepB (simEnv10T B) (configV hn ⟨s, inner, before⟩) (configV hn ⟨s', inner', after⟩)) :
    SStepB (simEnv10T B) (configV hn ⟨s, outer, [.frame n inner before]⟩)
      (configV hn ⟨s', outer, [.frame n inner' after]⟩) := by
  obtain ⟨hs, ho⟩ := typedV_stV_iff10T.1 hz
  obtain ⟨hs', -⟩ := typedV_stV_iff10T.1 hz'
  obtain ⟨hn', hi, hb⟩ := frame_inv10T (typedV_list_iff.1 hc _ (.head _))
  obtain ⟨-, hi', ha⟩ := frame_inv10T (typedV_list_iff.1 hc' _ (.head _))
  exact (StoreFix.sstepB10T_iff B).2 (sstep10_ctxtFrameT hs hs' ho hi hi' hn' hb ha ((StoreFix.sstepB10T_iff B).1 h))

/-! ## Nesting -/

/-- **The forward obligation at a pair of configurations**: whenever the states and codes of both
are typed, the image of `c` steps to the image of `c'` in the 1.0 script. -/
def FwdAt10T (B : Builtins) (hn : H → String) (c c' : Config H) : Prop :=
  TypedV (simEnv10T B) stateT (stateV hn c.store c.frame) →
    TypedV (simEnv10T B) stateT (stateV hn c'.store c'.frame) →
    TypedV (simEnv10T B) adminsT (.list (adminsToV c.code)) →
    TypedV (simEnv10T B) adminsT (.list (adminsToV c'.code)) →
    SStepB (simEnv10T B) (configV hn c) (configV hn c')

/-- `FwdAt10T` lifts through V1's `context`. -/
theorem fwdAt10_contextT {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (ih : FwdAt10T B hn ⟨s, f, before⟩ ⟨s', f', after⟩) (vs : List Execution.Runtime.Value)
    (tail : List Admin) :
    FwdAt10T B hn ⟨s, f, values vs ++ before ++ tail⟩ ⟨s', f', values vs ++ after ++ tail⟩ := by
  intro hz hz' hc hc'
  have hb : TypedV (simEnv10T B) adminsT (.list (adminsToV before)) := by
    rw [adminsToV_append3] at hc
    exact (typedV_list_append.1 (typedV_list_append.1 hc).1).2
  have ha : TypedV (simEnv10T B) adminsT (.list (adminsToV after)) := by
    rw [adminsToV_append3] at hc'
    exact (typedV_list_append.1 (typedV_list_append.1 hc').1).2
  exact fwd10_contextT vs tail hz hz' hc hc' (ih hz hz' hb ha)

/-- `FwdAt10T` lifts through V1's `label`. -/
theorem fwdAt10_labelT {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (ih : FwdAt10T B hn ⟨s, f, before⟩ ⟨s', f', after⟩) (n : Nat) (cont : V1.Expr) :
    FwdAt10T B hn ⟨s, f, [.label n cont before]⟩ ⟨s', f', [.label n cont after]⟩ :=
  fun hz hz' hc hc' => fwd10_labelT n cont hz hz' hc hc'
    (ih hz hz' (label_inv10T (typedV_list_iff.1 hc _ (.head _))).2.2
      (label_inv10T (typedV_list_iff.1 hc' _ (.head _))).2.2)

/-- `FwdAt10T` lifts through V1's `frame`. -/
theorem fwdAt10_frameT {s s' : Store H} {inner inner' : Frame} {before after : List Admin}
    (ih : FwdAt10T B hn ⟨s, inner, before⟩ ⟨s', inner', after⟩) (n : Nat) (outer : Frame) :
    FwdAt10T B hn ⟨s, outer, [.frame n inner before]⟩ ⟨s', outer, [.frame n inner' after]⟩ := by
  intro hz hz' hc hc'
  obtain ⟨-, hi, hb⟩ := frame_inv10T (typedV_list_iff.1 hc _ (.head _))
  obtain ⟨-, hi', ha⟩ := frame_inv10T (typedV_list_iff.1 hc' _ (.head _))
  have hzi : TypedV (simEnv10T B) stateT (stateV hn s inner) :=
    typedV_stV_iff10T.2 ⟨(typedV_stV_iff10T.1 hz).1, hi⟩
  have hzi' : TypedV (simEnv10T B) stateT (stateV hn s' inner') :=
    typedV_stV_iff10T.2 ⟨(typedV_stV_iff10T.1 hz').1, hi'⟩
  exact fwd10_frameT n hz hz' hc hc' (ih hzi hzi' hb ha)

/-- **The forward 1.0 half passes from the leaves to every nesting**, at every builtins. -/
theorem fwd10_nestT {L : Config H → Config H → Prop} (hL : ∀ c c', L c c' → FwdAt10T B hn c c')
    {c c' : Config H} (h : Nest10 L c c') : FwdAt10T B hn c c' := by
  induction h with
  | leaf h => exact hL _ _ h
  | context _ vs tail ih => exact fwdAt10_contextT ih vs tail
  | label _ n cont ih => exact fwdAt10_labelT ih n cont
  | frame _ n outer ih => exact fwdAt10_frameT ih n outer

/-- `fwd10_nestT` from typed configuration images. -/
theorem fwd10_nest_typedT {L : Config H → Config H → Prop}
    (hL : ∀ c c', L c c' → FwdAt10T B hn c c') {c c' : Config H}
    (hc : Typed10 (simEnv10T B) hn c) (hc' : Typed10 (simEnv10T B) hn c') (h : Nest10 L c c') :
    SStepB (simEnv10T B) (configV hn c) (configV hn c') :=
  fwd10_nestT hL h (typedV_state_of_typed10T hc) (typedV_state_of_typed10T hc')
    (typedV_code_of_typed10T hc) (typedV_code_of_typed10T hc')


end Silmaril.Wasm.SpecTec.Sim10.Whole
