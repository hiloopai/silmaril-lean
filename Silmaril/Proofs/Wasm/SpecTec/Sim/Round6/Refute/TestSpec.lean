module

public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.Thms

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Refute

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open RefsGC

variable {env : Env} {H : Type} {hn : H → String}

/-- `RefsGC.RStoreFuns` in every `simEnv B` (the proof of `Round5.Fwd.rStore_builtins`, which
uses nothing about the builtins). -/
theorem rStore_simEnv (B : Builtins) : RefsGC.RStoreFuns (simEnv B) :=
  have Pd := Prims.projDefs_simEnv B
  ⟨fun hn' _ _ s f hρ he => evalExp_callArgs (Prims.findDef_none_of_valsOnly hρ _)
      (Equiv.evalArgs_cons he Equiv.evalArgs_nil) (Prims.applies_moduleinst Pd hn' s f),
    fun hn' _ _ s f hρ he => evalExp_callArgs (Prims.findDef_none_of_valsOnly hρ _)
      (Equiv.evalArgs_cons he Equiv.evalArgs_nil) (Prims.applies_arrayinst Pd hn' s f),
    fun hn' _ _ s f hρ he => evalExp_callArgs (Prims.findDef_none_of_valsOnly hρ _)
      (Equiv.evalArgs_cons he Equiv.evalArgs_nil) (Prims.applies_structinst Pd hn' s f),
    fun hn' ρ ez ey s f y ea ei hρ h hz hy =>
      Prims.evalExp_elem_stateV (State.stateDefs_simEnv _) hn' ρ ez ey s f y ea ei h
        (Prims.findDef_none_of_valsOnly hρ _) hz hy,
    fun ρ e₁ e₂ m rt hρ =>
      RefOk.instReftype_simEnv _ ρ e₁ e₂ m rt (Prims.findDef_none_of_valsOnly hρ _)⟩

/-- `ref.test-true` does not fire when SpecTec's `Ref_ok` does not hold, under any reading of
`otherwise` (the direction of `Round5.Fwd.not_refTestTrueC` that the proof uses). -/
theorem not_refTestTrueN (G : RStoreFuns env) {O : ElseI} {els : Prop}
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
    (N : ∀ O : ElseI, ¬ DDerives env O "Ref_ok" "%|-%:%" []
      (.tuple [storeV hn s, refToValue r, CT.elemType (f.module.instRef rt)]))
    {c : Value} :
    ¬ RuleBody env (DDerives env O) els [] [] "%~>%" refTestTrueRule
      (.tuple [configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain ⟨hs, hf, hr, ht⟩ := binds_ref1 (lhs_of_concl he)
  obtain ⟨w, hw, hd⟩ := premW_rule (hp _ (List.mem_singleton_self _))
  rw [EvalExp.unique hw (evalExp_refOkArg G (valsOnly_scope hb) hs hf hr ht)] at hd
  exact N O hd

/-- **`ref.test-false` (rule 66) fires when SpecTec's `Ref_ok` does not hold**, whatever Core's
`RefOk` says. -/
theorem sread_refTestFalseN (h : HasRuleAt env "Step_read" "%~>%" 66 refTestFalseRule)
    (h₆₅ : HasRuleAt env "Step_read" "%~>%" 65 refTestTrueRule)
    (hT : ((relRules env "Step_read").map ruleTags).take 103 = readTagTable)
    (T : TypingFacts env hn) (R : RTyping env) (G : RStoreFuns env)
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
    (N : ∀ O : ElseI, ¬ DDerives env O "Ref_ok" "%|-%:%" []
      (.tuple [storeV hn s, refToValue r, CT.elemType (f.module.instRef rt)]))
    (hz : TypedV env stateT (stateV hn s f))
    (hc : TypedV env instrsT (.list (adminsToV [.ref r, .plain (.refTest rt)]))) :
    SRead env (configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩) (adminsToV [constI32 0]) := by
  let σ : List (IL.Id × Value) :=
    [("s", storeV hn s), ("f", frameV f), ("ref", refToValue r), ("rt", Encode.toValue rt)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨hs, hf⟩ := (T.state s f).1 hz
  have hr : TypedV env refT (refToValue r) := R.ref r (typed_head T hc)
  have hrt : TypedV env reftypeT (Encode.toValue rt) :=
    R.arg "REF.TEST" _ reftypeT (by simp [argTypes]) (typed_tail T hc)
  have ha : LhsIn (["REF.TEST"] ++ valTags) (configV hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩) :=
    .inr ⟨_, _, rfl, tagsIn_cons (tag_ref (refTags_sub _) r)
      (tagsIn_cons (tag_case (by decide)) tagsIn_nil)⟩
  have hel := otherwise_of_ruleAt h hT (i := 66) (b := .list (adminsToV [constI32 0])) (by decide)
    (exc := [65]) ha (by decide) (by
      intro j hj _ r' hr' w hw
      obtain rfl : j = 65 := by simpa using hj
      rw [relRules_of_ruleAt h₆₅ hr']
      obtain ⟨c, rfl⟩ := sameLhs_inv hw
      exact not_refTestTrueN G N)
  exact dderives_of_ruleAt h σ
    (QuantsOk.cons rfl (hs _ hρ) (QuantsOk.cons rfl (hf _ hρ)
      (QuantsOk.cons rfl (hr _ hρ) (QuantsOk.cons rfl (hrt _ hρ) QuantsOk.nil)))) (by eval_tac)
    (prems_one (.elsePr hel))

/-- **`ref.test` steps to `i32.const 0`** in every `simEnv B`, between typed images, whenever
SpecTec's `Ref_ok` fails at the reference and the instantiated type. -/
theorem fwdP_refTest0 (B : Builtins) {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
    (N : ∀ O : ElseI, ¬ DDerives (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [storeV hn s, refToValue r, CT.elemType (f.module.instRef rt)])) :
    FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 0]⟩ := by
  have T : TypingFacts (simEnv B) hn := Typing.typingFacts_simEnv B hn
  have rd : HasReadRules (envOfScript Specs.wasm30) := hasReadRules_wasm30
  exact RefsGC.fwd_of_sread T (hasStepRules_simEnv B).read fun hz hc =>
    sread_refTestFalseN (hasRuleAt_simEnv _ rd.refTestFalse) (hasRuleAt_simEnv _ rd.refTestTrue)
      (RefsGC.readTable_simEnv B) T (Typing.rTyping_simEnv B) (rStore_simEnv B) N hz hc

end Silmaril.Wasm.SpecTec.Sim.Round6.Refute
