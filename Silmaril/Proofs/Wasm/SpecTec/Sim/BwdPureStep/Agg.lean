module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Refs
public import Silmaril.Wasm.SpecTec.Sim.Aggregates.Thms

/-!
# Track bwd-pure-step: `array.new` and the aggregate traps, backward

`Backward.pure 41` (`array.new`: `val (CONST I32 n) (ARRAY.NEW x) ~> val^n (ARRAY.NEW_FIXED x n)`)
and the `Backward.step` fields 30 (`struct.set-null`), 33 (`array.set-null`) and 34
(`array.set-oob`, reading `$arrayinst(z)[a].FIELDS` back into the store's array `a`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

section Bwd

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins)
variable {s : Store H} {f : Frame} {is : List Admin} {w : Value}

/-- The image of `array.new`'s successor. -/
theorem adminsToV_arrayNew (v : Val) (c : BitVec 32) (x : TypeIdx) :
    adminsToV (vals (List.replicate c.toNat v) ++
      [.plain (.arrayNewFixed x ⟨c.toNat, c.isLt⟩)]) =
      List.replicate c.toNat (valV v) ++
        [.case "ARRAY.NEW_FIXED" (.tuple [Encode.toValue x, .case "%" (.tuple [.num (.natN c.toNat)])])] := by
  rw [adminsToV_append, adminsToV_vals, List.map_replicate]
  rfl

/-- `Backward.pure 41` (`array.new`). -/
theorem bwd_arrayNew (hf : Fires (simEnv B) "Step_pure" 41 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, a₃, rfl, hq, h₁, h₂, h₃, hr, -⟩ :=
    fires_three (hasRuleAt_simEnv B Equiv.ExecPureArrayNew.hasArrayNew_wasm30) hf
  obtain ⟨v, rfl, fv⟩ := val_of_var hq (.head _) h₁
  obtain ⟨c, rfl, hc⟩ := const32_of_lhs h₂
  obtain ⟨x, rfl⟩ := head_arrayNew (head_of_caseE h₃)
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (Encode.toValue x) :=
    idx_of_var' h₃ rfl
  have hn : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.varE "n") (.num (.natN c.toNat)) :=
    (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv hc))).1
  have fn := evalExp_varE_iff.1 hn
  have hrep := Vec.evalExp_iterListN_nodom (env := simEnv B) (ρ := VarEnv.empty.bindVals σ)
    (b := .subE (.varE "val") (.varT "val" []) (.varT "instr" [])) (eₙ := .varE "n")
    (k := c.toNat) hn (RefsGC.evalExp_sub_of (evalExp_var fv))
  refine ⟨_, ?_, .aggregate (.arrayNew v c)⟩
  rw [adminsToV_arrayNew]
  exact EvalExp.unique hr (evalExp_cat hrep (by beval))

/-- `Backward.step 30` (`struct.set-null`). -/
theorem bwd_structSetNull {c : Config H}
    (hf : Fires (simEnv B) "Step" 30 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).structSetNull hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain rfl := Typing.head_refNull (head_of_caseE h₁)
  obtain ⟨v, rfl, -⟩ := val_of_var hq (.tail _ (.head _)) h₂
  obtain ⟨x, i, rfl⟩ := head_structSet (head_of_caseE h₃)
  exact ⟨⟨s, f, [.trap]⟩, EvalExp.unique hr (by beval), .aggregate .structSetNull⟩

/-- `Backward.step 33` (`array.set-null`). -/
theorem bwd_arraySetNull {c : Config H}
    (hf : Fires (simEnv B) "Step" 33 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).arraySetNull hf
  obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := codes_four hes
  obtain rfl := Typing.head_refNull (head_of_caseE h₁)
  obtain ⟨i, rfl, -⟩ := const32_of_lhs h₂
  obtain ⟨v, rfl, -⟩ := val_of_var hq (.tail _ (.tail _ (.head _))) h₃
  obtain ⟨x, rfl⟩ := head_arraySet (head_of_caseE h₄)
  exact ⟨⟨s, f, [.trap]⟩, EvalExp.unique hr (by beval), .aggregate .arraySetNull⟩

/-- `$arrayinst(z)[a].FIELDS`'s length, read back into the store. -/
theorem arrayFields_of_eval {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {a : Nat}
    {v : Value} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (h : EvalExp (simEnv B) ρ (.lenE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")])
      (.varE "a")) "FIELDS")) v) :
    ∃ ai : ArrayInst, s.arrays[a]? = some ai ∧ v = .num (.natN ai.fields.length) := by
  obtain ⟨l, hl, rfl⟩ := evalExp_lenE_iff.1 h
  obtain ⟨u, hu, hfu⟩ := evalExp_dotE_iff.1 hl
  obtain ⟨L, k, hL, hk, hLk⟩ := evalExp_idxE_iff.1 hu
  have eL : L = .list (s.arrays.map arrayInstV) :=
    EvalExp.unique hL (Aggregates.evalExp_arrayinst (Aggregates.aggDefs_simEnv B)
      (Prims.findDef_none_of_valsOnly hρ _) (evalExp_var fz))
  have ek : Value.num (.natN k) = .num (.natN a) := EvalExp.unique hk (evalExp_var fa)
  simp only [Value.num.injEq, Num.natN.injEq] at ek
  subst eL ek
  simp only [Value.idx?, List.getElem?_map] at hLk
  obtain ⟨ai, hai, rfl⟩ := Option.map_eq_some_iff.1 hLk
  refine ⟨ai, hai, ?_⟩
  have e : Value.list l = .list (ai.fields.map fieldValV) :=
    Option.some.inj (hfu.symm.trans rfl)
  simp only [Value.list.injEq] at e
  rw [e, List.length_map]

/-- `Backward.step 34` (`array.set-oob`). -/
theorem bwd_arraySetOob {c : Config H}
    (hf : Fires (simEnv B) "Step" 34 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv B).arraySetOob hf
  obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := codes_four hes
  obtain ⟨n, rfl⟩ := head_refArray (head_of_caseE h₁)
  have fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN n)) := idx_of_var' h₁ rfl
  obtain ⟨i, rfl, hi⟩ := const32_of_lhs h₂
  obtain ⟨v, rfl, -⟩ := val_of_var hq (.tail _ (.tail _ (.tail _ (.head _)))) h₃
  obtain ⟨x, rfl⟩ := head_arraySet (head_of_caseE h₄)
  obtain ⟨v₁, v₂, e₁, e₂, hc⟩ := evalExp_cmpE_iff.1 (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  obtain ⟨ai, hai, rfl⟩ := arrayFields_of_eval B (valsOnly_bindVals σ) fz fa e₂
  have ev₁ : v₁ = .num (.natN i.toNat) := EvalExp.unique e₁ (RefsGC.evalExp_unpct hi)
  have hge : ai.fields.length ≤ i.toNat := by
    simpa [ev₁, cmpValues, Num.cmp, Res.ofOption] using hc
  exact ⟨⟨s, f, [.trap]⟩, EvalExp.unique hr (by beval), .aggregate (.arraySetOob hai hge)⟩

end Bwd

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
