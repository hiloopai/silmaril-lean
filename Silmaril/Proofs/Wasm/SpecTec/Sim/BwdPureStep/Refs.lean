module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Decode

/-!
# The reference rules of `Step_pure`, backward

`Backward.pure i` for `i` in 31–40 and 42–45 (`ref.i31`, `ref.is_null`, `ref.as_non_null`,
`ref.eq`, `i31.get`, `extern.convert_any`, `any.convert_extern`), at every `simEnv B`; `ref.i31`
and `i31.get-num` also need `$wrap__`/`$extend__` (`RefsGC.RFuns`). Each proof inverts the
rule's conclusion (`fires_two`, `fires_three`), decodes the code (`ref_of_var`, `head_*`), and
reads the premises back. An `otherwise` premise is refuted at a null (or equal) left-hand side
by exhibiting the earlier rule's derivation at the same scope (`otherwise_false`); for `ref.eq-false`
at two equal non-null references this is `ref.eq-true`, whose own `otherwise` is the family R
opcode criterion (`RefsGC.otherwise_of_ruleAt`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.SpecTec.Equiv.ExecRef
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- `eval_tac`, also reading variables off hypotheses `ρ.findVal? x = some v`. -/
macro "beval" : tactic => `(tactic| repeat (first
    | exact Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExps_nil'
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExps_cons'
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_tupE_of
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_listE_of
    | apply Silmaril.Wasm.SpecTec.Sim.evalExp_case
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_sub_of
    | exact Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_num'
    | (apply Silmaril.Wasm.SpecTec.Sim.evalExp_var; assumption)
    | (apply Silmaril.Wasm.SpecTec.Sim.evalExp_var; rfl)))

/-- An `otherwise` premise at `v` is refuted by an earlier rule firing on the same left-hand
side (under `noElse` premises and its own `otherwise`). -/
theorem otherwise_false {env : Env} {x : IL.Id} {k j : Nat} {r : Rule} {v w : Value}
    (ho : otherwise env x [] k v) (hj : j < k) (hr : HasRuleAt env x "%~>%" j r)
    (hs : SameLhs v w)
    (hb : RuleBody env (DDerives env noElse) (otherwiseAt env x [] j w) [] [] "%~>%" r w) :
    False := by
  obtain ⟨t, rules, hrel⟩ := Bwd.findRel_of_ruleAt hr
  exact Bwd.otherwise_elim ho j hj [] "%~>%" t rules r hrel (ruleAt_get hr hrel) w hs hb

/-- The `otherwise` premise of a rule whose only premise it is. -/
theorem else_of_prems {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv}
    (h : ∀ pr ∈ [Prem.elsePr], PremW env D els ρ pr) : els := by
  cases h _ (List.mem_singleton_self _) with
  | elsePr h => exact h

/-- `x = REF.NULL_ADDR` holds at a null reference. -/
theorem nullIf {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {x : IL.Id}
    (fx : ρ.findVal? x = some (refToValue .null)) :
    PremW env D els ρ (.ifPr (.cmpE .eqOp .boolT (.varE x) (.caseE "REF.NULL_ADDR" (.tupE [])))) :=
  .ifPr (RefsGC.evalExp_eq_true (evalExp_var fx) (by beval))

section Bwd

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} (B : Builtins)
variable {s : Store H} {f : Frame} {is : List Admin} {w : Value}

/-- The conclusion of a `Backward.pure` field. -/
abbrev PureBwd (P : Numerics.Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (is : List Admin) (w : Value) : Prop :=
  ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩

/-- `Backward.pure 32` (`ref.is_null-true`). -/
theorem bwd_isNullTrue (hf : Fires (simEnv B) "Step_pure" 32 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, hq, h₁, h₂, hr, hp⟩ := fires_two (simEnv_refRules B).refIsNullTrue hf
  obtain ⟨r, rfl, fr⟩ := ref_of_var hq (.head _) h₁
  obtain rfl := head_refIsNull (head_of_caseE h₂)
  obtain rfl := RefsGC.null_of_ifPr (evalExp_var fr) (hp _ (List.mem_singleton_self _))
  exact ⟨[constI32 1], EvalExp.unique hr (by beval), .reference .isNullTrue⟩

/-- `Backward.pure 33` (`ref.is_null-false`). -/
theorem bwd_isNullFalse (hf : Fires (simEnv B) "Step_pure" 33 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, hq, h₁, h₂, hr, hp⟩ := fires_two (simEnv_refRules B).refIsNullFalse hf
  obtain ⟨r, rfl, fr⟩ := ref_of_var hq (.head _) h₁
  obtain rfl := head_refIsNull (head_of_caseE h₂)
  refine ⟨[constI32 0], EvalExp.unique hr (by beval), .reference (.isNullFalse fun hn => ?_)⟩
  subst hn
  exact otherwise_false (else_of_prems hp) (by decide) (simEnv_refRules B).refIsNullTrue
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq, by beval, fun _ hpr => by
      rw [List.mem_singleton.1 hpr]; exact nullIf fr⟩

/-- `Backward.pure 34` (`ref.as_non_null-null`). -/
theorem bwd_asNonNullNull
    (hf : Fires (simEnv B) "Step_pure" 34 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, hq, h₁, h₂, hr, hp⟩ := fires_two (simEnv_refRules B).refAsNonNullNull hf
  obtain ⟨r, rfl, fr⟩ := ref_of_var hq (.head _) h₁
  obtain rfl := head_refAsNonNull (head_of_caseE h₂)
  obtain rfl := RefsGC.null_of_ifPr (evalExp_var fr) (hp _ (List.mem_singleton_self _))
  exact ⟨[.trap], EvalExp.unique hr (by beval), .reference .asNonNullNull⟩

/-- `Backward.pure 35` (`ref.as_non_null-addr`). -/
theorem bwd_asNonNullAddr
    (hf : Fires (simEnv B) "Step_pure" 35 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, hq, h₁, h₂, hr, hp⟩ := fires_two (simEnv_refRules B).refAsNonNullAddr hf
  obtain ⟨r, rfl, fr⟩ := ref_of_var hq (.head _) h₁
  obtain rfl := head_refAsNonNull (head_of_caseE h₂)
  refine ⟨[.ref r], EvalExp.unique hr (by beval), .reference (.asNonNullAddr fun hn => ?_)⟩
  subst hn
  exact otherwise_false (else_of_prems hp) (by decide) (simEnv_refRules B).refAsNonNullNull
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq, by beval, fun _ hpr => by
      rw [List.mem_singleton.1 hpr]; exact nullIf fr⟩

/-- `Backward.pure 42` (`extern.convert_any-null`). -/
theorem bwd_externConvertNull
    (hf : Fires (simEnv B) "Step_pure" 42 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, hq, h₁, h₂, hr, hp⟩ :=
    fires_two (simEnv_refRules B).externConvertAnyNull hf
  obtain ⟨r, rfl, fr⟩ := ref_of_var hq (.head _) h₁
  obtain rfl := head_externConvertAny (head_of_caseE h₂)
  obtain rfl := RefsGC.null_of_ifPr (evalExp_var fr) (hp _ (List.mem_singleton_self _))
  exact ⟨[.ref .null], EvalExp.unique hr (by beval), .reference .externConvertNull⟩

/-- `Backward.pure 43` (`extern.convert_any-addr`). -/
theorem bwd_externConvertAddr
    (hf : Fires (simEnv B) "Step_pure" 43 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, hq, h₁, h₂, hr, hp⟩ :=
    fires_two (simEnv_refRules B).externConvertAnyAddr hf
  obtain ⟨r, rfl, fr⟩ := ref_of_var hq (.head _) h₁
  obtain rfl := head_externConvertAny (head_of_caseE h₂)
  refine ⟨[.ref (.extern r)], EvalExp.unique hr (by beval),
    .reference (.externConvertAddr fun hn => ?_)⟩
  subst hn
  exact otherwise_false (else_of_prems hp) (by decide) (simEnv_refRules B).externConvertAnyNull
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq, by beval, fun _ hpr => by
      rw [List.mem_singleton.1 hpr]; exact nullIf fr⟩

/-- `Backward.pure 44` (`any.convert_extern-null`). -/
theorem bwd_anyConvertNull
    (hf : Fires (simEnv B) "Step_pure" 44 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, -, h₁, h₂, hr, -⟩ := fires_two (simEnv_refRules B).anyConvertExternNull hf
  obtain rfl := Typing.head_refNull (head_of_caseE h₁)
  obtain rfl := head_anyConvertExtern (head_of_caseE h₂)
  exact ⟨[.ref .null], EvalExp.unique hr (by beval), .reference .anyConvertNull⟩

/-- `Backward.pure 45` (`any.convert_extern-addr`). -/
theorem bwd_anyConvertAddr
    (hf : Fires (simEnv B) "Step_pure" 45 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, -, h₁, h₂, hr, -⟩ := fires_two (simEnv_refRules B).anyConvertExternAddr hf
  obtain ⟨r, rfl⟩ := head_refExtern (head_of_caseE h₁)
  obtain rfl := head_anyConvertExtern (head_of_caseE h₂)
  obtain ⟨u, hu, he⟩ := payload_of_caseE h₁
  have e : u = refToValue r := (Value.case.inj he).2.symm
  subst e
  refine ⟨[.ref r], EvalExp.unique hr ?_, .reference (.anyConvertAddr r)⟩
  exact RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (RefsGC.evalExp_sub_of hu)
    RefsGC.evalExps_nil')

/-- `Backward.pure 39` (`i31.get-null`). -/
theorem bwd_i31GetNull (hf : Fires (simEnv B) "Step_pure" 39 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, -, h₁, h₂, hr, -⟩ := fires_two (simEnv_refRules B).i31GetNull hf
  obtain rfl := Typing.head_refNull (head_of_caseE h₁)
  obtain ⟨sx, rfl⟩ := head_i31Get (head_of_caseE h₂)
  exact ⟨[.trap], EvalExp.unique hr (by beval), .reference (.i31GetNull sx)⟩

/-- `Backward.pure 40` (`i31.get-num`), given `$extend__`. -/
theorem bwd_i31GetNum (F : RefsGC.RFuns (simEnv B))
    (hf : Fires (simEnv B) "Step_pure" 40 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, -, h₁, h₂, hr, -⟩ := fires_two (simEnv_refRules B).i31GetNum hf
  obtain ⟨b, rfl⟩ := head_refI31Num (head_of_caseE h₁)
  obtain ⟨sx, rfl⟩ := head_i31Get (head_of_caseE h₂)
  obtain ⟨u₁, hu₁, he₁⟩ := payload_of_caseE h₁
  obtain ⟨u₂, hu₂, he₂⟩ := payload_of_caseE h₂
  have e₁ : u₁ = pctV b.toNat := (Value.case.inj he₁).2.symm
  have e₂ : u₂ = sxV sx := (Value.case.inj he₂).2.symm
  subst e₁ e₂
  have hx := F.extend (VarEnv.empty.bindVals σ) (.varE "sx") (.varE "i") sx b
    (valsOnly_bindVals σ) hu₂ hu₁
  refine ⟨_, EvalExp.unique hr ?_, .reference (.i31GetNum sx b)⟩
  cases sx <;>
    exact RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (evalExp_case (RefsGC.evalExp_tupE_of
      (RefsGC.evalExps_cons' (by beval) (RefsGC.evalExps_cons' hx RefsGC.evalExps_nil'))))
      RefsGC.evalExps_nil')

/-- `Backward.pure 31` (`ref.i31`), given `$wrap__`. -/
theorem bwd_refI31 (F : RefsGC.RFuns (simEnv B))
    (hf : Fires (simEnv B) "Step_pure" 31 (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  obtain ⟨σ, a₁, a₂, rfl, -, h₁, h₂, hr, -⟩ := fires_two (simEnv_refRules B).refI31 hf
  obtain ⟨u, hu, he⟩ := payload_of_caseE h₁
  obtain rfl := head_refI31 (head_of_caseE h₂)
  obtain ⟨u₁, u₂, hu₁, hu₂, rfl⟩ := State.evalExp_tup2_inv hu
  have e₁ : u₁ = caseNilV "I32" := EvalExp.unique hu₁ (by beval)
  subst e₁
  obtain ⟨c, rfl⟩ := (Typing.ctrlDecode_simEnv B).constI32 a₁ u₂ he
  have he' : Value.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]) =
      .case "CONST" (.tuple [caseNilV "I32", u₂]) := he
  have e₂ : u₂ = pctV c.toNat := by
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at he'
    exact he'.symm
  subst e₂
  have hw := F.wrap (VarEnv.empty.bindVals σ) (.varE "i") c (valsOnly_bindVals σ) hu₂
  exact ⟨[.ref (.i31 (c.setWidth 31))], EvalExp.unique hr (RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case hw) RefsGC.evalExps_nil')), .reference (.refI31 c)⟩

end Bwd

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
