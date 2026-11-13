module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XCtrl
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# Existence at `Wasm30.builtins` for the `throw_ref` handler cases

The redex `[HANDLER_n{c :: cs} (throwing a)]` is one handler. Besides the `Step_read` rule, four
`Step_pure` rules name `HANDLER` and force one instruction: `br-handler` (10), `return-handler`
(24), `handler-vals` (25) and `trap-handler` (28). The first three force `BR`, `RETURN` and
`TRAP` inside the handler's body (`ruleInner`, checked against the script by kernel `rfl`), which
`throwing a` avoids; `handler-vals` quantifies the body over `val*`, which `THROW_REF` is not.
`ctxt-handler` keeps the handler's catch list, so it is refuted by the shape of Core's
successor; `ctxt-instrs` can only step the empty code.

* `ruleInner_sound`, `not_fires_inner`: constructors forced inside a one-handler left-hand side.
* `not_fires_handlerVals`: `handler-vals` does not fire at `throwing a`.
* `sread_of_sstep_handler`: at every `simEnv B`, a `Step` fact from `z; [HANDLER (throwing a)]`
  that `ctxt-handler` does not produce is `Step/read`.
* `readH_builtins`, `readH_two_sided`: existence and uniqueness of the `Step_read` facts of
  `stepModel builtins` at `ReadH` redexes (`catch`, `catch_ref`, `next`), up to `CfgRel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn relRules relRules_simEnv)
open Silmaril.Wasm.SpecTec.Sim.Bwd (inv_pure inv_read inv_ctxtInstrs inv_ctxtHandler cfgV_inj)
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)

variable {H : Type}

/-! ## Constructors forced inside a handler's body -/

/-- The constructors a one-instruction left-hand side `[C(… , body)]` forces in `body`. -/
def innerTagsE : Exp → List MixopS
  | .listE [.caseE _ (.tupE es)] => (es.getLast?.map RefsGC.mustTags).getD []
  | _ => []

/-- `innerTagsE` of a conclusion `lhs ~> rhs`. -/
def concInner : Exp → List MixopS
  | .tupE [l, _] => innerTagsE l
  | _ => []

/-- `innerTagsE` of a rule's left-hand side. -/
def ruleInner : Rule → List MixopS
  | .ruleD _ _ _ e _ => concInner e

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `br-handler`, `return-handler` and `trap-handler` force `BR`, `RETURN`, `TRAP` in the body. -/
theorem ruleInner_pure :
    ((relRules (envOfScript Specs.wasm30) "Step_pure").map ruleInner)[10]? = some ["BR"] ∧
      ((relRules (envOfScript Specs.wasm30) "Step_pure").map ruleInner)[24]? = some ["RETURN"] ∧
      ((relRules (envOfScript Specs.wasm30) "Step_pure").map ruleInner)[28]? = some ["TRAP"] := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The last of a list of expressions denotes the last of its denotations. -/
theorem evalExps_getLast {env : Env} {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value} {e : Exp}, EvalExps env ρ es vs → es.getLast? = some e →
      ∃ v, vs.getLast? = some v ∧ EvalExp env ρ e v
  | [], _, _, _, he => absurd he (by simp)
  | [e₀], _, e, h, he => by
    obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 h
    have hws' : ws = [] := evalExps_nil_iff.1 hws
    have he' : e₀ = e := by simpa using he
    exact ⟨w, by rw [hws']; rfl, he' ▸ hw⟩
  | e₀ :: e₁ :: es, _, e, h, he => by
    obtain ⟨w, ws, -, hws, rfl⟩ := evalExps_cons_iff.1 h
    have he' : (e₁ :: es).getLast? = some e := by rw [← List.getLast?_cons_cons (a := e₀)]; exact he
    obtain ⟨v, hv, hev⟩ := evalExps_getLast hws he'
    obtain ⟨w₁, ws₁, -, -, rfl⟩ := evalExps_cons_iff.1 hws
    exact ⟨v, by rw [List.getLast?_cons_cons]; exact hv, hev⟩

/-- A one-instruction left-hand side with forced body constructors denotes a one-instruction
code whose body has them. -/
theorem innerTagsE_sound {env : Env} {ρ : VarEnv} {l : Exp} {h op : MixopS} {vs : List Value}
    (hl : EvalExp env ρ l (.list [.case h (.tuple vs)])) (hop : op ∈ innerTagsE l) :
    ∃ k w, vs.getLast? = some (.list k) ∧ Value.case op w ∈ k := by
  unfold innerTagsE at hop
  split at hop
  · rename_i hh es
    have hx : EvalExp env ρ (.caseE hh (.tupE es)) (.case h (.tuple vs)) := Exn.evalExp_list1_inv hl
    obtain ⟨u, hu, hue⟩ := evalExp_caseE_iff.1 hx
    obtain ⟨vs', hvs', hve⟩ := evalExp_tupE_iff.1 ((Value.case.inj hue).2 ▸ hu)
    have hes : EvalExps env ρ es vs := Value.tuple.inj hve ▸ hvs'
    cases hlast : es.getLast? with
    | none => simp [hlast] at hop
    | some e =>
      have hop' : op ∈ RefsGC.mustTags e := by simpa [hlast] using hop
      obtain ⟨v, hv, hev⟩ := evalExps_getLast hes hlast
      obtain ⟨k, hk, w, hw⟩ := RefsGC.mustTags_sound e hev hop'
      exact ⟨k, w, hk ▸ hv, hw⟩
  · simp at hop

/-- **Forced body constructors are sound** for a rule's left-hand side. -/
theorem ruleInner_sound {env : Env} {D : Interp} {els : Prop} {ps : List Param}
    {args : List ArgV} {opx : MixopS} {r : Rule} {h op : MixopS} {vs : List Value} {c : Value}
    (hb : RuleBody env D els ps args opx r (.tuple [.list [.case h (.tuple vs)], c]))
    (hop : op ∈ ruleInner r) : ∃ k w, vs.getLast? = some (.list k) ∧ Value.case op w ∈ k := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := hb
  simp only [ruleInner] at hop
  unfold concInner at hop
  split at hop
  · obtain ⟨vs₀, hvs₀, hv₀⟩ := evalExp_tupE_iff.1 he
    obtain ⟨u₁, ws, hl, -, rfl⟩ := evalExps_cons_iff.1 hvs₀
    have hu₁ : Value.list [.case h (.tuple vs)] = u₁ := by
      simp only [Value.tuple.injEq, List.cons.injEq] at hv₀
      exact hv₀.1
    exact innerTagsE_sound (hu₁ ▸ hl) hop
  · simp at hop

/-- **A rule forcing a body constructor the body avoids does not fire.** -/
theorem not_fires_inner {env : Env} {x : IL.Id} {i : Nat} {op : MixopS} {ops : List MixopS}
    (hT : ((relRules env x).map ruleInner)[i]? = some ops) (hop : op ∈ ops) {h : MixopS}
    {vs : List Value} {k : List Value} (hk : vs.getLast? = some (.list k)) {S : List MixopS}
    (hS : TagsIn S k) (hout : op ∉ S) {c : Value} :
    ¬ Fires env x i (.tuple [.list [.case h (.tuple vs)], c]) := by
  rintro ⟨t, rules, r, hrel, hr, hbody⟩
  have hrr : relRules env x = rules := by simp only [relRules, hrel]
  have hops : ruleInner r = ops := by
    rw [hrr, List.getElem?_map, hr] at hT
    exact Option.some.inj hT
  obtain ⟨k', w, hk', hw⟩ := ruleInner_sound hbody (hops ▸ hop)
  have hkk : k = k' := Value.list.inj (Option.some.inj (hk.symm.trans hk'))
  exact hout (hS _ (hkk ▸ hw) op w rfl)

/-! ## The rules that name `HANDLER` -/

/-- A rule whose row refutes the left-hand side does not fire, by index. -/
theorem not_fires_of_row {env : Env} {x : IL.Id} {T : List (List MixopS × Option Nat)}
    (hT : (relRules env x).map ruleInfo = T) {i : Nat} {a c : Value}
    (hb : ∀ row, T[i]? = some row → ∃ S n, LhsIs S n a ∧ Blk S n row) :
    ¬ Fires env x i (.tuple [a, c]) := by
  rintro ⟨t, rules, r, hrel, hr, hbody⟩
  have hrr : relRules env x = rules := by simp only [relRules, hrel]
  have hget : T[i]? = some (ruleInfo r) := by rw [← hT, hrr, List.getElem?_map, hr]; rfl
  obtain ⟨S, n, ha, hblk⟩ := hb _ hget
  exact not_ruleBody_of_blk ha hblk hbody

/-- The constructors of an image are the heads of its instructions. -/
theorem tagsIn_heads (l : List Admin) : TagsIn (l.map Typing.adminHead) (adminsToV l) := by
  intro x hx op w hxe
  rw [adminsToV_eq_map, List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  rw [Typing.adminToV_case hxe]
  exact List.mem_map_of_mem hb

/-- The image of a handler. -/
theorem adminsToV_handler (n : Nat) (cs : List Catch) (body : List Admin) :
    adminsToV [.handler n cs body] = [.case "HANDLER_%{%}%"
      (.tuple [.num (.natN n), .list (cs.map Encode.toValue), .list (adminsToV body)])] := rfl

/-- **`handler-vals` does not fire at `throwing a`**: the body is quantified over `val*`. -/
theorem not_fires_handlerVals (B : Builtins) {n : Nat} {cs : List Catch} {a : Nat} {w : Value} :
    ¬ Fires (simEnv B) "Step_pure" 25
      (.tuple [.list (adminsToV [.handler n cs (throwing a)]), w]) := by
  intro hf
  obtain ⟨-, ρ₀, σ, hps, hq, he, -⟩ := Exn.fires_body (simEnv_execRules B).handlerVals hf
  have hρ : VarEnv.empty = ρ₀ := Option.some.inj hps
  obtain ⟨hl, -⟩ := Exn.evalExp_tup2_inv (hρ ▸ he)
  obtain ⟨n', cs', body, hcode, -, -, hb⟩ := Exn.handler_decode hl
  obtain ⟨vs, hvs, -, ht⟩ := Exn.vals_quant (hρ ▸ hq) (by simp)
  have hbody : adminsToV body = vs := Value.list.inj (EvalExp.unique hb hvs)
  obtain ⟨vs', hvs'⟩ := (Typing.ctrlDecode_simEnv B).vals _ body ⟨rfl, rfl, rfl⟩ (hbody ▸ ht)
  have hth : throwing a = vals vs' := by
    have := (Admin.handler.inj (List.cons.inj hcode).1).2.2
    rw [this, hvs']
  have hlast : (vals vs').getLast? = some (.plain .throwRef) := by rw [← hth]; rfl
  obtain ⟨v, -, hv⟩ := List.mem_map.1 (List.mem_of_getLast? hlast)
  exact absurd hv (by rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin])

/-- The rows of `Step_pure` that a one-handler code does not refute by its constructor. -/
theorem pure_handler_rows :
    (pureInfoT.zipIdx.all fun p => outside ["HANDLER_%{%}%"] p.1 || [10, 24, 25, 28].contains p.2)
      = true := by
  decide +kernel

/-- **No `Step_pure` rule fires at `[HANDLER (throwing a)]`.** -/
theorem not_fires_pure_handler (B : Builtins) {n : Nat} {cs : List Catch} {a : Nat} (j : Nat)
    (v : Value) :
    ¬ Fires (simEnv B) "Step_pure" j
      (.tuple [.list (adminsToV [.handler n cs (throwing a)]), v]) := by
  have hT := (tables_simEnv B).pureT
  have hbody : TagsIn ["REF.EXN_ADDR", "THROW_REF"] (adminsToV (throwing a)) :=
    tagsIn_heads (throwing a)
  by_cases hj : j ∈ [10, 24, 25, 28]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact not_fires_inner (by rw [relRules_simEnv]; exact ruleInner_pure.1)
        (List.mem_singleton_self _) rfl hbody (by decide)
    · exact not_fires_inner (by rw [relRules_simEnv]; exact ruleInner_pure.2.1)
        (List.mem_singleton_self _) rfl hbody (by decide)
    · exact not_fires_handlerVals B
    · exact not_fires_inner (by rw [relRules_simEnv]; exact ruleInner_pure.2.2)
        (List.mem_singleton_self _) rfl hbody (by decide)
  · refine not_fires_of_row hT fun row hrow => ⟨_, 1, .inl ⟨_, rfl, tagsIn_heads _, rfl⟩, .inl ?_⟩
    have hp := List.all_eq_true.1 pure_handler_rows (row, j)
      (List.mk_mem_zipIdx_iff_getElem?.2 hrow)
    simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hp
    exact outside_spec (hp.resolve_right hj)

/-! ## The inversion at a handler -/

/-- The rows of `Step` from `ctxt-label` on that a one-handler code refutes by its constructor,
except `ctxt-handler` (index 1 of the rest). -/
theorem step_handler_rows :
    ((stepInfoT.drop 3).zipIdx.all fun p => outside ["HANDLER_%{%}%"] p.1 || p.2 == 1) = true := by
  decide +kernel

/-- Every row of the three tables names a constructor. -/
theorem rows_tagged :
    (pureInfoT.all (outside []) && readInfoT.all (outside []) && stepRestT.all (outside [])) =
      true := by
  decide +kernel

/-- The empty code is inert. -/
theorem inert_nil {env : Env} (Tb : Tables env) : Inert env [] := by
  have hk := rows_tagged
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hp, hr⟩, hs⟩ := hk
  have blk : ∀ {T : List (List MixopS × Option Nat)}, T.all (outside []) = true →
      ∀ row ∈ T, Blk [] 0 row :=
    fun hT row hrow => .inl (outside_spec (List.all_eq_true.1 hT row hrow))
  refine ⟨fun i v => ?_, fun i z v => ?_, fun i z v hi => ?_⟩
  · exact not_fires_of_blk Tb.pureT (Nat.zero_le i) fun row hrow =>
      ⟨[], 0, .inl ⟨[], rfl, fun _ h => absurd h List.not_mem_nil, rfl⟩, blk hp row hrow⟩
  · exact not_fires_of_blk Tb.readT (Nat.zero_le i) fun row hrow =>
      ⟨[], 0, .inr ⟨z, [], rfl, fun _ h => absurd h List.not_mem_nil, rfl⟩, blk hr row hrow⟩
  · exact not_fires_of_blk Tb.stepT hi fun row hrow =>
      ⟨[], 0, .inr ⟨z, [], rfl, fun _ h => absurd h List.not_mem_nil, rfl⟩, blk hs row hrow⟩

/-- `ctxt-instrs` does not fire at a one-instruction code: it would step the empty code. -/
theorem not_ctxt_one {env : Env} (Tb : Tables env) {x z w : Value}
    (hf : Fires env "Step" 2 (.tuple [cfgV z [x], w])) : False := by
  obtain ⟨z₁, z₁', vs, is, is', rest, -, hne, h₁, -, hs'⟩ := inv_ctxtInstrs Tb.rules.ctxtInstrs hf
  have hlen : vs.length + is.length + rest.length = 1 := by
    have e : [x] = vs ++ is ++ rest := (cfgV_inj h₁).2
    simpa only [List.length_append, List.length_singleton] using (congrArg List.length e).symm
  have his : is = [] := by
    rcases hne with h | h
    · have := List.length_pos_iff.2 h
      exact List.eq_nil_of_length_eq_zero (by omega)
    · have := List.length_pos_iff.2 h
      exact List.eq_nil_of_length_eq_zero (by omega)
  refine not_sstep Tb 1 [] (by simp) (fun A M C h => ?_) z₁ _ (his ▸ hs')
  have hM : M = [] := List.eq_nil_of_length_eq_zero (by
    have := congrArg List.length h
    simp only [List.length_append, List.length_nil] at this
    omega)
  exact hM ▸ inert_nil Tb

/-- No `Step` rule from `ctxt-label` on fires at a one-handler code, but `ctxt-handler`. -/
theorem not_fires_step_handler (B : Builtins) {n : Nat} {cs : List Catch} {a : Nat} {z w : Value}
    (i : Nat) (hi : 3 ≤ i) (hi4 : i ≠ 4) :
    ¬ Fires (simEnv B) "Step" i (.tuple [cfgV z (adminsToV [.handler n cs (throwing a)]), w]) := by
  refine not_fires_of_row (tables_simEnv B).stepT fun row hrow =>
    ⟨_, 1, .inr ⟨z, _, rfl, tagsIn_heads _, rfl⟩, .inl ?_⟩
  have hrow' : (stepInfoT.drop 3)[i - 3]? = some row := by
    rw [List.getElem?_drop, Nat.add_sub_cancel' hi]
    exact hrow
  have hp := List.all_eq_true.1 step_handler_rows (row, i - 3)
    (List.mk_mem_zipIdx_iff_getElem?.2 hrow')
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  exact outside_spec (hp.resolve_right (by omega))

/-- **Inversion at a handler**: at every `simEnv B`, a `Step` fact from
`z; [HANDLER_n{cs} (throwing a)]` that is not a handler with the same `n` and `cs` (which only
`ctxt-handler` produces) is `Step/read`. -/
theorem sread_of_sstep_handler (B : Builtins) {n : Nat} {cs : List Catch} {a : Nat} {z w : Value}
    (hw : ∀ z' is', w ≠ cfgV z' [.case "HANDLER_%{%}%"
      (.tuple [.num (.natN n), .list (cs.map Encode.toValue), .list is'])])
    (hs : SStep (simEnv B) (cfgV z (adminsToV [.handler n cs (throwing a)])) w) :
    ∃ js, w = cfgV z js ∧
      SRead (simEnv B) (cfgV z (adminsToV [.handler n cs (throwing a)])) js := by
  have Tb := tables_simEnv B
  obtain ⟨tt, rules, hrel⟩ := Tb.step
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf =>
    obtain ⟨z₁, is, js, h₁, -, hq⟩ := inv_pure Tb.rules.pure hf
    obtain ⟨tp, rp, hrelp⟩ := Tb.pure
    obtain ⟨j, hj⟩ := (dderives_iff_fires hrelp).1 hq
    exact absurd ((cfgV_inj h₁).2 ▸ hj) (not_fires_pure_handler B j _)
  | 1, hf =>
    obtain ⟨z₁, is, js, h₁, h₂, hq⟩ := inv_read Tb.rules.read hf
    have e : z = z₁ ∧ adminsToV [.handler n cs (throwing a)] = is := cfgV_inj h₁
    exact ⟨js, e.1 ▸ h₂, e.1 ▸ e.2 ▸ hq⟩
  | 2, hf => exact (not_ctxt_one Tb hf).elim
  | 4, hf =>
    obtain ⟨z₁, z₁', m, cs', is, is', h₁, h₂, -⟩ := inv_ctxtHandler Tb.rules.ctxtHandler hf
    have e : [Value.case "HANDLER_%{%}%" (.tuple [.num (.natN n), .list (cs.map Encode.toValue),
        .list (adminsToV (throwing a))])] =
        [.case "HANDLER_%{%}%" (.tuple [m, .list cs', .list is])] := (cfgV_inj h₁).2
    simp only [List.cons.injEq, Value.case.injEq, Value.tuple.injEq, Value.list.injEq,
      and_true, true_and] at e
    exact (hw z₁' is' (by rw [h₂, ← e.1, ← e.2.1])).elim
  | 3, hf => exact absurd hf (not_fires_step_handler B 3 (by omega) (by omega))
  | 5, hf => exact absurd hf (not_fires_step_handler B 5 (by omega) (by omega))
  | k + 6, hf => exact absurd hf (not_fires_step_handler B (k + 6) (by omega) (by omega))

/-! ## At `Wasm30.builtins` -/

/-- A one-instruction code `CfgRel`-related to an image: its instruction, the related one and the
`AdminEq` between them. -/
theorem cfgRel_one_rev {hn : H → String} {c : Config H} {z' y : Value}
    (hrel : SpecTec.CfgRel hn (configV hn c) (cfgV z' [y])) :
    ∃ a a₁ b, c.code = [a] ∧ adminToV a = adminToV a₁ ∧ Bwd.AdminEq a₁ b ∧ adminToV b = y := by
  obtain ⟨⟨s₁, f₁, l₁⟩, ⟨s₂, f₂, l₂⟩, ⟨-, -, hce⟩, h₁, h₂⟩ := hrel
  obtain ⟨b, hdb, hb⟩ : ∃ b, l₂ = [b] ∧ adminToV b = y := single_of_adminsToV (cfgV_inj h₂).2
  subst hdb
  obtain ⟨a₁, hc₁, hab⟩ : ∃ a₁, l₁ = [a₁] ∧ Bwd.AdminEq a₁ b := by
    cases hce with
    | cons hab hrest => cases hrest; exact ⟨_, rfl, hab⟩
  have himg : [adminToV a₁] = adminsToV c.code := by
    have e := (cfgV_inj h₁).2
    rw [e, hc₁]
    rfl
  obtain ⟨a, hca, ha⟩ := single_of_adminsToV himg
  exact ⟨a, a₁, b, hca, ha, hab, hb⟩

/-- `AdminEq` keeps the depth and catch list of a handler's image. -/
theorem adminEq_handler_rev {a b : Admin} (h : Bwd.AdminEq a b) {m L X : Value}
    (hb : adminToV b = .case "HANDLER_%{%}%" (.tuple [m, L, X])) :
    ∃ X₁, adminToV a = .case "HANDLER_%{%}%" (.tuple [m, L, X₁]) := by
  cases h with
  | refl => exact ⟨X, hb⟩
  | call _ h₂ =>
    exact absurd ((Typing.adminToV_case hb).trans (adminHead_callRef h₂)) (by decide)
  | label _ => exact absurd (Value.case.inj hb).1 (by decide)
  | handler _ =>
    have e := Value.tuple.inj (Value.case.inj hb).2
    simp only [List.cons.injEq] at e
    exact ⟨_, by rw [← e.1, ← e.2.1]; rfl⟩
  | frame _ => exact absurd (Value.case.inj hb).1 (by decide)

/-- `ReadH` redexes are `CtrlRead` redexes. -/
theorem ReadH.toCtrl {c : Config H} {is' : List Admin} (h : ReadH c is') :
    FwdX30.CtrlRead c is' := by
  cases h with
  | catch_ he ht => exact .throwRefHandlerCatch he ht
  | catchRef he ht => exact .throwRefHandlerCatchRef he ht
  | next h => exact .throwRefHandlerNext h

/-- The catch lists of a `ReadH` redex and its successor differ, or the successor is not one
handler. -/
theorem readH_succ {c : Config H} {is' : List Admin} (hr : ReadH c is') :
    ∃ n cs a, c.code = [.handler n cs (throwing a)] ∧ ∀ a' X, is' = [a'] →
      adminToV a' ≠ .case "HANDLER_%{%}%"
        (.tuple [.num (.natN n), .list (cs.map Encode.toValue), X]) := by
  cases hr with
  | catch_ =>
    refine ⟨_, _, _, rfl, fun a' X his ha => ?_⟩
    obtain ⟨-, hb⟩ := (List.append_eq_singleton_iff.1 his).resolve_right (fun h => by simp at h)
    have hb' : Admin.plain (.br _) = a' := (List.cons.inj hb).1
    have hh : "HANDLER_%{%}%" = Typing.adminHead a' := Typing.adminToV_case ha
    rw [← hb'] at hh
    exact absurd hh (by simp [Typing.adminHead, Typing.instrHead])
  | catchRef =>
    refine ⟨_, _, _, rfl, fun a' X his _ => ?_⟩
    have := congrArg List.length his
    simp at this
  | next =>
    refine ⟨_, _, _, rfl, fun a' X his ha => ?_⟩
    obtain rfl := (List.cons.inj his).1.symm
    have e := Value.tuple.inj (Value.case.inj ha).2
    simp only [List.cons.injEq, Value.list.injEq] at e
    have := congrArg List.length e.2.1
    simp at this

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- At a `ReadH` redex, the `Step` observations `CfgRel`-related to Core's successor are not
`ctxt-handler` steps. -/
theorem readH_not_ctxt {c : Config H} {is' : List Admin} (hr : ReadH c is') {w : Value}
    (hrel : SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w) :
    ∃ n cs a, c.code = [.handler n cs (throwing a)] ∧ ∀ z' is'', w ≠ cfgV z' [.case "HANDLER_%{%}%"
      (.tuple [.num (.natN n), .list (cs.map Encode.toValue), .list is''])] := by
  obtain ⟨n, cs, a, hcode, hsucc⟩ := readH_succ hr
  refine ⟨n, cs, a, hcode, fun z' is'' hw => ?_⟩
  obtain ⟨a', a₁, b, hca, himg, hab, hb⟩ := cfgRel_one_rev (hw ▸ hrel)
  obtain ⟨X₁, ha₁⟩ := adminEq_handler_rev hab hb
  exact hsucc a' X₁ hca (himg.trans ha₁)

/-- **Existence at `builtins` for the `throw_ref` handler cases**: on `DomDet`, Core's
successor is a `Step_read` fact of `stepModel builtins` up to `CfgRel`. -/
theorem readH_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadH c is') :
    ∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  have hx : FwdX30.ReadHeadX (Profile.spec nd r) c is' := .ctrl hr.toCtrl
  obtain ⟨⟨w, hw, hrel⟩, -⟩ :=
    FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc hx.step
  obtain ⟨n, cs, a, hcode, hnot⟩ := readH_not_ctxt hr hrel
  have hnc : ¬ Round6.Target.CastRedex c.code := hx.not_castRedex
  have hs : SStep EB
      (cfgV (stateV hn c.store c.frame) (adminsToV [.handler n cs (throwing a)])) w :=
    hcode ▸ (Round6.Transfer.sstepB_iff_of_not_castRedex _ hn hnc w).1 hw
  obtain ⟨js, hjs, hq⟩ := sread_of_sstep_handler _ hnot hs
  have hq' : SRead EB (configV hn c) js := by rw [Bwd.configV_eq, hcode]; exact hq
  exact ⟨js, (Round6.Transfer.sReadB_iff_noCast hnc).2 hq', hjs ▸ hrel⟩

/-- **`Step_read` at `builtins` is two-sided at the `throw_ref` handler cases.** -/
theorem readH_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hr : ReadH c is') :
    (∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js)) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
          (cfgV (stateV hn c.store c.frame) js) :=
  ⟨readH_builtins hc hr, fun _ hjs hq =>
    FwdX30Fin.readFact_unique_builtins hc
      (FwdX30.ReadHeadX.ctrl (P := Profile.spec nd r) hr.toCtrl).step hjs hq⟩

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
