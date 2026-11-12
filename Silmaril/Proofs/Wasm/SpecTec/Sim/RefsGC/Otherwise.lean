module

public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Provenance
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `otherwise` premises by opcode

`otherwiseAt_of_table`: rule `i` of a relation may use its `otherwise` premise at `(a, b)` when
every earlier rule either names an instruction constructor that cannot occur in `a` (checked by
`checkAvoid` against a tag table, a `decide` over string literals) or is one of a short list of
exceptions refuted by hand. `pureTagTable_eq`/`readTagTable_eq` tie the tables to the pinned script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Forced constructors are present -/

/-- A list of expressions whose literal injections name `op` denotes a list containing an
injection named `op`. -/
theorem evalExps_caseTag {env : Env} {ρ : VarEnv} {op : MixopS} :
    ∀ {es : List Exp} {vs : List Value}, EvalExps env ρ es vs → op ∈ es.filterMap caseTag? →
      ∃ w, Value.case op w ∈ vs
  | [], _, _, hm => by simp at hm
  | e :: es, vs, h, hm => by
      obtain ⟨w, ws, he, hes, rfl⟩ := evalExps_cons_iff.1 h
      rw [List.filterMap_cons] at hm
      cases e with
      | caseE op' e' =>
          simp only [caseTag?, List.mem_cons] at hm
          rcases hm with rfl | hm
          · obtain ⟨u, -, rfl⟩ := evalExp_caseE_iff.1 he
            exact ⟨u, List.mem_cons_self⟩
          · obtain ⟨u, hu⟩ := evalExps_caseTag hes hm
            exact ⟨u, List.mem_cons_of_mem _ hu⟩
      | _ =>
          simp only [caseTag?] at hm
          obtain ⟨u, hu⟩ := evalExps_caseTag hes hm
          exact ⟨u, List.mem_cons_of_mem _ hu⟩

/-- A value of `cat?` that is a list, from a list on the left. -/
theorem cat?_list_left {a : List Value} {v₂ v : Value} (h : Value.cat? (.list a) v₂ = some v) :
    ∃ b, v₂ = .list b ∧ v = .list (a ++ b) := by
  cases v₂ <;> simp [Value.cat?] at h
  exact ⟨_, rfl, h.symm⟩

/-- A value of `cat?` that is a list, from a list on the right. -/
theorem cat?_list_right {b : List Value} {v₁ v : Value} (h : Value.cat? v₁ (.list b) = some v) :
    ∃ a, v₁ = .list a ∧ v = .list (a ++ b) := by
  cases v₁ with
  | list a => simp only [Value.cat?, Option.some.injEq] at h; exact ⟨a, rfl, h.symm⟩
  | opt o => cases o <;> simp [Value.cat?] at h
  | _ => simp [Value.cat?] at h

/-- **Forced constructors are present.** A pattern naming `op` among its forced constructors
denotes a list with an injection named `op` at top level. -/
theorem mustTags_sound {env : Env} {ρ : VarEnv} {op : MixopS} :
    ∀ (e : Exp) {v : Value}, EvalExp env ρ e v → op ∈ mustTags e →
      ∃ l, v = .list l ∧ ∃ w, Value.case op w ∈ l
  | e, v, h, hm => by
      cases e with
      | listE es =>
          obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
          exact ⟨vs, rfl, evalExps_caseTag hvs hm⟩
      | catE e₁ e₂ =>
          obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_catE_iff.1 h
          rcases List.mem_append.1 hm with hm | hm
          · obtain ⟨a, rfl, w, hw⟩ := mustTags_sound e₁ h₁ hm
            obtain ⟨b, -, rfl⟩ := cat?_list_left hc
            exact ⟨_, rfl, w, List.mem_append_left _ hw⟩
          · obtain ⟨b, rfl, w, hw⟩ := mustTags_sound e₂ h₂ hm
            obtain ⟨a, -, rfl⟩ := cat?_list_right hc
            exact ⟨_, rfl, w, List.mem_append_right _ hw⟩
      | _ => simp [mustTags] at hm

/-- A pattern forcing a constructor outside `S` does not denote a list whose constructors lie
in `S`. -/
theorem not_evalExp_mustTags {env : Env} {ρ : VarEnv} {S : List MixopS} {c : Exp} {op : MixopS}
    {k : List Value} (hS : op ∉ S) (hc : EvalExp env ρ c (.list k)) (hm : op ∈ mustTags c)
    (hk : TagsIn S k) : False := by
  obtain ⟨k', hk', w, hw⟩ := mustTags_sound c hc hm
  have hkk : k = k' := Value.list.inj hk'
  subst hkk
  exact hS (hk _ hw op w rfl)

/-- The code component of an evaluated `z; instr*` pattern. -/
theorem code_of_cfg {env : Env} {ρ : VarEnv} {z c : Exp} {v : Value}
    (he : EvalExp env ρ (.caseE "%;%" (.tupE [z, c])) v) :
    ∃ u w, EvalExp env ρ c w ∧ v = .case "%;%" (.tuple [u, w]) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 he
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨u₁, ws, -, hws, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨u₂, ws', hc, hnil, rfl⟩ := evalExps_cons_iff.1 hws
  obtain rfl : ws' = [] := evalExps_nil_iff.1 hnil
  exact ⟨u₁, u₂, hc, rfl⟩

/-- A left-hand side with a forced constructor outside `S` does not denote a value whose code has
its constructors in `S`. -/
theorem not_evalExp_codeTags {env : Env} {ρ : VarEnv} {S : List MixopS} {l : Exp} {a : Value}
    {op : MixopS} (ha : LhsIn S a) (hop : op ∈ codeTags l) (hS : op ∉ S)
    (he : EvalExp env ρ l a) : False := by
  unfold codeTags at hop
  split at hop
  · obtain ⟨u, w, hc, rfl⟩ := code_of_cfg he
    rcases ha with ⟨k, hk, -⟩ | ⟨z', k, hk, hkS⟩
    · cases hk
    · have hw : w = .list k := by
        simp only [cfgV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at hk
        exact hk.2.2.1
      subst hw
      exact not_evalExp_mustTags hS hc hop hkS
  · rcases ha with ⟨k, rfl, hkS⟩ | ⟨z', k, rfl, -⟩
    · exact not_evalExp_mustTags hS he hop hkS
    · obtain ⟨k', hk', -⟩ := mustTags_sound l he hop
      cases hk'

/-- **An earlier rule naming a foreign constructor does not fire.** -/
theorem not_ruleBody_of_tags {env : Env} {D : Interp} {els : Prop} {ps : List Param}
    {args : List ArgV} {opx : MixopS} {r : Rule} {S : List MixopS} {a c : Value} {op : MixopS}
    (ha : LhsIn S a) (hop : op ∈ ruleTags r) (hS : op ∉ S) :
    ¬ RuleBody env D els ps args opx r (.tuple [a, c]) := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  rintro ⟨-, ρ₀, σ, -, -, he, -⟩
  simp only [ruleTags] at hop
  unfold concTags at hop
  split at hop
  · rename_i l rh
    obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 he
    obtain ⟨u₁, ws, hl, -, rfl⟩ := evalExps_cons_iff.1 hvs
    simp only [Value.tuple.injEq, List.cons.injEq] at hv
    rw [← hv.1] at hl
    exact not_evalExp_codeTags ha hop hS hl
  · simp at hop

/-- `checkAvoid`, unfolded. -/
theorem checkAvoid_sound {T : List (List MixopS)} {i : Nat} {exc : List Nat} {S : List MixopS}
    (h : checkAvoid T i exc S = true) {j : Nat} (hj : j < i) (hx : j ∉ exc) :
    ∃ op ∈ T[j]?.getD [], op ∉ S := by
  simp only [checkAvoid, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  rcases h j hj with h | h
  · exact absurd (by simpa using h) hx
  · exact h

/-- **`otherwise` by opcode.** Rule `i` of `x` may use `otherwise` at `(a, b)` when, by the tag
table `T` of `x`'s rules, every earlier rule outside `exc` names a constructor outside `S ⊇` the
constructors of `a`, and the rules in `exc` are refuted separately. -/
theorem otherwiseAt_of_table {env : Env} {x : IL.Id} {t : Typ} {rules : List Rule}
    (hrel : env.findRel? x = some ([], "%~>%", t, rules)) {T : List (List MixopS)}
    (hT : ∀ j r, rules[j]? = some r → j < T.length → ruleTags r = T[j]?.getD [])
    {i : Nat} (hi : i ≤ T.length) {S : List MixopS} {exc : List Nat} {a b : Value}
    (ha : LhsIn S a) (hc : checkAvoid T i exc S = true)
    (hexc : ∀ j ∈ exc, j < i → ∀ r, rules[j]? = some r → ∀ w, SameLhs (.tuple [a, b]) w →
      ¬ RuleBody env (DDerives env noElse) (otherwiseAt env x [] j w) [] [] "%~>%" r w) :
    otherwiseAt env x [] i (.tuple [a, b]) := by
  rw [otherwiseAt]
  intro j hj ps op t' rules' r hrel' hr w hw
  rw [hrel] at hrel'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hrel'
  by_cases hx : j ∈ exc
  · exact hexc j hx hj r hr w hw
  · obtain ⟨op', hop', hS⟩ := checkAvoid_sound hc hj hx
    obtain ⟨a', b', c', h₁, rfl⟩ := hw
    simp only [Value.tuple.injEq, List.cons.injEq] at h₁
    obtain ⟨rfl, -⟩ := h₁
    rw [← hT j r hr (by omega)] at hop'
    exact not_ruleBody_of_tags ha hop' hS

/-! ## The tag tables, against the pinned script -/

/-- The rules of a relation, by name. -/
def relRules (env : Env) (x : IL.Id) : List Rule :=
  match env.findRel? x with
  | some (_, _, _, rs) => rs
  | none => []

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `pureTagTable` is the tag table of the first 46 rules of `Step_pure`. -/
theorem pureTagTable_eq :
    ((relRules (envOfScript Specs.wasm30) "Step_pure").map ruleTags).take 46 = pureTagTable := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `readTagTable` is the tag table of the 103 rules of `Step_read`. -/
theorem readTagTable_eq :
    ((relRules (envOfScript Specs.wasm30) "Step_read").map ruleTags).take 103 = readTagTable := by
  rfl

/-- A tag table read off a prefix of a relation's rules. -/
theorem tags_of_take {env : Env} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} (hrel : env.findRel? x = some (ps, op, t, rules)) {n : Nat}
    {T : List (List MixopS)} (hT : ((relRules env x).map ruleTags).take n = T) :
    ∀ j r, rules[j]? = some r → j < T.length → ruleTags r = T[j]?.getD [] := by
  intro j r hr hj
  simp only [relRules, hrel] at hT
  subst hT
  simp only [List.length_take, List.length_map] at hj
  simp [(Nat.lt_min.1 hj).1, hr]

end Silmaril.Wasm.SpecTec.Sim.RefsGC
