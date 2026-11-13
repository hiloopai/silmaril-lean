module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DTables
public import Silmaril.Wasm.SpecTec.Institution.FwdB30X.Thms

/-!
# Inverting `Step` at a redex of unbounded arity, at every evaluator

The redexes of `struct.new`, `array.new_fixed` and `throw` are a value prefix of any length
followed by one instruction named `t`, and the `Step` rule that fires there forces no length. So
`FwdB30S.stepOk` cannot refute `ctxt-instrs` at a proper infix: the same rule could fire at a
shorter suffix. It can be refuted from the successor instead. A `ctxt-instrs` step keeps a
non-empty prefix or suffix of the redex:

* a kept suffix ends in the `t` instruction, which Core's successor does not contain;
* a kept non-empty prefix leaves the stepped suffix a successor strictly shorter than Core's. A
  suffix ending in `t` steps to no code shorter than every right-hand side that names only
  constructors of `t :: valTags` (`no_sstep_short`, by recursion on the length).

* `rhsLen_sound`, `not_fires_rhs`: forced right-hand-side lengths are sound.
* `no_sstep_short`: no `Step` from a suffix ending in `t` to a short code without `t`.
* `sstep_head_tail`: **a `Step` fact from such a redex to a code of length at most `M` without
  `t` is a rule of `Step` from rule 6 on, fired at the whole redex.**
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30D

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn relRules)
open Silmaril.Wasm.SpecTec.Sim.Bwd (inv_pure inv_read inv_ctxtInstrs cfgV_inj)
open Silmaril.Wasm.SpecTec.Institution.FwdB30X

variable {env : Env}

/-! ## Forced right-hand sides -/

/-- Every list has its own constructors. -/
theorem tagsIn_self (l : List Value) :
    TagsIn (l.flatMap fun x => match x with | .case op _ => [op] | _ => []) l := by
  intro x hx op w hxe
  subst hxe
  exact List.mem_flatMap.2 ⟨_, hx, List.mem_singleton_self _⟩

/-- **Forced right-hand-side lengths are sound**: a rule whose right-hand side forces a code of
length `m` concludes only at code of length `m`. -/
theorem rhsLen_sound {D : Interp} {els : Prop} {ps : List Param} {args : List ArgV}
    {opx : MixopS} {r : Rule} {m : Nat} {a z : Value} {js : List Value} (hm : rhsLen r = some m)
    (hb : RuleBody env D els ps args opx r (.tuple [a, cfgV z js])) : js.length = m := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := hb
  simp only [rhsLen] at hm
  unfold concRhs at hm
  split at hm
  · obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 he
    obtain ⟨u₁, ws, -, hws, rfl⟩ := evalExps_cons_iff.1 hvs
    obtain ⟨u₂, ws', hr, -, rfl⟩ := evalExps_cons_iff.1 hws
    have hu₂ : cfgV z js = u₂ := by
      simp only [Value.tuple.injEq, List.cons.injEq] at hv
      exact hv.2.1
    exact (codeLen_sound (.inr ⟨z, js, rfl, tagsIn_self js, rfl⟩) hm (hu₂ ▸ hr)).symm
  · simp at hm

/-- A rule of `Step` whose right-hand side forces another length does not fire. -/
theorem not_fires_rhs (hR : (relRules env "Step").map rhsLen = stepRhsT) {i m : Nat}
    (hi : stepRhsT[i]? = some (some m)) {a z : Value} {js : List Value} (hne : js.length ≠ m) :
    ¬ Fires env "Step" i (.tuple [a, cfgV z js]) := by
  rintro ⟨t, rules, r, hrel, hr, hbody⟩
  have hrr : relRules env "Step" = rules := by simp only [relRules, hrel]
  have hm : rhsLen r = some m := by
    rw [← hR, hrr, List.getElem?_map, hr] at hi
    exact Option.some.inj hi
  exact hne (rhsLen_sound hm hbody)

/-- **A rule of `Step` from rule 3 on does not fire** from code with constructors in
`t :: valTags` to code shorter than `M`, when `rhsOk t M`. -/
theorem not_fires_step_short (Tb : Tables env) (hR : (relRules env "Step").map rhsLen = stepRhsT)
    {t : MixopS} {M : Nat} (hok : rhsOk t M = true) {i : Nat} (hi : 3 ≤ i) {l : List Value}
    (hl : TagsIn (t :: valTags) l) {z z' : Value} {js : List Value} (hjs : js.length < M) :
    ¬ Fires env "Step" i (.tuple [cfgV z l, cfgV z' js]) := by
  intro hf
  obtain ⟨tt, rules, r, hrel, hr, hbody⟩ := hf
  have hrr : relRules env "Step" = rules := by simp only [relRules, hrel]
  have hinfo : stepInfoT[i]? = some (ruleInfo r) := by
    rw [← Tb.stepT, hrr, List.getElem?_map, hr]; rfl
  have hrhs : stepRhsT[i]? = some (rhsLen r) := by
    rw [← hR, hrr, List.getElem?_map, hr]; rfl
  have hlt : i < 36 := by
    have hlen : i < stepInfoT.length := (List.getElem?_eq_some_iff.1 hinfo).1
    simpa [stepInfoT] using hlen
  have hc : (i < 3 || outside (t :: valTags) (stepInfoT.getD i ([], none)) ||
      (stepRhsT.getD i none).any (M ≤ ·)) = true :=
    List.all_eq_true.1 hok i (List.mem_range.2 hlt)
  have hc' : i < 3 ∨ outside (t :: valTags) (ruleInfo r) = true ∨
      ∃ m, rhsLen r = some m ∧ M ≤ m := by
    cases hrl : rhsLen r <;>
      simpa [List.getD_eq_getElem?_getD, hinfo, hrhs, hrl, or_assoc] using hc
  rcases hc' with hc' | hc' | ⟨m, hm, hMm⟩
  · omega
  · exact not_ruleBody_of_blk (.inr ⟨z, l, rfl, hl, rfl⟩) (.inl (outside_spec hc')) hbody
  · exact absurd (rhsLen_sound hm hbody) (by omega)

/-! ## The recursion -/

/-- The last element of a non-empty suffix is the last element. -/
theorem getLast?_append_of_ne {l m : List Value} (h : m ≠ []) :
    (l ++ m).getLast? = m.getLast? := by
  rw [List.getLast?_append]
  cases hm : m.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 hm) h
  | some x => rfl

/-- A `Step_pure` rule does not fire at code all of whose rows are refuted by its constructors. -/
theorem not_pure_tags (Tb : Tables env) {t : MixopS} (hp : chkTags t pureInfoT = true)
    {l : List Value} (hl : TagsIn (t :: valTags) l) {z w : Value} :
    ¬ Fires env "Step" 0 (.tuple [cfgV z l, w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, hq⟩ := inv_pure Tb.rules.pure hf
  obtain ⟨tp, rp, hrelp⟩ := Tb.pure
  obtain ⟨j, hj⟩ := (dderives_iff_fires hrelp).1 hq
  rw [← (cfgV_inj h₁).2] at hj
  exact not_fires_of_blk Tb.pureT (Nat.zero_le j) (fun row hrow =>
    ⟨_, _, .inl ⟨l, rfl, hl, rfl⟩,
      .inl (outside_spec (List.all_eq_true.1 hp row (by simpa using hrow)))⟩) hj

/-- A `Step_read` rule does not fire at code all of whose rows are refuted by its
constructors. -/
theorem not_read_tags (Tb : Tables env) {t : MixopS} (hrd : chkTags t readInfoT = true)
    {l : List Value} (hl : TagsIn (t :: valTags) l) {z w : Value} :
    ¬ Fires env "Step" 1 (.tuple [cfgV z l, w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, hq⟩ := inv_read Tb.rules.read hf
  obtain ⟨tr, rr, hrelr⟩ := Tb.read
  obtain ⟨j, hj⟩ := (dderives_iff_fires hrelr).1 hq
  rw [← (cfgV_inj h₁).2] at hj
  exact not_fires_of_blk Tb.readT (Nat.zero_le j) (fun row hrow =>
    ⟨_, _, .inr ⟨_, l, rfl, hl, rfl⟩,
      .inl (outside_spec (List.all_eq_true.1 hrd row (by simpa using hrow)))⟩) hj

/-- Infix constructors. -/
theorem tagsIn_infix {S : List MixopS} {l A M C : List Value} (hl : TagsIn S l)
    (he : l = A ++ M ++ C) : TagsIn S M :=
  fun x hx => hl x (by rw [he]; simp [hx])

/-- The decomposition of `ctxt-instrs` at a redex ending in `t`, to a code without `t`: the kept
suffix is empty, and a non-empty value prefix is kept, so the stepped suffix ends in `t` and
steps to a strictly shorter code without `t`. -/
theorem ctxt_split {t : MixopS} {l vs is is' rest js : List Value} {w₀ : Value}
    (hlast : l.getLast? = some (.case t w₀)) (hjs : ∀ w, Value.case t w ∉ js)
    (hne : vs ≠ [] ∨ rest ≠ []) (el : l = vs ++ is ++ rest) (ej : js = vs ++ is' ++ rest) :
    rest = [] ∧ vs ≠ [] ∧ l = vs ++ is ∧ js = vs ++ is' := by
  have hrest : rest = [] := by
    by_contra hr
    have hmem : Value.case t w₀ ∈ rest := by
      rw [el, getLast?_append_of_ne hr] at hlast
      exact List.mem_of_getLast? hlast
    exact hjs w₀ (by rw [ej]; simp [hmem])
  subst hrest
  exact ⟨rfl, hne.resolve_right (fun h => h rfl), by simpa using el, by simpa using ej⟩

/-- **No `Step` from a suffix ending in `t` to a short code without `t`**: at every evaluator
with the wasm-3.0 tables, if no `Step_pure` or `Step_read` rule names only constructors of
`t :: valTags`, and every such `Step` rule forces a right-hand side of length at least `M`, then
code with constructors in `t :: valTags` ending in `t` takes no `Step` to a code without `t` of
length below `M`. -/
theorem no_sstep_short (Tb : Tables env) (hR : (relRules env "Step").map rhsLen = stepRhsT)
    {t : MixopS} {M : Nat} (hp : chkTags t pureInfoT = true) (hrd : chkTags t readInfoT = true)
    (hok : rhsOk t M = true) :
    ∀ (n : Nat) (l : List Value), l.length < n → TagsIn (t :: valTags) l →
      ∀ {w₀ : Value}, l.getLast? = some (.case t w₀) →
      ∀ z z' (js : List Value), js.length < M → (∀ w, Value.case t w ∉ js) →
      ¬ SStep env (cfgV z l) (cfgV z' js)
  | 0, _, hlt, _, _, _, _, _, _, _, _, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, l, hlt, hl, w₀, hlast, z, z', js, hjM, hjs, hs => by
    obtain ⟨tt, rules, hrel⟩ := Tb.step
    obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
    match i, hf with
    | 0, hf => exact not_pure_tags Tb hp hl hf
    | 1, hf => exact not_read_tags Tb hrd hl hf
    | 2, hf =>
      obtain ⟨z₁, z₁', vs, is, is', rest, -, hne, h₁, h₂, hs'⟩ :=
        inv_ctxtInstrs Tb.rules.ctxtInstrs hf
      have el : l = vs ++ is ++ rest := (cfgV_inj h₁).2
      have ej : js = vs ++ is' ++ rest := (cfgV_inj h₂).2
      obtain ⟨-, hvs, el', ej'⟩ := ctxt_split hlast hjs hne el ej
      have hvl : 0 < vs.length := List.length_pos_iff.2 hvs
      cases is with
      | nil =>
        refine not_sstep Tb 1 [] (by simp) (fun A M' C h => ?_) z₁ _ hs'
        have hM : M' = [] := (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1).2
        exact hM ▸ inert_nil Tb
      | cons x xs =>
        have hlen : (x :: xs).length < n := by
          have := congrArg List.length el'
          simp only [List.length_append] at this
          omega
        have hlast' : (x :: xs).getLast? = some (.case t w₀) := by
          rw [el', getLast?_append_of_ne (List.cons_ne_nil _ _)] at hlast
          exact hlast
        have hjM' : is'.length < M := by
          have := congrArg List.length ej'
          simp only [List.length_append] at this
          omega
        have hjs' : ∀ w, Value.case t w ∉ is' := fun w hw => hjs w (by rw [ej']; simp [hw])
        exact no_sstep_short Tb hR hp hrd hok n (x :: xs) hlen
          (tagsIn_infix (A := vs) (C := []) hl (by rw [el', List.append_nil])) hlast' z₁ z₁' is'
          hjM' hjs' hs'
    | k + 3, hf => exact not_fires_step_short Tb hR hok (by omega) hl hjM hf

/-- **`ctxt-instrs` does not step a redex ending in `t` to a code without `t` of length at most
`M`**: it would step a proper suffix to a shorter code (`no_sstep_short`). -/
theorem not_ctxt_tail (Tb : Tables env) (hR : (relRules env "Step").map rhsLen = stepRhsT)
    {t : MixopS} {M : Nat} (hp : chkTags t pureInfoT = true) (hrd : chkTags t readInfoT = true)
    (hok : rhsOk t M = true) {l : List Value} (hl : TagsIn (t :: valTags) l) {w₀ : Value}
    (hlast : l.getLast? = some (.case t w₀)) {z z' : Value} {js : List Value}
    (hjM : js.length ≤ M) (hjs : ∀ w, Value.case t w ∉ js)
    (hf : Fires env "Step" 2 (.tuple [cfgV z l, cfgV z' js])) : False := by
  obtain ⟨z₁, z₁', vs, is, is', rest, -, hne, h₁, h₂, hs'⟩ :=
    inv_ctxtInstrs Tb.rules.ctxtInstrs hf
  have el : l = vs ++ is ++ rest := (cfgV_inj h₁).2
  have ej : js = vs ++ is' ++ rest := (cfgV_inj h₂).2
  obtain ⟨-, hvs, el', ej'⟩ := ctxt_split hlast hjs hne el ej
  have hvl : 0 < vs.length := List.length_pos_iff.2 hvs
  cases is with
  | nil =>
    refine not_sstep Tb 1 [] (by simp) (fun A M' C h => ?_) z₁ _ hs'
    have hM : M' = [] := (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1).2
    exact hM ▸ inert_nil Tb
  | cons x xs =>
    show False
    have hlast' : (x :: xs).getLast? = some (.case t w₀) := by
      rw [← getLast?_append_of_ne (l := vs) (List.cons_ne_nil _ _), ← el']
      exact hlast
    have hjM' : is'.length < M := by
      have hlen : js.length = vs.length + is'.length := by rw [ej', List.length_append]
      omega
    have hjs' : ∀ w, Value.case t w ∉ is' := fun w hw => hjs w (by rw [ej']; simp [hw])
    exact no_sstep_short Tb hR hp hrd hok _ (x :: xs) (Nat.lt_succ_self _)
      (tagsIn_infix (A := vs) (C := []) hl (by rw [el', List.append_nil])) hlast' z₁ z₁' is'
      hjM' hjs' hs'

/-- **Inversion at a redex of unbounded arity**: at every evaluator with the wasm-3.0 tables, a
`Step` fact from code with constructors in `t :: valTags` ending in `t`, to a code without `t`
of length at most `M`, is a rule of `Step` from rule 6 on fired at the whole code, when no
`Step_pure`, `Step_read` or context rule names only constructors of `t :: valTags` and every
other such rule forces a right-hand side of length at least `M`. -/
theorem sstep_head_tail (Tb : Tables env) (hR : (relRules env "Step").map rhsLen = stepRhsT)
    {t : MixopS} {M : Nat} (hp : chkTags t pureInfoT = true) (hrd : chkTags t readInfoT = true)
    (hctx : chkTags t (stepRestT.take 3) = true) (hok : rhsOk t M = true) {l : List Value}
    (hl : TagsIn (t :: valTags) l) {w₀ : Value} (hlast : l.getLast? = some (.case t w₀))
    {z z' : Value} {js : List Value} (hjM : js.length ≤ M) (hjs : ∀ w, Value.case t w ∉ js)
    (hs : SStep env (cfgV z l) (cfgV z' js)) :
    ∃ i, 6 ≤ i ∧ Fires env "Step" i (.tuple [cfgV z l, cfgV z' js]) := by
  obtain ⟨tt, rules, hrel⟩ := Tb.step
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  have hctx3 : ∀ i, 3 ≤ i → i < 6 → ¬ Fires env "Step" i (.tuple [cfgV z l, cfgV z' js]) :=
    fun i hi3 hi6 => not_fires_of_row Tb.stepT fun row hrow =>
      ⟨_, _, .inr ⟨z, l, rfl, hl, rfl⟩, .inl (outside_spec (List.all_eq_true.1 hctx row (by
        apply List.mem_of_getElem? (i := i - 3)
        rw [List.getElem?_take_of_lt (by omega), stepRestT, List.getElem?_drop,
          Nat.add_sub_cancel' hi3]
        exact hrow)))⟩
  match i, hf with
  | 0, hf => exact absurd hf (not_pure_tags Tb hp hl)
  | 1, hf => exact absurd hf (not_read_tags Tb hrd hl)
  | 2, hf => exact (not_ctxt_tail Tb hR hp hrd hok hl hlast hjM hjs hf).elim
  | 3, hf => exact absurd hf (hctx3 3 (by omega) (by omega))
  | 4, hf => exact absurd hf (hctx3 4 (by omega) (by omega))
  | 5, hf => exact absurd hf (hctx3 5 (by omega) (by omega))
  | k + 6, hf => exact ⟨k + 6, by omega, hf⟩

end Silmaril.Wasm.SpecTec.Institution.FwdB30D
