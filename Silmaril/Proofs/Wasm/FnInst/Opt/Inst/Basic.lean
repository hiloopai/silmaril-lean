module

public import Silmaril.Wasm.FnInst.Opt.Inst.Defs

@[expose] public section

/-! # The segment institution: peephole transfer, monotonicity, distinction

* `run_restrict`: code typed over `ft` does not look at functions past `ft`;
* `runEq_plug`, `runLe_plug`: equal (included) runs at a hole stay equal (included) in every
  typed context (congruence of plugging, per environment);
* `holds_plug_equiv`, `holds_plug_refine`, and the reflections `distSome_of_plug`,
  `distEvery_of_plug`: the same over a partial model, through completions;
* `sat_plug_equiv`, `sat_plug_refine`: the *peephole-rewrite theorem* as an entailment of the
  institution: `(τ, s ≈ s') ⊨ (𝟙, plug τ s ≈ plug τ s')`;
* `holds_mono`, `holds_distSome_anti`: monotonicity in information;
* `distSome_iff_not_equiv`, `distSome_of_distEvery`: how the two distinctions relate;
* `segEquiv_of_holds_top`, `peephole_module`: a rule valid at the minimal hole and the least
  informative model is valid in every body of every well-typed module whose function types
  extend the hole's.
-/

namespace Silmaril.Proofs.Wasm.FnInst.Opt

open Silmaril.Wasm.FnInst.Opt

open CategoryTheory

/-! ## Functions out of sight -/

theorem step_restrict {ft : FTypes} (E : Env) {i : Instr} {a : ℕ × ℕ}
    (ha : arity ft i = some a) (st : St) :
    step ft (E.restrict ft.length) i st = step ft E i st := by
  cases i with
  | call f =>
    have hf : ft[f]? = some a := ha
    have hlt : f < ft.length := (List.getElem?_eq_some_iff.mp hf).1
    have hE : E.restrict ft.length f = E f := by
      unfold Env.restrict
      rw [ite_eq_left hlt]
    simp only [step, callOut, hE]
  | _ => rfl

theorem run_restrict {ft : FTypes} (E : Env) {c : Code} {h h' : ℕ}
    (hc : chk ft c h = some h') (st : St) :
    run ft (E.restrict ft.length) c st = run ft E c st := by
  induction c generalizing h st with
  | nil => rfl
  | cons i c ih =>
    simp only [chk_cons] at hc
    simp only [run_cons]
    cases hi : hgt ft i h with
    | none => rw [hi] at hc; cases hc
    | some h₂ =>
      rw [hi] at hc
      obtain ⟨p, q, ha, -, -⟩ := hgt_spec.mp hi
      rw [step_restrict E ha st]
      exact Out.bind_congr fun st' _ => ih hc st'

theorem Env.restrict_completion {ft : FTypes} {E M : Env} (hE : E.Completion ft M) :
    (E.restrict ft.length).Completion ft (M.restrict ft.length) := by
  obtain ⟨hle, hty, htot⟩ := hE
  refine ⟨fun f args g => ?_, fun f n m hf => ?_, fun f args g => ?_⟩
  · unfold Env.restrict
    by_cases hf : f < ft.length
    · rw [ite_eq_left hf, ite_eq_left hf]
      exact hle f args g
    · rw [ite_eq_right hf, ite_eq_right hf]
  · have hlt : f < ft.length := (List.getElem?_eq_some_iff.mp hf).1
    have hr : E.restrict ft.length f = E f := by
      unfold Env.restrict
      rw [ite_eq_left hlt]
    rw [hr]
    exact hty f n m hf
  · unfold Env.restrict
    by_cases hf : f < ft.length
    · rw [ite_eq_left hf]
      exact htot f args g
    · rw [ite_eq_right hf]
      exact Env.top_total f args g

/-! ## Plugging, per environment -/

/-- The states reached by a context's `pre` code have the hole's operands on top. -/
theorem pre_height {X Y : HSig} (σ : X ⟶ Y) {E : Env} (hE : E.Typed Y.ft) {st st₁ : St}
    (hst : Y.n ≤ st.stack.length) (h₁ : Out.ok st₁ ∈ run Y.ft E σ.pre st) :
    X.n ≤ st₁.stack.length := by
  have hc : chk Y.ft σ.pre st.stack.length =
      some (st.stack.length - Y.n + (X.n + σ.j)) := chk_shift σ.pre_ty hst
  have hl : st₁.stack.length = st.stack.length - Y.n + (X.n + σ.j) := run_height hE hc rfl h₁
  omega

theorem run_plugC {X Y : HSig} (σ : X ⟶ Y) (E : Env) (c : Code) (st : St) :
    run Y.ft E (plugC σ c) st =
      Out.bind (Out.bind (run Y.ft E σ.pre st) (run Y.ft E c)) (run Y.ft E σ.post) := by
  unfold plugC
  rw [run_append, run_append]

theorem runEq_plug {X Y : HSig} (σ : X ⟶ Y) {E : Env} (hE : E.Typed Y.ft) (s s' : Seg X)
    (h : RunEq X.ft X.n E s.1 s'.1) : RunEq Y.ft Y.n E (plug σ s).1 (plug σ s').1 := by
  intro st hst
  have hmid : Out.bind (run Y.ft E σ.pre st) (run Y.ft E s.1) =
      Out.bind (run Y.ft E σ.pre st) (run Y.ft E s'.1) := by
    refine Out.bind_congr fun st₁ h₁ => ?_
    rw [← run_ft σ.ft_le E s.2, ← run_ft σ.ft_le E s'.2]
    exact h st₁ (pre_height σ hE hst h₁)
  show run Y.ft E (plugC σ s.1) st = run Y.ft E (plugC σ s'.1) st
  rw [run_plugC, run_plugC, hmid]

theorem runLe_plug {X Y : HSig} (σ : X ⟶ Y) {E : Env} (hE : E.Typed Y.ft) (s s' : Seg X)
    (h : RunLe X.ft X.n E s.1 s'.1) : RunLe Y.ft Y.n E (plug σ s).1 (plug σ s').1 := by
  intro st hst
  have hmid : Out.bind (run Y.ft E σ.pre st) (run Y.ft E s.1) ⊆
      Out.bind (run Y.ft E σ.pre st) (run Y.ft E s'.1) := by
    refine Out.bind_mono fun st₁ h₁ => ?_
    rw [← run_ft σ.ft_le E s.2, ← run_ft σ.ft_le E s'.2]
    exact h st₁ (pre_height σ hE hst h₁)
  show run Y.ft E (plugC σ s.1) st ⊆ run Y.ft E (plugC σ s'.1) st
  rw [run_plugC, run_plugC]
  exact Out.bind_mono_left hmid _

/-- A completion at `Y` restricts to a completion at `X`, with the same runs of `X`'s code. -/
theorem runEq_of_restrict {X : HSig} {E : Env} (s s' : Seg X)
    (h : RunEq X.ft X.n (E.restrict X.ft.length) s.1 s'.1) : RunEq X.ft X.n E s.1 s'.1 := by
  intro st hst
  rw [← run_restrict E s.2, ← run_restrict E s'.2]
  exact h st hst

theorem runLe_of_restrict {X : HSig} {E : Env} (s s' : Seg X)
    (h : RunLe X.ft X.n (E.restrict X.ft.length) s.1 s'.1) : RunLe X.ft X.n E s.1 s'.1 := by
  intro st hst
  rw [← run_restrict E s.2, ← run_restrict E s'.2]
  exact h st hst

theorem Env.completion_of_prefix {ft ft' : FTypes} (hp : ft <+: ft') {E M : Env}
    (hE : E.Completion ft' M) : E.Completion ft M :=
  ⟨hE.1, Env.typed_of_prefix hp hE.2.1, hE.2.2⟩

/-! ## Over partial models -/

theorem holds_plug_equiv {X Y : HSig} (σ : X ⟶ Y) {M : Env} {s s' : Seg X}
    (h : holds X M (.equiv s s')) : holds Y M (.equiv (plug σ s) (plug σ s')) :=
  fun E hE => runEq_plug σ hE.2.1 s s' (h E (Env.completion_of_prefix σ.ft_le hE))

theorem holds_plug_refine {X Y : HSig} (σ : X ⟶ Y) {M : Env} {s s' : Seg X}
    (h : holds X M (.refine s s')) : holds Y M (.refine (plug σ s) (plug σ s')) :=
  fun E hE => runLe_plug σ hE.2.1 s s' (h E (Env.completion_of_prefix σ.ft_le hE))

/-- A difference of plugged code in some completion is a difference of the segments there. -/
theorem distSome_of_plug {X Y : HSig} (σ : X ⟶ Y) {M : Env} {s s' : Seg X}
    (h : holds Y M (.distSome (plug σ s) (plug σ s'))) : holds X M (.distSome s s') := by
  obtain ⟨E, hE, hne⟩ := h
  exact ⟨E, Env.completion_of_prefix σ.ft_le hE, fun heq => hne (runEq_plug σ hE.2.1 s s' heq)⟩

theorem distEvery_of_plug {X Y : HSig} (σ : X ⟶ Y) {M : Env} {s s' : Seg X}
    (h : holds Y M (.distEvery (plug σ s) (plug σ s'))) (hX : ∀ E : Env, E.Completion X.ft M →
      E.Completion Y.ft M) : holds X M (.distEvery s s') :=
  fun E hE heq => h E (hX E hE) (runEq_plug σ (hX E hE).2.1 s s' heq)

/-! ## The peephole-rewrite theorem, in the institution -/

theorem Model.reduct_val {X Y : HSig} (σ : X ⟶ Y) (M : Model Y) :
    (Model.reduct σ M).1 = M.1.restrict X.ft.length := rfl

/-- Equivalence at the reduct gives equivalence over the model itself. -/
theorem holds_equiv_of_reduct {X Y : HSig} (τ : X ⟶ Y) (M : Model Y) {s s' : Seg X}
    (h : holds X (Model.reduct τ M).1 (.equiv s s')) : holds X M.1 (.equiv s s') := by
  intro E hE
  refine runEq_of_restrict s s' ?_
  exact h _ (Env.restrict_completion hE)

theorem holds_refine_of_reduct {X Y : HSig} (τ : X ⟶ Y) (M : Model Y) {s s' : Seg X}
    (h : holds X (Model.reduct τ M).1 (.refine s s')) : holds X M.1 (.refine s s') := by
  intro E hE
  refine runLe_of_restrict s s' ?_
  exact h _ (Env.restrict_completion hE)

theorem sat_equiv_iff {Y : HSig} (M : Model Y) (s s' : Seg Y) :
    Sat M (Sen.equiv s s') ↔ holds Y M.1 (.equiv s s') := by
  show holds Y (Model.reduct (𝟙 Y) M).1 _ ↔ _
  rw [Model.reduct_id]

/-- **The peephole-rewrite theorem** (institution form): a segment equivalence scoped at a
hole `X` placed in `Y` by `τ` entails the equivalence of the plugged code at `Y`. -/
theorem sat_plug_equiv {X Y : HSig} (τ : X ⟶ Y) (M : Model Y) {s s' : Seg X}
    (h : Sat M (Sen.scoped τ (.equiv s s'))) : Sat M (Sen.equiv (plug τ s) (plug τ s')) :=
  (sat_equiv_iff M _ _).2 (holds_plug_equiv τ (holds_equiv_of_reduct τ M h))

/-- The peephole-rewrite theorem for refinement. -/
theorem sat_plug_refine {X Y : HSig} (τ : X ⟶ Y) (M : Model Y) {s s' : Seg X}
    (h : Sat M (Sen.scoped τ (.refine s s'))) :
    Sat M (⟨Y, 𝟙 Y, .refine (plug τ s) (plug τ s')⟩ : Sen Y) := by
  show holds Y (Model.reduct (𝟙 Y) M).1 _
  rw [Model.reduct_id]
  exact holds_plug_refine τ (holds_refine_of_reduct τ M h)

/-! ## Information -/

/-- **Monotonicity.** Positive formulas (equivalence, refinement, distinction in every
completion, conjunctions of them) valid with less information stay valid with more. -/
theorem holds_mono {X : HSig} {M M' : Env} (hle : M' ≤ M) :
    ∀ {φ : Form X}, φ.Positive → holds X M φ → holds X M' φ
  | .equiv _ _, _, h => fun E hE => h E ⟨Env.le_trans hE.1 hle, hE.2⟩
  | .refine _ _, _, h => fun E hE => h E ⟨Env.le_trans hE.1 hle, hE.2⟩
  | .distEvery _ _, _, h => fun E hE => h E ⟨Env.le_trans hE.1 hle, hE.2⟩
  | .distSome _ _, hp, _ => hp.elim
  | .and _ _, hp, h => ⟨holds_mono hle hp.1 h.1, holds_mono hle hp.2 h.2⟩

/-- Distinction in some completion goes the other way: valid with more information, it stays
valid with less. -/
theorem holds_distSome_anti {X : HSig} {M M' : Env} (hle : M ≤ M') {s s' : Seg X}
    (h : holds X M (.distSome s s')) : holds X M' (.distSome s s') := by
  obtain ⟨E, hE, hne⟩ := h
  exact ⟨E, ⟨Env.le_trans hE.1 hle, hE.2⟩, hne⟩

theorem distSome_iff_not_equiv {X : HSig} {M : Env} {s s' : Seg X} :
    holds X M (.distSome s s') ↔ ¬ holds X M (.equiv s s') := by
  constructor
  · rintro ⟨E, hE, hne⟩ h
    exact hne (h E hE)
  · intro h
    by_contra hn
    exact h fun E hE => by_contra fun hne => hn ⟨E, hE, hne⟩

/-- Distinction in every completion implies distinction in some completion, when the model
has a completion at all (a model without completions makes every formula of the `∀` kind
hold vacuously). -/
theorem distSome_of_distEvery {X : HSig} {M : Env} {s s' : Seg X}
    (hc : ∃ E : Env, E.Completion X.ft M) (h : holds X M (.distEvery s s')) :
    holds X M (.distSome s s') := by
  obtain ⟨E, hE⟩ := hc
  exact ⟨E, hE, h E hE⟩

theorem Env.trapAll_completion (ft : FTypes) : Env.trapAll.Completion ft Env.top := by
  refine ⟨Env.le_top _, ?_, ?_⟩
  · intro f n m hf args g r g' hr
    cases Set.mem_singleton_iff.mp hr
  · intro f args g
    exact ⟨Ans.trap, Set.mem_singleton _⟩

/-! ## Refinement and equivalence -/

theorem holds_refine_of_equiv {X : HSig} {M : Env} {s s' : Seg X}
    (h : holds X M (.equiv s s')) : holds X M (.refine s s') :=
  fun E hE st hst => (h E hE st hst).le

/-- Equivalence is refinement both ways. -/
theorem holds_equiv_iff_refine {X : HSig} {M : Env} {s s' : Seg X} :
    holds X M (.equiv s s') ↔ holds X M (.refine s s') ∧ holds X M (.refine s' s) := by
  constructor
  · intro h
    exact ⟨holds_refine_of_equiv h, fun E hE st hst => (h E hE st hst).ge⟩
  · rintro ⟨h₁, h₂⟩ E hE st hst
    exact (h₁ E hE st hst).antisymm (h₂ E hE st hst)

/-! ## Every function of every module -/

/-- A rule valid at its minimal hole, over the least informative model, is valid over every
extension of the hole's function types. -/
theorem segEquiv_of_holds_top {X : HSig} {s s' : Seg X} (h : holds X Env.top (.equiv s s'))
    {ft : FTypes} (hp : X.ft <+: ft) : SegEquiv ft X.n Env.top s.1 s'.1 := by
  intro E hE st hst
  have hE' : (E.restrict X.ft.length).Completion X.ft Env.top := by
    have hr := Env.restrict_completion (Env.completion_of_prefix hp hE)
    refine ⟨fun f args g => Env.le_top _ f args g, hr.2⟩
  have heq := h _ hE' st hst
  rw [run_restrict E s.2, run_restrict E s'.2, run_ft hp E s.2, run_ft hp E s'.2] at heq
  exact heq

/-- **The peephole-rewrite theorem** (module form): a segment pair equivalent at its minimal
hole `X` over the least informative model can be exchanged at typed positions in any bodies of
any well-typed module whose function types extend `X`'s, and every function of the module
keeps its semantics at every call depth. -/
theorem peephole_module {X : HSig} {s s' : Seg X} (h : holds X Env.top (.equiv s s'))
    {M M' : Mdl} (hp : X.ft <+: M.ft) (hM : M.Typed) {imp : Env} (himp : imp.Typed M.ft)
    (himp' : imp.Total) (hR : Mdl.Rewrites s.1 s'.1 X.n X.m M M') :
    ∀ k, fsem M imp k = fsem M' imp k :=
  fsem_rewrite (segEquiv_of_holds_top h hp) (chk_ft hp s.2) hM himp himp' hR

end Silmaril.Proofs.Wasm.FnInst.Opt
