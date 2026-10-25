module

public import Silmaril.Logic.Metamath.Model.Basic
public import Silmaril.Logic.Metamath.Grammar.Correspondence

@[expose] public section

/-!
# Soundness of models

Every tree theorem of `Γ` holds in every model of `Γ` (`Model.sound`); this is
Carneiro, *Models for Metamath* (2016), Theorem 1, for tree formal systems.

A derivation step applies an axiom `B` under a substitution `τ`. The values
of the substituted trees form a valuation of `B`'s variables
(`Model.substVal`), and evaluating a substituted tree is evaluating the tree
under that valuation (`Grammar.eval_subst`). The disjoint-variable conditions
of `B` hold for it by compositionality of freshness, so the axiom applies.

A proof may use dummy variables. Any valuation of the assertion extends to
the dummies with values that are pairwise fresh and fresh for the values of
the assertion's variables (`Model.exists_extend_valuation`), chosen one at a
time with the freshness clause of the model. This satisfies every
disjoint-variable condition of the extended frame.

For an unambiguous grammar the string theorems of the flattened system are
the tree theorems (`Grammar.tderivable_iff_derivable`), so they also hold in
every model (`Model.sound_derivable`). A string assertion holds in a model
when every well-formed tree assertion flattening to it does
(`Model.SatisfiesStr`), and every string theorem holds (`Model.sound_str`).
-/

namespace Silmaril.Logic.Metamath

open Grammar

universe u w

variable {C V L : Type u} {G : Grammar L C V}

namespace Grammar.TAssertion

theorem mem_allVars_of_concl {A : TAssertion L C V} {v : V} (h : v ∈ A.concl.tree.vars) :
    v ∈ A.allVars :=
  List.mem_append_left _ h

theorem mem_allVars_of_essential {A : TAssertion L C V} {e : TExpr L C V}
    (he : e ∈ A.essentials) {v : V} (h : v ∈ e.tree.vars) : v ∈ A.allVars := by
  simp only [allVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨_, mem_essentials.1 he, h⟩

/-- In the extended frame, the variables of the assertion keep their sorts. -/
theorem ctx_extend_of_mem_allVars {A : TAssertion L C V} {D : TDummies A} {v : V}
    (hv : v ∈ A.allVars) {s : C} (h : (A.extend D).ctx v s) : A.ctx v s :=
  (ctx_extend.1 h).resolve_right fun hd => D.fresh _ hd hv

end Grammar.TAssertion

namespace Model

variable (M : Model.{u, w} G)

section Step

variable {ctx ctx' : V → C → Prop} {τ : V → Tree L V}

/-- The values of the substituted trees, as a valuation of the variables of
the substitution's source context. -/
def substVal (ρ : M.Valuation ctx') (hτ : ∀ v s, ctx v s → G.HasSort ctx' (τ v) s) :
    M.Valuation ctx :=
  fun v s h => M.value ρ (τ v) ((hτ v s h.1).synCtx h.2)

theorem synCtx_subst (hτ : ∀ v s, ctx v s → G.HasSort ctx' (τ v) s) (v : V) (s : C)
    (h : G.synCtx ctx v s) : G.HasSort (G.synCtx ctx') (τ v) s :=
  (hτ v s h.1).synCtx h.2

theorem value_subst (ρ : M.Valuation ctx') (hτ : ∀ v s, ctx v s → G.HasSort ctx' (τ v) s)
    (t : Tree L V) {s : C} (h : G.HasSort (G.synCtx ctx) t s)
    (h' : G.HasSort (G.synCtx ctx') (t.subst τ) s) :
    M.value ρ (t.subst τ) h' = M.value (M.substVal ρ hτ) t h :=
  eval_subst (synCtx_subst hτ) t h

/-- A substituted expression holds exactly when the expression holds under the
substituted valuation, for an expression well typed in the source context. -/
theorem holds_subst_iff (ρ : M.Valuation ctx') (hτ : ∀ v s, ctx v s → G.HasSort ctx' (τ v) s)
    {e : TExpr L C V} (he : e.WellTyped G ctx) :
    M.Holds ρ (e.subst τ) ↔ M.Holds (M.substVal ρ hτ) e := by
  obtain ⟨s, hs, ht⟩ := he
  constructor
  · rintro ⟨s', hs', ht', htrue⟩
    obtain rfl : s = s' := Option.some.inj (hs.symm.trans hs')
    have ht₀ := ht.synCtx (G.prov_sort hs)
    exact ⟨s, hs, ht₀, (congrArg (M.IsTrue hs) (M.value_subst ρ hτ _ ht₀ ht')).mp htrue⟩
  · rintro ⟨s', hs', ht', htrue⟩
    exact ⟨s', hs', ht'.subst (synCtx_subst hτ),
      (congrArg (M.IsTrue hs') (M.value_subst ρ hτ _ ht' _)).mpr htrue⟩

theorem holds_subst (ρ : M.Valuation ctx') (hτ : ∀ v s, ctx v s → G.HasSort ctx' (τ v) s)
    {e : TExpr L C V} (h : M.Holds (M.substVal ρ hτ) e) : M.Holds ρ (e.subst τ) := by
  obtain ⟨s', hs', ht', htrue⟩ := h
  exact ⟨s', hs', ht'.subst (synCtx_subst hτ),
    (congrArg (M.IsTrue hs') (M.value_subst ρ hτ _ ht' _)).mpr htrue⟩

end Step

/-- Every expression derived in the frame `F` holds under every valuation of
`F` satisfying its disjoint-variable conditions and essential hypotheses. -/
theorem TDerivation.holds {Γ : Set (TAssertion L C V)}
    (hΓ : ∀ B ∈ Γ, ∀ e ∈ B.essentials, e.WellTyped G B.ctx) (hM : M.IsModel Γ)
    {F : TAssertion L C V} (ρ : M.Valuation F.ctx) (hdv : M.DVHolds ρ F.dv)
    (hess : ∀ e ∈ F.essentials, M.Holds ρ e) {e : TExpr L C V} (d : TDerivation G Γ F e) :
    M.Holds ρ e := by
  induction d with
  | hyp he => exact hess _ he
  | app B hB τ sorted _ dv ih =>
    refine M.holds_subst ρ sorted (hM B hB _ ?_ fun e he => ?_)
    · intro x y hxy hne s t hx hy
      refine M.fresh_eval_eval ρ (τ x) (τ y) _ _ fun a ha b hb sa sb ha' hb' => ?_
      obtain ⟨hab, hd⟩ := dv x y hxy a ha b hb
      rcases hd with hd | hd
      · exact hdv a b hd hab sa sb ha' hb'
      · exact M.fresh_symm (hdv b a hd (Ne.symm hab) sb sa hb' ha')
    · exact (M.holds_subst_iff ρ sorted (hΓ B hB e he)).1 (ih e he)

section Dummies

variable {M}

/-- Values for a list of declarations, fresh for the given values `W` and
pairwise fresh at distinct variables. -/
theorem exists_fresh_values (W : List (Σ t, M.Carrier t)) (ps : List (C × V)) :
    ∃ δ : ∀ v s, (s, v) ∈ ps → s ∈ G.sorts → M.Carrier s,
      (∀ v s h hs, ∀ w ∈ W, M.Fresh (δ v s h hs) w.2) ∧
      ∀ v s h hs v' s' h' hs', v ≠ v' → M.Fresh (δ v s h hs) (δ v' s' h' hs') := by
  classical
  induction ps generalizing W with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, by simp, by simp⟩
  | cons p ps ih =>
    obtain ⟨c, z⟩ := p
    have tail : ∀ {v s}, (s, v) ∈ (c, z) :: ps → ¬ (v = z ∧ s = c) → (s, v) ∈ ps :=
      fun hm hvs => (List.mem_cons.1 hm).resolve_left fun e =>
        hvs ⟨(Prod.mk.inj e).2, (Prod.mk.inj e).1⟩
    by_cases hc : c ∈ G.sorts
    · obtain ⟨a, ha⟩ := M.exists_fresh c hc W
      obtain ⟨δ, h₁, h₂⟩ := ih (⟨c, a⟩ :: W)
      refine ⟨fun v s hm hs =>
        if hvs : v = z ∧ s = c then hvs.2 ▸ a else δ v s (tail hm hvs) hs, ?_, ?_⟩
      · intro v s hm hs w hw
        dsimp only
        split
        · rename_i hvs
          obtain ⟨rfl, rfl⟩ := hvs
          exact ha w hw
        · exact h₁ _ _ _ _ w (List.mem_cons_of_mem _ hw)
      · intro v s hm hs v' s' hm' hs' hne
        dsimp only
        split <;> split
        · rename_i h h'
          exact absurd (h.1.trans h'.1.symm) hne
        · rename_i hvs _
          obtain ⟨rfl, rfl⟩ := hvs
          exact M.fresh_symm (h₁ _ _ _ _ _ List.mem_cons_self)
        · rename_i hvs
          obtain ⟨rfl, rfl⟩ := hvs
          exact h₁ _ _ _ _ _ List.mem_cons_self
        · exact h₂ _ _ _ _ _ _ _ _ hne
    · obtain ⟨δ, h₁, h₂⟩ := ih W
      have tail' : ∀ {v s}, (s, v) ∈ (c, z) :: ps → s ∈ G.sorts → (s, v) ∈ ps :=
        fun hm hs => tail hm fun hvs => hc (hvs.2 ▸ hs)
      exact ⟨fun v s hm hs => δ v s (tail' hm hs) hs, fun _ _ _ _ => h₁ _ _ _ _,
        fun _ _ _ _ _ _ _ _ => h₂ _ _ _ _ _ _ _ _⟩

/-- The values of a valuation, as a list. -/
noncomputable def values {A : TAssertion L C V} (ρ : M.Valuation A.ctx) :
    List (Σ t, M.Carrier t) :=
  have := Classical.propDecidable
  A.floats.attach.filterMap fun p =>
    if hs : p.1.1 ∈ G.sorts then
      some ⟨p.1.1, ρ p.1.2 p.1.1 ⟨TAssertion.mem_floats.1 p.2, hs⟩⟩
    else none

theorem mem_values {A : TAssertion L C V} (ρ : M.Valuation A.ctx) {v : V} {s : C}
    (h : G.synCtx A.ctx v s) : ⟨s, ρ v s h⟩ ∈ values ρ := by
  simp only [values, List.mem_filterMap, List.mem_attach, true_and]
  exact ⟨⟨(s, v), TAssertion.mem_floats.2 h.1⟩, by simp [h.2]⟩

/-- A valuation of an assertion extends to its dummy variables so that every
disjoint-variable condition of the extended frame holds (Carneiro, proof of
Theorem 1). -/
theorem exists_extend_valuation (A : TAssertion L C V) (D : TDummies A) (ρ : M.Valuation A.ctx)
    (hdv : M.DVHolds ρ A.dv) :
    ∃ ρ' : M.Valuation (A.extend D).ctx,
      (∀ v s h h', ρ' v s h' = ρ v s h) ∧ M.DVHolds ρ' (A.extend D).dv := by
  classical
  obtain ⟨δ, h₁, h₂⟩ := exists_fresh_values (values ρ) D.floats
  have dummy : ∀ {v s}, (A.extend D).ctx v s → ¬ A.ctx v s → (s, v) ∈ D.floats :=
    fun h hA => (TAssertion.ctx_extend.1 h).resolve_left hA
  let ρ' : M.Valuation (A.extend D).ctx := fun v s h =>
    if hA : A.ctx v s then ρ v s ⟨hA, h.2⟩ else δ v s (dummy h.1 hA) h.2
  refine ⟨ρ', fun v s h h' => by simp [ρ', h.1], ?_⟩
  intro x y hxy hne s t hx hy
  simp only [ρ']
  split <;> split
  · rename_i hxA hyA
    refine hdv x y ?_ hne s t _ _
    rcases List.mem_append.1 hxy with hxy | hxy
    · exact hxy
    · exfalso
      rcases D.dv_dummy _ hxy with hd | hd <;> obtain ⟨⟨s', _⟩, hp, rfl⟩ := List.mem_map.1 hd
      · exact D.fresh _ hp (TAssertion.mem_allVars_of_ctx hxA)
      · exact D.fresh _ hp (TAssertion.mem_allVars_of_ctx hyA)
  · rename_i hxA _
    exact M.fresh_symm (h₁ _ _ _ _ _ (mem_values ρ ⟨hxA, hx.2⟩))
  · rename_i _ hyA
    exact h₁ _ _ _ _ _ (mem_values ρ ⟨hyA, hy.2⟩)
  · exact h₂ _ _ _ _ _ _ _ _ hne

end Dummies

/-- Soundness (Carneiro, *Models for Metamath*, Theorem 1): every tree
theorem of well-formed axioms holds in every model of the axioms. -/
theorem sound {Γ : Set (TAssertion L C V)} (hΓ : ∀ B ∈ Γ, B.WellFormed G) (hM : M.IsModel Γ)
    {A : TAssertion L C V} (h : TDerivable G Γ A) : M.Satisfies A := by
  obtain ⟨D, ⟨d⟩⟩ := tderivable_iff.1 h
  intro ρ hdv hess
  obtain ⟨ρ', hagree, hdv'⟩ := exists_extend_valuation A D ρ hdv
  have hess' : ∀ e ∈ (A.extend D).essentials, M.Holds ρ' e := by
    intro e he
    rw [TAssertion.essentials_extend] at he
    exact (hess e he).congr (fun _ _ s h => TAssertion.ctx_le_extend D _ s h)
      fun v _ s h₁ h₂ => (hagree v s h₁ h₂).symm
  have hc := TDerivation.holds M (fun B hB e he => (hΓ B hB).ess_wellTyped e he) hM ρ' hdv' hess' d
  exact hc.congr (fun v hv s h => TAssertion.ctx_extend_of_mem_allVars
      (TAssertion.mem_allVars_of_concl hv) h)
    fun v hv s h₁ h₂ => hagree v s h₂ h₁

/-- An assertion false in a model of `Γ` is not a tree theorem of `Γ`. -/
theorem not_tderivable {Γ : Set (TAssertion L C V)} (hΓ : ∀ B ∈ Γ, B.WellFormed G)
    (hM : M.IsModel Γ) {A : TAssertion L C V} (hA : ¬ M.Satisfies A) : ¬ TDerivable G Γ A :=
  fun h => hA (M.sound hΓ hM h)

/-- Tree theorems are true under every valuation of their variables when they
have no hypotheses beyond floating ones and no disjoint-variable conditions. -/
theorem sound_holds {Γ : Set (TAssertion L C V)} (hΓ : ∀ B ∈ Γ, B.WellFormed G)
    (hM : M.IsModel Γ) {A : TAssertion L C V} (h : TDerivable G Γ A) (hdv : A.dv = [])
    (hess : A.essentials = []) (ρ : M.Valuation A.ctx) : M.Holds ρ A.concl :=
  M.sound hΓ hM h ρ (by simp [DVHolds, hdv]) (by simp [hess])

section String

variable [DecidableEq V]

/-- Soundness for string theorems: for an unambiguous grammar, the flattening
of a well-formed tree assertion that is a string theorem of the syntax axioms
and the flattened axioms holds in every model of the axioms. -/
theorem sound_derivable (hG : G.Unambiguous) {Γ : Set (TAssertion L C V)}
    (hΓ : ∀ B ∈ Γ, B.WellFormed G) (hM : M.IsModel Γ) {A : TAssertion L C V}
    (hA : A.WellFormed G) (h : Derivable (G.axioms Γ) (A.flatten G)) : M.Satisfies A :=
  M.sound hΓ hM ((tderivable_iff_derivable hG hΓ hA).2 h)

/-- A string assertion holds in `M` when every well-formed tree assertion
flattening to it is satisfied. -/
def SatisfiesStr (A : Assertion C V) : Prop :=
  ∀ A' : TAssertion L C V, A'.WellFormed G → A'.flatten G = A → M.Satisfies A'

/-- String soundness: for an unambiguous grammar, every string theorem of the
syntax axioms and the flattened well-formed axioms holds in every model of the
axioms. -/
theorem sound_str (hG : G.Unambiguous) {Γ : Set (TAssertion L C V)}
    (hΓ : ∀ B ∈ Γ, B.WellFormed G) (hM : M.IsModel Γ) {A : Assertion C V}
    (h : Derivable (G.axioms Γ) A) : M.SatisfiesStr A := by
  rintro A' hA' rfl
  exact M.sound_derivable hG hΓ hM hA' h

theorem not_derivable (hG : G.Unambiguous) {Γ : Set (TAssertion L C V)}
    (hΓ : ∀ B ∈ Γ, B.WellFormed G) (hM : M.IsModel Γ) {A : TAssertion L C V}
    (hA : A.WellFormed G) (hn : ¬ M.Satisfies A) : ¬ Derivable (G.axioms Γ) (A.flatten G) :=
  fun h => hn (M.sound_derivable hG hΓ hM hA h)

end String

end Model

end Silmaril.Logic.Metamath
