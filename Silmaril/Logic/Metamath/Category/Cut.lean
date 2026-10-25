module

public import Silmaril.Logic.Metamath.Category.Substitution
public import Silmaril.Logic.Metamath.Theory.Cut

@[expose] public section

/-!
# Cut admissibility for tree derivations

The tree analogue of `Silmaril.Logic.Metamath.Theory.Cut`, for an arbitrary
grammar. A derivable tree assertion can be used like an axiom:
`TDerivable.cut` removes from the axiom set any assertion that is derivable
from the rest, and `TDerivable.trans` makes derivability between axiom sets
transitive.

Inlining a proof of `B` at a node that applies `B` under `σ` instantiates the
proof along a substitution that agrees with `σ` off the dummy variables of
that proof and renames the dummies to variables that are fresh for the
surrounding frame and for the trees that `σ` substitutes at disjoint
variables. The renamed dummies become dummies of the surrounding proof,
together with the disjointness conditions they need. Renaming apart requires
an infinite type of variables. The renaming is injective on the dummies, so
each dummy keeps a single floating hypothesis.

Consequences: dummy variables can be chosen to avoid any finite set, and
tree derivability is closed under adding hypotheses and disjointness
conditions.
-/

namespace Silmaril.Logic.Metamath.Grammar

universe u

variable {L C V : Type u}

/-- The variables of the pairs in `l`. -/
private def pairVars (l : List (V × V)) : List V := l.flatMap fun p => [p.1, p.2]

private theorem mem_pairVars_left {l : List (V × V)} {x y : V} (h : (x, y) ∈ l) :
    x ∈ pairVars l := List.mem_flatMap.2 ⟨(x, y), h, by simp⟩

private theorem mem_pairVars_right {l : List (V × V)} {x y : V} (h : (x, y) ∈ l) :
    y ∈ pairVars l := List.mem_flatMap.2 ⟨(x, y), h, by simp⟩

/-- All pairs of variables of the images of the pairs in `l`. -/
private def imagePairs (τ : V → Tree L V) (l : List (V × V)) : List (V × V) :=
  l.flatMap fun p => (τ p.1).vars.flatMap fun a => (τ p.2).vars.map fun b => (a, b)

private theorem mem_imagePairs {τ : V → Tree L V} {l : List (V × V)} {x y a b : V}
    (hxy : (x, y) ∈ l) (ha : a ∈ (τ x).vars) (hb : b ∈ (τ y).vars) :
    (a, b) ∈ imagePairs τ l := by
  simp only [imagePairs, List.mem_flatMap, List.mem_map]
  exact ⟨(x, y), hxy, a, ha, b, hb, rfl⟩

section Inline

variable [DecidableEq V]

/-- The substitution that inlines a proof with dummies `Z` at a node applying
its assertion under `σ`: the renaming `ρ` on the dummies and `σ` elsewhere. -/
private def inlineSubst (Z : List V) (σ : V → Tree L V) (ρ : V → V) (v : V) : Tree L V :=
  if v ∈ Z then .var (ρ v) else σ v

private theorem mem_vars_inlineSubst {Z : List V} {σ : V → Tree L V} {ρ : V → V} {v w : V}
    (h : w ∈ (inlineSubst Z σ ρ v).vars) : (v ∉ Z ∧ w ∈ (σ v).vars) ∨ (v ∈ Z ∧ w = ρ v) := by
  unfold inlineSubst at h
  split_ifs at h with h₁
  · exact Or.inr ⟨h₁, by simpa using h⟩
  · exact Or.inl ⟨h₁, h⟩

/-- The renamed dummies of an inlined proof, with the disjointness conditions
between them and the rest of the frame. -/
private def inlineDummies (F B : TAssertion L C V) (D : TDummies B) (σ : V → Tree L V)
    (ρ : V → V) (hρ : ∀ z ∈ D.vars, ρ z ∉ F.allVars)
    (hinj : ∀ x ∈ D.vars, ∀ y ∈ D.vars, ρ x = ρ y → x = y) : TDummies F where
  floats := D.floats.map fun p => (p.1, ρ p.2)
  dv := (imagePairs (inlineSubst D.vars σ ρ) (B.dv ++ D.dv)).filter
    fun q => q.1 ∈ D.vars.map ρ ∨ q.2 ∈ D.vars.map ρ
  fresh p hp := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hρ q.2 (List.mem_map_of_mem hq)
  nodup := by
    have e : (D.floats.map fun p => (p.1, ρ p.2)).map Prod.snd = D.vars.map ρ := by
      simp [TDummies.vars, Function.comp_def]
    rw [e]
    exact D.nodup.map_on hinj
  dv_dummy p hp := by
    have e : (D.floats.map fun p => (p.1, ρ p.2)).map Prod.snd = D.vars.map ρ := by
      simp [TDummies.vars, Function.comp_def]
    rw [e]
    exact of_decide_eq_true (List.mem_filter.1 hp).2

private theorem inlineDummies_vars (F B : TAssertion L C V) (D : TDummies B) (σ : V → Tree L V)
    (ρ : V → V) (hρ : ∀ z ∈ D.vars, ρ z ∉ F.allVars)
    (hinj : ∀ x ∈ D.vars, ∀ y ∈ D.vars, ρ x = ρ y → x = y) :
    (inlineDummies F B D σ ρ hρ hinj).vars = D.vars.map ρ := by
  simp [inlineDummies, TDummies.vars, List.map_map, Function.comp_def]

end Inline

namespace TDerivation

variable {G : Grammar L C V} {Γ : Set (TAssertion L C V)}

/-- Using a proved tree assertion inside another frame. Given a proof of `B`
with dummies `D`, a substitution `σ` well sorted on the floating variables of
`B` in the frame `F`, derivations in `F` of the instantiated essential
hypotheses, and the disjointness conditions of `B` for distinct variables, the
instance of `B`'s conclusion is derivable in `F` extended by fresh dummies
avoiding `S`. -/
theorem exists_inline [Infinite V] {B F : TAssertion L C V} (D : TDummies B)
    (d : TDerivation G Γ (B.extend D) B.concl) (σ : V → Tree L V)
    (sorted : ∀ v s, B.ctx v s → G.HasSort F.ctx (σ v) s)
    (premises : ∀ e ∈ B.essentials, TDerivation G Γ F (e.subst σ))
    (hσ : ∀ x y, (x, y) ∈ B.dv → x ≠ y →
      ∀ a ∈ (σ x).vars, ∀ b ∈ (σ y).vars, a ≠ b ∧ F.Disjoint a b)
    (S : Finset V) :
    ∃ D' : TDummies F, D'.Avoids S ∧
      Nonempty (TDerivation G Γ (F.extend D') (B.concl.subst σ)) := by
  classical
  obtain ⟨ρ, hinj, hT⟩ := exists_injOn_fresh D.vars
    (S ∪ F.allVars.toFinset ∪ ((pairVars (B.dv ++ D.dv)).flatMap fun y => (σ y).vars).toFinset)
  have hT' : ∀ z ∈ D.vars, ρ z ∉ S ∧ ρ z ∉ F.allVars ∧
      ∀ y ∈ pairVars (B.dv ++ D.dv), ρ z ∉ (σ y).vars := by
    intro z hz
    have h := hT z hz
    refine ⟨fun h' => h (by simp [h']), fun h' => h (by simp [h']), fun y hy h' => h ?_⟩
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap]
    exact Or.inr ⟨y, hy, h'⟩
  let τ := inlineSubst D.vars σ ρ
  let D' := inlineDummies F B D σ ρ (fun z hz => (hT' z hz).2.1) hinj
  have hD' : D'.vars = D.vars.map ρ := inlineDummies_vars F B D σ ρ _ hinj
  have hτB : ∀ v ∈ B.allVars, τ v = σ v := fun v hv => by
    have : v ∉ D.vars := fun h => D.vars_not_mem_allVars h hv
    simp [τ, inlineSubst, this]
  have hτZ : ∀ z ∈ D.vars, τ z = .var (ρ z) := fun z hz => by simp [τ, inlineSubst, hz]
  refine ⟨D', ?_, ?_⟩
  · intro v hv
    rw [hD'] at hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
    exact (hT' z hz).1
  have sorted' : ∀ v s, (B.extend D).ctx v s → G.HasSort (F.extend D').ctx (τ v) s := by
    intro v s hv
    rcases TAssertion.ctx_extend.1 hv with hv | hv
    · rw [hτB v (TAssertion.mem_allVars_of_ctx hv)]
      exact (sorted v s hv).mono (TAssertion.ctx_le_extend D')
    · rw [hτZ v (List.mem_map_of_mem (f := Prod.snd) hv)]
      exact .var (TAssertion.ctx_extend.2
        (Or.inr (List.mem_map_of_mem (f := fun p : C × V => (p.1, ρ p.2)) hv)))
  have hyps : ∀ e ∈ (B.extend D).essentials, TDerivation G Γ (F.extend D') (e.subst τ) := by
    intro e he
    rw [TAssertion.essentials_extend] at he
    refine ((premises e he).extend D').cast (TExpr.subst_congr fun v hv => ?_)
    exact (hτB v (TAssertion.mem_allVars_of_mem_essentials he hv)).symm
  have key : ∀ x y, (x, y) ∈ B.dv ++ D.dv → x ≠ y →
      ∀ a ∈ (τ x).vars, ∀ b ∈ (τ y).vars, a ≠ b ∧ (F.extend D').Disjoint a b := by
    intro x y hxy hne a ha b hb
    have hpair : (a, b) ∈ imagePairs τ (B.dv ++ D.dv) := mem_imagePairs hxy ha hb
    have hdisj : a ∈ D.vars.map ρ ∨ b ∈ D.vars.map ρ → (F.extend D').Disjoint a b := fun h =>
      Or.inl (List.mem_append_right _ (List.mem_filter.2 ⟨hpair, by simpa using h⟩))
    rcases mem_vars_inlineSubst ha with ⟨hx, ha'⟩ | ⟨hxZ, rfl⟩ <;>
      rcases mem_vars_inlineSubst hb with ⟨hy, hb'⟩ | ⟨hyZ, rfl⟩
    · have hB : (x, y) ∈ B.dv := by
        rcases List.mem_append.1 hxy with h | h
        · exact h
        · exfalso
          rcases D.dv_dummy _ h with h' | h'
          · exact hx h'
          · exact hy h'
      obtain ⟨h₁, h₂⟩ := hσ x y hB hne a ha' b hb'
      exact ⟨h₁, TAssertion.Disjoint.mono (F.dv_subset_extend D') h₂⟩
    · refine ⟨?_, hdisj (Or.inr (List.mem_map_of_mem hyZ))⟩
      rintro rfl
      exact (hT' y hyZ).2.2 x (mem_pairVars_left hxy) ha'
    · refine ⟨?_, hdisj (Or.inl (List.mem_map_of_mem hxZ))⟩
      intro h
      exact (hT' x hxZ).2.2 y (mem_pairVars_right hxy) (h ▸ hb')
    · exact ⟨fun h => hne (hinj x hxZ y hyZ h), hdisj (Or.inl (List.mem_map_of_mem hxZ))⟩
  have dv : DVPreserving τ (B.extend D).Disjoint (F.extend D').Disjoint := by
    intro a b hab hd a' ha' b' hb'
    rcases hd with h | h
    · exact key a b h hab a' ha' b' hb'
    · obtain ⟨h₁, h₂⟩ := key b a h (Ne.symm hab) b' hb' a' ha'
      exact ⟨Ne.symm h₁, h₂.symm⟩
  refine ⟨(d.subst τ sorted' hyps dv).cast (TExpr.subst_congr fun v hv => ?_)⟩
  exact hτB v (TAssertion.mem_allVars_of_mem_concl hv)

/-- Derivations of a list of goals in one frame combine into a single frame
extension. -/
private theorem exists_dummies_forall {F : TAssertion L C V}
    (g : TExpr L C V → TExpr L C V) (l : List (TExpr L C V))
    (h : ∀ e ∈ l, ∀ S : Finset V, ∃ D : TDummies F, D.Avoids S ∧
      Nonempty (TDerivation G Γ (F.extend D) (g e))) (S : Finset V) :
    ∃ D : TDummies F, D.Avoids S ∧ ∀ e ∈ l, Nonempty (TDerivation G Γ (F.extend D) (g e)) := by
  classical
  induction l generalizing S with
  | nil => exact ⟨TDummies.none F, TDummies.none_avoids S, by simp⟩
  | cons e l ih =>
    obtain ⟨D₁, hS₁, ⟨d₁⟩⟩ := h e (List.mem_cons_self ..) S
    obtain ⟨D₂, hS₂, hd₂⟩ :=
      ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')) (S ∪ D₁.vars.toFinset)
    have hD : ∀ v ∈ D₁.vars, v ∉ D₂.vars := fun v hv hv₂ => hS₂ v hv₂ (by simp [hv])
    refine ⟨D₁.union D₂ hD, hS₁.union (hS₂.mono Finset.subset_union_left) hD, ?_⟩
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨d₁.weaken (TAssertion.ctx_union_left D₁ D₂ hD)
        (by simp only [TAssertion.essentials_extend]; exact fun _ h => h)
        (F.dv_subset_union_left D₁ D₂ hD)⟩
    · obtain ⟨d₂⟩ := hd₂ e' he'
      exact ⟨d₂.weaken (TAssertion.ctx_union_right D₁ D₂ hD)
        (by simp only [TAssertion.essentials_extend]; exact fun _ h => h)
        (F.dv_subset_union_right D₁ D₂ hD)⟩

/-- Lemma elimination for tree derivations: every application of an assertion
of `Δ` is replaced by an inlined proof of it from `Γ`. The new dummies avoid
`S`. -/
theorem exists_cut [Infinite V] {Δ : Set (TAssertion L C V)}
    (hΔ : ∀ B ∈ Δ, TDerivable G Γ B)
    {F : TAssertion L C V} {e : TExpr L C V} (d : TDerivation G (Γ ∪ Δ) F e) (S : Finset V) :
    ∃ D : TDummies F, D.Avoids S ∧ Nonempty (TDerivation G Γ (F.extend D) e) := by
  classical
  induction d generalizing S with
  | hyp he =>
    exact ⟨TDummies.none F, TDummies.none_avoids S, ⟨(TDerivation.hyp he).extend _⟩⟩
  | app B hB σ hs premises hσ ih =>
    obtain ⟨D₀, hS₀, hprem⟩ :=
      exists_dummies_forall (TExpr.subst σ) B.essentials (fun e he => ih e he) S
    have prem : ∀ e ∈ B.essentials, TDerivation G Γ (F.extend D₀) (e.subst σ) :=
      fun e he => (hprem e he).some
    have hs₀ : ∀ v s, B.ctx v s → G.HasSort (F.extend D₀).ctx (σ v) s :=
      fun v s h => (hs v s h).mono (TAssertion.ctx_le_extend D₀)
    have hσ₀ : B.DVSafe σ (F.extend D₀).Disjoint := fun x y hxy a ha b hb =>
      (hσ x y hxy a ha b hb).imp_right (TAssertion.Disjoint.mono (F.dv_subset_extend D₀))
    by_cases hBΓ : B ∈ Γ
    · exact ⟨D₀, hS₀, ⟨TDerivation.app B hBΓ σ hs₀ prem hσ₀⟩⟩
    · have hBΔ : B ∈ Δ := ((Set.mem_union _ _ _).1 hB).resolve_left hBΓ
      obtain ⟨⟨DB, dB⟩⟩ := hΔ B hBΔ
      obtain ⟨D₁, hS₁, ⟨d₁⟩⟩ :=
        exists_inline DB dB σ hs₀ prem (fun x y hxy _ => hσ₀ x y hxy) S
      exact ⟨D₀.append D₁, hS₀.append hS₁, ⟨(F.extend_append D₀ D₁) ▸ d₁⟩⟩

end TDerivation

variable {G : Grammar L C V} {Γ Δ : Set (TAssertion L C V)} {A B : TAssertion L C V}

/-- Cut admissibility: tree assertions derivable from `Γ` may be added to `Γ`
without deriving anything new. -/
theorem TDerivable.cut [Infinite V] (hΔ : ∀ B ∈ Δ, TDerivable G Γ B)
    (hA : TDerivable G (Γ ∪ Δ) A) : TDerivable G Γ A := by
  obtain ⟨⟨D, d⟩⟩ := hA
  obtain ⟨D', -, ⟨d'⟩⟩ := TDerivation.exists_cut hΔ d ∅
  exact ⟨⟨D.append D', (A.extend_append D D') ▸ d'⟩⟩

/-- Tree derivability is transitive between axiom sets. -/
theorem TDerivable.trans [Infinite V] (hΔ : ∀ B ∈ Δ, TDerivable G Γ B)
    (hA : TDerivable G Δ A) : TDerivable G Γ A :=
  TDerivable.cut hΔ (hA.mono Set.subset_union_right)

/-- A single derivable lemma can be eliminated. -/
theorem TDerivable.cut_insert [Infinite V] (hB : TDerivable G Γ B)
    (hA : TDerivable G (insert B Γ) A) : TDerivable G Γ A := by
  refine TDerivable.cut (Δ := {B}) (by simpa using hB) ?_
  rwa [Set.union_singleton]

/-- A tree theorem may be applied inside another frame, adding fresh dummy
variables that avoid `S`. -/
theorem TDerivable.exists_apply [Infinite V] (hB : TDerivable G Γ B) {F : TAssertion L C V}
    (σ : V → Tree L V) (sorted : ∀ v s, B.ctx v s → G.HasSort F.ctx (σ v) s)
    (premises : ∀ e ∈ B.essentials, TDerivation G Γ F (e.subst σ))
    (hσ : B.DVSafe σ F.Disjoint) (S : Finset V) :
    ∃ D : TDummies F, D.Avoids S ∧
      Nonempty (TDerivation G Γ (F.extend D) (B.concl.subst σ)) := by
  obtain ⟨⟨D, d⟩⟩ := hB
  exact TDerivation.exists_inline D d σ sorted premises (fun x y hxy _ => hσ x y hxy) S

/-- An instance of a tree theorem is a tree theorem. -/
theorem TDerivable.of_instance [Infinite V] (hB : TDerivable G Γ B) (σ : V → Tree L V)
    (sorted : ∀ v s, B.ctx v s → G.HasSort A.ctx (σ v) s)
    (premises : ∀ e ∈ B.essentials, Nonempty (TDerivation G Γ A (e.subst σ)))
    (hσ : B.DVSafe σ A.Disjoint) (hA : A.concl = B.concl.subst σ) : TDerivable G Γ A := by
  obtain ⟨D, -, ⟨d⟩⟩ := hB.exists_apply σ sorted (fun e he => (premises e he).some) hσ ∅
  exact ⟨⟨D, d.cast hA.symm⟩⟩

/-- The dummy variables of a tree proof can be chosen to avoid any finite set. -/
theorem TDerivable.exists_avoiding [Infinite V] (h : TDerivable G Γ A) (S : Finset V) :
    ∃ D : TDummies A, D.Avoids S ∧ Nonempty (TDerivation G Γ (A.extend D) A.concl) := by
  obtain ⟨⟨D, d⟩⟩ := h
  obtain ⟨D', hS, ⟨d'⟩⟩ := TDerivation.exists_inline D d Tree.var (fun _ _ h => .var h)
    (fun e he => TDerivation.hyp (by simpa using he))
    (fun x y hxy hne a ha b hb => by
      simp only [Tree.vars_var, List.mem_singleton] at ha hb
      subst a b
      exact ⟨hne, Or.inl hxy⟩) S
  exact ⟨D', hS, ⟨d'.cast (TExpr.subst_var _)⟩⟩

/-- Weakening: tree derivability is closed under adding hypotheses and
disjointness conditions. -/
theorem TDerivable.weaken [Infinite V] {A' : TAssertion L C V} (h : TDerivable G Γ A)
    (hh : A.hyps ⊆ A'.hyps) (hd : A.dv ⊆ A'.dv) (hc : A'.concl = A.concl) :
    TDerivable G Γ A' := by
  classical
  obtain ⟨D, hS, ⟨d⟩⟩ := h.exists_avoiding A'.allVars.toFinset
  let D' : TDummies A' := D.transfer fun v hv h' => hS v hv (List.mem_toFinset.2 h')
  refine ⟨⟨D', (d.weaken ?_ ?_ ?_).cast hc.symm⟩⟩
  · intro v s hv
    rcases TAssertion.ctx_extend.1 hv with hv | hv
    · exact TAssertion.ctx_extend.2 (Or.inl (hh hv))
    · exact TAssertion.ctx_extend.2 (Or.inr hv)
  · rw [TAssertion.essentials_extend, TAssertion.essentials_extend]
    intro e he
    exact TAssertion.mem_essentials.2 (hh (TAssertion.mem_essentials.1 he))
  · intro p hp
    simp only [TAssertion.extend, List.mem_append] at hp ⊢
    exact hp.imp_left (fun h => hd h)

end Silmaril.Logic.Metamath.Grammar
