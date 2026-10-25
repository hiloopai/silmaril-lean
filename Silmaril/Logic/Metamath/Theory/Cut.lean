module

public import Silmaril.Logic.Metamath.Theory.Substitution
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Cut admissibility

A derivable assertion can be used like an axiom: `Derivable.cut` removes from
the axiom set any assertion that is derivable from the rest. This justifies
checking a database statement by statement: each `$p` may cite earlier `$p`s,
and inlining their proofs yields a derivation from the `$a`s alone.

Inlining a proof of `B` at a node that applies `B` under `σ` instantiates the
proof along a substitution that agrees with `σ` on the variables of `B` and
renames the dummy variables of that proof to variables that are fresh for the
surrounding frame and for the strings `σ` substitutes. The renamed dummies
become dummies of the surrounding proof, together with the disjointness
conditions they need. Renaming apart requires an infinite type of variables,
and the renaming is injective on the dummies, so each dummy keeps a single
floating hypothesis.

Consequences: dummy variables can be chosen to avoid any finite set,
derivability is closed under adding hypotheses and disjointness conditions,
and it is invariant under injective renaming of variables.
-/

namespace Silmaril.Logic.Metamath

universe u

variable {C V : Type u}

/-- An infinite supply of variables gives a renaming of any finite list of
variables that is injective on the list and avoids a given finite set. -/
theorem exists_injOn_fresh [Infinite V] (Z : List V) (T : Finset V) :
    ∃ ρ : V → V, (∀ x ∈ Z, ∀ y ∈ Z, ρ x = ρ y → x = y) ∧ ∀ z ∈ Z, ρ z ∉ T := by
  classical
  induction Z with
  | nil => exact ⟨fun v => v, by simp, by simp⟩
  | cons z Z ih =>
    obtain ⟨ρ, hinj, hT⟩ := ih
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (T ∪ (Z.map ρ).toFinset)
    have hwT : w ∉ T := fun h => hw (Finset.mem_union_left _ h)
    have hwZ : ∀ y ∈ Z, ρ y ≠ w := fun y hy h =>
      hw (Finset.mem_union_right _ (List.mem_toFinset.2 (h ▸ List.mem_map_of_mem hy)))
    refine ⟨Function.update ρ z w, ?_, ?_⟩
    · intro x hx y hy hxy
      by_cases hxz : x = z <;> by_cases hyz : y = z
      · rw [hxz, hyz]
      · subst hxz
        rw [Function.update_self, Function.update_of_ne hyz] at hxy
        exact absurd hxy.symm (hwZ y ((List.mem_cons.1 hy).resolve_left hyz))
      · subst hyz
        rw [Function.update_self, Function.update_of_ne hxz] at hxy
        exact absurd hxy (hwZ x ((List.mem_cons.1 hx).resolve_left hxz))
      · rw [Function.update_of_ne hxz, Function.update_of_ne hyz] at hxy
        exact hinj x ((List.mem_cons.1 hx).resolve_left hxz) y
          ((List.mem_cons.1 hy).resolve_left hyz) hxy
    · intro x hx
      by_cases hxz : x = z
      · subst hxz
        rw [Function.update_self]
        exact hwT
      · rw [Function.update_of_ne hxz]
        exact hT x ((List.mem_cons.1 hx).resolve_left hxz)

/-- All pairs of variables of the images of the pairs in `l`. -/
private def imagePairs (τ : Subst C V) (l : List (V × V)) : List (V × V) :=
  l.flatMap fun p => (Str.vars (τ p.1)).flatMap fun a => (Str.vars (τ p.2)).map fun b => (a, b)

private theorem mem_imagePairs {τ : Subst C V} {l : List (V × V)} {x y a b : V}
    (hxy : (x, y) ∈ l) (ha : a ∈ Str.vars (τ x)) (hb : b ∈ Str.vars (τ y)) :
    (a, b) ∈ imagePairs τ l := by
  simp only [imagePairs, List.mem_flatMap, List.mem_map]
  exact ⟨(x, y), hxy, a, ha, b, hb, rfl⟩

section Inline

variable [DecidableEq V]

/-- The substitution that inlines a proof of `B` with dummies `Z` at a node
applying `B` under `σ`: `σ` on the variables of `B`, the renaming `ρ` on the
dummies, and the empty string elsewhere. -/
private def inlineSubst (B : Assertion C V) (Z : List V) (σ : Subst C V) (ρ : V → V) :
    Subst C V :=
  fun v => if v ∈ B.allVars then σ v else if v ∈ Z then [Sym.var (ρ v)] else []

private theorem mem_vars_inlineSubst {B : Assertion C V} {Z : List V} {σ : Subst C V}
    {ρ : V → V} {v u : V} (h : u ∈ Str.vars (inlineSubst B Z σ ρ v)) :
    (v ∈ B.allVars ∧ u ∈ Str.vars (σ v)) ∨ (v ∉ B.allVars ∧ v ∈ Z ∧ u = ρ v) := by
  unfold inlineSubst at h
  split_ifs at h with h₁ h₂
  · exact Or.inl ⟨h₁, h⟩
  · simp only [Str.vars_cons, Sym.vars_var, Str.vars_nil, List.append_nil,
      List.mem_singleton] at h
    exact Or.inr ⟨h₁, h₂, h⟩
  · simp at h

/-- The renamed dummies of an inlined proof, with the disjointness conditions
between them and the rest of the frame. -/
private def inlineDummies (F B : Assertion C V) (D : Dummies B) (σ : Subst C V) (ρ : V → V)
    (hρ : ∀ z ∈ D.vars, ρ z ∉ F.allVars)
    (hinj : ∀ x ∈ D.vars, ∀ y ∈ D.vars, ρ x = ρ y → x = y) : Dummies F where
  floats := D.floats.map fun p => (p.1, ρ p.2)
  dv := (imagePairs (inlineSubst B D.vars σ ρ) (B.dv ++ D.dv)).filter
    fun q => q.1 ∈ D.vars.map ρ ∨ q.2 ∈ D.vars.map ρ
  fresh p hp := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hρ q.2 (List.mem_map_of_mem hq)
  nodup := by
    have e : (D.floats.map fun p => (p.1, ρ p.2)).map Prod.snd = D.vars.map ρ := by
      simp [Dummies.vars, Function.comp_def]
    rw [e]
    exact D.vars_nodup.map_on hinj
  dv_dummy p hp := by
    have e : (D.floats.map fun p => (p.1, ρ p.2)).map Prod.snd = D.vars.map ρ := by
      simp [Dummies.vars, Function.comp_def]
    rw [e]
    exact of_decide_eq_true (List.mem_filter.1 hp).2

private theorem inlineDummies_vars (F B : Assertion C V) (D : Dummies B) (σ : Subst C V)
    (ρ : V → V) (hρ : ∀ z ∈ D.vars, ρ z ∉ F.allVars)
    (hinj : ∀ x ∈ D.vars, ∀ y ∈ D.vars, ρ x = ρ y → x = y) :
    (inlineDummies F B D σ ρ hρ hinj).vars = D.vars.map ρ := by
  simp [inlineDummies, Dummies.vars, List.map_map, Function.comp_def]

end Inline

namespace Derivation

variable {Γ : Set (Assertion C V)}

/-- Using a proved assertion inside another frame. Given a proof of `B` with
dummies `D`, derivations in the frame `F` of every hypothesis of `B`
instantiated by `σ`, and the disjointness conditions of `B` for distinct
variables, the instance of `B`'s conclusion is derivable in `F` extended by
fresh dummies avoiding `S`. -/
theorem exists_inline [Infinite V] {B F : Assertion C V} (D : Dummies B)
    (d : Derivation Γ (B.extend D) B.concl) (σ : Subst C V)
    (premises : ∀ e ∈ B.hypExprs, Derivation Γ F (e.subst σ))
    (hσ : ∀ x y, (x, y) ∈ B.dv → x ≠ y →
      ∀ a ∈ Str.vars (σ x), ∀ b ∈ Str.vars (σ y), a ≠ b ∧ F.Disjoint a b)
    (S : Finset V) :
    ∃ D' : Dummies F, D'.Avoids S ∧
      Nonempty (Derivation Γ (F.extend D') (B.concl.subst σ)) := by
  classical
  obtain ⟨ρ, hinj, hT⟩ := exists_injOn_fresh D.vars
    (S ∪ F.allVars.toFinset ∪ (B.allVars.flatMap fun y => Str.vars (σ y)).toFinset)
  have hT' : ∀ z ∈ D.vars, ρ z ∉ S ∧ ρ z ∉ F.allVars ∧
      ∀ y ∈ B.allVars, ρ z ∉ Str.vars (σ y) := by
    intro z hz
    have h := hT z hz
    refine ⟨fun h' => h (by simp [h']), fun h' => h (by simp [h']), fun y hy h' => h ?_⟩
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap]
    exact Or.inr ⟨y, hy, h'⟩
  let τ := inlineSubst B D.vars σ ρ
  let D' := inlineDummies F B D σ ρ (fun z hz => (hT' z hz).2.1) hinj
  have hD' : D'.vars = D.vars.map ρ := inlineDummies_vars F B D σ ρ _ hinj
  have hτB : ∀ v ∈ B.allVars, τ v = σ v := fun v hv => by simp [τ, inlineSubst, hv]
  have hτZ : ∀ z ∈ D.vars, τ z = [Sym.var (ρ z)] := fun z hz => by
    simp [τ, inlineSubst, D.vars_not_mem_allVars hz, hz]
  refine ⟨D', ?_, ?_⟩
  · intro v hv
    rw [hD'] at hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
    exact (hT' z hz).1
  have hyps : ∀ e ∈ (B.extend D).hypExprs, Derivation Γ (F.extend D') (e.subst τ) := by
    intro e he
    by_cases h : e ∈ B.hypExprs
    · refine ((premises e h).extend D').cast (Expr.subst_congr fun v hv => ?_)
      exact (hτB v (Assertion.mem_allVars_of_mem_hypExprs h hv)).symm
    · refine Derivation.hyp ?_
      obtain ⟨p, hp, rfl⟩ := (Assertion.mem_hypExprs_extend.1 he).resolve_left h
      have hz : p.2 ∈ D.vars := List.mem_map_of_mem hp
      refine Assertion.mem_hypExprs_extend.2 (Or.inr ⟨(p.1, ρ p.2), ?_, ?_⟩)
      · exact List.mem_map_of_mem (f := fun p : C × V => (p.1, ρ p.2)) hp
      · simp [Expr.subst, hτZ _ hz]
  have key : ∀ x y, (x, y) ∈ B.dv ++ D.dv → x ≠ y →
      ∀ a ∈ Str.vars (τ x), ∀ b ∈ Str.vars (τ y), a ≠ b ∧ (F.extend D').Disjoint a b := by
    intro x y hxy hne a ha b hb
    have hpair : (a, b) ∈ imagePairs τ (B.dv ++ D.dv) := mem_imagePairs hxy ha hb
    have hdisj : a ∈ D.vars.map ρ ∨ b ∈ D.vars.map ρ → (F.extend D').Disjoint a b := fun h =>
      Or.inl (List.mem_append_right _ (List.mem_filter.2 ⟨hpair, by simpa using h⟩))
    rcases mem_vars_inlineSubst ha with ⟨hx, ha'⟩ | ⟨hx, hxZ, rfl⟩ <;>
      rcases mem_vars_inlineSubst hb with ⟨hy, hb'⟩ | ⟨hy, hyZ, rfl⟩
    · have hB : (x, y) ∈ B.dv := by
        rcases List.mem_append.1 hxy with h | h
        · exact h
        · exfalso
          rcases D.dv_dummy _ h with h' | h'
          · exact D.vars_not_mem_allVars h' hx
          · exact D.vars_not_mem_allVars h' hy
      obtain ⟨h₁, h₂⟩ := hσ x y hB hne a ha' b hb'
      exact ⟨h₁, Assertion.Disjoint.mono (F.dv_subset_extend D') h₂⟩
    · refine ⟨?_, hdisj (Or.inr (List.mem_map_of_mem hyZ))⟩
      rintro rfl
      exact (hT' y hyZ).2.2 x hx ha'
    · refine ⟨?_, hdisj (Or.inl (List.mem_map_of_mem hxZ))⟩
      intro h
      exact (hT' x hxZ).2.2 y hy (h ▸ hb')
    · exact ⟨fun h => hne (hinj x hxZ y hyZ h), hdisj (Or.inl (List.mem_map_of_mem hxZ))⟩
  have dv : τ.DVPreserving (B.extend D).Disjoint (F.extend D').Disjoint := by
    intro a b hab hd a' ha' b' hb'
    rcases hd with h | h
    · exact key a b h hab a' ha' b' hb'
    · obtain ⟨h₁, h₂⟩ := key b a h (Ne.symm hab) b' hb' a' ha'
      exact ⟨Ne.symm h₁, h₂.symm⟩
  refine ⟨(d.subst τ hyps dv).cast (Expr.subst_congr fun v hv => ?_)⟩
  exact hτB v (Assertion.mem_allVars_of_mem_concl hv)

/-- Derivations of a list of goals in one frame combine into a single frame
extension. -/
private theorem exists_dummies_forall {F : Assertion C V}
    (g : Expr C V → Expr C V) (l : List (Expr C V))
    (h : ∀ e ∈ l, ∀ S : Finset V, ∃ D : Dummies F, D.Avoids S ∧
      Nonempty (Derivation Γ (F.extend D) (g e))) (S : Finset V) :
    ∃ D : Dummies F, D.Avoids S ∧ ∀ e ∈ l, Nonempty (Derivation Γ (F.extend D) (g e)) := by
  classical
  induction l generalizing S with
  | nil => exact ⟨Dummies.none F, Dummies.none_avoids S, by simp⟩
  | cons e l ih =>
    obtain ⟨D₁, hS₁, ⟨d₁⟩⟩ := h e (List.mem_cons_self ..) S
    obtain ⟨D₂, hS₂, hd₂⟩ :=
      ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')) (S ∪ D₁.vars.toFinset)
    have hD : ∀ v ∈ D₁.vars, v ∉ D₂.vars := fun v hv hv₂ => hS₂ v hv₂ (by simp [hv])
    refine ⟨D₁.union D₂ hD, hS₁.union (hS₂.mono Finset.subset_union_left) hD, ?_⟩
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨d₁.weaken (F.hypExprs_subset_union_left D₁ D₂ hD)
        (F.dv_subset_union_left D₁ D₂ hD)⟩
    · obtain ⟨d₂⟩ := hd₂ e' he'
      exact ⟨d₂.weaken (F.hypExprs_subset_union_right D₁ D₂ hD)
        (F.dv_subset_union_right D₁ D₂ hD)⟩

/-- Lemma elimination for derivations: every application of an assertion of
`Δ` is replaced by an inlined proof of it from `Γ`. The new dummies avoid `S`. -/
theorem exists_cut [Infinite V] {Δ : Set (Assertion C V)}
    (hΔ : ∀ B ∈ Δ, Derivable Γ B)
    {F : Assertion C V} {e : Expr C V} (d : Derivation (Γ ∪ Δ) F e) (S : Finset V) :
    ∃ D : Dummies F, D.Avoids S ∧ Nonempty (Derivation Γ (F.extend D) e) := by
  classical
  induction d generalizing S with
  | hyp he =>
    exact ⟨Dummies.none F, Dummies.none_avoids S, ⟨(Derivation.hyp he).extend _⟩⟩
  | app B hB σ premises hσ ih =>
    obtain ⟨D₀, hS₀, hprem⟩ :=
      exists_dummies_forall (Expr.subst σ) B.hypExprs (fun e he => ih e he) S
    have prem : ∀ e ∈ B.hypExprs, Derivation Γ (F.extend D₀) (e.subst σ) :=
      fun e he => (hprem e he).some
    have hσ₀ : B.DVSafe σ (F.extend D₀).Disjoint := fun x y hxy a ha b hb =>
      (hσ x y hxy a ha b hb).imp_right (Assertion.Disjoint.mono (F.dv_subset_extend D₀))
    by_cases hBΓ : B ∈ Γ
    · exact ⟨D₀, hS₀, ⟨Derivation.app B hBΓ σ prem hσ₀⟩⟩
    · have hBΔ : B ∈ Δ := ((Set.mem_union _ _ _).1 hB).resolve_left hBΓ
      obtain ⟨⟨DB, dB⟩⟩ := hΔ B hBΔ
      obtain ⟨D₁, hS₁, ⟨d₁⟩⟩ :=
        exists_inline DB dB σ prem (fun x y hxy _ => hσ₀ x y hxy) S
      exact ⟨D₀.append D₁, hS₀.append hS₁, ⟨(F.extend_append D₀ D₁) ▸ d₁⟩⟩

end Derivation

variable {Γ Δ : Set (Assertion C V)} {A B : Assertion C V}

/-- Cut admissibility: assertions derivable from `Γ` may be added to `Γ`
without deriving anything new. -/
theorem Derivable.cut [Infinite V] (hΔ : ∀ B ∈ Δ, Derivable Γ B)
    (hA : Derivable (Γ ∪ Δ) A) : Derivable Γ A := by
  obtain ⟨⟨D, d⟩⟩ := hA
  obtain ⟨D', -, ⟨d'⟩⟩ := Derivation.exists_cut hΔ d ∅
  exact ⟨⟨D.append D', (A.extend_append D D') ▸ d'⟩⟩

/-- Derivability is transitive between axiom sets. -/
theorem Derivable.trans [Infinite V] (hΔ : ∀ B ∈ Δ, Derivable Γ B)
    (hA : Derivable Δ A) : Derivable Γ A :=
  Derivable.cut hΔ (hA.mono Set.subset_union_right)

/-- A single derivable lemma can be eliminated. -/
theorem Derivable.cut_insert [Infinite V] (hB : Derivable Γ B)
    (hA : Derivable (insert B Γ) A) : Derivable Γ A := by
  refine Derivable.cut (Δ := {B}) (by simpa using hB) ?_
  rwa [Set.union_singleton]

/-- A theorem may be applied inside another frame, adding fresh dummy
variables that avoid `S`. -/
theorem Derivable.exists_apply [Infinite V] (hB : Derivable Γ B) {F : Assertion C V}
    (σ : Subst C V) (premises : ∀ e ∈ B.hypExprs, Derivation Γ F (e.subst σ))
    (hσ : B.DVSafe σ F.Disjoint) (S : Finset V) :
    ∃ D : Dummies F, D.Avoids S ∧ Nonempty (Derivation Γ (F.extend D) (B.concl.subst σ)) := by
  obtain ⟨⟨D, d⟩⟩ := hB
  exact Derivation.exists_inline D d σ premises (fun x y hxy _ => hσ x y hxy) S

/-- An instance of a theorem is a theorem: if every hypothesis of `B`,
instantiated by `σ`, is derivable in the frame of `A`, and `σ` respects the
disjointness conditions of `B` there, then `A` is derivable. -/
theorem Derivable.of_instance [Infinite V] (hB : Derivable Γ B) (σ : Subst C V)
    (premises : ∀ e ∈ B.hypExprs, Nonempty (Derivation Γ A (e.subst σ)))
    (hσ : B.DVSafe σ A.Disjoint) (hA : A.concl = B.concl.subst σ) : Derivable Γ A := by
  obtain ⟨D, -, ⟨d⟩⟩ := hB.exists_apply σ (fun e he => (premises e he).some) hσ ∅
  exact ⟨⟨D, d.cast hA.symm⟩⟩

private theorem exists_rename_dummies [Infinite V] (D : Dummies A)
    (d : Derivation Γ (A.extend D) A.concl) (S : Finset V) :
    ∃ D' : Dummies A, D'.Avoids S ∧ Nonempty (Derivation Γ (A.extend D') A.concl) := by
  obtain ⟨D', hS, ⟨d'⟩⟩ := Derivation.exists_inline D d Subst.id
    (fun e he => Derivation.hyp (by simpa using he))
    (fun x y hxy hne a ha b hb => by
      simp only [Subst.vars_rename, List.mem_singleton] at ha hb
      subst a b
      exact ⟨hne, Or.inl hxy⟩) S
  exact ⟨D', hS, ⟨d'.cast (Expr.subst_id _)⟩⟩

/-- The dummy variables of a proof can be chosen to avoid any finite set. -/
theorem Derivable.exists_avoiding [Infinite V] (h : Derivable Γ A) (S : Finset V) :
    ∃ D : Dummies A, D.Avoids S ∧ Nonempty (Derivation Γ (A.extend D) A.concl) := by
  obtain ⟨⟨D, d⟩⟩ := h
  exact exists_rename_dummies D d S

namespace Dummies

/-- Dummies of `A` that avoid the variables of `A'` are dummies of `A'`. -/
def transfer {A' : Assertion C V} (D : Dummies A) (h : ∀ v ∈ D.vars, v ∉ A'.allVars) :
    Dummies A' where
  floats := D.floats
  dv := D.dv
  fresh p hp := h p.2 (List.mem_map_of_mem hp)
  nodup := D.nodup
  dv_dummy := D.dv_dummy

@[simp] theorem transfer_vars {A' : Assertion C V} (D : Dummies A)
    (h : ∀ v ∈ D.vars, v ∉ A'.allVars) : (D.transfer h).vars = D.vars := rfl

end Dummies

/-- Weakening: derivability is closed under adding hypotheses and
disjointness conditions. -/
theorem Derivable.weaken [Infinite V] {A' : Assertion C V} (h : Derivable Γ A)
    (hh : A.hyps ⊆ A'.hyps) (hd : A.dv ⊆ A'.dv) (hc : A'.concl = A.concl) :
    Derivable Γ A' := by
  classical
  obtain ⟨D, hS, ⟨d⟩⟩ := h.exists_avoiding A'.allVars.toFinset
  let D' : Dummies A' := D.transfer fun v hv h' => hS v hv (List.mem_toFinset.2 h')
  refine ⟨⟨D', (d.weaken ?_ ?_).cast hc.symm⟩⟩
  · intro e he
    simp only [Assertion.hypExprs, Assertion.extend, List.map_append, List.mem_append] at he ⊢
    rcases he with he | he
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      exact Or.inl (List.mem_map_of_mem (hh hx))
    · exact Or.inr he
  · intro p hp
    simp only [Assertion.extend, List.mem_append] at hp ⊢
    exact hp.imp_left (fun h => hd h)

theorem Str.vars_subst_rename (ρ : V → V) (s : Str C V) :
    Str.vars (Str.subst (Subst.rename ρ) s) = (Str.vars s).map ρ := by
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simp [ih, Subst.rename]

theorem Assertion.allVars_rename (ρ : V → V) (A : Assertion C V) :
    (A.rename ρ).allVars = A.allVars.map ρ := by
  have hh : ∀ h : Hyp C V, (h.rename ρ).vars = h.vars.map ρ := by
    intro h
    cases h <;> simp [Hyp.rename, Hyp.vars, Expr.vars, Str.vars_subst_rename]
  simp [Assertion.allVars, Assertion.rename, Expr.vars, Str.vars_subst_rename, List.map_flatMap,
    List.flatMap_map, hh]

/-- Derivability is invariant under injective renaming of variables. -/
theorem Derivable.rename {ρ : V → V} (hρ : Function.Injective ρ) (h : Derivable Γ A) :
    Derivable Γ (A.rename ρ) := by
  obtain ⟨⟨D, d⟩⟩ := h
  let D' : Dummies (A.rename ρ) :=
    { floats := D.floats.map fun p => (p.1, ρ p.2)
      dv := D.dv.map (Prod.map ρ ρ)
      fresh := by
        intro p hp h'
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        rw [Assertion.allVars_rename] at h'
        obtain ⟨v, hv, hvq⟩ := List.mem_map.1 h'
        exact D.fresh q hq (hρ hvq ▸ hv)
      nodup := by
        simpa [Function.comp_def] using D.nodup.map hρ
      dv_dummy := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        simp only [List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd]
        have hm : ∀ v ∈ D.floats.map Prod.snd, ρ v ∈ D.floats.map fun x => ρ x.2 := by
          intro v hv
          obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
          exact List.mem_map_of_mem (f := fun x => ρ x.2) hr
        exact (D.dv_dummy q hq).imp (hm _) (hm _) }
  have hframe : (A.extend D).rename ρ = (A.rename ρ).extend D' := by
    simp [Assertion.rename, Assertion.extend, D', Hyp.rename, Function.comp_def]
  exact ⟨⟨D', hframe ▸ d.rename ρ (fun x y hxy _ h' => hxy (hρ h'))⟩⟩

/-- Renaming along a permutation neither creates nor destroys theorems. -/
theorem Derivable.rename_perm_iff (e : Equiv.Perm V) :
    Derivable Γ (A.rename e) ↔ Derivable Γ A := by
  refine ⟨fun h => ?_, Derivable.rename e.injective⟩
  have h' := h.rename e.symm.injective
  rwa [Assertion.rename_rename, show (e.symm ∘ e : V → V) = fun v => v from
    funext e.symm_apply_apply, Assertion.rename_id] at h'

end Silmaril.Logic.Metamath
