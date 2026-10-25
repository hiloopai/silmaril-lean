module

public import Mathlib.SetTheory.ZFC.Basic
public import Silmaril.Logic.SetTheory.Axioms

@[expose] public section

/-!
# `ZFSet` is a model of set.mm's ZFC

Mathlib's `ZFSet.{u}` satisfies every axiom of ZFC in the exact shape stated in
set.mm (`Silmaril.Logic.SetTheory.Axioms`), for every variable type and every
instance of the schemes allowed by the disjoint-variable conditions.

Each axiom is first proved in a plain form with the scheme's formula as an
arbitrary Lean predicate (`ZFSetModel.exists_rep`, ...). The valuation form
then follows by computing the updated valuations. Replacement holds for
arbitrary predicates because Lean's `ZFSet` is closed under images of arbitrary
functions on small index types. The axiom of choice uses `Classical.choice`,
and set.mm's `ax-ac` also needs regularity, which holds by well-foundedness of
`∈` on `ZFSet`.
-/

namespace Silmaril.Logic.SetTheory

universe u v

namespace ZFSetModel

open ZFSet

/-- Extensionality. -/
theorem ext_of_forall {x y : ZFSet.{u}} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := ZFSet.ext h

/-- Replacement for an arbitrary functional relation `P`. -/
theorem exists_rep (P : ZFSet.{u} → ZFSet.{u} → Prop) (x : ZFSet.{u})
    (h : ∀ a, ∃ b, ∀ c, P a c → c = b) :
    ∃ y : ZFSet.{u}, ∀ c, c ∈ y ↔ ∃ a, a ∈ x ∧ P a c := by
  refine ⟨range (fun p : {a : x // ∃ c, P a.1 c} => p.2.choose), fun c => ?_⟩
  simp only [mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.1, p.1.2, p.2.choose_spec⟩
  · rintro ⟨a, ha, hc⟩
    refine ⟨⟨⟨a, ha⟩, c, hc⟩, ?_⟩
    obtain ⟨b, hb⟩ := h a
    exact (hb _ (Exists.choose_spec (⟨c, hc⟩ : ∃ c, P a c))).trans (hb c hc).symm

/-- Separation for an arbitrary predicate `P`. -/
theorem exists_sep (P : ZFSet.{u} → Prop) (z : ZFSet.{u}) :
    ∃ y : ZFSet.{u}, ∀ a, a ∈ y ↔ a ∈ z ∧ P a :=
  ⟨ZFSet.sep P z, fun _ => mem_sep⟩

/-- The null set axiom. -/
theorem exists_nul : ∃ x : ZFSet.{u}, ∀ y, y ∉ x := ⟨∅, notMem_empty⟩

/-- The power set axiom. -/
theorem exists_pow (x : ZFSet.{u}) :
    ∃ y : ZFSet.{u}, ∀ z : ZFSet.{u}, (∀ w, w ∈ z → w ∈ x) → z ∈ y :=
  ⟨powerset x, fun _ h => mem_powerset.2 fun _ hw => h _ hw⟩

/-- The pairing axiom. -/
theorem exists_pr (x y : ZFSet.{u}) : ∃ z : ZFSet.{u}, ∀ w, (w = x ∨ w = y) → w ∈ z :=
  ⟨{x, y}, fun _ h => mem_pair.2 h⟩

/-- The union axiom. -/
theorem exists_un (x : ZFSet.{u}) :
    ∃ y : ZFSet.{u}, ∀ z : ZFSet.{u}, (∃ w : ZFSet.{u}, z ∈ w ∧ w ∈ x) → z ∈ y :=
  ⟨⋃₀ x, fun _ ⟨_, hz, hw⟩ => mem_sUnion_of_mem hz hw⟩

/-- The regularity axiom. -/
theorem reg (x : ZFSet.{u}) (h : ∃ y, y ∈ x) :
    ∃ y, y ∈ x ∧ ∀ z : ZFSet.{u}, z ∈ y → z ∉ x := by
  obtain ⟨y, hy, he⟩ := regularity x fun hx => by
    obtain ⟨y, hy⟩ := h
    exact notMem_empty y (hx ▸ hy)
  refine ⟨y, hy, fun z hzy hzx => notMem_empty z ?_⟩
  rw [← he]
  exact mem_inter.2 ⟨hzx, hzy⟩

/-- The iterated singletons `x`, `{x}`, `{{x}}`, .... -/
noncomputable def singletonTower (x : ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  (fun s => ({s} : ZFSet.{u}))^[n] x

/-- set.mm's axiom of infinity: every set lies in a set each of whose members lies in
another member. -/
theorem exists_inf (x : ZFSet.{u}) :
    ∃ y : ZFSet.{u}, x ∈ y ∧ ∀ z, z ∈ y → ∃ w : ZFSet.{u}, z ∈ w ∧ w ∈ y := by
  refine ⟨range (fun n : ULift.{u} ℕ => singletonTower x n.down),
    mem_range.2 ⟨⟨0⟩, rfl⟩, fun z hz => ?_⟩
  obtain ⟨⟨n⟩, rfl⟩ := mem_range.1 hz
  refine ⟨singletonTower x (n + 1), ?_, mem_range.2 ⟨⟨n + 1⟩, rfl⟩⟩
  simp [singletonTower, Function.iterate_succ_apply']

/-- The axiom of infinity in the form `ax-inf2`: `omega` is a witness. -/
theorem exists_inf2 : ∃ x : ZFSet.{u}, (∃ y, y ∈ x ∧ ∀ z, z ∉ y) ∧
    ∀ y, y ∈ x → ∃ z, z ∈ x ∧ ∀ w, w ∈ z ↔ w ∈ y ∨ w = y :=
  ⟨omega, ⟨∅, omega_zero, notMem_empty⟩, fun y hy =>
    ⟨insert y y, omega_succ hy, fun w => by rw [mem_insert_iff, or_comm]⟩⟩

/-- A choice of an element of each nonempty set. -/
noncomputable def pick (w : ZFSet.{u}) : ZFSet.{u} :=
  open Classical in if h : w.Nonempty then h.some else ∅

theorem pick_mem {w : ZFSet.{u}} (h : w.Nonempty) : pick w ∈ w := by
  simp only [pick, h, ↓reduceDIte]
  exact h.some_mem

/-- set.mm's axiom of choice `ax-ac`: a set of pairs `{w, pick w}` selects a unique element
of each nonempty member of `x`. -/
theorem exists_ac (x : ZFSet.{u}) : ∃ y : ZFSet.{u}, ∀ z w : ZFSet.{u}, z ∈ w ∧ w ∈ x →
    ∃ v, ∀ u, (∃ t : ZFSet.{u}, (u ∈ w ∧ w ∈ t) ∧ (u ∈ t ∧ t ∈ y)) ↔ u = v := by
  refine ⟨range (fun p : {w : x // w.1.Nonempty} => ({p.1.1, pick p.1.1} : ZFSet)),
    fun z w ⟨hzw, hwx⟩ => ⟨pick w, fun u => ?_⟩⟩
  have hw : w.Nonempty := ⟨z, hzw⟩
  constructor
  · rintro ⟨t, ⟨huw, hwt⟩, hut, hty⟩
    obtain ⟨⟨⟨w', hw'x⟩, hw'⟩, rfl⟩ := mem_range.1 hty
    have hpw' := pick_mem hw'
    rcases mem_pair.1 hwt with rfl | rfl <;> rcases mem_pair.1 hut with rfl | rfl
    · exact absurd huw (mem_irrefl _)
    · rfl
    · exact absurd huw (mem_asymm hpw')
    · exact absurd huw (mem_irrefl _)
  · rintro rfl
    exact ⟨{w, pick w}, ⟨pick_mem hw, mem_pair.2 (.inl rfl)⟩, mem_pair.2 (.inr rfl),
      mem_range.2 ⟨⟨⟨w, hwx⟩, hw⟩, rfl⟩⟩

/-- Maes' axiom of choice `ax-ac2`. Either some member `y` of `x` is covered by the other
members, or a choice set for `x` avoiding `x` exists. -/
theorem exists_ac2 (x : ZFSet.{u}) : ∃ y : ZFSet.{u}, ∀ z : ZFSet.{u}, ∃ v : ZFSet.{u}, ∀ u,
    (y ∈ x ∧ (z ∈ y → (v ∈ x ∧ ¬ y = v) ∧ z ∈ v)) ∨
    (y ∉ x ∧ (z ∈ x → (v ∈ z ∧ v ∈ y) ∧ (u ∈ z ∧ u ∈ y → u = v))) := by
  by_cases hA : ∃ y ∈ x, ∀ z ∈ y, ∃ v ∈ x, y ≠ v ∧ z ∈ v
  · obtain ⟨y, hyx, hy⟩ := hA
    refine ⟨y, fun z => ?_⟩
    by_cases hz : z ∈ y
    · obtain ⟨v, hvx, hyv, hzv⟩ := hy z hz
      exact ⟨v, fun _ => .inl ⟨hyx, fun _ => ⟨⟨hvx, hyv⟩, hzv⟩⟩⟩
    · exact ⟨∅, fun _ => .inl ⟨hyx, fun h => absurd h hz⟩⟩
  · push Not at hA
    let p : x → ZFSet.{u} := fun a => (hA a.1 a.2).choose
    have hp : ∀ a : x, p a ∈ a.1 ∧ ∀ v ∈ x, a.1 ≠ v → p a ∉ v := fun a =>
      (hA a.1 a.2).choose_spec
    have hU : ⋃₀ x ∉ ⋃₀ x := mem_irrefl _
    have hUz : ∀ z ∈ x, ⋃₀ x ∉ z := fun z hz h => hU (mem_sUnion_of_mem h hz)
    let c := insert (⋃₀ x) (range p)
    refine ⟨c, fun z => ?_⟩
    by_cases hz : z ∈ x
    · refine ⟨p ⟨z, hz⟩, fun u => .inr ⟨fun hc => hUz c hc (mem_insert _ _), fun _ =>
        ⟨⟨(hp ⟨z, hz⟩).1, mem_insert_of_mem _ (mem_range_self _)⟩, ?_⟩⟩⟩
      rintro ⟨huz, huc⟩
      rcases mem_insert_iff.1 huc with rfl | hur
      · exact absurd huz (hUz z hz)
      · obtain ⟨a, rfl⟩ := mem_range.1 hur
        by_cases haz : a.1 = z
        · obtain ⟨a, ha⟩ := a
          subst haz
          rfl
        · exact absurd huz ((hp a).2 z hz haz)
    · exact ⟨∅, fun _ => .inr ⟨fun hc => hUz c hc (mem_insert _ _), fun h => absurd h hz⟩⟩

open Function

variable {V : Type v} [DecidableEq V]

/-- `ax-ext` holds in `ZFSet`. -/
theorem valid_ext {x y z : V} (hxz : x ≠ z) (hyz : y ≠ z) :
    Valid (Axioms.ext (M := ZFSet.{u}) x y z) := by
  intro ρ
  simp only [Axioms.ext, Wff.imp, Wff.all, Wff.iff, Wff.mem, Wff.eq, update_apply, hxz, hyz,
    ite_false, ite_true]
  exact ZFSet.ext

/-- `ax-rep` holds in `ZFSet` for an arbitrary formula `φ`. -/
theorem valid_rep {x y z w : V} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (φ : Wff ZFSet.{u} V) : Valid (Axioms.rep x y z w φ) := by
  intro ρ
  simp only [Axioms.rep, Wff.imp, Wff.all, Wff.ex, Wff.iff, Wff.and, Wff.mem, Wff.eq,
    update_apply, hxy, hxz, hxw, hyz, hyw, hzw, hyz.symm, hzw.symm, hyw.symm, ite_false,
    ite_true, update_comm hyz, update_comm hyw, update_comm hzw, update_idem]
  exact ZFSetModel.exists_rep _ (ρ x)

/-- `ax-sep` holds in `ZFSet` when `y` is not free in `φ`. -/
theorem valid_sep {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (φ : Wff ZFSet.{u} V)
    (hφ : Wff.NotFree y φ) :
    Valid (Axioms.sep (M := ZFSet.{u}) x y z φ) := by
  intro ρ
  simp only [Axioms.sep, Wff.and, Wff.iff, Wff.mem, Wff.all, Wff.ex, update_apply, hxy, hxy.symm,
    hxz.symm, hyz.symm, ite_false, ite_true, update_comm hxy.symm, hφ.apply]
  exact ZFSetModel.exists_sep (fun a => φ (update ρ x a)) (ρ z)

/-- `ax-nul` holds in `ZFSet`. set.mm imposes no disjoint-variable condition, and for `x = y`
the instance `E. x A. x -. x e. x` holds by irreflexivity of `∈`. -/
theorem valid_nul (x y : V) : Valid (Axioms.nul (M := ZFSet.{u}) x y) := by
  intro ρ
  by_cases hxy : x = y
  · subst hxy
    simp only [Axioms.nul, Wff.not, Wff.mem, Wff.all, Wff.ex, update_self]
    exact ⟨∅, mem_irrefl⟩
  · simp only [Axioms.nul, Wff.not, Wff.mem, Wff.all, Wff.ex, update_apply, hxy, Ne.symm hxy,
      ite_false, ite_true]
    exact ZFSetModel.exists_nul

/-- `ax-pow` holds in `ZFSet`. -/
theorem valid_pow {x y z w : V} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) :
    Valid (Axioms.pow (M := ZFSet.{u}) x y z w) := by
  intro ρ
  simp only [Axioms.pow, Wff.imp, Wff.mem, Wff.all, Wff.ex, update_apply, hxy, hxz, hxw, hyz,
    hyz.symm, hyw.symm, hzw, hzw.symm, ite_false, ite_true]
  exact ZFSetModel.exists_pow (ρ x)

/-- `ax-pr` holds in `ZFSet`. -/
theorem valid_pr {x y z w : V} (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hzw : z ≠ w) :
    Valid (Axioms.pr (M := ZFSet.{u}) x y z w) := by
  intro ρ
  simp only [Axioms.pr, Wff.imp, Wff.or, Wff.eq, Wff.mem, Wff.all, Wff.ex, update_apply, hxz, hxw,
    hyz, hyw, hzw, hzw.symm, ite_false, ite_true]
  exact ZFSetModel.exists_pr (ρ x) (ρ y)

/-- `ax-un` holds in `ZFSet`. -/
theorem valid_un {x y z w : V} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hzw : z ≠ w) :
    Valid (Axioms.un (M := ZFSet.{u}) x y z w) := by
  intro ρ
  simp only [Axioms.un, Wff.imp, Wff.and, Wff.mem, Wff.all, Wff.ex, update_apply, hxy, hxz, hxw,
    hyz, hyz.symm, hyw.symm, hzw, hzw.symm, ite_false, ite_true]
  exact ZFSetModel.exists_un (ρ x)

/-- `ax-reg` holds in `ZFSet`. -/
theorem valid_reg {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Valid (Axioms.reg (M := ZFSet.{u}) x y z) := by
  intro ρ
  simp only [Axioms.reg, Wff.imp, Wff.not, Wff.and, Wff.mem, Wff.all, Wff.ex, update_apply, hxy,
    hxz, hyz, hyz.symm, ite_false, ite_true]
  exact ZFSetModel.reg (ρ x)

/-- `ax-inf` holds in `ZFSet`. -/
theorem valid_inf {x y z w : V} (hxy : x ≠ y) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Valid (Axioms.inf (M := ZFSet.{u}) x y z w) := by
  intro ρ
  simp only [Axioms.inf, Wff.imp, Wff.and, Wff.mem, Wff.all, Wff.ex, update_apply, hxy, hyz,
    hyz.symm, hyw, hyw.symm, hzw, hzw.symm, ite_false, ite_true]
  exact ZFSetModel.exists_inf (ρ x)

/-- `ax-inf2` holds in `ZFSet`. -/
theorem valid_inf2 {x y z w : V} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) :
    Valid (Axioms.inf2 (M := ZFSet.{u}) x y z w) := by
  intro ρ
  simp only [Axioms.inf2, Wff.imp, Wff.not, Wff.and, Wff.or, Wff.iff, Wff.eq, Wff.mem, Wff.all,
    Wff.ex, update_apply, hxy, hxy.symm, hxz, hxz.symm, hxw.symm, hyz, hyz.symm, hyw, hyw.symm, hzw,
    hzw.symm, ite_false, ite_true]
  exact ZFSetModel.exists_inf2

/-- `ax-ac` holds in `ZFSet`. -/
theorem valid_ac {x y z w v u t : V} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hyv : y ≠ v) (hyu : y ≠ u) (hyt : y ≠ t) (hzw : z ≠ w) (hzv : z ≠ v)
    (hzu : z ≠ u) (hzt : z ≠ t) (hwv : w ≠ v) (hwu : w ≠ u) (hwt : w ≠ t) (hvu : v ≠ u)
    (hvt : v ≠ t) (hut : u ≠ t) :
    Valid (Axioms.ac (M := ZFSet.{u}) x y z w v u t) := by
  intro ρ
  simp only [Axioms.ac, Wff.imp, Wff.and, Wff.iff, Wff.eq, Wff.mem, Wff.all, Wff.ex, update_apply,
    hxy, hxz, hxw, hyz, hyz.symm, hyw, hyw.symm, hyv, hyv.symm, hyu, hyu.symm, hyt, hyt.symm, hzw,
    hzw.symm, hzv.symm, hzu.symm, hzt.symm, hwv, hwv.symm, hwu, hwu.symm, hwt, hwt.symm, hvu,
    hvu.symm, hvt.symm, hut, hut.symm, ite_false, ite_true]
  exact ZFSetModel.exists_ac (ρ x)

/-- `ax-ac2` holds in `ZFSet`. -/
theorem valid_ac2 {x y z v u : V} (hxy : x ≠ y) (hxz : x ≠ z) (hxv : x ≠ v) (hxu : x ≠ u)
    (hyz : y ≠ z) (hyv : y ≠ v) (hyu : y ≠ u) (hzv : z ≠ v) (hzu : z ≠ u) (hvu : v ≠ u) :
    Valid (Axioms.ac2 (M := ZFSet.{u}) x y z v u) := by
  intro ρ
  simp only [Axioms.ac2, Wff.imp, Wff.not, Wff.and, Wff.or, Wff.eq, Wff.mem, Wff.all, Wff.ex,
    update_apply, hxy, hxz, hxv, hxu, hyz, hyz.symm, hyv, hyv.symm, hyu, hyu.symm, hzv, hzv.symm,
    hzu, hzu.symm, hvu, hvu.symm, ite_false, ite_true]
  exact ZFSetModel.exists_ac2 (ρ x)

end ZFSetModel

open ZFSetModel

variable (V : Type v) [DecidableEq V]

/-- `ZFSet` is a model of set.mm's ZF. -/
theorem zf_zfset : ZF ZFSet.{u} V where
  ext _ _ _ h := valid_ext (by simp_all) (by simp_all)
  rep _ _ _ _ φ h := valid_rep (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) φ
  sep _ _ _ φ h hφ _ := valid_sep (by simp_all) (by simp_all) (by simp_all) φ hφ
  nul := valid_nul
  pow _ _ _ _ h := valid_pow (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all)
  pr _ _ _ _ h h' := valid_pr (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all)
  un _ _ _ _ h := valid_un (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all)
  reg _ _ _ h := valid_reg (by simp_all) (by simp_all) (by simp_all)
  inf _ _ _ _ h := valid_inf (by simp_all) (by simp_all) (by simp_all) (by simp_all)
  inf2 _ _ _ _ h := valid_inf2 (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all)

/-- `ZFSet` is a model of set.mm's ZFC. -/
theorem zfc_zfset : ZFC ZFSet.{u} V where
  toZF := zf_zfset V
  ac _ _ _ _ _ _ _ h := valid_ac (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all)
  ac2 _ _ _ _ _ h := valid_ac2 (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)

end Silmaril.Logic.SetTheory
