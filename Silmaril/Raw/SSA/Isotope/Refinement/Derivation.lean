module

public import Silmaril.Raw.SSA.Isotope.Refinement.Laws

/-!
# Derivations of the written refinement theory

Refinement is directed. Symmetry is supplied only for the designated equation
schemes; uniformity uses the same generated refinement in its premise.
Every judgment has two well-typed endpoints. Formation checks are explicit on
primitive rules: the printed beta premises do not by themselves guarantee that
a zero-use body can discard a value of a linear type.
-/

@[expose] public section
set_option autoImplicit true

namespace Silmaril.Isotope.Refinement

universe u v w

namespace Polarity

/-- Source endpoint of a polarity-marked judgment. -/
def source {α : Sort u} : Polarity → α → α → α
  | .positive, a, _ => a
  | .negative, _, b => b

/-- Target endpoint of a polarity-marked judgment. -/
def target {α : Sort u} : Polarity → α → α → α
  | .positive, _, b => b
  | .negative, a, _ => a

@[simp] theorem orient_endpoints {α : Sort u} (p : Polarity)
    (R : α → α → Prop) (a b : α) : p.orient R a b ↔ R (p.source a b) (p.target a b) := by
  cases p <;> exact Iff.rfl

end Polarity

/-- A family of directed judgments indexed by quantitative contexts and types. -/
abbrev Relation (τ : Type u) (Φ : Type v) :=
  {n : Nat} → QCtx τ n → Term Φ n → Term Φ n → τ → Prop

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

/-- Judgment formation forgets the particular effect upper bound, not typing. -/
abbrev WellTyped (F : Fragment) (Γ : QCtx τ n) (a : Term Φ n) (A : τ) : Prop :=
  Nonempty (HasType F Γ (⊤ : ε) a A)

/-- The full native directed theory, with all written rule side conditions. -/
inductive Refines {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
    {Φ : Type v} [HasTy Φ τ] {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
    (F : Fragment) (R : Relation τ Φ) : Relation τ Φ where
  | base {Γ : QCtx τ n} {a b : Term Φ n} {A : τ}
      (h : R Γ a b A) (ha : WellTyped (ε := ε) F Γ a A)
      (hb : WellTyped (ε := ε) F Γ b A) : Refines (ε := ε) F (@R) Γ a b A
  | refl {Γ : QCtx τ n} {a : Term Φ n} {A : τ}
      (h : WellTyped (ε := ε) F Γ a A) : Refines (ε := ε) F (@R) Γ a a A
  | trans : Refines (ε := ε) F (@R) Γ a b A → Refines (ε := ε) F (@R) Γ b c A → Refines (ε := ε) F (@R) Γ a c A
  | equation {Γ : QCtx τ n} {a b : Term Φ n} {A : τ} (p : Polarity)
      (h : EquationAxiom (ε := ε) F Γ a b A)
      (ha : WellTyped (ε := ε) F Γ a A) (hb : WellTyped (ε := ε) F Γ b A) :
      Refines (ε := ε) F (@R) Γ (p.source a b) (p.target a b) A
  | directional {Γ : QCtx τ n} {a b : Term Φ n} {A : τ} (p : Polarity)
      (h : DirectionalAxiom (ε := ε) F p Γ a b A)
      (ha : WellTyped (ε := ε) F Γ a A) (hb : WellTyped (ε := ε) F Γ b A) :
      Refines (ε := ε) F (@R) Γ (p.source a b) (p.target a b) A
  | uniformity {Γ : QCtx τ n} {Δ : QCtx τ m}
      {a b : Term Φ n} {c d : Term Φ m} {A B : τ} (p : Polarity)
      (rule : UniformityRule (ε := ε) F p Γ a b A Δ c d B)
      (hc : WellTyped (ε := ε) F Δ c B) (hd : WellTyped (ε := ε) F Δ d B)
      (square : Refines (ε := ε) F (@R) Γ (p.source a b) (p.target a b) A) :
      Refines (ε := ε) F (@R) Δ (p.source c d) (p.target c d) B
  | op {Γ : QCtx τ n} {a b : Term Φ n} {f : Φ}
      (h : Refines (ε := ε) F (@R) Γ a b (instrSrc f)) :
      Refines (ε := ε) F (@R) Γ (.op f a) (.op f b) (instrTrg f)
  | let₁ {Γ Γl Γr : QCtx τ n} {a a' : Term Φ n} {b b' : Term Φ (n + 1)} {A B : τ}
      (split : Γ.Split Γl Γr) (ha : Refines (ε := ε) F (@R) Γr a a' A)
      (hb : Refines (ε := ε) F (@R) (Γl.snoc A) b b' B) :
      Refines (ε := ε) F (@R) Γ (.let₁ a b) (.let₁ a' b') B
  | pair {Γ Γl Γr : QCtx τ n} {a a' b b' : Term Φ n} {A B : τ}
      (split : Γ.Split Γl Γr) (ha : Refines (ε := ε) F (@R) Γl a a' A) (hb : Refines (ε := ε) F (@R) Γr b b' B) :
      Refines (ε := ε) F (@R) Γ (.pair a b) (.pair a' b') (product A B)
  | let₂ {Γ Γl Γr : QCtx τ n} {a a' : Term Φ n} {b b' : Term Φ (n + 2)} {A B C : τ}
      (split : Γ.Split Γl Γr) (ha : Refines (ε := ε) F (@R) Γr a a' (product A B))
      (hb : Refines (ε := ε) F (@R) ((Γl.snoc A).snoc B) b b' C) :
      Refines (ε := ε) F (@R) Γ (.let₂ a b) (.let₂ a' b') C
  | inl {Γ : QCtx τ n} {a a' : Term Φ n} {A B : τ}
      (fragment : F.HasCase) (h : Refines (ε := ε) F (@R) Γ a a' A) :
      Refines (ε := ε) F (@R) Γ (.inl a) (.inl a') (coprod A B)
  | inr {Γ : QCtx τ n} {a a' : Term Φ n} {A B : τ}
      (fragment : F.HasCase) (h : Refines (ε := ε) F (@R) Γ a a' B) :
      Refines (ε := ε) F (@R) Γ (.inr a) (.inr a') (coprod A B)
  | case {Γ Γl Γr : QCtx τ n} {a a' : Term Φ n}
      {l l' r r' : Term Φ (n + 1)} {A B C : τ}
      (fragment : F.HasCase) (split : Γ.Split Γl Γr)
      (ha : Refines (ε := ε) F (@R) Γr a a' (coprod A B))
      (hl : Refines (ε := ε) F (@R) (Γl.snoc A) l l' C) (hr : Refines (ε := ε) F (@R) (Γl.snoc B) r r' C) :
      Refines (ε := ε) F (@R) Γ (.case a l r) (.case a' l' r') C
  | abort {Γ : QCtx τ n} {a a' : Term Φ n} {A : τ}
      (fragment : F.HasCase) (h : Refines (ε := ε) F (@R) Γ a a' Silmaril.empty) :
      Refines (ε := ε) F (@R) Γ (.abort a) (.abort a') A
  | iter {Γ Γl Γr : QCtx τ n} {a a' : Term Φ n} {b b' : Term Φ (n + 1)} {A B : τ}
      (fragment : F.HasIter) (split : Γ.Split Γl Γr) (unrestricted : Γl.linearity = ⊤)
      (ha : Refines (ε := ε) F (@R) Γr a a' A) (hb : Refines (ε := ε) F (@R) (Γl.snoc A) b b' (coprod B A)) :
      Refines (ε := ε) F (@R) Γ (.iter a b) (.iter a' b') B

namespace Refines

variable {F : Fragment} {R Q : Relation τ Φ}

/-- Every intermediate judgment is formed in the advertised quantitative fiber. -/
theorem wellTyped {Γ : QCtx τ n} {a b : Term Φ n} {A : τ}
    (h : Refines (ε := ε) F R Γ a b A) :
    WellTyped (ε := ε) F Γ a A ∧ WellTyped (ε := ε) F Γ b A := by
  induction h with
  | base _ ha hb => exact ⟨ha, hb⟩
  | refl h => exact ⟨h, h⟩
  | trans _ _ ih ik => exact ⟨ih.1, ik.2⟩
  | equation p _ ha hb | directional p _ ha hb => cases p <;> first | exact ⟨ha, hb⟩ | exact ⟨hb, ha⟩
  | uniformity p _ hc hd _ _ => cases p <;> first | exact ⟨hc, hd⟩ | exact ⟨hd, hc⟩
  | op _ ih =>
    obtain ⟨⟨ha⟩, ⟨hb⟩⟩ := ih
    exact ⟨⟨.op le_top ha⟩, ⟨.op le_top hb⟩⟩
  | let₁ s _ _ ih ik =>
    obtain ⟨⟨ha⟩, ⟨ha'⟩⟩ := ih
    obtain ⟨⟨hb⟩, ⟨hb'⟩⟩ := ik
    exact ⟨⟨.let₁ s ha hb⟩, ⟨.let₁ s ha' hb'⟩⟩
  | pair s _ _ ih ik =>
    obtain ⟨⟨ha⟩, ⟨ha'⟩⟩ := ih
    obtain ⟨⟨hb⟩, ⟨hb'⟩⟩ := ik
    exact ⟨⟨.pair s ha hb⟩, ⟨.pair s ha' hb'⟩⟩
  | let₂ s _ _ ih ik =>
    obtain ⟨⟨ha⟩, ⟨ha'⟩⟩ := ih
    obtain ⟨⟨hb⟩, ⟨hb'⟩⟩ := ik
    exact ⟨⟨.let₂ s ha hb⟩, ⟨.let₂ s ha' hb'⟩⟩
  | inl f _ ih =>
    obtain ⟨⟨ha⟩, ⟨hb⟩⟩ := ih
    exact ⟨⟨.inl f ha⟩, ⟨.inl f hb⟩⟩
  | inr f _ ih =>
    obtain ⟨⟨ha⟩, ⟨hb⟩⟩ := ih
    exact ⟨⟨.inr f ha⟩, ⟨.inr f hb⟩⟩
  | case f s _ _ _ ih il ir =>
    obtain ⟨⟨ha⟩, ⟨ha'⟩⟩ := ih
    obtain ⟨⟨hl⟩, ⟨hl'⟩⟩ := il
    obtain ⟨⟨hr⟩, ⟨hr'⟩⟩ := ir
    exact ⟨⟨.case f s ha hl hr⟩, ⟨.case f s ha' hl' hr'⟩⟩
  | abort f _ ih =>
    obtain ⟨⟨ha⟩, ⟨hb⟩⟩ := ih
    exact ⟨⟨.abort f ha⟩, ⟨.abort f hb⟩⟩
  | iter f s u _ _ ih ik =>
    obtain ⟨⟨ha⟩, ⟨ha'⟩⟩ := ih
    obtain ⟨⟨hb⟩, ⟨hb'⟩⟩ := ik
    exact ⟨⟨.iter f s u EffectSystem.iterable_top ha hb⟩,
      ⟨.iter f s u EffectSystem.iterable_top ha' hb'⟩⟩

/-- Replace each primitive rewrite by a derivation, preserving recursive rules. -/
theorem bind (hbase : ∀ {n} {Γ : QCtx τ n} {a b : Term Φ n} {A : τ},
      R Γ a b A → WellTyped (ε := ε) F Γ a A → WellTyped (ε := ε) F Γ b A →
        Refines (ε := ε) F Q Γ a b A)
    {Γ : QCtx τ n} {a b : Term Φ n} {A : τ}
    (h : Refines (ε := ε) F R Γ a b A) : Refines (ε := ε) F Q Γ a b A := by
  induction h with
  | base h ha hb => exact hbase h ha hb
  | refl h => exact .refl h
  | trans _ _ ih ik => exact .trans ih ik
  | equation p h ha hb => exact .equation p h ha hb
  | directional p h ha hb => exact .directional p h ha hb
  | uniformity p r hc hd _ ih => exact .uniformity p r hc hd ih
  | op _ ih => exact .op ih
  | let₁ s _ _ ih ik => exact .let₁ s ih ik
  | pair s _ _ ih ik => exact .pair s ih ik
  | let₂ s _ _ ih ik => exact .let₂ s ih ik
  | inl f _ ih => exact .inl f ih
  | inr f _ ih => exact .inr f ih
  | case f s _ _ _ ih il ir => exact .case f s ih il ir
  | abort f _ ih => exact .abort f ih
  | iter f s u _ _ ih ik => exact .iter f s u ih ik

/-- The theory constructor is monotone in the selected base rewrites. -/
theorem mono (hbase : ∀ {n} {Γ : QCtx τ n} {a b : Term Φ n} {A : τ},
      R Γ a b A → Q Γ a b A)
    {Γ : QCtx τ n} {a b : Term Φ n} {A : τ}
    (h : Refines (ε := ε) F R Γ a b A) : Refines (ε := ε) F Q Γ a b A :=
  h.bind fun h ha hb => .base (hbase h) ha hb

@[simp] theorem idempotent {Γ : QCtx τ n} {a b : Term Φ n} {A : τ} :
    Refines (ε := ε) F (Refines (ε := ε) F R) Γ a b A ↔ Refines (ε := ε) F R Γ a b A :=
  ⟨fun h => h.bind (fun h _ _ => h), fun h => .base h h.wellTyped.1 h.wellTyped.2⟩

end Refines

/-- Equations in the written theory are mutual refinement, not symmetric closure. -/
def Equates (F : Fragment) (R : Relation τ Φ) : Relation τ Φ :=
  fun Γ a b A => Refines (ε := ε) F R Γ a b A ∧ Refines (ε := ε) F R Γ b a A

namespace Equates

variable {F : Fragment} {R : Relation τ Φ}

theorem refl {Γ : QCtx τ n} {a : Term Φ n} {A : τ}
    (ha : WellTyped (ε := ε) F Γ a A) : Equates (ε := ε) F R Γ a a A :=
  ⟨.refl ha, .refl ha⟩

theorem symm {Γ : QCtx τ n} {a b : Term Φ n} {A : τ}
    (h : Equates (ε := ε) F R Γ a b A) : Equates (ε := ε) F R Γ b a A := ⟨h.2, h.1⟩

theorem trans {Γ : QCtx τ n} {a b c : Term Φ n} {A : τ}
    (h : Equates (ε := ε) F R Γ a b A) (k : Equates (ε := ε) F R Γ b c A) :
    Equates (ε := ε) F R Γ a c A := ⟨h.1.trans k.1, k.2.trans h.2⟩

/-- Every designated equation has both derivation directions. -/
theorem ofAxiom {Γ : QCtx τ n} {a b : Term Φ n} {A : τ}
    (h : EquationAxiom (ε := ε) F Γ a b A)
    (ha : WellTyped (ε := ε) F Γ a A) (hb : WellTyped (ε := ε) F Γ b A) :
    Equates (ε := ε) F R Γ a b A :=
  ⟨.equation .positive h ha hb, .equation .negative h ha hb⟩

end Equates
end Silmaril.Isotope.Refinement
