module

public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.RawTheory
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Typing

/-!
# Exact typed equational theory of LetSeq

Every step has well-typed endpoints. Raw axiom instances carry both endpoint
typings, so no typing assumption about ill-typed intermediate terms is hidden
in the equivalence closure. Each fragment has its own independent closure.
-/

@[expose] public section
set_option autoImplicit true

namespace Silmaril.Isotope.LetSeq.LocallyNameless

variable {τ : Type u} [HasProduct τ] [HasUnit τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]

/-- Typed congruence closure of the fragment's raw schemes. -/
inductive Equiv (pureEff : ε) (Γ : Isotope.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → Tm ν Φ n → τ → Prop where
  | refl (h : HasType Φ Γ β a A) : Equiv pureEff Γ β a a A
  | symm : Equiv pureEff Γ β a b A → Equiv pureEff Γ β b a A
  | trans : Equiv pureEff Γ β a b A → Equiv pureEff Γ β b c A → Equiv pureEff Γ β a c A
  | op : Equiv pureEff Γ β a a' (instrSrc f) →
      Equiv pureEff Γ β (.op f a) (.op f a') (instrTrg f)
  | let₁ (ha : Equiv pureEff Γ β a a' A)
      (hb : Equiv pureEff Γ (.snoc β A) b b' B) :
      Equiv pureEff Γ β (.let₁ a b) (.let₁ a' b') B
  | unit : Equiv pureEff Γ β .unit .unit Silmaril.unit
  | pair (ha : Equiv pureEff Γ β a a' A) (hb : Equiv pureEff Γ β b b' B) :
      Equiv pureEff Γ β (.pair a b) (.pair a' b') (Silmaril.product A B)
  | let₂ (he : Equiv pureEff Γ β e e' (Silmaril.product A B))
      (hc : Equiv pureEff Γ (.snoc (.snoc β A) B) c c' C) :
      Equiv pureEff Γ β (.let₂ e c) (.let₂ e' c') C
  | ax (hax : CoreAxiom pureEff a b)
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
      Equiv pureEff Γ β a b A

namespace Equiv

/-- Both endpoints of an equation have its advertised exact type. -/
theorem hasType {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ} (h : Equiv pureEff Γ β a b A) :
    HasType Φ Γ β a A ∧ HasType Φ Γ β b A := by
  induction h with
  | refl h => exact ⟨h, h⟩
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ⟨ih.1, ik.2⟩
  | op h ih => exact ⟨.op ih.1, .op ih.2⟩
  | let₁ ha hb iha ihb => exact ⟨.let₁ iha.1 ihb.1, .let₁ iha.2 ihb.2⟩
  | unit => exact ⟨.unit, .unit⟩
  | pair ha hb iha ihb => exact ⟨.pair iha.1 ihb.1, .pair iha.2 ihb.2⟩
  | let₂ ha hb iha ihb => exact ⟨.let₂ iha.1 ihb.1, .let₂ iha.2 ihb.2⟩
  | ax h ha hb => exact ⟨ha, hb⟩

/-- Reflexivity holds precisely on the advertised exact typing fiber. -/
@[simp] theorem refl_iff {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ} :
    Equiv pureEff Γ β a a A ↔ HasType Φ Γ β a A :=
  ⟨fun h => h.hasType.1, .refl⟩

/-- Typed equations forget to their type-erased raw equations. -/
theorem toRaw {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ} (h : Equiv pureEff Γ β a b A) : RawEquiv pureEff a b := by
  induction h with
  | refl h => exact .refl _
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik
  | op h ih => exact .op ih
  | let₁ ha hb iha ihb => exact .let₁ iha ihb
  | unit => exact .refl _
  | pair ha hb iha ihb => exact .pair iha ihb
  | let₂ ha hb iha ihb => exact .let₂ iha ihb
  | ax h ha hb => exact .ax h

end Equiv

/- Derived typed interfaces discharge the endpoint obligations of each raw scheme. -/
namespace Equiv

variable {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
variable {A B C D : τ} {f : Φ}

theorem letBeta (hp : Pure pureEff a) (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B) :
      Equiv pureEff Γ β (.let₁ a b) (Tm.instantiate b a) B := by
  exact .ax (.structural (.letBeta hp)) (.let₁ ha hb) (hb.instantiate ha)

theorem letEta {n} {β : BoundCtx τ n} {a : Tm ν Φ n} (ha : HasType Φ Γ β a A) :
      Equiv pureEff Γ β (.let₁ a (.bv 0)) a A := by
  exact .ax (.structural (.letEta _)) (.let₁ ha .bv) ha

theorem unitEta (ha : HasType Φ Γ β a Silmaril.unit) :
      Equiv pureEff Γ β (.let₁ a .unit) a Silmaril.unit := by
  exact .ax (.structural (.unitEta _)) (.let₁ ha .unit) ha

theorem pairBeta (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Equiv pureEff Γ β (.let₂ (.pair a b) c) (.let₁ a (.let₁ (Tm.lift b) c)) C := by
  exact .ax (.structural (.pairBeta _ _ _)) (.let₂ (.pair ha hb) hc)
    (.let₁ ha (.let₁ hb.lift hc))

theorem pairEta {n} {β : BoundCtx τ n} {a : Tm ν Φ n}
      (ha : HasType Φ Γ β a (Silmaril.product A B)) :
      Equiv pureEff Γ β (.let₂ a (.pair (.bv 1) (.bv 0))) a
        (Silmaril.product A B) := by
  exact .ax (.structural (.pairEta _)) (.let₂ ha (.pair .bv .bv)) ha

theorem bindOp {n} {β : BoundCtx τ n} {a : Tm ν Φ n} {c : Tm ν Φ (n + 1)}
      (ha : HasType Φ Γ β a (Silmaril.instrSrc f))
      (hc : HasType Φ Γ (.snoc β (Silmaril.instrTrg f)) c C) :
      Equiv pureEff Γ β (.let₁ (.op f a) c)
        (.let₁ a (.let₁ (.op f (.bv 0)) (Tm.underBinder c))) C := by
  exact .ax (.sequencing (.bindOp _ _)) (.let₁ (.op ha) hc)
    (.let₁ ha (.let₁ (.op .bv) hc.underBinder))

theorem bindLet (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
      (hc : HasType Φ Γ (.snoc β B) c C) :
      Equiv pureEff Γ β (.let₁ (.let₁ a b) c)
        (.let₁ a (.let₁ b (Tm.underBinder c))) C := by
  exact .ax (.sequencing (.bindLet _ _ _)) (.let₁ (.let₁ ha hb) hc)
    (.let₁ ha (.let₁ hb hc.underBinder))

theorem bindLetPair (he : HasType Φ Γ β e (Silmaril.product A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
      (hd : HasType Φ Γ (.snoc β C) d D) :
      Equiv pureEff Γ β (.let₁ (.let₂ e c) d)
        (.let₂ e (.let₁ c (Tm.underBinder (Tm.underBinder d)))) D := by
  exact .ax (.sequencing (.bindLetPair _ _ _)) (.let₁ (.let₂ he hc) hd)
    (.let₂ he (.let₁ hc hd.underBinder.underBinder))

theorem bindPair {n} {β : BoundCtx τ n} {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)}
      (ha : HasType Φ Γ β a (Silmaril.product A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Equiv pureEff Γ β (.let₂ a c)
        (.let₁ a (.let₂ (.bv 0) (Tm.underTwoBinders c))) C := by
  exact .ax (.sequencing (.bindPair _ _)) (.let₂ ha hc)
    (.let₁ ha (.let₂ .bv hc.underTwoBinders))

end Equiv

end Silmaril.Isotope.LetSeq.LocallyNameless
