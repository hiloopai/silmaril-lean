module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.RawTheory
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Structural

/-!
# Exact typed equational theory of LetIter

Every step has well-typed endpoints. Raw axiom instances carry both endpoint
typings, so no typing assumption about ill-typed intermediate terms is hidden
in the equivalence closure. Each fragment has its own independent closure.
-/

@[expose] public section
set_option autoImplicit true

namespace Silmaril.Isotope.LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ]
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
  | inl (h : Equiv pureEff Γ β a a' A) :
      Equiv pureEff Γ β (.inl a) (.inl a') (Silmaril.coprod A B)
  | inr (h : Equiv pureEff Γ β b b' B) :
      Equiv pureEff Γ β (.inr b) (.inr b') (Silmaril.coprod A B)
  | case (he : Equiv pureEff Γ β e e' (Silmaril.coprod A B))
      (hl : Equiv pureEff Γ (.snoc β A) l l' C)
      (hr : Equiv pureEff Γ (.snoc β B) r r' C) :
      Equiv pureEff Γ β (.case e l r) (.case e' l' r') C
  | abort (h : Equiv pureEff Γ β a a' Silmaril.empty) :
      Equiv pureEff Γ β (.abort a) (.abort a') C
  | iter (ha : Equiv pureEff Γ β a a' A)
      (hb : Equiv pureEff Γ (.snoc β A) b b' (Silmaril.coprod B A)) :
      Equiv pureEff Γ β (.iter a b) (.iter a' b') B
  | ax (hax : CoreAxiom pureEff a b)
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
      Equiv pureEff Γ β a b A
  | uniformity {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)}
      (ha : HasType Φ Γ β a A)
      (hh : HasType Φ Γ (.snoc β A) h A') (hp : Pure pureEff h)
      (hb : HasType Φ Γ (.snoc β A) b (Silmaril.coprod B A))
      (hb' : HasType Φ Γ (.snoc β A') b' (Silmaril.coprod B A'))
      (square : Equiv pureEff Γ (.snoc β A)
        (.case b (.inl (.bv (0 : Fin (n + 2))))
          (.inr (Tm.underBinder h)))
        (Tm.instantiate
          (Tm.underBinder b') h)
        (Silmaril.coprod B A')) :
      Equiv pureEff Γ β (.iter a b) (.iter (.let₁ a h) b') B

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
  | inl h ih => exact ⟨.inl ih.1, .inl ih.2⟩
  | inr h ih => exact ⟨.inr ih.1, .inr ih.2⟩
  | case he hl hr ihe ihl ihr => exact ⟨.case ihe.1 ihl.1 ihr.1, .case ihe.2 ihl.2 ihr.2⟩
  | abort h ih => exact ⟨.abort ih.1, .abort ih.2⟩
  | iter ha hb iha ihb => exact ⟨.iter iha.1 ihb.1, .iter iha.2 ihb.2⟩
  | uniformity ha hh hp hb hb' square ih => exact ⟨.iter ha hb, .iter (.let₁ ha hh) hb'⟩

/-- Reflexivity holds precisely on the advertised exact typing fiber. -/
@[simp] theorem refl_iff {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ} :
    Equiv pureEff Γ β a a A ↔ HasType Φ Γ β a A :=
  ⟨fun h => h.hasType.1, .refl⟩

/-- Typed equations forget to raw equations, including the uniformity square. -/
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
  | inl h ih => exact .inl ih
  | inr h ih => exact .inr ih
  | case he hl hr ihe ihl ihr => exact .case ihe ihl ihr
  | abort h ih => exact .abort ih
  | iter ha hb iha ihb => exact .iter iha ihb
  | uniformity ha hh hp hb hb' square ih => exact .uniformity hp ih

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

theorem caseBetaL (he : HasType Φ Γ β e A) (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Equiv pureEff Γ β (.case (.inl e) l r) (.let₁ e l) C := by
  exact .ax (.structural (.caseBetaL _ _ _)) (.case (.inl he) hl hr) (.let₁ he hl)

theorem caseBetaR (he : HasType Φ Γ β e B) (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) :
      Equiv pureEff Γ β (.case (.inr e) l r) (.let₁ e r) C := by
  exact .ax (.structural (.caseBetaR _ _ _)) (.case (.inr he) hl hr) (.let₁ he hr)

theorem caseEta {n} {β : BoundCtx τ n} {e : Tm ν Φ n}
      (he : HasType Φ Γ β e (Silmaril.coprod A B)) :
      Equiv pureEff Γ β (.case e (.inl (.bv 0)) (.inr (.bv 0))) e
        (Silmaril.coprod A B) := by
  exact .ax (.structural (.caseEta _)) (.case he (.inl .bv) (.inr .bv)) he

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

theorem bindLetCase (he : HasType Φ Γ β e (Silmaril.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C)
      (hd : HasType Φ Γ (.snoc β C) d D) :
      Equiv pureEff Γ β (.let₁ (.case e l r) d)
        (.case e (.let₁ l (Tm.underBinder d)) (.let₁ r (Tm.underBinder d))) D := by
  exact .ax (.sequencing (.bindLetCase _ _ _ _)) (.let₁ (.case he hl hr) hd)
    (.case he (.let₁ hl hd.underBinder) (.let₁ hr hd.underBinder))

theorem bindPair {n} {β : BoundCtx τ n} {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)}
      (ha : HasType Φ Γ β a (Silmaril.product A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
      Equiv pureEff Γ β (.let₂ a c)
        (.let₁ a (.let₂ (.bv 0) (Tm.underTwoBinders c))) C := by
  exact .ax (.sequencing (.bindPair _ _)) (.let₂ ha hc)
    (.let₁ ha (.let₂ .bv hc.underTwoBinders))

theorem bindCase {n} {β : BoundCtx τ n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
      (he : HasType Φ Γ β e (Silmaril.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C) :
      Equiv pureEff Γ β (.case e l r)
        (.let₁ e (.case (.bv 0) (Tm.underBinder l) (Tm.underBinder r))) C := by
  exact .ax (.sequencing (.bindCase _ _ _)) (.case he hl hr)
    (.let₁ he (.case .bv hl.underBinder hr.underBinder))

theorem emptyInitial (ha : HasType Φ Γ β a Silmaril.empty)
      (hb : HasType Φ Γ (.snoc β A) b B) (hc : HasType Φ Γ (.snoc β A) c B) :
      Equiv pureEff Γ β (.let₁ (.abort a) b) (.let₁ (.abort a) c) B := by
  exact .ax (.structural (.emptyInitial _ _ _)) (.let₁ (.abort ha) hb)
    (.let₁ (.abort ha) hc)

/-- Unfold one iteration step. -/
theorem fixpoint {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b (coprod B A)) :
    Equiv pureEff Γ β (.iter a b)
      (.let₁ a (.case b (.bv 0) (.iter (.bv 0) (Tm.underBinder (Tm.underBinder b))))) B := by
  exact .ax (.iteration (.fixpoint _ _)) (.iter ha hb)
    (.let₁ ha (.case hb .bv (.iter .bv hb.underBinder.underBinder)))

/-- Postcomposition commutes with iteration. -/
theorem naturality {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b (coprod B A))
    (hc : HasType Φ Γ (.snoc β B) c C) :
    Equiv pureEff Γ β (.let₁ (.iter a b) c)
      (.iter a (.case b (.inl (Tm.underBinder c)) (.inr (.bv 0)))) C := by
  exact .ax (.iteration (.naturality _ _ _)) (.let₁ (.iter ha hb) hc)
    (.iter ha (.case hb (.inl hc.underBinder) (.inr .bv)))

/-- Nested iterations combine by codiagonal. -/
theorem codiagonal {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (coprod (coprod B A) A)) :
    Equiv pureEff Γ β (.iter a (.iter (.bv 0) (Tm.underBinder b)))
      (.iter a (.case b (.bv 0) (.inr (.bv 0)))) B := by
  exact .ax (.iteration (.codiagonal _ _)) (.iter ha (.iter .bv hb.underBinder))
    (.iter ha (.case hb .bv (.inr .bv)))

/-- Evaluate the initializer before entering the loop. -/
theorem iterBind {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b (coprod B A)) :
    Equiv pureEff Γ β (.iter a b) (.let₁ a (.iter (.bv 0) (Tm.underBinder b))) B := by
  exact .ax (.iteration (.iterBind _ _)) (.iter ha hb)
    (.let₁ ha (.iter .bv hb.underBinder))

end Equiv

end Silmaril.Isotope.LetIter.LocallyNameless
