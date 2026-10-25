module

public import Silmaril.Logic.HOLLight.Classical

@[expose] public section

/-!
# Excluded middle from Hilbert choice

Diaconescu's argument is carried out in the object calculus: the choice terms
for `{false} ∪ {x | p}` and `{true} ∪ {x | p}` coincide when `p` holds. Their
membership properties then give either `p` or its negation. No semantic
completeness assumption or additional inference rule is used.
-/

namespace Silmaril.Logic.HOLLight
namespace Derives

private def choiceBody (a p : Tm) : Tm :=
  Tm.disj (Tm.equal .bool (.bvar 0) a.weaken) p.weaken

private def choicePredicate (a p : Tm) : Tm := .lam .bool (choiceBody a p)

private def choicePoint (a p : Tm) : Tm := Tm.select .bool (choicePredicate a p)

private theorem choiceBodyTyping {sig : Signature} {a p : Tm}
    (ha : HasType sig [] a .bool) (hp : HasType sig [] p .bool) :
    HasType sig [.bool] (choiceBody a p) .bool :=
  (HasType.equal (by trivial) (.bvar rfl (by trivial)) (ha.weaken .bool)).disj (hp.weaken .bool)

private theorem choicePredicateTyping {sig : Signature} {a p : Tm}
    (ha : HasType sig [] a .bool) (hp : HasType sig [] p .bool) :
    HasType sig [] (choicePredicate a p) (.arr .bool .bool) :=
  .lam (by trivial) (choiceBodyTyping ha hp)

private theorem choicePointTyping {sig : Signature} {a p : Tm}
    (ha : HasType sig [] a .bool) (hp : HasType sig [] p .bool) :
    HasType sig [] (choicePoint a p) .bool :=
  .select (by trivial) (choicePredicateTyping ha hp)

private theorem choiceBody_open (a p value : Tm) :
    (choiceBody a p).open value = Tm.disj (Tm.equal .bool value a) p := by
  have hw (t : Tm) : t.weaken.subst (Tm.openSub value) = t := Tm.open_weaken t value
  simp only [choiceBody, Tm.«open», Tm.subst_disj, Tm.subst_equal, Tm.subst,
    Tm.openSub, hw]

private theorem choicePredicateBeta {sig : Signature} {a p value : Tm}
    (ha : HasType sig [] a .bool) (hp : HasType sig [] p .bool)
    (hv : HasType sig [] value .bool) : Derives sig classicalTheory ∅
      (Tm.equal .bool (.app (choicePredicate a p) value)
        (Tm.disj (Tm.equal .bool value a) p)) := by
  simpa only [choicePredicate, choiceBody_open] using generalBeta (choiceBodyTyping ha hp) hv

private theorem choiceMembership {sig : Signature} {a p : Tm}
    (ha : HasType sig [] a .bool) (hp : HasType sig [] p .bool) :
    Derives sig classicalTheory ∅ (Tm.disj (Tm.equal .bool (choicePoint a p) a) p) := by
  have self : Derives sig classicalTheory ∅ (Tm.disj (Tm.equal .bool a a) p) :=
    (Derives.refl ha).disjIntroLeft hp
  have member : Derives sig classicalTheory ∅ (.app (choicePredicate a p) a) := by
    simpa only [Finset.union_self] using (choicePredicateBeta ha hp ha).symm.eqMp self
  have selected := impElim (.app (choicePredicateTyping ha hp) (choicePointTyping ha hp))
    (selection (by trivial) (choicePredicateTyping ha hp) ha) member
  simpa only [Finset.union_empty, Finset.empty_union] using
    (choicePredicateBeta ha hp (choicePointTyping ha hp)).eqMp selected

private theorem typedInsert {sig : Signature} {H : Hyps} {p : Tm}
    (hH : TypedHyps sig [] H) (hp : HasType sig [] p .bool) :
    TypedHyps sig [] (insert p H) := by
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact hp
  · exact hH t ht

private theorem liftEmpty {sig : Signature} {H : Hyps} {p : Tm}
    (hH : TypedHyps sig [] H) (proof : Derives sig classicalTheory ∅ p) :
    Derives sig classicalTheory H p := proof.weaken (Finset.empty_subset _) hH

private theorem choicesEqual {sig : Signature} {p : Tm} (hp : HasType sig [] p .bool) :
    Derives sig classicalTheory {p}
      (Tm.equal .bool (choicePoint Tm.falsity p) (choicePoint Tm.truth p)) := by
  let s := choiceBody Tm.falsity p
  let t := choiceBody Tm.truth p
  let n := Tm.freshName [s, t, p]
  have hs : s.Fresh (n, .bool) := Tm.freshName_fresh _ (by simp) _
  have ht : t.Fresh (n, .bool) := Tm.freshName_fresh _ (by simp) _
  have hH : ∀ q ∈ ({p} : Hyps), q.Fresh (n, .bool) := by
    intro q hq
    have same := Finset.mem_singleton.mp hq
    subst q
    exact Tm.freshName_fresh _ (by simp) _
  have hx : HasType sig [] (.fvar n .bool) .bool := .fvar n (by trivial)
  have left : Derives sig classicalTheory {p}
      (Tm.disj (Tm.equal .bool (.fvar n .bool) Tm.falsity) p) :=
    disjIntroRight (.equal (by trivial) hx HasType.falsity) (Derives.assume hp)
  have right : Derives sig classicalTheory {p}
      (Tm.disj (Tm.equal .bool (.fvar n .bool) Tm.truth) p) :=
    disjIntroRight (.equal (by trivial) hx HasType.truth) (Derives.assume hp)
  have equality := left.eqTrueIntro.transSame right.eqTrueIntro.symm
  have opened : Derives sig classicalTheory {p}
      (Tm.equal .bool (s.open (.fvar n .bool)) (t.open (.fvar n .bool))) := by
    simpa only [s, t, choiceBody_open] using equality
  have predicates := absOpen n (by trivial) (choiceBodyTyping HasType.falsity hp)
    (choiceBodyTyping HasType.truth hp) hs ht hH opened
  have hselect : HasType sig [] (.const (.select .bool)) (.arr (.arr .bool .bool) .bool) :=
    .const (.select (by trivial))
  simpa only [Finset.empty_union, choicePoint, choicePredicate, Tm.select] using
    (Derives.refl hselect).mkComb predicates

/-- Object-level excluded middle is derivable from the selection axiom. -/
theorem excludedMiddle {sig : Signature} {p : Tm} (hp : HasType sig [] p .bool) :
    Derives sig classicalTheory ∅ (Tm.disj p (Tm.neg p)) := by
  let a := choicePoint Tm.falsity p
  let b := choicePoint Tm.truth p
  let q := Tm.equal .bool a Tm.falsity
  let r := Tm.equal .bool b Tm.truth
  let result := Tm.disj p (Tm.neg p)
  have ha : HasType sig [] a .bool := choicePointTyping HasType.falsity hp
  have hb : HasType sig [] b .bool := choicePointTyping HasType.truth hp
  have hq : HasType sig [] q .bool := .equal (by trivial) ha HasType.falsity
  have hr : HasType sig [] r .bool := .equal (by trivial) hb HasType.truth
  have hn : HasType sig [] (Tm.neg p) .bool := hp.neg
  have hresult : HasType sig [] result .bool := hp.disj hn
  have h₀ : TypedHyps sig [] (∅ : Hyps) := by intro t ht; simp at ht
  have hqH := typedInsert h₀ hq
  have hrqH := typedInsert hqH hr
  have hprqH := typedInsert hrqH hp
  have same : Derives sig classicalTheory (insert p (insert r (insert q ∅)))
      (Tm.equal .bool a b) :=
    (choicesEqual hp).weaken (by intro t ht; have same := Finset.mem_singleton.mp ht; subst t; simp)
      hprqH
  have eqFalse : Derives sig classicalTheory (insert p (insert r (insert q ∅))) q :=
    assumeIn hprqH (by simp)
  have eqTrue : Derives sig classicalTheory (insert p (insert r (insert q ∅))) r :=
    assumeIn hprqH (by simp)
  have contradiction : Derives sig classicalTheory (insert p (insert r (insert q ∅)))
      Tm.falsity := by
    have impossible := eqFalse.symm.transSame same |>.transSame eqTrue
    exact impossible.symm.eqMpSame (liftEmpty hprqH truth)
  have negative : Derives sig classicalTheory (insert r (insert q ∅)) (Tm.neg p) :=
    impIntro hp contradiction
  have both : Derives sig classicalTheory (insert r (insert q ∅)) result :=
    disjIntroRight hp negative
  have fromP {K : Hyps} (hK : TypedHyps sig [] K) (hmem : p ∈ K) :
      Derives sig classicalTheory K result := (assumeIn hK hmem).disjIntroLeft hn
  have ifFalse : Derives sig classicalTheory (insert q ∅) result :=
    disjElim hr hp hresult (liftEmpty hqH (choiceMembership HasType.truth hp)) both
      (fromP (typedInsert hqH hp) (by simp))
  exact disjElim hq hp hresult (choiceMembership HasType.falsity hp) ifFalse
    (fromP (typedInsert h₀ hp) (by simp))

end Derives
end Silmaril.Logic.HOLLight
