module

public import Silmaril.Logic.HOLLight.Kernel.Structural

@[expose] public section

/-!
# Derived logical rules

These results construct derivations in the primitive HOL kernel. The logical
vocabulary in `Logic` consists entirely of expanded equality/lambda terms.
-/

namespace Silmaril.Logic.HOLLight
namespace Derives

variable {sig : Signature} {theory : Theory} {H K : Hyps}
variable {A B : Ty} {p q P x f : Tm}

theorem truth : Derives sig theory ∅ Tm.truth :=
  .refl (HasType.identity (by simp [Ty.WellFormed]))

theorem eqTrueIntro (proof : Derives sig theory H p) :
    Derives sig theory H (Tm.equal .bool p Tm.truth) := by
  have d := proof.deductAntisym (truth (sig := sig) (theory := theory))
  apply d.weaken _ proof.typedHyps
  intro t ht
  exact Finset.mem_of_mem_erase (show t ∈ H.erase Tm.truth from (by simpa using ht))

theorem eqTrueElim (proof : Derives sig theory H (Tm.equal .bool p Tm.truth)) :
    Derives sig theory H p := by
  simpa only [Finset.union_empty] using proof.symm.eqMp (truth (sig := sig) (theory := theory))

theorem transSame {C : Ty} {s t r : Tm}
    (left : Derives sig theory H (Tm.equal C s t))
    (right : Derives sig theory H (Tm.equal C t r)) :
    Derives sig theory H (Tm.equal C s r) := by
  simpa only [Finset.union_self] using left.trans right

theorem eqMpSame (eqn : Derives sig theory H (Tm.equal .bool p q))
    (proof : Derives sig theory H p) : Derives sig theory H q := by
  simpa only [Finset.union_self] using eqn.eqMp proof

theorem conjIntroSame (left : Derives sig theory H p) (right : Derives sig theory H q) :
    Derives sig theory H (Tm.conj p q) := by
  let C := Ty.arr .bool (.arr .bool .bool)
  have hC : C.WellFormed sig.tyOps := by simp [C, Ty.WellFormed]
  let n := Tm.freshName (H.toList ++ [p, q])
  have hp : p.Fresh (n, C) := Tm.freshName_fresh _ (by simp) C
  have hq : q.Fresh (n, C) := Tm.freshName_fresh _ (by simp) C
  have hH : ∀ t ∈ H, t.Fresh (n, C) := by
    intro t ht
    exact Tm.freshName_fresh _ (by simp [ht]) C
  have hf : HasType sig [] (.fvar n C) C := .fvar n hC
  have eqn := ((Derives.refl (theory := theory) hf).mkComb left.eqTrueIntro).mkComb right.eqTrueIntro
  have eqn' : Derives sig theory H
      (Tm.equal .bool (.app (.app (.fvar n C) p) q)
        (.app (.app (.fvar n C) Tm.truth) Tm.truth)) := by
    simpa only [Finset.empty_union, Finset.union_self] using eqn
  have abstracted := eqn'.abs n hC hH
  change Derives sig theory H (Tm.equal (.arr C .bool)
    (.lam C (.app (.app ((Tm.fvar n C).replaceFree (n, C) (.bvar 0))
      (p.replaceFree (n, C) (.bvar 0))) (q.replaceFree (n, C) (.bvar 0))))
    (.lam C (.app (.app ((Tm.fvar n C).replaceFree (n, C) (.bvar 0))
      (Tm.truth.replaceFree (n, C) (.bvar 0))) (Tm.truth.replaceFree (n, C) (.bvar 0))))) at abstracted
  rw [Tm.replaceFree_self, Tm.replaceFree_of_fresh hp, Tm.replaceFree_of_fresh hq] at abstracted
  simpa only [Tm.conj, Tm.Closed.weaken_eq left.typing.scope, Tm.Closed.weaken_eq right.typing.scope,
    Tm.replaceFree, Tm.freeSubst_truth, C] using abstracted

theorem conjIntro (left : Derives sig theory H p) (right : Derives sig theory K q) :
    Derives sig theory (H ∪ K) (Tm.conj p q) := by
  apply conjIntroSame (left.unionHyps right.typedHyps)
  simpa only [Finset.union_comm] using right.unionHyps left.typedHyps

private theorem subst_openSub_weaken (t value : Tm) :
    t.weaken.subst (Tm.openSub value) = t := Tm.open_weaken t value

private theorem applyConj (hp : HasType sig [] p .bool) (hq : HasType sig [] q .bool)
    (hf : HasType sig [] f (.arr .bool (.arr .bool .bool)))
    (proof : Derives sig theory H (Tm.conj p q)) :
    Derives sig theory H
      (Tm.equal .bool (.app (.app f p) q) (.app (.app f Tm.truth) Tm.truth)) := by
  have hC : (Ty.arr .bool (.arr .bool .bool)).WellFormed sig.tyOps := by trivial
  have left := generalBeta (theory := theory)
    (HasType.app (.app (.bvar (i := 0) rfl hC) (hp.weaken _)) (hq.weaken _)) hf
  have right := generalBeta (theory := theory)
    (HasType.app (.app (.bvar (i := 0) rfl hC) HasType.truth) HasType.truth) hf
  have applied := proof.mkComb (Derives.refl hf)
  have result := left.symm.trans applied |>.trans right
  simpa only [Tm.conj, Tm.«open», Tm.subst, Tm.openSub,
    subst_openSub_weaken, Tm.subst_truth, Finset.empty_union, Finset.union_empty] using result

private def firstBool : Tm := .lam .bool (.lam .bool (.bvar 1))
private def secondBool : Tm := .lam .bool (.lam .bool (.bvar 0))

private theorem firstBool_typing :
    HasType sig [] firstBool (.arr .bool (.arr .bool .bool)) :=
  .lam (by trivial) (.lam (by trivial) (.bvar rfl (by trivial)))

private theorem secondBool_typing :
    HasType sig [] secondBool (.arr .bool (.arr .bool .bool)) :=
  .lam (by trivial) (.lam (by trivial) (.bvar rfl (by trivial)))

private theorem firstBool_beta (hp : HasType sig [] p .bool) (hq : HasType sig [] q .bool) :
    Derives sig theory ∅ (Tm.equal .bool (.app (.app firstBool p) q) p) := by
  have first := generalBeta (theory := theory)
    (HasType.lam (Γ := [Ty.bool]) (A := .bool) (by trivial) (.bvar (i := 1) rfl (by trivial))) hp
  have second := generalBeta (theory := theory) (hp.weaken .bool) hq
  have result := (first.mkComb (Derives.refl hq)).trans second
  simpa only [firstBool, Tm.«open», Tm.subst, Tm.liftSub, Tm.openSub,
    subst_openSub_weaken, Finset.union_self] using result

private theorem secondBool_beta (hp : HasType sig [] p .bool) (hq : HasType sig [] q .bool) :
    Derives sig theory ∅ (Tm.equal .bool (.app (.app secondBool p) q) q) := by
  have first := generalBeta (theory := theory)
    (HasType.lam (Γ := [Ty.bool]) (A := .bool) (by trivial) (.bvar (i := 0) rfl (by trivial))) hp
  have second := generalBeta (theory := theory)
    (HasType.bvar (Γ := [Ty.bool]) (i := 0) (A := .bool) rfl (by trivial)) hq
  have result := (first.mkComb (Derives.refl hq)).trans second
  simpa only [secondBool, Tm.«open», Tm.subst, Tm.liftSub, Tm.openSub,
    Finset.union_self] using result

theorem conjElimLeft (hp : HasType sig [] p .bool) (hq : HasType sig [] q .bool)
    (proof : Derives sig theory H (Tm.conj p q)) : Derives sig theory H p := by
  have middle := applyConj hp hq firstBool_typing proof
  have result := (firstBool_beta hp hq).symm.trans middle
    |>.trans (firstBool_beta (sig := sig) HasType.truth HasType.truth)
  apply eqTrueElim
  simpa only [Finset.empty_union, Finset.union_empty] using result

theorem conjElimRight (hp : HasType sig [] p .bool) (hq : HasType sig [] q .bool)
    (proof : Derives sig theory H (Tm.conj p q)) : Derives sig theory H q := by
  have middle := applyConj hp hq secondBool_typing proof
  have result := (secondBool_beta hp hq).symm.trans middle
    |>.trans (secondBool_beta (sig := sig) HasType.truth HasType.truth)
  apply eqTrueElim
  simpa only [Finset.empty_union, Finset.union_empty] using result

theorem assumeIn (typed : TypedHyps sig [] H) (member : p ∈ H) :
    Derives sig theory H p :=
  (Derives.assume (typed p member)).weaken (Finset.singleton_subset_iff.mpr member) typed

private theorem typedInsert (hH : TypedHyps sig [] H) (hp : HasType sig [] p .bool) :
    TypedHyps sig [] (insert p H) := by
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact hp
  · exact hH t ht

theorem impIntro (hp : HasType sig [] p .bool)
    (proof : Derives sig theory (insert p H) q) : Derives sig theory H (Tm.imp p q) := by
  have hp' : Derives sig theory (insert p H) p :=
    assumeIn proof.typedHyps (Finset.mem_insert_self _ _)
  have left := conjIntroSame hp' proof
  have right := conjElimLeft (theory := theory) hp proof.typing (Derives.assume (hp.conj proof.typing))
  have result := left.deductAntisym right
  apply result.weaken _ (fun t ht => proof.typedHyps t (Finset.mem_insert_of_mem ht))
  intro t ht
  have ht' : t ∈ (insert p H).erase p := by simpa using ht
  rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase ht') with rfl | ht
  · simp at ht'
  · exact ht

theorem impElim (hq : HasType sig [] q .bool)
    (implication : Derives sig theory H (Tm.imp p q))
    (argument : Derives sig theory K p) : Derives sig theory (H ∪ K) q :=
  conjElimRight argument.typing hq (implication.symm.eqMp argument)

theorem impElimSame (hq : HasType sig [] q .bool)
    (implication : Derives sig theory H (Tm.imp p q))
    (argument : Derives sig theory H p) : Derives sig theory H q := by
  simpa only [Finset.union_self] using impElim hq implication argument

theorem allElim (hx : HasType sig [] x A)
    (proof : Derives sig theory H (Tm.all A P)) : Derives sig theory H (.app P x) := by
  have applied := proof.mkComb (Derives.refl hx)
  have beta := generalBeta (theory := theory) (HasType.truth (Γ := [A])) hx
  have result := applied.trans beta
  apply eqTrueElim
  simpa only [Tm.all, Tm.«open», Tm.subst_truth, Finset.union_empty] using result

/-- Generalize an opened body at a fresh free name. -/
theorem allIntroFresh {body : Tm} (hA : A.WellFormed sig.tyOps)
    (hb : HasType sig [A] body .bool) (name : Nat)
    (freshBody : body.Fresh (name, A)) (freshHyps : ∀ t ∈ H, t.Fresh (name, A))
    (proof : Derives sig theory H (body.open (.fvar name A))) :
    Derives sig theory H (Tm.all A (.lam A body)) := by
  apply absOpen name hA hb HasType.truth freshBody
    (by simp [Tm.Fresh]) freshHyps
  simpa only [Tm.«open», Tm.subst_truth] using proof.eqTrueIntro

/-- A convenient fresh-name-independent formulation of universal introduction. -/
theorem allIntro {body : Tm} (hA : A.WellFormed sig.tyOps)
    (hb : HasType sig [A] body .bool)
    (proof : ∀ n, body.Fresh (n, A) → (∀ t ∈ H, t.Fresh (n, A)) →
      Derives sig theory H (body.open (.fvar n A))) :
    Derives sig theory H (Tm.all A (.lam A body)) := by
  let n := Tm.freshName (body :: H.toList)
  have hb' : body.Fresh (n, A) := Tm.freshName_fresh _ (by simp) A
  have hH : ∀ t ∈ H, t.Fresh (n, A) := by
    intro t ht
    exact Tm.freshName_fresh _ (by simp [ht]) A
  exact allIntroFresh hA hb n hb' hH (proof n hb' hH)

theorem falsityElim (hp : HasType sig [] p .bool)
    (proof : Derives sig theory H Tm.falsity) : Derives sig theory H p := by
  have applied := allElim hp proof
  have beta := generalBeta (theory := theory)
    (HasType.bvar (Γ := [Ty.bool]) (i := 0) (A := .bool) rfl (by trivial)) hp
  simpa only [Tm.identity, Tm.«open», Tm.subst, Tm.openSub, Finset.empty_union] using beta.eqMp applied

private theorem disjBodyTyping (hp : HasType sig [] p .bool) (hq : HasType sig [] q .bool) :
    HasType sig [Ty.bool]
      (Tm.imp (Tm.imp p.weaken (.bvar 0)) (Tm.imp (Tm.imp q.weaken (.bvar 0)) (.bvar 0))) .bool :=
  ((hp.weaken .bool).imp (.bvar rfl (by trivial))).imp
    (((hq.weaken .bool).imp (.bvar rfl (by trivial))).imp (.bvar rfl (by trivial)))

theorem disjIntroLeft (proof : Derives sig theory H p) (hq : HasType sig [] q .bool) :
    Derives sig theory H (Tm.disj p q) := by
  apply allIntro (by trivial) (disjBodyTyping proof.typing hq)
  intro n _ _
  let r := Tm.fvar n .bool
  have hr : HasType sig [] r .bool := .fvar n (by trivial)
  have hpr := proof.typing.imp hr
  have hqr := hq.imp hr
  let K := insert (Tm.imp q r) (insert (Tm.imp p r) H)
  have hK : TypedHyps sig [] K := typedInsert (typedInsert proof.typedHyps hpr) hqr
  have hp : Derives sig theory K p := proof.weaken (by intro t ht; simp [K, ht]) hK
  have hi : Derives sig theory K (Tm.imp p r) := assumeIn hK (by simp [K])
  have result := impIntro hpr (impIntro hqr (impElimSame hr hi hp))
  simpa only [Tm.«open», Tm.subst_imp, Tm.subst, Tm.openSub, subst_openSub_weaken] using result

theorem disjIntroRight (hp : HasType sig [] p .bool) (proof : Derives sig theory H q) :
    Derives sig theory H (Tm.disj p q) := by
  apply allIntro (by trivial) (disjBodyTyping hp proof.typing)
  intro n _ _
  let r := Tm.fvar n .bool
  have hr : HasType sig [] r .bool := .fvar n (by trivial)
  have hpr := hp.imp hr
  have hqr := proof.typing.imp hr
  let K := insert (Tm.imp q r) (insert (Tm.imp p r) H)
  have hK : TypedHyps sig [] K := typedInsert (typedInsert proof.typedHyps hpr) hqr
  have hq : Derives sig theory K q := proof.weaken (by intro t ht; simp [K, ht]) hK
  have hi : Derives sig theory K (Tm.imp q r) := assumeIn hK (by simp [K])
  have result := impIntro hpr (impIntro hqr (impElimSame hr hi hq))
  simpa only [Tm.«open», Tm.subst_imp, Tm.subst, Tm.openSub, subst_openSub_weaken] using result

theorem disjElim {r : Tm} (hp : HasType sig [] p .bool) (hq : HasType sig [] q .bool)
    (hr : HasType sig [] r .bool) (proof : Derives sig theory H (Tm.disj p q))
    (left : Derives sig theory (insert p H) r)
    (right : Derives sig theory (insert q H) r) : Derives sig theory H r := by
  have applied := allElim hr proof
  have beta := generalBeta (theory := theory) (disjBodyTyping hp hq) hr
  have implication : Derives sig theory H
      (Tm.imp (Tm.imp p r) (Tm.imp (Tm.imp q r) r)) := by
    simpa only [Tm.«open», Tm.subst_imp, Tm.subst, Tm.openSub,
      subst_openSub_weaken, Finset.empty_union] using beta.eqMp applied
  exact impElimSame hr (impElimSame ((hq.imp hr).imp hr) implication (impIntro hp left))
    (impIntro hq right)

private theorem exBodyTyping (hA : A.WellFormed sig.tyOps)
    (hP : HasType sig [] P (.arr A .bool)) :
    HasType sig [Ty.bool]
      (Tm.imp (Tm.all A (.lam A (Tm.imp (.app P.weaken.weaken (.bvar 0)) (.bvar 1))))
        (.bvar 0)) .bool :=
  (HasType.all hA (.lam hA
    ((HasType.app ((hP.weaken .bool).weaken A) (.bvar rfl hA)).imp
      (.bvar rfl (by trivial))))).imp (.bvar rfl (by trivial))

theorem exIntro (hA : A.WellFormed sig.tyOps) (hP : HasType sig [] P (.arr A .bool))
    (hx : HasType sig [] x A) (proof : Derives sig theory H (.app P x)) :
    Derives sig theory H (Tm.ex A P) := by
  apply allIntro (by trivial) (exBodyTyping hA hP)
  intro n _ _
  let r := Tm.fvar n .bool
  have hr : HasType sig [] r .bool := .fvar n (by trivial)
  let body := Tm.imp (.app P.weaken (.bvar 0)) r.weaken
  have hbody : HasType sig [A] body .bool :=
    (HasType.app (hP.weaken A) (.bvar rfl hA)).imp (hr.weaken A)
  let hypothesis := Tm.all A (.lam A body)
  have hh : HasType sig [] hypothesis .bool := HasType.all hA (.lam hA hbody)
  have hK : TypedHyps sig [] (insert hypothesis H) := typedInsert proof.typedHyps hh
  have general : Derives sig theory (insert hypothesis H) hypothesis := assumeIn hK (by simp)
  have beta := generalBeta (theory := theory) hbody hx
  have implication : Derives sig theory (insert hypothesis H) (Tm.imp (.app P x) r) := by
    simpa only [body, Tm.«open», Tm.subst_imp, Tm.subst, Tm.openSub,
      subst_openSub_weaken, Finset.empty_union] using beta.eqMp (allElim hx general)
  have argument := proof.weaken (Finset.subset_insert _ _) hK
  have result := impIntro hh (impElimSame hr implication argument)
  simpa only [Tm.«open», Tm.subst_imp, Tm.subst_all, Tm.subst, Tm.liftSub,
    Tm.openSub, Tm.subst_weaken, subst_openSub_weaken, hypothesis, body] using result

private theorem exApply {r : Tm} (hA : A.WellFormed sig.tyOps)
    (hP : HasType sig [] P (.arr A .bool)) (hr : HasType sig [] r .bool)
    (proof : Derives sig theory H (Tm.ex A P)) :
    Derives sig theory H
      (Tm.imp (Tm.all A (.lam A (Tm.imp (.app P.weaken (.bvar 0)) r.weaken))) r) := by
  have applied := allElim hr proof
  have beta := generalBeta (theory := theory) (exBodyTyping hA hP) hr
  simpa only [Tm.«open», Tm.subst_imp, Tm.subst_all, Tm.subst, Tm.liftSub,
    Tm.openSub, Tm.subst_weaken, subst_openSub_weaken, Finset.empty_union] using beta.eqMp applied

/-- Existential elimination has the usual freshness requirements on the
predicate, hypotheses, and desired conclusion. -/
theorem exElimFresh {r : Tm} (hA : A.WellFormed sig.tyOps)
    (hP : HasType sig [] P (.arr A .bool)) (hr : HasType sig [] r .bool)
    (proof : Derives sig theory H (Tm.ex A P)) (name : Nat)
    (freshPredicate : P.Fresh (name, A)) (freshResult : r.Fresh (name, A))
    (freshHyps : ∀ t ∈ H, t.Fresh (name, A))
    (branch : Derives sig theory (insert (.app P (.fvar name A)) H) r) :
    Derives sig theory H r := by
  have hbody : HasType sig [A] (Tm.imp (.app P.weaken (.bvar 0)) r.weaken) .bool :=
    (HasType.app (hP.weaken A) (.bvar rfl hA)).imp (hr.weaken A)
  have freshBody : (Tm.imp (.app P.weaken (.bvar 0)) r.weaken).Fresh (name, A) := by
    simp only [Tm.Fresh] at freshPredicate freshResult ⊢
    simp [Tm.imp, Tm.equal, Tm.freeVars, freshPredicate, freshResult]
  have generalized : Derives sig theory H
      (Tm.all A (.lam A (Tm.imp (.app P.weaken (.bvar 0)) r.weaken))) := by
    apply allIntroFresh hA hbody name freshBody freshHyps
    simpa only [Tm.«open», Tm.subst_imp, Tm.subst, Tm.openSub, subst_openSub_weaken] using
      impIntro (HasType.app hP (.fvar name hA)) branch
  exact impElimSame hr (exApply hA hP hr proof) generalized

/-- The schematic eta axiom at an arbitrary function type. -/
theorem eta (hA : A.WellFormed sig.tyOps) (hB : B.WellFormed sig.tyOps)
    (hf : HasType sig [] f (.arr A B)) : Derives sig classicalTheory ∅ (Tm.eta A B f) := by
  have base : Derives sig classicalTheory ∅
      (Tm.eta (.var 0) (.var 1) (.fvar 0 (.arr (.var 0) (.var 1)))) :=
    .axiom (by simp [classicalTheory])
      (.eta (by simp [Ty.WellFormed]) (by simp [Ty.WellFormed])
        (.fvar 0 (by simp [Ty.WellFormed])))
  let θ : Nat → Ty := fun n => if n = 0 then A else B
  have typedθ : ∀ n, (θ n).WellFormed sig.tyOps := by
    intro n
    dsimp [θ]
    split <;> assumption
  have instantiated : Derives sig classicalTheory ∅ (Tm.eta A B (.fvar 0 (.arr A B))) := by
    simpa [Tm.tySubst, θ] using base.instType θ typedθ
  let σ : Nat → Ty → Tm := fun n C => if (n, C) = (0, .arr A B) then f else .fvar n C
  have typed : ∀ n C, C.WellFormed sig.tyOps → HasType sig [] (σ n C) C := by
    intro n C hC
    dsimp [σ]
    split
    · rename_i heq
      cases Prod.mk.inj heq |>.2
      exact hf
    · exact .fvar n hC
  simpa [Tm.freeSubst, σ] using instantiated.inst σ typed

/-- The schematic selection axiom can be instantiated at any declared type,
predicate, and witness. Replacements are simultaneous, even if the supplied
terms contain the schematic names themselves. -/
theorem selection (hA : A.WellFormed sig.tyOps)
    (hP : HasType sig [] P (.arr A .bool)) (hx : HasType sig [] x A) :
    Derives sig classicalTheory ∅ (Tm.selection A P x) := by
  have base : Derives sig classicalTheory ∅
      (Tm.selection (.var 0) (.fvar 0 (.arr (.var 0) .bool)) (.fvar 1 (.var 0))) :=
    .axiom (by simp [classicalTheory])
      (.selection (by simp [Ty.WellFormed])
        (.fvar 0 (by simp [Ty.WellFormed])) (.fvar 1 (by simp [Ty.WellFormed])))
  have instantiated : Derives sig classicalTheory ∅
      (Tm.selection A (.fvar 0 (.arr A .bool)) (.fvar 1 A)) := by
    simpa only [Finset.image_empty, Tm.tySubst_selection, Tm.tySubst,
      Ty.subst_var, Ty.subst_arr, Ty.subst_bool] using
      (base.instType (fun _ => A) (fun _ => hA))
  let σ : Nat → Ty → Tm := fun n C =>
    if (n, C) = (0, .arr A .bool) then P else if (n, C) = (1, A) then x else .fvar n C
  have typed : ∀ n C, C.WellFormed sig.tyOps → HasType sig [] (σ n C) C := by
    intro n C hC
    simp only [σ]
    split
    · rename_i heq
      cases Prod.mk.inj heq |>.2
      exact hP
    · split
      · rename_i heq
        cases Prod.mk.inj heq |>.2
        exact hx
      · exact .fvar n hC
  simpa [Tm.freeSubst, σ] using
    (instantiated.inst σ typed)

end Derives
end Silmaril.Logic.HOLLight
