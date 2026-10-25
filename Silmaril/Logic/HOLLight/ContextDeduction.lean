module

public import Silmaril.Logic.HOLLight.Classical
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# Finite contexts as conjunctions

`Tm.andList` (defined with the logical vocabulary) is an executable, ordered
conjunction with truth as its empty case. `Tm.andAll` is a convenience for the
kernel's finite-set contexts. It
uses the noncomputable `Finset.toList`; none of its logical properties depend
on the selected order. Reordering and repeated list entries yield provably
equal conjunctions.

The deduction theorem identifies a derivation from a finite typed context
with a closed derivation of its conjunction implying the conclusion. All
results use the existing derived rules and hold for any explicit theory.
-/

namespace Silmaril.Logic.HOLLight

namespace Tm

/-- Conjoin a finite context using a chosen list order. For an executable
representation with an explicit order, use `andList`. -/
noncomputable def andAll (H : Hyps) : Tm := andList H.toList

@[simp] theorem andAll_empty : andAll ∅ = truth := by simp [andAll]

end Tm

namespace HasType

theorem andAll {sig : Signature} {Γ : List Ty} {H : Hyps}
    (typed : TypedHyps sig Γ H) : HasType sig Γ (Tm.andAll H) .bool :=
  andList (fun p hp => typed p (Finset.mem_toList.mp hp))

end HasType

namespace Derives

variable {sig : Signature} {theory : Theory} {H K : Hyps} {ps qs : List Tm} {p : Tm}

/-- Introduce a list conjunction from derivations of all its entries. -/
theorem andListIntro (typed : TypedHyps sig [] H)
    (premises : ∀ q ∈ ps, Derives sig theory H q) :
    Derives sig theory H (Tm.andList ps) := by
  induction ps with
  | nil => exact (truth (sig := sig) (theory := theory)).weaken (Finset.empty_subset _) typed
  | cons q qs ih =>
    exact (premises q (List.mem_cons_self ..)).conjIntroSame
      (ih (fun r hr => premises r (List.mem_cons_of_mem q hr)))

/-- Project any member of a list conjunction. -/
theorem andListElim (typed : ∀ q ∈ ps, HasType sig [] q .bool)
    (proof : Derives sig theory H (Tm.andList ps)) (member : p ∈ ps) :
    Derives sig theory H p := by
  induction ps with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons q qs ih =>
    have hq := typed q (List.mem_cons_self ..)
    have hqs : ∀ r ∈ qs, HasType sig [] r .bool :=
      fun r hr => typed r (List.mem_cons_of_mem q hr)
    rcases List.mem_cons.mp member with rfl | hp
    · exact conjElimLeft hq (HasType.andList hqs) proof
    · exact ih hqs (conjElimRight hq (HasType.andList hqs) proof) hp

/-- Introduce the conjunction of a finite context. -/
theorem andAllIntro (typed : TypedHyps sig [] H)
    (premises : ∀ q ∈ K, Derives sig theory H q) :
    Derives sig theory H (Tm.andAll K) :=
  andListIntro typed (fun q hq => premises q (Finset.mem_toList.mp hq))

/-- Project any formula belonging to the conjoined context. -/
theorem andAllElim (typed : TypedHyps sig [] K)
    (proof : Derives sig theory H (Tm.andAll K)) (member : p ∈ K) :
    Derives sig theory H p :=
  andListElim (fun q hq => typed q (Finset.mem_toList.mp hq)) proof
    (Finset.mem_toList.mpr member)

/-- A typed context proves the conjunction of all its assumptions. -/
theorem andAllSelf (typed : TypedHyps sig [] H) :
    Derives sig theory H (Tm.andAll H) :=
  andAllIntro typed (fun _ hq => assumeIn typed hq)

/-- Replacing a finite context by its single conjunction preserves derivability. -/
theorem andAll_context_iff (typed : TypedHyps sig [] H) :
    Derives sig theory {Tm.andAll H} p ↔ Derives sig theory H p := by
  have typedConjunction : TypedHyps sig [] {Tm.andAll H} := by
    intro q hq
    have same := Finset.mem_singleton.mp hq
    subst q
    exact HasType.andAll typed
  constructor
  · intro proof
    apply proof.substituteHyps typed
    intro q hq
    have same := Finset.mem_singleton.mp hq
    subst q
    exact andAllSelf typed
  · intro proof
    apply proof.substituteHyps typedConjunction
    intro q hq
    exact andAllElim typed (Derives.assume (HasType.andAll typed)) hq

/-- The finite-context deduction theorem, including the empty context. -/
theorem andAll_imp_iff (typed : TypedHyps sig [] H) (hp : HasType sig [] p .bool) :
    Derives sig theory ∅ (Tm.imp (Tm.andAll H) p) ↔ Derives sig theory H p := by
  constructor
  · intro proof
    apply (andAll_context_iff typed).mp
    simpa only [Finset.empty_union] using
      impElim hp proof (Derives.assume (HasType.andAll typed))
  · intro proof
    exact impIntro (HasType.andAll typed) ((andAll_context_iff typed).mpr proof)

/-- The list version retains an executable conjunction while the kernel context
forgets ordering and multiplicity. -/
theorem andList_context_iff (typed : ∀ q ∈ ps, HasType sig [] q .bool) :
    Derives sig theory {Tm.andList ps} p ↔ Derives sig theory ps.toFinset p := by
  have typedContext : TypedHyps sig [] ps.toFinset :=
    fun q hq => typed q (List.mem_toFinset.mp hq)
  have typedConjunction : TypedHyps sig [] {Tm.andList ps} := by
    intro q hq
    have same := Finset.mem_singleton.mp hq
    subst q
    exact HasType.andList typed
  constructor
  · intro proof
    apply proof.substituteHyps typedContext
    intro q hq
    have same := Finset.mem_singleton.mp hq
    subst q
    exact andListIntro typedContext
      (fun r hr => assumeIn typedContext (List.mem_toFinset.mpr hr))
  · intro proof
    apply proof.substituteHyps typedConjunction
    intro q hq
    exact andListElim typed (Derives.assume (HasType.andList typed))
      (List.mem_toFinset.mp hq)

/-- Deduction with an explicit list ordering needs no noncomputable syntax operation. -/
theorem andList_imp_iff (typed : ∀ q ∈ ps, HasType sig [] q .bool)
    (hp : HasType sig [] p .bool) :
    Derives sig theory ∅ (Tm.imp (Tm.andList ps) p) ↔ Derives sig theory ps.toFinset p := by
  constructor
  · intro proof
    apply (andList_context_iff typed).mp
    simpa only [Finset.empty_union] using
      impElim hp proof (Derives.assume (HasType.andList typed))
  · intro proof
    exact impIntro (HasType.andList typed) ((andList_context_iff typed).mpr proof)

/-- Only list membership affects the provable meaning of a finite conjunction. -/
theorem andList_equivalent (typed : ∀ q ∈ ps, HasType sig [] q .bool)
    (members : ∀ q, q ∈ ps ↔ q ∈ qs) :
    Derives sig theory ∅ (Tm.equal .bool (Tm.andList ps) (Tm.andList qs)) := by
  have typed' : ∀ q ∈ qs, HasType sig [] q .bool :=
    fun q hq => typed q ((members q).mpr hq)
  have typedPs : TypedHyps sig [] {Tm.andList ps} := by
    intro q hq
    have same := Finset.mem_singleton.mp hq
    subst q
    exact HasType.andList typed
  have typedQs : TypedHyps sig [] {Tm.andList qs} := by
    intro q hq
    have same := Finset.mem_singleton.mp hq
    subst q
    exact HasType.andList typed'
  have forward : Derives sig theory {Tm.andList ps} (Tm.andList qs) :=
    andListIntro typedPs (fun q hq => andListElim typed
      (Derives.assume (HasType.andList typed)) ((members q).mpr hq))
  have backward : Derives sig theory {Tm.andList qs} (Tm.andList ps) :=
    andListIntro typedQs (fun q hq => andListElim typed'
      (Derives.assume (HasType.andList typed')) ((members q).mp hq))
  simpa using backward.deductAntisym forward

/-- Permuting the list changes no logical content. -/
theorem andList_perm (typed : ∀ q ∈ ps, HasType sig [] q .bool) (perm : ps.Perm qs) :
    Derives sig theory ∅ (Tm.equal .bool (Tm.andList ps) (Tm.andList qs)) :=
  andList_equivalent typed (fun _ => perm.mem_iff)

/-- Repeated assumptions may be removed from a list conjunction. -/
theorem andList_dedup (typed : ∀ q ∈ ps, HasType sig [] q .bool) :
    Derives sig theory ∅ (Tm.equal .bool (Tm.andList ps) (Tm.andList ps.dedup)) :=
  andList_equivalent typed (by intro q; simp)

end Derives
end Silmaril.Logic.HOLLight
