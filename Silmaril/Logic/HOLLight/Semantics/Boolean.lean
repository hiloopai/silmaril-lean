module

public import Silmaril.Logic.HOLLight.Semantics.Type

@[expose] public section

/-!
# Boolean meanings of the defined logical vocabulary

These carrier-level operations follow the equality-only definitions in
`HOLLight.Logic`. Their truth conditions establish the usual connectives and
quantifiers using full function spaces and actual equality.
-/

namespace Silmaril.Logic.HOLLight.Carrier

universe u

noncomputable def truth : bool.{u} := eq (arr bool bool) id id
noncomputable def all (A : Carrier.{u}) (p : A → bool.{u}) : bool.{u} :=
  eq (arr A bool) p (fun _ => truth)
noncomputable def falsity : bool.{u} := all bool id
noncomputable def conj (p q : bool.{u}) : bool.{u} :=
  eq (arr (arr bool (arr bool bool)) bool)
    (fun f => f p q) (fun f => f truth truth)
noncomputable def imp (p q : bool.{u}) : bool.{u} := eq bool (conj p q) p
noncomputable def neg (p : bool.{u}) : bool.{u} := imp p falsity
noncomputable def disj (p q : bool.{u}) : bool.{u} :=
  all bool (fun r => imp (imp p r) (imp (imp q r) r))
noncomputable def ex (A : Carrier.{u}) (p : A → bool.{u}) : bool.{u} :=
  all bool (fun r => imp (all A (fun x => imp (p x) r)) r)

@[simp] theorem truth_truth : Truth (truth.{u}) := by
  exact (truth_eq _ _).mpr rfl

@[simp] theorem eq_truth_iff (p : bool.{u}) : p = truth ↔ Truth p := by
  constructor
  · intro h; simp [h]
  · intro h
    exact bool_ext (by simp [h])

@[simp] theorem truth_all (A : Carrier.{u}) (p : A → bool.{u}) :
    Truth (all A p) ↔ ∀ x, Truth (p x) := by
  rw [all, truth_eq]
  constructor
  · intro h x
    exact (eq_truth_iff _).mp (congrFun h x)
  · intro h
    exact _root_.funext (fun x => (eq_truth_iff _).mpr (h x))

@[simp] theorem not_truth_falsity : ¬ Truth (falsity.{u}) := by
  intro h
  have := (truth_all bool id).mp h (ULift.up false)
  exact Bool.noConfusion this

@[simp] theorem truth_conj (p q : bool.{u}) :
    Truth (conj p q) ↔ Truth p ∧ Truth q := by
  rw [conj, truth_eq]
  constructor
  · intro h
    exact ⟨(eq_truth_iff _).mp (congrFun h (fun x _ => x)),
      (eq_truth_iff _).mp (congrFun h (fun _ y => y))⟩
  · rintro ⟨hp, hq⟩
    rw [(eq_truth_iff p).mpr hp, (eq_truth_iff q).mpr hq]

@[simp] theorem truth_imp (p q : bool.{u}) :
    Truth (imp p q) ↔ (Truth p → Truth q) := by
  rw [imp, truth_eq]
  constructor
  · intro h hp
    exact ((truth_conj p q).mp (h.symm ▸ hp)).2
  · intro h
    apply bool_ext
    rw [truth_conj]
    exact ⟨And.left, fun hp => ⟨hp, h hp⟩⟩

@[simp] theorem truth_neg (p : bool.{u}) : Truth (neg p) ↔ ¬ Truth p := by
  simp [neg]

@[simp] theorem truth_disj (p q : bool.{u}) :
    Truth (disj p q) ↔ Truth p ∨ Truth q := by
  classical
  simp only [disj, truth_all, truth_imp]
  constructor
  · intro h
    apply Classical.byContradiction
    intro neither
    have np : ¬ Truth p := fun hp => neither (.inl hp)
    have nq : ¬ Truth q := fun hq => neither (.inr hq)
    exact not_truth_falsity (h falsity (fun hp => False.elim (np hp))
      (fun hq => False.elim (nq hq)))
  · intro h r hp hq
    exact h.elim hp hq

@[simp] theorem truth_ex (A : Carrier.{u}) (p : A → bool.{u}) :
    Truth (ex A p) ↔ ∃ x, Truth (p x) := by
  classical
  simp only [ex, truth_all, truth_imp]
  constructor
  · intro h
    apply Classical.byContradiction
    intro noWitness
    exact not_truth_falsity (h falsity (fun x hx =>
      False.elim (noWitness ⟨x, hx⟩)))
  · rintro ⟨x, hx⟩ r h
    exact h x hx

noncomputable def injective (A B : Carrier.{u}) (f : A → B) : bool.{u} :=
  all A (fun x => all A (fun y => imp (eq B (f x) (f y)) (eq A x y)))

noncomputable def surjective (A B : Carrier.{u}) (f : A → B) : bool.{u} :=
  all B (fun y => ex A (fun x => eq B (f x) y))

@[simp] theorem truth_injective (A B : Carrier.{u}) (f : A → B) :
    Truth (injective A B f) ↔ Function.Injective f := by
  simp [injective, Function.Injective]

@[simp] theorem truth_surjective (A B : Carrier.{u}) (f : A → B) :
    Truth (surjective A B f) ↔ Function.Surjective f := by
  simp [surjective, Function.Surjective]

/-- The standard infinity assertion has a witness in the lifted naturals. -/
theorem infinity_valid :
    Truth (ex (arr ind ind) (fun f => conj (injective ind ind f) (neg (surjective ind ind f)))) := by
  rw [truth_ex]
  refine ⟨fun n => ULift.up (n.down + 1), ?_⟩
  rw [truth_conj, truth_injective, truth_neg, truth_surjective]
  constructor
  · intro x y h
    have h' : x.down + 1 = y.down + 1 := congrArg ULift.down h
    exact ULift.ext (Nat.add_right_cancel h')
  · intro h
    obtain ⟨x, hx⟩ := h (ULift.up 0)
    have : x.down + 1 = 0 := congrArg ULift.down hx
    exact Nat.noConfusion this

theorem eta_valid (A B : Carrier.{u}) (f : A → B) :
    Truth (eq (arr A B) (fun x => f x) f) := (truth_eq _ _).mpr rfl

theorem selection_valid (A : Carrier.{u}) (p : A → bool.{u}) (x : A) :
    Truth (imp (p x) (p (choose A p))) :=
  (truth_imp _ _).mpr (choose_spec p)

end Silmaril.Logic.HOLLight.Carrier
