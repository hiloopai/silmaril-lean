module

public import Silmaril.Semantics.ITree.Defs
public import Silmaril.Proofs.Semantics.ITree.Basic
import all Silmaril.Proofs.Semantics.ITree.Basic
import Batteries.Tactic.Alias

/-!
# Observe: proofs

Proofs for `Silmaril.Semantics.ITree.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree

universe u v w

namespace Visible

end Visible

@[simp] private theorem roll_out {E : Type u → Type u} {A : Type v} (t : Tree E A) :
    roll (out t) = t := rootEquiv.apply_symm_apply t
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.roll_out := Silmaril.Elgot.ITree.roll_out

@[simp] private theorem out_roll {E : Type u → Type u} {A : Type v}
    (x : Part (Visible E A (Tree E A))) : out (roll x) = x := rootEquiv.symm_apply_apply x
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.out_roll := Silmaril.Elgot.ITree.out_roll

@[simp] private theorem out_diverge {E : Type u → Type u} {A : Type v} :
    out (diverge : Tree E A) = Part.none := by rw [← roll_none, out_roll]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.out_diverge := Silmaril.Elgot.ITree.out_diverge

@[simp] private theorem out_ret {E : Type u → Type u} {A : Type v} (a : A) :
    out (ret (E := E) a) = Part.some (.ret a) := by rw [← roll_ret, out_roll]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.out_ret := Silmaril.Elgot.ITree.out_ret

@[simp] private theorem out_vis {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) (k : R → Tree E A) : out (vis e k) = Part.some (.vis e k) := by
  rw [← roll_vis, out_roll]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.out_vis := Silmaril.Elgot.ITree.out_vis

private theorem out_injective {E : Type u → Type u} {A : Type v} :
    Function.Injective (out (E := E) (A := A)) := rootEquiv.symm.injective
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.out_injective := Silmaril.Elgot.ITree.out_injective

private theorem observe_succ_eq_out {E : Type u → Type u} {A : Type v} (t : Tree E A) (n : Nat) :
    t.observe (n + 1) = Visible.map (fun child => child.observe n) <$> out t := by
  exact congrArg (fun t => t.observe (n + 1)) (roll_out t).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.observe_succ_eq_out := Silmaril.Elgot.ITree.observe_succ_eq_out

@[simp] private theorem out_eq_none_iff {E : Type u → Type u} {A : Type v} (t : Tree E A) :
    out t = Part.none ↔ t = diverge := by
  rw [← out_diverge, out_injective.eq_iff]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.out_eq_none_iff := Silmaril.Elgot.ITree.out_eq_none_iff

@[simp] private theorem ret_inj {E : Type u → Type u} {A : Type v} {a b : A} :
    ret (E := E) a = ret b ↔ a = b := by
  rw [← out_injective.eq_iff]
  simp only [out_ret, Part.some_inj, Visible.ret.injEq]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.ret_inj := Silmaril.Elgot.ITree.ret_inj

@[simp] private theorem vis_inj {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) (k l : R → Tree E A) : vis e k = vis e l ↔ k = l :=
  ⟨vis_continuation_injective e, congrArg (vis e)⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.vis_inj := Silmaril.Elgot.ITree.vis_inj

@[simp] private theorem ret_ne_diverge {E : Type u → Type u} {A : Type v} (a : A) :
    ret (E := E) a ≠ diverge := by
  intro h
  have := congrArg out h
  simp at this
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.ret_ne_diverge := Silmaril.Elgot.ITree.ret_ne_diverge

@[simp] private theorem vis_ne_diverge {E : Type u → Type u} {A : Type v} {R : Type u}
    (e : E R) (k : R → Tree E A) : vis e k ≠ diverge := by
  intro h
  have := congrArg out h
  simp at this
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.vis_ne_diverge := Silmaril.Elgot.ITree.vis_ne_diverge

@[simp] private theorem ret_ne_vis {E : Type u → Type u} {A : Type v} {R : Type u}
    (a : A) (e : E R) (k : R → Tree E A) : ret a ≠ vis e k := by
  intro h
  have := congrArg out h
  simp at this
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.ret_ne_vis := Silmaril.Elgot.ITree.ret_ne_vis

private theorem cases_visible {E : Type u → Type u} {A : Type v} (t : Tree E A) :
    t = diverge ∨ (∃ a, t = ret a) ∨ ∃ (R : Type u) (e : E R) (k : R → Tree E A), t = vis e k := by
  obtain ⟨x, rfl⟩ := roll_surjective t
  induction x using Part.induction_on with
  | hnone => exact Or.inl roll_none
  | hsome x =>
    cases x with
    | ret a => exact Or.inr (Or.inl ⟨a, roll_ret a⟩)
    | @vis R e k => exact Or.inr (Or.inr ⟨R, e, k, roll_vis e k⟩)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.cases_visible := Silmaril.Elgot.ITree.cases_visible

end Silmaril.Elgot.ITree
