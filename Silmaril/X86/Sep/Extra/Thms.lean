module

public import Silmaril.X86.Sep.Extra.Defs
public import Silmaril.X86.Sep.Thms
import Silmaril.Proofs.X86.Sep.Extra

/-!
# Laws of `sor` and `strue`

* `strue`: `entails_strue` (everything entails it), `strue_sep_strue`, `strue_absorb`
  (`P ∗ strue ∗ strue ⊢ P ∗ strue`), `sep_strue_intro` (`P ⊢ P ∗ strue`: anything may be
  dropped into the garbage) and `sep_strue_weaken` (a conjunct may be dropped into it).
* `sor`: introduction and elimination (`sor_intro_left`, `sor_intro_right`, `sor_elim`),
  monotonicity (`sor_mono`), `sor_comm`, and distribution of `∗` over `sor` (`sor_sep`,
  `sep_sor`, as equalities).

The proofs are short and kept in this header, except `sor_sep`.
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Frag (union Disjoint)

/-! ## `strue` -/

/-- Everything entails `strue`. -/
theorem entails_strue (P : SProp) : P ⊢ₛ strue := fun _ _ => trivial

theorem strue_sep_strue : (strue ∗ strue) ⊢ₛ strue := entails_strue _

/-- Two pieces of garbage are one. -/
theorem strue_absorb (P : SProp) : (P ∗ strue ∗ strue) ⊢ₛ (P ∗ strue) :=
  sep_mono_right P strue_sep_strue

/-- Garbage may always be added (it may be empty). -/
theorem sep_strue_intro (P : SProp) : P ⊢ₛ (P ∗ strue) :=
  entails_trans (entails_of_eq (sep_emp P).symm) (sep_mono_right P (entails_strue emp))

/-- A conjunct may be dropped into the garbage. -/
theorem sep_strue_weaken (P Q : SProp) : (P ∗ Q) ⊢ₛ (P ∗ strue) :=
  sep_mono_right P (entails_strue Q)

/-! ## `sor` -/

theorem sor_intro_left (P Q : SProp) : P ⊢ₛ sor P Q := fun _ h => .inl h

theorem sor_intro_right (P Q : SProp) : Q ⊢ₛ sor P Q := fun _ h => .inr h

theorem sor_elim {P Q R : SProp} (hp : P ⊢ₛ R) (hq : Q ⊢ₛ R) : sor P Q ⊢ₛ R :=
  fun h hpq => hpq.elim (hp h) (hq h)

theorem sor_mono {P P' Q Q' : SProp} (hp : P ⊢ₛ P') (hq : Q ⊢ₛ Q') : sor P Q ⊢ₛ sor P' Q' :=
  fun h hpq => hpq.imp (hp h) (hq h)

theorem sor_comm (P Q : SProp) : sor P Q = sor Q P := by
  funext h; exact propext Or.comm

/-- `∗` distributes over `sor` (on the right). -/
theorem sor_sep (P Q R : SProp) : (sor P Q ∗ R) = sor (P ∗ R) (Q ∗ R) :=
  Silmaril.Proofs.X86.Sep.sor_sep P Q R

/-- `∗` distributes over `sor` (on the left). -/
theorem sep_sor (P Q R : SProp) : (P ∗ sor Q R) = sor (P ∗ Q) (P ∗ R) := by
  rw [sep_comm, sor_sep, sep_comm Q P, sep_comm R P]

end Silmaril.X86.Sep
