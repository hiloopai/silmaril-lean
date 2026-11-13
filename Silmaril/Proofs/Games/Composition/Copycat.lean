module

public import Silmaril.Games.Composition.Defs

/-!
# Copycat plays: legality and receptiveness

The plays of the copycat strategy are the prefixes of `Ev.double w` for an
alternating `w`. That they are legal and receptive is proved in
`Silmaril.Games.Composition.Defs`, where `Strategy.id` needs it; this module keeps
the unfolding lemmas of `Ev.double` under the names the unit proofs use, and
the former names of the copycat facts as deprecated aliases.
-/

public section

namespace Silmaril.Proofs.Games.Composition

open Silmaril.Games

universe u

variable {E : Sig.{u}}

@[simp] theorem double_nil : Ev.double ([] : List (Ev E)) = [] := rfl

@[simp] theorem double_cons (x : Ev E) (w : List (Ev E)) :
    Ev.double (x :: w) = Ev.copy x ++ Ev.double w := by
  simp [Ev.double]

@[simp] theorem copy_ask (m : E.Op) : Ev.copy (.ask m) = [.inr (.ask m), .inl (.ask m)] := rfl

@[simp] theorem copy_ans (m : E.Op) (n : E.Ar m) :
    Ev.copy (.ans m n) = [.inl (.ans m n), .inr (.ans m n)] := rfl

@[deprecated Ev.path_double (since := "2026-11-12")]
theorem path_double {w : List (Ev E)} (hw : Ev.Alternating w) :
    ∃ x, Path .idle (Ev.double w) x :=
  Ev.path_double hw

@[deprecated Ev.legal_of_prefix_double (since := "2026-11-12")]
theorem legal_of_prefix_double {w : List (Ev E)} (hw : Ev.Alternating w)
    {c : List (Move E E)} (hc : c <+: Ev.double w) : Legal c :=
  Ev.legal_of_prefix_double hw hc

@[deprecated Ev.receptive_double (since := "2026-11-12")]
theorem receptive_double {w : List (Ev E)} (hw : Ev.Alternating w) :
    ∀ {c : List (Move E E)}, c <+: Ev.double w → ∀ {x y : Pos E E} {o : Move E E},
      Path .idle c x → Step x o y → o.IsO →
      ∃ w', Ev.Alternating w' ∧ c ++ [o] <+: Ev.double w' :=
  fun hc _ _ _ hx hxy ho => Ev.receptive_double hw hc hx hxy ho

end Silmaril.Proofs.Games.Composition
