module

public import Silmaril.Formats.Compression.Transform.Defs
public import Silmaril.Formats.Compression.Thms

/-!
# Proofs of the transform laws

Stated in `Silmaril.Formats.Compression.Transform.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Transform

open Silmaril.Formats.Compression

theorem inverts_andThen {t u : Transform} {p : t.Params} {q : u.Params} {e e' : Encoder}
    (ht : t.Inverts p e) (hu : u.Inverts q e') :
    (t.andThen u).Inverts (p, q) (fun data => e (e' data)) := by
  intro data
  simp [Transform.andThen, ht (e' data), hu data]

theorem linearAt_andThen {t u : Transform} {p : t.Params} {q : u.Params} {k l : Nat}
    (ht : t.LinearAt p k) (hu : u.LinearAt q l) : (t.andThen u).LinearAt (p, q) (l * k) := by
  intro bytes out h
  simp only [Transform.andThen, Option.bind_eq_some_iff] at h
  obtain ⟨mid, h₁, h₂⟩ := h
  have a := ht h₁
  have b := hu h₂
  rw [Nat.mul_assoc]
  exact Nat.le_trans b (Nat.mul_le_mul_left l a)

theorem andThen_assoc_run (t u v : Transform) (p : t.Params) (q : u.Params) (r : v.Params)
    (bytes : List UInt8) :
    ((t.andThen u).andThen v).run ((p, q), r) bytes = (t.andThen (u.andThen v)).run (p, q, r) bytes := by
  simp only [Transform.andThen, Option.bind_assoc]

end Silmaril.Proofs.Formats.Compression.Transform
