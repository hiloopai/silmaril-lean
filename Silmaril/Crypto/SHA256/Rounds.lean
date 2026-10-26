module

public import Silmaril.Crypto.SHA256.Kernel
public import Mathlib.Data.List.GetD

/-!
# The SHA-256 rounds as an indexed function (FIPS 180-4 §6.2.2 step 3)

`Silmaril.Crypto.SHA256.Kernel` gives the sixty-four rounds in two shapes, and a
machine-code proof can use neither directly:

* `rounds st W = (Ks.zip W).foldl roundStep st` is a **fold**, which has no index.  A
  loop invariant for a counted loop is a predicate `I : Nat → State → Prop` stepping
  `t ↦ t + 1`, and there is nothing in a `foldl` for `t` to be.
* `roundsUnrolled` is sixty-four `let`s written out, which has nothing to induct on.

Note that `roundsUnrolled_eq_rounds` being `rfl` does **not** help.  The obstruction is
the *shape*, not the equality: neither side carries an index, so no amount of rewriting
between them produces something an invariant can step.  That is why this module adds a
third form rather than bending one of the two.

`roundsUpTo` is the same computation by recursion on the round number.  It is what a
counted-loop rule consumes directly, and `roundsUpTo_64` converts to the specification's
`rounds` once, at the end of the induction.

Everything here is generic in the schedule `W : Nat → Word` and the entry state, and
mentions no machine state, so it is shared by every optimisation level's round loop.
The schedule itself is `Silmaril.Crypto.SHA256.Schedule`'s business; this module is
deliberately parametric in it, because a round loop that reads `W t` from a slot and
adds it without inspecting it does not need to know what the schedule is.

## Definitions
- `roundsUpTo`: the first `t` rounds, by recursion on `t`.

## Theorems
- `roundsUpTo_zero`, `roundsUpTo_succ`: the two defining equations, as rewrite rules.
- `roundsUpTo_take`: the indexed form agrees with the fold on every prefix.
- `roundsUpTo_64`: sixty-four indexed rounds are the specification's `rounds`.
-/

@[expose] public section

namespace Silmaril.Crypto.SHA256.Kernel

/-- The first `t` rounds, indexed rather than folded, so that a counted-loop
invariant can step it. -/
def roundsUpTo (W : Nat → Word) (st : State) : Nat → State
  | 0 => st
  | t + 1 => roundStep (roundsUpTo W st t) (Ks.getD t 0, W t)

@[simp] theorem roundsUpTo_zero (W : Nat → Word) (st : State) :
    roundsUpTo W st 0 = st := rfl

theorem roundsUpTo_succ (W : Nat → Word) (st : State) (t : Nat) :
    roundsUpTo W st (t + 1) = roundStep (roundsUpTo W st t) (Ks.getD t 0, W t) := rfl

/-- The indexed form agrees with the fold on every prefix of the schedule. -/
theorem roundsUpTo_take (W : Nat → Word) (st : State) (Wl : List Word)
    (hlen : Wl.length = 64) (hW : ∀ j, j < 64 → W j = Wl.getD j 0) :
    ∀ n, n ≤ 64 → roundsUpTo W st n = ((Ks.zip Wl).take n).foldl roundStep st := by
  have hKlen : Ks.length = 64 := rfl
  have hzlen : (Ks.zip Wl).length = 64 := by
    rw [List.length_zip, hKlen, hlen]
    omega
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hn' : n < (Ks.zip Wl).length := by omega
    have helem : (Ks.zip Wl)[n]'hn' = (Ks.getD n 0, W n) := by
      rw [List.getElem_zip, hW n (by omega)]
      have h1 : Ks.getD n 0 = Ks[n]'(show n < Ks.length by omega) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show n < Ks.length by omega)]
        rfl
      have h2 : Wl.getD n 0 = Wl[n]'(show n < Wl.length by omega) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show n < Wl.length by omega)]
        rfl
      rw [h1, h2]
    rw [List.take_add_one, List.foldl_append, ← ih (by omega),
      List.getElem?_eq_getElem hn']
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, roundsUpTo_succ]
    rw [helem]

/-- **The bridge.** Sixty-four indexed rounds are the specification's `rounds`. -/
theorem roundsUpTo_64 (W : Nat → Word) (st : State) (Wl : List Word)
    (hlen : Wl.length = 64) (hW : ∀ j, j < 64 → W j = Wl.getD j 0) :
    roundsUpTo W st 64 = rounds st Wl := by
  have hzlen : (Ks.zip Wl).length = 64 := by
    rw [List.length_zip, show Ks.length = 64 from rfl, hlen]
    omega
  rw [roundsUpTo_take W st Wl hlen hW 64 (by omega), rounds,
    List.take_of_length_le (by omega)]

end Silmaril.Crypto.SHA256.Kernel
