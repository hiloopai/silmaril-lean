module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Strictness

/-! # Exercise sheet 2, question 2 (strictness)

Source: `cam-optcomp-2025-exercise-sheet-2` in `references.bib`, question 2.


(a) `Prog.IsStrictIn g 1` (notes p. 22): `g(d₀, ⊥, d₂) = ⊥` for all `d₀, d₂`;
operationally, whenever the second argument loops, so does the call, so it is
safe to evaluate that argument first (call-by-value).

(b) `fSharp_eq`: `f♯ = λ(x, y).0` and `gSharp_eq`: `g♯ = λ(x, y).x ∧ y`. Both
are strict in both parameters (`f_strict`, `g_strict`), so both allow
call-by-value for both; but `f` never evaluates its parameters: it is strict
because it never terminates, not because it needs them.

(c) `fcSharp_eq`: `f♯(x, y, z) = x ∧ (y ∨ (y ∧ z)) = x ∧ y`.

(d) The bit vector of `f1(x, y, z) = if x then y else z` is `(1, 0, 0)`
(`f1_bits`): it is strict in `x` only. From bits alone, `g1(x, y) =
f1(x, y, y+1)` can only be found strict in `x`, since `y` reaches `f1` only in
non-strict positions. The strictness function `f1♯ = x ∧ (y ∨ z)` shows that
`g1` is strict in `y` too (`g1_strict_y`), so `y` can be passed by value.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S2Q2

open Strictness

/-- Built-ins: `cond`, `=`, `+`, `0` and `+1`. -/
inductive P where
  | cond | eq | plus | zero | add1

@[reducible] def P.arity : P → ℕ
  | .cond => 3
  | .eq | .plus => 2
  | .zero => 0
  | .add1 => 1

def P.sem : (a : P) → (Fin a.arity → Part ℤ) → Part ℤ
  | .cond, d => (d 0).bind fun p => if p = 0 then d 2 else d 1
  | .eq, d => (d 0).bind fun a => (d 1).map fun b => if a = b then 1 else 0
  | .plus, d => (d 0).bind fun a => (d 1).map fun b => a + b
  | .zero, _ => Part.some 0
  | .add1, d => (d 0).map (· + 1)

def P.sharp : (a : P) → (Fin a.arity → Bool) → Bool
  | .cond, x => x 0 && (x 1 || x 2)
  | .eq, x | .plus, x => x 0 && x 1
  | .zero, _ => true
  | .add1, x => x 0

/-- The strictness functions are monotone. -/
theorem P.sharp_mono : ∀ a, Monotone (P.sharp a)
  | .cond => fun x y h => by
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    simp only [P.sharp]
    revert h0 h1 h2
    generalize x 0 = a0; generalize x 1 = a1; generalize x 2 = a2
    generalize y 0 = b0; generalize y 1 = b1; generalize y 2 = b2
    revert a0 a1 a2 b0 b1 b2
    decide
  | .eq | .plus => fun x y h => by
    have h0 := h 0; have h1 := h 1
    simp only [P.sharp]
    revert h0 h1
    generalize x 0 = a0; generalize x 1 = a1
    generalize y 0 = b0; generalize y 1 = b1
    revert a0 a1 b0 b1
    decide
  | .add1 => fun _ _ h => h 0
  | .zero => fun _ _ _ => le_rfl

/-- The strictness functions are safe. -/
theorem P.sharp_safe : ∀ a x (d : Fin a.arity → Part ℤ), P.sharp a x = false →
    (∀ j, x j = false → d j = Part.none) → P.sem a d = Part.none
  | .cond, x, d, hx, hd => by
    simp only [P.sharp, Bool.and_eq_false_iff, Bool.or_eq_false_iff] at hx
    rcases hx with h0 | ⟨h1, h2⟩
    · simp only [P.sem, hd 0 h0, Part.bind_none]
    · simp only [P.sem, hd 1 h1, hd 2 h2, ite_self, part_bind_none_right]
  | .eq, x, d, hx, hd => by
    simp only [P.sharp, Bool.and_eq_false_iff] at hx
    rcases hx with h0 | h1
    · simp only [P.sem, hd 0 h0, Part.bind_none]
    · simp only [P.sem, hd 1 h1, Part.map_none, part_bind_none_right]
  | .plus, x, d, hx, hd => by
    simp only [P.sharp, Bool.and_eq_false_iff] at hx
    rcases hx with h0 | h1
    · simp only [P.sem, hd 0 h0, Part.bind_none]
    · simp only [P.sem, hd 1 h1, Part.map_none, part_bind_none_right]
  | .add1, x, d, hx, hd => by simp only [P.sem, hd 0 hx, Part.map_none]
  | .zero, _, _, hx, _ => by simp [P.sharp] at hx

/-- Signatures with `n` user functions of arities `far`. -/
@[reducible] def sig (n : ℕ) (far : Fin n → ℕ) : Sig where
  B := P
  bar := P.arity
  sem := P.sem
  sharp := P.sharp
  n := n
  far := far

/-! ## (b) -/

/-- `f(x, y) = f(x, y)` (function 0) and `g(x, y) = x + y` (function 1). -/
def progB : Prog (sig 2 fun _ => 2) where
  body
    | ⟨0, _⟩ => .call 0 ![.arg 0, .arg 1]
    | ⟨1, _⟩ => .prim P.plus ![.arg 0, .arg 1]
    | ⟨n + 2, h⟩ => absurd h (by simp)

theorem fSharp_eq : progB.sharp 0 = fun _ => false := by
  have hle := progB.sharp_le (c := fun f _ => if f = 0 then false else true) (by
    intro f x
    by_cases h : f = 0
    · subst h
      show (if (0 : Fin 2) = 0 then false else true) ≤ _
      simp
    · show _ ≤ (if f = 0 then false else true)
      simp [h])
  funext x
  apply le_antisymm _ (Bool.false_le _)
  simpa using hle 0 x

theorem gSharp_eq : progB.sharp 1 = fun x => x 0 && x 1 := by
  funext x
  rw [← congrFun (congrFun (progB.sharp_isFixedPt P.sharp_mono) 1) x]
  rfl

theorem f_strict (i : Fin 2) : Prog.IsStrictIn (progB.denote 0) i :=
  progB.strict_of_sharp P.sharp_mono P.sharp_safe (by simp only [fSharp_eq])

theorem g_strict (i : Fin 2) : Prog.IsStrictIn (progB.denote 1) i := by
  refine progB.strict_of_sharp P.sharp_mono P.sharp_safe ?_
  rw [gSharp_eq]
  revert i
  decide

/-! ## (c) -/

/-- `f(x, y, z) = if x = 0 then y else y + z`, as
`cond(eq(x, 0), y, plus(y, z))`: `eq` yields `1` when its arguments are equal,
and `cond` takes its second argument on a non-zero test. -/
def progC : Prog (sig 1 fun _ => 3) where
  body _ := .prim P.cond ![.prim P.eq ![.arg 0, .prim P.zero ![]], .arg 1,
    .prim P.plus ![.arg 1, .arg 2]]

theorem fcSharp_eq : progC.sharp 0 = fun x => x 0 && x 1 := by
  funext x
  rw [← congrFun (congrFun (progC.sharp_isFixedPt P.sharp_mono) 0) x]
  show ((x 0 && true) && (x 1 || (x 1 && x 2))) = (x 0 && x 1)
  generalize x 0 = a; generalize x 1 = b; generalize x 2 = c
  revert a b c
  decide

/-! ## (d) -/

/-- `f1(x, y, z) = if x then y else z` (function 0, arity 3) and
`g1(x, y) = f1(x, y, y+1)` (function 1, arity 2). -/
@[reducible] def sigD : Sig := sig 2 ![3, 2]

/-- The body of `f1`. -/
def f1Body : Expr sigD 3 := .prim P.cond ![.arg 0, .arg 1, .arg 2]

/-- The body of `g1`. -/
def g1Body : Expr sigD 2 := .call 0 ![.arg 0, .arg 1, .prim P.add1 ![.arg 1]]

def progD : Prog sigD where
  body := Fin.cases (motive := fun f => Expr sigD (sigD.far f)) f1Body
    (Fin.cases (motive := fun i => Expr sigD (sigD.far i.succ)) g1Body fun j => j.elim0)

/-- `f1` denotes its body. -/
theorem denote_f1 (d : Fin 3 → Part ℤ) :
    progD.denote 0 d = (d 0).bind fun p => if p = 0 then d 2 else d 1 :=
  progD.denote_eq_of_const fun _ => rfl

/-- The bit vector of `f1`: strict in `x` only. -/
theorem f1_bits (i : Fin 3) : Prog.IsStrictIn (progD.denote 0) i ↔ i.val = 0 := by
  match i with
  | ⟨0, _⟩ =>
    refine ⟨fun _ => rfl, fun _ d hd => ?_⟩
    have h0 : d (0 : Fin 3) = Part.none := hd
    show progD.denote 0 d = Part.none
    rw [denote_f1 d, h0, Part.bind_none]
  | ⟨1, _⟩ =>
    refine ⟨fun hs => ?_, fun h => by simp at h⟩
    have h := hs ![Part.some 0, Part.none, Part.some 0] rfl
    rw [denote_f1] at h
    change (Part.some (0 : ℤ)).bind (fun p => if p = 0 then Part.some 0 else Part.none) =
      Part.none at h
    simp at h
  | ⟨2, _⟩ =>
    refine ⟨fun hs => ?_, fun h => by simp at h⟩
    have h := hs ![Part.some 1, Part.some 0, Part.none] rfl
    rw [denote_f1] at h
    change (Part.some (1 : ℤ)).bind (fun p => if p = 0 then Part.none else Part.some 0) =
      Part.none at h
    simp at h
  | ⟨n + 3, h⟩ => exact absurd h (by omega)

/-- The strictness function shows `g1` strict in `y`. -/
theorem g1_strict_y : progD.sharp 1 (fun j => decide (j.val ≠ 1)) = false := by
  have hfix := progD.sharp_isFixedPt P.sharp_mono
  rw [← congrFun (congrFun hfix 1) _]
  show progD.sharp 0 _ = false
  rw [← congrFun (congrFun hfix 0) _]
  rfl

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S2Q2
