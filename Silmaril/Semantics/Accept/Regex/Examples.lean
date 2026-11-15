module

public import Silmaril.Semantics.Accept.Regex.Thms

/-! # Regular-expression presentations: worked examples and regression tests

* `digits`, the byte regex `[0-9]+`, with its language characterized exactly (sound and
  complete), its regularity, and Bool matcher tests;
* `items`, a comma-separated list `x (',' x)*` whose item `x` is an **abstract leaf**: any
  acceptor set. Its matcher is assembled from a Bool checker for the leaf
  (`decides_matchB_ofBool`); substituting `digits` for the leaf gives a leaf-free (hence
  regular) expression, and evaluation commutes with the substitution (`eval_bind`);
* monotonicity in the leaf language.

Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.RegexExamples

open Silmaril.Accept Silmaril.Accept.Regex Silmaril.Accept.Regex.Expr
open scoped Computability

/-! ## `[0-9]+` over bytes -/

/-- ASCII digits `0x30`–`0x39`. -/
def isDigit (b : UInt8) : Prop := 0x30 ≤ b ∧ b ≤ 0x39

/-- `[0-9]+`, leaf-free. -/
def digits {ι : Type} : Expr ι UInt8 := oneOrMore (byteRange 0x30 0x39)

/-- `[0-9]+` presents exactly the nonempty strings of digits, in every environment. -/
theorem eval_digits {ι : Type} (ρ : ι → Language UInt8) :
    eval ρ digits = {w | w ≠ [] ∧ ∀ b ∈ w, isDigit b} := by
  ext w
  simp only [digits, eval_oneOrMore, eval_byteRange, Bytes.range, Regex.oneOrMore,
    Language.mem_mul]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, v, hv, rfl⟩
    exact ⟨List.cons_ne_nil _ _, by simpa [isDigit, ha] using mem_kstar_letters.1 hv⟩
  · rintro ⟨hw, hd⟩
    obtain ⟨a, v, rfl⟩ := List.exists_cons_of_ne_nil hw
    exact ⟨[a], ⟨a, hd a (by simp), rfl⟩, v, mem_kstar_letters.2 fun b hb => hd b (by simp [hb]),
      rfl⟩

example : (eval (ι := Empty) Empty.elim digits).IsRegular := isRegular_eval _ fun i _ => i.elim

/-- No leaves, so the leaf checkers are irrelevant. -/
def digitsB (w : List UInt8) : Bool := matchB (ι := Empty) Empty.elim digits w

example : Decides digitsB (eval (ι := Empty) Empty.elim digits) :=
  decides_matchB _ (fun i => i.elim) _

example : digitsB [0x31, 0x32, 0x33] = true := by decide
example : digitsB [] = false := by decide
example : digitsB [0x31, 0x61] = false := by decide

/-! ## A list of arbitrary items -/

/-- `x (',' x)*` with the item `x` an abstract leaf. -/
def items : Expr Unit UInt8 := comp (leaf ()) (star (comp (char 0x2c) (leaf ())))

/-- Lowercase ASCII words, as a Bool checker (any acceptor with a checker would do). -/
def lowerB (w : List UInt8) : Bool := !w.isEmpty && w.all fun b => decide (0x61 ≤ b ∧ b ≤ 0x7a)

/-- The matcher of `items` with lowercase words as items. -/
def lowerItemsB : List UInt8 → Bool := matchB (fun _ => lowerB) items

example : Decides lowerItemsB (eval (fun _ => ofBool lowerB) items) :=
  decides_matchB_ofBool _ _

-- `ab,c` is accepted; `ab,,c`, `,c` and `` are not.
example : lowerItemsB [0x61, 0x62, 0x2c, 0x63] = true := by decide
example : lowerItemsB [0x61, 0x62, 0x2c, 0x2c, 0x63] = false := by decide
example : lowerItemsB [0x2c, 0x63] = false := by decide
example : lowerItemsB [] = false := by decide

/-- Monotonicity: enlarging the item language enlarges the list language. -/
example {L L' : Language UInt8} (h : L ≤ L') :
    eval (fun _ => L) items ≤ eval (fun _ => L') items :=
  eval_mono fun _ _ => h

/-- Substituting `digits` for the item: the result is leaf-free, its value is the list
language at the item language `[0-9]+`, and it is regular. -/
def digitItems : Expr Empty UInt8 := bind (fun _ => digits) items

example (ρ : Empty → Language UInt8) :
    eval ρ digitItems = eval (fun _ => {w | w ≠ [] ∧ ∀ b ∈ w, isDigit b}) items := by
  rw [digitItems, eval_bind]; simp only [eval_digits]

example : (eval Empty.elim digitItems).IsRegular := isRegular_eval _ fun i _ => i.elim

end Silmaril.Accept.RegexExamples
