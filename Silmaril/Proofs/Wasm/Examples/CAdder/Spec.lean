module

public import Silmaril.Proofs.Wasm.Examples.CAdder.Instance
public import Silmaril.Wasm.Logic.Arith.Thms

@[expose] public section

/-!
# The compiled C adder: the source, and the straight-line exports

The C source of each export, read on `BitVec 32` (`Src.add`, `Src.mul`, `Src.max`, `Src.odd`,
`Src.popcount`, `Src.gcd`), `expected j args` (the source's value for export `j`), and the
symbolic execution of the five straight-line compiled bodies, in both readings of the logic
(`Wp m`: partial `HWP` or total `TWP` correctness).

The compiled bodies are not the source: `add` and `mul` swap their operands, `max` is `select`
on `i32.gt_s` (the source compares with `<`), `odd` is `(a << 1) | 1` (the source computes
`a * 2 + 1`), and clang replaced the popcount loop by the single instruction `i32.popcnt`.

`Src.popcount` is "the number of set bits" (`BitVec.cpop`), which is what the C loop is meant
to compute; that the loop computes it is tested (`source_popcount_counts_ones`), not proved.
`Src.gcd a b` is `Nat.gcd` of the unsigned readings.
-/

namespace Silmaril.Wasm.Examples.CAdder

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Post exec)
open Silmaril.Wasm.Logic.Hoare (HWP Wp Corr)
open Silmaril.Wasm.Examples.Common (Wp.exec_eq)

/-! ## The C source, on `BitVec 32` -/

namespace Src

/-- `(uint32_t)a + (uint32_t)b`. -/
def add (a b : BitVec 32) : BitVec 32 := a + b
/-- `(uint32_t)a * (uint32_t)b`. -/
def mul (a b : BitVec 32) : BitVec 32 := a * b
/-- `a < b ? b : a` on `int32_t`. -/
def max (a b : BitVec 32) : BitVec 32 := if a.toInt < b.toInt then b else a
/-- `(uint32_t)a * 2u + 1u`. -/
def odd (a : BitVec 32) : BitVec 32 := a * 2 + 1
/-- The number of set bits of `x` (what Kernighan's loop in the source counts). -/
def popcount (x : BitVec 32) : BitVec 32 := x.cpop
/-- Euclid's algorithm on `uint32_t`: the greatest common divisor, `gcd(0, 0) = 0`. -/
def gcd (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)

end Src

/-- The value the C source computes for export `j` (`add`, `mul`, `max`, `odd`, `popcount`,
`gcd`, in export order) on `args`. -/
def expected : Nat → List Val → Option (BitVec 32)
  | 0, [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (Src.add a b)
  | 1, [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (Src.mul a b)
  | 2, [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (Src.max a b)
  | 3, [.num ⟨.int .i32, a⟩] => some (Src.odd a)
  | 4, [.num ⟨.int .i32, a⟩] => some (Src.popcount a)
  | 5, [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (Src.gcd a b)
  | _, _ => none

/-! ## The compiled code agrees with the source -/

/-- `max`: `select` on `a >s b` is the source's `a < b ? b : a`. -/
theorem select_gtS (a b : BitVec 32) :
    (if intRelOp .i32 (.gt .signed) a b ≠ 0 then a else b) = Src.max a b := by
  have hc : intRelOp .i32 (.gt .signed) a b ≠ 0 ↔ b.toInt < a.toInt := by
    show bool32 (decide (a.toInt > b.toInt)) ≠ 0 ↔ _
    rw [Silmaril.Wasm.Logic.Core.bool32_ne_zero_iff, decide_eq_true_iff]
  rw [Src.max]
  by_cases h₁ : b.toInt < a.toInt
  · have h₂ : ¬ a.toInt < b.toInt := by omega
    simp only [hc.2 h₁, h₂, ne_eq, not_false_eq_true, ↓reduceIte]
  · by_cases h₂ : a.toInt < b.toInt
    · simp only [mt hc.1 h₁, h₂, ↓reduceIte]
    · have he : a = b := BitVec.toInt_inj.1 (by omega)
      subst he
      simp only [ite_self]

/-- `odd`: `(a << 1) | 1` is the source's `a * 2 + 1`. -/
theorem shl_or_one (a : BitVec 32) : (a <<< (1#32 % 32)) ||| 1 = Src.odd a := by
  have h₁ : a <<< (1#32 % 32) = a <<< 1 := rfl
  have h₂ : a <<< 1 = a * 2 := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    rfl
  have h₃ : (a * 2) &&& 1 = 0 := by
    rw [← h₂]
    ext i hi
    rcases i with _ | i <;> simp [BitVec.getElem_one]
  rw [h₁, h₂, Src.odd, BitVec.add_eq_or_of_and_eq_zero _ _ h₃]

/-! ## Symbolic execution of the straight-line bodies -/

/-- The frame of a call on two `i32` arguments, without declared locals. -/
def frame2 (x y : BitVec 32) : Frame := ⟨[some (.i32 x), some (.i32 y)], adderMI⟩

/-- The frame of a call on one `i32` argument. -/
def frame1 (x : BitVec 32) : Frame := ⟨[some (.i32 x)], adderMI⟩

theorem exec_add (s : Store Nat) (x y : BitVec 32) :
    exec s (frame2 x y) [] body0 = some (s, frame2 x y, [.i32 (y + x)]) := rfl

theorem exec_mul (s : Store Nat) (x y : BitVec 32) :
    exec s (frame2 x y) [] body1 = some (s, frame2 x y, [.i32 (y * x)]) := rfl

theorem exec_max (s : Store Nat) (x y : BitVec 32) :
    exec s (frame2 x y) [] (body2.take 5) =
      some (s, frame2 x y, [.i32 (intRelOp .i32 (.gt .signed) x y), .i32 y, .i32 x]) := rfl

theorem exec_odd (s : Store Nat) (x : BitVec 32) :
    exec s (frame1 x) [] body3 = some (s, frame1 x, [.i32 ((x <<< (1#32 % 32)) ||| 1)]) := rfl

theorem exec_popcount (s : Store Nat) (x : BitVec 32) :
    exec s (frame1 x) [] body4 = some (s, frame1 x, [.i32 x.cpop]) := rfl

variable {m : Corr} {P : Profile} {host : HostSemantics Nat}

/-- A straight-line body evaluating to `rs` (top first) ends with `rs.reverse`, store
unchanged. -/
theorem wp_of_exec {s : Store Nat} {F : Frame} {is : List Instr} {rs : List Val} {Q : Post Nat}
    (he : exec s F [] is = some (s, F, rs)) (hQ : Q s F (.normal rs.reverse)) :
    Wp m P host s F (expression is) Q := by
  have h := Wp.exec_eq (m := m) (P := P) (host := host) (vs := []) (rest := []) (Q := Q) he
    (by simpa using Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := m) hQ)
  simpa using h

theorem add_wp (s : Store Nat) (x y : BitVec 32) {Q : Post Nat}
    (hQ : Q s (frame2 x y) (.normal [.i32 (Src.add x y)])) :
    Wp m P host s (frame2 x y) (expression body0) Q :=
  wp_of_exec (Q := Q) (exec_add s x y) (by rw [Src.add, BitVec.add_comm] at hQ; exact hQ)

theorem mul_wp (s : Store Nat) (x y : BitVec 32) {Q : Post Nat}
    (hQ : Q s (frame2 x y) (.normal [.i32 (Src.mul x y)])) :
    Wp m P host s (frame2 x y) (expression body1) Q :=
  wp_of_exec (Q := Q) (exec_mul s x y) (by rw [Src.mul, BitVec.mul_comm] at hQ; exact hQ)

theorem odd_wp (s : Store Nat) (x : BitVec 32) {Q : Post Nat}
    (hQ : Q s (frame1 x) (.normal [.i32 (Src.odd x)])) :
    Wp m P host s (frame1 x) (expression body3) Q :=
  wp_of_exec (Q := Q) (exec_odd s x) (by rw [← shl_or_one] at hQ; exact hQ)

theorem popcount_wp (s : Store Nat) (x : BitVec 32) {Q : Post Nat}
    (hQ : Q s (frame1 x) (.normal [.i32 (Src.popcount x)])) :
    Wp m P host s (frame1 x) (expression body4) Q :=
  wp_of_exec (Q := Q) (exec_popcount s x) hQ

theorem max_wp (s : Store Nat) (x y : BitVec 32) {Q : Post Nat}
    (hQ : Q s (frame2 x y) (.normal [.i32 (Src.max x y)])) :
    Wp m P host s (frame2 x y) (expression body2) Q := by
  have hsplit : expression body2 = expression (body2.take 5) ++ [.plain (.select none)] := rfl
  rw [hsplit]
  refine Wp.exec_eq (m := m) (vs := []) (exec_max s x y) ?_
  have hq := select_gtS x y
  by_cases hc : intRelOp .i32 (.gt .signed) x y = 0
  · rw [hc] at hq ⊢
    simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hq
    have hk : Wp m P host s (frame2 x y) (vals [.i32 y]) Q :=
      Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := m) (vs := [.i32 y])
        (by rw [show Val.i32 y = Val.i32 (Src.max x y) from congrArg Val.i32 hq]; exact hQ)
    exact Silmaril.Wasm.Logic.Hoare.Wp.selectFalse (us := []) (rest := []) (by simpa using hk)
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte] at hq
    have hk : Wp m P host s (frame2 x y) (vals [.i32 x]) Q :=
      Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := m) (vs := [.i32 x])
        (by rw [show Val.i32 x = Val.i32 (Src.max x y) from congrArg Val.i32 hq]; exact hQ)
    exact Silmaril.Wasm.Logic.Hoare.Wp.selectTrue (us := []) (rest := []) hc (by simpa using hk)

end Silmaril.Wasm.Examples.CAdder
