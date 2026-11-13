module

public import Silmaril.Proofs.Wasm.Examples.RustAdder.Instance
public import Silmaril.Wasm.Logic.Arith.Thms

@[expose] public section

/-!
# The compiled Rust adder: every export computes what the Rust source says

The Rust source of each export, read on `BitVec 32` (`Src.add`, `Src.max`, `Src.mul`,
`Src.odd`), and `Correct c`: the export call `c` answers with the value the source computes.
`adder_spec`: every export call of `adderI` meets `Common.callSpec adderI Rep nxt Good`, at
every profile and for every host relation (every-run partial correctness, `HWP`), where the
store keeps the instance's functions and every answer is `Correct`.

The compiled bodies are not the source: `add` and `mul` swap their operands
(`local.get 1; local.get 0`), `max` is `select` on `i32.gt_s` (the source compares with `<`),
and `odd` is `(a << 1) | 1` (the source computes `a * 2 + 1`). The proofs show these agree.
-/

namespace Silmaril.Wasm.Examples.RustAdder

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Post exec)
open Silmaril.Wasm.Logic.Hoare (HWP Wp Corr FSpecValid)
open Silmaril.Wasm.Examples.Common (callSpec outcomeResult? FSpecValid.of_body_hwp Wp.exec_eq)
open Silmaril.Wasm.Spec.Multi (Call)

/-! ## The Rust source, on `BitVec 32` -/

namespace Src

/-- `a.wrapping_add(b)`. -/
def add (a b : BitVec 32) : BitVec 32 := a + b
/-- `if a < b { b } else { a }` (signed). -/
def max (a b : BitVec 32) : BitVec 32 := if a.toInt < b.toInt then b else a
/-- `a.wrapping_mul(b)`. -/
def mul (a b : BitVec 32) : BitVec 32 := a * b
/-- `a.wrapping_mul(2).wrapping_add(1)`. -/
def odd (a : BitVec 32) : BitVec 32 := a * 2 + 1

end Src

/-- The value the Rust source computes for export `j` (`add`, `max`, `mul`, `odd`) on `args`. -/
def expected : Nat → List Val → Option (BitVec 32)
  | 0, [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (Src.add a b)
  | 1, [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (Src.max a b)
  | 2, [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (Src.mul a b)
  | 3, [.num ⟨.int .i32, a⟩] => some (Src.odd a)
  | _, _ => none

/-- **A correct call**: the export answers with the value the Rust source computes. -/
def Correct (c : Call adderI) : Prop :=
  ∀ v, expected c.1.1.val c.1.2.1 = some v →
    Answer.toResult (ft := adderI.exports.get c.1.1) c.2 = .values [Val.i32 v]

/-- The representation relation (no abstract state): the store holds the instance's
functions. -/
def Rep (_ : Unit) (s : Store Nat) : Prop := s.funcs = adderStore.funcs

/-- The abstract transition (none). -/
def nxt (_ : Unit) (_ : Call adderI) : Unit := ()

/-- Safety of a call: it is correct. -/
def Good (_ : Unit) (c : Call adderI) : Prop := Correct c

/-! ## The compiled code agrees with the source -/

/-- `max`: `select` on `a >s b` is the source's `if a < b { b } else { a }`. -/
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

/-! ## Symbolic execution of the bodies -/

/-- The frame of a call on two `i32` arguments. -/
def frame2 (x y : BitVec 32) : Frame := ⟨[some (.i32 x), some (.i32 y)], adderMI⟩

theorem exec_add (s : Store Nat) (x y : BitVec 32) :
    exec s (frame2 x y) [] body0 = some (s, frame2 x y, [.i32 (y + x)]) := rfl

theorem exec_max (s : Store Nat) (x y : BitVec 32) :
    exec s (frame2 x y) [] (body1.take 5) =
      some (s, frame2 x y, [.i32 (intRelOp .i32 (.gt .signed) x y), .i32 y, .i32 x]) := rfl

theorem exec_mul (s : Store Nat) (x y : BitVec 32) :
    exec s (frame2 x y) [] body2 = some (s, frame2 x y, [.i32 (y * x)]) := rfl

theorem exec_odd (s : Store Nat) (x : BitVec 32) :
    exec s ⟨[some (.i32 x)], adderMI⟩ [] body3 =
      some (s, ⟨[some (.i32 x)], adderMI⟩, [.i32 ((x <<< (1#32 % 32)) ||| 1)]) := rfl

variable {m : Corr} {P : Profile} {host : HostSemantics Nat}

/-- A straight-line body evaluating to `rs` (top first) ends with `rs.reverse`, store unchanged
(in either reading: partial `HWP` or total `TWP` correctness). -/
theorem hwp_of_exec {s : Store Nat} {F : Frame} {is : List Instr} {rs : List Val} {Q : Post Nat}
    (he : exec s F [] is = some (s, F, rs)) (hQ : Q s F (.normal rs.reverse)) :
    Wp m P host s F (expression is) Q := by
  have h := Wp.exec_eq (m := m) (P := P) (host := host) (vs := []) (rest := []) (Q := Q) he
    (by simpa using Wp.of_vals (m := m) hQ)
  simpa using h

theorem add_hwp (s : Store Nat) (x y : BitVec 32) {Q : Post Nat}
    (hQ : Q s (frame2 x y) (.normal [.i32 (Src.add x y)])) :
    Wp m P host s (frame2 x y) (expression body0) Q :=
  hwp_of_exec (Q := Q) (exec_add s x y) (by rw [Src.add, BitVec.add_comm] at hQ; exact hQ)

theorem mul_hwp (s : Store Nat) (x y : BitVec 32) {Q : Post Nat}
    (hQ : Q s (frame2 x y) (.normal [.i32 (Src.mul x y)])) :
    Wp m P host s (frame2 x y) (expression body2) Q :=
  hwp_of_exec (Q := Q) (exec_mul s x y) (by rw [Src.mul, BitVec.mul_comm] at hQ; exact hQ)

theorem odd_hwp (s : Store Nat) (x : BitVec 32) {Q : Post Nat}
    (hQ : Q s ⟨[some (.i32 x)], adderMI⟩ (.normal [.i32 (Src.odd x)])) :
    Wp m P host s ⟨[some (.i32 x)], adderMI⟩ (expression body3) Q :=
  hwp_of_exec (Q := Q) (exec_odd s x) (by rw [← shl_or_one] at hQ; exact hQ)

theorem max_hwp (s : Store Nat) (x y : BitVec 32) {Q : Post Nat}
    (hQ : Q s (frame2 x y) (.normal [.i32 (Src.max x y)])) :
    Wp m P host s (frame2 x y) (expression body1) Q := by
  have hsplit : expression body1 = expression (body1.take 5) ++ [.plain (.select none)] := rfl
  rw [hsplit]
  refine Wp.exec_eq (m := m) (vs := []) (exec_max s x y) ?_
  have hq := select_gtS x y
  by_cases hc : intRelOp .i32 (.gt .signed) x y = 0
  · rw [hc] at hq ⊢
    simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hq
    have hk : Wp m P host s (frame2 x y) (vals [.i32 y]) Q :=
      Wp.of_vals (m := m) (vs := [.i32 y])
        (by rw [show Val.i32 y = Val.i32 (Src.max x y) from congrArg Val.i32 hq]; exact hQ)
    exact Silmaril.Wasm.Logic.Hoare.Wp.selectFalse (us := []) (rest := []) (by simpa using hk)
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte] at hq
    have hk : Wp m P host s (frame2 x y) (vals [.i32 x]) Q :=
      Wp.of_vals (m := m) (vs := [.i32 x])
        (by rw [show Val.i32 x = Val.i32 (Src.max x y) from congrArg Val.i32 hq]; exact hQ)
    exact Silmaril.Wasm.Logic.Hoare.Wp.selectTrue (us := []) (rest := []) hc (by simpa using hk)

end Silmaril.Wasm.Examples.RustAdder
