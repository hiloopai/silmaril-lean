module

public import Silmaril.Compiler.Core.Verified.IntExpr.Defs
public import Silmaril.Compiler.Core.Verified.OpsLink.Defs
public import Silmaril.Compiler.Core.Verified.Arith.Defs

/-! # `int` expressions over one local, in Lir registers

`t.ops d` computes the expression `t` into register `d`, the local in register 3 and the
temporaries in the registers above `d`: a literal is a `const`, a read of the local a `move`
from register 3, `e₁ op e₂` the code of `e₁` into `d`, of `e₂` into `d + 1`, then the 64-bit
`add`/`sub`/`mul` of the two. A comparison is the 64-bit signed `cmp` of its operands (`0` or
`1`), then `c₂ + (c₁ - c₂) * cmp`. A conditional `c == 0 ? a : b` computes `c`, `a` and `b`
(they only read), then `b + (a - b) * (c == 0)`: no branch. `e₁ & e₂` (and `|`, `^`) is the
64-bit `and` (`or`, `xor`) of the operands, the word of the integer operation (`Bitwise`).

`ops_exec`: the code runs without getting stuck and without touching memory, leaves a word in
`d` and every register below `d` unchanged; when `t.Ok n` the word is the one of `t.val n`.
On 64-bit words `+`, `-`, `*` are the integer operators modulo `2^64`, and comparisons of
words of `int`s are the comparisons of the `int`s; Core only fixes the result when `t.Ok n`
(`IntExpr.term_runs`) and allows anything otherwise (`IntExpr.term_fails`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.IntExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Machine
open ConvInt (IsInt)

/-- The Lir operator of an operator of the fragment. -/
def binop : IntOp → Lir.Binop
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | _ => .add

/-- The Lir operator of a bitwise operator. -/
def bitop : Bitwise.Op → Lir.Binop
  | .and => .and
  | .or => .or
  | .xor => .xor

theorem bitop_eval (o : Bitwise.Op) (x y : Int) :
    (bitop o).eval (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) =
      some (BitVec.ofInt 64 (o.apply x y)) := by
  cases o <;> simp [bitop, Lir.Binop.eval, Bitwise.Op.apply, Bitwise.ofInt_land, Bitwise.ofInt_lor,
    Bitwise.ofInt_xor]

/-- The signed Lir condition of a relation (equality for the operators that are none). -/
def lirCond : BinOp → Lir.Cond
  | .lt => .lts
  | .le => .les
  | .gt => .gts
  | .ge => .ges
  | _ => .eq

/-- The code of `t` into register `d`. -/
def Term.ops (d : Mir.Reg) : Term → List (Lir.Op Mir.Reg)
  | .lit c => [.const d (BitVec.ofInt 64 c)]
  | .var => [.move d 3]
  | .bin op a b => a.ops d ++ b.ops (d + 1) ++ [.binary (binop op) d d (d + 1)]
  | .cmp r c₁ c₂ a b => a.ops d ++ b.ops (d + 1) ++
      [.binary (.cmp (lirCond r)) d d (d + 1), .const (d + 1) (BitVec.ofInt 64 (c₁ - c₂)),
        .binary .mul d d (d + 1), .const (d + 1) (BitVec.ofInt 64 c₂), .binary .add d d (d + 1)]
  | .cond c a b => c.ops d ++ a.ops (d + 1) ++ b.ops (d + 2) ++
      [.unary .eqz d d, .binary .sub (d + 1) (d + 1) (d + 2), .binary .mul d d (d + 1),
        .binary .add d d (d + 2)]
  | .bit o a b => a.ops d ++ b.ops (d + 1) ++ [.binary (bitop o) d d (d + 1)]
  | .divpos o q a => a.ops d ++ [.const (d + 1) (BitVec.ofNat 64 q.val),
      .binary o.lir d d (d + 1)]

theorem binop_eval (op : IntOp) (x y : Int) :
    (binop op).eval (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) =
      some (BitVec.ofInt 64 (Guard.apply op x y)) := by
  cases op <;> simp only [binop, Lir.Binop.eval, Guard.apply]
  all_goals first
    | rw [BitVec.ofInt_add]
    | rw [BitVec.ofInt_mul]
    | rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, ← BitVec.sub_eq_add_neg]

theorem binop_some (op : IntOp) (x y : Lir.Word) : ∃ z, (binop op).eval x y = some z := by
  cases op <;> simp [binop, Lir.Binop.eval]

/-- On words of `int`s the signed condition is the relation. -/
theorem lirCond_eval (r : BinOp) {x y : Int} (hx : IsInt x) (hy : IsInt y) :
    (lirCond r).eval (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = Guard.holds r x y := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have ex := Arith.toInt_ofInt_of_fits (v := x) (by omega) (by omega)
  have ey := Arith.toInt_ofInt_of_fits (v := y) (by omega) (by omega)
  cases r <;> simp [lirCond, Lir.Cond.eval, Guard.holds, ex, ey, ← BitVec.toInt_inj]

/-- The result of a comparison from its flag. -/
theorem select_cmp (b : Bool) (c₁ c₂ : Int) :
    Lir.ofBool b * BitVec.ofInt 64 (c₁ - c₂) + BitVec.ofInt 64 c₂ =
      BitVec.ofInt 64 (if b then c₁ else c₂) := by
  cases b
  · simp [Lir.ofBool]
  · simp only [Lir.ofBool, ite_true]
    rw [show (1 : Lir.Word) * BitVec.ofInt 64 (c₁ - c₂) = BitVec.ofInt 64 (c₁ - c₂) from
      BitVec.one_mul _, ← BitVec.ofInt_add, Int.sub_add_cancel]

/-- The result of a conditional from its flag. -/
theorem select_cond (b : Bool) (wa wb : Lir.Word) :
    Lir.ofBool b * (wa - wb) + wb = if b then wa else wb := by
  cases b <;> simp [Lir.ofBool]

/-- The word of an `int` is zero exactly when the `int` is. -/
theorem ofInt_eq_zero {v : Int} (hv : IsInt v) : (BitVec.ofInt 64 v == 0) = decide (v = 0) := by
  obtain ⟨h1, h2⟩ := hv
  have ev := Arith.toInt_ofInt_of_fits (v := v) (by omega) (by omega)
  by_cases h : v = 0
  · subst h; decide
  · have : BitVec.ofInt 64 v ≠ 0 := by
      intro h0
      rw [h0] at ev
      exact h (by simpa using ev.symm)
    simp only [h, decide_false, beq_eq_false_iff_ne]
    exact this

theorem get_below {fr : Lir.Frame Mir.Reg} {r d : Nat} (hr : r < d) (w : Lir.Word) :
    (fr.set d w).get r = fr.get r := by
  have hne : r ≠ d := Nat.ne_of_lt hr
  simp [hne]

/-- **The code of `t`** runs from every frame holding the word of `n` in register 3, leaves a
word in `d` (the one of `t.val n` when `t.Ok n`) and the registers below `d` as they were. -/
theorem Term.ops_exec {n : Int} : (t : Term) → (d : Nat) → 4 ≤ d →
    (fr : Lir.Frame Mir.Reg) → (mem : Lir.Memory) → fr.get 3 = some (BitVec.ofInt 64 n) →
    ∃ fr' w, Lir.execOps (t.ops d) fr mem = some (fr', mem) ∧ fr'.get d = some w ∧
      (t.Ok n → w = BitVec.ofInt 64 (t.val n)) ∧ ∀ r : Nat, r < d → fr'.get r = fr.get r
  | .lit c, d, _, fr, mem, _ =>
    ⟨fr.set d (BitVec.ofInt 64 c), BitVec.ofInt 64 c, by simp [Term.ops, Lir.execOps, Lir.Op.exec], by simp,
      fun _ => by simp [Term.val], fun r hr => get_below hr _⟩
  | .var, d, hd, fr, mem, h3 =>
    ⟨fr.set d (BitVec.ofInt 64 n), BitVec.ofInt 64 n, by simp [Term.ops, Lir.execOps, Lir.Op.exec, h3], by simp,
      fun _ => by simp [Term.val], fun r hr => get_below hr _⟩
  | .bin op a b, d, hd, fr, mem, h3 => by
    have h3d : (3 : Nat) < d := Nat.lt_of_lt_of_le (by decide) hd
    obtain ⟨fr₁, w₁, x₁, g₁, v₁, p₁⟩ := Term.ops_exec a d hd fr mem h3
    obtain ⟨fr₂, w₂, x₂, g₂, v₂, p₂⟩ := Term.ops_exec b (d + 1) (Nat.le_succ_of_le hd) fr₁ mem
      (by rw [p₁ 3 h3d]; exact h3)
    have gd : fr₂.get d = some w₁ := by rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    obtain ⟨z, hz⟩ := binop_some op w₁ w₂
    refine ⟨fr₂.set d z, z, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [Term.ops, Lir.execOps_append, x₁, Option.bind_some, x₂]
      simp [Lir.execOps, Lir.Op.exec, gd, g₂, hz]
    · obtain ⟨ok₁, ok₂, -⟩ := ok
      rw [v₁ ok₁, v₂ ok₂, binop_eval] at hz
      exact (Option.some.inj hz).symm
    · rw [get_below hr, p₂ r (Nat.lt_succ_of_lt hr), p₁ r hr]
  | .cmp rl c₁ c₂ a b, d, hd, fr, mem, h3 => by
    have h3d : (3 : Nat) < d := Nat.lt_of_lt_of_le (by decide) hd
    obtain ⟨fr₁, w₁, x₁, g₁, v₁, p₁⟩ := Term.ops_exec a d hd fr mem h3
    obtain ⟨fr₂, w₂, x₂, g₂, v₂, p₂⟩ := Term.ops_exec b (d + 1) (Nat.le_succ_of_le hd) fr₁ mem
      (by rw [p₁ 3 h3d]; exact h3)
    have gd : fr₂.get d = some w₁ := by rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    let f := Lir.ofBool ((lirCond rl).eval w₁ w₂)
    let K := BitVec.ofInt 64 (c₁ - c₂)
    let C := BitVec.ofInt 64 c₂
    refine ⟨((((fr₂.set d f).set (d + 1) K).set d (f * K)).set (d + 1) C).set d (f * K + C),
      f * K + C, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [Term.ops, Lir.execOps_append, x₁, Option.bind_some, x₂]
      simp [Lir.execOps, Lir.Op.exec, gd, g₂, Lir.Binop.eval, f, K, C]
    · obtain ⟨ok₁, ok₂, -, -⟩ := ok
      simp only [f, K, C, v₁ ok₁, v₂ ok₂, lirCond_eval rl (Term.int_of_ok a ok₁) (Term.int_of_ok b ok₂),
        select_cmp, Term.val, Guard.compare]
    · have r1 : r < d + 1 := Nat.lt_succ_of_lt hr
      rw [get_below hr, get_below r1, get_below hr, get_below r1, get_below hr,
        p₂ r r1, p₁ r hr]
  | .cond c a b, d, hd, fr, mem, h3 => by
    have h3d : (3 : Nat) < d := Nat.lt_of_lt_of_le (by decide) hd
    obtain ⟨fr₁, wc, x₁, g₁, v₁, p₁⟩ := Term.ops_exec c d hd fr mem h3
    obtain ⟨fr₂, wa, x₂, g₂, v₂, p₂⟩ := Term.ops_exec a (d + 1) (by omega) fr₁ mem
      (by rw [p₁ 3 h3d]; exact h3)
    obtain ⟨fr₃, wb, x₃, g₃, v₃, p₃⟩ := Term.ops_exec b (d + 2) (by omega) fr₂ mem
      (by rw [p₂ 3 (by omega), p₁ 3 h3d]; exact h3)
    have gc : fr₃.get d = some wc := by rw [p₃ d (by omega), p₂ d (by omega)]; exact g₁
    have ga : fr₃.get (d + 1) = some wa := by rw [p₃ (d + 1) (by omega)]; exact g₂
    let f := Lir.ofBool (wc == 0)
    refine ⟨(((fr₃.set d f).set (d + 1) (wa - wb)).set d (f * (wa - wb))).set d
      (f * (wa - wb) + wb), f * (wa - wb) + wb, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [Term.ops, Lir.execOps_append, x₁, Option.bind_some, x₂, x₃]
      simp [Lir.execOps, Lir.Op.exec, gc, ga, g₃, Lir.Binop.eval, Lir.Unop.eval, f]
    · obtain ⟨okc, okb⟩ := ok
      have hcv := Term.int_of_ok c okc
      simp only [f, select_cond, v₁ okc, ofInt_eq_zero hcv, Term.val]
      by_cases h0 : c.val n = 0
      · rw [ite_eq_left h0] at okb
        simp [h0, v₂ okb]
      · rw [ite_eq_right h0] at okb
        simp [h0, v₃ okb]
    · have r1 : r < d + 1 := by omega
      have r2 : r < d + 2 := by omega
      rw [get_below hr, get_below hr, get_below r1, get_below hr, p₃ r r2, p₂ r r1, p₁ r hr]
  | .bit o a b, d, hd, fr, mem, h3 => by
    have h3d : (3 : Nat) < d := Nat.lt_of_lt_of_le (by decide) hd
    obtain ⟨fr₁, w₁, x₁, g₁, v₁, p₁⟩ := Term.ops_exec a d hd fr mem h3
    obtain ⟨fr₂, w₂, x₂, g₂, v₂, p₂⟩ := Term.ops_exec b (d + 1) (Nat.le_succ_of_le hd) fr₁ mem
      (by rw [p₁ 3 h3d]; exact h3)
    have gd : fr₂.get d = some w₁ := by rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    obtain ⟨z, hz⟩ : ∃ z, (bitop o).eval w₁ w₂ = some z := by
      cases o <;> simp [bitop, Lir.Binop.eval]
    refine ⟨fr₂.set d z, z, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [Term.ops, Lir.execOps_append, x₁, Option.bind_some, x₂]
      simp [Lir.execOps, Lir.Op.exec, gd, g₂, hz]
    · obtain ⟨ok₁, ok₂⟩ := ok
      rw [v₁ ok₁, v₂ ok₂, bitop_eval] at hz
      exact (Option.some.inj hz).symm
    · rw [get_below hr, p₂ r (Nat.lt_succ_of_lt hr), p₁ r hr]

  | .divpos o q a, d, hd, fr, mem, h3 => by
    obtain ⟨fr₁, w, ex, get, val, below⟩ := Term.ops_exec a d hd fr mem h3
    obtain ⟨z, hz⟩ := DivRem.lir_some o w q
    let fr₂ := fr₁.set (d + 1) (BitVec.ofNat 64 q.val)
    refine ⟨fr₂.set d z, z, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [Term.ops, Lir.execOps_append, ex, Option.bind_some]
      simp [Lir.execOps, Lir.Op.exec, fr₂, get_below (by omega : d < d + 1), get, hz]
    · rw [val ok, DivRem.lir_eval o (Term.int_of_ok a ok)] at hz
      exact (Option.some.inj hz).symm
    · rw [get_below hr, get_below (by omega : r < d + 1), below r hr]

/-- The code of `int x = n; return t;`: the local in register 3, the result in register 0. -/
def exprOps (n : Int) (t : Term) : List (Lir.Op Mir.Reg) :=
  .const 3 (BitVec.ofInt 64 n) :: t.ops 4 ++ [.move 0 4]

/-- **The code of `int x = n; return t;`** leaves the word of `t.val n` in register 0 when
`t.Ok n`. -/
theorem exprOps_exec {n : Int} {t : Term} (ok : t.Ok n) (fr0 : Lir.Frame Mir.Reg)
    (mem : Lir.Memory) :
    ∃ fr, Lir.execOps (exprOps n t) fr0 mem = some (fr, mem) ∧
      fr.get 0 = some (BitVec.ofInt 64 (t.val n)) := by
  obtain ⟨fr₁, w, x₁, g₁, v₁, -⟩ := Term.ops_exec (n := n) t 4 (Nat.le_refl 4)
    (fr0.set 3 (BitVec.ofInt 64 n)) mem (by simp)
  rw [v₁ ok] at g₁
  refine ⟨fr₁.set 0 (BitVec.ofInt 64 (t.val n)), ?_, by simp⟩
  simp only [exprOps, List.cons_append, Lir.execOps_cons, Lir.Op.exec, Option.bind_some,
    Lir.execOps_append, x₁]
  simp [Lir.execOps, g₁]

end Silmaril.Compile.Core.Verified.IntExpr
