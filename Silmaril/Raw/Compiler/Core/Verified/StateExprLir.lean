module

public import Silmaril.Compiler.Core.Verified.StateExpr.Defs
public import Silmaril.Compiler.Core.Verified.IntExprLir.Defs

/-! # Runtime expressions and assignments over several integer locals

Unlike closing a statement sequence by substitution, this code reads the current
local registers on every execution. Locals lie below the temporary register base.
The proofs are parametric in their current values and the entire linear memory.
No source execution is used by the translator.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateExprLir

open Silmaril.Machine
open StateExpr (Key Term)
open IntExpr (bitop bitop_eval binop lirCond binop_eval binop_some lirCond_eval select_cmp select_cond
  ofInt_eq_zero get_below)

/-- The code of `t` into register `d`. -/
def ops (regs : Key → Mir.Reg) (d : Mir.Reg) : Term → List (Lir.Op Mir.Reg)
  | .lit c => [.const d (BitVec.ofInt 64 c)]
  | .var q => [.move d (regs q)]
  | .bin op a b => ops regs d a ++ ops regs (d + 1) b ++ [.binary (binop op) d d (d + 1)]
  | .cmp r c₁ c₂ a b => ops regs d a ++ ops regs (d + 1) b ++
      [.binary (.cmp (lirCond r)) d d (d + 1), .const (d + 1) (BitVec.ofInt 64 (c₁ - c₂)),
        .binary .mul d d (d + 1), .const (d + 1) (BitVec.ofInt 64 c₂), .binary .add d d (d + 1)]
  | .cond c a b => ops regs d c ++ ops regs (d + 1) a ++ ops regs (d + 2) b ++
      [.unary .eqz d d, .binary .sub (d + 1) (d + 1) (d + 2), .binary .mul d d (d + 1),
        .binary .add d d (d + 2)]
  | .un u a => ops regs d a ++ [.const (d + 1) (BitVec.ofInt 64 u.base),
      .binary .sub d (d + 1) d]
  | .bit o a b => ops regs d a ++ ops regs (d + 1) b ++ [.binary (bitop o) d d (d + 1)]
  | .divpos o q a => ops regs d a ++ [.const (d + 1) (BitVec.ofNat 64 q.val),
      .binary o.lir d d (d + 1)]


/-- Expression code always executes when its reads are defined below the temporary base.
It leaves the correct word when the source expression is in range, and preserves memory
and every register below the base, including all locals. -/
theorem ops_exec (regs : Key → Mir.Reg) (σ : Key → Int) :
    (t : Term) → (d : Nat) → (fr : Lir.Frame Mir.Reg) → (mem : Lir.Memory) →
    (∀ q ∈ t.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q))) →
    ∃ fr' w, Lir.execOps (ops regs d t) fr mem = some (fr', mem) ∧ fr'.get d = some w ∧
      (t.Ok σ → w = BitVec.ofInt 64 (t.val σ)) ∧ ∀ r : Nat, r < d → fr'.get r = fr.get r
  | .lit c, d, fr, mem, _ =>
    ⟨fr.set d (BitVec.ofInt 64 c), BitVec.ofInt 64 c, by simp [ops, Lir.execOps, Lir.Op.exec], by simp,
      fun _ => by simp [Term.val], fun r hr => get_below hr _⟩
  | .var q, d, fr, mem, reads => by
    have read := (reads q (by simp [Term.vars])).2
    exact ⟨fr.set d (BitVec.ofInt 64 (σ q)), BitVec.ofInt 64 (σ q),
      by simp [ops, Lir.execOps, Lir.Op.exec, read], by simp,
      fun _ => rfl, fun r hr => IntExpr.get_below hr _⟩
  | .bin op a b, d, fr, mem, reads => by
    have ra : ∀ q ∈ a.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    have rb : ∀ q ∈ b.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    obtain ⟨fr₁, w₁, x₁, g₁, v₁, p₁⟩ := ops_exec regs σ a d fr mem ra
    obtain ⟨fr₂, w₂, x₂, g₂, v₂, p₂⟩ := ops_exec regs σ b (d + 1) fr₁ mem (by
      intro q hq
      exact ⟨Nat.lt_succ_of_lt (rb q hq).1, by rw [p₁ _ (rb q hq).1]; exact (rb q hq).2⟩)
    have gd : fr₂.get d = some w₁ := by rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    obtain ⟨z, hz⟩ := binop_some op w₁ w₂
    refine ⟨fr₂.set d z, z, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [ops, Lir.execOps_append, x₁, Option.bind_some, x₂]
      simp [Lir.execOps, Lir.Op.exec, gd, g₂, hz]
    · obtain ⟨ok₁, ok₂, -⟩ := ok
      rw [v₁ ok₁, v₂ ok₂, binop_eval] at hz
      exact (Option.some.inj hz).symm
    · rw [get_below hr, p₂ r (Nat.lt_succ_of_lt hr), p₁ r hr]
  | .cmp rl c₁ c₂ a b, d, fr, mem, reads => by
    have ra : ∀ q ∈ a.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    have rb : ∀ q ∈ b.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    obtain ⟨fr₁, w₁, x₁, g₁, v₁, p₁⟩ := ops_exec regs σ a d fr mem ra
    obtain ⟨fr₂, w₂, x₂, g₂, v₂, p₂⟩ := ops_exec regs σ b (d + 1) fr₁ mem (by
      intro q hq
      exact ⟨Nat.lt_succ_of_lt (rb q hq).1, by rw [p₁ _ (rb q hq).1]; exact (rb q hq).2⟩)
    have gd : fr₂.get d = some w₁ := by rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    let f := Lir.ofBool ((lirCond rl).eval w₁ w₂)
    let K := BitVec.ofInt 64 (c₁ - c₂)
    let C := BitVec.ofInt 64 c₂
    refine ⟨((((fr₂.set d f).set (d + 1) K).set d (f * K)).set (d + 1) C).set d (f * K + C),
      f * K + C, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [ops, Lir.execOps_append, x₁, Option.bind_some, x₂]
      simp [Lir.execOps, Lir.Op.exec, gd, g₂, Lir.Binop.eval, f, K, C]
    · obtain ⟨ok₁, ok₂, -, -⟩ := ok
      simp only [f, K, C, v₁ ok₁, v₂ ok₂, lirCond_eval rl (Term.int_of_ok a ok₁) (Term.int_of_ok b ok₂),
        select_cmp, Term.val, Guard.compare]
    · have r1 : r < d + 1 := Nat.lt_succ_of_lt hr
      rw [get_below hr, get_below r1, get_below hr, get_below r1, get_below hr,
        p₂ r r1, p₁ r hr]
  | .cond c a b, d, fr, mem, reads => by
    have rc : ∀ q ∈ c.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    have ra : ∀ q ∈ a.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    have rb : ∀ q ∈ b.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    obtain ⟨fr₁, wc, x₁, g₁, v₁, p₁⟩ := ops_exec regs σ c d fr mem rc
    obtain ⟨fr₂, wa, x₂, g₂, v₂, p₂⟩ := ops_exec regs σ a (d + 1) fr₁ mem (by
      intro q hq
      exact ⟨Nat.lt_succ_of_lt (ra q hq).1, by rw [p₁ _ (ra q hq).1]; exact (ra q hq).2⟩)
    obtain ⟨fr₃, wb, x₃, g₃, v₃, p₃⟩ := ops_exec regs σ b (d + 2) fr₂ mem (by
      intro q hq
      have bound := (rb q hq).1
      exact ⟨Nat.lt_succ_of_lt (Nat.lt_succ_of_lt bound),
        by rw [p₂ _ (Nat.lt_succ_of_lt bound), p₁ _ bound]; exact (rb q hq).2⟩)
    have gc : fr₃.get d = some wc := by rw [p₃ d (by omega), p₂ d (by omega)]; exact g₁
    have ga : fr₃.get (d + 1) = some wa := by rw [p₃ (d + 1) (by omega)]; exact g₂
    let f := Lir.ofBool (wc == 0)
    refine ⟨(((fr₃.set d f).set (d + 1) (wa - wb)).set d (f * (wa - wb))).set d
      (f * (wa - wb) + wb), f * (wa - wb) + wb, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [ops, Lir.execOps_append, x₁, Option.bind_some, x₂, x₃]
      simp [Lir.execOps, Lir.Op.exec, gc, ga, g₃, Lir.Binop.eval, Lir.Unop.eval, f]
    · obtain ⟨okc, okb⟩ := ok
      have hcv := Term.int_of_ok c okc
      simp only [f, select_cond, v₁ okc, ofInt_eq_zero hcv, Term.val]
      by_cases h0 : c.val σ = 0
      · rw [ite_eq_left h0] at okb
        simp [h0, v₂ okb]
      · rw [ite_eq_right h0] at okb
        simp [h0, v₃ okb]
    · have r1 : r < d + 1 := by omega
      have r2 : r < d + 2 := by omega
      rw [get_below hr, get_below hr, get_below r1, get_below hr, p₃ r r2, p₂ r r1, p₁ r hr]


  | .un u a, d, fr, mem, reads => by
    obtain ⟨fr₁, w, x, g, v, p⟩ := ops_exec regs σ a d fr mem reads
    let c := BitVec.ofInt 64 u.base
    refine ⟨(fr₁.set (d + 1) c).set d (c - w), c - w, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp [ops, Lir.execOps_append, x, Lir.execOps, Lir.Op.exec, g, Lir.Binop.eval, c]
    · rw [v ok.1]
      simp [c, Term.val, Unary.Unop.apply, Int.sub_eq_add_neg, BitVec.ofInt_add,
        BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
    · rw [get_below hr, get_below (Nat.lt_succ_of_lt hr), p r hr]
  | .bit o a b, d, fr, mem, reads => by
    have ra : ∀ q ∈ a.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    have rb : ∀ q ∈ b.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) :=
      fun q hq => reads q (by simp [Term.vars, hq])
    obtain ⟨fr₁, w₁, x₁, g₁, v₁, p₁⟩ := ops_exec regs σ a d fr mem ra
    obtain ⟨fr₂, w₂, x₂, g₂, v₂, p₂⟩ := ops_exec regs σ b (d + 1) fr₁ mem (by
      intro q hq
      exact ⟨Nat.lt_succ_of_lt (rb q hq).1, by rw [p₁ _ (rb q hq).1]; exact (rb q hq).2⟩)
    have gd : fr₂.get d = some w₁ := by rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    obtain ⟨z, hz⟩ : ∃ z, (bitop o).eval w₁ w₂ = some z := by
      cases o <;> simp [bitop, Lir.Binop.eval]
    refine ⟨fr₂.set d z, z, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [ops, Lir.execOps_append, x₁, Option.bind_some, x₂]
      simp [Lir.execOps, Lir.Op.exec, gd, g₂, hz]
    · obtain ⟨ok₁, ok₂⟩ := ok
      rw [v₁ ok₁, v₂ ok₂, bitop_eval] at hz
      exact (Option.some.inj hz).symm
    · rw [get_below hr, p₂ r (Nat.lt_succ_of_lt hr), p₁ r hr]


  | .divpos o q a, d, fr, mem, reads => by
    obtain ⟨fr₁, w, ex, get, val, below⟩ := ops_exec regs σ a d fr mem reads
    obtain ⟨z, hz⟩ := DivRem.lir_some o w q
    let fr₂ := fr₁.set (d + 1) (BitVec.ofNat 64 q.val)
    refine ⟨fr₂.set d z, z, ?_, by simp, fun ok => ?_, fun r hr => ?_⟩
    · simp only [ops, Lir.execOps_append, ex, Option.bind_some]
      simp [Lir.execOps, Lir.Op.exec, fr₂, get_below (by omega : d < d + 1), get, hz]
    · rw [val ok, DivRem.lir_eval o (Term.int_of_ok a ok)] at hz
      exact (Option.some.inj hz).symm
    · rw [get_below hr, get_below (by omega : r < d + 1), below r hr]

/-- Evaluate a right-hand side, then update its local register at run time. -/
def assignOps (regs : Key → Mir.Reg) (d : Nat) (q : Key) (t : Term) : List (Lir.Op Mir.Reg) :=
  ops regs d t ++ [.move (regs q) d]

/-- Assignment preserves memory and every other register below the temporary base.
The destination may also occur in the right-hand side. -/
theorem assignOps_exec (regs : Key → Mir.Reg) (σ : Key → Int) (d : Nat) (q : Key) (t : Term)
    (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory) (ok : t.Ok σ)
    (reads : ∀ k ∈ t.vars, regs k < d ∧ fr.get (regs k) = some (BitVec.ofInt 64 (σ k))) :
    ∃ fr', Lir.execOps (assignOps regs d q t) fr mem = some (fr', mem) ∧
      fr'.get (regs q) = some (BitVec.ofInt 64 (t.val σ)) ∧
      ∀ r < d, r ≠ regs q → fr'.get r = fr.get r := by
  obtain ⟨f, w, exec, result, value, below⟩ := ops_exec regs σ t d fr mem reads
  rw [value ok] at result
  refine ⟨f.set (regs q) (BitVec.ofInt 64 (t.val σ)), ?_, by simp, ?_⟩
  · simp [assignOps, Lir.execOps_append, exec, Lir.execOps, Lir.Op.exec, result]
  · intro r hr ne
    simp only [Lir.Frame.get_set, ite_eq_right ne]
    exact below r hr

end Silmaril.Compile.Core.Verified.StateExprLir
