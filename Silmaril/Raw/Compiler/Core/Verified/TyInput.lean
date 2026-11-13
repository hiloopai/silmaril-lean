module

public import Silmaril.Compiler.Core.Verified.TyLir.Defs
/-! # Typed expressions with runtime inputs

`TyLir` computes closed terms. Parameter bodies must retain their inputs until runtime:
`ops` reads each symbolic input from its assigned register and reuses the proved typed
operators. Input registers are below the temporary base and survive the computation.
The theorem permits several independent inputs, with values of any integer type.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.TyInput

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Machine
open TyExpr (Key Term)

/-- Compute an open typed expression, reading variables from `regs`. -/
def ops (regs : Key → Mir.Reg) (d : Mir.Reg) : Term → List (Lir.Op Mir.Reg)
  | .lit c => [.const d (BitVec.ofInt 64 c)]
  | .var q _ => [.move d (regs q)]
  | .bin g a b | .ebin g a b => ops regs d a ++ ops regs (d + 1) b ++ TyLir.gops d g
  | .un g a => [.const d 0] ++ ops regs (d + 1) a ++ TyLir.gops d g

/-- Only the variables actually read need registers. Different variables may share a
register when their values agree; no bound or injectivity of the whole map is required. -/
def Inputs (regs : Key → Mir.Reg) (σ : Key → Int) (d : Nat) (fr : Lir.Frame Mir.Reg)
    (t : Term) : Prop :=
  ∀ p ∈ t.vars, regs p.1 < d ∧ fr.get (regs p.1) = some (BitVec.ofInt 64 (σ p.1))

/-- Typed arithmetic, casts and comparisons compute the word of the open term and
preserve memory and every register below the temporary base. No source range assumption
is needed for execution; the source simulation separately discharges signed overflow. -/
theorem ops_exec (regs : Key → Mir.Reg) (σ : Key → Int) :
    (t : Term) → t.Wf → (d : Nat) → (fr : Lir.Frame Mir.Reg) → (mem : Lir.Memory) →
    Inputs regs σ d fr t →
    ∃ fr', Lir.execOps (ops regs d t) fr mem = some (fr', mem) ∧
      fr'.get d = some (BitVec.ofInt 64 (t.val σ)) ∧
      ∀ r : Nat, r < d → fr'.get r = fr.get r
  | .lit c, _, d, fr, mem, _ =>
    ⟨fr.set d (BitVec.ofInt 64 c), by simp [ops, Lir.execOps, Lir.Op.exec], by simp [Term.val],
      fun r hr => IntExpr.get_below hr _⟩
  | .var q ity, _, d, fr, mem, reads => by
    have read := (reads (q, ity) (by simp [Term.vars])).2
    exact ⟨fr.set d (BitVec.ofInt 64 (σ q)), by simp [ops, Lir.execOps, Lir.Op.exec, read],
      by simp [Term.val], fun r hr => IntExpr.get_below hr _⟩
  | .bin g a b, ⟨wg, wa, wb⟩, d, fr, mem, reads => by
    have ra : Inputs regs σ d fr a := fun q hq => reads q (by simp [Term.vars, hq])
    have rb : Inputs regs σ d fr b := fun q hq => reads q (by simp [Term.vars, hq])
    obtain ⟨fr₁, x₁, g₁, p₁⟩ := ops_exec regs σ a wa d fr mem ra
    obtain ⟨fr₂, x₂, g₂, p₂⟩ := ops_exec regs σ b wb (d + 1) fr₁ mem (by
      intro q hq
      exact ⟨Nat.lt_succ_of_lt (rb q hq).1, by rw [p₁ _ (rb q hq).1]; exact (rb q hq).2⟩)
    have gd : fr₂.get d = some (BitVec.ofInt 64 (a.val σ)) := by
      rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := TyLir.gops_exec wg d fr₂ mem gd g₂
    refine ⟨fr₃, ?_, by simpa [Term.val] using g₃, fun r hr => ?_⟩
    · simp only [ops, Lir.execOps_append, x₁, Option.bind_some, x₂]; exact x₃
    · rw [p₃ r hr, p₂ r (Nat.lt_succ_of_lt hr), p₁ r hr]
  | .ebin g a b, ⟨wg, wa, wb⟩, d, fr, mem, reads => by
    have ra : Inputs regs σ d fr a := fun q hq => reads q (by simp [Term.vars, hq])
    have rb : Inputs regs σ d fr b := fun q hq => reads q (by simp [Term.vars, hq])
    obtain ⟨fr₁, x₁, g₁, p₁⟩ := ops_exec regs σ a wa d fr mem ra
    obtain ⟨fr₂, x₂, g₂, p₂⟩ := ops_exec regs σ b wb (d + 1) fr₁ mem (by
      intro q hq
      exact ⟨Nat.lt_succ_of_lt (rb q hq).1, by rw [p₁ _ (rb q hq).1]; exact (rb q hq).2⟩)
    have gd : fr₂.get d = some (BitVec.ofInt 64 (a.val σ)) := by
      rw [p₂ d (Nat.lt_succ_self d)]; exact g₁
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := TyLir.gops_exec wg d fr₂ mem gd g₂
    refine ⟨fr₃, ?_, by simpa [Term.val] using g₃, fun r hr => ?_⟩
    · simp only [ops, Lir.execOps_append, x₁, Option.bind_some, x₂]; exact x₃
    · rw [p₃ r hr, p₂ r (Nat.lt_succ_of_lt hr), p₁ r hr]
  | .un g a, ⟨wg, wa⟩, d, fr, mem, reads => by
    let fr₀ := fr.set d (BitVec.ofInt 64 0)
    obtain ⟨fr₂, x₂, g₂, p₂⟩ := ops_exec regs σ a wa (d + 1) fr₀ mem (by
      intro q hq
      have r := reads q hq
      exact ⟨Nat.lt_succ_of_lt r.1, by rw [IntExpr.get_below r.1]; exact r.2⟩)
    have gd : fr₂.get d = some (BitVec.ofInt 64 0) := by
      rw [p₂ d (Nat.lt_succ_self d)]; simp [fr₀]
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := TyLir.gops_exec wg d fr₂ mem gd g₂
    refine ⟨fr₃, ?_, by simpa [Term.val] using g₃, fun r hr => ?_⟩
    · simp only [ops, Lir.execOps_append]
      have h0 : Lir.execOps [Lir.Op.const d 0] fr mem = some (fr₀, mem) := by
        simp [Lir.execOps, Lir.Op.exec, fr₀]
      rw [h0]; simp only [Option.bind_some, x₂]; exact x₃
    · rw [p₃ r hr, p₂ r (Nat.lt_succ_of_lt hr)]; exact IntExpr.get_below hr _

/-- Substitution of symbolic definitions is valid for arbitrary runtime inputs, extending
the closed-at-zero interface used by `TyState` and `TyRun`. -/
theorem close_val (ds : Key → Term) (σ : Key → Int) : (t : Term) →
    (TyExpr.close ds t).val σ = t.val (fun q => (ds q).val σ)
  | .lit _ | .var _ _ => rfl
  | .bin _ a b | .ebin _ a b => by simp [TyExpr.close, Term.val, close_val ds σ a, close_val ds σ b]
  | .un _ a => by simp [TyExpr.close, Term.val, close_val ds σ a]

theorem close_ok (ds : Key → Term) (σ : Key → Int) (hds : ∀ q, (ds q).Ok σ) :
    (t : Term) → t.Ok (fun q => (ds q).val σ) → (TyExpr.close ds t).Ok σ
  | .lit _, _ => trivial
  | .var q _, _ => hds q
  | .bin _ a b, h | .ebin _ a b, h => by
    exact ⟨close_ok ds σ hds a h.1, close_ok ds σ hds b h.2.1,
      by simpa only [close_val] using h.2.2⟩
  | .un _ a, h =>
    ⟨close_ok ds σ hds a h.1, by simpa only [close_val] using h.2⟩

theorem close_wf (ds : Key → Term) (hds : ∀ q, (ds q).Wf) :
    (t : Term) → t.Wf → (TyExpr.close ds t).Wf
  | .lit _, _ => trivial
  | .var q _, _ => hds q
  | .bin _ a b, h | .ebin _ a b, h => ⟨h.1, close_wf ds hds a h.2.1, close_wf ds hds b h.2.2⟩
  | .un _ a, h => ⟨h.1, close_wf ds hds a h.2⟩

/-- Store a typed expression into a mutable register slot. The source statement's
conversion is already present in the expression (`TyStmt.convT`). -/
def assign (regs : Key → Mir.Reg) (q : Key) (d : Mir.Reg) (t : Term) : List (Lir.Op Mir.Reg) :=
  ops regs d t ++ [.move (regs q) d]

theorem assign_exec (regs : Key → Mir.Reg) (σ : Key → Int) {t : Term} (wf : t.Wf)
    (q : Key) (d : Nat) (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory) (reads : Inputs regs σ d fr t) :
    ∃ fr', Lir.execOps (assign regs q d t) fr mem = some (fr', mem) ∧
      fr'.get (regs q) = some (BitVec.ofInt 64 (t.val σ)) ∧
      ∀ r : Nat, r < d → r ≠ regs q → fr'.get r = fr.get r := by
  obtain ⟨fr₁, run, value, keeps⟩ := ops_exec regs σ t wf d fr mem reads
  refine ⟨fr₁.set (regs q) (BitVec.ofInt 64 (t.val σ)), ?_, by simp, ?_⟩
  · simp [assign, Lir.execOps_append, run, Lir.execOps, Lir.Op.exec, value]
  · intro r hr hq
    rw [Lir.Frame.get_set, ite_eq_right hq, keeps r hr]

end Silmaril.Compile.Core.Verified.TyInput
