module

public import Silmaril.Compiler.Core.Verified.PrintLink.Defs
public import Silmaril.Compiler.Core.Verified.IntExprLir.Defs
/-! # Runtime integer expressions in the printf output buffer

The integer expression is compiled into registers above the output routine's
working registers. Its result is moved into the decimal routine's input register;
the existing output buffer and length survive expression evaluation. This is
an append operation, so literal prefixes, suffixes and earlier statements compose.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintExpr

open Silmaril.Machine Silmaril.Compile
open PrintLink

/-- Evaluate the expression at run time, then append its signed decimal digits.
Register 3 contains the expression's input local; registers 24 and above are scratch. -/
def decimalOps (t : IntExpr.Term) : List Op :=
  t.ops 24 ++ [.move rVal 24] ++ PrintLink.decimalOps

/-- The expression evaluator preserves every register of the buffer invariant. -/
theorem inv_below {size : Nat} {fr fr' : Lir.Frame Mir.Reg} {m : Lir.Memory}
    {out : List UInt8} (inv : Inv size fr m out)
    (keep : ∀ r : Nat, r < 24 → fr'.get r = fr.get r) : Inv size fr' m out := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, inv.buf, inv.size⟩
  · rw [keep rBase (by decide)]; exact inv.regs.base
  · rw [keep rLen (by decide)]; exact inv.regs.len
  · rw [keep rOne (by decide)]; exact inv.regs.one
  · rw [keep rZero (by decide)]; exact inv.regs.zero
  · rw [keep rTen (by decide)]; exact inv.regs.ten
  · rw [keep rChar0 (by decide)]; exact inv.regs.char0

/-- A valid signed-int expression is evaluated and printed at run time, preserving
all prior output. The source proof may take its UB arm before requiring validity. -/
theorem decimal_exec {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}
    (inv : Inv size fr m out) (room : outBase + out.length + 11 ≤ size) (hs : size < 2 ^ 64)
    {n : Int} {t : IntExpr.Term} (ok : t.Ok n) (range : ConvInt.IsInt (t.val n))
    (input : fr.get 3 = some (BitVec.ofInt 64 n)) (os : List Op) :
    ∃ fr' m', Lir.execOps (decimalOps t ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ Item.render (.int (t.val n))) := by
  obtain ⟨fr₁, w, run, get, value, keep⟩ := IntExpr.Term.ops_exec t 24 (by decide) fr m input
  rw [value ok] at get
  have inv₁ := inv_below inv keep
  have inv₂ : Inv size (fr₁.set rVal (BitVec.ofInt 64 (t.val n))) m out :=
    inv_set inv₁ (by decide) _
  have small : (t.val n).natAbs < 10 ^ 10 := by
    obtain ⟨lo, hi⟩ := range
    omega
  obtain ⟨fr₂, m₂, run₂, inv₃⟩ := PrintLink.decimal_exec inv₂ room hs small
    (get_set_eq _ _ _) os
  refine ⟨fr₂, m₂, ?_, inv₃⟩
  simp only [decimalOps, List.append_assoc, Lir.execOps_append, run, Option.bind_some]
  simpa only [Lir.execOps_cons, Lir.execOps_nil, Lir.execOps_append, Lir.Op.exec, get,
    Option.map_some, Option.bind_some] using run₂

/-- Closed State expressions use zero as the unused input local. Setting it also
preserves the buffer invariant. -/
def closedDecimalOps (t : IntExpr.Term) : List Op :=
  .const 3 0 :: decimalOps t

theorem closedDecimal_exec {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory}
    {out : List UInt8} (inv : Inv size fr m out) (room : outBase + out.length + 11 ≤ size)
    (hs : size < 2 ^ 64) {t : IntExpr.Term} (ok : t.Ok 0) (range : ConvInt.IsInt (t.val 0))
    (os : List Op) :
    ∃ fr' m', Lir.execOps (closedDecimalOps t ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ Item.render (.int (t.val 0))) := by
  obtain ⟨fr', m', run, post⟩ := decimal_exec (inv_set inv (r := 3) (by decide) 0) room hs ok range
    (by simp) os
  exact ⟨fr', m', by simpa [closedDecimalOps, Lir.execOps, Lir.Op.exec] using run, post⟩

end Silmaril.Compile.Core.Verified.PrintExpr
