module

public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Logic.Arith.Thms

/-!
# Simplification lemmas for verification conditions

Rewrites used by the `wat_vc` tactic (`Silmaril.Wasm.Logic.VC.Thms`) to evaluate the conditions
`wpc` produces for concrete code: the default value of an integer local, injectivity of
integer values, and signed comparisons as comparisons of `BitVec.toInt` (the unsigned ones are
in `Silmaril.Wasm.Logic.Arith.Thms`). All by `rfl` or `cases`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- The default value of an integer local. -/
theorem defaultVal_int32 (ts : List Validation.CTypeUse) :
    defaultVal? ((Validation.liftVal (.num (.int .i32))).substAll ts) =
      some (.num ⟨.int .i32, (0 : BitVec 32)⟩) := rfl

theorem defaultVal_int64 (ts : List Validation.CTypeUse) :
    defaultVal? ((Validation.liftVal (.num (.int .i64))).substAll ts) =
      some (.num ⟨.int .i64, (0 : BitVec 64)⟩) := rfl

theorem defaultVal_i32 (ts : List Validation.CTypeUse) :
    defaultVal? ((Validation.liftVal ValType.i32).substAll ts) =
      some (.num ⟨.int .i32, (0 : BitVec 32)⟩) := rfl

theorem defaultVal_i64 (ts : List Validation.CTypeUse) :
    defaultVal? ((Validation.liftVal ValType.i64).substAll ts) =
      some (.num ⟨.int .i64, (0 : BitVec 64)⟩) := rfl

theorem numVal_i32_eq (a b : BitVec 32) :
    ((⟨.int .i32, a⟩ : NumVal) = ⟨.int .i32, b⟩) ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]

theorem numVal_i64_eq (a b : BitVec 64) :
    ((⟨.int .i64, a⟩ : NumVal) = ⟨.int .i64, b⟩) ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]

section I32
variable (x y : BitVec 32)

theorem intRelOp_i32_ltS :
    intRelOp .i32 (.lt .signed) x y = bool32 (decide (x.toInt < y.toInt)) := rfl
theorem intRelOp_i32_leS :
    intRelOp .i32 (.le .signed) x y = bool32 (decide (x.toInt ≤ y.toInt)) := rfl
theorem intRelOp_i32_gtS :
    intRelOp .i32 (.gt .signed) x y = bool32 (decide (x.toInt > y.toInt)) := rfl
theorem intRelOp_i32_geS :
    intRelOp .i32 (.ge .signed) x y = bool32 (decide (x.toInt ≥ y.toInt)) := rfl

theorem intTestOp_i32 (op : IntTestOp) : intTestOp .i32 op x = bool32 (decide (x = 0#32)) := by
  simp only [intTestOp, bool32]
  rfl

end I32

section I64
variable (x y : BitVec 64)

theorem intRelOp_i64_eq : intRelOp .i64 .eq x y = bool32 (x == y) := rfl
theorem intRelOp_i64_ne : intRelOp .i64 .ne x y = bool32 (x != y) := rfl
theorem intRelOp_i64_ltU :
    intRelOp .i64 (.lt .unsigned) x y = bool32 (decide (x.toNat < y.toNat)) := rfl
theorem intRelOp_i64_leU :
    intRelOp .i64 (.le .unsigned) x y = bool32 (decide (x.toNat ≤ y.toNat)) := rfl
theorem intRelOp_i64_gtU :
    intRelOp .i64 (.gt .unsigned) x y = bool32 (decide (x.toNat > y.toNat)) := rfl
theorem intRelOp_i64_geU :
    intRelOp .i64 (.ge .unsigned) x y = bool32 (decide (x.toNat ≥ y.toNat)) := rfl
theorem intRelOp_i64_ltS :
    intRelOp .i64 (.lt .signed) x y = bool32 (decide (x.toInt < y.toInt)) := rfl
theorem intRelOp_i64_leS :
    intRelOp .i64 (.le .signed) x y = bool32 (decide (x.toInt ≤ y.toInt)) := rfl
theorem intRelOp_i64_gtS :
    intRelOp .i64 (.gt .signed) x y = bool32 (decide (x.toInt > y.toInt)) := rfl
theorem intRelOp_i64_geS :
    intRelOp .i64 (.ge .signed) x y = bool32 (decide (x.toInt ≥ y.toInt)) := rfl

theorem intTestOp_i64 (op : IntTestOp) : intTestOp .i64 op x = bool32 (decide (x = 0#64)) := by
  simp only [intTestOp, bool32]
  rfl

end I64

end Silmaril.Wasm.Logic.VC
