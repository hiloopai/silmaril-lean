module

public import Silmaril.Wasm.Lime1.FromV1

/-! # Lime1 constant-expression syntax and feature witnesses

`isConstOp` is syntactic eligibility only. Validation must separately check
operand/result types and restrict global reads to the globals allowed by the
constant-expression context. The profile's extended-const feature adds only
i32/i64 addition, subtraction and multiplication, not arbitrary numeric ops.
-/

@[expose] public section
namespace Silmaril.Wasm.Lime1

/-- The six arithmetic instructions added by extended-const. -/
def Instr.isExtendedConstOp : Instr → Bool
  | .intBinOp _ .add | .intBinOp _ .sub | .intBinOp _ .mul => true
  | _ => false

/-- Context-independent constant-expression instruction eligibility. -/
def Instr.isConstOp : Instr → Bool
  | .intConst _ _ | .floatConst _ _ | .globalGet _ => true
  | i => i.isExtendedConstOp

def Expr.isConstSyntax (es : Expr) : Bool := es.all Instr.isConstOp

@[simp] theorem Expr.isConstSyntax_append (left right : Expr) :
    isConstSyntax (left ++ right) = (isConstSyntax left && isConstSyntax right) := by
  simp [isConstSyntax]

/-- Extended constant arithmetic over an imported immutable i32 global. -/
def extendedConstant : Expr :=
  [.globalGet ⟨0⟩, .intConst .i32 4, .intBinOp .i32 .mul,
    .intConst .i32 8, .intBinOp .i32 .add]

theorem extendedConstant_syntax : Expr.isConstSyntax extendedConstant = true := rfl

theorem division_not_constant (t : IntType) (s : Signedness) :
    Instr.isConstOp (.intBinOp t (.div s)) = false := rfl

theorem saturation_not_constant (src : FloatType) (dst : IntType) (s : Signedness) :
    Instr.isConstOp (.convert (.truncSat src dst s)) = false := rfl

/-- Bulk-memory-opt really extends the source instruction set. -/
theorem memoryCopy_not_v1 (i : V1.Instr) : i.toLime ≠ .memoryCopy := by
  cases i <;> simp [V1.Instr.toLime]

/-- A multi-result function and a type-indexed structured body. -/
def multiResult : Module where
  types := [⟨[], [.int .i32, .int .i64]⟩]
  funcs := [⟨⟨0⟩, [], [.block (.typeIdx ⟨0⟩)
    [.intConst .i32 7, .intConst .i64 11]]⟩]

/-- The type index and both scalar result types survive the Core 3 injection. -/
theorem multiResult_core_type :
    multiResult.toCore.types =
      [⟨[⟨true, [], .func ⟨[], [.num (.int .i32), .num (.int .i64)]⟩⟩]⟩] := rfl

/-- Nested bodies, including new instructions, survive the canonical retraction. -/
def nestedBody : Instr := .block .empty [
  .loop .empty [.memoryCopy, .memoryFill],
  .intConst .i64 255, .intUnOp .i64 (.extend .i8),
  .floatConst .f32 0, .convert (.truncSat .f32 .i32 .signed)]

theorem nestedBody_roundtrip : Instr.ofCore? nestedBody.toCore = some nestedBody := by simp

end Silmaril.Wasm.Lime1
