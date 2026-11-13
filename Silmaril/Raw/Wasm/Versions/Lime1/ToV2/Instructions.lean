module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToV2.Types
public import Silmaril.Wasm.V2.ToCore.Instructions

/-!
# Lime1 instructions as WebAssembly 2.0 syntax

The instruction half of the subset theorem `Lime1 ⊆ 2.0`. Every one of Lime1's
seven features except extended constant expressions is a Wasm 2.0 feature, and
extended-const is a *validation* restriction, not a syntactic one: `i32.add` is
an ordinary 2.0 instruction. `Instr.toV2` is therefore **total**, and the
question of which Lime1 modules remain *valid* in 2.0 is deferred to the
validation layer (see `NOTES.md` and the `NoExtendedConst` side
condition stated there).

What the injection adds, relative to `Lime1.Instr`:

* `SELECT` gets its (absent) type annotation: 2.0's `SELECT (valtype*)?`
  (`1-syntax:410`) with `none`;
* `CALL_INDIRECT` gets the explicit table index `0`, because 2.0 writes
  `CALL_INDIRECT tableidx typeidx` (`1-syntax:427`) where Lime1 names table `0`
  implicitly. (2.0's memory instructions still name memory `0` implicitly, so
  no memory index is inserted — that only happens at the Core 3.0 step.)
* `CONVERT op` is re-split into 2.0's untyped
  `CVTOP numtype_1 numtype_2 cvtop` (`1-syntax:437`); see
  `Lime1/ToV2/Types.lean`.

`Instr.ofV2?` recognises exactly that image: it rejects every 2.0 instruction
that is not Lime1 syntax — vector instructions, reference instructions, table
instructions, passive segment instructions, an explicit `SELECT` annotation and
a nonzero `CALL_INDIRECT` table index.

## The commuting triangle

`Instr.toV2_toCore` and `Expr.toV2_toCore` say

```
V2.Instr.toCore (Instr.toV2 i) = some (Instr.toCore i)
```

— the 2.0 route to Core 3.0 computes exactly the direct `Lime1 → Core 3.0`
injection of `Lime1/ToCore/Instructions.lean`. The `some` is forced: `V2`'s
`Instr.toCore` is `Option`-valued because 2.0's `CVTOP` is untyped
(`Silmaril/Wasm/V2/ToCore/Instructions.lean`), and the content of the triangle
at `CONVERT` is precisely that the triple `V2.CvtOp.ofCore` produces is one of
the defined ones.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1

/-! ## Conversions

A Lime1 `CONVERT` becomes a whole 2.0 instruction, since 2.0 carries the source
and target types on the instruction rather than in the operator. -/

/-- `CVTOP numtype_1 numtype_2 cvtop` (`1-syntax:437`) for a Lime1 conversion;
this is `V2.CvtOp.toInstr`, i.e. `ConvertOp.toV2` packaged as an instruction. -/
def ConvertOp.toV2Instr (op : ConvertOp) : V2.Instr := V2.CvtOp.toInstr op

/-- The 2.0 image of a Lime1 conversion really is a `CVTOP`. -/
theorem ConvertOp.toV2Instr_eq (op : ConvertOp) :
    ConvertOp.toV2Instr op =
      .cvtOp (ConvertOp.toV2 op).1 (ConvertOp.toV2 op).2.1 (ConvertOp.toV2 op).2.2 := rfl

/-! ## The injection -/

mutual

/-- The Wasm 2.0 instruction denoted by a Lime1 instruction. Total: Lime1 is a
syntactic subset of 2.0. -/
def Instr.toV2 : Instr → V2.Instr
  | .nop => .nop
  | .unreachable => .unreachable
  | .drop => .drop
  | .select => .select none
  | .block t body => .block (BlockType.toV2 t) (Expr.toV2 body)
  | .loop t body => .loop (BlockType.toV2 t) (Expr.toV2 body)
  | .if_ t left right => .if_ (BlockType.toV2 t) (Expr.toV2 left) (Expr.toV2 right)
  | .br l => .br l
  | .brIf l => .brIf l
  | .brTable ls l => .brTable ls l
  | .call f => .call f
  | .callIndirect t => .callIndirect ⟨0, Nat.two_pow_pos 32⟩ t
  | .return_ => .return_
  | .localGet x => .localGet x
  | .localSet x => .localSet x
  | .localTee x => .localTee x
  | .globalGet x => .globalGet x
  | .globalSet x => .globalSet x
  | .intLoad t p a => .intLoad t (loadPackToV2 p) (MemArg.toV2 a)
  | .floatLoad t a => .floatLoad t (MemArg.toV2 a)
  | .intStore t p a => .intStore t (p.map PackSize.toV2) (MemArg.toV2 a)
  | .floatStore t a => .floatStore t (MemArg.toV2 a)
  | .memorySize => .memorySize
  | .memoryGrow => .memoryGrow
  | .memoryFill => .memoryFill
  | .memoryCopy => .memoryCopy
  | .intConst t x => .intConst t x
  | .floatConst t x => .floatConst t x
  | .intUnOp t op => .intUnOp t op.toV2
  | .intBinOp t op => .intBinOp t op
  | .intTestOp t op => .intTestOp t op
  | .intRelOp t op => .intRelOp t op
  | .floatUnOp t op => .floatUnOp t op
  | .floatBinOp t op => .floatBinOp t op
  | .floatRelOp t op => .floatRelOp t op
  | .convert op => ConvertOp.toV2Instr op

/-- `expr ::= instr*` on both sides. -/
def Expr.toV2 : Expr → V2.Expr
  | [] => []
  | i :: is => Instr.toV2 i :: Expr.toV2 is

end

theorem Expr.toV2_eq_map (es : Expr) : Expr.toV2 es = es.map Instr.toV2 := by
  induction es with
  | nil => rfl
  | cons i es ih => simp only [Expr.toV2, ih, List.map_cons]

/-! ## The retraction -/

mutual

/-- Recognise exactly the Lime1 instruction image inside the 2.0 syntax. -/
def Instr.ofV2? : V2.Instr → Option Instr
  | .nop => some .nop
  | .unreachable => some .unreachable
  | .drop => some .drop
  | .select none => some .select
  | .block t body => do return .block (← BlockType.ofV2? t) (← Expr.ofV2? body)
  | .loop t body => do return .loop (← BlockType.ofV2? t) (← Expr.ofV2? body)
  | .if_ t left right => do
      return .if_ (← BlockType.ofV2? t) (← Expr.ofV2? left) (← Expr.ofV2? right)
  | .br l => some (.br l)
  | .brIf l => some (.brIf l)
  | .brTable ls l => some (.brTable ls l)
  | .call f => some (.call f)
  | .callIndirect table t =>
      if table = ⟨0, Nat.two_pow_pos 32⟩ then some (.callIndirect t) else none
  | .return_ => some .return_
  | .localGet x => some (.localGet x)
  | .localSet x => some (.localSet x)
  | .localTee x => some (.localTee x)
  | .globalGet x => some (.globalGet x)
  | .globalSet x => some (.globalSet x)
  | .intLoad t p a => do return .intLoad t (← loadPackOfV2? p) (← MemArg.ofV2? a)
  | .floatLoad t a => do return .floatLoad t (← MemArg.ofV2? a)
  | .intStore t p a => do return .intStore t (← storePackOfV2? p) (← MemArg.ofV2? a)
  | .floatStore t a => do return .floatStore t (← MemArg.ofV2? a)
  | .memorySize => some .memorySize
  | .memoryGrow => some .memoryGrow
  | .memoryFill => some .memoryFill
  | .memoryCopy => some .memoryCopy
  | .intConst t x => some (.intConst t x)
  | .floatConst t x => some (.floatConst t x)
  | .intUnOp t op => (IntUnOp.ofV2? op).map (.intUnOp t)
  | .intBinOp t op => some (.intBinOp t op)
  | .intTestOp t op => some (.intTestOp t op)
  | .intRelOp t op => some (.intRelOp t op)
  | .floatUnOp t op => some (.floatUnOp t op)
  | .floatBinOp t op => some (.floatBinOp t op)
  | .floatRelOp t op => some (.floatRelOp t op)
  | .cvtOp target source op => (ConvertOp.ofV2? (target, source, op)).map Instr.convert
  | _ => none

/-- `expr ::= instr*`, retracted pointwise. -/
def Expr.ofV2? : V2.Expr → Option Expr
  | [] => some []
  | i :: is => do return (← Instr.ofV2? i) :: (← Expr.ofV2? is)

end

@[simp] theorem Instr.ofV2?_toV2Instr (op : ConvertOp) :
    Instr.ofV2? (ConvertOp.toV2Instr op) = some (.convert op) := by
  have h := ConvertOp.ofV2?_toV2 op
  rw [ConvertOp.toV2Instr_eq]
  simp only [Instr.ofV2?]
  rw [show ((ConvertOp.toV2 op).1, (ConvertOp.toV2 op).2.1, (ConvertOp.toV2 op).2.2)
      = ConvertOp.toV2 op from rfl, h, Option.map_some]

mutual

@[simp] theorem Instr.ofV2?_toV2 (i : Instr) : Instr.ofV2? i.toV2 = some i := by
  cases i with
  | block t body => simp [Instr.toV2, Instr.ofV2?, Expr.ofV2?_toV2 body]
  | loop t body => simp [Instr.toV2, Instr.ofV2?, Expr.ofV2?_toV2 body]
  | if_ t left right =>
      simp [Instr.toV2, Instr.ofV2?, Expr.ofV2?_toV2 left, Expr.ofV2?_toV2 right]
  | convert op => simp [Instr.toV2]
  | _ => simp [Instr.toV2, Instr.ofV2?]
termination_by sizeOf i

@[simp] theorem Expr.ofV2?_toV2 (es : Expr) : Expr.ofV2? (Expr.toV2 es) = some es := by
  cases es with
  | nil => rfl
  | cons i es =>
      simp only [Expr.toV2, Expr.ofV2?, Instr.ofV2?_toV2 i, Expr.ofV2?_toV2 es]
      rfl
termination_by sizeOf es

end

theorem Instr.toV2_injective : Function.Injective Instr.toV2 :=
  injective_of_ofV2? Instr.ofV2?_toV2

theorem Expr.toV2_injective : Function.Injective Expr.toV2 :=
  injective_of_ofV2? Expr.ofV2?_toV2

/-! ## The commuting triangle -/

@[simp] theorem Instr.toV2Instr_toCore (op : ConvertOp) :
    V2.Instr.toCore (ConvertOp.toV2Instr op) = some (.convert op) := by
  have h := ConvertOp.ofV2?_toV2 op
  rw [ConvertOp.toV2Instr_eq]
  simp only [V2.Instr.toCore]
  rw [show V2.CvtOp.toCore (ConvertOp.toV2 op).1 (ConvertOp.toV2 op).2.1 (ConvertOp.toV2 op).2.2
      = ConvertOp.ofV2? (ConvertOp.toV2 op) from rfl, h, Option.map_some]

mutual

/-- The `Lime1 → 2.0 → Core 3.0` route computes the direct `Lime1 → Core 3.0`
injection of `Lime1/ToCore/Instructions.lean`. -/
@[simp] theorem Instr.toV2_toCore (i : Instr) :
    V2.Instr.toCore (Instr.toV2 i) = some (Instr.toCore i) := by
  cases i with
  | block t body =>
      simp [Instr.toV2, V2.Instr.toCore, Instr.toCore, Expr.toV2_toCore body]
  | loop t body =>
      simp [Instr.toV2, V2.Instr.toCore, Instr.toCore, Expr.toV2_toCore body]
  | if_ t left right =>
      simp [Instr.toV2, V2.Instr.toCore, Instr.toCore,
        Expr.toV2_toCore left, Expr.toV2_toCore right]
  | convert op => simp [Instr.toV2, Instr.toCore]
  | intLoad t p a =>
      simp [Instr.toV2, V2.Instr.toCore, Instr.toCore, loadPackToV2_eq_toCore]
  | intStore t p a =>
      simp [Instr.toV2, V2.Instr.toCore, Instr.toCore, PackSize.toV2_eq_toCore_fun]
  | intUnOp t op =>
      simp [Instr.toV2, V2.Instr.toCore, Instr.toCore, IntUnOp.toV2_eq_toCore]
  | _ => simp [Instr.toV2, V2.Instr.toCore, Instr.toCore]
termination_by sizeOf i

@[simp] theorem Expr.toV2_toCore (es : Expr) :
    V2.Expr.toCore (Expr.toV2 es) = some (Expr.toCore es) := by
  cases es with
  | nil => rfl
  | cons i es =>
      simp only [Expr.toV2, V2.Expr.toCore, Expr.toCore, Instr.toV2_toCore i,
        Expr.toV2_toCore es, Option.bind_some, Option.map_some]
termination_by sizeOf es

end

/-! ## Checks -/

example : Instr.ofV2? (Instr.toV2 (.memoryCopy)) = some .memoryCopy := rfl
example : Instr.ofV2? (.callIndirect ⟨1, by omega⟩ ⟨0, Nat.two_pow_pos 32⟩) = none := rfl
example : Instr.ofV2? (.select (some [V2.ValType.i32])) = none := rfl
example : Instr.ofV2? (.refIsNull) = none := rfl
example : Instr.ofV2? (.tableGet ⟨0, Nat.two_pow_pos 32⟩) = none := rfl
example : Instr.toV2 (.intUnOp .i64 (.extend .i8)) = .intUnOp .i64 (.extend .i8) := rfl
example : Instr.toV2 (.convert (.truncSat .f32 .i32 .unsigned))
    = .cvtOp (.int .i32) (.float .f32) (.truncSat .unsigned) := rfl

end Silmaril.Wasm.Lime1
