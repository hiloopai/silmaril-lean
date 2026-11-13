module

public import Silmaril.Wasm.Lime1.FromV1
-- Hand copy (track ws4-p1-lime-wasmi): source namespaces kept, import lines rewritten; one repair:
-- `set_option linter.unusedTactic false` for the file (an unused `<;>` in the mutual
-- `Instr.toV1?_sound`; CI builds with --wfail).

/-! # Checked projection into the Wasm1 instruction language

The projection preserves source syntax exactly. Bulk memory, sign-extension,
saturating conversion, and indexed block types are rejected, including inside
structured bodies. This is a profile check, not operand or module validation.
-/

@[expose] public section

set_option linter.unusedTactic false

namespace Silmaril.Wasm.Lime1

def BlockType.toV1? : BlockType → Option V1.BlockType
  | .empty => some none
  | .value t => some (some t)
  | .typeIdx _ => none

def IntUnOp.toV1? : IntUnOp → Option V1.IntUnOp
  | .clz => some .clz
  | .ctz => some .ctz
  | .popcnt => some .popcnt
  | .extend _ => none

def ConvertOp.toV1? : ConvertOp → Option V1.ConvertOp
  | .wrap => some .wrap
  | .extend s => some (.extend s)
  | .trunc s t sign => some (.trunc s t sign)
  | .truncSat .. => none
  | .convert s t sign => some (.convert s t sign)
  | .demote => some .demote
  | .promote => some .promote
  | .reinterpretInt t => some (.reinterpretInt t)
  | .reinterpretFloat t => some (.reinterpretFloat t)

mutual

def Instr.toV1? : Instr → Option V1.Instr
  | .nop => some .nop
  | .unreachable => some .unreachable
  | .drop => some .drop
  | .select => some .select
  | .block t body => do return .block (← t.toV1?) (← Expr.toV1? body)
  | .loop t body => do return .loop (← t.toV1?) (← Expr.toV1? body)
  | .if_ t left right => do return .if_ (← t.toV1?) (← Expr.toV1? left) (← Expr.toV1? right)
  | .br l => some (.br l)
  | .brIf l => some (.brIf l)
  | .brTable ls l => some (.brTable ls l)
  | .call f => some (.call f)
  | .callIndirect t => some (.callIndirect t)
  | .return_ => some .return_
  | .localGet i => some (.localGet i)
  | .localSet i => some (.localSet i)
  | .localTee i => some (.localTee i)
  | .globalGet i => some (.globalGet i)
  | .globalSet i => some (.globalSet i)
  | .intLoad t p a => some (.intLoad t p a)
  | .floatLoad t a => some (.floatLoad t a)
  | .intStore t p a => some (.intStore t p a)
  | .floatStore t a => some (.floatStore t a)
  | .memorySize => some .memorySize
  | .memoryGrow => some .memoryGrow
  | .memoryCopy | .memoryFill => none
  | .intConst t x => some (.intConst t x)
  | .floatConst t x => some (.floatConst t x)
  | .intUnOp t op => do return .intUnOp t (← op.toV1?)
  | .intBinOp t op => some (.intBinOp t op)
  | .intTestOp t op => some (.intTestOp t op)
  | .intRelOp t op => some (.intRelOp t op)
  | .floatUnOp t op => some (.floatUnOp t op)
  | .floatBinOp t op => some (.floatBinOp t op)
  | .floatRelOp t op => some (.floatRelOp t op)
  | .convert op => do return .convert (← ConvertOp.toV1? op)

def Expr.toV1? : Expr → Option V1.Expr
  | [] => some []
  | i :: es => do return (← i.toV1?) :: (← Expr.toV1? es)

end

@[simp] theorem BlockType.toV1?_toLime (t : V1.BlockType) :
    BlockType.toV1? (V1.BlockType.toLime t) = some t := by cases t <;> rfl

@[simp] theorem IntUnOp.toV1?_toLime (op : V1.IntUnOp) :
    IntUnOp.toV1? op.toLime = some op := by cases op <;> rfl

@[simp] theorem ConvertOp.toV1?_toCore (op : V1.ConvertOp) :
    ConvertOp.toV1? op.toCore = some op := by cases op <;> rfl

theorem BlockType.toV1?_sound {t : BlockType} {out : V1.BlockType}
    (h : t.toV1? = some out) : V1.BlockType.toLime out = t := by
  cases t <;> simp only [BlockType.toV1?, Option.some.injEq] at h <;> cases h <;> rfl

theorem IntUnOp.toV1?_sound {op : IntUnOp} {out : V1.IntUnOp}
    (h : op.toV1? = some out) : out.toLime = op := by
  cases op <;> simp only [IntUnOp.toV1?, Option.some.injEq] at h <;> cases h <;> rfl

theorem ConvertOp.toV1?_sound {op : ConvertOp} {out : V1.ConvertOp}
    (h : ConvertOp.toV1? op = some out) : out.toCore = op := by
  cases op <;> simp only [ConvertOp.toV1?, Option.some.injEq] at h <;> cases h <;> rfl

mutual

@[simp] theorem Instr.toV1?_toLime (i : V1.Instr) : Instr.toV1? i.toLime = some i := by
  cases i with
  | block t body => simp [V1.Instr.toLime, Instr.toV1?, Expr.toV1?_toLime body]
  | loop t body => simp [V1.Instr.toLime, Instr.toV1?, Expr.toV1?_toLime body]
  | if_ t left right => simp [V1.Instr.toLime, Instr.toV1?, Expr.toV1?_toLime left, Expr.toV1?_toLime right]
  | _ => simp [V1.Instr.toLime, Instr.toV1?]
termination_by sizeOf i

@[simp] theorem Expr.toV1?_toLime (es : V1.Expr) : Expr.toV1? (V1.Expr.toLime es) = some es := by
  cases es with
  | nil => rfl
  | cons i es => simp [V1.Expr.toLime, Expr.toV1?, Instr.toV1?_toLime i, Expr.toV1?_toLime es]
termination_by sizeOf es

end

mutual

theorem Instr.toV1?_sound {i : Instr} {out : V1.Instr}
    (h : i.toV1? = some out) : out.toLime = i := by
  cases i with
  | block t body =>
    simp only [Instr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨t', ht, body', hb, rfl⟩ := h
    simp [V1.Instr.toLime, BlockType.toV1?_sound ht, Expr.toV1?_sound hb]
  | loop t body =>
    simp only [Instr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨t', ht, body', hb, rfl⟩ := h
    simp [V1.Instr.toLime, BlockType.toV1?_sound ht, Expr.toV1?_sound hb]
  | if_ t left right =>
    simp only [Instr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨t', ht, left', hl, right', hr, rfl⟩ := h
    simp [V1.Instr.toLime, BlockType.toV1?_sound ht, Expr.toV1?_sound hl, Expr.toV1?_sound hr]
  | intUnOp t op =>
    simp only [Instr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨op', hp, rfl⟩ := h
    simp [V1.Instr.toLime, IntUnOp.toV1?_sound hp]
  | convert op =>
    simp only [Instr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨op', hp, rfl⟩ := h
    simp [V1.Instr.toLime, ConvertOp.toV1?_sound hp]
  | _ => simp only [Instr.toV1?, Option.some.injEq] at h; cases h <;> rfl
termination_by sizeOf i

theorem Expr.toV1?_sound {es : Expr} {out : V1.Expr}
    (h : Expr.toV1? es = some out) : V1.Expr.toLime out = es := by
  cases es with
  | nil => simp only [Expr.toV1?, Option.some.injEq] at h; cases h; rfl
  | cons i es =>
    simp only [Expr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨i', hi, es', hs, rfl⟩ := h
    simp [V1.Expr.toLime, Instr.toV1?_sound hi, Expr.toV1?_sound hs]
termination_by sizeOf es

end

theorem Instr.toV1?_eq_some_iff {i : Instr} {out : V1.Instr} :
    i.toV1? = some out ↔ out.toLime = i :=
  ⟨Instr.toV1?_sound, fun h => h ▸ Instr.toV1?_toLime out⟩

theorem Expr.toV1?_eq_some_iff {es : Expr} {out : V1.Expr} :
    Expr.toV1? es = some out ↔ V1.Expr.toLime out = es :=
  ⟨Expr.toV1?_sound, fun h => h ▸ Expr.toV1?_toLime out⟩

example : Expr.toV1? [.block .empty [.loop .empty [.br ⟨0⟩]]] =
    some [.block none [.loop none [.br ⟨0⟩]]] := rfl
example : Expr.toV1? [.if_ (.value (.int .i32)) [.intConst .i32 7] [.intConst .i32 9]] =
    some [.if_ (some (.int .i32)) [.intConst .i32 7] [.intConst .i32 9]] := rfl
example : Expr.toV1? [.block .empty [.memoryCopy]] = none := rfl
example : Expr.toV1? [.memoryFill] = none := rfl
example : Expr.toV1? [.loop (.typeIdx ⟨0⟩) []] = none := rfl
example : Instr.toV1? (.intUnOp .i64 (.extend .i8)) = none := rfl
example : Instr.toV1? (.convert (.truncSat .f32 .i32 .unsigned)) = none := rfl

end Silmaril.Wasm.Lime1
