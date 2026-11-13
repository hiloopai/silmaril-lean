module

public import Silmaril.Wasm.Lime1ToV1.Defs

/-!
# The checked projection from Lime1 into Wasm 1.0 syntax: theorems

* `instrToV1?_toLime`, `exprToV1?_toLime`: the projection inverts the injection
  `V1.Instr.toLime`.
* `instrToV1?_sound`, `exprToV1?_sound`: whatever the projection returns maps back to its input.
* `instrToV1?_eq_some_iff`, `exprToV1?_eq_some_iff`: so the projection succeeds exactly on the
  image of the injection, where it returns the preimage.
* Examples: nested structured bodies project; bulk memory, indexed block types, sign extension
  and saturating truncation do not, also when nested.

Ported from an earlier development `Silmaril/Wasm/Lime1/ToV1.lean`. The soundness proofs
state each decomposition of a bind (`obtain … : … := by simpa … using h`) instead of
rewriting the hypothesis in place.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1ToV1

open Silmaril.Wasm

@[simp] theorem blockTypeToV1?_toLime (t : V1.BlockType) :
    blockTypeToV1? (V1.BlockType.toLime t) = some t := by cases t <;> rfl

@[simp] theorem intUnOpToV1?_toLime (op : V1.IntUnOp) :
    intUnOpToV1? op.toLime = some op := by cases op <;> rfl

@[simp] theorem convertOpToV1?_toCore (op : V1.ConvertOp) :
    convertOpToV1? op.toCore = some op := by cases op <;> rfl

theorem blockTypeToV1?_sound {t : Lime1.BlockType} {out : V1.BlockType}
    (h : blockTypeToV1? t = some out) : V1.BlockType.toLime out = t := by
  cases t <;> simp only [blockTypeToV1?, Option.some.injEq, reduceCtorEq] at h <;> cases h <;> rfl

theorem intUnOpToV1?_sound {op : Lime1.IntUnOp} {out : V1.IntUnOp}
    (h : intUnOpToV1? op = some out) : out.toLime = op := by
  cases op <;> simp only [intUnOpToV1?, Option.some.injEq, reduceCtorEq] at h <;> cases h <;> rfl

theorem convertOpToV1?_sound {op : ConvertOp} {out : V1.ConvertOp}
    (h : convertOpToV1? op = some out) : out.toCore = op := by
  cases op <;> simp only [convertOpToV1?, Option.some.injEq, reduceCtorEq] at h <;> cases h <;> rfl

mutual

@[simp] theorem instrToV1?_toLime (i : V1.Instr) : instrToV1? i.toLime = some i := by
  cases i with
  | block t body => simp [V1.Instr.toLime, instrToV1?, exprToV1?_toLime body]
  | loop t body => simp [V1.Instr.toLime, instrToV1?, exprToV1?_toLime body]
  | if_ t left right =>
    simp [V1.Instr.toLime, instrToV1?, exprToV1?_toLime left, exprToV1?_toLime right]
  | _ => simp [V1.Instr.toLime, instrToV1?]
termination_by sizeOf i

@[simp] theorem exprToV1?_toLime (es : V1.Expr) : exprToV1? (V1.Expr.toLime es) = some es := by
  cases es with
  | nil => rfl
  | cons i es => simp [V1.Expr.toLime, exprToV1?, instrToV1?_toLime i, exprToV1?_toLime es]
termination_by sizeOf es

end

mutual

theorem instrToV1?_sound {i : Lime1.Instr} {out : V1.Instr}
    (h : instrToV1? i = some out) : out.toLime = i := by
  cases i with
  | block t body =>
    obtain ⟨t', ht, body', hb, rfl⟩ : ∃ t', blockTypeToV1? t = some t' ∧
        ∃ body', exprToV1? body = some body' ∧ V1.Instr.block t' body' = out := by
      simpa [instrToV1?, Option.bind_eq_some_iff] using h
    simp [V1.Instr.toLime, blockTypeToV1?_sound ht, exprToV1?_sound hb]
  | loop t body =>
    obtain ⟨t', ht, body', hb, rfl⟩ : ∃ t', blockTypeToV1? t = some t' ∧
        ∃ body', exprToV1? body = some body' ∧ V1.Instr.loop t' body' = out := by
      simpa [instrToV1?, Option.bind_eq_some_iff] using h
    simp [V1.Instr.toLime, blockTypeToV1?_sound ht, exprToV1?_sound hb]
  | if_ t left right =>
    obtain ⟨t', ht, left', hl, right', hr, rfl⟩ : ∃ t', blockTypeToV1? t = some t' ∧
        ∃ left', exprToV1? left = some left' ∧ ∃ right', exprToV1? right = some right' ∧
          V1.Instr.if_ t' left' right' = out := by
      simpa [instrToV1?, Option.bind_eq_some_iff] using h
    simp [V1.Instr.toLime, blockTypeToV1?_sound ht, exprToV1?_sound hl, exprToV1?_sound hr]
  | intUnOp t op =>
    obtain ⟨op', hp, rfl⟩ : ∃ op', intUnOpToV1? op = some op' ∧ V1.Instr.intUnOp t op' = out := by
      simpa [instrToV1?, Option.bind_eq_some_iff] using h
    simp [V1.Instr.toLime, intUnOpToV1?_sound hp]
  | convert op =>
    obtain ⟨op', hp, rfl⟩ : ∃ op', convertOpToV1? op = some op' ∧ V1.Instr.convert op' = out := by
      simpa [instrToV1?, Option.bind_eq_some_iff] using h
    simp [V1.Instr.toLime, convertOpToV1?_sound hp]
  | memoryCopy | memoryFill => exact absurd h (by simp [instrToV1?])
  | _ =>
    have hout : _ = out := Option.some.inj h
    rw [← hout]
    rfl
termination_by sizeOf i

theorem exprToV1?_sound {es : Lime1.Expr} {out : V1.Expr}
    (h : exprToV1? es = some out) : V1.Expr.toLime out = es := by
  cases es with
  | nil =>
    have hout : out = [] := (Option.some.inj h).symm
    rw [hout]; rfl
  | cons i es =>
    obtain ⟨i', hi, es', hs, rfl⟩ : ∃ i', instrToV1? i = some i' ∧
        ∃ es', exprToV1? es = some es' ∧ i' :: es' = out := by
      simpa [exprToV1?, Option.bind_eq_some_iff] using h
    simp [V1.Expr.toLime, instrToV1?_sound hi, exprToV1?_sound hs]
termination_by sizeOf es

end

/-- The projection succeeds exactly on the image of `V1.Instr.toLime`. -/
theorem instrToV1?_eq_some_iff {i : Lime1.Instr} {out : V1.Instr} :
    instrToV1? i = some out ↔ out.toLime = i :=
  ⟨instrToV1?_sound, fun h => h ▸ instrToV1?_toLime out⟩

/-- The projection succeeds exactly on the image of `V1.Expr.toLime`. -/
theorem exprToV1?_eq_some_iff {es : Lime1.Expr} {out : V1.Expr} :
    exprToV1? es = some out ↔ V1.Expr.toLime out = es :=
  ⟨exprToV1?_sound, fun h => h ▸ exprToV1?_toLime out⟩

example : exprToV1? [.block .empty [.loop .empty [.br ⟨0⟩]]] =
    some [.block none [.loop none [.br ⟨0⟩]]] := rfl
example : exprToV1? [.if_ (.value (.int .i32)) [.intConst .i32 7] [.intConst .i32 9]] =
    some [.if_ (some (.int .i32)) [.intConst .i32 7] [.intConst .i32 9]] := rfl
example : exprToV1? [.block .empty [.memoryCopy]] = none := rfl
example : exprToV1? [.memoryFill] = none := rfl
example : exprToV1? [.loop (.typeIdx ⟨0⟩) []] = none := rfl
example : instrToV1? (.intUnOp .i64 (.extend .i8)) = none := rfl
example : instrToV1? (.convert (.truncSat .f32 .i32 .unsigned)) = none := rfl

end Silmaril.Wasm.Lime1ToV1
