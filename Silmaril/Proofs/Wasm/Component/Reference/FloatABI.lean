module

public import Silmaril.Proofs.Wasm.Component.Reference.FlatABI

/-!
# The flat canonical ABI of the reference machine with floats

`Silmaril.Proofs.Wasm.Component.Reference.FlatABI` relates the reference flat ABI to the IR's for
float-free types. With floats the two differ in two places (`Canon/Flat.lean`):

* lowering a NaN `f32`/`f64` issues the choice C7 `choose (.nan t x)`, whose admissible
  answers are `NanLower prof t x` (`Value/Nan.lean`): some NaN (`nondet`), a NaN in the image of
  REF `random_nan_bits` (`refStrict`), the canonical NaN (`deterministic`); a non-NaN is lowered
  unchanged;
* lifting canonicalises NaNs (REF `canonicalize_nan32/64`).

The fragment: `floatOk t`, floats anywhere except in variant payloads (which are float-free; a
float payload is re-encoded by `coerceLower`, a second C7 choice, which is not treated here).

* `NanAt prof t v v'`: `v'` is an admissible lowering of `v` at type `t` (floats related by
  `NanLower prof`, everything else equal); `canonAt t w`: `w` with its floats canonicalised;
* `ChoiceProg prof Q p`: `p` consists of C7 choices only and ends in a result satisfying `Q`
  for every admissible sequence of answers;
* `lowerFlatTypes_float`: reference `lower_flat` of `vs` is a `ChoiceProg` whose results are the
  IR lowerings `lowerArgs ts vs'` of the admissible `vs'` (`NanAtList prof ts vs vs'`, well
  typed);
* `liftFlatTypes_float`: reference `lift_flat` returns the canonicalisation of the IR lift
  `canonAtList ts ws` (as reference values) where the IR lift returns `ws`, or traps at its first
  operation where it fails.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Runtime (RtId)
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm (FloatType)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## The fragment, NaN relations and canonicalisation (defined in the `Sound` header) -/

export Silmaril.Wasm.Component.Reference (floatOk floatOkList canonAt canonAtList NanAt NanAtList)

/-- A non-NaN lowers to itself under every profile. -/
theorem nanLower_self {prof : ProfileKind} {t : FloatType} {x : BitVec t.width}
    (h : isNaN t x = false) : NanLower prof t x x := by
  cases prof
  · simp only [NanLower, h, Bool.false_eq_true, ↓reduceIte]
  · exact ⟨(scrambleNaN_false_iff t x x).mpr (.inl ⟨h, rfl⟩), fun e => absurd (e.symm.trans h)
      (by decide)⟩
  · exact (scrambleNaN_true_iff t x x).mpr (canonicalizeNaN_of_not_isNaN h).symm

/-! ## Programs of NaN choices -/

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {σ : Type}

variable (prof : ProfileKind) in
/-- `p` consists of C7 choices only and ends in a result satisfying `Q`, for every admissible
answer to each choice. -/
inductive ChoiceProg {α : Type} (Q : α → Prop) : P E σ α → Prop where
  | pure {a : α} : Q a → ChoiceProg Q (.pure a)
  | nan {t : FloatType} {x : BitVec t.width} {k : (ChoiceKind.nan t x).Resp → P E σ α} :
      (∀ r, NanLower prof t x r → ChoiceProg Q (k r)) →
      ChoiceProg Q (.op (S := Eff E σ) (.choose (.nan t x)) k)

namespace ChoiceProg

variable {prof : ProfileKind}

theorem bind {α β : Type} {Q : α → Prop} {R : β → Prop} {p : P E σ α} {f : α → P E σ β}
    (h : ChoiceProg prof Q p) (hf : ∀ a, Q a → ChoiceProg prof R (f a)) :
    ChoiceProg prof R (p >>= f) := by
  induction h with
  | pure ha => exact hf _ ha
  | nan _ ih => exact .nan fun r hr => ih r hr

theorem mono {α : Type} {Q R : α → Prop} {p : P E σ α} (h : ChoiceProg prof Q p)
    (hQR : ∀ a, Q a → R a) : ChoiceProg prof R p := by
  induction h with
  | pure ha => exact .pure (hQR _ ha)
  | nan _ ih => exact .nan fun r hr => ih r hr

theorem pure' {α : Type} {Q : α → Prop} {a : α} (h : Q a) :
    ChoiceProg prof Q (Pure.pure a : P E σ α) :=
  .pure h

end ChoiceProg

/-- **`maybe_scramble_nan`** (`lowerFloat`) chooses an admissible lowering. -/
theorem lowerFloat_choice (prof : ProfileKind) (t : FloatType) (x : BitVec t.width) :
    ChoiceProg prof (fun y => NanLower prof t x y) (lowerFloat t x : P E σ _) := by
  cases h : isNaN t x
  · rw [lowerFloat_of_not_isNaN h]
    exact .pure (nanLower_self h)
  · rw [lowerFloat_of_isNaN h]
    exact .nan fun r hr => .pure hr

/-! ## Values related by `NanAt` -/

/-- The admissible lowerings of `v` at `t`, lowered. -/
def LowOut (prof : ProfileKind) (t : ValTy) (v : IVal) (out : List Flat) : Prop :=
  ∃ v', NanAt prof t v v' ∧ t.check v' = true ∧ out = t.lower v'

/-- The admissible lowerings of `vs` at `ts`, lowered. -/
def LowOutList (prof : ProfileKind) (ts : List ValTy) (vs : List IVal) (out : List Flat) :
    Prop :=
  ∃ vs', NanAtList prof ts vs vs' ∧ ValTy.checkList ts vs' = true ∧ out = ValTy.lowerList ts vs'

/-- Types other than floats and records relate a value to itself only. -/
theorem nanAt_other {prof : ProfileKind} {t : ValTy} (h32 : t ≠ .f32) (h64 : t ≠ .f64)
    (hr : ∀ ts, t ≠ .record ts) (v : IVal) : NanAt prof t v v := by
  cases t <;> first | exact absurd rfl h32 | exact absurd rfl h64 | exact absurd rfl (hr _) | rfl

/-- `canonAt` keeps values of types other than floats and records. -/
theorem canonAt_other {t : ValTy} (h32 : t ≠ .f32) (h64 : t ≠ .f64) (hr : ∀ ts, t ≠ .record ts)
    (v : IVal) : canonAt t v = v := by
  cases t <;> first | exact absurd rfl h32 | exact absurd rfl h64 | exact absurd rfl (hr _) | rfl

/-- A `floatOk` type other than floats and records is float-free. -/
theorem floatFree_of_floatOk {t : ValTy} (h : floatOk t = true) (h32 : t ≠ .f32)
    (h64 : t ≠ .f64) (hr : ∀ ts, t ≠ .record ts) : floatFree t = true := by
  cases t <;>
    first
      | exact absurd rfl h32 | exact absurd rfl h64 | exact absurd rfl (hr _) | rfl
      | (simp only [floatOk] at h; simpa only [floatFree] using h)

/-! ## Lowering -/

variable (lim : Limits) (q : Quirks) (cx : Silmaril.Wasm.Component.Runtime.LiftLowerContext E)
  (p : Silmaril.Wasm.AddrType)

/-- A float-free type lowers without choice. -/
theorem lowerAt_free (prof : ProfileKind) {t : ValTy} {v : IVal} (hf : floatFree t = true)
    (h32 : t ≠ .f32) (h64 : t ≠ .f64) (hr : ∀ ts, t ≠ .record ts) (h : t.check v = true) :
    ChoiceProg prof (LowOut prof t v)
      (lowerFlatAt lim q cx p (toRefVal v) (toClosed t) : P E σ _) := by
  rw [lowerFlatAt_toClosed lim q cx p t v hf h]
  exact .pure ⟨v, nanAt_other h32 h64 hr v, h, rfl⟩

/-- An `f32` lowers to an admissible lowering. -/
theorem lowerAt_f32 (prof : ProfileKind) (x : BitVec 32) :
    ChoiceProg prof (LowOut prof .f32 (.f32 x))
      (lowerFlatAt lim q cx p (toRefVal (.f32 x)) (toClosed .f32) : P E σ _) := by
  have e : (lowerFlatAt lim q cx p (toRefVal (.f32 x)) (toClosed .f32) : P E σ _) =
      lowerFloat .f32 x >>= fun y => pure [⟨.float .f32, y⟩] := rfl
  rw [e]
  exact (lowerFloat_choice prof .f32 x).bind fun y hy => .pure ⟨.f32 y, hy, rfl, rfl⟩

/-- An `f64` lowers to an admissible lowering. -/
theorem lowerAt_f64 (prof : ProfileKind) (x : BitVec 64) :
    ChoiceProg prof (LowOut prof .f64 (.f64 x))
      (lowerFlatAt lim q cx p (toRefVal (.f64 x)) (toClosed .f64) : P E σ _) := by
  have e : (lowerFlatAt lim q cx p (toRefVal (.f64 x)) (toClosed .f64) : P E σ _) =
      lowerFloat .f64 x >>= fun y => pure [⟨.float .f64, y⟩] := rfl
  rw [e]
  exact (lowerFloat_choice prof .f64 x).bind fun y hy => .pure ⟨.f64 y, hy, rfl, rfl⟩

/-- A record lowers as its fields. -/
theorem lowOut_record {prof : ProfileKind} {ts : List ValTy} {vs : List IVal} {out : List Flat}
    (h : LowOutList prof ts vs out) : LowOut prof (.record ts) (.record vs) out := by
  obtain ⟨vs', hn, hc, rfl⟩ := h
  exact ⟨.record vs', hn, hc, rfl⟩

/-- One field more. -/
theorem lowOut_cons {prof : ProfileKind} {t : ValTy} {ts : List ValTy} {v : IVal}
    {vs : List IVal} {a b : List Flat} (ha : LowOut prof t v a) (hb : LowOutList prof ts vs b) :
    LowOutList prof (t :: ts) (v :: vs) (a ++ b) := by
  obtain ⟨v', hn, hc, rfl⟩ := ha
  obtain ⟨vs', hn', hc', rfl⟩ := hb
  refine ⟨v' :: vs', ⟨hn, hn'⟩, ?_, rfl⟩
  simp only [ValTy.checkList, hc, hc', Bool.and_self]

mutual
/-- **Reference `lower_flat` with floats** chooses an admissible lowering. -/
theorem lowerAt_float (prof : ProfileKind) : ∀ (t : ValTy) (v : IVal), floatOk t = true →
    t.check v = true →
      ChoiceProg prof (LowOut prof t v)
        (lowerFlatAt lim q cx p (toRefVal v) (toClosed t) : P E σ _)
  | .f32, .f32 x, _, _ => lowerAt_f32 lim q cx p prof x
  | .f64, .f64 x, _, _ => lowerAt_f64 lim q cx p prof x
  | .record ts, .record vs, hf, h => by
    have ih := lowerFields_float prof ts vs (labels "f" (toClosedList ts)) (labels_map_snd "f" _)
      (by simpa only [floatOk] using hf) (by simpa only [ValTy.check] using h)
    exact ih.mono fun _ => lowOut_record
  | .bool, v, hf, h | .s8, v, hf, h | .u8, v, hf, h | .s16, v, hf, h | .u16, v, hf, h
  | .s32, v, hf, h | .u32, v, hf, h | .s64, v, hf, h | .u64, v, hf, h | .char, v, hf, h
  | .variant _, v, hf, h =>
    lowerAt_free lim q cx p prof (floatFree_of_floatOk hf (by simp) (by simp) (by simp))
      (by simp) (by simp) (by simp) h
  | .f32, .bool _, _, h | .f32, .s8 _, _, h | .f32, .u8 _, _, h | .f32, .s16 _, _, h
  | .f32, .u16 _, _, h | .f32, .s32 _, _, h | .f32, .u32 _, _, h | .f32, .s64 _, _, h
  | .f32, .u64 _, _, h | .f32, .f64 _, _, h | .f32, .char _, _, h | .f32, .record _, _, h
  | .f32, .variant _ _, _, h | .f64, .bool _, _, h | .f64, .s8 _, _, h | .f64, .u8 _, _, h
  | .f64, .s16 _, _, h | .f64, .u16 _, _, h | .f64, .s32 _, _, h | .f64, .u32 _, _, h
  | .f64, .s64 _, _, h | .f64, .u64 _, _, h | .f64, .f32 _, _, h | .f64, .char _, _, h
  | .f64, .record _, _, h | .f64, .variant _ _, _, h | .record _, .bool _, _, h
  | .record _, .s8 _, _, h | .record _, .u8 _, _, h | .record _, .s16 _, _, h
  | .record _, .u16 _, _, h | .record _, .s32 _, _, h | .record _, .u32 _, _, h
  | .record _, .s64 _, _, h | .record _, .u64 _, _, h | .record _, .f32 _, _, h
  | .record _, .f64 _, _, h | .record _, .char _, _, h | .record _, .variant _ _, _, h => by
    simp [ValTy.check] at h

/-- `lowerAt_float` on record fields. -/
theorem lowerFields_float (prof : ProfileKind) : ∀ (ts : List ValTy) (vs : List IVal)
    (fs : List (String × WIT.ClosedType RtId)), fs.map Prod.snd = toClosedList ts →
      floatOkList ts = true → ValTy.checkList ts vs = true →
        ChoiceProg prof (LowOutList prof ts vs)
          (lowerFlatFields lim q cx p (toRefVals vs) fs : P E σ _)
  | [], [], [], _, _, _ => .pure ⟨[], rfl, rfl, rfl⟩
  | [], [], _ :: _, h, _, _ => by simp [toClosedList] at h
  | _ :: _, _, [], h, _, _ => by simp [toClosedList] at h
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, (n, u) :: fs, hfs, hf, h => by
    have hfs' : u = toClosed t ∧ fs.map Prod.snd = toClosedList ts := by
      simpa only [List.map_cons, toClosedList, List.cons.injEq] using hfs
    have hf' : floatOk t = true ∧ floatOkList ts = true := by
      simpa only [floatOkList, Bool.and_eq_true] using hf
    have h' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using h
    rw [hfs'.1]
    exact (lowerAt_float prof t v hf'.1 h'.1).bind fun a ha =>
      (lowerFields_float prof ts vs fs hfs'.2 hf'.2 h'.2).bind fun b hb =>
        .pure (lowOut_cons ha hb)
end

/-- `lowerAt_float` on argument lists. -/
theorem lowerFlatTypes_float (prof : ProfileKind) : ∀ (ts : List ValTy) (vs : List IVal),
    floatOkList ts = true → ValTy.checkList ts vs = true →
      ChoiceProg prof (LowOutList prof ts vs)
        (lowerFlatTypes lim q cx p (toRefVals vs) (toClosedList ts) : P E σ _)
  | [], [], _, _ => .pure ⟨[], rfl, rfl, rfl⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [ValTy.checkList] at h
  | t :: ts, v :: vs, hf, h => by
    have hf' : floatOk t = true ∧ floatOkList ts = true := by
      simpa only [floatOkList, Bool.and_eq_true] using hf
    have h' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using h
    exact (lowerAt_float lim q cx p prof t v hf'.1 h'.1).bind fun a ha =>
      (lowerFlatTypes_float prof ts vs hf'.2 h'.2).bind fun b hb => .pure (lowOut_cons ha hb)

/-- **Reference `lower_flat_values` with floats**: after reading the pointer type, a program of
NaN choices ending in the IR lowering of an admissible argument list. -/
theorem lowerFlatValues_float {max : Nat} {ts : List ValTy} {vs : List IVal}
    (hmax : (ValTy.flatList ts).length ≤ max) (op : Option FlatCursor) :
    (lowerFlatValues lim q cx max (vs.map toRefVal) (toClosedList ts) op : P E σ _) =
      ptrType cx >>= fun p => lowerFlatTypes lim q cx p (toRefVals vs) (toClosedList ts) := by
  unfold lowerFlatValues
  congr 1
  funext p
  have hle : ¬ (flattenTypes p (toClosedList ts)).length > max := by
    rw [flattenTypes_toClosed]
    omega
  simp only [hle, ↓reduceIte, ← toRefVals_eq]

/-! ## Lifting -/

/-- `LiftRel` up to the canonicalisation of the result. -/
def LiftRelC (t : ValTy) (prog : P E σ (Value.Val × FlatCursor))
    (res : Option (IVal × List Flat)) (ys : List Flat) (n' : Nat) : Prop :=
  match res with
  | some (w, r) => prog = pure (toRefVal (canonAt t w), ⟨ys, n'⟩) ∧ r = ys.drop n'
  | none => IsTrap prog

/-- `LiftsRel` up to the canonicalisation of the results. -/
def LiftsRelC (ts : List ValTy) (prog : P E σ (List Value.Val × FlatCursor))
    (res : Option (List IVal × List Flat)) (ys : List Flat) (n' : Nat) : Prop :=
  match res with
  | some (ws, r) => prog = pure (toRefVals (canonAtList ts ws), ⟨ys, n'⟩) ∧ r = ys.drop n'
  | none => IsTrap prog

/-- A float-free scalar or variant: `LiftRel` is `LiftRelC`. -/
theorem liftRelC_of {t : ValTy} {prog : P E σ (Value.Val × FlatCursor)}
    {res : Option (IVal × List Flat)} {ys : List Flat} {n' : Nat} (h32 : t ≠ .f32)
    (h64 : t ≠ .f64) (hr : ∀ ts, t ≠ .record ts) (h : LiftRel prog res ys n') :
    LiftRelC t prog res ys n' := by
  cases res with
  | none => exact h
  | some pr =>
    obtain ⟨w, r⟩ := pr
    obtain ⟨hp, hr'⟩ := h
    exact ⟨by rw [hp, canonAt_other h32 h64 hr], hr'⟩

theorem wrap_f32 (b : BitVec (Silmaril.Wasm.NumType.float .f32).width) :
    wrapI64ToI32 ⟨.float .f32, b⟩ = b := by
  change BitVec.ofNat 32 (b : BitVec 32).toNat = (b : BitVec 32)
  rw [BitVec.ofNat_toNat]
  exact BitVec.setWidth_eq _

theorem bits64_f64 (b : BitVec (Silmaril.Wasm.NumType.float .f64).width) :
    flatBits64 ⟨.float .f64, b⟩ = b := by
  change BitVec.ofNat 64 (b : BitVec 64).toNat = (b : BitVec 64)
  rw [BitVec.ofNat_toNat]
  exact BitVec.setWidth_eq _

/-- An `f32` lifts canonicalised. -/
theorem liftAt_f32 (ys : List Flat) (n : Nat) (ht : Typed (ValTy.flat .f32) (ys.drop n)) :
    LiftRelC (σ := σ) .f32 (liftFlatAt (σ := σ) lim q cx p (toClosed .f32) ⟨ys, n⟩)
      (ValTy.lift .f32 (ys.drop n)) ys (n + (ValTy.flat .f32).length) := by
  obtain ⟨y, rest, hd⟩ := drop_cons_of_typed ht (List.cons_ne_nil _ _)
  have hy : y.type = .float .f32 := typed_head (hd ▸ ht)
  obtain ⟨ty, b⟩ := y
  have hty : ty = .float .f32 := hy
  subst hty
  have hrest : rest = ys.drop (n + 1) := (drop_succ_of hd).symm
  rw [hd]
  refine ⟨?_, hrest⟩
  simp only [toClosed, liftFlatAt, liftFlatPrim, next_eq hd, pure_bind, wrap_f32]
  rfl

/-- An `f64` lifts canonicalised. -/
theorem liftAt_f64 (ys : List Flat) (n : Nat) (ht : Typed (ValTy.flat .f64) (ys.drop n)) :
    LiftRelC (σ := σ) .f64 (liftFlatAt (σ := σ) lim q cx p (toClosed .f64) ⟨ys, n⟩)
      (ValTy.lift .f64 (ys.drop n)) ys (n + (ValTy.flat .f64).length) := by
  obtain ⟨y, rest, hd⟩ := drop_cons_of_typed ht (List.cons_ne_nil _ _)
  have hy : y.type = .float .f64 := typed_head (hd ▸ ht)
  obtain ⟨ty, b⟩ := y
  have hty : ty = .float .f64 := hy
  subst hty
  have hrest : rest = ys.drop (n + 1) := (drop_succ_of hd).symm
  rw [hd]
  refine ⟨?_, hrest⟩
  simp only [toClosed, liftFlatAt, liftFlatPrim, next_eq hd, pure_bind, bits64_f64]
  rfl

/-- A record lifts as its fields. -/
theorem liftRelC_record {ts : List ValTy} {ys : List Flat} {n n' : Nat}
    {prog : P E σ (List Value.Val × FlatCursor)}
    (h : LiftsRelC ts prog (ValTy.liftList ts (ys.drop n)) ys n') :
    LiftRelC (.record ts) (prog >>= fun x => pure (Value.Val.record x.1, x.2))
      (ValTy.lift (.record ts) (ys.drop n)) ys n' := by
  simp only [ValTy.lift]
  revert h
  cases ValTy.liftList ts (ys.drop n) with
  | none => intro h; exact h.bind _
  | some pr =>
    intro h
    obtain ⟨hp, hr⟩ := h
    refine ⟨?_, hr⟩
    rw [hp]
    rfl

/-- One field more, after the first lifted. -/
theorem liftsRelC_cons {t : ValTy} {ts : List ValTy} {ys : List Flat} {n : Nat} {w : IVal}
    {prog₂ : P E σ (List Value.Val × FlatCursor)}
    (ih₂ : LiftsRelC ts prog₂ (ValTy.liftList ts (ys.drop (n + t.flat.length))) ys
      (n + t.flat.length + (ValTy.flatList ts).length)) :
    LiftsRelC (t :: ts) (prog₂ >>= fun x => pure (toRefVal (canonAt t w) :: x.1, x.2))
      ((ValTy.liftList ts (ys.drop (n + t.flat.length))).map fun p => (w :: p.1, p.2)) ys
      (n + (t.flat.length + (ValTy.flatList ts).length)) := by
  revert ih₂
  cases ValTy.liftList ts (ys.drop (n + t.flat.length)) with
  | none => intro ih₂; exact ih₂.bind _
  | some pr₂ =>
    intro ih₂
    obtain ⟨hp₂, hr₂⟩ := ih₂
    refine ⟨?_, by rw [hr₂, Nat.add_assoc]⟩
    rw [hp₂, pure_bind, Nat.add_assoc]
    rfl

mutual
/-- **Reference `lift_flat` with floats** is the canonicalised IR lift, or traps where the IR
lift fails. -/
theorem liftAt_float : ∀ (t : ValTy) (ys : List Flat) (n : Nat), floatOk t = true →
    Typed t.flat (ys.drop n) →
      LiftRelC (σ := σ) t (liftFlatAt (σ := σ) lim q cx p (toClosed t) ⟨ys, n⟩)
        (ValTy.lift t (ys.drop n)) ys (n + t.flat.length)
  | .f32, ys, n, _, ht => liftAt_f32 lim q cx p ys n ht
  | .f64, ys, n, _, ht => liftAt_f64 lim q cx p ys n ht
  | .record ts, ys, n, hf, ht => by
    have ih := liftFields_float ts (labels "f" (toClosedList ts)) ys n (labels_map_snd "f" _)
      (by simpa only [floatOk] using hf) (by simpa only [ValTy.flat] using ht)
    simp only [ValTy.flat]
    exact liftRelC_record ih
  | .bool, ys, n, hf, ht | .s8, ys, n, hf, ht | .u8, ys, n, hf, ht | .s16, ys, n, hf, ht
  | .u16, ys, n, hf, ht | .s32, ys, n, hf, ht | .u32, ys, n, hf, ht | .s64, ys, n, hf, ht
  | .u64, ys, n, hf, ht | .char, ys, n, hf, ht | .variant _, ys, n, hf, ht =>
    liftRelC_of (by simp) (by simp) (by simp)
      (liftFlatAt_toClosed lim q cx p _ ys n
        (floatFree_of_floatOk hf (by simp) (by simp) (by simp)) ht)

/-- `liftAt_float` on record fields. -/
theorem liftFields_float : ∀ (ts : List ValTy) (fs : List (String × WIT.ClosedType RtId))
    (ys : List Flat) (n : Nat), fs.map Prod.snd = toClosedList ts → floatOkList ts = true →
      Typed (ValTy.flatList ts) (ys.drop n) →
        LiftsRelC (σ := σ) ts (liftFlatFields (σ := σ) lim q cx p fs ⟨ys, n⟩)
          (ValTy.liftList ts (ys.drop n)) ys (n + (ValTy.flatList ts).length)
  | [], [], ys, n, _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => by simp [toClosedList] at h
  | t :: ts, (nm, u) :: fs, ys, n, hfs, hf, ht => by
    have hfs' : u = toClosed t ∧ fs.map Prod.snd = toClosedList ts := by
      simpa only [List.map_cons, toClosedList, List.cons.injEq] using hfs
    have hf' : floatOk t = true ∧ floatOkList ts = true := by
      simpa only [floatOkList, Bool.and_eq_true] using hf
    have ht' : Typed (t.flat ++ ValTy.flatList ts) (ys.drop n) := by
      simpa only [ValTy.flatList] using ht
    have ih₁ := liftAt_float t ys n hf'.1 ht'.left
    rw [hfs'.1]
    simp only [liftFlatFields, ValTy.liftList, ValTy.flatList, List.length_append]
    revert ih₁
    cases ValTy.lift t (ys.drop n) with
    | none => intro ih₁; exact ih₁.bind _
    | some pr =>
      intro ih₁
      obtain ⟨w, r⟩ := pr
      obtain ⟨hp, hr⟩ := ih₁
      have ht₂ : Typed (ValTy.flatList ts) (ys.drop (n + t.flat.length)) := by
        have h₂ := ht'.right
        rwa [List.drop_drop] at h₂
      have ih₂ := liftFields_float ts fs ys (n + t.flat.length) hfs'.2 hf'.2 ht₂
      rw [hp, pure_bind, hr]
      exact liftsRelC_cons ih₂
end

/-- `liftFields_float` on argument lists. -/
theorem liftFlatTypes_float (ts : List ValTy) (ys : List Flat) (n : Nat)
    (hf : floatOkList ts = true) (ht : Typed (ValTy.flatList ts) (ys.drop n)) :
    LiftsRelC (σ := σ) ts (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, n⟩)
      (ValTy.liftList ts (ys.drop n)) ys (n + (ValTy.flatList ts).length) := by
  have h := liftFields_float (σ := σ) lim q cx p ts _ ys n (labels_map_snd "f" _) hf ht
  have heq : ∀ (fs : List (String × WIT.ClosedType RtId)) (c : FlatCursor),
      (liftFlatFields (σ := σ) lim q cx p fs c) = liftFlatTypes lim q cx p (fs.map Prod.snd) c := by
    intro fs
    induction fs with
    | nil => intro c; rfl
    | cons f fs ih =>
      intro c
      obtain ⟨nm, u⟩ := f
      simp only [liftFlatFields, liftFlatTypes, List.map_cons, ih]
  rwa [heq, labels_map_snd] at h

/-- **The direct lift path with floats relates to `liftArgs`**: the canonicalised results, or a
trap at the first operation where `liftArgs` fails. -/
theorem liftFlatTypes_liftArgs_float {ts : List ValTy} {ys : List Flat}
    (hf : floatOkList ts = true) (hys : ys.map (·.type) = ValTy.flatList ts) :
    match liftArgs ts ys with
    | some ws => ∃ c, (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, 0⟩) =
        pure ((canonAtList ts ws).map toRefVal, c)
    | none => IsTrap (liftFlatTypes (σ := σ) lim q cx p (toClosedList ts) ⟨ys, 0⟩) := by
  have hlen : ys.length = (ValTy.flatList ts).length := by rw [← hys, List.length_map]
  have ht : Typed (ValTy.flatList ts) (ys.drop 0) := by
    refine ⟨?_, by simp [hlen]⟩
    rw [List.drop_zero, ← hlen, List.take_length, hys]
  have h := liftFlatTypes_float (σ := σ) lim q cx p ts ys 0 hf ht
  rw [List.drop_zero] at h
  unfold liftArgs
  revert h
  cases ValTy.liftList ts ys with
  | none => intro h; exact h
  | some pr =>
    intro h
    obtain ⟨ws, r⟩ := pr
    obtain ⟨hp, hr⟩ := h
    have hr' : r = [] := by rw [hr, Nat.zero_add, ← hlen, List.drop_length]
    subst hr'
    exact ⟨_, by rw [hp, toRefVals_eq]⟩

/-! ## The deterministic profile -/

/-- Under the deterministic profile a float lowers to its canonicalisation only. -/
theorem nanLower_deterministic {t : Silmaril.Wasm.FloatType} {x y : BitVec t.width}
    (h : NanLower .deterministic t x y) : y = canonicalizeNaN t x :=
  (scrambleNaN_true_iff t x y).mp h

mutual
/-- **Under the deterministic profile the admissible lowering is unique**: the
canonicalisation. -/
theorem nanAt_deterministic : ∀ (t : ValTy) (v w : Silmaril.Wasm.Component.Val),
    NanAt .deterministic t v w → w = canonAt t v
  | .f32, .f32 x, .f32 y, h => congrArg _ (nanLower_deterministic h)
  | .f64, .f64 x, .f64 y, h => congrArg _ (nanLower_deterministic h)
  | .record ts, .record vs, .record ws, h => congrArg _ (nanAtList_deterministic ts vs ws h)
  | .f32, .f32 _, .bool _, h | .f32, .f32 _, .s8 _, h | .f32, .f32 _, .u8 _, h
  | .f32, .f32 _, .s16 _, h | .f32, .f32 _, .u16 _, h | .f32, .f32 _, .s32 _, h
  | .f32, .f32 _, .u32 _, h | .f32, .f32 _, .s64 _, h | .f32, .f32 _, .u64 _, h
  | .f32, .f32 _, .f64 _, h | .f32, .f32 _, .char _, h | .f32, .f32 _, .record _, h
  | .f32, .f32 _, .variant _ _, h | .f64, .f64 _, .bool _, h | .f64, .f64 _, .s8 _, h
  | .f64, .f64 _, .u8 _, h | .f64, .f64 _, .s16 _, h | .f64, .f64 _, .u16 _, h
  | .f64, .f64 _, .s32 _, h | .f64, .f64 _, .u32 _, h | .f64, .f64 _, .s64 _, h
  | .f64, .f64 _, .u64 _, h | .f64, .f64 _, .f32 _, h | .f64, .f64 _, .char _, h
  | .f64, .f64 _, .record _, h | .f64, .f64 _, .variant _ _, h
  | .record _, .record _, .bool _, h | .record _, .record _, .s8 _, h
  | .record _, .record _, .u8 _, h | .record _, .record _, .s16 _, h
  | .record _, .record _, .u16 _, h | .record _, .record _, .s32 _, h
  | .record _, .record _, .u32 _, h | .record _, .record _, .s64 _, h
  | .record _, .record _, .u64 _, h | .record _, .record _, .f32 _, h
  | .record _, .record _, .f64 _, h | .record _, .record _, .char _, h
  | .record _, .record _, .variant _ _, h => by cases h
  | .f32, .bool _, _, h | .f32, .s8 _, _, h | .f32, .u8 _, _, h | .f32, .s16 _, _, h
  | .f32, .u16 _, _, h | .f32, .s32 _, _, h | .f32, .u32 _, _, h | .f32, .s64 _, _, h
  | .f32, .u64 _, _, h | .f32, .f64 _, _, h | .f32, .char _, _, h | .f32, .record _, _, h
  | .f32, .variant _ _, _, h | .f64, .bool _, _, h | .f64, .s8 _, _, h | .f64, .u8 _, _, h
  | .f64, .s16 _, _, h | .f64, .u16 _, _, h | .f64, .s32 _, _, h | .f64, .u32 _, _, h
  | .f64, .s64 _, _, h | .f64, .u64 _, _, h | .f64, .f32 _, _, h | .f64, .char _, _, h
  | .f64, .record _, _, h | .f64, .variant _ _, _, h | .record _, .bool _, _, h
  | .record _, .s8 _, _, h | .record _, .u8 _, _, h | .record _, .s16 _, _, h
  | .record _, .u16 _, _, h | .record _, .s32 _, _, h | .record _, .u32 _, _, h
  | .record _, .s64 _, _, h | .record _, .u64 _, _, h | .record _, .f32 _, _, h
  | .record _, .f64 _, _, h | .record _, .char _, _, h | .record _, .variant _ _, _, h
  | .bool, _, _, h | .s8, _, _, h | .u8, _, _, h | .s16, _, _, h | .u16, _, _, h
  | .s32, _, _, h | .u32, _, _, h | .s64, _, _, h | .u64, _, _, h | .char, _, _, h
  | .variant _, _, _, h => h.symm

/-- `nanAt_deterministic` on lists. -/
theorem nanAtList_deterministic : ∀ (ts : List ValTy) (vs ws : List Silmaril.Wasm.Component.Val),
    NanAtList .deterministic ts vs ws → ws = canonAtList ts vs
  | t :: ts, v :: vs, w :: ws, h =>
    congrArg₂ List.cons (nanAt_deterministic t v w h.1) (nanAtList_deterministic ts vs ws h.2)
  | t :: ts, v :: vs, [], h => by cases h
  | [], _, _, h | _ :: _, [], _, h => h.symm
end

end Silmaril.Proofs.Wasm.Component.Reference
