module

public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Computable interpreter: pure families (parametric and numeric)

`parametricStep?` and `numericStep?` compute the head steps of the
`ParametricStep` and `NumericStep` families in the single-threaded
deterministic profile, with soundness and completeness against `Det.Head`.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace Pure

/-- The top value of the stack. -/
def top1 (vs : List Val) : Option Val := vs.getLast?

/-- The top two values, bottom-first. -/
def top2 (vs : List Val) : Option (Val × Val) :=
  match vs.reverse with
  | w :: v :: _ => some (v, w)
  | _ => none

/-- The top three values, bottom-first. -/
def top3 (vs : List Val) : Option (Val × Val × Val) :=
  match vs.reverse with
  | c :: w :: v :: _ => some (v, w, c)
  | _ => none

/-- A numeric value of the given type. -/
def asNum (n : NumType) : Val → Option (BitVec n.width)
  | .num ⟨n', x⟩ => if h : n' = n then some (h ▸ x) else none
  | _ => none

theorem asNum_eq_some {n : NumType} {v : Val} {x : BitVec n.width} :
    asNum n v = some x ↔ v = .num ⟨n, x⟩ := by
  rcases v with ⟨n', x'⟩ | _ | _
  · by_cases h : n' = n
    · subst h; simp [asNum]
    · simp [asNum, h]
  · simp [asNum]
  · simp [asNum]

@[simp] theorem asNum_num (n : NumType) (x : BitVec n.width) :
    asNum n (.num ⟨n, x⟩) = some x := asNum_eq_some.mpr rfl

/-- An integer value of the given type. -/
def asInt (t : IntType) : Val → Option (BitVec t.width)
  | .num ⟨.int t', x⟩ => if h : t' = t then some (cast (by subst h; rfl) x) else none
  | _ => none

/-- A float value of the given type. -/
def asFloat (t : FloatType) : Val → Option (BitVec t.width)
  | .num ⟨.float t', x⟩ => if h : t' = t then some (cast (by subst h; rfl) x) else none
  | _ => none

/-- An `i32` value. -/
def asI32 : Val → Option (BitVec 32)
  | .num ⟨.int .i32, x⟩ => some x
  | _ => none

theorem asInt_eq_some {t : IntType} {v : Val} {x : BitVec t.width} :
    asInt t v = some x ↔ v = .num ⟨.int t, x⟩ := by
  constructor
  · intro h
    rcases v with ⟨(t' | t'), x'⟩ | _ | _ <;> try simp only [asInt] at h
    all_goals try (split at h)
    all_goals first
      | (rename_i he; subst he; injection h with h; subst h; rfl)
      | cases h
  · rintro rfl; exact dite_eq_left rfl

theorem asFloat_eq_some {t : FloatType} {v : Val} {x : BitVec t.width} :
    asFloat t v = some x ↔ v = .num ⟨.float t, x⟩ := by
  constructor
  · intro h
    rcases v with ⟨(t' | t'), x'⟩ | _ | _ <;> try simp only [asFloat] at h
    all_goals try (split at h)
    all_goals first
      | (rename_i he; subst he; injection h with h; subst h; rfl)
      | cases h
  · rintro rfl; exact dite_eq_left rfl

theorem asI32_eq_some {v : Val} {x : BitVec 32} : asI32 v = some x ↔ v = .num ⟨.int .i32, x⟩ := by
  constructor
  · intro h
    rcases v with ⟨((_ | _) | t'), x'⟩ | _ | _ <;> try simp only [asI32] at h
    all_goals first
      | (injection h with h; subst h; rfl)
      | cases h
  · rintro rfl; rfl

@[simp] theorem asInt_num (t : IntType) (x : BitVec t.width) :
    asInt t (.num ⟨.int t, x⟩) = some x := asInt_eq_some.mpr rfl

@[simp] theorem asFloat_num (t : FloatType) (x : BitVec t.width) :
    asFloat t (.num ⟨.float t, x⟩) = some x := asFloat_eq_some.mpr rfl

@[simp] theorem asI32_num (x : BitVec 32) : asI32 (.num ⟨.int .i32, x⟩) = some x :=
  asI32_eq_some.mpr rfl

theorem top1_sound {vs : List Val} {v : Val} (h : top1 vs = some v) :
    1 ≤ vs.length ∧ vs.drop (vs.length - 1) = [v] := by
  unfold top1 at h
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h
  simp

theorem top2_sound {vs : List Val} {v w : Val} (h : top2 vs = some (v, w)) :
    2 ≤ vs.length ∧ vs.drop (vs.length - 2) = [v, w] := by
  unfold top2 at h
  split at h
  · rename_i w' v' r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : vs = r.reverse ++ [v', w'] := by
      rw [← List.reverse_reverse vs, heq]; simp
    subst this; simp
  · simp at h

theorem top3_sound {vs : List Val} {v w c : Val} (h : top3 vs = some (v, w, c)) :
    3 ≤ vs.length ∧ vs.drop (vs.length - 3) = [v, w, c] := by
  unfold top3 at h
  split at h
  · rename_i c' w' v' r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have : vs = r.reverse ++ [v', w', c'] := by
      rw [← List.reverse_reverse vs, heq]; simp
    subst this; simp
  · simp at h

@[simp] theorem top1_app (q : List Val) (v : Val) : top1 (q ++ [v]) = some v := by
  simp [top1]

@[simp] theorem top2_app (q : List Val) (v w : Val) : top2 (q ++ [v, w]) = some (v, w) := by
  simp [top2]

@[simp] theorem top3_app (q : List Val) (v w c : Val) :
    top3 (q ++ [v, w, c]) = some (v, w, c) := by
  simp [top3]

theorem filterMap_vals (args : List Val) : (vals args).filterMap Admin.val? = args := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- Read the arguments and the instruction off a family left-hand side. -/
theorem inv_args {args : List Val} {e : Admin} {l : List Admin} (h : vals args ++ [e] = l) :
    args = l.dropLast.filterMap Admin.val? ∧ l.getLast? = some e := by
  subst h; simp [filterMap_vals]

end Pure

open _root_.Silmaril.Wasm.SingleThreaded.Exec.Pure

/-! ## Parametric instructions -/

/-- Head step of the parametric family. -/
def parametricStep? (_o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match e with
  | .plain .nop => some (0, ⟨s, f, []⟩)
  | .plain .unreachable => some (0, ⟨s, f, [.trap]⟩)
  | .plain .drop => (top1 vs).map fun _ => (1, ⟨s, f, []⟩)
  | .plain (.select _) =>
    (top3 vs).bind fun p =>
      (asI32 p.2.2).map fun b =>
        (3, ⟨s, f, [if b = 0 then p.2.1.toAdmin else p.1.toAdmin]⟩)
  | _ => none

theorem parametricStep?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {e : Admin} {k : Nat} {c : Config H} (h : parametricStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  unfold parametricStep? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, by simpa using Head.parametric (s := s) (f := f) (P := profile o) (args := []) (e := .plain .nop) ParametricStep.nop⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, by simpa using Head.parametric (s := s) (f := f) (P := profile o) (args := []) (e := .plain .unreachable) ParametricStep.unreachable⟩
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨v, hv, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top1_sound hv
    refine ⟨hk, ?_⟩
    rw [hd]
    exact Head.parametric (ParametricStep.drop v)
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨v₁, v₂, cv⟩, hp, h⟩ := h
    cases hb : asI32 cv with
    | none => simp [hb] at h
    | some b =>
    simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top3_sound hp
    simp only [asI32_eq_some] at hb
    subst hb
    refine ⟨hk, ?_⟩
    rw [hd]
    split
    · rename_i hb0
      subst hb0
      exact Head.parametric (ParametricStep.selectFalse v₁ v₂ _)
    · rename_i hb0
      exact Head.parametric (ParametricStep.selectTrue (c := b) hb0)
  · simp at h

theorem parametricStep?_complete {o : GrowOracle} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {c : Config H} (h : Head (profile o) s f args e c)
    (hf : famOf e = .parametric) (hq : ∃ q, vs = q ++ args) :
    parametricStep? o s f vs e = some (args.length, c) := by
  have hr := h.fam_inv (by rw [hf]; decide)
  rw [hf] at hr
  obtain ⟨is', hs, rfl⟩ := hr
  obtain ⟨q, rfl⟩ := hq
  generalize hl : vals args ++ [e] = l at hs
  cases hs with
  | unreachable =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; rfl
  | nop =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; rfl
  | drop v =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [parametricStep?]
  | selectTrue hc =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [parametricStep?, Val.i32]; intro h0; exact absurd h0 hc
  | selectFalse v₁ v₂ ts =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [parametricStep?, Val.i32]

/-! ## Numeric instructions -/

/-- Head step of the numeric family (canonical NaNs). -/
def numericStep? (_o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match e with
  | .plain (.intUnOp t op) =>
    (top1 vs).bind fun v => (asInt t v).map fun x =>
      (1, ⟨s, f, [.plain (.intConst t (intUnOp t op x))]⟩)
  | .plain (.floatUnOp t op) =>
    (top1 vs).bind fun v => (asFloat t v).map fun x =>
      (1, ⟨s, f, [.plain (.floatConst t (floatUnOp t op x))]⟩)
  | .plain (.intTestOp t op) =>
    (top1 vs).bind fun v => (asInt t v).map fun x =>
      (1, ⟨s, f, [constI32 (intTestOp t op x)]⟩)
  | .plain (.intBinOp t op) =>
    (top2 vs).bind fun p => (asInt t p.1).bind fun x =>
      (asInt t p.2).map fun y =>
        (2, ⟨s, f, match intBinOp t op x y with
          | .ok z => [.plain (.intConst t z)]
          | .error _ => [.trap]⟩)
  | .plain (.floatBinOp t op) =>
    (top2 vs).bind fun p => (asFloat t p.1).bind fun x =>
      (asFloat t p.2).map fun y =>
        (2, ⟨s, f, [.plain (.floatConst t (floatBinOp t op x y))]⟩)
  | .plain (.intRelOp t op) =>
    (top2 vs).bind fun p => (asInt t p.1).bind fun x =>
      (asInt t p.2).map fun y =>
        (2, ⟨s, f, [constI32 (intRelOp t op x y)]⟩)
  | .plain (.floatRelOp t op) =>
    (top2 vs).bind fun p => (asFloat t p.1).bind fun x =>
      (asFloat t p.2).map fun y =>
        (2, ⟨s, f, [constI32 (floatRelOp t op x y)]⟩)
  | .plain (.convert op) =>
    (top1 vs).bind fun v => (asNum op.source v).map fun x =>
      (1, ⟨s, f, match convert op x with
        | .ok z => [(Val.num ⟨op.target, z⟩).toAdmin]
        | .error _ => [.trap]⟩)
  | _ => none

theorem numericStep?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val}
    {e : Admin} {k : Nat} {c : Config H} (h : numericStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  unfold numericStep? at h
  split at h
  all_goals try simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  · obtain ⟨v, hv, x, hx, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top1_sound hv
    simp only [asInt_eq_some] at hx; subst hx
    exact ⟨hk, by rw [hd]; exact Head.numeric NumericStep.intUnOp⟩
  · obtain ⟨v, hv, x, hx, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top1_sound hv
    simp only [asFloat_eq_some] at hx; subst hx
    exact ⟨hk, by rw [hd]; exact Head.numeric (NumericStep.floatUnOp (by simp [floatUnOpP]))⟩
  · obtain ⟨v, hv, x, hx, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top1_sound hv
    simp only [asInt_eq_some] at hx; subst hx
    exact ⟨hk, by rw [hd]; exact Head.numeric NumericStep.intTestOp⟩
  · obtain ⟨⟨v, w⟩, hp, x, hx, y, hy, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top2_sound hp
    simp only [asInt_eq_some] at hx hy; subst hx hy
    refine ⟨hk, ?_⟩
    rw [hd]
    split
    · rename_i z hz; exact Head.numeric (NumericStep.intBinOp hz)
    · rename_i z hz; exact Head.numeric (NumericStep.intBinOpTrap hz)
  · obtain ⟨⟨v, w⟩, hp, x, hx, y, hy, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top2_sound hp
    simp only [asFloat_eq_some] at hx hy; subst hx hy
    exact ⟨hk, by rw [hd]; exact Head.numeric (NumericStep.floatBinOp (by simp [floatBinOpP]))⟩
  · obtain ⟨⟨v, w⟩, hp, x, hx, y, hy, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top2_sound hp
    simp only [asInt_eq_some] at hx hy; subst hx hy
    exact ⟨hk, by rw [hd]; exact Head.numeric NumericStep.intRelOp⟩
  · obtain ⟨⟨v, w⟩, hp, x, hx, y, hy, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top2_sound hp
    simp only [asFloat_eq_some] at hx hy; subst hx hy
    exact ⟨hk, by rw [hd]; exact Head.numeric NumericStep.floatRelOp⟩
  · obtain ⟨v, hv, x, hx, rfl, rfl⟩ := h
    obtain ⟨hk, hd⟩ := top1_sound hv
    simp only [asNum_eq_some] at hx; subst hx
    refine ⟨hk, ?_⟩
    rw [hd]
    split
    · rename_i z hz
      exact Head.numeric (NumericStep.convert (by simp [convertP, hz]))
    · rename_i z hz
      exact Head.numeric (NumericStep.convertTrap (e := z) (by simp [convertP, hz]))
  · simp at h

theorem numericStep?_complete {o : GrowOracle} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {c : Config H} (h : Head (profile o) s f args e c)
    (hf : famOf e = .numeric) (hq : ∃ q, vs = q ++ args) :
    numericStep? o s f vs e = some (args.length, c) := by
  have hr := h.fam_inv (by rw [hf]; decide)
  rw [hf] at hr
  obtain ⟨is', hs, rfl⟩ := hr
  obtain ⟨q, rfl⟩ := hq
  generalize hl : vals args ++ [e] = l at hs
  cases hs with
  | intUnOp =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [numericStep?]
  | floatUnOp hz =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [floatUnOpP] at hz; subst hz; simp [numericStep?]
  | intBinOp hz =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [numericStep?, hz]
  | intBinOpTrap hz =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [numericStep?, hz]
  | floatBinOp hz =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [floatBinOpP] at hz; subst hz; simp [numericStep?]
  | intTestOp =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [numericStep?]
  | intRelOp =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [numericStep?]
  | floatRelOp =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [numericStep?]
  | convert hz =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [convertP] at hz; simp [numericStep?, ← hz]
  | convertTrap hz =>
    obtain ⟨rfl, he⟩ := inv_args hl
    simp at he; subst he; simp [convertP] at hz; simp [numericStep?, ← hz]

end Silmaril.Wasm.SingleThreaded.Exec
