module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Logic.Core.Thms

@[expose] public section

/-!
# Straight-line native evaluation is Core 3.0 straight-line execution: proofs

`exec1_of_evalFlat`: on a straight-line integer instruction (with in-range local writes), a
normal step of silmaril-lean's native `evalFlat` is a step of Silmaril's straight-line Core
evaluator `Silmaril.Wasm.Logic.Core.exec1` (whose soundness `exec_sound` gives Core 3.0 runs at
every profile and host). `exec_of_eval`: a normal native evaluation `Binaryen.Eval` of
straight-line trees is the `exec` of their lowering. New proofs. Summary in
`Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core

variable {H : Type} {s s' : Store H} {f f' : Frame} {stk stk' : List Val}

/-- Popping an integer is reading the top value. -/
theorem popInt_cons (t : IntType) (x : Val) (r : List Val) :
    popInt t (x :: r) = (Binaryen.asInt t x).map (fun a => (a, r)) := by
  rcases x with ⟨⟨ty, b⟩⟩ | _ | _ <;> (try rcases ty with ty | ty) <;> (try cases ty) <;> cases t <;> rfl
theorem flat_intBinOp (t : IntType) (op : IntBinOp)
  (h : Binaryen.evalFlat s f stk (.intBinOp t op) = some (s', f', .normal stk')) :
  exec1 s f stk (.intBinOp t op) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  rcases stk with _ | ⟨y, _ | ⟨x, r⟩⟩
  · simp [Binaryen.evalFlat] at h
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    cases hx : Binaryen.asInt t x <;> cases hy : Binaryen.asInt t y <;> simp [hx, hy] at h
    simp only [exec1, popInt_cons, hx, hy, Option.map_some, Option.bind_some]
    split at h <;> simp_all [Binaryen.ofInt]
theorem flat_intRelOp (t : IntType) (op : IntRelOp)
  (h : Binaryen.evalFlat s f stk (.intRelOp t op) = some (s', f', .normal stk')) :
  exec1 s f stk (.intRelOp t op) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  rcases stk with _ | ⟨y, _ | ⟨x, r⟩⟩
  · simp [Binaryen.evalFlat] at h
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    cases hx : Binaryen.asInt t x <;> cases hy : Binaryen.asInt t y <;> simp [hx, hy] at h
    simp only [exec1, popInt_cons, hx, hy, Option.map_some, Option.bind_some]
    simp_all [Binaryen.ofInt, Val.i32]
theorem flat_intUnOp (t : IntType) (op : IntUnOp)
  (h : Binaryen.evalFlat s f stk (.intUnOp t op) = some (s', f', .normal stk')) :
  exec1 s f stk (.intUnOp t op) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  rcases stk with _ | ⟨x, r⟩
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    cases hx : Binaryen.asInt t x <;> simp only [hx, Option.map_some, Option.map_none, reduceCtorEq] at h
    simp only [exec1, popInt_cons, hx, Option.map_some]
    simp_all [Binaryen.ofInt]
theorem flat_intTestOp (t : IntType) (op : IntTestOp)
  (h : Binaryen.evalFlat s f stk (.intTestOp t op) = some (s', f', .normal stk')) :
  exec1 s f stk (.intTestOp t op) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  rcases stk with _ | ⟨x, r⟩
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    cases hx : Binaryen.asInt t x <;> simp only [hx, Option.map_some, Option.map_none, reduceCtorEq] at h
    simp only [exec1, popInt_cons, hx, Option.map_some]
    simp_all [Binaryen.ofInt, Val.i32]
theorem flat_localGet (x : LocalIdx)
  (h : Binaryen.evalFlat s f stk (.localGet x) = some (s', f', .normal stk')) :
  exec1 s f stk (.localGet x) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  simp only [Binaryen.evalFlat] at h
  simp only [exec1, localVal?, Frame.local?]
  cases hv : f.locals[x.toNat]? with
  | none => simp [hv] at h
  | some o => cases o <;> simp_all
theorem flat_localSet (x : LocalIdx) (hx : x.toNat < f.locals.length)
  (h : Binaryen.evalFlat s f stk (.localSet x) = some (s', f', .normal stk')) :
  exec1 s f stk (.localSet x) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  rcases stk with _ | ⟨v, r⟩
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    simp only [exec1, popV, Option.bind_some, hx, ite_true]
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Frame.setLocal]
theorem flat_localTee (x : LocalIdx) (hx : x.toNat < f.locals.length)
  (h : Binaryen.evalFlat s f stk (.localTee x) = some (s', f', .normal stk')) :
  exec1 s f stk (.localTee x) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  rcases stk with _ | ⟨v, r⟩
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    simp only [exec1, popV, Option.bind_some, hx, ite_true]
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Frame.setLocal]
theorem flat_globalGet (x : GlobalIdx)
  (h : Binaryen.evalFlat s f stk (.globalGet x) = some (s', f', .normal stk')) :
  exec1 s f stk (.globalGet x) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  simp only [Binaryen.evalFlat] at h
  simp only [exec1]
  cases hg : s.global? f x <;> simp_all
theorem flat_globalSet (x : GlobalIdx)
  (h : Binaryen.evalFlat s f stk (.globalSet x) = some (s', f', .normal stk')) :
  exec1 s f stk (.globalSet x) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  rcases stk with _ | ⟨v, r⟩
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    simp only [exec1, popV, Option.bind_some]
    cases hg : s.global? f x <;> simp_all
theorem flat_drop (h : Binaryen.evalFlat s f stk .drop = some (s', f', .normal stk')) :
  exec1 s f stk .drop = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  rcases stk with _ | ⟨v, r⟩
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    simp only [exec1, popV, Option.map_some]
    simp_all
theorem flat_nop (h : Binaryen.evalFlat s f stk .nop = some (s', f', .normal stk')) :
  exec1 s f stk .nop = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  simp only [Binaryen.evalFlat] at h
  simp_all [exec1]
theorem flat_intConst (t : IntType) (b : BitVec t.width)
    (h : Binaryen.evalFlat s f stk (.intConst t b) = some (s', f', .normal stk')) :
  exec1 s f stk (.intConst t b) = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  simp only [Binaryen.evalFlat] at h
  simp_all [exec1, Binaryen.ofInt]
theorem exec1_of_evalFlat {i : Instr} (hs : Instr.straight i = true)
    (hb : Instr.setsBelow f.locals.length i = true)
    (h : Binaryen.evalFlat s f stk i = some (s', f', .normal stk')) :
    exec1 s f stk i = some (s', f', stk') ∧ f'.locals.length = f.locals.length := by
  cases i <;> simp only [Instr.straight, Bool.false_eq_true] at hs
  all_goals first
    | exact flat_intBinOp _ _ h | exact flat_intRelOp _ _ h | exact flat_intUnOp _ _ h
    | exact flat_intTestOp _ _ h
    | exact flat_localGet _ h | exact flat_globalGet _ h | exact flat_globalSet _ h
    | exact flat_drop h
    | exact flat_nop h
    | exact flat_localSet _ (of_decide_eq_true hb) h
    | exact flat_localTee _ (of_decide_eq_true hb) h

theorem straight_op {n : Nat} {i : Instr} {args es : List Binaryen.BExpr}
    (h : BExpr.straightList n (.op i args :: es) = true) :
    Instr.straight i = true ∧ Instr.setsBelow n i = true ∧ BExpr.straightList n args = true ∧
      BExpr.straightList n es = true := by
  simp only [BExpr.straightList, BExpr.straight, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The lowering of an operator tree runs its arguments, then the operator. -/
theorem exec_op {s₁ s₂ : Store H} {f₁ f₂ : Frame} {stk₁ stk₂ : List Val} {i : Instr}
    {args es : List Binaryen.BExpr} {r : Option (Store H × Frame × List Val)}
    (e₁ : exec s f stk (Binaryen.BExpr.lowerList args) = some (s₁, f₁, stk₁))
    (e₂ : exec1 s₁ f₁ stk₁ i = some (s₂, f₂, stk₂))
    (e₃ : exec s₂ f₂ stk₂ (Binaryen.BExpr.lowerList es) = r) :
    exec s f stk (Binaryen.BExpr.lowerList (.op i args :: es)) = r := by
  rw [Binaryen.BExpr.lowerList_cons, Binaryen.BExpr.lower_op, List.append_assoc, exec_append, e₁]
  show exec s₁ f₁ stk₁ (i :: Binaryen.BExpr.lowerList es) = r
  rw [exec_cons_of_some e₂]
  exact e₃

/-- The operator case of `exec_of_eval`. -/
theorem eval_op_case {s₁ s₂ : Store H} {f₁ f₂ : Frame} {stk₁ stk₂ : List Val} {i : Instr}
    {args es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ih1 : ∀ {s' : Store H} {f' : Frame} {stk' : List Val},
      ((s₁, f₁, .normal stk₁) : Store H × Frame × Binaryen.Flow) = (s', f', .normal stk') →
      BExpr.straightList f.locals.length args = true →
      exec s f stk (Binaryen.BExpr.lowerList args) = some (s', f', stk') ∧
        f'.locals.length = f.locals.length)
    (ih2 : ∀ {s' : Store H} {f' : Frame} {stk' : List Val}, r = (s', f', .normal stk') →
      BExpr.straightList f₂.locals.length es = true →
      exec s₂ f₂ stk₂ (Binaryen.BExpr.lowerList es) = some (s', f', stk') ∧
        f'.locals.length = f₂.locals.length) :
    ∀ {s' : Store H} {f' : Frame} {stk' : List Val}, r = (s', f', .normal stk') →
      BExpr.straightList f.locals.length (.op i args :: es) = true →
      exec s f stk (Binaryen.BExpr.lowerList (.op i args :: es)) = some (s', f', stk') ∧
        f'.locals.length = f.locals.length := by
    intro s' f' stk' hr hst
    have h4 : Instr.straight i = true ∧ Instr.setsBelow f.locals.length i = true ∧
        BExpr.straightList f.locals.length args = true ∧
        BExpr.straightList f.locals.length es = true := straight_op hst
    have h1 : exec s f stk (Binaryen.BExpr.lowerList args) = some (s₁, f₁, stk₁) ∧
        f₁.locals.length = f.locals.length := ih1 rfl h4.2.2.1
    have h2 : exec1 s₁ f₁ stk₁ i = some (s₂, f₂, stk₂) ∧
        f₂.locals.length = f₁.locals.length :=
      exec1_of_evalFlat h4.1 (h1.2 ▸ h4.2.1) hflat
    have hse : BExpr.straightList f₂.locals.length es = true := by
      rw [h2.2, h1.2]
      exact h4.2.2.2
    have h3 : exec s₂ f₂ stk₂ (Binaryen.BExpr.lowerList es) = some (s', f', stk') ∧
        f'.locals.length = f₂.locals.length := ih2 hr hse
    exact ⟨exec_op h1.1 h2.1 h3.1, h3.2.trans (h2.2.trans h1.2)⟩

/-- **Normal native evaluation of straight-line trees is straight-line Core evaluation** of
their lowering; the number of locals is preserved. -/
theorem exec_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : Binaryen.Eval s f stk es r) :
    ∀ {s' : Store H} {f' : Frame} {stk' : List Val}, r = (s', f', .normal stk') →
      BExpr.straightList f.locals.length es = true →
      exec s f stk (Binaryen.BExpr.lowerList es) = some (s', f', stk') ∧
        f'.locals.length = f.locals.length := by
  induction h with
  | nil =>
    intro s' f' stk' hr _
    cases hr
    exact ⟨rfl, rfl⟩
  | @opOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hflat _ ih1 ih2 => exact eval_op_case hflat ih1 ih2
  | argsAbort _ hfl =>
    intro s' f' stk' hr _
    cases hr
    exact absurd trivial hfl
  | opStop _ _ _ hfl =>
    intro s' f' stk' hr _
    cases hr
    exact absurd trivial hfl
  | _ =>
    intro s' f' stk' _ hst
    simp [BExpr.straightList, BExpr.straight, Instr.straight] at hst

end Silmaril.Wasm.Interp
