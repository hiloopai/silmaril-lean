module

public import Silmaril.Proofs.Wasm.Interp.Straight

@[expose] public section

/-!
# Traps of straight-line native evaluation are Core 3.0 traps: proofs

`steps_trap_of_eval`: a native evaluation of straight-line trees ending in a trap (an integer
division or remainder by zero, or a signed overflow) is a Core 3.0 run of the lowering, in any
code context, to `[trap]`, at every profile and host. New proofs. Summary in
`Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core

variable {H : Type} {s s' : Store H} {f f' : Frame} {stk : List Val}

/-- A straight-line instruction completes normally, or is a binary operator (which may trap). -/
theorem flat_flow {i : Instr} (hs : Instr.straight i = true) {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) :
    fl.IsNormal ∨ ∃ t op, i = .intBinOp t op := by
  cases i <;> simp only [Instr.straight, Bool.false_eq_true] at hs
  case intBinOp t op => exact .inr ⟨t, op, rfl⟩
  all_goals
    rcases fl with _ | _ | _ | _ | _
    · exact .inl trivial
    all_goals
      simp only [Binaryen.evalFlat] at h
      (repeat' split at h) <;> simp [Option.bind_eq_some_iff] at h
variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- A value read as an integer is that integer. -/
theorem eq_ofInt_of_asInt {t : IntType} {x : Val} {a : BitVec t.width}
    (h : Binaryen.asInt t x = some a) : x = .num ⟨.int t, a⟩ := by
  rcases x with ⟨⟨ty, b⟩⟩ | _ | _ <;> (try rcases ty with ty | ty) <;> (try cases ty) <;> cases t <;>
    simp only [Binaryen.asInt, reduceCtorEq] at h <;> (cases h; rfl)

/-- Inversion of a trapping native binary operator. -/
theorem binop_trap_inv {t : IntType} {op : IntBinOp}
    (h : Binaryen.evalFlat s f stk (.intBinOp t op) = some (s', f', .trap)) :
    ∃ (a b : BitVec t.width) (r : List Val) (e : Numerics.IntTrap),
      stk = .num ⟨.int t, b⟩ :: .num ⟨.int t, a⟩ :: r ∧ Numerics.intBinOp t op a b = .error e ∧
        s' = s ∧ f' = f := by
  rcases stk with _ | ⟨y, _ | ⟨x, r⟩⟩
  · simp [Binaryen.evalFlat] at h
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    cases hx : Binaryen.asInt t x <;> cases hy : Binaryen.asInt t y <;> simp [hx, hy] at h
    rename_i a b
    split at h
    · simp at h
    · rename_i e he
      obtain ⟨rfl, rfl⟩ : s = s' ∧ f = f' := by simpa using h
      exact ⟨a, b, r, e, by rw [eq_ofInt_of_asInt hx, eq_ofInt_of_asInt hy], he, rfl, rfl⟩

/-- A trapping native binary operator is a Core 3.0 run to a trap. -/
theorem steps_binop_trap {t : IntType} {op : IntBinOp}
    (h : Binaryen.evalFlat s f stk (.intBinOp t op) = some (s', f', .trap)) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ [.plain (.intBinOp t op)] ++ rest⟩ ⟨s', f', [.trap]⟩ := by
  obtain ⟨a, b, r, e, rfl, he, hs, hf⟩ := binop_trap_inv h
  rw [hs, hf]
  have hstep : Step P host ⟨s, f, vals r.reverse ++
      [.plain (.intConst t a), .plain (.intConst t b), .plain (.intBinOp t op)] ++ rest⟩
      ⟨s, f, vals r.reverse ++ [.trap] ++ rest⟩ :=
    Step.ctx r.reverse rest (.numeric (.intBinOpTrap he))
  have e1 : vals (Val.num ⟨.int t, b⟩ :: Val.num ⟨.int t, a⟩ :: r).reverse ++
      [.plain (.intBinOp t op)] ++ rest = vals r.reverse ++
      [.plain (.intConst t a), .plain (.intConst t b), .plain (.intBinOp t op)] ++ rest := by
    simp [vals, Val.toAdmin]
  have h2 : Steps P host ⟨s, f, vals r.reverse ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩ := by
    simpa using steps_trap (P := P) (host := host) s f r.reverse rest
  rw [e1]
  exact Relation.ReflTransGen.head hstep h2

/-- The lowering of an operator tree, as code. -/
theorem expr_op (i : Instr) (args es : List Binaryen.BExpr) (rest : List Admin) :
    expression (Binaryen.BExpr.lowerList (.op i args :: es)) ++ rest =
      expression (Binaryen.BExpr.lowerList args) ++
        (.plain i :: (expression (Binaryen.BExpr.lowerList es) ++ rest)) := by
  simp [expression]

/-- The arguments of an operator, run normally. -/
theorem steps_args {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {args : List Binaryen.BExpr}
    (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (hst : BExpr.straightList f.locals.length args = true) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args) ++ rest⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ rest⟩ :=
  exec_sound rest (exec_of_eval hargs rfl hst).1

/-- The trapping-operator case of `steps_trap_of_eval`. -/
theorem trap_opStop {s₁ s₂ : Store H} {f₁ f₂ : Frame} {stk₁ : List Val} {i : Instr}
    {args es : List Binaryen.BExpr} {fl : Binaryen.Flow}
    (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal)
    {s' : Store H} {f' : Frame} (hr : ((s₂, f₂, fl) : Store H × Frame × Binaryen.Flow) =
      (s', f', .trap))
    (hst : BExpr.straightList f.locals.length (.op i args :: es) = true) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ expression
      (Binaryen.BExpr.lowerList (.op i args :: es)) ++ rest⟩ ⟨s', f', [.trap]⟩ := by
  have h4 := straight_op hst
  have hb : ∃ t op, i = .intBinOp t op := (flat_flow h4.1 hflat).resolve_left hfl
  obtain ⟨t, op, rfl⟩ := hb
  cases hr
  have h1 := steps_args (P := P) (host := host) hargs h4.2.2.1
    (.plain (.intBinOp t op) :: (expression (Binaryen.BExpr.lowerList es) ++ rest))
  have h2 := steps_binop_trap (P := P) (host := host) hflat
    (expression (Binaryen.BExpr.lowerList es) ++ rest)
  rw [List.append_assoc, expr_op, ← List.append_assoc]
  exact h1.trans (by simpa using h2)

/-- The normal-operator case of `steps_trap_of_eval`. -/
theorem trap_opOk {s₁ s₂ : Store H} {f₁ f₂ : Frame} {stk₁ stk₂ : List Val} {i : Instr}
    {args es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ih : ∀ {s' : Store H} {f' : Frame}, r = (s', f', .trap) →
      BExpr.straightList f₂.locals.length es = true → ∀ rest : List Admin,
      Steps P host ⟨s₂, f₂, vals stk₂.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩
        ⟨s', f', [.trap]⟩)
    {s' : Store H} {f' : Frame} (hr : r = (s', f', .trap))
    (hst : BExpr.straightList f.locals.length (.op i args :: es) = true) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ expression
      (Binaryen.BExpr.lowerList (.op i args :: es)) ++ rest⟩ ⟨s', f', [.trap]⟩ := by
  have h4 := straight_op hst
  have e1 := exec_of_eval hargs rfl h4.2.2.1
  have e2 := exec1_of_evalFlat h4.1 (e1.2 ▸ h4.2.1) hflat
  have hse : BExpr.straightList f₂.locals.length es = true := by
    rw [e2.2, e1.2]
    exact h4.2.2.2
  have hex : exec s f stk (Binaryen.BExpr.lowerList args ++ [i]) = some (s₂, f₂, stk₂) := by
    rw [exec_append, e1.1]
    exact exec_cons_of_some e2.1
  have h1 : Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args ++ [i]) ++
      (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩
      ⟨s₂, f₂, vals stk₂.reverse ++ (expression (Binaryen.BExpr.lowerList es) ++ rest)⟩ :=
    exec_sound _ hex
  have e3 : vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es)) ++ rest =
      vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args ++ [i]) ++
        (expression (Binaryen.BExpr.lowerList es) ++ rest) := by
    simp [expression]
  rw [e3]
  exact h1.trans (by simpa using ih hr hse rest)

/-- **A trapping native evaluation of straight-line trees is a Core 3.0 run to a trap.** -/
theorem steps_trap_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : Binaryen.Eval s f stk es r) :
    ∀ {s' : Store H} {f' : Frame}, r = (s', f', .trap) →
      BExpr.straightList f.locals.length es = true → ∀ rest : List Admin,
      Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩
        ⟨s', f', [.trap]⟩ := by
  induction h with
  | nil => intro s' f' hr; cases hr
  | @argsAbort s s₁ f f₁ stk i args es fl hargs hfl ih =>
    intro s' f' hr hst rest
    have h4 := straight_op hst
    rw [List.append_assoc, expr_op, ← List.append_assoc]
    exact ih hr h4.2.2.1 _
  | @opOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hargs hflat _ _ ih2 => exact trap_opOk hargs hflat ih2
  | opStop _ hargs hflat hfl => exact trap_opStop hargs hflat hfl
  | _ =>
    intro s' f' _ hst
    simp [BExpr.straightList, BExpr.straight, Instr.straight] at hst

end Silmaril.Wasm.Interp
