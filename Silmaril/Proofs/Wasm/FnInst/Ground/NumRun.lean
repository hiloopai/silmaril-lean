module

public import Silmaril.Wasm.FnInst.Ground.Num.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic

@[expose] public section

/-! # The stack fragment: runs, and adequacy for silmaril's small-step semantics

* `nstep_app`, `run_app`: an outcome is stable under a deeper stack;
* `split_op`, `all_consts`, `run_consts`: a code that is not all constants is constants, then
  a non-constant instruction, then the rest;
* **`nstep_transGen`**, **`run_steps`**: a run with an outcome is a run of
  `Execution.Core.Step` (any profile, any host), from `vals st.reverse ++ code ++ rest` to the
  outcome's code (`Out.code`: the final values, or the values below a `trap` or a `br` and
  the code still after it).
-/

namespace Silmaril.Wasm.FnInst.Ground.Num

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.SingleThreaded.Exec.Pure (asInt asInt_eq_some)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Outcomes under deeper stacks -/

/-- Put `S` below the stack of an outcome. -/
def Out1.app (S : List Val) : Out1 → Out1
  | .ok st => .ok (st ++ S)
  | .stop st k => .stop (st ++ S) k

/-- Put `S` below the stack of an outcome. -/
def Out.app (S : List Val) : Out → Out
  | .ok st => .ok (st ++ S)
  | .stop st k c => .stop (st ++ S) k c

/-- The code of an outcome, bottom first. -/
def Out1.code : Out1 → List Admin
  | .ok st => vals st.reverse
  | .stop st k => vals st.reverse ++ [k]

/-- The code of an outcome, bottom first. -/
def Out.code : Out → List Admin
  | .ok st => vals st.reverse
  | .stop st k c => vals st.reverse ++ k :: expression (lower c)

theorem nstep_app {i : NInstr} {X : List Val} {o : Out1} (h : nstep i X = some o)
    (S : List Val) : nstep i (X ++ S) = some (o.app S) := by
  cases i <;> rcases X with _ | ⟨v, _ | ⟨w, _ | ⟨u, X⟩⟩⟩ <;>
    simp only [nstep, Option.map_eq_some_iff, Option.bind_eq_some_iff, reduceCtorEq,
      Option.some.injEq, List.cons_append, List.nil_append] at h ⊢ <;>
    first
    | (obtain rfl := h; rfl)
    | (obtain ⟨x, hx, rfl⟩ := h; exact ⟨x, hx, rfl⟩)
    | (obtain ⟨x, hx, y, hy, rfl⟩ := h; exact ⟨x, hx, y, hy, rfl⟩)
    | (obtain ⟨x, hx, y, hy, rfl⟩ := h
       refine ⟨x, hx, y, hy, ?_⟩
       split <;> rfl)
    | (obtain ⟨x, hx, rfl⟩ := h
       refine ⟨x, hx, ?_⟩
       split <;> rfl)

theorem run_cons (i : NInstr) (c : List NInstr) (st : List Val) :
    run (i :: c) st = (nstep i st).bind fun
      | .ok st' => run c st'
      | .stop st' k => some (.stop st' k c) := rfl

theorem run_app : ∀ {c : List NInstr} {X : List Val} {o : Out}, run c X = some o →
    ∀ S, run c (X ++ S) = some (o.app S)
  | [], X, o, h, S => by
    have ho : o = .ok X := (Option.some.inj h).symm
    rw [ho]
    rfl
  | i :: c, X, o, h, S => by
    obtain ⟨o₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    rw [run_cons, nstep_app h₁ S, Option.bind_some]
    cases o₁ with
    | ok st' => exact run_app h₂ S
    | stop st' k =>
      have ho : o = .stop st' k c := (Option.some.inj h₂).symm
      rw [ho]
      rfl

/-! ## Constants -/

/-- The values of a list of constants, bottom first. -/
def cvals (pre : List NInstr) : List Val := pre.map NInstr.cval

theorem const_of_isConst {j : NInstr} (h : j.isConst = true) : ∃ t k, j = .const t k := by
  cases j <;> first | exact ⟨_, _, rfl⟩ | exact absurd h (by simp [NInstr.isConst])

theorem run_consts : ∀ {pre : List NInstr}, (∀ j ∈ pre, j.isConst = true) →
    ∀ (c : List NInstr) (st : List Val), run (pre ++ c) st = run c ((cvals pre).reverse ++ st)
  | [], _, c, st => rfl
  | j :: pre, hp, c, st => by
    obtain ⟨t, k, rfl⟩ := const_of_isConst (hp j (by simp))
    have ih := run_consts (pre := pre) (fun j hj => hp j (by simp [hj])) c
      (.num ⟨.int t, k⟩ :: st)
    rw [List.cons_append, run_cons]
    simpa [cvals, NInstr.cval, nstep] using ih

theorem expression_consts : ∀ {pre : List NInstr}, (∀ j ∈ pre, j.isConst = true) →
    expression (lower pre) = vals (cvals pre)
  | [], _ => rfl
  | j :: pre, hp => by
    obtain ⟨t, k, rfl⟩ := const_of_isConst (hp j (by simp))
    have ih := expression_consts (pre := pre) (fun j hj => hp j (by simp [hj]))
    simp only [lower, List.map_cons, expression, cvals, vals] at ih ⊢
    rw [ih]
    rfl

theorem split_op : ∀ {a : List NInstr}, StkOp a →
    ∃ pre i a₁, a = pre ++ i :: a₁ ∧ (∀ j ∈ pre, j.isConst = true) ∧ i.isConst = false
  | [], ⟨_, hj, _⟩ => absurd hj (by simp)
  | j :: a, ⟨i, hi, hc⟩ => by
    cases hj : j.isConst with
    | false => exact ⟨[], j, a, rfl, by simp, hj⟩
    | true =>
      have hi' : i ∈ a := by
        rcases List.mem_cons.mp hi with rfl | h
        · rw [hj] at hc; cases hc
        · exact h
      obtain ⟨pre, i', a₁, rfl, hpre, hi'c⟩ := split_op ⟨i, hi', hc⟩
      refine ⟨j :: pre, i', a₁, rfl, ?_, hi'c⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | h
      · exact hj
      · exact hpre x h

theorem all_consts {a : List NInstr} (h : ¬ StkOp a) : ∀ j ∈ a, j.isConst = true := by
  intro j hj
  cases hc : j.isConst with
  | true => rfl
  | false => exact absurd ⟨j, hj, hc⟩ h

/-! ## Runs of the interpreter are runs of the machine -/

/-- A head step under the values below it and before the code after it. -/
theorem head_lift {s : Store H} {f : Frame} {X W us : List Val} {o : Out1} {ws : List Admin}
    {i : NInstr} (hX : X.reverse = W ++ us) (ho : o.code = vals W ++ ws)
    (h : Step P host ⟨s, f, vals us ++ [.plain i.lower]⟩ ⟨s, f, ws⟩) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain i.lower :: rest⟩ ⟨s, f, o.code ++ rest⟩ := by
  have h₁ := Step.append_right (Step.vals_left h W) rest
  rw [hX, ho]
  simpa only [vals_append, List.append_assoc, List.singleton_append] using h₁

theorem step_un {t : IntType} {op : IntUnOp} {X : List Val} {o : Out1}
    (h : nstep (.un t op) X = some o) (s : Store H) (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain (NInstr.un t op).lower :: rest⟩
      ⟨s, f, o.code ++ rest⟩ := by
  rcases X with _ | ⟨v, X⟩
  · cases h
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := asInt_eq_some.mp hx
    exact head_lift (i := .un t op) (W := X.reverse) (us := [.num ⟨.int t, x⟩]) (by simp)
      (by simp [Out1.code, vals, Val.toAdmin]) (Step.numeric NumericStep.intUnOp) rest

theorem step_test {t : IntType} {op : IntTestOp} {X : List Val} {o : Out1}
    (h : nstep (.test t op) X = some o) (s : Store H) (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain (NInstr.test t op).lower :: rest⟩
      ⟨s, f, o.code ++ rest⟩ := by
  rcases X with _ | ⟨v, X⟩
  · cases h
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := asInt_eq_some.mp hx
    exact head_lift (i := .test t op) (W := X.reverse) (us := [.num ⟨.int t, x⟩]) (by simp)
      (by simp [Out1.code, vals, constI32]) (Step.numeric NumericStep.intTestOp) rest

theorem step_rel {t : IntType} {op : IntRelOp} {X : List Val} {o : Out1}
    (h : nstep (.rel t op) X = some o) (s : Store H) (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain (NInstr.rel t op).lower :: rest⟩
      ⟨s, f, o.code ++ rest⟩ := by
  rcases X with _ | ⟨y, _ | ⟨x, X⟩⟩
  · cases h
  · cases h
  · obtain ⟨a, ha, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h'
    obtain rfl := asInt_eq_some.mp ha
    obtain rfl := asInt_eq_some.mp hb
    exact head_lift (i := .rel t op) (W := X.reverse) (us := [.num ⟨.int t, a⟩, .num ⟨.int t, b⟩]) (by simp)
      (by simp [Out1.code, vals, constI32]) (Step.numeric NumericStep.intRelOp) rest

theorem step_bin {t : IntType} {op : IntBinOp} {X : List Val} {o : Out1}
    (h : nstep (.bin t op) X = some o) (s : Store H) (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain (NInstr.bin t op).lower :: rest⟩
      ⟨s, f, o.code ++ rest⟩ := by
  rcases X with _ | ⟨y, _ | ⟨x, X⟩⟩
  · cases h
  · cases h
  · obtain ⟨a, ha, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h'
    obtain rfl := asInt_eq_some.mp ha
    obtain rfl := asInt_eq_some.mp hb
    rcases hz : intBinOp t op a b with e | z
    · exact head_lift (i := .bin t op) (W := X.reverse) (us := [.num ⟨.int t, a⟩, .num ⟨.int t, b⟩]) (by simp)
        (by simp [Out1.code]) (Step.numeric (NumericStep.intBinOpTrap hz)) rest
    · exact head_lift (i := .bin t op) (W := X.reverse) (us := [.num ⟨.int t, a⟩, .num ⟨.int t, b⟩]) (by simp)
        (by simp [Out1.code, vals, Val.toAdmin]) (Step.numeric (NumericStep.intBinOp hz)) rest

theorem step_drop {X : List Val} {o : Out1} (h : nstep .drop X = some o) (s : Store H)
    (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain NInstr.drop.lower :: rest⟩
      ⟨s, f, o.code ++ rest⟩ := by
  rcases X with _ | ⟨v, X⟩
  · cases h
  · obtain rfl : Out1.ok X = o := Option.some.inj h
    exact head_lift (i := .drop) (W := X.reverse) (us := [v]) (by simp) (by simp [Out1.code])
      (Step.parametric (ParametricStep.drop v)) rest

theorem step_nop {X : List Val} {o : Out1} (h : nstep .nop X = some o) (s : Store H)
    (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain NInstr.nop.lower :: rest⟩
      ⟨s, f, o.code ++ rest⟩ := by
  obtain rfl : Out1.ok X = o := Option.some.inj h
  exact head_lift (i := .nop) (W := X.reverse) (us := []) (by simp) (by simp [Out1.code])
    (Step.parametric ParametricStep.nop) rest

theorem step_select {ts : Option (List ValType)} {X : List Val} {o : Out1}
    (h : nstep (.select ts) X = some o) (s : Store H) (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain (NInstr.select ts).lower :: rest⟩
      ⟨s, f, o.code ++ rest⟩ := by
  rcases X with _ | ⟨c, _ | ⟨b, _ | ⟨a, X⟩⟩⟩
  · cases h
  · cases h
  · cases h
  · obtain ⟨cc, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := asInt_eq_some.mp hc
    by_cases h0 : cc = 0
    · subst h0
      exact head_lift (i := .select ts) (W := X.reverse) (us := [a, b, Val.i32 0])
        (by simp only [List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append]; rfl)
        (by simp [Out1.code]) (Step.parametric (ParametricStep.selectFalse a b ts)) rest
    · exact head_lift (i := .select ts) (W := X.reverse) (us := [a, b, Val.i32 cc])
        (by simp only [List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append]; rfl)
        (by rw [ite_eq_right h0]; simp [Out1.code]) (Step.parametric (ParametricStep.selectTrue h0)) rest

theorem step_brIf {l : LabelIdx} {X : List Val} {o : Out1}
    (h : nstep (.brIf l) X = some o) (s : Store H) (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain (NInstr.brIf l).lower :: rest⟩
      ⟨s, f, o.code ++ rest⟩ := by
  rcases X with _ | ⟨c, X⟩
  · cases h
  · obtain ⟨cc, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := asInt_eq_some.mp hc
    by_cases h0 : cc = 0
    · subst h0
      exact head_lift (i := .brIf l) (W := X.reverse) (us := [Val.i32 0])
        (by simp only [List.reverse_cons]; rfl)
        (by simp [Out1.code]) Step.brIfFalse rest
    · exact head_lift (i := .brIf l) (W := X.reverse) (us := [Val.i32 cc])
        (by simp only [List.reverse_cons]; rfl)
        (by rw [ite_eq_right h0]; simp [Out1.code]) (Step.brIfTrue h0) rest

/-- **One non-constant instruction is one machine step.** -/
theorem nstep_step {i : NInstr} (hi : i.isConst = false) {X : List Val} {o : Out1}
    (h : nstep i X = some o) (s : Store H) (f : Frame) (rest : List Admin) :
    Step P host ⟨s, f, vals X.reverse ++ .plain i.lower :: rest⟩ ⟨s, f, o.code ++ rest⟩ := by
  cases i with
  | const => cases hi
  | un => exact step_un h s f rest
  | bin => exact step_bin h s f rest
  | test => exact step_test h s f rest
  | rel => exact step_rel h s f rest
  | drop => exact step_drop h s f rest
  | nop => exact step_nop h s f rest
  | select => exact step_select h s f rest
  | brIf => exact step_brIf h s f rest

/-- One instruction is a machine run (no step for a constant). -/
theorem nstep_steps {i : NInstr} {X : List Val} {o : Out1} (h : nstep i X = some o)
    (s : Store H) (f : Frame) (rest : List Admin) :
    Steps P host ⟨s, f, vals X.reverse ++ .plain i.lower :: rest⟩ ⟨s, f, o.code ++ rest⟩ := by
  cases hc : i.isConst with
  | false => exact .single (nstep_step hc h s f rest)
  | true =>
    obtain ⟨t, k, rfl⟩ := const_of_isConst hc
    obtain rfl : Out1.ok (.num ⟨.int t, k⟩ :: X) = o := Option.some.inj h
    have e : vals X.reverse ++ Admin.plain (NInstr.const t k).lower :: rest =
        (Out1.ok (.num ⟨.int t, k⟩ :: X)).code ++ rest := by
      simp [Out1.code, vals, NInstr.lower, Val.toAdmin]
    rw [e]

/-- **Adequacy**: a run with an outcome is a run of the machine to the outcome's code. -/
theorem run_steps {c : List NInstr} {X : List Val} {o : Out} (h : run c X = some o)
    (s : Store H) (f : Frame) (rest : List Admin) :
    Steps P host ⟨s, f, vals X.reverse ++ expression (lower c) ++ rest⟩ ⟨s, f, o.code ++ rest⟩ := by
  induction c generalizing X o with
  | nil =>
    obtain rfl : Out.ok X = o := Option.some.inj h
    show Steps P host ⟨s, f, vals X.reverse ++ [] ++ rest⟩ _
    rw [List.append_nil]
    rfl
  | cons i c ih =>
    obtain ⟨o₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have hs := nstep_steps (P := P) (host := host) h₁ s f (expression (lower c) ++ rest)
    have e : vals X.reverse ++ expression (lower (i :: c)) ++ rest =
        vals X.reverse ++ .plain i.lower :: (expression (lower c) ++ rest) := by
      simp [lower, expression]
    rw [e]
    cases o₁ with
    | ok st' => exact hs.trans (by simpa [Out1.code] using ih h₂)
    | stop st' k =>
      obtain rfl : Out.stop st' k c = o := Option.some.inj h₂
      simpa [Out1.code, Out.code] using hs

end Silmaril.Wasm.FnInst.Ground.Num
