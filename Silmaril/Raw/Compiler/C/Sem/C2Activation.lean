module

public import Silmaril.Compiler.C.Sem.C2Prefix.Defs
/-!
# Composing C2 activations with body proofs

The activation below is precisely the allocation and argument-binding part of
`C2.callFn`. The theorems expose that boundary without changing the interpreter.
In particular, stack allocation, conversions and uninitialized declarations are
executed, rather than replaced with a proposed initial register environment.
-/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C2

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open C0 (Stop)
open C1 (store)

/-- Allocate actual memory locals and bind parameters to a fresh activation.
Argument-count checking remains the responsibility of `callFn`. -/
def activation (P : Prog) (fd : C1.FunDef) (vs : List Val) (caller : C1.Env) :
    Except Stop C1.Env := do
  let mut mem := caller.mem
  let mut frame : Std.HashMap Nat Nat := {}
  for (x, ty) in fd.memLocals do
    let (size, align) ← P.sizeAlign ty
    let (a, m) ← mem.alloc size align
    mem := m
    frame := frame.insert x a
  let mut regs : Std.HashMap Nat Int := {}
  for ((x, pt), v) in fd.params.zip vs do
    match v, frame[x]? with
    | .agg v, some a => mem ← writeAgg mem a v
    | .agg _, none => throw (.unsupported "an aggregate parameter outside memory")
    | .scalar v, some a => mem ← store mem pt a (← C1.convTo pt v)
    | .scalar v, none => regs := regs.insert x (← C1.convTo pt v)
  return ⟨regs, frame, mem, caller.out⟩

/-- The exact scalar-return boundary of the original interpreter. The body
contract can be assembled from internal prefixes; it is not a public-call
execution premise. Caller registers, frame and stack pointer are restored. -/
theorem callFn_of_activation (P : Prog) (n : Nat) (g : Sym) (fd : C1.FunDef)
    (vs : List Val) (caller active returned : C1.Env) (r : Option Val) (v : Int)
    (lookup : P.funcs[g.number]? = some fd)
    (arity : fd.params.length = vs.length)
    (prepared : activation P fd vs caller = .ok active)
    (body : loop P n fd (some fd.body) .stop active = .ok (r, returned))
    (scalar : aggOf fd.ret = none)
    (notAggregate : ∀ a, r ≠ some (.agg a))
    (converted : C1.convTo fd.ret ((r.map Val.int).getD 0) = .ok v) :
    callFn P (n + 1) g vs caller =
      .ok (.scalar v, ⟨caller.regs, caller.frame,
        { returned.mem with sp := caller.mem.sp }, returned.out⟩) := by
  have factored : callFn P (n + 1) g vs caller = do
      let env ← activation P fd vs caller
      let (r, returned) ← loop P n fd (some fd.body) .stop env
      let r ← match aggOf fd.ret, r with
        | some _, some (.agg v) => pure (Val.agg v)
        | some ty, _ => do
          let (size, _) ← P.sizeAlign ty
          pure (Val.agg ⟨ByteArray.mk (Array.replicate size 0),
            ByteArray.mk (Array.replicate size 0)⟩)
        | none, some (.agg _) => throw (.unsupported "an aggregate result of a scalar function")
        | none, r => pure (Val.scalar (← C1.convTo fd.ret ((r.map Val.int).getD 0)))
      return (r, ⟨caller.regs, caller.frame,
        { returned.mem with sp := caller.mem.sp }, returned.out⟩) := by
    cases caller
    simp only [callFn, lookup, arity, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, activation]
    simp only [bind_assoc]
    rfl
  rw [factored, prepared]
  simp only [Bind.bind, Except.bind, body, scalar]
  cases r with
  | none => simp only [Option.map_none, Option.getD_none] at converted ⊢; rw [converted]; rfl
  | some r =>
    cases r with
    | agg a => exact False.elim (notAggregate a rfl)
    | scalar value =>
      simp only [Option.map_some, Option.getD_some] at converted ⊢
      rw [converted]
      rfl

/-- Effect of one uninitialized declaration. A memory-resident local is
cleared using its actual prepared type; a register local becomes absent. -/
def uninitialized (P : Prog) (fd : C1.FunDef) (env : C1.Env) (x : Sym) :
    Except Stop C1.Env := do
  match env.frame[x.number]? with
  | some a =>
    let ty := ((fd.memLocals.find? (·.1 == x.number)).map (·.2)).getD (.mk [] .void)
    let (size, _) ← P.sizeAlign ty
    env.withMem (fun m => .ok (m.clear a size))
  | none => pure ⟨env.regs.erase x.number, env.frame, env.mem, env.out⟩

theorem step_uninitialized (P : Prog) (n : Nat) (fd : C1.FunDef)
    (s : TypedStatement) (x : Sym) (k : C0.Kont) (env after : C1.Env)
    (shape : s.node = .declaration [(x, none)])
    (effect : uninitialized P fd env x = .ok after) :
    step P (n + 1) fd (some s) k env = .ok (.running none k, after) := by
  simp only [step, shape, List.forIn_cons, List.forIn_nil]
  unfold uninitialized at effect
  split at effect <;>
    simp_all only [Bind.bind, Except.bind, pure, Except.pure]
  split at effect
  · contradiction
  · simp_all [C1.Env.withMem]

/-- Several variables in one original declaration share one source step. -/
theorem step_uninitialized_group (P : Prog) (n : Nat) (fd : C1.FunDef)
    (s : TypedStatement) (xs : List Sym) (k : C0.Kont) (env after : C1.Env)
    (shape : s.node = .declaration (xs.map (fun x => (x, none))))
    (effect : xs.foldlM (uninitialized P fd) env = .ok after) :
    step P (n + 1) fd (some s) k env = .ok (.running none k, after) := by
  simp only [step, shape, List.forIn_map]
  have fold : (forIn xs env (fun x env => do
      match env.frame[x.number]? with
      | some a =>
        let ty := ((fd.memLocals.find? (·.1 == x.number)).map (·.2)).getD (.mk [] .void)
        let (size, _) ← P.sizeAlign ty
        let env ← env.withMem (fun m => .ok (m.clear a size))
        pure (ForInStep.yield env)
      | none => pure (ForInStep.yield
          ⟨env.regs.erase x.number, env.frame, env.mem, env.out⟩))) =
      xs.foldlM (uninitialized P fd) env := by
    clear shape effect
    induction xs generalizing env with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.forIn_cons, List.foldlM_cons, uninitialized]
      cases h : env.frame[x.number]? with
      | none =>
        simp only [Bind.bind, Except.bind, pure, Except.pure]
        exact ih _
      | some a =>
        cases ht : P.sizeAlign
            (((fd.memLocals.find? (·.1 == x.number)).map (·.2)).getD (.mk [] .void)) with
        | error e => simp only [Bind.bind, Except.bind]
        | ok sa =>
          simp only [C1.Env.withMem, Bind.bind, Except.bind, pure, Except.pure]
          exact ih _
  calc
    _ = (do
      let env ← xs.foldlM (uninitialized P fd) env
      pure (Next.running none k, env)) := by
      rw [← fold]
      congr 1
      apply congrArg (fun f => forIn xs env f)
      funext x env
      cases env.frame[x.number]? <;> rfl
    _ = _ := by rw [effect]; rfl

/-- Execute a source sequence of uninitialized declarations. The
effect is the checked allocation-aware operation above, not an arbitrary
statement-machine success premise. Each declaration takes two outer steps. -/
theorem uninitialized_prefix (P : Prog) (fd : C1.FunDef)
    {ss : List TypedStatement} {xs : List (List Sym)}
    (shapes : List.Forall₂ (fun s xs =>
      s.node = .declaration (xs.map (fun x => (x, none)))) ss xs)
    (env after : C1.Env)
    (effect : xs.foldlM (fun env xs => xs.foldlM (uninitialized P fd) env) env = .ok after)
    (tail : List TypedStatement) (k : C0.Kont) (fuel : Nat) :
    Prefix P fd (fuel + 2 * ss.length + 1) ⟨none, .seq (ss ++ tail) k, env⟩
      (fuel + 1) ⟨none, .seq tail k, after⟩ := by
  induction shapes generalizing env with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at effect
    subst after
    exact .refl _ _
  | @cons s x ss xs shape shapes ih =>
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at effect
    cases h : x.foldlM (uninitialized P fd) env with
    | error e => simp only [h] at effect; contradiction
    | ok middle =>
      simp only [h] at effect
      have rest := ih middle effect
      have path : Prefix P fd (fuel + 2 * ss.length + 1 + 2)
          ⟨none, .seq ((s :: ss) ++ tail) k, env⟩
          (fuel + 1) ⟨none, .seq tail k, after⟩ :=
        .cons (middle := ⟨some s, .seq (ss ++ tail) k, env⟩) (by rfl) (.cons
          (step_uninitialized_group P (fuel + 2 * ss.length) fd s x (.seq (ss ++ tail) k)
            env middle shape h) rest)
      simpa only [List.length_cons, Nat.mul_succ, Nat.add_assoc] using path

end Silmaril.Compile.C.Sem.C2
