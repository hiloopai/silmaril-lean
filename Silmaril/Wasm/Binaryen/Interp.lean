module

public import Silmaril.Wasm.Binaryen.Behaviour

@[expose] public section

/-! # Native semantics (later milestone): a fuel interpreter over layer D

The IR's *defining* semantics is its lowering (`Binaryen/Behaviour.lean`). This
interpreter is the second, native semantics: a big-step, fuel-indexed evaluator
of folded trees with Binaryen's flow outcomes (`Flow = normal | brk | ret | trap
| throw`; `throw` is unused until the EH milestone), in the style of Binaryen's
own `ExpressionRunner` (`src/wasm-interpreter.h`, version_133) but with de Bruijn
labels (layer N reaches it through `resolve`).

It is usable only together with `lower_adequate` (a separate interpreter-adequacy development (not included in this package)):
the lowering is **sound and complete** for it, for returns, traps, throws and
divergence. Then `nbeh`-level and Core-level reasoning are interchangeable.

Stacks are top-first here. Function bodies are taken from the store, which
holds Core code; they are evaluated through `liftInstrs` (exact for lowering,
`lowerList_liftInstrs`), and `run_lift_lower` says evaluation is invariant under
folding, so evaluating a module's own trees is the same.

Adequacy is restricted to the integer, memory-free native profile
(`NativeProfile.lean`), independently of the wider optimizer profile. Unsupported
instructions return `none` (stuck, or out of fuel); no numerics profile is needed
for the integer operations, which are deterministic.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core

variable {H : Type}

/-- Outcomes of evaluating a sequence (`Flow` in Binaryen's interpreter). -/
inductive Flow where
  | normal (vs : List Val)
  | brk (n : Nat) (vs : List Val)
  | ret (vs : List Val)
  | trap
  | throw (a : Nat)
  deriving Repr

/-- The integer of type `t` a value holds. -/
def asInt : (t : IntType) → Val → Option (BitVec t.width)
  | .i32, .num ⟨.int .i32, x⟩ => some x
  | .i64, .num ⟨.int .i64, x⟩ => some x
  | _, _ => none

/-- An integer value. -/
def ofInt (t : IntType) (x : BitVec t.width) : Val := .num ⟨.int t, x⟩

/-- An i32 condition. -/
def truthy (v : Val) : Option Bool := (asInt .i32 v).map (· != 0)

/-- One flat instruction on a top-first stack. -/
def evalFlat (s : Store H) (f : Frame) (stk : List Val) : Instr → Option (Store H × Frame × Flow)
  | .nop => some (s, f, .normal stk)
  | .unreachable => some (s, f, .trap)
  | .drop => match stk with
    | _ :: r => some (s, f, .normal r)
    | [] => none
  | .select _ => match stk with
    | c :: b :: a :: r => (truthy c).map fun t => (s, f, .normal ((if t then a else b) :: r))
    | _ => none
  | .intConst t b => some (s, f, .normal (ofInt t b :: stk))
  | .intUnOp t op => match stk with
    | x :: r => (asInt t x).map fun v => (s, f, .normal (ofInt t (Numerics.intUnOp t op v) :: r))
    | [] => none
  | .intTestOp t op => match stk with
    | x :: r => (asInt t x).map fun v =>
        (s, f, .normal (ofInt .i32 (Numerics.intTestOp t op v) :: r))
    | [] => none
  | .intBinOp t op => match stk with
    | y :: x :: r => do
      let a ← asInt t x
      let b ← asInt t y
      match Numerics.intBinOp t op a b with
      | .ok z => some (s, f, .normal (ofInt t z :: r))
      | .error _ => some (s, f, .trap)
    | _ => none
  | .intRelOp t op => match stk with
    | y :: x :: r => do
      let a ← asInt t x
      let b ← asInt t y
      some (s, f, .normal (ofInt .i32 (Numerics.intRelOp t op a b) :: r))
    | _ => none
  | .localGet x => (f.locals[x.toNat]?).join.map fun v => (s, f, .normal (v :: stk))
  | .localSet x => match stk with
    | v :: r => some (s, f.setLocal x v, .normal r)
    | [] => none
  | .localTee x => match stk with
    | v :: r => some (s, f.setLocal x v, .normal (v :: r))
    | [] => none
  | .globalGet g => (s.global? f g).map fun p => (s, f, .normal (p.2.value :: stk))
  | .globalSet g => match stk with
    | v :: r => (s.global? f g).map fun p => (s.setGlobal p.1 v, f, .normal r)
    | [] => none
  | .br l => some (s, f, .brk l.toNat stk)
  | .brIf l => match stk with
    | c :: r => (truthy c).map fun t => (s, f, if t then .brk l.toNat r else .normal r)
    | [] => none
  | .brTable ls d => match stk with
    | c :: r => (asInt .i32 c).map fun i => (s, f, .brk ((ls[i.toNat]?).getD d).toNat r)
    | [] => none
  | .return_ => some (s, f, .ret stk)
  | _ => none

/-- Parameter and result counts of a block type. -/
def arity (f : Frame) : BlockType → Option (Nat × Nat)
  | .empty => some (0, 0)
  | .value _ => some (0, 1)
  | .typeIdx x => (f.type? x >>= Validation.DefType.funcType?).map fun p => (p.1.length, p.2.length)

/-- **The fuel interpreter.** `run n s f stk es` evaluates `es` on the top-first
stack `stk`; `none` means out of fuel or stuck. -/
def run : Nat → Store H → Frame → List Val → List BExpr → Option (Store H × Frame × Flow)
  | 0, _, _, _, _ => none
  | _ + 1, s, f, stk, [] => some (s, f, .normal stk)
  | n + 1, s, f, stk, e :: es =>
    let cont : Store H × Frame × Flow → Option (Store H × Frame × Flow) := fun
      | (s', f', .normal stk') => run n s' f' stk' es
      | r => some r
    match e with
    | .op (.call x) args =>
      match run n s f stk args with
      | some (s₁, f₁, .normal stk₁) =>
        match s₁.func? f₁ x with
        | some (_, fi) =>
          match fi.code, Validation.DefType.funcType? fi.type with
          | .wasm fn, some (ps, rs) =>
            let callee := Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals
            match run n s₁ callee [] (liftInstrs fn.body) with
            | some (s₂, _, .normal vs) | some (s₂, _, .ret vs) | some (s₂, _, .brk 0 vs) =>
                cont (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length))
            | some (s₂, _, .trap) => some (s₂, f₁, .trap)
            | some (s₂, _, .throw a) => some (s₂, f₁, .throw a)
            | _ => none
          | _, _ => none
        | none => none
      | r => r
    | .op i args =>
      match run n s f stk args with
      | some (s₁, f₁, .normal stk₁) => (evalFlat s₁ f₁ stk₁ i).bind cont
      | r => r
    | .block bt body =>
      match arity f bt with
      | some (np, nr) =>
        match run n s f (stk.take np) body with
        | some (s₁, f₁, .normal vs) | some (s₁, f₁, .brk 0 vs) =>
            cont (s₁, f₁, .normal (vs.take nr ++ stk.drop np))
        | some (s₁, f₁, .brk (k + 1) vs) => some (s₁, f₁, .brk k vs)
        | r => r
      | none => none
    | .loop bt body =>
      match arity f bt with
      | some (np, nr) =>
        match run n s f (stk.take np) body with
        | some (s₁, f₁, .normal vs) => cont (s₁, f₁, .normal (vs.take nr ++ stk.drop np))
        | some (s₁, f₁, .brk 0 vs) => run n s₁ f₁ (vs.take np ++ stk.drop np) (e :: es)
        | some (s₁, f₁, .brk (k + 1) vs) => some (s₁, f₁, .brk k vs)
        | r => r
      | none => none
    | .if_ bt c t el =>
      match run n s f stk c with
      | some (s₁, f₁, .normal (cv :: stk₁)) =>
        match truthy cv, arity f₁ bt with
        | some b, some (np, nr) =>
          match run n s₁ f₁ (stk₁.take np) (if b then t else el) with
          | some (s₂, f₂, .normal vs) | some (s₂, f₂, .brk 0 vs) =>
              cont (s₂, f₂, .normal (vs.take nr ++ stk₁.drop np))
          | some (s₂, f₂, .brk (k + 1) vs) => some (s₂, f₂, .brk k vs)
          | r => r
        | _, _ => none
      | some (_, _, .normal []) => none
      | r => r
    | .tryTable .. => none

/-- Invoke function address `a` on bottom-first arguments `vs`. -/
def invokeRun (fuel : Nat) (s : Store H) (a : Nat) (vs : List Val) : Option (Store H × Flow) :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code, Validation.DefType.funcType? fi.type with
    | .wasm fn, some (_, rs) =>
      match run fuel s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) with
      | some (s', _, .normal ws) | some (s', _, .ret ws) | some (s', _, .brk 0 ws) =>
          some (s', .normal (ws.take rs.length).reverse)
      | some (s', _, .trap) => some (s', .trap)
      | some (s', _, .throw x) => some (s', .throw x)
      | _ => none
    | _, _ => none
  | none => none

/-- The observable behaviour of a final flow. -/
def flowBeh : Flow → Option (Behaviour Val)
  | .normal vs => some (.returns vs)
  | .trap => some .traps
  | .throw a => some (.throws a)
  | _ => none

/-- **Native behaviours** of an invocation: terminating outcomes at some fuel, and
divergence when no fuel suffices (closed deterministic profile). -/
def nbeh (s : Store H) (a : Nat) (vs : List Val) : Set (Behaviour Val) :=
  {b | (∃ fuel s' fl, invokeRun fuel s a vs = some (s', fl) ∧ flowBeh fl = some b) ∨
    (b = .diverges ∧ ∀ fuel, invokeRun fuel s a vs = none)}

/-- Native behaviours of export `x` of a closed module. Instantiation (global
initialisers, start) is Core's; a native instantiation is a later refinement. -/
def nbehModule (P : Numerics.Profile) (m : BModule) (x : String) (vs : List Val) :
    Set (Behaviour Val) :=
  {b | ∃ (s : Store Empty) (mi : ModuleInst) (a : Nat), Ready P closedHost {} m.lower [] s mi ∧
    exportFunc? mi x = some a ∧ b ∈ nbeh s a vs}

/-! ## Fuel monotonicity -/

/-- Unfolding `run` at a flat non-call operator. -/
theorem run_op_eq {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {args es : List BExpr} (hi : ∀ x, i = .call x → False) :
    run (n + 1) s f stk (.op i args :: es) =
      match run n s f stk args with
      | some (s₁, f₁, .normal stk₁) => (evalFlat s₁ f₁ stk₁ i).bind fun
          | (s', f', .normal stk') => run n s' f' stk' es
          | r => some r
      | r => r := by
  cases i <;> first | exact absurd rfl (hi _) | rfl

/-- One more unit of fuel never changes a result that was already reached. -/
theorem run_succ_eq (n : Nat) (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) :
    run n s f stk es ≠ none → run (n + 1) s f stk es = run n s f stk es := by
  fun_induction run n s f stk es <;> intro h
  all_goals (try (simp at h; done))
  all_goals (try (rw [run]; done))
  all_goals (try simp (config := {zetaDelta := true}) only at h)
  all_goals (first | rw [run_op_eq ‹_›] | rw [run])
  all_goals (try (simp (config := {zetaDelta := true}) [*]; done))
  case case12 n s f stk es cont i args hi s₁ f₁ stk₁ hargs ih2 ih1 =>
    rw [ih1 (by simp [hargs]), hargs]
    simp only [cont] at h ⊢
    rcases ho : evalFlat s₁ f₁ stk₁ i with _ | ⟨s', f', fl⟩
    · rfl
    · rw [ho] at h
      cases fl <;> simp_all

/-- More fuel never changes a terminating result. -/
theorem run_mono {n n' : Nat} (hle : n ≤ n') {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : run n s f stk es = some r) :
    run n' s f stk es = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => rw [run_succ_eq _ _ _ _ _ (by simp [ih]), ih]

/-! ## The fuel-free big-step relation

`Eval s f stk es r` is the inductive relation whose rules are the branches of
`run` that produce a result; `eval_of_run` and `run_of_eval` say it is exactly
"some fuel suffices". It is the form used to reason about the interpreter
(sequencing `eval_append_iff`, folding invariance `run_lift_lower`). -/

/-- Normal completion. -/
def Flow.IsNormal : Flow → Prop
  | .normal _ => True
  | _ => False

/-- Flows that leave a block, loop or `if` unchanged: returns, traps, throws. -/
def Flow.Escapes : Flow → Prop
  | .ret _ | .trap | .throw _ => True
  | _ => False

/-- The values a block body (or `if` arm) hands to the block's continuation:
normal completion or a branch to the block's own label. -/
def Flow.blockVals : Flow → Option (List Val)
  | .normal vs | .brk 0 vs => some vs
  | _ => none

/-- The values a callee body hands back to its caller. -/
def Flow.retVals : Flow → Option (List Val)
  | .normal vs | .ret vs | .brk 0 vs => some vs
  | _ => none

/-- **The big-step relation** of `run`, without fuel. -/
inductive Eval : Store H → Frame → List Val → List BExpr → Store H × Frame × Flow → Prop where
  | nil {s : Store H} {f : Frame} {stk : List Val} : Eval s f stk [] (s, f, .normal stk)
  | argsAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {fl : Flow} (hargs : Eval s f stk args (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      Eval s f stk (.op i args :: es) (s₁, f₁, fl)
  | callOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {fl : Flow} {r : Store H × Frame × Flow}
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : Eval s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) (s₂, f₂, fl))
      (hvs : fl.retVals = some vs)
      (hk : Eval s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
      Eval s f stk (.op (.call x) args :: es) r
  | callTrap {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType}
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : Eval s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) (s₂, f₂, .trap)) :
      Eval s f stk (.op (.call x) args :: es) (s₂, f₁, .trap)
  | callThrow {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {t : Nat}
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hbody : Eval s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
        (liftInstrs fn.body) (s₂, f₂, .throw t)) :
      Eval s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t)
  | opOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {r : Store H × Frame × Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
      (hk : Eval s₂ f₂ stk₂ es r) :
      Eval s f stk (.op i args :: es) r
  | opStop {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {i : Instr}
      {args es : List BExpr} {fl : Flow} (hi : ∀ x, i ≠ .call x)
      (hargs : Eval s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
      Eval s f stk (.op i args :: es) (s₂, f₂, fl)
  | blockOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) (hk : Eval s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      Eval s f stk (.block bt body :: es) r
  | blockBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : Eval s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      Eval s f stk (.block bt body :: es) (s₁, f₁, .brk k vs)
  | blockEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      Eval s f stk (.block bt body :: es) (s₁, f₁, fl)
  | loopOk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, .normal vs))
      (hk : Eval s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
      Eval s f stk (.loop bt body :: es) r
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {r : Store H × Frame × Flow}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, .brk 0 vs))
      (hk : Eval s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
      Eval s f stk (.loop bt body :: es) r
  | loopBrk {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr k : Nat}
      (har : arity f bt = some (np, nr))
      (hbody : Eval s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
      Eval s f stk (.loop bt body :: es) (s₁, f₁, .brk k vs)
  | loopEsc {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow}
      (har : arity f bt = some (np, nr)) (hbody : Eval s f (stk.take np) body (s₁, f₁, fl))
      (hfl : fl.Escapes) :
      Eval s f stk (.loop bt body :: es) (s₁, f₁, fl)
  | ifOk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {r : Store H × Frame × Flow}
      (hc : Eval s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : Eval s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) (hk : Eval s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
      Eval s f stk (.if_ bt c t el :: es) r
  | ifBrk {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr k : Nat}
      (hc : Eval s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : Eval s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, .brk (k + 1) vs)) :
      Eval s f stk (.if_ bt c t el :: es) (s₂, f₂, .brk k vs)
  | ifEsc {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      (hc : Eval s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : Eval s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl)) (hfl : fl.Escapes) :
      Eval s f stk (.if_ bt c t el :: es) (s₂, f₂, fl)
  | ifAbort {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {bt : BlockType}
      {c t el es : List BExpr} {fl : Flow}
      (hc : Eval s f stk c (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
      Eval s f stk (.if_ bt c t el :: es) (s₁, f₁, fl)

theorem Flow.notNormal_brk {k : Nat} {vs : List Val} : ¬ (Flow.brk k vs).IsNormal := fun h => h
theorem Flow.notNormal_ret {vs : List Val} : ¬ (Flow.ret vs).IsNormal := fun h => h
theorem Flow.notNormal_trap : ¬ Flow.trap.IsNormal := fun h => h
theorem Flow.notNormal_throw {a : Nat} : ¬ (Flow.throw a).IsNormal := fun h => h

open Lean Meta Elab Tactic in
/-- For every equation hypothesis `hx` and every hypothesis `ih : ∀ …, A → B` whose
last premise unifies with the type of `hx`, add `ih … hx`. -/
local elab "run_saturate" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d
    for ih in hyps do
      let ihTy ← instantiateMVars ih.type
      unless ihTy.isForall do continue
      for hx in hyps do
        let hxTy ← instantiateMVars hx.type
        unless hxTy.isAppOfArity ``Eq 3 do continue
        let res ← observing? do
          let (ms, _, body) ← forallMetaTelescopeReducing ihTy
          if ms.isEmpty then failure
          let last := ms.back!
          let lastTy ← inferType last
          unless (← withReducible (isDefEq lastTy hxTy)) do failure
          last.mvarId!.assign hx.toExpr
          let pf ← instantiateMVars (mkAppN ih.toExpr ms)
          if pf.hasExprMVar then failure
          let ty ← instantiateMVars body
          return (pf, ty)
        if let some (pf, ty) := res then
          let (_, g') ← g.note `hsat pf ty
          g := g'
    replaceMainGoal [g]

local macro "eval_leaf" : tactic =>
  `(tactic| first | assumption | rfl | exact True.intro | exact fun h => h)

local macro "eval_close" : tactic => `(tactic| first
  | exact Eval.nil
  | exact Eval.argsAbort (by eval_leaf) (by eval_leaf)
  | exact Eval.callOk (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
      (by eval_leaf) (by eval_leaf)
  | exact Eval.callTrap (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.callThrow (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.opOk (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.opStop (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.blockOk (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.blockBrk (by eval_leaf) (by eval_leaf)
  | exact Eval.blockEsc (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.loopOk (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.loopBack (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.loopBrk (by eval_leaf) (by eval_leaf)
  | exact Eval.loopEsc (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.ifOk (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
      (by eval_leaf)
  | exact Eval.ifBrk (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.ifEsc (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf) (by eval_leaf)
  | exact Eval.ifAbort (by eval_leaf) (by eval_leaf)
  | (exfalso; solve_by_elim (maxDepth := 3)))

/-- Fuel results are `Eval` results. -/
theorem eval_of_run {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : run n s f stk es = some r) : Eval s f stk es r := by
  fun_induction run n s f stk es generalizing r
  all_goals (try simp (config := {zetaDelta := true}) only at h)
  case case12 n s f stk es cont i args hi s₁ f₁ stk₁ hargs ih2 ih1 =>
    rcases ho : evalFlat s₁ f₁ stk₁ i with _ | ⟨s', f', fl⟩
    · simp [ho] at h
    · rw [ho] at h
      cases fl
      case normal stk' => exact Eval.opOk hi (ih1 hargs) ho (ih2 _ _ _ h)
      all_goals
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        exact Eval.opStop hi (ih1 hargs) ho (fun h => h)
  all_goals (try (cases h))
  all_goals (try (obtain ⟨s', f', fl⟩ := r; rcases fl with vs | ⟨_ | k, vs⟩ | vs | _ | t))
  all_goals run_saturate
  all_goals (try eval_close)
  all_goals (rcases vs with _ | ⟨_, _⟩ <;> (exfalso; solve_by_elim (maxDepth := 3)))

/-- `Eval` results are reached with enough fuel. -/
theorem run_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) : ∃ n, run n s f stk es = some r := by
  induction h with
  | nil => exact ⟨1, rfl⟩
  | @argsAbort s s₁ f f₁ stk i args es fl hargs hfl ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    by_cases hc : ∃ x, i = .call x
    · obtain ⟨x, rfl⟩ := hc
      rw [run]
      rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.IsNormal]
    · rw [run_op_eq (fun x hx => hc ⟨x, hx⟩)]
      rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.IsNormal]
  | @callOk s s₁ s₂ f f₁ f₂ stk stk₁ vs x args es a fi fn ps rs fl r hargs hfi hcode hty hbody hvs
      hk ih1 ih2 ih3 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2; obtain ⟨n3, h3⟩ := ih3
    refine ⟨n1 + n2 + n3 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 + n3 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 + n3 by omega) h2
    have h3' := run_mono (show n3 ≤ n1 + n2 + n3 by omega) h3
    rw [run]
    rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.retVals]
  | @callTrap s s₁ s₂ f f₁ f₂ stk stk₁ x args es a fi fn ps rs hargs hfi hcode hty hbody ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 by omega) h2
    rw [run]
    simp_all
  | @callThrow s s₁ s₂ f f₁ f₂ stk stk₁ x args es a fi fn ps rs t hargs hfi hcode hty hbody
      ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 by omega) h2
    rw [run]
    simp_all
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es r hi hargs hflat hk ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 by omega) h2
    rw [run_op_eq hi]
    simp_all
  | @opStop s s₁ s₂ f f₁ f₂ stk stk₁ i args es fl hi hargs hflat hfl ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, ?_⟩
    rw [run_op_eq hi]
    rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.IsNormal]
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har hbody hvs hk ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 by omega) h2
    rw [run]
    rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.blockVals]
  | @blockBrk s s₁ f f₁ stk vs bt body es np nr k har hbody ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, ?_⟩
    rw [run]
    simp_all
  | @blockEsc s s₁ f f₁ stk bt body es np nr fl har hbody hfl ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, ?_⟩
    rw [run]
    rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.Escapes]
  | @loopOk s s₁ f f₁ stk vs bt body es np nr r har hbody hk ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 by omega) h2
    rw [run]
    simp_all
  | @loopBack s s₁ f f₁ stk vs bt body es np nr r har hbody hk ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 by omega) h2
    rw [run]
    simp_all
  | @loopBrk s s₁ f f₁ stk vs bt body es np nr k har hbody ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, ?_⟩
    rw [run]
    simp_all
  | @loopEsc s s₁ f f₁ stk bt body es np nr fl har hbody hfl ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, ?_⟩
    rw [run]
    rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.Escapes]
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r hc hb har harm hvs hk
      ih1 ih2 ih3 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2; obtain ⟨n3, h3⟩ := ih3
    refine ⟨n1 + n2 + n3 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 + n3 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 + n3 by omega) h2
    have h3' := run_mono (show n3 ≤ n1 + n2 + n3 by omega) h3
    rw [run]
    rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.blockVals]
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k hc hb har harm ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 by omega) h2
    rw [run]
    simp_all
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl hc hb har harm hfl ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, ?_⟩
    have h1' := run_mono (show n1 ≤ n1 + n2 by omega) h1
    have h2' := run_mono (show n2 ≤ n1 + n2 by omega) h2
    rw [run]
    rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.Escapes]
  | @ifAbort s s₁ f f₁ stk bt c t el es fl hc hfl ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, ?_⟩
    rw [run]
    rcases fl with _ | ⟨_ | k, _⟩ | _ | _ | _ <;> simp_all [Flow.IsNormal]

/-! ## Sequencing -/

/-- What running `es` after an intermediate result `x` yields: `es` runs from a
normal result; any other flow skips it. -/
def Next (x : Store H × Frame × Flow) (es : List BExpr) (r : Store H × Frame × Flow) : Prop :=
  match x with
  | (s', f', .normal stk') => Eval s' f' stk' es r
  | _ => r = x

theorem next_of_not_normal {s : Store H} {f : Frame} {fl : Flow} (hfl : ¬ fl.IsNormal)
    {es : List BExpr} {r : Store H × Frame × Flow} : Next (s, f, fl) es r ↔ r = (s, f, fl) := by
  cases fl <;> simp_all [Next, Flow.IsNormal]

theorem Flow.not_normal_of_escapes {fl : Flow} (h : fl.Escapes) : ¬ fl.IsNormal := by
  cases fl <;> simp_all [Flow.Escapes, Flow.IsNormal]

theorem eval_nil_iff {s : Store H} {f : Frame} {stk : List Val} {r : Store H × Frame × Flow} :
    Eval s f stk [] r ↔ r = (s, f, .normal stk) := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

/-- Splitting off the head of a sequence. -/
theorem eval_cons_split {s : Store H} {f : Frame} {stk : List Val} {l : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk l r) :
    ∀ e es, l = e :: es → ∃ x, Eval s f stk [e] x ∧ Next x es r := by
  induction h with
  | nil => intro e es h; cases h
  | argsAbort hargs hfl _ =>
    intro e es h; cases h
    exact ⟨_, .argsAbort hargs hfl, (next_of_not_normal hfl).2 rfl⟩
  | callOk hargs hfi hcode hty hbody hvs hk =>
    intro e es h; cases h
    exact ⟨_, .callOk hargs hfi hcode hty hbody hvs .nil, hk⟩
  | callTrap hargs hfi hcode hty hbody =>
    intro e es h; cases h
    exact ⟨_, .callTrap hargs hfi hcode hty hbody, rfl⟩
  | callThrow hargs hfi hcode hty hbody =>
    intro e es h; cases h
    exact ⟨_, .callThrow hargs hfi hcode hty hbody, rfl⟩
  | opOk hi hargs hflat hk =>
    intro e es h; cases h
    exact ⟨_, .opOk hi hargs hflat .nil, hk⟩
  | opStop hi hargs hflat hfl =>
    intro e es h; cases h
    exact ⟨_, .opStop hi hargs hflat hfl, (next_of_not_normal hfl).2 rfl⟩
  | blockOk har hbody hvs hk =>
    intro e es h; cases h
    exact ⟨_, .blockOk har hbody hvs .nil, hk⟩
  | blockBrk har hbody =>
    intro e es h; cases h
    exact ⟨_, .blockBrk har hbody, rfl⟩
  | blockEsc har hbody hfl =>
    intro e es h; cases h
    exact ⟨_, .blockEsc har hbody hfl, (next_of_not_normal (Flow.not_normal_of_escapes hfl)).2 rfl⟩
  | loopOk har hbody hk =>
    intro e es h; cases h
    exact ⟨_, .loopOk har hbody .nil, hk⟩
  | loopBack har hbody hk _ ih =>
    intro e es h; cases h
    obtain ⟨x, hx, hn⟩ := ih _ _ rfl
    exact ⟨x, .loopBack har hbody hx, hn⟩
  | loopBrk har hbody =>
    intro e es h; cases h
    exact ⟨_, .loopBrk har hbody, rfl⟩
  | loopEsc har hbody hfl =>
    intro e es h; cases h
    exact ⟨_, .loopEsc har hbody hfl, (next_of_not_normal (Flow.not_normal_of_escapes hfl)).2 rfl⟩
  | ifOk hc hb har harm hvs hk =>
    intro e es h; cases h
    exact ⟨_, .ifOk hc hb har harm hvs .nil, hk⟩
  | ifBrk hc hb har harm =>
    intro e es h; cases h
    exact ⟨_, .ifBrk hc hb har harm, rfl⟩
  | ifEsc hc hb har harm hfl =>
    intro e es h; cases h
    exact ⟨_, .ifEsc hc hb har harm hfl,
      (next_of_not_normal (Flow.not_normal_of_escapes hfl)).2 rfl⟩
  | ifAbort hc hfl =>
    intro e es h; cases h
    exact ⟨_, .ifAbort hc hfl, (next_of_not_normal hfl).2 rfl⟩

/-- Joining a head with its continuation. -/
theorem eval_cons_join {s : Store H} {f : Frame} {stk : List Val} {l : List BExpr}
    {x : Store H × Frame × Flow} (h : Eval s f stk l x) :
    ∀ e es r, l = [e] → Next x es r → Eval s f stk (e :: es) r := by
  induction h with
  | nil => intro e es r h; cases h
  | argsAbort hargs hfl _ =>
    intro e es r h hn; cases h
    rw [(next_of_not_normal hfl).1 hn]; exact .argsAbort hargs hfl
  | callOk hargs hfi hcode hty hbody hvs hk =>
    intro e es r h hn; cases h
    cases hk
    exact .callOk hargs hfi hcode hty hbody hvs hn
  | callTrap hargs hfi hcode hty hbody =>
    intro e es r h hn; cases h
    rw [show r = _ from hn]; exact .callTrap hargs hfi hcode hty hbody
  | callThrow hargs hfi hcode hty hbody =>
    intro e es r h hn; cases h
    rw [show r = _ from hn]; exact .callThrow hargs hfi hcode hty hbody
  | opOk hi hargs hflat hk =>
    intro e es r h hn; cases h
    cases hk
    exact .opOk hi hargs hflat hn
  | opStop hi hargs hflat hfl =>
    intro e es r h hn; cases h
    rw [(next_of_not_normal hfl).1 hn]; exact .opStop hi hargs hflat hfl
  | blockOk har hbody hvs hk =>
    intro e es r h hn; cases h
    cases hk
    exact .blockOk har hbody hvs hn
  | blockBrk har hbody =>
    intro e es r h hn; cases h
    rw [show r = _ from hn]; exact .blockBrk har hbody
  | blockEsc har hbody hfl =>
    intro e es r h hn; cases h
    rw [(next_of_not_normal (Flow.not_normal_of_escapes hfl)).1 hn]; exact .blockEsc har hbody hfl
  | loopOk har hbody hk =>
    intro e es r h hn; cases h
    cases hk
    exact .loopOk har hbody hn
  | loopBack har hbody hk _ ih =>
    intro e es r h hn; cases h
    exact .loopBack har hbody (ih _ _ _ rfl hn)
  | loopBrk har hbody =>
    intro e es r h hn; cases h
    rw [show r = _ from hn]; exact .loopBrk har hbody
  | loopEsc har hbody hfl =>
    intro e es r h hn; cases h
    rw [(next_of_not_normal (Flow.not_normal_of_escapes hfl)).1 hn]; exact .loopEsc har hbody hfl
  | ifOk hc hb har harm hvs hk =>
    intro e es r h hn; cases h
    cases hk
    exact .ifOk hc hb har harm hvs hn
  | ifBrk hc hb har harm =>
    intro e es r h hn; cases h
    rw [show r = _ from hn]; exact .ifBrk hc hb har harm
  | ifEsc hc hb har harm hfl =>
    intro e es r h hn; cases h
    rw [(next_of_not_normal (Flow.not_normal_of_escapes hfl)).1 hn]; exact .ifEsc hc hb har harm hfl
  | ifAbort hc hfl =>
    intro e es r h hn; cases h
    rw [(next_of_not_normal hfl).1 hn]; exact .ifAbort hc hfl

theorem eval_cons_iff {s : Store H} {f : Frame} {stk : List Val} {e : BExpr} {es : List BExpr}
    {r : Store H × Frame × Flow} :
    Eval s f stk (e :: es) r ↔ ∃ x, Eval s f stk [e] x ∧ Next x es r :=
  ⟨fun h => eval_cons_split h e es rfl, fun ⟨_, hx, hn⟩ => eval_cons_join hx e es r rfl hn⟩

/-- **Sequencing**: running `a ++ b` is running `a`, then `b` from a normal result. -/
theorem eval_append_iff (a b : List BExpr) {s : Store H} {f : Frame} {stk : List Val}
    {r : Store H × Frame × Flow} :
    Eval s f stk (a ++ b) r ↔ ∃ x, Eval s f stk a x ∧ Next x b r := by
  induction a generalizing s f stk r with
  | nil =>
    simp only [List.nil_append, eval_nil_iff]
    constructor
    · intro h; exact ⟨_, rfl, h⟩
    · rintro ⟨x, rfl, h⟩; exact h
  | cons e a ih =>
    rw [List.cons_append, eval_cons_iff]
    constructor
    · rintro ⟨y, hy, hn⟩
      obtain ⟨s', f', fl⟩ := y
      cases fl
      case normal stk' =>
        obtain ⟨x, hx, hn'⟩ := (ih (s := s') (f := f') (stk := stk') (r := r)).1 hn
        exact ⟨x, eval_cons_iff.2 ⟨_, hy, hx⟩, hn'⟩
      all_goals
        refine ⟨_, eval_cons_iff.2 ⟨_, hy, rfl⟩, ?_⟩
        simp only [Next] at hn ⊢
        exact hn
    · rintro ⟨x, hx, hn⟩
      obtain ⟨y, hy, hn'⟩ := eval_cons_iff.1 hx
      refine ⟨y, hy, ?_⟩
      obtain ⟨s', f', fl⟩ := y
      cases fl
      case normal stk' => exact (ih (s := s') (f := f') (stk := stk') (r := r)).2 ⟨x, hn', hn⟩
      all_goals
        simp only [Next] at hn' ⊢
        subst hn'
        exact hn

/-! ## Folding invariance -/

theorem next_mono {a b : List BExpr}
    (hab : ∀ {s : Store H} {f : Frame} {stk : List Val} {r : Store H × Frame × Flow},
      Eval s f stk a r → Eval s f stk b r)
    {x r : Store H × Frame × Flow} (h : Next x a r) : Next x b r := by
  obtain ⟨s', f', fl⟩ := x
  cases fl
  case normal stk' => exact hab h
  all_goals exact h

theorem liftInstrs_append (a b : List Instr) :
    liftInstrs (a ++ b) = liftInstrs a ++ liftInstrs b := by
  induction a with
  | nil => simp [liftInstrs]
  | cons i a ih => simp [liftInstrs, ih]

theorem liftInstr_flat {i : Instr} (h : structuredInstr i = false) : liftInstr i = .op i [] := by
  unfold liftInstr; split <;> simp_all [structuredInstr]

theorem lift_lower_nil : liftInstrs (BExpr.lowerList []) = [] := by simp [liftInstrs]

theorem lift_lower_cons (e : BExpr) (es : List BExpr) :
    liftInstrs (BExpr.lowerList (e :: es)) =
      liftInstrs e.lower ++ liftInstrs (BExpr.lowerList es) := by
  simp [liftInstrs_append]

theorem lift_lower_op {i : Instr} (h : structuredInstr i = false) (args : List BExpr) :
    liftInstrs (BExpr.op i args).lower = liftInstrs (BExpr.lowerList args) ++ [.op i []] := by
  simp [liftInstrs_append, liftInstrs, liftInstr_flat h]

theorem lift_lower_block (bt : BlockType) (body : List BExpr) :
    liftInstrs (BExpr.block bt body).lower = [.block bt (liftInstrs (BExpr.lowerList body))] := by
  simp [BExpr.lower, liftInstrs, liftInstr]

theorem lift_lower_loop (bt : BlockType) (body : List BExpr) :
    liftInstrs (BExpr.loop bt body).lower = [.loop bt (liftInstrs (BExpr.lowerList body))] := by
  simp [BExpr.lower, liftInstrs, liftInstr]

theorem lift_lower_if (bt : BlockType) (c t el : List BExpr) :
    liftInstrs (BExpr.if_ bt c t el).lower = liftInstrs (BExpr.lowerList c) ++
      [.if_ bt [] (liftInstrs (BExpr.lowerList t)) (liftInstrs (BExpr.lowerList el))] := by
  simp [BExpr.lower, liftInstrs_append, liftInstrs, liftInstr]

theorem lift_lower_tryTable (bt : BlockType) (cs : List Catch) (body : List BExpr) :
    liftInstrs (BExpr.tryTable bt cs body).lower =
      [.tryTable bt cs (liftInstrs (BExpr.lowerList body))] := by
  simp [BExpr.lower, liftInstrs, liftInstr]

theorem structuredList_cons' {e : BExpr} {es : List BExpr} :
    BExpr.structuredList (e :: es) = true ↔
      e.structured = true ∧ BExpr.structuredList es = true := by
  simp [BExpr.structuredList]

theorem structured_op' {i : Instr} {args : List BExpr} :
    (BExpr.op i args).structured = true ↔
      structuredInstr i = false ∧ BExpr.structuredList args = true := by
  simp [BExpr.structured]

theorem structured_block' {bt : BlockType} {b : List BExpr} :
    (BExpr.block bt b).structured = true ↔ BExpr.structuredList b = true := by
  simp [BExpr.structured]

theorem structured_loop' {bt : BlockType} {b : List BExpr} :
    (BExpr.loop bt b).structured = true ↔ BExpr.structuredList b = true := by
  simp [BExpr.structured]

theorem structured_if' {bt : BlockType} {c t el : List BExpr} :
    (BExpr.if_ bt c t el).structured = true ↔ BExpr.structuredList c = true ∧
      BExpr.structuredList t = true ∧ BExpr.structuredList el = true := by
  simp [BExpr.structured, and_assoc]

theorem eval_lift_ite {b : Bool} {t el : List BExpr} {s : Store H} {f : Frame} {stk : List Val}
    {r : Store H × Frame × Flow}
    (h : Eval s f stk (liftInstrs (BExpr.lowerList (if b then t else el))) r) :
    Eval s f stk
      (if b then liftInstrs (BExpr.lowerList t) else liftInstrs (BExpr.lowerList el)) r := by
  cases b <;> exact h

theorem eval_ite_of_lift {b : Bool} {t el : List BExpr}
    (ht : ∀ {s : Store H} {f : Frame} {stk : List Val} {r : Store H × Frame × Flow},
      Eval s f stk (liftInstrs (BExpr.lowerList t)) r → Eval s f stk t r)
    (hel : ∀ {s : Store H} {f : Frame} {stk : List Val} {r : Store H × Frame × Flow},
      Eval s f stk (liftInstrs (BExpr.lowerList el)) r → Eval s f stk el r)
    {s : Store H} {f : Frame} {stk : List Val} {r : Store H × Frame × Flow}
    (h : Eval s f stk
      (if b then liftInstrs (BExpr.lowerList t) else liftInstrs (BExpr.lowerList el)) r) :
    Eval s f stk (if b then t else el) r := by
  cases b
  · exact hel h
  · exact ht h

/-- Running a tree is running its lifted lowering (one direction). -/
theorem eval_lift_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) :
    BExpr.structuredList es = true → Eval s f stk (liftInstrs (BExpr.lowerList es)) r := by
  induction h with
  | nil => intro _; rw [lift_lower_nil]; exact .nil
  | argsAbort hargs hfl ih =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hi, ha⟩ := structured_op'.1 he
    rw [lift_lower_cons, lift_lower_op hi, List.append_assoc, eval_append_iff]
    exact ⟨_, ih ha, (next_of_not_normal hfl).2 rfl⟩
  | callOk hargs hfi hcode hty hbody hvs hk ih1 _ ih3 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hi, ha⟩ := structured_op'.1 he
    rw [lift_lower_cons, lift_lower_op hi, List.append_assoc, eval_append_iff]
    exact ⟨_, ih1 ha, Eval.callOk .nil hfi hcode hty hbody hvs (ih3 hes)⟩
  | callTrap hargs hfi hcode hty hbody ih1 _ =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hi, ha⟩ := structured_op'.1 he
    rw [lift_lower_cons, lift_lower_op hi, List.append_assoc, eval_append_iff]
    exact ⟨_, ih1 ha, Eval.callTrap .nil hfi hcode hty hbody⟩
  | callThrow hargs hfi hcode hty hbody ih1 _ =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hi, ha⟩ := structured_op'.1 he
    rw [lift_lower_cons, lift_lower_op hi, List.append_assoc, eval_append_iff]
    exact ⟨_, ih1 ha, Eval.callThrow .nil hfi hcode hty hbody⟩
  | opOk hi' hargs hflat hk ih1 ih2 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hi, ha⟩ := structured_op'.1 he
    rw [lift_lower_cons, lift_lower_op hi, List.append_assoc, eval_append_iff]
    exact ⟨_, ih1 ha, Eval.opOk hi' .nil hflat (ih2 hes)⟩
  | opStop hi' hargs hflat hfl ih1 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hi, ha⟩ := structured_op'.1 he
    rw [lift_lower_cons, lift_lower_op hi, List.append_assoc, eval_append_iff]
    exact ⟨_, ih1 ha, Eval.opStop hi' .nil hflat hfl⟩
  | blockOk har hbody hvs hk ih1 ih2 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    rw [lift_lower_cons, lift_lower_block]
    exact Eval.blockOk har (ih1 (structured_block'.1 he)) hvs (ih2 hes)
  | blockBrk har hbody ih1 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    rw [lift_lower_cons, lift_lower_block]
    exact Eval.blockBrk har (ih1 (structured_block'.1 he))
  | blockEsc har hbody hfl ih1 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    rw [lift_lower_cons, lift_lower_block]
    exact Eval.blockEsc har (ih1 (structured_block'.1 he)) hfl
  | loopOk har hbody hk ih1 ih2 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    rw [lift_lower_cons, lift_lower_loop]
    exact Eval.loopOk har (ih1 (structured_loop'.1 he)) (ih2 hes)
  | loopBack har hbody hk ih1 ih2 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    have h2 := ih2 hs
    rw [lift_lower_cons, lift_lower_loop] at h2 ⊢
    exact Eval.loopBack har (ih1 (structured_loop'.1 he)) h2
  | loopBrk har hbody ih1 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    rw [lift_lower_cons, lift_lower_loop]
    exact Eval.loopBrk har (ih1 (structured_loop'.1 he))
  | loopEsc har hbody hfl ih1 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    rw [lift_lower_cons, lift_lower_loop]
    exact Eval.loopEsc har (ih1 (structured_loop'.1 he)) hfl
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r hc hb har harm hvs hk
      ih1 ih2 ih3 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hcs, hts, hels⟩ := structured_if'.1 he
    rw [lift_lower_cons, lift_lower_if, List.append_assoc, eval_append_iff]
    have harm' := eval_lift_ite (ih2 (by cases b <;> assumption))
    refine ⟨_, ih1 hcs, Eval.ifOk .nil hb har harm' hvs (ih3 hes)⟩
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k hc hb har harm ih1 ih2 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hcs, hts, hels⟩ := structured_if'.1 he
    rw [lift_lower_cons, lift_lower_if, List.append_assoc, eval_append_iff]
    have harm' := eval_lift_ite (ih2 (by cases b <;> assumption))
    refine ⟨_, ih1 hcs, Eval.ifBrk .nil hb har harm'⟩
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl hc hb har harm hfl ih1 ih2 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hcs, hts, hels⟩ := structured_if'.1 he
    rw [lift_lower_cons, lift_lower_if, List.append_assoc, eval_append_iff]
    have harm' := eval_lift_ite (ih2 (by cases b <;> assumption))
    refine ⟨_, ih1 hcs, Eval.ifEsc .nil hb har harm' hfl⟩
  | ifAbort hc hfl ih1 =>
    intro hs
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    obtain ⟨hcs, hts, hels⟩ := structured_if'.1 he
    rw [lift_lower_cons, lift_lower_if, List.append_assoc, eval_append_iff]
    exact ⟨_, ih1 hcs, (next_of_not_normal hfl).2 rfl⟩

mutual
/-- Running the lifted lowering of a structured list is running the list. -/
theorem eval_of_eval_lift : ∀ (es : List BExpr), BExpr.structuredList es = true →
    ∀ {s : Store H} {f : Frame} {stk : List Val} {r : Store H × Frame × Flow},
      Eval s f stk (liftInstrs (BExpr.lowerList es)) r → Eval s f stk es r
  | [], _, _, _, _, _, h => by rw [lift_lower_nil] at h; exact h
  | e :: es, hs, _, _, _, _, h => by
    obtain ⟨he, hes⟩ := structuredList_cons'.1 hs
    rw [lift_lower_cons, eval_append_iff] at h
    obtain ⟨x, hx, hn⟩ := h
    exact eval_cons_iff.2 ⟨x, eval_head_of_lift e he hx,
      next_mono (fun h => eval_of_eval_lift es hes h) hn⟩

/-- Running the lifted lowering of a structured tree is running the tree. -/
theorem eval_head_of_lift : ∀ (e : BExpr), e.structured = true →
    ∀ {s : Store H} {f : Frame} {stk : List Val} {x : Store H × Frame × Flow},
      Eval s f stk (liftInstrs e.lower) x → Eval s f stk [e] x
  | .op i args, he, s, f, stk, x, h => by
    obtain ⟨hi, ha⟩ := structured_op'.1 he
    rw [lift_lower_op hi, eval_append_iff] at h
    obtain ⟨⟨s₁, f₁, fl⟩, hy, hn⟩ := h
    have hy' := eval_of_eval_lift args ha hy
    cases fl
    case normal stk₁ =>
      simp only [Next] at hn
      cases hn with
      | argsAbort hargs hfl => cases hargs; exact absurd trivial hfl
      | callOk hargs hfi hcode hty hbody hvs hk =>
        cases hargs; exact .callOk hy' hfi hcode hty hbody hvs hk
      | callTrap hargs hfi hcode hty hbody => cases hargs; exact .callTrap hy' hfi hcode hty hbody
      | callThrow hargs hfi hcode hty hbody =>
        cases hargs; exact .callThrow hy' hfi hcode hty hbody
      | opOk hi' hargs hflat hk => cases hargs; exact .opOk hi' hy' hflat hk
      | opStop hi' hargs hflat hfl => cases hargs; exact .opStop hi' hy' hflat hfl
    all_goals
      simp only [Next] at hn
      subst hn
      exact .argsAbort hy' (by simp [Flow.IsNormal])
  | .block bt body, he, s, f, stk, x, h => by
    have hb := structured_block'.1 he
    rw [lift_lower_block] at h
    cases h with
    | blockOk har hbody hvs hk => exact .blockOk har (eval_of_eval_lift body hb hbody) hvs hk
    | blockBrk har hbody => exact .blockBrk har (eval_of_eval_lift body hb hbody)
    | blockEsc har hbody hfl => exact .blockEsc har (eval_of_eval_lift body hb hbody) hfl
  | .loop bt body, he, s, f, stk, x, h => by
    have hb := structured_loop'.1 he
    rw [lift_lower_loop] at h
    have key : ∀ {s : Store H} {f : Frame} {stk : List Val} {x : Store H × Frame × Flow}
        {l : List BExpr}, Eval s f stk l x →
        l = [BExpr.loop bt (liftInstrs (BExpr.lowerList body))] →
        Eval s f stk [BExpr.loop bt body] x := by
      intro s f stk x l h
      induction h
      case loopOk har hbody hk _ _ =>
        intro hl; cases hl; exact .loopOk har (eval_of_eval_lift body hb hbody) hk
      case loopBack har hbody hk _ ih =>
        intro hl; cases hl; exact .loopBack har (eval_of_eval_lift body hb hbody) (ih rfl)
      case loopBrk har hbody _ =>
        intro hl; cases hl; exact .loopBrk har (eval_of_eval_lift body hb hbody)
      case loopEsc har hbody hfl _ =>
        intro hl; cases hl; exact .loopEsc har (eval_of_eval_lift body hb hbody) hfl
      all_goals (intro hl; cases hl)
    exact key h rfl
  | .if_ bt c t el, he, s, f, stk, x, h => by
    obtain ⟨hcs, hts, hels⟩ := structured_if'.1 he
    rw [lift_lower_if, eval_append_iff] at h
    obtain ⟨⟨s₁, f₁, fl⟩, hy, hn⟩ := h
    have hy' := eval_of_eval_lift c hcs hy
    cases fl
    case normal stk₁ =>
      simp only [Next] at hn
      cases hn with
      | ifOk hc hb har harm hvs hk =>
        cases hc
        exact .ifOk hy' hb har (eval_ite_of_lift (fun h => eval_of_eval_lift t hts h)
          (fun h => eval_of_eval_lift el hels h) harm) hvs hk
      | ifBrk hc hb har harm =>
        cases hc
        exact .ifBrk hy' hb har (eval_ite_of_lift (fun h => eval_of_eval_lift t hts h)
          (fun h => eval_of_eval_lift el hels h) harm)
      | ifEsc hc hb har harm hfl =>
        cases hc
        exact .ifEsc hy' hb har (eval_ite_of_lift (fun h => eval_of_eval_lift t hts h)
          (fun h => eval_of_eval_lift el hels h) harm) hfl
      | ifAbort hc hfl => cases hc; exact absurd trivial hfl
    all_goals
      simp only [Next] at hn
      subst hn
      exact .ifAbort hy' (by simp [Flow.IsNormal])
  | .tryTable bt cs body, _, s, f, stk, x, h => by
    rw [lift_lower_tryTable] at h
    cases h
end

/-- Evaluation is invariant under folding. -/
theorem run_lift_lower (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr)
    (hs : BExpr.structuredList es = true) (r : Store H × Frame × Flow) :
    (∃ n, run n s f stk (liftInstrs (BExpr.lowerList es)) = some r) ↔
      ∃ n, run n s f stk es = some r := by
  constructor
  · rintro ⟨n, h⟩; exact run_of_eval (eval_of_eval_lift es hs (eval_of_run h))
  · rintro ⟨n, h⟩; exact run_of_eval (eval_lift_of_eval (eval_of_run h) hs)


end Silmaril.Wasm.Binaryen
