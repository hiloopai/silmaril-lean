module

public import Mathlib.Data.Set.Defs

/-!
# WasmFX with continuation-valued locals, a continuation queue and a log: `StepFXL`

`StepFX'` (`Silmaril.Wasm.Models.FXV`) keeps continuation references on the operand stack only:
frame locals, globals, tables and the arguments of calls are Core values, and `print_i32` is an
unobserved host call. The schedulers of the WasmFX explainer keep continuations in a local
(`$nextk`), pass them to `$enqueue` and get them back from `$dequeue`, and are specified by what
they print. This module adds a **second, separate model** next to `StepFX'` in which they can be
written:

* **Values** `V`: `i32` constants (as integers; the examples do no arithmetic), `ref.null`, and
  continuation references `cont k`. **Locals hold any value**, continuations included.
* **The continuation store** `conts` (one-shot: `none` once resumed), as in `ConfigFX`.
* **The queue** `queue`: the explainer's imported `queue` module (`queue-empty`, `dequeue`,
  `enqueue`) as primitive operations on a FIFO of values; `dequeue` of an empty queue gives
  `ref.null`.
* **The log** `log`: the values printed by `print_i32` (the explainer's `$log`), oldest first.
  It is the observation (`Obs`).

Code (`I`) is structured as in Wasm: `block` with a result arity, `loop`, `if` (no results),
`br`, `return`, `call`, `local.get`/`local.set`, `ref.null`, `ref.is_null`, `drop`, and the
stack-switching instructions `cont.new` (of a function index, i.e. `ref.func f; cont.new`),
`resume` with `(on $tag $label)` clauses and `suspend`. Tags have fixed payload arities (`ar`),
so `suspend` pops exactly its payload: unlike `StepFX'` (whose untyped `suspend` may split the
payload anywhere, `FXAsyncBack.suspend_split`) the machine is **deterministic**.

**Configurations** (`Cfg`) are a stack of activation frames (`Fr`, top first). A frame has its
remaining code, its operand stack (top first), its locals, its label stack (`Lab`: the arity of a
branch, the code after a branch and after the end, and the operands below the label) and its
result arity. A frame that is not on top records what it waits for (`wait`): a call (`none`) or
a `resume` with clauses `hs` (`some hs`). A continuation is the list of frames above its
resumer, captured by `suspend` up to the innermost frame waiting on a `resume` with a clause for
the tag; the resumer then branches to the clause's label with the payload and the new
continuation. A returning frame passes its results to the frame below, whether that frame called
it or resumed it. Every failure (missing operands, unknown functions or labels, a null or used
continuation, an unhandled tag) traps.

`step` is the one-step function and **`StepFXL`** the relation it defines; `beh` gives the
observable behaviours (the log and results of a finished run, the log of a trap, or divergence).

Not modelled: Core Wasm beyond these instructions (no arithmetic, memories, globals, tables or
exceptions), validation, `cont.bind`, `resume_throw`, `switch`, `barrier`, and arguments of
`resume` (the explainer's thread continuations have type `(cont (func))`). The machine is not
derived from `StepFX'`; relating the two is open (docs/projects/wasm-wasi.md).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXL

/-! ## Syntax -/

/-- Values: `i32` constants, `ref.null`, continuation references. -/
inductive V where
  | i32 (n : Int)
  | null
  | cont (k : Nat)
  deriving DecidableEq, Repr

/-- Instructions. -/
inductive I where
  | const (n : Int)
  | refNull
  | refIsNull
  | drop
  | localGet (i : Nat)
  | localSet (i : Nat)
  | call (f : Nat)
  /-- `call $log`: `print_i32`. -/
  | log
  /-- The queue interface: `call $queue-empty`, `call $enqueue`, `call $dequeue`. -/
  | qEmpty
  | enq
  | deq
  /-- `ref.func f; cont.new`. -/
  | contNew (f : Nat)
  /-- `resume` with clauses `(on $tag $label)`, as pairs `(tag, label)`. -/
  | resume (hs : List (Nat × Nat))
  | suspend (t : Nat)
  /-- `block` with `n` results. -/
  | block (n : Nat) (body : List I)
  /-- `loop` without parameters. -/
  | loop (body : List I)
  /-- `if` without results. -/
  | if_ (thn els : List I)
  | br (l : Nat)
  | ret

/-- A function: parameters, extra locals (initially `ref.null`), results and body. -/
structure Fn where
  np : Nat
  nl : Nat
  nr : Nat
  body : List I

/-- A program: functions by index. -/
abbrev Prog := List Fn

/-! ## Configurations -/

/-- A label: the values a branch carries, the code after a branch, the code after the end, and
the operands below the label. -/
structure Lab where
  ar : Nat
  brk : List I
  fin : List I
  ops : List V

/-- An activation frame. -/
structure Fr where
  code : List I
  ops : List V
  locals : List V
  labs : List Lab
  nr : Nat
  /-- When not on top: waiting on a call (`none`) or on a `resume` with clauses (`some hs`). -/
  wait : Option (List (Nat × Nat))

/-- A configuration. -/
structure Cfg where
  conts : List (Option (List Fr))
  queue : List V
  log : List Int
  stack : List Fr

/-- How a run stops: finished with the log and the results of the bottom frame, or trapped with
the log so far. -/
inductive Outcome where
  | done (log : List Int) (vs : List V)
  | trap (log : List Int)
  deriving DecidableEq, Repr

/-- The result of one step. -/
inductive Res where
  | next (c : Cfg)
  | stop (o : Outcome)

/-- The outcome of a result, if it stopped. -/
def Res.out : Res → Option Outcome
  | .next _ => none
  | .stop o => some o

/-! ## One step -/

/-- The fresh frame of a call of `F` with arguments `args` (top first). -/
def enter (F : Fn) (args : List V) : Fr :=
  ⟨F.body, [], args.reverse ++ List.replicate F.nl .null, [], F.nr, none⟩

/-- Branch to label `l` of frame `fr`. -/
def branch (fr : Fr) (l : Nat) : Option Fr :=
  match fr.labs.drop l with
  | [] => none
  | lab :: labs =>
    if lab.ar ≤ fr.ops.length then
      some { fr with code := lab.brk, ops := fr.ops.take lab.ar ++ lab.ops, labs := labs }
    else none

/-- The innermost frame waiting on a `resume` with a clause for tag `t`: the frames above it,
the label of the clause, the resumer and the frames below it. -/
def split (t : Nat) : List Fr → Option (List Fr × Nat × Fr × List Fr)
  | [] => none
  | b :: rest =>
    match b.wait.bind (List.lookup t) with
    | some l => some ([], l, b, rest)
    | none => (split t rest).map fun x => (b :: x.1, x.2)

/-- Return the values `vs` to the frames `rest` below. -/
def retTo (c : Cfg) (vs : List V) : List Fr → Res
  | [] => .stop (.done c.log vs)
  | b :: rest => .next { c with stack := { b with ops := vs ++ b.ops, wait := none } :: rest }

/-- Continue with top frame `fr'` over `rest`. -/
abbrev upd (c : Cfg) (fr' : Fr) (rest : List Fr) : Res := .next { c with stack := fr' :: rest }

/-- Execute instruction `i` of the top frame `fr` (code `i :: k`). -/
def exec (P : Prog) (ar : Nat → Nat) (c : Cfg) (fr : Fr) (i : I) (k : List I)
    (rest : List Fr) : Res :=
  let fr₀ := { fr with code := k }
  let trap : Res := .stop (.trap c.log)
  match i, fr.ops with
  | .const n, ops => upd c { fr₀ with ops := .i32 n :: ops } rest
  | .refNull, ops => upd c { fr₀ with ops := .null :: ops } rest
  | .refIsNull, v :: ops =>
    upd c { fr₀ with ops := .i32 (if v = .null then 1 else 0) :: ops } rest
  | .drop, _ :: ops => upd c { fr₀ with ops := ops } rest
  | .localGet x, ops =>
    match fr.locals[x]? with
    | some v => upd c { fr₀ with ops := v :: ops } rest
    | none => trap
  | .localSet x, v :: ops =>
    if x < fr.locals.length then upd c { fr₀ with ops := ops, locals := fr.locals.set x v } rest
    else trap
  | .call f, ops =>
    match P[f]? with
    | some F =>
      if F.np ≤ ops.length then
        let st := enter F (ops.take F.np) :: { fr₀ with ops := ops.drop F.np, wait := none } :: rest
        .next { c with stack := st }
      else trap
    | none => trap
  | .log, .i32 n :: ops =>
    .next { c with log := c.log ++ [n], stack := { fr₀ with ops := ops } :: rest }
  | .qEmpty, ops =>
    upd c { fr₀ with ops := .i32 (if c.queue = [] then 1 else 0) :: ops } rest
  | .enq, v :: ops =>
    .next { c with queue := c.queue ++ [v], stack := { fr₀ with ops := ops } :: rest }
  | .deq, ops =>
    match c.queue with
    | [] => upd c { fr₀ with ops := .null :: ops } rest
    | v :: q => .next { c with queue := q, stack := { fr₀ with ops := v :: ops } :: rest }
  | .contNew f, ops =>
    match P[f]? with
    | some F =>
      let seg : List Fr := [enter F []]
      let K' := c.conts ++ [some seg]
      .next { c with conts := K', stack := { fr₀ with ops := .cont c.conts.length :: ops } :: rest }
    | none => trap
  | .resume hs, .cont j :: ops =>
    match c.conts[j]? with
    | some (some seg) =>
      let K' := c.conts.set j none
      .next { c with conts := K', stack := seg ++ { fr₀ with ops := ops, wait := some hs } :: rest }
    | _ => trap
  | .suspend t, ops =>
    if ar t ≤ ops.length then
      match split t rest with
      | some (above, l, b, below) =>
        let kont := { fr₀ with ops := ops.drop (ar t) } :: above
        let b' := { b with ops := .cont c.conts.length :: ops.take (ar t) ++ b.ops, wait := none }
        match branch b' l with
        | some b'' => .next { c with conts := c.conts ++ [some kont], stack := b'' :: below }
        | none => trap
      | none => trap
    else trap
  | .block n body, ops =>
    upd c { fr with code := body, ops := [], labs := ⟨n, k, k, ops⟩ :: fr.labs } rest
  | .loop body, ops =>
    upd c { fr with code := body, ops := [], labs := ⟨0, .loop body :: k, k, ops⟩ :: fr.labs } rest
  | .if_ thn els, .i32 n :: ops =>
    let body := if n = 0 then els else thn
    upd c { fr with code := body, ops := [], labs := ⟨0, k, k, ops⟩ :: fr.labs } rest
  | .br l, _ =>
    match branch fr l with
    | some fr' => upd c fr' rest
    | none => trap
  | .ret, ops => if fr.nr ≤ ops.length then retTo c (ops.take fr.nr) rest else trap
  | _, _ => trap

/-- **One step.** -/
def step (P : Prog) (ar : Nat → Nat) (c : Cfg) : Res :=
  match c.stack with
  | [] => .stop (.trap c.log)
  | fr :: rest =>
    match fr.code, fr.labs with
    | i :: k, _ => exec P ar c fr i k rest
    | [], lab :: labs =>
      upd c { fr with code := lab.fin, ops := fr.ops ++ lab.ops, labs := labs } rest
    | [], [] =>
      if fr.nr ≤ fr.ops.length then retTo c (fr.ops.take fr.nr) rest else .stop (.trap c.log)

/-- **The step relation** of the machine. -/
def StepFXL (P : Prog) (ar : Nat → Nat) (c c' : Cfg) : Prop := step P ar c = .next c'

/-- Run at most `n` steps. -/
def runN (P : Prog) (ar : Nat → Nat) : Nat → Cfg → Res
  | 0, c => .next c
  | n + 1, c =>
    match step P ar c with
    | .next c' => runN P ar n c'
    | .stop o => .stop o

/-! ## Observations -/

/-- Observable behaviours: the log and results of a finished run, the log of a trap, or
divergence. -/
inductive Obs where
  | done (log : List Int) (vs : List V)
  | trap (log : List Int)
  | diverges

/-- An outcome as an observation. -/
def Outcome.toObs : Outcome → Obs
  | .done l vs => .done l vs
  | .trap l => .trap l

/-- **The behaviours** of a configuration. -/
def beh (P : Prog) (ar : Nat → Nat) (c : Cfg) : Set Obs :=
  {b | ∃ n o, runN P ar n c = .stop o ∧ b = o.toObs} ∪
  {b | b = .diverges ∧ ∀ n, ∃ c', runN P ar n c = .next c'}

/-- The initial configuration: call function `f` with no arguments and empty stores. -/
def init (P : Prog) (f : Nat) : Cfg :=
  match P[f]? with
  | some F => ⟨[], [], [], [enter F []]⟩
  | none => ⟨[], [], [], []⟩

end Silmaril.Wasm.Models.FXL
