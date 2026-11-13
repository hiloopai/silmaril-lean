module

public import Mathlib.Data.Set.Defs

/-!
# An asyncify-style lowering of one-shot effect handlers (a WasmFX handler kernel)

The earlier WasmFX lowerings (`Silmaril.Wasm.Models.FXLower`, `FXBind`, `FXAbort`) compile single
instruction patterns in which the handler is never used, or is used once and abortively. This
module states a lowering of **general one-shot handlers**: arbitrary nesting, forwarding of
unhandled tags through inner handlers, continuations as first-class values that may be stored,
passed, resumed later under a different handler, or dropped, and a trap on a second resume.

Both sides are small abstract frame machines over an arbitrary type `V` of Core values (in the
Wasm models, `Silmaril.Wasm.Val`). They are **not** `StepFX'` and Core `Step`; the doc section
"Stretch, fxcps" in `docs/projects/wasm-components.md` says how the source machine reflects `StepFX'`.

**Source: the handler kernel** (`sstep`). A configuration (`SCfg`) is a continuation store
`conts` (one-shot: `none` once consumed, as in `ConfigFX`) and a stack of frames (`SFrame`, top
first). A frame has its remaining code, its operand stack (`SV`: Core values and continuation
references, as `FXV.FVal`), and `wait`: what the frame waits for, a call (`none`) or a `resume`
with handler clauses `hs` (`some hs`). So the handler frame that `StepFX` puts between a
resumer and the bottom of the resumed code is kept on the resumer. Instructions (`Ins`):

* `push`, `prim n op` (a pure operation on `n` Core values), `drop`;
* `call f`, `cond f g` (call `f` or `g` on a test of the top value) on a function table
  `Prog V := Nat → Option (Nat × List (Ins V))` (arity and body); a function returns its whole
  operand stack when its code is exhausted;
* `contNew f`: a fresh continuation of `f` (one frame, empty operands);
* `resume n hs`: consume the continuation on top, push its frames back with the `n` values below
  it as arguments, and wait on them with clauses `hs`;
* `suspend t n`: capture the frames up to the innermost waiting `resume` with a clause
  `(on t h)` (frames waiting on a call, or on a `resume` without a clause for `t`, are captured
  too) as a new continuation, and call the handler function `h` in the resumer with the payload
  and the new continuation on top.

A clause `(on t h)` names a handler *function*: its results become the results of the `resume`.
In WasmFX `(on $t $l)` branches to a label of the resumer; with no locals, the code after a
`block $l … resume … end` is such a function. Handlers are shallow (the handler runs outside
the resumed code) and one-shot. Every failure (missing operands, an unknown function, a consumed
or missing continuation, an unhandled tag) traps.

**Target: an asyncify machine** (`tstep`). No continuations and no handler frames. Frames hold
code and operands only (`TFrame`); a heap of saved stacks replaces the continuation store, and a
global mode (`Mode`) is normal, unwinding or rewinding, as in Binaryen's Asyncify:

* `alloc f` stores a one-frame record of `f` (the compiled `contNew`);
* `startUnwind t n` saves the current frame with the payload set aside and enters
  `unwind t payload buf`; then each frame below executes its call-site check, one per step:
  `chk` (after a call) saves the frame and returns; `rchk hs` (after a resume) either handles
  `t` (the saved frames become a heap record, the handler is called, the mode is normal again)
  or saves the frame and returns as `chk` does;
* `startRewind n` consumes a record and enters `rewind`, which re-enters the saved frames one per
  step, bottom first, and passes the arguments to the top one. Re-entering a frame at its saved
  resume point models the prologue dispatch of a rewound function (a `br_table` on the saved
  index, here a code suffix);
* `chk`, `rchk` are no-ops in normal mode.

**The lowering** `comp` is local: `call f ↦ call f; chk`, `cond f g ↦ cond f g; chk`,
`resume n hs ↦ startRewind n; rchk hs`, `contNew f ↦ alloc f`, `suspend t n ↦ startUnwind t n`,
the rest unchanged. `compP` compiles a function table; `trC` relates configurations.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAsync

/-! ## Values, outcomes and runs -/

/-- A value of either machine: a Core value or a continuation (record) reference. -/
inductive SV (V : Type) where
  | val (v : V)
  | cont (k : Nat)

/-- How a run stops. -/
inductive Outcome (V : Type) where
  | done (vs : List (SV V))
  | trap

/-- The result of one step. -/
inductive Res (C V : Type) where
  | next (c : C)
  | stop (o : Outcome V)

/-- Map the configuration of a result. -/
def Res.map {C D V : Type} (g : C → D) : Res C V → Res D V
  | .next c => .next (g c)
  | .stop o => .stop o

/-- Run at most `n` steps. -/
def runN {C V : Type} (step : C → Res C V) : Nat → C → Res C V
  | 0, c => .next c
  | n + 1, c =>
    match step c with
    | .next c' => runN step n c'
    | .stop o => .stop o

/-- Observable behaviours: an outcome, or divergence. -/
inductive Obs (V : Type) where
  | done (vs : List (SV V))
  | trap
  | diverges

/-- An outcome as a behaviour. -/
def Outcome.toObs {V : Type} : Outcome V → Obs V
  | .done vs => .done vs
  | .trap => .trap

/-- The behaviours of a deterministic machine from `c`. -/
def beh {C V : Type} (step : C → Res C V) (c : C) : Set (Obs V) :=
  {b | ∃ n o, runN step n c = .stop o ∧ b = o.toObs} ∪
  {b | b = .diverges ∧ ∀ n, ∃ c', runN step n c = .next c'}

/-! ## Common pieces -/

/-- A handler clause `(on tag fn)`. -/
structure Clause where
  tag : Nat
  fn : Nat

/-- The handler function of the first clause for tag `t`. -/
def lookup (t : Nat) (hs : List Clause) : Option Nat :=
  (hs.find? (fun c => c.tag == t)).map Clause.fn

/-- Pop `n` operands (top first). -/
def popN {α : Type} (n : Nat) (ops : List α) : Option (List α × List α) :=
  if n ≤ ops.length then some (ops.take n, ops.drop n) else none

/-- Core values among the operands. -/
def allVals {V : Type} : List (SV V) → Option (List V)
  | [] => some []
  | .val v :: r => (allVals r).map (v :: ·)
  | .cont _ :: _ => none

/-! ## Source: the handler kernel -/

/-- Source instructions. -/
inductive Ins (V : Type) where
  | push (v : V)
  | prim (n : Nat) (op : List V → List V)
  | drop
  | call (f : Nat)
  | cond (f g : Nat)
  | contNew (f : Nat)
  | resume (n : Nat) (hs : List Clause)
  | suspend (t n : Nat)

/-- A function table: arity and body. -/
abbrev Prog (I : Type) := Nat → Option (Nat × List I)

/-- A source frame. -/
structure SFrame (V : Type) where
  code : List (Ins V)
  ops : List (SV V)
  /-- What the frame waits for when it is not on top: a call, or a `resume` with clauses. -/
  wait : Option (List Clause)

/-- A source configuration. -/
structure SCfg (V : Type) where
  conts : List (Option (List (SFrame V)))
  stack : List (SFrame V)

/-- Find the innermost frame waiting on a `resume` with a clause for `t`: the frames passed, the
handler function, the resumer and the frames below it. -/
def split {V : Type} (t : Nat) : List (SFrame V) →
    Option (List (SFrame V) × Nat × SFrame V × List (SFrame V))
  | [] => none
  | b :: rest =>
    match b.wait.bind (lookup t) with
    | some h => some ([], h, b, rest)
    | none => (split t rest).map fun x => (b :: x.1, x.2)

/-- Push arguments on the top frame of a stack. -/
def pushTop {F : Type} (upd : F → F) : List F → List F
  | [] => []
  | x :: xs => upd x :: xs

/-- Call a function from the top frame (after its instruction is consumed). -/
def scall {V : Type} (P : Prog (Ins V)) (K : List (Option (List (SFrame V)))) (f : Nat)
    (fr : SFrame V) (ops : List (SV V)) (c : List (Ins V)) (rest : List (SFrame V)) :
    Res (SCfg V) V :=
  match P f with
  | none => .stop .trap
  | some (np, body) =>
    match popN np ops with
    | none => .stop .trap
    | some (args, o) =>
      .next ⟨K, ⟨body, args, none⟩ :: { fr with code := c, ops := o, wait := none } :: rest⟩

/-- Execute instruction `i` of the top frame `fr` (code `i :: c`). -/
def sexec {V : Type} (P : Prog (Ins V)) (test : V → Bool) (K : List (Option (List (SFrame V))))
    (fr : SFrame V) (i : Ins V) (c : List (Ins V)) (rest : List (SFrame V)) : Res (SCfg V) V :=
  match i with
  | .push v => .next ⟨K, { fr with code := c, ops := .val v :: fr.ops } :: rest⟩
  | .prim n op =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (a, o) =>
      match allVals a with
      | none => .stop .trap
      | some vs => .next ⟨K, { fr with code := c, ops := (op vs).map .val ++ o } :: rest⟩
  | .drop =>
    match fr.ops with
    | [] => .stop .trap
    | _ :: o => .next ⟨K, { fr with code := c, ops := o } :: rest⟩
  | .call f => scall P K f fr fr.ops c rest
  | .cond f g =>
    match fr.ops with
    | .val v :: o => scall P K (if test v then f else g) fr o c rest
    | _ => .stop .trap
  | .contNew f =>
    match P f with
    | none => .stop .trap
    | some (_, body) =>
      .next ⟨K ++ [some [⟨body, [], none⟩]],
        { fr with code := c, ops := .cont K.length :: fr.ops } :: rest⟩
  | .resume n hs =>
    match fr.ops with
    | .cont k :: o =>
      match popN n o with
      | none => .stop .trap
      | some (args, o') =>
        match K[k]? with
        | some (some (top :: seg)) =>
          .next ⟨K.set k none, { top with ops := args ++ top.ops } :: seg ++
            { fr with code := c, ops := o', wait := some hs } :: rest⟩
        | _ => .stop .trap
    | _ => .stop .trap
  | .suspend t n =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (p, o) =>
      match split t rest with
      | none => .stop .trap
      | some (m, h, r, rs) =>
        match P h with
        | none => .stop .trap
        | some (_, body) =>
          .next ⟨K ++ [some ({ fr with code := c, ops := o } :: m)],
            ⟨body, .cont K.length :: p, none⟩ :: { r with wait := none } :: rs⟩

/-- **The source step.** -/
def sstep {V : Type} (P : Prog (Ins V)) (test : V → Bool) (x : SCfg V) : Res (SCfg V) V :=
  match x.stack with
  | [] => .stop .trap
  | fr :: rest =>
    match fr.code with
    | [] =>
      match rest with
      | [] => .stop (.done fr.ops)
      | b :: rest' => .next ⟨x.conts, { b with ops := fr.ops ++ b.ops } :: rest'⟩
    | i :: c => sexec P test x.conts fr i c rest

/-! ## Target: an asyncify machine -/

/-- Target instructions: no continuations, no handlers. -/
inductive TIns (V : Type) where
  | push (v : V)
  | prim (n : Nat) (op : List V → List V)
  | drop
  | call (f : Nat)
  | cond (f g : Nat)
  /-- Store a fresh one-frame record of function `f`. -/
  | alloc (f : Nat)
  /-- Consume a record and rewind it with `n` arguments. -/
  | startRewind (n : Nat)
  /-- Start unwinding with tag `t` and a payload of `n` values. -/
  | startUnwind (t n : Nat)
  /-- The check after a call. -/
  | chk
  /-- The check after a resume, with its clauses. -/
  | rchk (hs : List Clause)

/-- A target frame. -/
structure TFrame (V : Type) where
  code : List (TIns V)
  ops : List (SV V)

/-- The asyncify mode. -/
inductive Mode (V : Type) where
  | normal
  /-- Unwinding with tag `t` and payload `p`; `buf` holds the frames saved so far (top first). -/
  | unwind (t : Nat) (p : List (SV V)) (buf : List (TFrame V))
  /-- Rewinding: the frames still to re-enter (bottom first) and the arguments. -/
  | rewind (pending : List (TFrame V)) (args : List (SV V))

/-- A target configuration. -/
structure TCfg (V : Type) where
  heap : List (Option (List (TFrame V)))
  mode : Mode V
  stack : List (TFrame V)

/-- Call a function from the top frame (after its instruction is consumed). -/
def tcall {V : Type} (P : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (f : Nat)
    (ops : List (SV V)) (c : List (TIns V)) (rest : List (TFrame V)) : Res (TCfg V) V :=
  match P f with
  | none => .stop .trap
  | some (np, body) =>
    match popN np ops with
    | none => .stop .trap
    | some (args, o) => .next ⟨h, .normal, ⟨body, args⟩ :: ⟨c, o⟩ :: rest⟩

/-- Execute instruction `i` of the top frame in normal mode. -/
def texec {V : Type} (P : Prog (TIns V)) (test : V → Bool) (h : List (Option (List (TFrame V))))
    (fr : TFrame V) (i : TIns V) (c : List (TIns V)) (rest : List (TFrame V)) : Res (TCfg V) V :=
  match i with
  | .push v => .next ⟨h, .normal, ⟨c, .val v :: fr.ops⟩ :: rest⟩
  | .prim n op =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (a, o) =>
      match allVals a with
      | none => .stop .trap
      | some vs => .next ⟨h, .normal, ⟨c, (op vs).map .val ++ o⟩ :: rest⟩
  | .drop =>
    match fr.ops with
    | [] => .stop .trap
    | _ :: o => .next ⟨h, .normal, ⟨c, o⟩ :: rest⟩
  | .call f => tcall P h f fr.ops c rest
  | .cond f g =>
    match fr.ops with
    | .val v :: o => tcall P h (if test v then f else g) o c rest
    | _ => .stop .trap
  | .alloc f =>
    match P f with
    | none => .stop .trap
    | some (_, body) => .next ⟨h ++ [some [⟨body, []⟩]], .normal, ⟨c, .cont h.length :: fr.ops⟩ :: rest⟩
  | .startRewind n =>
    match fr.ops with
    | .cont k :: o =>
      match popN n o with
      | none => .stop .trap
      | some (args, o') =>
        match h[k]? with
        | some (some (top :: seg)) =>
          .next ⟨h.set k none, .rewind (top :: seg).reverse args, ⟨c, o'⟩ :: rest⟩
        | _ => .stop .trap
    | _ => .stop .trap
  | .startUnwind t n =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (p, o) => .next ⟨h, .unwind t p [⟨c, o⟩], rest⟩
  | .chk => .next ⟨h, .normal, ⟨c, fr.ops⟩ :: rest⟩
  | .rchk _ => .next ⟨h, .normal, ⟨c, fr.ops⟩ :: rest⟩

/-- One unwinding step at frame `b`: its call-site check. -/
def tunwind {V : Type} (P : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) (buf : List (TFrame V)) (b : TFrame V) (rest : List (TFrame V)) :
    Res (TCfg V) V :=
  match b.code with
  | .chk :: _ => .next ⟨h, .unwind t p (buf ++ [b]), rest⟩
  | .rchk hs :: c =>
    match lookup t hs with
    | none => .next ⟨h, .unwind t p (buf ++ [b]), rest⟩
    | some hf =>
      match P hf with
      | none => .stop .trap
      | some (_, body) =>
        .next ⟨h ++ [some buf], .normal, ⟨body, .cont h.length :: p⟩ :: ⟨.chk :: c, b.ops⟩ :: rest⟩
  | _ => .stop .trap

/-- **The target step.** -/
def tstep {V : Type} (P : Prog (TIns V)) (test : V → Bool) (x : TCfg V) : Res (TCfg V) V :=
  match x.mode with
  | .normal =>
    match x.stack with
    | [] => .stop .trap
    | fr :: rest =>
      match fr.code with
      | [] =>
        match rest with
        | [] => .stop (.done fr.ops)
        | b :: rest' => .next ⟨x.heap, .normal, ⟨b.code, fr.ops ++ b.ops⟩ :: rest'⟩
      | i :: c => texec P test x.heap fr i c rest
  | .unwind t p buf =>
    match x.stack with
    | [] => .stop .trap
    | b :: rest => tunwind P x.heap t p buf b rest
  | .rewind pending args =>
    match pending with
    | [] => .stop .trap
    | [b] => .next ⟨x.heap, .normal, ⟨b.code, args ++ b.ops⟩ :: x.stack⟩
    | b :: b' :: bs => .next ⟨x.heap, .rewind (b' :: bs) args, b :: x.stack⟩

/-! ## The lowering -/

/-- **Compile source code** (asyncify: a check after every call site). -/
def comp {V : Type} : List (Ins V) → List (TIns V)
  | [] => []
  | .push v :: c => .push v :: comp c
  | .prim n op :: c => .prim n op :: comp c
  | .drop :: c => .drop :: comp c
  | .call f :: c => .call f :: .chk :: comp c
  | .cond f g :: c => .cond f g :: .chk :: comp c
  | .contNew f :: c => .alloc f :: comp c
  | .resume n hs :: c => .startRewind n :: .rchk hs :: comp c
  | .suspend t n :: c => .startUnwind t n :: comp c

/-- Compile a function table. -/
def compP {V : Type} (P : Prog (Ins V)) : Prog (TIns V) :=
  fun f => (P f).map fun x => (x.1, comp x.2)

/-- The check a waiting frame resumes at. -/
def mark {V : Type} : Option (List Clause) → List (TIns V)
  | none => [.chk]
  | some hs => [.rchk hs]

/-- A waiting (non-top) source frame in the target. -/
def trB {V : Type} (b : SFrame V) : TFrame V := ⟨mark b.wait ++ comp b.code, b.ops⟩

/-- A source stack in the target: the top frame runs its compiled code, every frame below sits at
its check. -/
def trS {V : Type} : List (SFrame V) → List (TFrame V)
  | [] => []
  | fr :: rest => ⟨comp fr.code, fr.ops⟩ :: rest.map trB

/-- **Source configurations in the target.** -/
def trC {V : Type} (x : SCfg V) : TCfg V :=
  ⟨x.conts.map (Option.map trS), .normal, trS x.stack⟩

/-- The source configuration that calls `f` with arguments `args`. -/
def sInit {V : Type} (f : Nat) (args : List (SV V)) : SCfg V := ⟨[], [⟨[.call f], args, none⟩]⟩

/-- The target configuration that calls `f` with arguments `args`. -/
def tInit {V : Type} (f : Nat) (args : List (SV V)) : TCfg V :=
  ⟨[], .normal, [⟨[.call f, .chk], args⟩]⟩

end Silmaril.Wasm.Models.FXAsync
