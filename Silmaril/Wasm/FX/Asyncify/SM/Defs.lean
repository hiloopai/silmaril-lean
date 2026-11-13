module

public import Silmaril.Wasm.Models.FXAsync.Defs

/-!
# Asyncify by a whole-program state machine

A third way to run the one-shot handler kernel (`FXAsync.sstep`) without continuations: compile
the whole program into **one dispatch loop** whose state is a number. Every function is cut at
every instruction; the program counter `(fn, pc)` (a function number and a position in its
body) is data, and each step dispatches on it (`loop; br_table` over the states, as in a
regenerator-style generator compiler or a Duff's-device interpreter). The call stack is data
too: a list of frame records `PFrame` (function, program counter, operands, what the frame waits
for), kept in linear memory or GC structs. There are no call-site checks, no unwinding and no
rewinding: a `suspend` moves the records above the handling resumer into the continuation store
in one step, a `resume` moves them back.

* `PFrame`, `PCfg`: frame records and configurations (a continuation store of record lists and a
  record stack, top first).
* `smCode P f₀ fn`: the body of state-machine function `fn`: `0` is the root code `[call f₀]`
  (the initial call), `g + 1` is the body of kernel function `g` (empty when undefined).
* `pstep P f₀ test`: **the state-machine step**. It fetches the case `(smCode P f₀ fn)[pc]?` of the
  top record: `none` returns (the operand stack goes to the record below), `some i` executes
  `i` and moves the program counter to `pc + 1`. A call pushes the callee's record at `pc = 0`.
* `psplit t`: the records above the innermost resumer with a clause for `t`.
* `pInit f args`: the root record calling `f`.

The instructions are the kernel's own (`Ins`), so the compiler of this strategy is the identity
on function tables: what changes is the machine, which keeps no code suffixes and no host call
stack, only numbers and records. `dec` reads a configuration back as a kernel configuration
(each record's code is the suffix `(smCode P f₀ fn).drop pc`); the results (`Thms`) show
`sstep (dec x) = (pstep x).map dec`, so the two run in lock step.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.SM

open Silmaril.Wasm.Models.FXAsync

/-- A frame record of the state machine. -/
structure PFrame (V : Type) where
  /-- The function: `0` is the root, `g + 1` the kernel function `g`. -/
  fn : Nat
  /-- The program counter: the position of the next instruction in the body. -/
  pc : Nat
  ops : List (SV V)
  wait : Option (List Clause)

/-- A state-machine configuration: a continuation store and a record stack (top first). -/
structure PCfg (V : Type) where
  conts : List (Option (List (PFrame V)))
  stack : List (PFrame V)

variable {V : Type}

/-- The body of state-machine function `fn` (`0` is the root code of a call of `f₀`). -/
def smCode (P : Prog (Ins V)) (f₀ : Nat) : Nat → List (Ins V)
  | 0 => [.call f₀]
  | g + 1 => ((P g).map Prod.snd).getD []

/-- The innermost record waiting on a `resume` with a clause for `t`: the records passed, the
handler function, the resumer and the records below it. -/
def psplit (t : Nat) : List (PFrame V) →
    Option (List (PFrame V) × Nat × PFrame V × List (PFrame V))
  | [] => none
  | b :: rest =>
    match b.wait.bind (lookup t) with
    | some h => some ([], h, b, rest)
    | none => (psplit t rest).map fun x => (b :: x.1, x.2)

/-- Call kernel function `g` from the record `fr` (whose program counter is already moved). -/
def pcall (P : Prog (Ins V)) (K : List (Option (List (PFrame V)))) (g : Nat) (fr : PFrame V)
    (ops : List (SV V)) (rest : List (PFrame V)) : Res (PCfg V) V :=
  match P g with
  | none => .stop .trap
  | some (np, _) =>
    match popN np ops with
    | none => .stop .trap
    | some (args, o) => .next ⟨K, ⟨g + 1, 0, args, none⟩ :: { fr with ops := o, wait := none } :: rest⟩

/-- Execute the case `i` of the top record `fr`. -/
def pexec (P : Prog (Ins V)) (test : V → Bool) (K : List (Option (List (PFrame V))))
    (fr : PFrame V) (i : Ins V) (rest : List (PFrame V)) : Res (PCfg V) V :=
  let fr' := { fr with pc := fr.pc + 1 }
  match i with
  | .push v => .next ⟨K, { fr' with ops := .val v :: fr.ops } :: rest⟩
  | .prim n op =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (a, o) =>
      match allVals a with
      | none => .stop .trap
      | some vs => .next ⟨K, { fr' with ops := (op vs).map .val ++ o } :: rest⟩
  | .drop =>
    match fr.ops with
    | [] => .stop .trap
    | _ :: o => .next ⟨K, { fr' with ops := o } :: rest⟩
  | .call g => pcall P K g fr' fr.ops rest
  | .cond f g =>
    match fr.ops with
    | .val v :: o => pcall P K (if test v then f else g) fr' o rest
    | _ => .stop .trap
  | .contNew g =>
    match P g with
    | none => .stop .trap
    | some _ =>
      .next ⟨K ++ [some [⟨g + 1, 0, [], none⟩]], { fr' with ops := .cont K.length :: fr.ops } :: rest⟩
  | .resume n hs =>
    match fr.ops with
    | .cont k :: o =>
      match popN n o with
      | none => .stop .trap
      | some (args, o') =>
        match K[k]? with
        | some (some (top :: seg)) =>
          .next ⟨K.set k none, { top with ops := args ++ top.ops } :: seg ++
            { fr' with ops := o', wait := some hs } :: rest⟩
        | _ => .stop .trap
    | _ => .stop .trap
  | .suspend t n =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (p, o) =>
      match psplit t rest with
      | none => .stop .trap
      | some (m, h, r, rs) =>
        match P h with
        | none => .stop .trap
        | some _ =>
          .next ⟨K ++ [some ({ fr' with ops := o } :: m)],
            ⟨h + 1, 0, .cont K.length :: p, none⟩ :: { r with wait := none } :: rs⟩

/-- **The state-machine step**: dispatch on the program counter of the top record. -/
def pstep (P : Prog (Ins V)) (f₀ : Nat) (test : V → Bool) (x : PCfg V) : Res (PCfg V) V :=
  match x.stack with
  | [] => .stop .trap
  | fr :: rest =>
    match (smCode P f₀ fr.fn)[fr.pc]? with
    | none =>
      match rest with
      | [] => .stop (.done fr.ops)
      | b :: rest' => .next ⟨x.conts, { b with ops := fr.ops ++ b.ops } :: rest'⟩
    | some i => pexec P test x.conts fr i rest

/-- The root record calling `f` with arguments `args`. -/
def pInit (args : List (SV V)) : PCfg V := ⟨[], [⟨0, 0, args, none⟩]⟩

/-! ## Reading a configuration back -/

/-- A record as a kernel frame: its code is the suffix of its body at its program counter. -/
def decF (P : Prog (Ins V)) (f₀ : Nat) (fr : PFrame V) : SFrame V :=
  ⟨(smCode P f₀ fr.fn).drop fr.pc, fr.ops, fr.wait⟩

/-- **A state-machine configuration as a kernel configuration.** -/
def dec (P : Prog (Ins V)) (f₀ : Nat) (x : PCfg V) : SCfg V :=
  ⟨x.conts.map (Option.map (List.map (decF P f₀))), x.stack.map (decF P f₀)⟩

end Silmaril.Wasm.FX.Asyncify.SM
