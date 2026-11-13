module

public import Silmaril.Wasm.FX.Asyncify.SM.Defs

/-!
# Asyncify by continuation-passing style (defunctionalized continuations)

A fourth way to run the one-shot handler kernel (`FXAsync.sstep`) without continuations of the
host machine. Each function is compiled in **continuation-passing style**: the rest of the
function after a call site is a separate continuation, named by a label `(fn, r)` (the function
and the resume position `r` of the code after the call), and a call does not return to its
caller on the host stack: it pushes a **continuation record** (the label, the saved operands and
what the caller waits for) and jumps to the callee (in Core 3.0, `return_call` with the
continuation in linear memory or a GC struct). A function that finishes pops the next record and
dispatches on its label (`br_table` on `r`). Continuations are thus first-order data
(defunctionalized), and the handler kernel's continuations are lists of these records:

* `CIns`: the kernel's instructions, with every call site, `resume` and `suspend` annotated
  with the label `(fn, r)` of its continuation;
* `annK fn pc c`: the **CPS compiler** on code at position `pc` of function `fn` (labels
  `(fn, pc + 1)`); `compK P` compiles every body (function `g` as label function `g + 1`, `0` is
  the root);
* `CCfg`: the continuation store, the running piece (code, operands, wait) and the
  continuation, a list of records `SM.PFrame`; `cstep C f₀ test`: **the CPS step**. A `suspend`
  splits the continuation at the handling resumer in one step and a `resume` pushes a captured
  record list back: no unwinding, no rewinding, no checks.

`toC` reads a state-machine configuration (`SM.PCfg`) as a CPS configuration: only the top record
becomes running code. The results (`Thms`) show `cstep (toC x) = (pstep x).map toC`, so CPS runs
in lock step with the state machine, hence with the kernel.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.CPS

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify.SM (PFrame PCfg psplit)

/-- CPS instructions: call sites, `resume` and `suspend` carry their continuation's label. -/
inductive CIns (V : Type) where
  | push (v : V)
  | prim (n : Nat) (op : List V → List V)
  | drop
  | call (g fn r : Nat)
  | cond (f g fn r : Nat)
  | contNew (g : Nat)
  | resume (n : Nat) (hs : List Clause) (fn r : Nat)
  | suspend (t n fn r : Nat)

/-- The running piece of code. -/
structure CFrame (V : Type) where
  code : List (CIns V)
  ops : List (SV V)
  wait : Option (List Clause)

/-- A CPS configuration: continuation store, running piece (none: stuck), continuation. -/
structure CCfg (V : Type) where
  conts : List (Option (List (PFrame V)))
  top : Option (CFrame V)
  kont : List (PFrame V)

variable {V : Type}

/-! ## The CPS compiler -/

/-- Annotate one instruction at position `pc` of function `fn`. -/
def annI (fn pc : Nat) : Ins V → CIns V
  | .push v => .push v
  | .prim n op => .prim n op
  | .drop => .drop
  | .call g => .call g fn (pc + 1)
  | .cond f g => .cond f g fn (pc + 1)
  | .contNew g => .contNew g
  | .resume n hs => .resume n hs fn (pc + 1)
  | .suspend t n => .suspend t n fn (pc + 1)

/-- **The CPS compiler** on code at position `pc` of function `fn`. -/
def annK (fn : Nat) : Nat → List (Ins V) → List (CIns V)
  | _, [] => []
  | pc, i :: c => annI fn pc i :: annK fn (pc + 1) c

/-- Compile a function table (function `g` gets label function `g + 1`). -/
def compK (P : Prog (Ins V)) : Prog (CIns V) :=
  fun g => (P g).map fun x => (x.1, annK (g + 1) 0 x.2)

/-! ## The machine -/

/-- The compiled body of label function `fn` (`0`: the root code of a call of `f₀`). -/
def kCode (C : Prog (CIns V)) (f₀ : Nat) : Nat → List (CIns V)
  | 0 => [.call f₀ 0 1]
  | g + 1 => ((C g).map Prod.snd).getD []

/-- **Dispatch** on a continuation record: run the piece at its label. -/
def enter (C : Prog (CIns V)) (f₀ : Nat) (b : PFrame V) : CFrame V :=
  ⟨(kCode C f₀ b.fn).drop b.pc, b.ops, b.wait⟩

/-- Call `g`: push the continuation record `(fn, r)` and jump to the callee. -/
def ccall (C : Prog (CIns V)) (K : List (Option (List (PFrame V)))) (g fn r : Nat) (ops : List (SV V)) (kont : List (PFrame V)) : Res (CCfg V) V :=
  match C g with
  | none => .stop .trap
  | some (np, body) =>
    match popN np ops with
    | none => .stop .trap
    | some (args, o) => .next ⟨K, some ⟨body, args, none⟩, ⟨fn, r, o, none⟩ :: kont⟩

/-- Execute instruction `i` of the running piece `fr` (code `i :: c`). -/
def cexec (C : Prog (CIns V)) (f₀ : Nat) (test : V → Bool) (K : List (Option (List (PFrame V))))
    (fr : CFrame V) (i : CIns V) (c : List (CIns V)) (kont : List (PFrame V)) :
    Res (CCfg V) V :=
  match i with
  | .push v => .next ⟨K, some { fr with code := c, ops := .val v :: fr.ops }, kont⟩
  | .prim n op =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (a, o) =>
      match allVals a with
      | none => .stop .trap
      | some vs => .next ⟨K, some { fr with code := c, ops := (op vs).map .val ++ o }, kont⟩
  | .drop =>
    match fr.ops with
    | [] => .stop .trap
    | _ :: o => .next ⟨K, some { fr with code := c, ops := o }, kont⟩
  | .call g fn r => ccall C K g fn r fr.ops kont
  | .cond f g fn r =>
    match fr.ops with
    | .val v :: o => ccall C K (if test v then f else g) fn r o kont
    | _ => .stop .trap
  | .contNew g =>
    match C g with
    | none => .stop .trap
    | some _ =>
      .next ⟨K ++ [some [⟨g + 1, 0, [], none⟩]],
        some { fr with code := c, ops := .cont K.length :: fr.ops }, kont⟩
  | .resume n hs fn r =>
    match fr.ops with
    | .cont k :: o =>
      match popN n o with
      | none => .stop .trap
      | some (args, o') =>
        match K[k]? with
        | some (some (top :: seg)) =>
          .next ⟨K.set k none, some (enter C f₀ { top with ops := args ++ top.ops }),
            seg ++ ⟨fn, r, o', some hs⟩ :: kont⟩
        | _ => .stop .trap
    | _ => .stop .trap
  | .suspend t n fn r =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (p, o) =>
      match psplit t kont with
      | none => .stop .trap
      | some (m, h, rr, rs) =>
        match C h with
        | none => .stop .trap
        | some (_, body) =>
          .next ⟨K ++ [some (⟨fn, r, o, fr.wait⟩ :: m)], some ⟨body, .cont K.length :: p, none⟩,
            { rr with wait := none } :: rs⟩

/-- **The CPS step.** A finished piece pops the next continuation record and dispatches. -/
def cstep (C : Prog (CIns V)) (f₀ : Nat) (test : V → Bool) (x : CCfg V) : Res (CCfg V) V :=
  match x.top with
  | none => .stop .trap
  | some fr =>
    match fr.code with
    | [] =>
      match x.kont with
      | [] => .stop (.done fr.ops)
      | b :: rest => .next ⟨x.conts, some (enter C f₀ { b with ops := fr.ops ++ b.ops }), rest⟩
    | i :: c => cexec C f₀ test x.conts fr i c x.kont

/-- The CPS configuration of a call of `f₀` with arguments `args`. -/
def cInit (C : Prog (CIns V)) (f₀ : Nat) (args : List (SV V)) : CCfg V :=
  ⟨[], some (enter C f₀ ⟨0, 0, args, none⟩), []⟩

/-! ## From the state machine -/

/-- **A state-machine configuration in CPS**: the top record runs, the others are the
continuation. -/
def toC (C : Prog (CIns V)) (f₀ : Nat) (x : SM.PCfg V) : CCfg V :=
  match x.stack with
  | [] => ⟨x.conts, none, []⟩
  | fr :: rest => ⟨x.conts, some (enter C f₀ fr), rest⟩

end Silmaril.Wasm.FX.Asyncify.CPS
