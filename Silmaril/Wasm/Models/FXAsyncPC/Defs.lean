module

public import Silmaril.Wasm.Models.FXAsync.Defs

/-!
# First-order asyncify: resume indices, a mode register and a heap of frame records

`Silmaril.Wasm.Models.FXAsync` lowers one-shot handlers to an asyncify machine `tstep`. That
machine keeps two liberties that Core 3.0 does not have:

* a **saved frame stores its code suffix** (the rest of its function body), not a function and a
  resume index; a rewound frame is re-entered by keeping that suffix;
* the **mode** is an inductive value `Mode` carrying the unwinding buffer and payload.

This module removes both. The machine `fstep` is the same asyncify machine with first-order
state, the state a Core 3.0 implementation keeps in a global and in GC structs (or linear
memory):

* **Saved frames are records** `Rec`: a function number `fn`, a **resume index** `r` and the
  saved operands. The heap is a list of record lists (one-shot: `none` once consumed), as in
  Binaryen's Asyncify buffers or a GC array of frame structs.
* **The mode is a number** in a register `mode` (`0` normal, `1` unwinding, `2` rewinding, any
  other value traps), next to the registers `tag`, `pay` and `buf` (the tag, the payload or the
  rewinding arguments, and the records saved or still to re-enter).
* **Resume points are numbered.** The program is annotated (`ann fn pc`): every check and every
  `startUnwind` carries its function number and the resume index it saves, `2 * pc` for the
  instruction at position `pc` (`2 * (pc + 1)` after a `startUnwind`). A handled `rchk` turns
  its frame into one that waits on the handler call; that frame saves the odd index
  `2 * pc + 1`. Index `0` is the function entry, used by `alloc`.
* **Rewinding dispatches on the resume index** (`disp`): an even index `2 * pc` re-enters the
  annotated body at position `pc`, an odd one at the handler-call check after the `rchk` at
  `pc`. In Core this is the `br_table` prologue of a rewound function. Function `0` is the root
  code `R` (the initial call); function `f + 1` is the compiled function `f`.

`fInit` is the call of `f`, as `tInit`. The results (`Thms`) show that `fstep` and `tstep` run
in lock step, so with `FXAsync.lower_correct` the handler kernel and `fstep` have the same
behaviours.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAsyncPC

open Silmaril.Wasm.Models.FXAsync

/-- Annotated target instructions: the asyncify instructions with function numbers and resume
indices. -/
inductive AIns (V : Type) where
  | push (v : V)
  | prim (n : Nat) (op : List V → List V)
  | drop
  | call (f : Nat)
  | cond (f g : Nat)
  | alloc (f : Nat)
  | startRewind (n : Nat)
  /-- Start unwinding; the suspending frame saves function `fn`, resume index `r`. -/
  | startUnwind (t n fn r : Nat)
  /-- The check after a call; when unwinding, the frame saves `fn`, `r`. -/
  | chk (fn r : Nat)
  /-- The check after a resume; when unwinding without handling, the frame saves `fn`, `r`. -/
  | rchk (hs : List Clause) (fn r : Nat)

/-- A running frame: annotated code and operands. -/
structure AFrame (V : Type) where
  code : List (AIns V)
  ops : List (SV V)

/-- A saved frame record: a function number, a resume index and the operands. -/
structure Rec (V : Type) where
  fn : Nat
  r : Nat
  ops : List (SV V)

/-- A first-order asyncify configuration: a heap of records, registers and a stack. -/
structure FCfg (V : Type) where
  heap : List (Option (List (Rec V)))
  /-- The mode register: `0` normal, `1` unwinding, `2` rewinding. -/
  mode : Nat
  tag : Nat
  /-- The payload (unwinding) or the arguments (rewinding). -/
  pay : List (SV V)
  /-- The records saved so far, top first (unwinding), or still to re-enter, bottom first
  (rewinding). -/
  buf : List (Rec V)
  stack : List (AFrame V)

/-! ## Annotation -/

/-- Annotate one instruction at position `pc` of function `fn`. -/
def annI {V : Type} (fn pc : Nat) : TIns V → AIns V
  | .push v => .push v
  | .prim n op => .prim n op
  | .drop => .drop
  | .call f => .call f
  | .cond f g => .cond f g
  | .alloc f => .alloc f
  | .startRewind n => .startRewind n
  | .startUnwind t n => .startUnwind t n fn (2 * (pc + 1))
  | .chk => .chk fn (2 * pc)
  | .rchk hs => .rchk hs fn (2 * pc)

/-- Annotate code starting at position `pc` of function `fn`. -/
def ann {V : Type} (fn : Nat) : Nat → List (TIns V) → List (AIns V)
  | _, [] => []
  | pc, i :: c => annI fn pc i :: ann fn (pc + 1) c

/-- The code table: `0` is the root code, `f + 1` the target function `f`. -/
def bodies {V : Type} (Q : Prog (TIns V)) (R : List (TIns V)) : Nat → Option (List (TIns V))
  | 0 => some R
  | f + 1 => (Q f).map Prod.snd

/-- The annotated function table: function `f` is annotated as function number `f + 1`. -/
def annP {V : Type} (Q : Prog (TIns V)) : Prog (AIns V) :=
  fun f => (Q f).map fun x => (x.1, ann (f + 1) 0 x.2)

/-- **Dispatch on a resume index** (the `br_table` prologue): the annotated code at which a
record of function `fn` with index `r` re-enters. -/
def disp {V : Type} (B : Nat → Option (List (TIns V))) (fn r : Nat) : Option (List (AIns V)) :=
  match B fn with
  | none => none
  | some body =>
    if r % 2 = 0 then some (ann fn (r / 2) (body.drop (r / 2)))
    else
      match body.drop (r / 2) with
      | .rchk _ :: d => some (.chk fn r :: ann fn (r / 2 + 1) d)
      | _ => none

/-! ## The machine -/

/-- Call a function from the top frame (after its instruction is consumed). -/
def fcall {V : Type} (P : Prog (AIns V)) (h : List (Option (List (Rec V)))) (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) (f : Nat) (ops : List (SV V)) (c : List (AIns V))
    (rest : List (AFrame V)) : Res (FCfg V) V :=
  match P f with
  | none => .stop .trap
  | some (np, body) =>
    match popN np ops with
    | none => .stop .trap
    | some (args, o) => .next ⟨h, 0, t, p, b, ⟨body, args⟩ :: ⟨c, o⟩ :: rest⟩

/-- Execute instruction `i` of the top frame in normal mode (the registers `t`, `p`, `b` are
kept unless the instruction sets them). -/
def fexec {V : Type} (P : Prog (AIns V)) (test : V → Bool) (h : List (Option (List (Rec V))))
    (t : Nat) (p : List (SV V)) (b : List (Rec V)) (fr : AFrame V) (i : AIns V)
    (c : List (AIns V)) (rest : List (AFrame V)) : Res (FCfg V) V :=
  match i with
  | .push v => .next ⟨h, 0, t, p, b, ⟨c, .val v :: fr.ops⟩ :: rest⟩
  | .prim n op =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (a, o) =>
      match allVals a with
      | none => .stop .trap
      | some vs => .next ⟨h, 0, t, p, b, ⟨c, (op vs).map .val ++ o⟩ :: rest⟩
  | .drop =>
    match fr.ops with
    | [] => .stop .trap
    | _ :: o => .next ⟨h, 0, t, p, b, ⟨c, o⟩ :: rest⟩
  | .call f => fcall P h t p b f fr.ops c rest
  | .cond f g =>
    match fr.ops with
    | .val v :: o => fcall P h t p b (if test v then f else g) o c rest
    | _ => .stop .trap
  | .alloc f =>
    match P f with
    | none => .stop .trap
    | some _ =>
      .next ⟨h ++ [some [⟨f + 1, 0, []⟩]], 0, t, p, b, ⟨c, .cont h.length :: fr.ops⟩ :: rest⟩
  | .startRewind n =>
    match fr.ops with
    | .cont k :: o =>
      match popN n o with
      | none => .stop .trap
      | some (args, o') =>
        match h[k]? with
        | some (some (top :: seg)) =>
          .next ⟨h.set k none, 2, t, args, (top :: seg).reverse, ⟨c, o'⟩ :: rest⟩
        | _ => .stop .trap
    | _ => .stop .trap
  | .startUnwind t' n fn r =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (p', o) => .next ⟨h, 1, t', p', [⟨fn, r, o⟩], rest⟩
  | .chk _ _ => .next ⟨h, 0, t, p, b, ⟨c, fr.ops⟩ :: rest⟩
  | .rchk _ _ _ => .next ⟨h, 0, t, p, b, ⟨c, fr.ops⟩ :: rest⟩

/-- One unwinding step at frame `fr`: its call-site check. -/
def funwind {V : Type} (P : Prog (AIns V)) (h : List (Option (List (Rec V)))) (t : Nat)
    (p : List (SV V)) (b : List (Rec V)) (fr : AFrame V) (rest : List (AFrame V)) :
    Res (FCfg V) V :=
  match fr.code with
  | .chk fn r :: _ => .next ⟨h, 1, t, p, b ++ [⟨fn, r, fr.ops⟩], rest⟩
  | .rchk hs fn r :: c =>
    match lookup t hs with
    | none => .next ⟨h, 1, t, p, b ++ [⟨fn, r, fr.ops⟩], rest⟩
    | some hf =>
      match P hf with
      | none => .stop .trap
      | some (_, body) =>
        .next ⟨h ++ [some b], 0, t, p, b,
          ⟨body, .cont h.length :: p⟩ :: ⟨.chk fn (r + 1) :: c, fr.ops⟩ :: rest⟩
  | _ => .stop .trap

/-- **The first-order asyncify step.** The mode register selects normal execution, one
unwinding step, or one rewinding step (a dispatch on the resume index of the next record). -/
def fstep {V : Type} (P : Prog (AIns V)) (B : Nat → Option (List (TIns V))) (test : V → Bool)
    (x : FCfg V) : Res (FCfg V) V :=
  match x.mode with
  | 0 =>
    match x.stack with
    | [] => .stop .trap
    | fr :: rest =>
      match fr.code with
      | [] =>
        match rest with
        | [] => .stop (.done fr.ops)
        | b :: rest' => .next ⟨x.heap, 0, x.tag, x.pay, x.buf, ⟨b.code, fr.ops ++ b.ops⟩ :: rest'⟩
      | i :: c => fexec P test x.heap x.tag x.pay x.buf fr i c rest
  | 1 =>
    match x.stack with
    | [] => .stop .trap
    | fr :: rest => funwind P x.heap x.tag x.pay x.buf fr rest
  | 2 =>
    match x.buf with
    | [] => .stop .trap
    | [q] =>
      match disp B q.fn q.r with
      | none => .stop .trap
      | some code => .next ⟨x.heap, 0, x.tag, x.pay, [], ⟨code, x.pay ++ q.ops⟩ :: x.stack⟩
    | q :: q' :: qs =>
      match disp B q.fn q.r with
      | none => .stop .trap
      | some code => .next ⟨x.heap, 2, x.tag, x.pay, q' :: qs, ⟨code, q.ops⟩ :: x.stack⟩
  | _ + 3 => .stop .trap

/-- The root code of a call of `f`. -/
def rootCode {V : Type} (f : Nat) : List (TIns V) := [.call f, .chk]

/-- The first-order configuration that calls `f` with arguments `args`. -/
def fInit {V : Type} (f : Nat) (args : List (SV V)) : FCfg V :=
  ⟨[], 0, 0, [], [], [⟨ann 0 0 (rootCode f), args⟩]⟩

end Silmaril.Wasm.Models.FXAsyncPC
