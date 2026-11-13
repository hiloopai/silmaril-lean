module

public import Silmaril.Wasm.Models.FXAsyncPC.Defs

/-!
# The shadow-stack strategy: saved frames in one linear memory

The first-order asyncify machine `FXAsyncPC.fstep` keeps its saved frames as lists of records
(`Rec`: a function number, a resume index, the operands) in a heap of record lists, and the
records being written or read in a register `buf`. Binaryen's Asyncify does neither: unwinding
**writes** each frame's state into a linear-memory buffer (the *asyncify data*, a stack that
grows as frames unwind), and rewinding **reads** it back, last written first. This module states
that strategy as a machine `mstep` and the encoding of records as memory cells.

* **Memory.** One growing list of cells (`Cell`: a number or a value, standing for an `i32` or a
  stored value slot). It is never shrunk: a consumed buffer is dead memory, as in a bump
  allocator.
* **A record** `q` is written as its operands, then a trailer of three numbers: function, resume
  index, operand count (`enc q`). The trailer comes last so that the record can be read
  backwards from its end (`popRev`), as a rewinding Asyncify pops its data stack.
* **A buffer** of records `q₁, …, qₘ` (top frame first, as unwinding saves them) is
  `enc q₁ ++ … ++ enc qₘ` (`encBuf`); rewinding reads `qₘ` (the bottom frame) first.
* **Continuations** are entries of a table `tbl` (one-shot: `none` once consumed), each the end
  address of its buffer and its record count: the `externref`/`i32` handle that a Core 3.0
  implementation would keep for a suspended stack.
* **Registers.** As in `fstep`: `mode` (`0` normal, `1` unwinding, `2` rewinding), `tag`, `pay`;
  instead of `buf`, a count `cnt` of records written (unwinding) or still to read (rewinding),
  and `top`, the end of the part still to read (rewinding).

The machine runs the same annotated programs as `fstep` (`AIns`, `disp` for re-entry). The
results (`Thms`) show that `mstep` and `fstep` run in lock step, so the handler kernel and the
shadow-stack machine have the same behaviours.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Shadow

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC

/-- A memory cell: a number, or a stored value. -/
inductive Cell (V : Type) where
  | num (n : Nat)
  | sv (x : SV V)

variable {V : Type}

/-- **The encoding of a record**: operands, then function, resume index and operand count. -/
def enc (q : Rec V) : List (Cell V) :=
  q.ops.map .sv ++ [.num q.fn, .num q.r, .num q.ops.length]

/-- The encoding of a buffer, first record at the lowest address. -/
def encBuf : List (Rec V) → List (Cell V)
  | [] => []
  | q :: qs => enc q ++ encBuf qs

/-- Read `n` value cells. -/
def takeSV : Nat → List (Cell V) → Option (List (SV V) × List (Cell V))
  | 0, l => some ([], l)
  | n + 1, .sv x :: l => (takeSV n l).map fun r => (x :: r.1, r.2)
  | _ + 1, _ => none

/-- **Read the last record** of a memory prefix, given reversed (last cell first); returns the
record and the rest (still reversed). -/
def popRev : List (Cell V) → Option (Rec V × List (Cell V))
  | .num n :: .num r :: .num fn :: l => (takeSV n l).map fun x => (⟨fn, r, x.1.reverse⟩, x.2)
  | _ => none

/-- A shadow-stack configuration. -/
structure MCfg (V : Type) where
  mem : List (Cell V)
  /-- The continuation table: end address and record count of a saved buffer. -/
  tbl : List (Option (Nat × Nat))
  mode : Nat
  tag : Nat
  pay : List (SV V)
  /-- Records written (unwinding) or still to read (rewinding). -/
  cnt : Nat
  /-- The end of the part still to read (rewinding). -/
  top : Nat
  stack : List (AFrame V)

/-! ## The machine -/

/-- Call a function from the top frame (after its instruction is consumed). -/
def mcall (P : Prog (AIns V)) (x : MCfg V) (f : Nat) (ops : List (SV V)) (c : List (AIns V))
    (rest : List (AFrame V)) : Res (MCfg V) V :=
  match P f with
  | none => .stop .trap
  | some (np, body) =>
    match popN np ops with
    | none => .stop .trap
    | some (args, o) => .next { x with mode := 0, stack := ⟨body, args⟩ :: ⟨c, o⟩ :: rest }

/-- Execute instruction `i` of the top frame `fr` in normal mode. -/
def mexec (P : Prog (AIns V)) (test : V → Bool) (x : MCfg V) (fr : AFrame V) (i : AIns V)
    (c : List (AIns V)) (rest : List (AFrame V)) : Res (MCfg V) V :=
  match i with
  | .push v => .next { x with mode := 0, stack := ⟨c, .val v :: fr.ops⟩ :: rest }
  | .prim n op =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (a, o) =>
      match allVals a with
      | none => .stop .trap
      | some vs => .next { x with mode := 0, stack := ⟨c, (op vs).map .val ++ o⟩ :: rest }
  | .drop =>
    match fr.ops with
    | [] => .stop .trap
    | _ :: o => .next { x with mode := 0, stack := ⟨c, o⟩ :: rest }
  | .call f => mcall P x f fr.ops c rest
  | .cond f g =>
    match fr.ops with
    | .val v :: o => mcall P x (if test v then f else g) o c rest
    | _ => .stop .trap
  | .alloc f =>
    match P f with
    | none => .stop .trap
    | some _ =>
      .next { x with mem := x.mem ++ enc ⟨f + 1, 0, []⟩,
                     tbl := x.tbl ++ [some ((x.mem ++ enc ⟨f + 1, 0, []⟩).length, 1)],
                     mode := 0, stack := ⟨c, .cont x.tbl.length :: fr.ops⟩ :: rest }
  | .startRewind n =>
    match fr.ops with
    | .cont k :: o =>
      match popN n o with
      | none => .stop .trap
      | some (args, o') =>
        match x.tbl[k]? with
        | some (some (e, m + 1)) =>
          .next { x with tbl := x.tbl.set k none, mode := 2, pay := args, cnt := m + 1, top := e,
                         stack := ⟨c, o'⟩ :: rest }
        | _ => .stop .trap
    | _ => .stop .trap
  | .startUnwind t n fn r =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (p, o) =>
      .next { x with mem := x.mem ++ enc ⟨fn, r, o⟩, mode := 1, tag := t, pay := p, cnt := 1,
                     stack := rest }
  | .chk _ _ => .next { x with mode := 0, stack := ⟨c, fr.ops⟩ :: rest }
  | .rchk _ _ _ => .next { x with mode := 0, stack := ⟨c, fr.ops⟩ :: rest }

/-- One unwinding step at frame `fr`: write its record, or hand the buffer to the handler. -/
def munwind (P : Prog (AIns V)) (x : MCfg V) (fr : AFrame V) (rest : List (AFrame V)) :
    Res (MCfg V) V :=
  match fr.code with
  | .chk fn r :: _ =>
    .next { x with mem := x.mem ++ enc ⟨fn, r, fr.ops⟩, cnt := x.cnt + 1, stack := rest }
  | .rchk hs fn r :: c =>
    match lookup x.tag hs with
    | none =>
      .next { x with mem := x.mem ++ enc ⟨fn, r, fr.ops⟩, cnt := x.cnt + 1, stack := rest }
    | some hf =>
      match P hf with
      | none => .stop .trap
      | some (_, body) =>
        .next { x with tbl := x.tbl ++ [some (x.mem.length, x.cnt)], mode := 0,
                       stack := ⟨body, .cont x.tbl.length :: x.pay⟩ ::
                         ⟨.chk fn (r + 1) :: c, fr.ops⟩ :: rest }
  | _ => .stop .trap

/-- One rewinding step: read the last unread record and re-enter it. -/
def mrewind (B : Nat → Option (List (TIns V))) (x : MCfg V) : Res (MCfg V) V :=
  match x.cnt with
  | 0 => .stop .trap
  | m + 1 =>
    match popRev (x.mem.take x.top).reverse with
    | none => .stop .trap
    | some (q, l) =>
      match disp B q.fn q.r with
      | none => .stop .trap
      | some code =>
        match m with
        | 0 => .next { x with mode := 0, cnt := 0, stack := ⟨code, x.pay ++ q.ops⟩ :: x.stack }
        | m' + 1 => .next { x with cnt := m' + 1, top := l.length,
                                   stack := ⟨code, q.ops⟩ :: x.stack }

/-- **The shadow-stack step.** -/
def mstep (P : Prog (AIns V)) (B : Nat → Option (List (TIns V))) (test : V → Bool)
    (x : MCfg V) : Res (MCfg V) V :=
  match x.mode with
  | 0 =>
    match x.stack with
    | [] => .stop .trap
    | fr :: rest =>
      match fr.code with
      | [] =>
        match rest with
        | [] => .stop (.done fr.ops)
        | b :: rest' => .next { x with stack := ⟨b.code, fr.ops ++ b.ops⟩ :: rest' }
      | i :: c => mexec P test x fr i c rest
  | 1 =>
    match x.stack with
    | [] => .stop .trap
    | fr :: rest => munwind P x fr rest
  | 2 => mrewind B x
  | _ + 3 => .stop .trap

/-- The shadow-stack configuration that calls `f` with arguments `args`. -/
def mInit (f : Nat) (args : List (SV V)) : MCfg V :=
  ⟨[], [], 0, 0, [], 0, 0, [⟨ann 0 0 (rootCode f), args⟩]⟩

end Silmaril.Wasm.FX.Asyncify.Shadow
