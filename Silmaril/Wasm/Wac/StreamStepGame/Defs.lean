module

public import Silmaril.Wasm.Wac.StreamStep.Defs
public import Silmaril.Wasm.Component.Algebra.StreamGame.Defs
public import Silmaril.Wasm.Component.Async.Defs

/-!
# WAC: the chunk game, the stream game and the async machine

`Wac.StreamStep.stepSem` reads a stream package `tI(in: stream<u8>) -> stream<u8>` as the
**chunk game** of its code's transformer: a question writes a chunk, its answer is what the
callee emitted on it; the end of the input is answered by the flush. Two other readings of the
same transformer exist in Silmaril:

* the **pull game** of `Algebra.StreamGame` (`den T = kahn (ans T)`), where every answer from
  upstream is one item (`item v`) or the end of a stream, and `ans T` is the stream function on
  answers;
* the **async machine** of `Component.Async` (`step : Store → Op → Option (Store × Res)`), where
  items move between tasks by `stream.read`/`stream.write` rendezvous and the end of a stream is
  `stream.drop-writable`.

This module states how a whole stream of the chunk game is played in the other two
(`Silmaril.Wasm.Wac.StreamStepGame.Thms`):

* `itemsOf cs e`: the upstream history of the pull game for the chunks `cs` followed by the end
  answer `e` (each item one answer);
* `rdv st r w xs`: one rendezvous of the async machine: the reader `r` asks for `xs.length`
  items (`stream.read`, it blocks), then the writer `w` writes `xs` (`stream.write`, it completes);
* `chunksM`, `sessionM`: a whole stream of the chunk game on the machine. For each chunk `xs`,
  the caller's write of `xs` into the input stream `(ri, wi)` meets the callee's read; the
  callee's write of the answer `(T.feed s xs).2` into the output stream `(ro, wo)` meets the
  caller's read. At the end, the callee writes the flush, the caller drops the writable end of
  the input and the callee the writable end of the output.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamStepGame

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Algebra.StreamGame Silmaril.Wasm.Component.Algebra.Kahn
open Silmaril.Wasm.Component.Async

/-- The pull game's upstream history of a whole stream: the items of the chunks `cs`, one answer
each, then the end answer `e`. -/
def itemsOf (cs : List (List Val)) (e : Ans) : List Ans := cs.flatten.map item ++ [e]

/-- An answer that ends a stream in the pull game (`DROPPED`, a trap, anything but one item). -/
def IsEnd (e : Ans) : Prop := ofItem e = none

/-- **One rendezvous** on the async machine: `stream.read r xs.length` (the reader blocks), then
`stream.write w xs`. -/
def rdv (st : Store) (r w : Nat) (xs : List Val) : Option Store :=
  match step st (.streamRead r xs.length) with
  | some (st₁, _) =>
    match step st₁ (.streamWrite w xs) with
    | some (st₂, _) => some st₂
    | none => none
  | none => none

/-- The chunks `cs` of the chunk game of `T` from state `s`, on the machine: the chunk into the
input stream (reader `ri`, writer `wi`), then the answer into the output stream (reader `ro`,
writer `wo`); the final store and transformer state. -/
def chunksM {σ : Type} (T : Tr σ Val Val) (ri wi ro wo : Nat) :
    Store → σ → List (List Val) → Option (Store × σ)
  | st, s, [] => some (st, s)
  | st, s, xs :: cs =>
    match rdv st ri wi xs with
    | some st₁ =>
      match rdv st₁ ro wo (T.feed s xs).2 with
      | some st₂ => chunksM T ri wi ro wo st₂ (T.feed s xs).1 cs
      | none => none
    | none => none

/-- **A whole stream of the chunk game on the machine**: the chunks, the flush written into the
output stream, then `stream.drop-writable` of the input (by the caller) and of the output (by the
callee). -/
def sessionM {σ : Type} (T : Tr σ Val Val) (ri wi ro wo : Nat) (st : Store)
    (cs : List (List Val)) : Option Store :=
  match chunksM T ri wi ro wo st T.init cs with
  | some (st₁, s) =>
    match rdv st₁ ro wo (T.flush s) with
    | some st₂ =>
      match step st₂ (.streamDropW wi) with
      | some (st₃, _) =>
        match step st₃ (.streamDropW wo) with
        | some (st₄, _) => some st₄
        | none => none
      | none => none
    | none => none
  | none => none

/-- The stream `s` is open between the reader `r` and the writer `w`, with no copy pending and its
writable end not dropped. -/
structure Open (st : Store) (r w s : Nat) : Prop where
  hw : st.tbl w = some (.streamW s)
  hr : st.tbl r = some (.streamR s)
  idle : (st.chans s).pend = .idle
  live : (st.chans s).wDropped = false

end Silmaril.Wasm.Wac.StreamStepGame
