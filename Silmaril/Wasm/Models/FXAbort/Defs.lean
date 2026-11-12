module

public import Silmaril.Wasm.Models.FXV.Defs

/-!
# Lowering abortive handlers to exceptions: the smallest fragment

An **abortive** handler never resumes the continuation it receives: its handler code drops it.
Such a handler can be compiled to an exception handler:

    block (result t* (ref $ct))                    block (result t*)
      resume $ct (on $x 0) …            ↦            try_table (catch $x 0) …
    end                                            end
    drop  ;; the continuation                      (nothing)
    ks                                             ks

with `suspend $x` (payload `W`) lowered to `throw $x`. The fragment here is the administrative
code at the moment the handler's body suspends at once:

* `abortSrc hs W x ks`: FX code: a label of arity `|W| + 1` (the payload and the continuation)
  whose continuation is `drop; ks`, around a handler frame `hs` whose body is `W; suspend x`;
* `abortTgt W x l ks`: Core code: a label of arity `|W|` with continuation `ks`, around an
  exception handler `catch x l` whose body is `W; throw x` (the shape that `try_table` leaves);
* `abortJoin W ks`: Core code `W; ks`, which both sides reach.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAbort

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX

/-- **Source**: an abortive `(on x l)` handler whose body suspends at once with payload `W`. -/
def abortSrc (hs : List HClause) (W : List Val) (x : TagIdx) (ks : List Instr) :
    List AdminFX :=
  [.label (W.length + 1) (.core .drop :: ks.map .core) [.handler hs (cvals W ++ [.fx (.suspend x)])]]

/-- **Target**: `catch x l` around `W; throw x`, in a label of arity `|W|`. -/
def abortTgt (W : List Val) (x : TagIdx) (l : LabelIdx) (ks : List Instr) : List Admin :=
  [.label W.length ks [.handler W.length [.catch_ x l] (vals W ++ [.plain (.throw x)])]]

/-- The code both sides reach: the payload, then the code after the block. -/
def abortJoin (W : List Val) (ks : List Instr) : List Admin := vals W ++ expression ks

end Silmaril.Wasm.Models.FXAbort
