module

public import Silmaril.Wasm.Execution.Core.Step

/-!
# The non-local shapes of the tail-call rewrite: definitions

After `return_call x` the source and the target (`call x; return`) reach different exit
kernels, and the callee runs in different places:

* the **source** reduces `return_call x` to `REF.FUNC_ADDR a; RETURN_CALL_REF dt`, which bubbles
  out of every enclosing `LABEL` (`return_call_ref-label`) and then out of the caller's `FRAME`
  (`return_call_ref-frame-addr`), keeping only the arguments: the callee runs *outside* the
  caller's frame (`srcPending`);
* the **target** reduces `call x` to `REF.FUNC_ADDR a; CALL_REF dt` and calls *inside* the
  caller's frame and labels, followed by `RETURN` and dead code (`tgtWrap`): only when the
  callee has returned does `RETURN` bubble out (`return-label`, `return-frame`).

Between them, the enclosing contexts are labels only (`LabCtx`); a `HANDLER` there would catch
an exception of the callee in the target and not in the source (`TailCex`).

* `LabCtx`, `LabCtx.fill`: label-only evaluation contexts `LABEL_n{cont} (val* [_] instr*)`;
* `srcPending k fi pre L pre' vs a c restL rest`: the caller's frame at the source's pending tail
  call `val* (REF.FUNC_ADDR a) c` (with `c` a `RETURN_CALL_REF`);
* `tgtWrap k fi pre L pre' X restL rest`: the caller's frame with `X` (the callee, or what it has
  become) in front of `RETURN` under the same labels.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.TailRel

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- A label-only evaluation context. -/
inductive LabCtx where
  | hole
  | label (n : Nat) (cont : List Instr) (pre : List Val) (L : LabCtx) (rest : List Admin)

/-- Plug code into a label-only context. -/
def LabCtx.fill : LabCtx → List Admin → List Admin
  | .hole, X => X
  | .label n cont pre L rest, X => [.label n cont (vals pre ++ L.fill X ++ rest)]

/-- **The source's pending tail call**, inside the caller's frame. -/
def srcPending (k : Nat) (fi : Frame) (pre : List Val) (L : LabCtx) (pre' vs : List Val) (a : Nat)
    (c : Admin) (restL rest : List Admin) : Admin :=
  .frame k fi (vals pre ++ L.fill (vals pre' ++ vals (vs ++ [.ref (.func a)]) ++ c :: restL) ++ rest)

/-- **The target's wrapper**: `X` runs inside the caller's frame and labels, before `RETURN`. -/
def tgtWrap (k : Nat) (fi : Frame) (pre : List Val) (L : LabCtx) (pre' : List Val)
    (X restL rest : List Admin) : Admin :=
  .frame k fi (vals pre ++ L.fill (vals pre' ++ X ++ .plain .return_ :: restL) ++ rest)

end Silmaril.Wasm.LimeCompile.TailRel
