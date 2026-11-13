module

public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitLoops

/-!
# Completeness of executable Core 3.0 instantiation: definitions

silmaril-lean proves the executable instantiation functions **sound**: `prepare?_sound`,
`instantiateInit?_sound` and `prepareDirect?_steps` say that what they compute is reachable
from a configuration of the specification's `Instantiate`. This topic adds the converse.
Every `Instantiate` derivation is found by `prepare?`, and every run of the
segment-initialisation code to the empty code is computed by `initSegments?`. The results are
in `Silmaril.Wasm.Instantiation.Thms`.

* `initCode m`: the element and data segment code of `$instantiate`, as `prepare?` builds it
  (`prepare?_code`);
* `IsOffset m e`: `e` is the offset expression of an active element or data segment of `m`;
* `OffsetCompleteAt o ev f e`: in the host-free deterministic profile `profile o`, every
  evaluation of `e` from frame `f` keeps the frame, yields exactly one value, and is found by
  the evaluator `ev`.

Ported from an earlier development `Silmaril/Wasm/Execution/Core/Exec/{PrepareComplete,
SegmentInitComplete,InstantiateInitComplete,PrepareDirectComplete}.lean`
(see `docs/projects/wasm-components.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Instantiation

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- The element and data segment-initialisation code built by `prepare?`. -/
def initCode (m : Module) : List Admin :=
  expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
  expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d)

/-- `e` is the offset of an active element or data segment of `m`. -/
def IsOffset (m : Module) (e : Expr) : Prop :=
  (∃ el ∈ m.elems, ∃ y, el.mode = .active y e) ∨ (∃ d ∈ m.data, ∃ y, d.mode = .active y e)

/-- Every host-free evaluation of `e` from frame `f` keeps the frame, yields one value, and is
found by `ev`. -/
def OffsetCompleteAt (o : GrowOracle) (ev : Store H → Frame → Expr → Option (Store H × Val))
    (f : Frame) (e : Expr) : Prop :=
  ∀ s s' f' vs, EvalExpr (profile o) Det.noHost s f e s' f' vs →
    f' = f ∧ ∃ v, vs = [v] ∧ ev s f e = some (s', v)

end Silmaril.Wasm.Instantiation
