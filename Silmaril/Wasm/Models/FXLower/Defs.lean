module

public import Silmaril.Wasm.Models.FX.Defs

/-!
# Lowering WasmFX to Wasm: a first fragment

A first compilation of WasmFX code to Core 3.0 code, for the smallest fragment where the
continuation machinery can be compiled away: **resuming a fresh continuation of a Core
function**. The source

    ref.func a; cont.new $ct; resume $ct (on …)*     (with arguments vs)

allocates a one-shot continuation of `a`, consumes it at once and runs the body under a handler
frame. If `a` is a Core function, its body has no `suspend` or `switch` (Core code has no FX
instructions, and `blockFX` keeps FX host functions out of Core steps), so the handler frame is
never used. The target is a plain call:

    ref.func a; call_ref (type of a)                 (with arguments vs)

The fragment is stated on administrative code, which is where `StepFX` and Core `Step` meet:

* `srcResume a ct hs vs`: the FX source configuration code;
* `tgtCall a d vs`: the Core target code (`d` is the defined type of `a`);
* `onHandler hs cs`: Core code `cs` under a handler frame, as FX code (an intermediate form).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX

/-- **Source**: resume a fresh continuation of function address `a` with arguments `vs`. -/
def srcResume (a : Nat) (ct : TypeIdx) (hs : List OnClause) (vs : List Val) : List AdminFX :=
  cvals vs ++ [.core (.ref (.func a)), .fx (.contNew ct), .fx (.resume ct hs)]

/-- **Target**: call function address `a` (of defined type `d`) with arguments `vs`. -/
def tgtCall (a : Nat) (d : DefType) (vs : List Val) : List Admin :=
  vals vs ++ [.ref (.func a), .callRefType d]

/-- Core code under a handler frame. -/
def onHandler (hs : List HClause) (cs : List Admin) : List AdminFX :=
  [.handler hs (cs.map .core)]

end Silmaril.Wasm.Models.FXLower
