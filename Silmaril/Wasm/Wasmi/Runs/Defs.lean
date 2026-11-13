module

public import Silmaril.Wasm.Wasmi.Observed.Defs

/-!
# Every run of the wasmi 0.40.0 model on a rounding call

Track wasmi showed single runs of the wasmi 0.40.0 model (`Silmaril.Wasm.Wasmi.Observed.Step`) on
the harness's rounding witness calls (`wasmi_returns`, `model_returns`). This topic gives the
model's **full behaviour sets** on those calls: every finite run, every trap and every infinite
run. Two definitions:

* `fire`, `fireA`: the code after a quirk step. A quirk step (`Variant.Ctx Quirk`) rewrites the
  first redex `t.const x; t.op` of the code (under leading values, labels, handlers and frames)
  to `t.const x`; `fire` is this rewrite as a function, so quirk steps are deterministic
  (`Silmaril.Wasm.Wasmi.Runs.ctx_quirk_iff`);
* `wUnOpP P t op x z`: the results the model allows for `t.op x` at profile `P`: the input when
  `op` rounds and `x` is a NaN (the quirk), otherwise every result Core allows.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.Runs

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Wasmi.Observed

mutual
/-- `fire` inside a label, handler or frame. -/
def fireA : Admin → Admin
  | .label n cont b => .label n cont (fire b)
  | .handler n cs b => .handler n cs (fire b)
  | .frame n f b => .frame n f (fire b)
  | a => a

/-- **The code after a quirk step**: the first redex `t.const x; t'.op`, after the leading
values and inside labels, handlers and frames, becomes `t.const x`. Meaningful where `pending`
holds. -/
def fire : List Admin → List Admin
  | [] => []
  | .plain (.floatConst t x) :: .plain (.floatUnOp _ _) :: rest => .plain (.floatConst t x) :: rest
  | a :: rest =>
    match a.val? with
    | some _ => a :: fire rest
    | none => fireA a :: rest
end

/-- **The results the wasmi 0.40.0 model allows for `t.op x`** at profile `P`: the input for a
rounding operator on a NaN, otherwise the results Core 3.0 allows. -/
def wUnOpP (P : Profile) (t : FloatType) (op : FloatUnOp) (x z : FloatValue t) : Prop :=
  if IsRound op = true ∧ isNaNB t x = true then z = x else floatUnOpP P t op x z

end Silmaril.Wasm.Wasmi.Runs
