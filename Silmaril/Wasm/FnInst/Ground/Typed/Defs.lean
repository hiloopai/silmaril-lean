module

public import Silmaril.Wasm.FnInst.Ground.Defs

@[expose] public section

/-! # A typed frame-free bridge: reads on the typed side

`Good` pairs need equal runs from **every** frame, so a right side that reads a local has
to cope with frames where the local is missing or unset. Silmaril's typed closure
(`Execution.Core.Sim.TypedBaseSim`, used by `exportRefines_of_typedBodiesRel`) knows that the
right configuration is typed in its active context. Typing turns each leading `local.get` of
the right side into a value of the actual frame (`CtxOk.set`), and typing survives the steps
of those reads. So the right side may read several locals, provided the runs agree in the
frames where its leading reads hold values:

* `LeadRd b f`: every leading `local.get` of `b` holds a value in `f`;
* `RunRefT a b`: wherever `a` runs and the leading reads of `b` hold values, `b` runs to the
  same result;
* `GoodT a b`: a stack-only left side that is not all constants (`StkOp`), with `RunRefT`;
* `GTI`, `GT`: the source and runtime base relations (the right side never moves before the
  left side has become values; the runtime pairs keep `PairRefT`).

The bridge is `gTypedSim : TypedBaseSim P F GTI GT gCodeRank` at every numerical profile
(`Silmaril.Wasm.FnInst.Ground.Typed.Thms`).
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The leading reads of `b` hold values in `f`. -/
def LeadRd : List GInstr → Frame → Prop
  | .localGet x :: L, f => (∃ v, f.local? x = some (some v)) ∧ LeadRd L f
  | _, _ => True

/-- Equal runs where the right side's leading reads hold values. -/
def RunRefT (a b : List GInstr) : Prop :=
  ∀ f st r, LeadRd b f → run a f st = some r → run b f st = some r

/-- Typed pairs: a stack-only left side with equal runs where the right side's leading reads
hold values. -/
def GoodT (a b : List GInstr) : Prop := StkOp a ∧ RunRefT a b

/-- Source base pairs: lowered typed pairs. -/
def GTI (x y : List Instr) : Prop :=
  ∃ a b, GoodT a b ∧ x = lower a ∧ y = lower b

/-- The semantic condition of a typed runtime pair. -/
def PairRefT (q : List Val) (a : List GInstr) (r : List Val) (b : List GInstr) : Prop :=
  ∀ f S res, LeadRd b f → run a f (q.reverse ++ S) = some res →
    run b f (r.reverse ++ S) = some res

/-- Runtime base pairs: a stack-only left side, after values `q`, against values `r` and the
untouched right code `b`. -/
def GT (x y : List Admin) : Prop :=
  ∃ q a r b, x = vals q ++ expression (lower a) ∧ y = vals r ++ expression (lower b) ∧
    StkOp a ∧ PairRefT q a r b

end Silmaril.Wasm.FnInst.Ground
