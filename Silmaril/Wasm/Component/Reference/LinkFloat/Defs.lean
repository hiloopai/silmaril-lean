module

public import Silmaril.Wasm.Component.Reference.LinkSound.Defs
public import Silmaril.Wasm.Component.Reference.FloatV.Defs

/-!
# Soundness of two linked components with floats: definitions

`Linked2.sound` (`Reference.LinkSound`) assumes `l.imp.FloatFree`: no floats in the importer's
exports or imports. This header states the observation for floats anywhere in the importer's
*exports* (variant payloads included), the imports — and so, by `WireTy`, the wired exports of
the exporter — float-free:

* `Linked2.ImportsFloatFree l`: the component types of the importer's imports have no floats;
* `Linked2.IRObsV P l j vs' b`: `Linked2.IRObs` on the arguments `vs'` (an admissible lowering of
  the reference arguments, `NanAtVList`), with returned values reported canonicalised
  (`canonAtVList`), as `IRObsFV` for `Simple`;
* `Linked2.NanCallsV`, `Linked2.canonCallsV`, `Linked2.canonResultsV`, `Linked2.SeqIRObsV`: for
  sequences of calls, the admissible lowerings of the calls, their canonicalisations, the
  canonicalised results and the last call's observation (as `NanCallsV`, `canonCallsV`,
  `canonResultsV`, `SeqIRObsFV` for `Simple`).

**Why the imports stay float-free.** The linked IR `l.toComp.den (impSem P)` passes a float from
the importer's core instance to the exporter's bit for bit (`ImpRel` lifts with `liftArgs`,
`RetAt` lowers with `lowerArgs`; the IR models no NaN canonicalisation), and back. The reference
machine canonicalises the NaN in the trampoline's `lift_flat` and then makes a C7 choice
(`NanLower prof`) in the exporter's `lower_flat`. An exporter that observes NaN bits
(`i32.reinterpret_f32`) of a non-canonical NaN produced by the importer then returns, in the
reference machine, bits that no IR play has, at every component choice profile: under
`deterministic` the canonical NaN, under `nondet` any NaN, under `refStrict` a `RandomNaNBits`
NaN, against the IR's raw bits. Covering floats across the wiring needs a linked IR that relates
the two components' floats by NaN lowering at each crossing (a NaN-relational linked IR), not
`l.toComp.den (impSem P)`. (The counterexample is formalised in part in
`Reference.LinkFloatWire`: the reference and IR answers are computed, but neither the
reference over `core3P P` nor the absence of other IR plays is shown.)
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component

namespace Linked2

/-- The component types of the importer's imports have no floats. -/
def ImportsFloatFree (l : Linked2) : Prop :=
  ∀ p ∈ l.imp.imports, floatFreeList p.2.params = true ∧ floatFreeList p.2.results = true

/-- **What the IR must exhibit for a reference outcome** `b`, with floats in the importer's
export `j`: the play of the call on the arguments `vs'`, the returned values reported
canonicalised (`canonAtVList`); a trap is the play answering `none`. Divergence and deadlock
impose nothing. -/
def IRObsV (P : Silmaril.Wasm.Numerics.Profile) (l : Linked2) (j : Fin l.imp.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) : Outcome → Prop
  | .returns (some rs) => ∃ ws : List Silmaril.Wasm.Component.Val,
      rs = (canonAtVList l.imp.exports[j].ty.results ws).map toRefVal ∧
      [.inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) (some (.vals ws)))] ∈
        l.toComp.den (impSem P)
  | .traps =>
      [.inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) none)] ∈
        l.toComp.den (impSem P)
  | _ => True

/-- **Admissible lowerings of the calls** `calls` of the importer's exports: the same exports,
each argument list related by `NanAtVList prof` (`NanCallsV` for `Linked2`). -/
def NanCallsV (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2) :
    List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val) →
    List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val) → Prop :=
  List.Forall₂ fun q q' => q'.1 = q.1 ∧ NanAtVList prof l.imp.exports[q.1].ty.params q.2 q'.2

/-- The calls with canonicalised arguments (`canonCallsV` for `Linked2`). -/
def canonCallsV (l : Linked2)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val) :=
  calls.map fun q => (q.1, canonAtVList l.imp.exports[q.1].ty.params q.2)

/-- The reference images of the IR results `wss` of the calls, canonicalised
(`canonResultsV` for `Linked2`). -/
def canonResultsV (l : Linked2) :
    List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val) →
    List (List Silmaril.Wasm.Component.Val) → List (List Silmaril.Wasm.Component.Value.Val)
  | q :: cs, ws :: wss =>
    (canonAtVList l.imp.exports[q.1].ty.results ws).map toRefVal :: canonResultsV l cs wss
  | _, _ => []

/-- **What the IR must exhibit for the last call of a sequence** with floats in the importer's
exports: `Linked2.SeqIRObs` with the returned values reported canonicalised. -/
def SeqIRObsV (P : Silmaril.Wasm.Numerics.Profile) (l : Linked2)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (wss : List (List Silmaril.Wasm.Component.Val)) (j : Fin l.imp.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) : Outcome → Prop
  | .returns (some rs) => ∃ ws : List Silmaril.Wasm.Component.Val,
      rs = (canonAtVList l.imp.exports[j].ty.results ws).map toRefVal ∧
      seqMoves l (calls ++ [(j, vs)]) (wss ++ [ws]) ∈ l.toComp.den (impSem P)
  | .traps => seqMoves l calls wss ++
      [.inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)),
        .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) none)] ∈
        l.toComp.den (impSem P)
  | _ => True

end Linked2

/-! ## Litmus: an importer with an `f32` export -/

namespace Litmus

/-- `(type (func (param i32) (result i32))) (type (func (param f32) (result f32)))
(import "env" "g" (func (type 0))) (func (type 1) local.get 0)
(export "f" (func 0)) (export "h" (func 1))`: the import re-exported as `f`, and the identity
on `f32` exported as `h`. -/
def fhCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[.f32], [.f32]⟩⟩]⟩]
  imports := [⟨"env", "g", .func ⟨0⟩⟩]
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩, ⟨"h", .func ⟨1⟩⟩]

/-- The module with its import and export interfaces. -/
def fhMod : ImpModule :=
  ⟨fhCore3, [("g", ⟨[.int .i32], [.int .i32]⟩)],
    [("f", ⟨[.int .i32], [.int .i32]⟩), ("h", ⟨[.float .f32], [.float .f32]⟩)]⟩

/-- `fwdS` with a second export `h: func(f32) -> f32`, the identity: the import
`g: func(u32) -> u32` lowered into `fhCore3`, whose exports are lifted as
`f: func(u32) -> u32` and `h: func(f32) -> f32`. -/
def fhS : SimpleI :=
  ⟨fhMod, [("g", ⟨[.u32], [.u32]⟩)],
    [⟨"f", ⟨[.u32], [.u32]⟩, 0⟩, ⟨"h", ⟨[.f32], [.f32]⟩, 1⟩]⟩

/-- `fhS` with its import `g` answered by the doubler's export `g`: `f(x) = 2x`, `h(x) = x`.
The importer exports a float (`h`); its import, and so the wired export of the exporter, is
float-free. -/
def dblFhL : Linked2 := ⟨dblS, fhS, [0]⟩

end Litmus

end Silmaril.Wasm.Component.Reference
