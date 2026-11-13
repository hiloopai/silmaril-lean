module

public import Silmaril.Wasm.Component.Reference.Start.Defs
public import Silmaril.Wasm.Component.Reference.Example.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LitmusStart

/-!
# Simple components with a start function: theorems

For simple components whose module may have a start function (`Simple.InstS`), at every silmaril
profile `P` and component choice profile, over `core3P P` with the reference host:

* `Simple.sound_start` (proved): every behaviour of instantiating `c.toRef` and calling export
  `j` on the reference images of well-typed IR values is matched by the IR denotation over
  `modSemS P` (`IRObs`). A trap of the start function is a trap of the instantiation, matched
  because `modSemS P` traps on every question when the start phase may fail;
* `Simple.sound_seq_start` (proved): the same for sequences of calls on one instance
  (`seqBehaviours`, `SeqIRObs`), the instance's store threaded from a store the start phase
  returns at;
* `modSem_le_modSemS` (proved): on a module with an instance (no start function), `modSemS P`
  contains `modSem P`.

Litmus (`Litmus.startS`, start function storing `42` in a global read by the export `get`):
`Litmus.startS_instS`, `Litmus.startS_valid`, `Litmus.start_ref` (the reference machine over
`core3 neverFail` returns `42`) and `Litmus.start_sound`.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.{StartBase,StartCall,StartInst,StartRun,
StartPhase,StartSeq,StartIR,LitmusStart}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

/-- **`modSemS P` extends `modSem P`** on modules with an instance (proved). -/
theorem modSem_le_modSemS (P : Profile) {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) : (modSem P).sem m ≤ (modSemS P).sem m :=
  Silmaril.Proofs.Wasm.Component.Reference.modSem_le_modSemS hI

/-- **Soundness of the component IR with a start function** (proved, every profile and
component choice profile): for a float-free simple component within the flat arities whose
module, possibly with a start function, is instantiated as `Simple.toRef` assumes, every
behaviour of calling export `j` on the reference images of well-typed IR values, after
instantiating `c.toRef` (running the start function), is matched by the IR denotation over
`modSemS P`. -/
theorem Simple.sound_start (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.InstS) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name (vs.map toRefVal),
      IRObs (c.toComp.den (modSemS P)) ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Silmaril.Proofs.Wasm.Component.Reference.simple_sound_start P prof c hc hf hi ha j vs hvs

/-- **Soundness for sequences of calls with a start function** (proved, every profile and
component choice profile). -/
theorem Simple.sound_seq_start (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.InstS) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSemS P) ∧
      SeqIRObs c (c.toComp.den (modSemS P)) calls wss j vs p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.simple_sound_seq_start P prof c hc hf hi ha calls j vs ht
    hvs p hp

namespace Litmus

open Silmaril.Wasm.Component.Reference.Core3Adder (emb first)

theorem startS_instS : startS.InstS := Silmaril.Proofs.Wasm.Component.Reference.Litmus.startS_instS

theorem startS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 startS.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.startS_valid

/-- **The reference machine runs the start function**: over `core3 neverFail`, `get()` returns
`42`. -/
theorem start_ref : Outcome.returns (some [toRefVal (.u32 42)]) ∈
    exportBehaviours first.prof (Host.ofEmbedder emb) () startS.toRef [] "get" [] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.start_ref

/-- **Soundness for the start litmus.** -/
theorem start_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) :
    ∀ b ∈ exportBehaviours prof (refHost P) () startS.toRef [] "get" [],
      IRObs (startS.toComp.den (modSemS P)) ⟨0, by decide⟩ [] b :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.start_sound P prof

end Litmus

end Silmaril.Wasm.Component.Reference
