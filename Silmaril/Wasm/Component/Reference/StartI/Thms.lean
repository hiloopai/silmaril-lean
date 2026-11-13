module

public import Silmaril.Wasm.Component.Reference.StartI.Defs
public import Silmaril.Wasm.Component.Reference.Litmus.Defs
public import Silmaril.Wasm.Component.Reference.Example.Defs
import Silmaril.Proofs.Wasm.Component.Reference.StartISound
import Silmaril.Proofs.Wasm.Component.Reference.LitmusStartI

/-!
# Components with imports and a start function: theorems

For components with canon-lowered imports whose module may have a start function
(`SimpleI.InstS`), under the hypothesis that **the start phase makes no import call**
(`ImpModule.StartNoCall P`), at every silmaril profile `P` and component choice profile, over
`core3P P` with a host answering the imports:

* `SimpleI.sound_startS`, `SimpleI.sound_start` (proved): every behaviour of instantiating
  `c.toRef` (running the start function) and calling export `j` on the reference images of
  well-typed IR values is matched by the IR denotation over `impSemS P` (`IRObsIS`, resp.
  `IRObsI` for a stateless host). A trap of the start function is a trap of the instantiation,
  matched because `impSemS P` traps on every question when the start phase may fail;
* `SimpleI.sound_seq_startS`, `SimpleI.sound_seq_start` (proved): the same for sequences of
  calls on one instance (`seqBehavioursI`, `SeqIRObsIS`/`SeqIRObsI`), the instance's store
  threaded from a store the start phase returns at;
* `impSem_le_impSemS` (proved): on a module with an instance (no start function), `impSemS P`
  contains `impSem P`.

The hypothesis `StartNoCall` is semantic (no Core run of the start phase without host functions
reaches a host-call redex). Start functions that call imports are not covered: the IR's plays
begin with an export question, so they cannot show import calls made during instantiation.

Litmus (`Litmus.startIS`: import `g: func(u32) -> u32`; start function storing `42` in a global
read by the export `get`; export `f` forwarding to `g`): `Litmus.startIS_instS`,
`Litmus.startIS_valid`, `Litmus.startI_ref` (the reference machine over `core3 neverFail` with
the host `g(n) = n + 1` returns `42` from `get()`), `Litmus.startIMod_noCall` (the hypothesis,
discharged at every profile through the every-run program logic `Silmaril.Wasm.Logic.Hoare`: the
start function's specification `FSpecValid`, `FSpecValid.invoke_safe`, and the fact that a
host-call redex neither steps without host functions nor is an exit) and `Litmus.startI_sound`.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.{StartIBase,StartICall,StartIRun,StartIPhase,
StartISeq,StartIIR,StartISound,LitmusStartI}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Component (ProfileKind)
open Silmaril.Wasm.Component.Runtime (HostFuncId)
open Silmaril.Wasm.Component.Value (Val)
open Silmaril.Wasm.Numerics (Profile)

/-- **`impSemS P` extends `impSem P`** on modules with an instance (proved). -/
theorem impSem_le_impSemS (P : Profile) {m : ImpModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) : (impSem P).sem m ≤ (impSemS P).sem m :=
  Silmaril.Proofs.Wasm.Component.Reference.impSem_le_impSemS hI

/-- **Soundness of the component IR with imports and a start function, stateful host** (proved,
every profile and component choice profile): for a float-free component with imports within the
flat arities, wired as `SimpleI.toRef` assumes with a start function allowed, whose start phase
makes no import call, and a stateful host `g` answering in the IR's types, every behaviour of
instantiating `c.toRef` from host state `s₀` and calling export `j` on the reference images of
well-typed IR values is matched by the IR denotation over `impSemS P`. -/
theorem SimpleI.sound_startS (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree) (har : c.Arity) {σ : Type}
    (g : σ → HostFuncId → List Val → Option (List Val × σ)) (hg : c.HostOkS g) (s₀ : σ)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports c.exports[j].name
        (vs.map toRefVal),
      IRObsIS (c.toComp.den (impSemS P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g s₀ b :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_sound_startS P prof c hc hi hn hff har g hg s₀
    j vs hvs

/-- **Soundness with imports and a start function, stateless host** (proved). -/
theorem SimpleI.sound_start (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree) (har : c.Arity)
    (g : HostFuncId → List Val → Option (List Val)) (hg : c.HostOk g)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehavioursI prof (answerHost P g) () c.toRef c.imports c.exports[j].name
        (vs.map toRefVal),
      IRObsI (c.toComp.den (impSemS P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g b :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_sound_start P prof c hc hi hn hff har g hg j vs
    hvs

/-- **Soundness for sequences of calls with imports and a start function, stateful host**
(proved, every profile and component choice profile). -/
theorem SimpleI.sound_seq_startS (P : Profile) (prof : ProfileKind) (c : SimpleI)
    (hc : c.Good) (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree)
    (har : c.Arity) {σ : Type} (g : σ → HostFuncId → List Val → Option (List Val × σ))
    (hg : c.HostOkS g) (s₀ : σ)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Val) × Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))) (s₁ : σ),
      p.1 = wss.map (·.map toRefVal) ∧ HostRun g s₀ dss.flatten s₁ ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSemS P) ∧
      SeqIRObsIS c (c.toComp.den (impSemS P)) calls dss wss j vs g s₁ p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_sound_seq_startS P prof c hc hi hn hff har g hg
    s₀ calls j vs ht hvs p hp

/-- **Soundness for sequences of calls with imports and a start function, stateless host**
(proved). -/
theorem SimpleI.sound_seq_start (P : Profile) (prof : ProfileKind) (c : SimpleI) (hc : c.Good)
    (hi : c.InstS) (hn : c.mod.StartNoCall P) (hff : c.FloatFree) (har : c.Arity)
    (g : HostFuncId → List Val → Option (List Val)) (hg : c.HostOk g)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Val) × Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHost P g) () c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))),
      p.1 = wss.map (·.map toRefVal) ∧ (∀ ds ∈ dss, ∀ d ∈ ds, HostAnswers g d) ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSemS P) ∧
      SeqIRObsI c (c.toComp.den (impSemS P)) calls dss wss j vs g p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_sound_seq_start P prof c hc hi hn hff har g hg
    calls j vs ht hvs p hp

namespace Litmus

theorem startIS_instS : startIS.InstS := Silmaril.Proofs.Wasm.Component.Reference.Litmus.startIS_instS

theorem startIS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 startIS.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.startIS_valid

/-- **The start function of `startIMod` makes no import call** (proved, every profile). -/
theorem startIMod_noCall (P : Profile) : startIMod.StartNoCall P :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.startIMod_noCall P

/-- **The reference machine runs the start function**: over `core3 neverFail` with the host
`g(n) = n + 1`, `get()` returns `42`. -/
theorem startI_ref : Outcome.returns (some [toRefVal (.u32 42)]) ∈
    exportBehavioursI Silmaril.Wasm.Component.Reference.Core3Adder.first.prof
      (Host.ofEmbedder embI) () startIS.toRef startIS.imports "get" [] :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.startI_ref

/-- **Soundness on the start litmus with an import.** -/
theorem startI_sound (P : Profile) (prof : ProfileKind) :
    ∀ b ∈ exportBehavioursI prof (answerHost P fwdG) () startIS.toRef startIS.imports "get" [],
      IRObsI (startIS.toComp.den (impSemS P)) ⟨1, by decide⟩ [] fwdG b :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.startI_sound P prof

end Litmus

end Silmaril.Wasm.Component.Reference
