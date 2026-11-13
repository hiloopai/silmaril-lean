module

public import Silmaril.Wasm.Component.Reference.LinkFloat.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkFloatSound
import Silmaril.Proofs.Wasm.Component.Reference.LinkFloatSeq
import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkFloat

/-!
# Soundness of two linked components with floats in the importer's exports

`Linked2.sound_floatV` (proved, every silmaril profile `P` and component choice profile `prof`;
proof in `Silmaril.Proofs.Wasm.Component.Reference.LinkFloatSound`, with the branching top-level
call in `LinkFloatCall`): `Linked2.sound` with `l.imp.FloatFree` weakened to
`l.ImportsFloatFree`. The importer's exports may carry floats at every type, variant payloads
included; the IR is called on an admissible lowering `vs'` of the arguments (`NanAtVList prof`)
and the returned values are reported canonicalised (`Linked2.IRObsV`), as in
`Simple.sound_floatV`. `Linked2.sound_floatV_deterministic`: under the deterministic profile
`vs'` is `canonAtVList params vs`.

Not covered: floats in the importer's imports (equivalently, by `WireTy`, in the wired exports of
the exporter). The linked IR passes them bit for bit while the reference machine canonicalises
and re-chooses them at the crossing, so `l.toComp.den (impSem P)` does not cover them (see
`Reference.LinkFloat.Defs`; the litmus `Litmus.nanRb_floatWire` in
`Reference.LinkFloatWire`).

`Linked2.sound_seq_floatV` (proved, every profile and component choice profile; proof in
`Silmaril.Proofs.Wasm.Component.Reference.LinkFloatSeq`, with the branching call between calls in
`LinkFloatCallK`): `Linked2.sound_seq` with the same weakening. The linked IR plays the resolved
calls on admissible lowerings `calls'` of their arguments (`Linked2.NanCallsV`), the reference
reporting the IR results canonicalised (`Linked2.canonResultsV`), and the last call on an
admissible lowering `vs'` as `Linked2.SeqIRObsV` prescribes, as `Simple.sound_seq_floatV`.
`Linked2.sound_seq_floatV_deterministic`: the lowerings are the canonicalisations
(`Linked2.canonCallsV`, `canonAtVList`).

Litmus (proved; proofs in `Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkFloat`): `dblFhL`,
the doubler answering the import of `fhS`, whose export `h: func(f32) -> f32` carries a float
(`Litmus.dblFhL_not_floatFree`: `Linked2.sound` does not apply). `Litmus.dblFh_sound_floatV`
and `Litmus.dblFh_sound_seq_floatV` instantiate the two theorems for calls of `h`; the IR
denotation of `dblFhL` is not computed.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Numerics (Profile)

/-- **Soundness of two linked components with floats in the importer's exports** (proved, every
profile and component choice profile): under the hypotheses of `Linked2.sound` with
`l.imp.FloatFree` replaced by float-free imports, every behaviour of instantiating `l.toRef` and
calling the importer's export `j` on the reference images of well-typed IR values is the linked
IR observation of the call on an admissible lowering `vs'` of `vs` (floats related by
`NanLower prof` at any depth, variant payloads included), with returned values canonicalised. -/
theorem Linked2.sound_floatV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (l : Linked2) (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : Silmaril.Wasm.Component.ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHost impl) h₀ l.toRef [] l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ vs', NanAtVList prof l.imp.exports[j].ty.params vs vs' ∧
      Silmaril.Wasm.Component.ValTy.checkList l.imp.exports[j].ty.params vs' = true ∧
      Linked2.IRObsV P l j vs' b :=
  Silmaril.Proofs.Wasm.Component.Reference.linked2_sound_floatV P prof l hEg hEi hIg hIi har hfi hW
    hN hn hS impl h₀ j vs hvs b hb

/-- **Under the deterministic component profile** (proved): the linked IR is called on the
canonicalisation of the arguments. -/
theorem Linked2.sound_floatV_deterministic (P : Profile) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ)
    (h₀ : σ) (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : Silmaril.Wasm.Component.ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours .deterministic (linkHost impl) h₀ l.toRef []
      l.imp.exports[j].name (vs.map toRefVal)) :
    Linked2.IRObsV P l j (canonAtVList l.imp.exports[j].ty.params vs) b :=
  Silmaril.Proofs.Wasm.Component.Reference.linked2_sound_floatV_deterministic P l hEg hEi hIg hIi
    har hfi hW hN hn hS impl h₀ j vs hvs b hb

/-- **Soundness of two linked components for sequences of calls with floats in the importer's
exports** (proved, every profile and component choice profile): under the hypotheses of
`Linked2.sound_seq` with `l.imp.FloatFree` replaced by float-free imports, every behaviour of
instantiating `l.toRef`, calling the importer's exports `calls` in order (each resolving), then
export `j`, on reference images of well-typed IR values, is the linked IR play of admissible
lowerings `calls'` of the calls, with the IR results `wss` reported canonicalised, and the last
outcome is matched on an admissible lowering `vs'` of `vs` as `Linked2.SeqIRObsV` prescribes. -/
theorem Linked2.sound_seq_floatV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (l : Linked2) (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : Silmaril.Wasm.Component.ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHost impl) h₀ l.toRef
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ (calls' : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (vs' : List Silmaril.Wasm.Component.Val),
      Linked2.NanCallsV prof l calls calls' ∧ SimpleI.TypedCalls l.imp calls' ∧
      NanAtVList prof l.imp.exports[j].ty.params vs vs' ∧
      Silmaril.Wasm.Component.ValTy.checkList l.imp.exports[j].ty.params vs' = true ∧
      p.1 = Linked2.canonResultsV l calls' wss ∧
      Linked2.seqMoves l calls' wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObsV P l calls' wss j vs' p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.linked2_sound_seq_floatV P prof l hEg hEi hIg hIi har hfi
    hW hN hn hS impl h₀ calls j vs ht hvs p hp

/-- **Sequences of linked calls with floats under the deterministic component profile**
(proved): the linked IR is called on the canonicalised arguments. -/
theorem Linked2.sound_seq_floatV_deterministic (P : Profile) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : Silmaril.Wasm.Component.ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours .deterministic (linkHost impl) h₀ l.toRef
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val),
      p.1 = Linked2.canonResultsV l (Linked2.canonCallsV l calls) wss ∧
      Linked2.seqMoves l (Linked2.canonCallsV l calls) wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObsV P l (Linked2.canonCallsV l calls) wss j
        (canonAtVList l.imp.exports[j].ty.params vs) p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.linked2_sound_seq_floatV_deterministic P l hEg hEi hIg
    hIi har hfi hW hN hn hS impl h₀ calls j vs ht hvs p hp

/-- **Litmus: the importer of `dblFhL` exports a float** (proved), so `Linked2.sound` does not
apply to it. -/
theorem Litmus.dblFhL_not_floatFree : ¬ Litmus.dblFhL.imp.FloatFree :=
  Silmaril.Proofs.Wasm.Component.Reference.dblFhL_not_floatFree

/-- **Litmus: a call of the float export `h` of `dblFhL`** (proved, every profile, component
choice profile and host functions): the linked IR call of `h` on an admissible lowering of the
argument. -/
theorem Litmus.dblFh_sound_floatV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (x : BitVec 32) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHost impl) h₀ Litmus.dblFhL.toRef [] "h"
      [toRefVal (.f32 x)]) :
    ∃ vs', NanAtVList prof [.f32] [.f32 x] vs' ∧
      Silmaril.Wasm.Component.ValTy.checkList [.f32] vs' = true ∧
      Linked2.IRObsV P Litmus.dblFhL ⟨1, by decide⟩ vs' b :=
  Silmaril.Proofs.Wasm.Component.Reference.dblFh_sound_floatV P prof impl h₀ x b hb

/-- **Litmus: sequences of calls of the float export `h` of `dblFhL`** (proved, every profile,
component choice profile and host functions). -/
theorem Litmus.dblFh_sound_seq_floatV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (xs : List (BitVec 32)) (x : BitVec 32)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHost impl) h₀ Litmus.dblFhL.toRef
      (xs.map fun a => ("h", [toRefVal (.f32 a)])) "h" [toRefVal (.f32 x)]) :
    ∃ (calls' : List (Fin Litmus.dblFhL.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (vs' : List Silmaril.Wasm.Component.Val),
      Linked2.NanCallsV prof Litmus.dblFhL (xs.map fun a => (⟨1, by decide⟩, [.f32 a])) calls' ∧
      SimpleI.TypedCalls Litmus.dblFhL.imp calls' ∧ NanAtVList prof [.f32] [.f32 x] vs' ∧
      Silmaril.Wasm.Component.ValTy.checkList [.f32] vs' = true ∧
      p.1 = Linked2.canonResultsV Litmus.dblFhL calls' wss ∧
      Linked2.seqMoves Litmus.dblFhL calls' wss ∈ Litmus.dblFhL.toComp.den (impSem P) ∧
      Linked2.SeqIRObsV P Litmus.dblFhL calls' wss ⟨1, by decide⟩ vs' p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.dblFh_sound_seq_floatV P prof impl h₀ xs x p hp

/-- `l.imp.FloatFree` gives float-free imports (proved). -/
theorem Linked2.importsFloatFree_of_floatFree (l : Linked2) (h : l.imp.FloatFree) :
    l.ImportsFloatFree :=
  h.2

end Silmaril.Wasm.Component.Reference
