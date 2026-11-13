module

public import Silmaril.Wasm.Component.Reference.LinkSound.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkSound
import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkSound
import Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq
import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkSeq
public import Silmaril.Wasm.Component.Reference.Litmus.Defs

/-!
# Soundness of two linked components

`Linked2.sound` (proved, every profile and component choice profile; proof in
`Silmaril.Proofs.Wasm.Component.Reference.LinkSound`): every behaviour of instantiating the
reference translation `l.toRef` of two linked components and calling an export of the importer
on well-typed values is matched by the IR denotation of `l.toComp` (`Linked2.IRObs`). The
importer's calls of its imports run, inside the reference machine, as nested `canon lower` /
`canon lift` calls of the exporter in the shared core store; on the IR side they are component
import calls answered by the exporter's canonical-ABI specification (`Linked2.ExpRun`).

`Linked2.sound_seq` (proved, every profile and component choice profile; proof in
`Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq`): the same for sequences of calls of the
importer's exports on one instance of `l.toRef`; both components' instance states persist between
calls (the importer's play of its core instance and the exporter's run of its specification are
each threaded from their instance's store), and the resolved calls are one multi-question play of
the linked IR (`Linked2.seqMoves`, `Linked2.SeqIRObs`).

`dblFwd_sound`, `dblFwd_sound_seq`: the instances for the litmus `dblFwdL` (the doubler
answering `fwdS`'s import).

Not covered here: nested components beyond `Linked2`, floats in the importer's interface (floats
in the importer's exports: `Linked2.sound_floatV`, `Silmaril.Wasm.Component.Reference.LinkFloat`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Numerics (Profile)

/-- **Soundness of two linked components for single calls** (proved, every profile and
component choice profile): for an exporter and an importer in the instantiation fragment, the
importer float-free and within the flat arities, the wiring well typed and injective, export
names avoiding generated type names and both core modules in the split fragment, every behaviour
of instantiating `l.toRef` and calling the importer's export `j` on the reference images of
well-typed IR values, under `linkHost impl` from any host state, is matched by the linked IR
denotation over `impSem P`. -/
theorem Linked2.sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2)
    (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : Silmaril.Wasm.Component.ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHost impl) h₀ l.toRef [] l.imp.exports[j].name
      (vs.map toRefVal)) :
    Linked2.IRObs P l j vs b :=
  Silmaril.Proofs.Wasm.Component.Reference.linked2_sound P prof l hEg hEi hIg hIi har hff hW hN hn
    hS impl h₀ j vs hvs b hb

/-- **Soundness of the litmus `dblFwdL`** (proved, every profile, component choice profile and
host functions): every behaviour of instantiating `dblFwdL.toRef` and calling `f` on `x` is
matched by the linked IR (`Linked2.sound`). -/
theorem Litmus.dblFwd_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) (x : BitVec 32) :
    ∀ b ∈ exportBehaviours prof (linkHost impl) h₀ Litmus.dblFwdL.toRef [] "f"
        [toRefVal (.u32 x)],
      Linked2.IRObs P Litmus.dblFwdL ⟨0, by decide⟩ [.u32 x] b :=
  Silmaril.Proofs.Wasm.Component.Reference.dblFwd_sound P prof impl h₀ x

/-- **Soundness of two linked components for sequences of calls on one instance** (proved, every
profile and component choice profile): under the hypotheses of `Linked2.sound`, every behaviour
of instantiating `l.toRef`, calling the importer's exports `calls` in order (each resolving),
then export `j`, on the reference images of well-typed IR values, under `linkHost impl` from any
host state, records reference images of IR results `wss`; the linked IR denotation plays the
resolved calls with these results, and the last outcome as `Linked2.SeqIRObs` prescribes. -/
theorem Linked2.sound_seq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2)
    (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk)
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
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Linked2.seqMoves l calls wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObs P l calls wss j vs p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.linked2_sound_seq P prof l hEg hEi hIg hIi har hff hW hN
    hn hS impl h₀ calls j vs ht hvs p hp

/-- **Sequences of calls of the litmus `dblFwdL`** (proved, every profile, component choice
profile and host functions): every behaviour of instantiating `dblFwdL.toRef`, calling `f` on
each of `xs` (each resolving), then on `x`, is matched by the linked IR (`Linked2.sound_seq`). -/
theorem Litmus.dblFwd_sound_seq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (xs : List (BitVec 32)) (x : BitVec 32)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHost impl) h₀ Litmus.dblFwdL.toRef
      (xs.map fun a => ("f", [toRefVal (.u32 a)])) "f" [toRefVal (.u32 x)]) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Linked2.seqMoves Litmus.dblFwdL (xs.map fun a => (⟨0, by decide⟩, [.u32 a])) wss ∈
        Litmus.dblFwdL.toComp.den (impSem P) ∧
      Linked2.SeqIRObs P Litmus.dblFwdL (xs.map fun a => (⟨0, by decide⟩, [.u32 a])) wss
        ⟨0, by decide⟩ [.u32 x] p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.dblFwd_sound_seq P prof impl h₀ xs x p hp

end Silmaril.Wasm.Component.Reference
