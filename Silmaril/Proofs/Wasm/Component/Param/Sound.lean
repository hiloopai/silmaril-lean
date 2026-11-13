module

public import Silmaril.Wasm.Component.Param.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Thms
public import Silmaril.Wasm.Component.Reference.LinkSound.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.MultiIR

/-!
# Soundness of the component IR over an engine: proofs

* `refToSpec_core3P`, `seqRefToSpec_core3P`, `link2Sound_core3P`, `link2SoundSeq_core3P`: the
  Core 3.0 engine `core3P P` has the four soundness properties (from the existing proofs);
* `Simple.soundE`, `Simple.sound_seqE`, `Linked2.soundE`, `Linked2.sound_seqE`: soundness of the
  IR over any engine with these properties, by composing with the engine-independent IR halves
  (`specToIR`, `seqSpecToIR`);
* `Simple.sound_core3P`, `Simple.sound_seq_core3P`, `Linked2.sound_core3P`,
  `Linked2.sound_seq_core3P`: the existing theorems recovered as instances.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

theorem map_id_core3P (P : Profile) (c : Core3Component) :
    Silmaril.Wasm.Component.Syntax.Component.map (N := (core3P P).Module) id c = c :=
  Silmaril.Wasm.Component.Syntax.Component.map_id c

theorem refHostE_core3P (P : Profile) : refHostE (core3P P) = refHost P := rfl

theorem linkHostE_core3P {P : Profile} {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) :
    linkHostE impl = linkHost impl := rfl

/-! ## The Core 3.0 engine -/

theorem refToSpec_core3P (P : Profile) : RefToSpec (core3P P) id P := by
  intro prof c hc hf hi ha x hx vs hvs
  erw [map_id_core3P, refHostE_core3P]
  exact refToSpec_of_arity P prof c hc hf hi ha x hx vs hvs

theorem seqRefToSpec_core3P (P : Profile) : SeqRefToSpec (core3P P) id P := by
  intro prof c hc hf hi ha calls j vs ht hvs p hp
  erw [map_id_core3P, refHostE_core3P] at hp
  exact seq_refToSpec P prof c hc hf hi ha calls j vs ht hvs p hp

theorem link2Sound_core3P (P : Profile) : Link2Sound (core3P P) id P := by
  intro prof l hEg hEi hIg hIi har hff hW hN hn hS σ impl h₀ j vs hvs b hb
  erw [map_id_core3P, linkHostE_core3P] at hb
  exact Linked2.sound P prof l hEg hEi hIg hIi har hff hW hN hn hS impl h₀ j vs hvs b hb

theorem link2SoundSeq_core3P (P : Profile) : Link2SoundSeq (core3P P) id P := by
  intro prof l hEg hEi hIg hIi har hff hW hN hn hS σ impl h₀ calls j vs ht hvs p hp
  erw [map_id_core3P, linkHostE_core3P] at hp
  exact Linked2.sound_seq P prof l hEg hEi hIg hIi har hff hW hN hn hS impl h₀ calls j vs ht
    hvs p hp

/-! ## Soundness over an engine -/

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]
  {ofCore : Silmaril.Wasm.Module → E.Module} {P : Profile}

/-- **Soundness of the IR over an engine with the reference-machine half.** -/
theorem Simple.soundE (hR : RefToSpec E ofCore P) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE E) () (c.toRef.map ofCore) [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  specToIR P c hc j vs b (hR prof c hc hf hi ha _ (List.getElem_mem j.isLt) vs hvs hb)

/-- **Soundness of the IR for sequences of calls over an engine with the reference-machine
half for sequences.** -/
theorem Simple.sound_seqE (hR : SeqRefToSpec E ofCore P)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHostE E) () (c.toRef.map ofCore)
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs p.2 := by
  obtain ⟨I, wss, s, hI, hseq, hp1, hp2⟩ := hR prof c hc hf hi ha calls j vs ht hvs p hp
  exact ⟨wss, hp1, Silmaril.Proofs.Wasm.Component.Reference.seq_prefix hc hI hseq,
    Silmaril.Proofs.Wasm.Component.Reference.seqIRObs_of p.2
      (seqSpecToIR P c hc I hI calls wss s j vs p.2 hseq hp2)⟩

/-- **Soundness of two linked components over an engine** with `Link2Sound`. -/
theorem Linked2.soundE (hR : Link2Sound E ofCore P) (prof : Silmaril.Wasm.Component.ProfileKind)
    (l : Linked2) (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl E σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHostE impl) h₀ (l.toRef.map ofCore) []
      l.imp.exports[j].name (vs.map toRefVal)) :
    Linked2.IRObs P l j vs b :=
  hR prof l hEg hEi hIg hIi har hff hW hN hn hS impl h₀ j vs hvs b hb

/-- **Soundness of two linked components for sequences of calls over an engine** with
`Link2SoundSeq`. -/
theorem Linked2.sound_seqE (hR : Link2SoundSeq E ofCore P)
    (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl E σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHostE impl) h₀ (l.toRef.map ofCore)
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Linked2.seqMoves l calls wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObs P l calls wss j vs p.2 :=
  hR prof l hEg hEi hIg hIi har hff hW hN hn hS impl h₀ calls j vs ht hvs p hp

/-! ## The existing theorems as instances -/

/-- `Reference.Simple.sound`, recovered from `Simple.soundE`. -/
theorem Simple.sound_core3P (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b := by
  refine Simple.soundE (refToSpec_core3P P) prof c hc hf hi ha j vs hvs b ?_
  erw [map_id_core3P]; assumption

/-- `Reference.Simple.sound_seq`, recovered from `Simple.sound_seqE`. -/
theorem Simple.sound_seq_core3P (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs p.2 := by
  refine Simple.sound_seqE (seqRefToSpec_core3P P) prof c hc hf hi ha calls j vs ht hvs p ?_
  erw [map_id_core3P]; assumption

end Silmaril.Proofs.Wasm.Component.Param
