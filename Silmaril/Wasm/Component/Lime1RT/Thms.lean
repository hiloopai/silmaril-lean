module

public import Silmaril.Wasm.Component.Lime1RT.Defs
public import Silmaril.Wasm.Component.Lime1G.Thms
public import Silmaril.Wasm.Component.Hered.Thms
public import Silmaril.Proofs.Wasm.Component.Lime1RT.Rt

/-!
# Core 3.0 restricted to Lime1 at runtime: theorems

**What `core3LG` does not restrict.**

* `core3LG_sem_eq`: the game semantics of `Lime1G.core3LG P` (Core 3.0 with validity restricted
  to `lime1`) **is** that of Core 3.0, for every module, Lime1 or not. The restriction lives in
  `Valid`, which neither `engineSem` nor the component machine consults.

**The runtime restriction `core3LRG P`.**

* `lime1RT_closed`: the runtime invariant of `lime1` is closed under the Core 3.0 internal step;
* `core3LRG_le`: the game semantics refines Core 3.0's;
* **`core3LRG_sem_eq`**: on every module whose Core 3.0 instance has a store of `lime1`, it
  equals Core 3.0's. So the runtime restriction loses nothing on Lime1 code, and outside it no
  internal step leaves Lime1;
* `refToSpecH_core3LRG` (and the three siblings): the hereditary soundness properties of
  `Silmaril.Wasm.Component.Hered`, inherited from Core 3.0 by `RefToSpecH.restrict`. They also hold
  for every further restriction (a profile inside Lime1);
* **`Simple.sound_core3LRG`**, `Simple.sound_seq_core3LRG`, **`Linked2.sound_core3LRG`**,
  `Linked2.sound_seq_core3LRG`: soundness of the reference component machine over the runtime
  restriction against the IR. `refToSpecH_core3LG` gives the same properties for `core3LG`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1RT

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
  Silmaril.Wasm.Component.Hered
open Silmaril.Wasm.Numerics (Profile)

/-! ## `core3LG` is Core 3.0 at the game level -/

/-- Every instance respects a restriction whose runtime invariant is `True`. -/
theorem respects_lime1R (P : Profile) (I : EInstance (core3P P)) :
    Silmaril.Proofs.Wasm.Component.Param.Respects (Lime1G.lime1R P) I (fun _ => True) where
  closed _ _ := trivial
  init := trivial
  invoke _ _ _ _ _ := trivial
  store _ _ _ := trivial
  resume _ _ _ _ _ _ _ := trivial

/-- **The game semantics of `core3LG P` is that of Core 3.0**: restricting `Valid` alone does
not restrict the engine's game semantics. -/
theorem core3LG_sem_eq (P : Profile) (m : NumModule) :
    (Lime1G.core3LG P).sem.sem m = (core3G P).sem.sem m :=
  Silmaril.Proofs.Wasm.Component.Lime1RT.engineSem_restrict_eq (E := core3P P)
    (r := Lime1G.lime1R P) NumModule.mod m fun I _ => ⟨_, respects_lime1R P I⟩

/-! ## The runtime restriction -/

/-- **The runtime invariant of `lime1` is closed under the Core 3.0 internal step.** -/
theorem lime1RT_closed (P : Profile) : (lime1RT P).Closed :=
  Silmaril.Proofs.Wasm.Component.Lime1RT.closed P

/-- The runtime restriction refines Core 3.0. -/
theorem core3LRG_le (P : Profile) : (core3LRG P).sem.Le (core3G P).sem :=
  engineSem_restrict_le (E := core3P P) (r := lime1RT P) NumModule NumModule.mod

/-- **On an instance whose store is of `lime1`, the runtime restriction is Core 3.0.** -/
theorem engineStrategy_core3LRG_eq (P : Profile) {I : EInstance (core3P P)}
    (hI : Silmaril.Wasm.Models.Rt.StoreIn Silmaril.Wasm.Models.lime1 (H := Nat) I.store)
    (imps exps : CoreIface) :
    engineStrategy (restrict (core3P P) (lime1RT P)) I.res imps exps =
      engineStrategy (core3P P) I imps exps :=
  engineStrategy_restrict_eq (Silmaril.Proofs.Wasm.Component.Lime1RT.respects P hI) imps exps

/-- **The game semantics of the runtime restriction is Core 3.0's on every module whose Core
3.0 instance has a store of `lime1`** (and on every module without an instance). -/
theorem core3LRG_sem_eq (P : Profile) (m : NumModule)
    (hm : ∀ I, instOf (core3P P) m.mod (CoreModule.imports m) (CoreModule.exports m) = some I →
      Silmaril.Wasm.Models.Rt.StoreIn Silmaril.Wasm.Models.lime1 (H := Nat) I.store) :
    (core3LRG P).sem.sem m = (core3G P).sem.sem m :=
  Silmaril.Proofs.Wasm.Component.Lime1RT.engineSem_restrict_eq (E := core3P P)
    (r := lime1RT P) NumModule.mod m fun I h =>
      ⟨_, Silmaril.Proofs.Wasm.Component.Lime1RT.respects P (hm I h)⟩

/-! ## Soundness -/

theorem refToSpecH_core3LRG (P : Profile) :
    RefToSpecH (restrict (core3P P) (lime1RT P)) id P :=
  (refToSpecH_core3P P).restrict (lime1RT P)

theorem seqRefToSpecH_core3LRG (P : Profile) :
    SeqRefToSpecH (restrict (core3P P) (lime1RT P)) id P :=
  (seqRefToSpecH_core3P P).restrict (lime1RT P)

theorem link2SoundH_core3LRG (P : Profile) :
    Link2SoundH (restrict (core3P P) (lime1RT P)) id P :=
  (link2SoundH_core3P P).restrict (lime1RT P)

theorem link2SoundSeqH_core3LRG (P : Profile) :
    Link2SoundSeqH (restrict (core3P P) (lime1RT P)) id P :=
  (link2SoundSeqH_core3P P).restrict (lime1RT P)

/-- `core3LG` has the hereditary reference-machine half too. -/
theorem refToSpecH_core3LG (P : Profile) :
    RefToSpecH (restrict (core3P P) (Lime1G.lime1R P)) id P :=
  (refToSpecH_core3P P).restrict (Lime1G.lime1R P)

/-- **Soundness of the IR for the reference machine over Core 3.0 restricted to `lime1` at
runtime.** -/
theorem Simple.sound_core3LRG (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (restrict (core3P P) (lime1RT P))) ()
      (c.toRef.map id) [] c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Hered.Simple.sound_restrictH (refToSpecH_core3P P) (lime1RT P) prof c hc hf hi ha j vs hvs b
    hb

/-- Soundness for sequences of calls over the runtime restriction. -/
theorem Simple.sound_seq_core3LRG (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHostE (restrict (core3P P) (lime1RT P))) ()
      (c.toRef.map id) (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal))
      c.exports[j].name (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs p.2 :=
  Hered.Simple.sound_seq_restrictH (seqRefToSpecH_core3P P) (lime1RT P) prof c hc hf hi ha calls
    j vs ht hvs p hp

/-- **Soundness of two linked components over the runtime restriction.** -/
theorem Linked2.sound_core3LRG (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (l : Linked2) (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (restrict (core3P P) (lime1RT P)) σ)
    (h₀ : σ) (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHostE impl) h₀ (l.toRef.map id) []
      l.imp.exports[j].name (vs.map toRefVal)) :
    Reference.Linked2.IRObs P l j vs b :=
  Hered.Linked2.sound_restrictH (link2SoundH_core3P P) (lime1RT P) prof l hEg hEi hIg hIi har hff
    hW hN hn hS impl h₀ j vs hvs b hb

/-- Soundness of two linked components for sequences of calls over the runtime restriction. -/
theorem Linked2.sound_seq_core3LRG (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (l : Linked2) (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (restrict (core3P P) (lime1RT P)) σ)
    (h₀ : σ) (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHostE impl) h₀ (l.toRef.map id)
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Reference.Linked2.seqMoves l calls wss ∈ l.toComp.den (impSem P) ∧
      Reference.Linked2.SeqIRObs P l calls wss j vs p.2 :=
  Hered.Linked2.sound_seq_restrictH (link2SoundSeqH_core3P P) (lime1RT P) prof l hEg hEi hIg hIi
    har hff hW hN hn hS impl h₀ calls j vs ht hvs p hp

end Silmaril.Wasm.Component.Lime1RT
