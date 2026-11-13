module

public import Silmaril.Wasm.Component.Param.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Restrict
public import Silmaril.Proofs.Wasm.Component.Param.Sound
public import Silmaril.Proofs.Wasm.Component.Param.SpecToIR
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Sound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Seq
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.LinkSound

/-!
# The Component Model parametrized by a core engine: theorems

All proved; proofs in `Silmaril.Proofs.Wasm.Component.Param`.

**Restrictions** (`restrict E r`):

* `restrict_lawful`, `restrict_resumeLawful`: the engine laws pass to restrictions;
* `steps_restrict`: from a configuration of the runtime invariant, closed under internal steps,
  the engine's runs are restricted runs;
* `engineStrategy_restrict_le` (always) and `engineStrategy_restrict_eq` (for an instance that
  respects the restriction): the game semantics of a restricted instance;
* `engineSem_restrict_le`, `den_restrict_le`: the core semantics of the IR and the denotation of
  every component over a restriction refine those over the engine.

**Soundness over an engine** (the fallback of `docs/projects/spectec/README.md` §3: the reference-machine
half is a property of the engine):

* `refToSpec_core3P`, `seqRefToSpec_core3P`, `link2Sound_core3P`, `link2SoundSeq_core3P`: the
  Core 3.0 engine at every profile has the four properties;
* `Simple.soundE`, `Simple.sound_seqE`, `Linked2.soundE`, `Linked2.sound_seqE`: soundness of the
  IR (over `modSem P` / `impSem P`) for every engine with the properties;
* `Simple.sound_core3P`, `Simple.sound_seq_core3P`: `Reference.Simple.sound` and
  `Reference.Simple.sound_seq` recovered as instances (the old statements are kept);
* `refToSpec_restrict_core3P`: every restriction `restrict (core3P P) r` of the Core 3.0 engine
  has the reference-machine half, hence `Simple.sound_restrict_core3P`: soundness of the IR
  over `modSem P` for the reference machine over the restricted engine. Proof: the
  `core3P`-specific phases of `refToSpec_of_arity` re-run over `core3R P V IR` (Core 3.0 with
  validity `V` and an internal step `IR` contained in `InternalP P`, `refToSpec_core3R`), of
  which `restrict (core3P P) r` is an instance by definition; likewise for sequences of calls
  (`seqRefToSpec_core3R`, `seqRefToSpec_restrict_core3P`, `Simple.sound_seq_restrict_core3P`);
* `link2Sound_restrict_core3P`, `link2SoundSeq_restrict_core3P`: every restriction of the Core
  3.0 engine has soundness of two linked components, for single calls and for sequences of calls
  (through `link2Sound_core3R`, `link2SoundSeq_core3R`: the linked-soundness chain re-run over
  `core3R P V IR`), hence `Linked2.sound_restrict_core3P` and `Linked2.sound_seq_restrict_core3P`:
  soundness of the linked IR over `impSem P` for the reference machine over the restricted engine;
* `specToIRE`: the IR half over the game semantics of **any** engine: terminating outcomes of
  the engine's canonical-ABI specification `exportSpecE` are plays of the IR over
  `engineSem E NumModule emb`; `Simple.soundG`: soundness over `engineSem` from `RefToSpecE`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-! ## Restrictions -/

section Restrict

variable {E : Engine} {r : Restriction E}

/-- The laws of an engine pass to its restrictions. -/
theorem restrict_lawful [E.Lawful] : (restrict E r).Lawful :=
  Silmaril.Proofs.Wasm.Component.Param.restrict_lawful

/-- Resumption progress passes to restrictions. -/
theorem restrict_resumeLawful [E.ResumeLawful] : (restrict E r).ResumeLawful :=
  Silmaril.Proofs.Wasm.Component.Param.restrict_resumeLawful

/-- From a configuration of a closed runtime invariant, runs of the engine are restricted runs. -/
theorem steps_restrict (hc : r.Closed) {H : Type} {c c' : E.Config H} (h0 : r.Rt c)
    (h : Silmaril.Wasm.Component.Engine.CoreEngine.Steps E c c') :
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps (restrict E r) c c' ∧ r.Rt c' :=
  Silmaril.Proofs.Wasm.Component.Param.steps_restrict hc h0 h

/-- **The game semantics of a restricted instance refines the engine's.** -/
theorem engineStrategy_restrict_le (I : EInstance E) (imps exps : CoreIface) :
    engineStrategy (restrict E r) I.res imps exps ≤ engineStrategy E I imps exps :=
  Silmaril.Proofs.Wasm.Component.Param.engineStrategy_restrict_le I imps exps

/-- **An instance that respects a restriction has the game semantics of the restricted
instance.** -/
theorem engineStrategy_restrict_eq {I : EInstance E} {Sto : E.Store Nat → Prop}
    (hR : Silmaril.Proofs.Wasm.Component.Param.Respects r I Sto) (imps exps : CoreIface) :
    engineStrategy (restrict E r) I.res imps exps = engineStrategy E I imps exps :=
  Silmaril.Proofs.Wasm.Component.Param.engineStrategy_restrict_eq hR imps exps

/-- **The core semantics of a restriction refines the engine's.** -/
theorem engineSem_restrict_le (M : Type) [CoreModule M] (emb : M → E.Module) :
    (engineSem (restrict E r) M emb).Le (engineSem E M emb) :=
  Silmaril.Proofs.Wasm.Component.Param.engineSem_restrict_le M emb

/-- **Every component over a restriction refines the component over the engine.** -/
theorem den_restrict_le {M : Type} [CoreModule M] (emb : M → E.Module) (c : Comp M) :
    c.den (engineSem (restrict E r) M emb) ≤ c.den (engineSem E M emb) :=
  Strategy.comp_mono (Strategy.comp_mono le_rfl (denU_mono (engineSem_restrict_le M emb) c)) le_rfl

end Restrict

/-! ## Soundness over an engine -/

/-- The Core 3.0 engine has the reference-machine half. -/
theorem refToSpec_core3P (P : Profile) : RefToSpec (core3P P) id P :=
  Silmaril.Proofs.Wasm.Component.Param.refToSpec_core3P P

/-- The Core 3.0 engine has the reference-machine half for sequences of calls. -/
theorem seqRefToSpec_core3P (P : Profile) : SeqRefToSpec (core3P P) id P :=
  Silmaril.Proofs.Wasm.Component.Param.seqRefToSpec_core3P P

/-- The Core 3.0 engine has soundness of two linked components. -/
theorem link2Sound_core3P (P : Profile) : Link2Sound (core3P P) id P :=
  Silmaril.Proofs.Wasm.Component.Param.link2Sound_core3P P

/-- The Core 3.0 engine has soundness of two linked components for sequences of calls. -/
theorem link2SoundSeq_core3P (P : Profile) : Link2SoundSeq (core3P P) id P :=
  Silmaril.Proofs.Wasm.Component.Param.link2SoundSeq_core3P P

/-! ## Restrictions of the Core 3.0 engine -/

/-- **The reference-machine half over Core 3.0 with a smaller internal step**: `core3R P V IR`
is `core3P P` with validity `V` and internal step `IR`; when `IR` is contained in `InternalP P`
it has the reference-machine half. -/
theorem refToSpec_core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H →
      Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H → Prop)
    (hIR : Silmaril.Proofs.Wasm.Component.Param.Core3R.Sub P IR) :
    RefToSpec (Silmaril.Proofs.Wasm.Component.Param.Core3R.core3R P V IR) id P :=
  Silmaril.Proofs.Wasm.Component.Param.Core3R.refToSpec_core3R P V IR hIR

/-- **Every restriction of the Core 3.0 engine has the reference-machine half.** -/
theorem refToSpec_restrict_core3P (P : Profile) (r : Restriction (core3P P)) :
    RefToSpec (restrict (core3P P) r) id P :=
  Silmaril.Proofs.Wasm.Component.Param.Core3R.refToSpec_restrict_core3P P r

/-- **Soundness of the IR for the reference machine over a restriction of Core 3.0**: every
behaviour of calling export `j` of `c.toRef` over `restrict (core3P P) r` is matched by the IR
denotation over `modSem P`. -/
theorem Simple.sound_restrict_core3P (P : Profile) (r : Restriction (core3P P))
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (restrict (core3P P) r)) () (c.toRef.map id) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Silmaril.Proofs.Wasm.Component.Param.Simple.soundE (refToSpec_restrict_core3P P r) prof c hc hf
    hi ha j vs hvs b hb

/-- **The sequence half over Core 3.0 with a smaller internal step.** -/
theorem seqRefToSpec_core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H →
      Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H → Prop)
    (hIR : Silmaril.Proofs.Wasm.Component.Param.Core3R.Sub P IR) :
    SeqRefToSpec (Silmaril.Proofs.Wasm.Component.Param.Core3R.core3R P V IR) id P :=
  Silmaril.Proofs.Wasm.Component.Param.Core3R.seqRefToSpec_core3R P V IR hIR

/-- **Every restriction of the Core 3.0 engine has the sequence half.** -/
theorem seqRefToSpec_restrict_core3P (P : Profile) (r : Restriction (core3P P)) :
    SeqRefToSpec (restrict (core3P P) r) id P :=
  Silmaril.Proofs.Wasm.Component.Param.Core3R.seqRefToSpec_restrict_core3P P r

/-- **Soundness of the IR for sequences of calls over a restriction of Core 3.0.** -/
theorem Simple.sound_seq_restrict_core3P (P : Profile) (r : Restriction (core3P P))
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHostE (restrict (core3P P) r)) () (c.toRef.map id)
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs p.2 :=
  Silmaril.Proofs.Wasm.Component.Param.Simple.sound_seqE (seqRefToSpec_restrict_core3P P r) prof c
    hc hf hi ha calls j vs ht hvs p hp

/-! ## Linked components over restrictions of the Core 3.0 engine -/

/-- **Soundness of two linked components over Core 3.0 with a smaller internal step.** -/
theorem link2Sound_core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H →
      Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H → Prop)
    (hIR : Silmaril.Proofs.Wasm.Component.Param.Core3R.Sub P IR) :
    Link2Sound (Silmaril.Proofs.Wasm.Component.Param.Core3R.core3R P V IR) id P :=
  Silmaril.Proofs.Wasm.Component.Param.Core3R.link2Sound_core3R P V IR hIR

/-- **Soundness of two linked components for sequences of calls over Core 3.0 with a smaller
internal step.** -/
theorem link2SoundSeq_core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H →
      Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H → Prop)
    (hIR : Silmaril.Proofs.Wasm.Component.Param.Core3R.Sub P IR) :
    Link2SoundSeq (Silmaril.Proofs.Wasm.Component.Param.Core3R.core3R P V IR) id P :=
  Silmaril.Proofs.Wasm.Component.Param.Core3R.link2SoundSeq_core3R P V IR hIR

/-- **Every restriction of the Core 3.0 engine has soundness of two linked components.** -/
theorem link2Sound_restrict_core3P (P : Profile) (r : Restriction (core3P P)) :
    Link2Sound (restrict (core3P P) r) id P :=
  Silmaril.Proofs.Wasm.Component.Param.Core3R.link2Sound_restrict_core3P P r

/-- **Every restriction of the Core 3.0 engine has soundness of two linked components for
sequences of calls.** -/
theorem link2SoundSeq_restrict_core3P (P : Profile) (r : Restriction (core3P P)) :
    Link2SoundSeq (restrict (core3P P) r) id P :=
  Silmaril.Proofs.Wasm.Component.Param.Core3R.link2SoundSeq_restrict_core3P P r

/-- **Soundness of two linked components over a restriction of Core 3.0**: every behaviour of
instantiating `l.toRef` over `restrict (core3P P) r` and calling the importer's export `j`,
under host functions `impl`, is matched by the linked IR denotation over `impSem P`. -/
theorem Linked2.sound_restrict_core3P (P : Profile) (r : Restriction (core3P P))
    (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (restrict (core3P P) r) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHostE impl) h₀ (l.toRef.map id) []
      l.imp.exports[j].name (vs.map toRefVal)) :
    Linked2.IRObs P l j vs b :=
  Silmaril.Proofs.Wasm.Component.Param.Linked2.soundE (link2Sound_restrict_core3P P r) prof l hEg
    hEi hIg hIi har hff hW hN hn hS impl h₀ j vs hvs b hb

/-- **Soundness of two linked components for sequences of calls over a restriction of Core
3.0.** -/
theorem Linked2.sound_seq_restrict_core3P (P : Profile) (r : Restriction (core3P P))
    (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (restrict (core3P P) r) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHostE impl) h₀ (l.toRef.map id)
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Linked2.seqMoves l calls wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObs P l calls wss j vs p.2 :=
  Silmaril.Proofs.Wasm.Component.Param.Linked2.sound_seqE (link2SoundSeq_restrict_core3P P r) prof
    l hEg hEi hIg hIi har hff hW hN hn hS impl h₀ calls j vs ht hvs p hp

end Silmaril.Wasm.Component.Param
