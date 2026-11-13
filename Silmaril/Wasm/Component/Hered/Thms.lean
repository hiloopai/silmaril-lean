module

public import Silmaril.Wasm.Component.Hered.Defs
public import Silmaril.Wasm.Component.Param.Thms

/-!
# Hereditary soundness properties of a core engine: theorems

* `withRel_self`, `restrict_eq_withRel`, `withRel_withRel`: `E`, `restrict E r` and iterated
  changes of `E` are instances of `withRel E` (all `rfl`);
* `RefToSpecH.refToSpec` (and siblings): the hereditary properties imply the plain ones;
* `RefToSpecH.restrict`, `RefToSpecH.withRel` (and siblings): they are closed under
  restriction and under shrinking the internal step. This is the formulation of "`RefToSpec`
  passes to restrictions" that holds for an **abstract** engine; the plain implication
  `RefToSpec E → RefToSpec (restrict E r)` stays unproved (see `Hered.Defs`);
* `refToSpecH_core3P`, `seqRefToSpecH_core3P`, `link2SoundH_core3P`, `link2SoundSeqH_core3P`:
  the Core 3.0 engine has all four at every profile. These are the `core3R` theorems of Tracks
  I4/I5 read through `withRel (core3P P) = core3R P` (definitionally);
* `Simple.sound_restrictH`, `Simple.sound_seq_restrictH`, `Linked2.sound_restrictH`,
  `Linked2.sound_seq_restrictH`: soundness of the IR (over `modSem P` / `impSem P`) for the
  reference machine over **any restriction of any engine** with the hereditary properties.
  The Core 3.0 restriction theorems of `Param.Thms` are the instance `E := core3P P`
  (`Simple.sound_restrict_core3P'`).

New statements; the proofs are one-liners over `Param`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Hered

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

section Generic

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]
  {ofCore : Silmaril.Wasm.Module → E.Module} {P : Profile}

/-! ## `withRel` -/

theorem withRel_self (E : Engine) : withRel E E.Valid E.Internal = E := rfl

theorem restrict_eq_withRel (E : Engine) (r : Restriction E) :
    restrict E r = withRel E (fun m => E.Valid m ∧ r.Mod m)
      (fun c c' => E.Internal c c' ∧ r.Rt c') := rfl

theorem withRel_withRel (E : Engine) (V V' : E.Module → Prop)
    (IR IR' : {H : Type} → E.Config H → E.Config H → Prop) :
    withRel (withRel E V IR) V' IR' = withRel E V' IR' := rfl

theorem subRel_refl (E : Engine) : SubRel E E.Internal := fun h => h

theorem SubRel.trans {E : Engine} {V : E.Module → Prop}
    {IR IR' : {H : Type} → E.Config H → E.Config H → Prop} (h : SubRel E IR)
    (h' : SubRel (withRel E V IR) IR') : SubRel E IR' := fun x => h (h' x)

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The internal step of a restriction is contained in the engine's. -/
theorem subRel_restrict (r : Restriction E) :
    SubRel E (fun c c' => E.Internal c c' ∧ r.Rt c') := fun h => h.1

/-! ## The hereditary properties imply the plain ones -/

theorem RefToSpecH.refToSpec (h : RefToSpecH E ofCore P) : RefToSpec E ofCore P :=
  h E.Valid E.Internal (subRel_refl E)

theorem SeqRefToSpecH.seqRefToSpec (h : SeqRefToSpecH E ofCore P) :
    SeqRefToSpec E ofCore P :=
  h E.Valid E.Internal (subRel_refl E)

theorem Link2SoundH.link2Sound (h : Link2SoundH E ofCore P) : Link2Sound E ofCore P :=
  h E.Valid E.Internal (subRel_refl E)

theorem Link2SoundSeqH.link2SoundSeq (h : Link2SoundSeqH E ofCore P) :
    Link2SoundSeq E ofCore P :=
  h E.Valid E.Internal (subRel_refl E)

/-! ## Closure under shrinking the internal step and under restriction -/

theorem RefToSpecH.withRel (h : RefToSpecH E ofCore P) {V : E.Module → Prop}
    {IR : {H : Type} → E.Config H → E.Config H → Prop} (hIR : SubRel E IR) :
    RefToSpecH (Hered.withRel E V IR) ofCore P :=
  fun V' _ hIR' => h V' _ (hIR.trans hIR')

theorem SeqRefToSpecH.withRel (h : SeqRefToSpecH E ofCore P) {V : E.Module → Prop}
    {IR : {H : Type} → E.Config H → E.Config H → Prop} (hIR : SubRel E IR) :
    SeqRefToSpecH (Hered.withRel E V IR) ofCore P :=
  fun V' _ hIR' => h V' _ (hIR.trans hIR')

theorem Link2SoundH.withRel (h : Link2SoundH E ofCore P) {V : E.Module → Prop}
    {IR : {H : Type} → E.Config H → E.Config H → Prop} (hIR : SubRel E IR) :
    Link2SoundH (Hered.withRel E V IR) ofCore P :=
  fun V' _ hIR' => h V' _ (hIR.trans hIR')

theorem Link2SoundSeqH.withRel (h : Link2SoundSeqH E ofCore P) {V : E.Module → Prop}
    {IR : {H : Type} → E.Config H → E.Config H → Prop} (hIR : SubRel E IR) :
    Link2SoundSeqH (Hered.withRel E V IR) ofCore P :=
  fun V' _ hIR' => h V' _ (hIR.trans hIR')

/-- **The hereditary reference-machine half passes to every restriction.** -/
theorem RefToSpecH.restrict (h : RefToSpecH E ofCore P) (r : Restriction E) :
    RefToSpecH (Param.restrict E r) ofCore P :=
  h.withRel (subRel_restrict r)

theorem SeqRefToSpecH.restrict (h : SeqRefToSpecH E ofCore P) (r : Restriction E) :
    SeqRefToSpecH (Param.restrict E r) ofCore P :=
  h.withRel (subRel_restrict r)

theorem Link2SoundH.restrict (h : Link2SoundH E ofCore P) (r : Restriction E) :
    Link2SoundH (Param.restrict E r) ofCore P :=
  h.withRel (subRel_restrict r)

theorem Link2SoundSeqH.restrict (h : Link2SoundSeqH E ofCore P) (r : Restriction E) :
    Link2SoundSeqH (Param.restrict E r) ofCore P :=
  h.withRel (subRel_restrict r)

/-- **Every restriction of an engine with the hereditary half has the reference-machine half**:
the formulation of "`RefToSpec` passes to restrictions" for an abstract engine. -/
theorem refToSpec_restrict (h : RefToSpecH E ofCore P) (r : Restriction E) :
    RefToSpec (Param.restrict E r) ofCore P :=
  (h.restrict r).refToSpec

theorem seqRefToSpec_restrict (h : SeqRefToSpecH E ofCore P) (r : Restriction E) :
    SeqRefToSpec (Param.restrict E r) ofCore P :=
  (h.restrict r).seqRefToSpec

theorem link2Sound_restrict (h : Link2SoundH E ofCore P) (r : Restriction E) :
    Link2Sound (Param.restrict E r) ofCore P :=
  (h.restrict r).link2Sound

theorem link2SoundSeq_restrict (h : Link2SoundSeqH E ofCore P) (r : Restriction E) :
    Link2SoundSeq (Param.restrict E r) ofCore P :=
  (h.restrict r).link2SoundSeq

/-! ## Soundness over restrictions of an abstract engine -/

/-- **Soundness of the IR for the reference machine over any restriction of an engine with the
hereditary reference-machine half.** -/
theorem Simple.sound_restrictH (hR : RefToSpecH E ofCore P) (r : Restriction E)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (Param.restrict E r)) () (c.toRef.map ofCore) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Silmaril.Proofs.Wasm.Component.Param.Simple.soundE (refToSpec_restrict hR r) prof c hc hf hi ha
    j vs hvs b hb

/-- **Soundness of the IR for sequences of calls over any restriction of an engine with the
hereditary sequence half.** -/
theorem Simple.sound_seq_restrictH (hR : SeqRefToSpecH E ofCore P) (r : Restriction E)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHostE (Param.restrict E r)) () (c.toRef.map ofCore)
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs p.2 :=
  Silmaril.Proofs.Wasm.Component.Param.Simple.sound_seqE (seqRefToSpec_restrict hR r) prof c hc hf
    hi ha calls j vs ht hvs p hp

/-- **Soundness of two linked components over any restriction of an engine with hereditary
linked soundness.** -/
theorem Linked2.sound_restrictH (hR : Link2SoundH E ofCore P) (r : Restriction E)
    (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (Param.restrict E r) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHostE impl) h₀ (l.toRef.map ofCore) []
      l.imp.exports[j].name (vs.map toRefVal)) :
    Reference.Linked2.IRObs P l j vs b :=
  Silmaril.Proofs.Wasm.Component.Param.Linked2.soundE (link2Sound_restrict hR r) prof l hEg hEi
    hIg hIi har hff hW hN hn hS impl h₀ j vs hvs b hb

/-- **Soundness of two linked components for sequences of calls over any restriction of an
engine with hereditary linked soundness for sequences.** -/
theorem Linked2.sound_seq_restrictH (hR : Link2SoundSeqH E ofCore P) (r : Restriction E)
    (prof : Silmaril.Wasm.Component.ProfileKind) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (Param.restrict E r) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHostE impl) h₀ (l.toRef.map ofCore)
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Reference.Linked2.seqMoves l calls wss ∈ l.toComp.den (impSem P) ∧
      Reference.Linked2.SeqIRObs P l calls wss j vs p.2 :=
  Silmaril.Proofs.Wasm.Component.Param.Linked2.sound_seqE (link2SoundSeq_restrict hR r) prof l hEg
    hEi hIg hIi har hff hW hN hn hS impl h₀ calls j vs ht hvs p hp

end Generic

/-! ## Core 3.0 has the hereditary properties -/

theorem withRel_core3P (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H →
      Silmaril.Proofs.Wasm.Component.Param.Core3R.Cfg3 H → Prop) :
    withRel (core3P P) V IR = Silmaril.Proofs.Wasm.Component.Param.Core3R.core3R P V IR := rfl

/-- **Core 3.0 has the hereditary reference-machine half at every profile.** -/
theorem refToSpecH_core3P (P : Profile) : RefToSpecH (core3P P) id P :=
  fun V IR hIR => refToSpec_core3R P V IR hIR

theorem seqRefToSpecH_core3P (P : Profile) : SeqRefToSpecH (core3P P) id P :=
  fun V IR hIR => seqRefToSpec_core3R P V IR hIR

theorem link2SoundH_core3P (P : Profile) : Link2SoundH (core3P P) id P :=
  fun V IR hIR => link2Sound_core3R P V IR hIR

theorem link2SoundSeqH_core3P (P : Profile) : Link2SoundSeqH (core3P P) id P :=
  fun V IR hIR => link2SoundSeq_core3R P V IR hIR

/-- The I4 theorem `Param.refToSpec_restrict_core3P` is the instance `E := core3P P` of the
generic `refToSpec_restrict`. -/
theorem refToSpec_restrict_core3P' (P : Profile) (r : Restriction (core3P P)) :
    RefToSpec (Param.restrict (core3P P) r) id P :=
  refToSpec_restrict (refToSpecH_core3P P) r

/-- Restrictions of restrictions of Core 3.0 (for example a profile inside Lime1) are sound:
the hereditary half passes through any number of restrictions. -/
theorem refToSpecH_restrict_restrict_core3P (P : Profile) (r : Restriction (core3P P))
    (r' : Restriction (Param.restrict (core3P P) r)) :
    RefToSpecH (Param.restrict (Param.restrict (core3P P) r) r') id P :=
  ((refToSpecH_core3P P).restrict r).restrict r'

end Silmaril.Wasm.Component.Hered
