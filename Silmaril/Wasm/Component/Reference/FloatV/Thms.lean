module

public import Silmaril.Wasm.Component.Reference.FloatV.Defs
import Silmaril.Proofs.Wasm.Component.Reference.FloatVSound
import Silmaril.Proofs.Wasm.Component.Reference.FloatVSeqSound
import Silmaril.Proofs.Wasm.Component.Reference.LitmusFloatV
import Silmaril.Proofs.Wasm.Component.Reference.FloatVSpecial

/-!
# Floats in variant payloads: theorems

The float soundness theorems of `Reference.Sound.Thms` (`Simple.sound_float`,
`Simple.sound_seq_float`, for floats anywhere except in variant payloads, `SimpleFloatOk`)
extended to floats at every type, without a hypothesis on the types (proved, every silmaril
profile `P` and component choice profile `prof`; axioms `propext`, `Classical.choice`,
`Quot.sound`):

* `Simple.sound_floatV`: every behaviour of the reference machine calling export `j` of
  `c.toRef` on the reference images of well-typed IR values `vs` is the IR observation of the
  call on an admissible lowering `vs'` (`NanAtVList prof`: floats related by `NanLower prof` at
  any depth, variant payloads included), with returned values canonicalised (`IRObsFV`);
* `Simple.sound_floatV_deterministic`: under the deterministic profile `vs'` is
  `canonAtVList params vs`;
* `Simple.sound_seq_floatV`, `Simple.sound_seq_floatV_deterministic`: the same for sequences
  of calls on one instance (`NanCallsV`, `canonResultsV`, `SeqIRObsFV`);
* `nanAtVList_of_nanAtList`, `canonAtVList_eq_canonAtList`: on `floatOk` types (and well-typed
  arguments) the old relations `NanAtList`, `canonAtList` are special cases;
* litmus `Litmus.floatVariantS_sound`, `Litmus.floatVariantS_sound_deterministic`: an `f32`
  payload sharing an `i32` joined slot (two C7 choices on lowering).

The old statements are unchanged. Proof modules: `FloatVSlots`, `FloatVLower`, `FloatVCanon`,
`FloatVLift` (the flat ABI) and `FloatVPath`, `FloatVCall`, `FloatVSound`, `FloatVSeqPath`,
`FloatVSeq`, `FloatVSeqSound` (copies of the float call and sequence proofs with the new
relations).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm.Component (ValTy)

/-- **Soundness with floats at every type** (proved): every behaviour of the reference machine
calling export `j` of `c.toRef` on the reference images of well-typed IR values `vs` is the IR
observation of the call on an admissible lowering `vs'` of `vs`, floats in variant payloads
included, with returned values canonicalised. -/
theorem Simple.sound_floatV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    ∃ vs', NanAtVList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      IRObsFV (k := c.toComp.exports.length) (c.toComp.den (modSem P))
        ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results vs' b :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_floatV P prof c hc hi ha j vs hvs b hb

/-- **Soundness with floats at every type under the deterministic component profile**
(proved): the IR is called on the canonicalisation of the arguments. -/
theorem Simple.sound_floatV_deterministic (P : Profile) (c : Simple) (hc : c.Good)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Outcome)
    (hb : b ∈ exportBehaviours .deterministic (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObsFV (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results
      (canonAtVList c.exports[j].ty.params vs) b :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_floatV_deterministic P c hc hi ha j vs
    hvs b hb

/-- **Soundness for sequences of calls with floats at every type** (proved). -/
theorem Simple.sound_seq_floatV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (calls' : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (vs' : List Silmaril.Wasm.Component.Val),
      NanCallsV prof c calls calls' ∧ TypedCalls c calls' ∧
      NanAtVList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      p.1 = canonResultsV c calls' wss ∧ seqMoves c calls' wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObsFV c (c.toComp.den (modSem P)) calls' wss j vs' p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_seq_floatV P prof c hc hi ha calls j vs
    ht hvs p hp

/-- **Sequences with floats at every type under the deterministic component profile**
(proved): the IR is called on the canonicalised arguments. -/
theorem Simple.sound_seq_floatV_deterministic (P : Profile) (c : Simple) (hc : c.Good)
    (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours .deterministic (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = canonResultsV c (canonCallsV c calls) wss ∧
      seqMoves c (canonCallsV c calls) wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObsFV c (c.toComp.den (modSem P)) (canonCallsV c calls) wss j
        (canonAtVList c.exports[j].ty.params vs) p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_seq_floatV_deterministic P c hc hi ha
    calls j vs ht hvs p hp

/-- **Litmus: an `f32` in a variant payload** (proved): a call of `tag-plus-bits` on `c(x)` is
the IR call on `c(y)` for an admissible lowering `y` of `x`. -/
theorem Litmus.floatVariantS_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x : BitVec 32) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () Litmus.floatVariantS.toRef []
      Litmus.floatVariantS.exports[0].name [toRefVal (.variant 0 (some (.f32 x)))]) :
    ∃ y, NanLower prof .f32 x y ∧
      IRObsFV (k := Litmus.floatVariantS.toComp.exports.length)
        (Litmus.floatVariantS.toComp.den (modSem P)) ⟨0, by decide⟩ [.u32]
        [.variant 0 (some (.f32 y))] b :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.floatVariantS_sound P prof x b hb

/-- **Litmus under the deterministic component profile** (proved). -/
theorem Litmus.floatVariantS_sound_deterministic (P : Profile) (x : BitVec 32) (b : Outcome)
    (hb : b ∈ exportBehaviours .deterministic (refHost P) () Litmus.floatVariantS.toRef []
      Litmus.floatVariantS.exports[0].name [toRefVal (.variant 0 (some (.f32 x)))]) :
    IRObsFV (k := Litmus.floatVariantS.toComp.exports.length)
      (Litmus.floatVariantS.toComp.den (modSem P)) ⟨0, by decide⟩ [.u32]
      [.variant 0 (some (.f32 (Silmaril.Wasm.Component.ABI.canonicalizeNaN .f32 x)))] b :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.floatVariantS_sound_deterministic P x b hb

/-- **`NanAtList` is a special case of `NanAtVList`** (proved) on well-typed values of types
with floats only outside variant payloads. -/
theorem nanAtVList_of_nanAtList {prof : Silmaril.Wasm.Component.ProfileKind} (ts : List ValTy)
    (vs ws : List Silmaril.Wasm.Component.Val) (hf : floatOkList ts = true)
    (hc : ValTy.checkList ts vs = true) (h : NanAtList prof ts vs ws) : NanAtVList prof ts vs ws :=
  Silmaril.Proofs.Wasm.Component.Reference.nanAtVList_of_nanAtList ts vs ws hf hc h

/-- **`canonAtVList` is `canonAtList`** (proved) on types with floats only outside variant
payloads. -/
theorem canonAtVList_eq_canonAtList (ts : List ValTy) (vs : List Silmaril.Wasm.Component.Val)
    (hf : floatOkList ts = true) : canonAtVList ts vs = canonAtList ts vs :=
  Silmaril.Proofs.Wasm.Component.Reference.canonAtVList_eq_canonAtList ts vs hf

end Silmaril.Wasm.Component.Reference
