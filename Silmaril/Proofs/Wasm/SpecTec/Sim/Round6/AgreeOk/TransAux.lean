module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.DGroup
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.Canon

/-!
# Round 6: the motives of the transcription, and its bounded parts

The transcription of canonical derivations (`Trans.lean`) reads every judgment of `TyOkB`/`SubB`
at a context `Δ` (whose `TYPES` are ignored) in the SpecTec context `ctxOf Δ`, the empty context
with `RECS` the images of `Δ.recs`. Its motives `OkD` and `SubD` name the relation each sort is
read by (`Heaptype_ok`, …, `Comptype_sub`), and read sequences pointwise. This file has the
bookkeeping: bounds of the parts of bounded types, the images of composite types, and pointwise
relations over sequences.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_list natV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.AgreeSub (CtxT)
open Round4 (tyBnd)

/-! ## Contexts -/

/-- The SpecTec context of `Δ`: the empty context with `RECS` the images of `Δ.recs`. -/
def ctxOf (Δ : TypeCtx) : Value := RefOkB.ctxR (Δ.recs.map tyV)

/-- Every `RECS` entry of `Δ` is bounded. -/
def RecsBnd (Δ : TypeCtx) : Prop := ∀ st ∈ Δ.recs, tyBnd st = true

/-- `ctxOf Δ` is a typed context when `Δ`'s `RECS` are bounded. -/
theorem ctxT_of {B : Builtins} {Δ : TypeCtx} (h : RecsBnd Δ) : CtxT B (ctxOf Δ) :=
  RefOkB.typedV_ctxR fun w hw => by
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hw
    exact Round5.Pos.tyT_tyV st (h st hst)

/-- `RECS` lookups, at the images. -/
theorem recs_map {Δ : TypeCtx} {i : Nat} {st : CSubType} (h : Δ.recs[i]? = some st) :
    (Δ.recs.map tyV)[i]? = some (tyV st) := by
  simp [h]

/-- A `RECS` entry of a bounded context is bounded. -/
theorem RecsBnd.get {Δ : TypeCtx} (hR : RecsBnd Δ) {i : Nat} {st : CSubType}
    (h : Δ.recs[i]? = some st) : tyBnd st = true :=
  hR st (List.mem_of_getElem? h)

/-- A group's own context, at the images. -/
theorem ctxOf_withRecsA (Δ : TypeCtx) (sts : List CSubType) :
    ctxOf (RefOkV.withRecsA Δ sts) = RefOkB.ctxR (sts.map tyV ++ Δ.recs.map tyV) := by
  simp [ctxOf, RefOkV.withRecsA]

/-- A bounded group's context is bounded. -/
theorem RecsBnd.withRecsA {Δ : TypeCtx} (hR : RecsBnd Δ) {subs : Ty (.list .sub)}
    (hb : tyBnd subs = true) : RecsBnd (RefOkV.withRecsA Δ subs.toList) := by
  intro st hst
  rcases List.mem_append.1 hst with h | h
  · exact Round5.Fwd.tyBnd_of_mem hb h
  · exact hR st h

/-! ## Bounds -/

/-- A sequence is bounded when its elements are. -/
theorem tyBnd_list_iff {k : TKind} (l : Ty (.list k)) :
    tyBnd l = true ↔ ∀ a ∈ l.toList, tyBnd a = true := by
  rw [← Ty.ofList_toList l]
  generalize l.toList = L
  induction L with
  | nil => simp [tyBnd]
  | cons b L ih => simp [tyBnd, ih]

/-- The parts of a bounded `REC` with a first member. -/
theorem tyBnd_groupCons {st : CSubType} {sts : Ty (.list .sub)}
    (h : tyBnd (Ty.group (.cons st sts) : CRecType) = true) :
    tyBnd st = true ∧ tyBnd (Ty.group sts : CRecType) = true := by
  have h' := Round5.Pos.tyBnd_group.1 h
  have hc := tyBnd_cons_iff.1 h'.2
  refine ⟨hc.1, Round5.Pos.tyBnd_group.2 ⟨?_, hc.2⟩⟩
  have := h'.1
  simp only [Ty.toList_cons, List.length_cons] at this
  omega

/-- The prefix of a bounded `STRUCT` is bounded. -/
theorem tyBnd_structApp {fs extra : Ty (.list .field)}
    (h : tyBnd (Ty.struct (fs.app extra)) = true) :
    tyBnd fs = true ∧ tyBnd extra = true := by
  have hl := (tyBnd_list_iff _).1 (tyBnd_struct' h)
  simp only [Ty.app, Ty.toList_ofList, List.mem_append] at hl
  exact ⟨(tyBnd_list_iff _).2 fun a ha => hl a (.inl ha),
    (tyBnd_list_iff _).2 fun a ha => hl a (.inr ha)⟩

/-- A declared supertype of a bounded defined type is bounded. -/
theorem tyBnd_superOf {d : DefType} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    {j : Nat} {u : CTypeUse} (hd : tyBnd d = true) (h : unrolldt d = some (.sub fin sups ct))
    (hj : sups.toList[j]? = some u) : tyBnd u = true :=
  Round5.Fwd.tyBnd_of_mem (Round5.Fwd.tyBnd_of_unrolldt hd h).1 (List.mem_of_getElem? hj)

/-- The unrolling of a canonically valid type use is bounded, in a bounded context. -/
theorem tyBnd_unrollUse {Δ Δ' : TypeCtx} (hR : RecsBnd Δ) {u : CTypeUse} {st : CSubType}
    (hok : TyOkB Δ' u) (hu : tyBnd u = true) (h : Δ.unrollUse u = some st) : tyBnd st = true := by
  cases u with
  | recv i => exact hR.get h
  | dt d => exact Round5.Fwd.tyBnd_unrolldt hu h
  | idx x => exact absurd hok TyOkB.not_idx

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
