module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatCall
public import Silmaril.Proofs.Wasm.Component.Reference.InstRun
public import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR
public import Silmaril.Proofs.Wasm.Component.Reference.RefToSpec

/-!
# Soundness of the component IR with floats

Without `Simple.FloatFree` the reference machine and the IR differ in their treatment of NaNs:
lowering an argument NaN may choose another NaN (C7, admissible answers `NanLower prof`), and
lifting a result canonicalises NaNs. Core code can observe NaN payloads, so the reference call
is not the IR call on the same arguments. The precise relation (`Simple.sound_float`), for
floats anywhere except in variant payloads (`SimpleFloatOk`): every behaviour of the reference
machine calling export `j` on `vs.map toRefVal` is an IR observation of the call on **some**
admissible lowering `vs'` of `vs` (`NanAtList prof ts vs vs'`), whose returned values `ws` the
reference reports **canonicalised** (`canonAtList`):

* returned results `rs`: `rs = (canonAtList results ws).map toRefVal` and the IR plays
  `ask (j, vals vs') · ans (vals ws)`;
* a trap: the IR plays `ask (j, vals vs') · ans none`.

Under the deterministic component profile the admissible lowering is unique, the
canonicalisation of the arguments (`nanAtList_deterministic`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## `toRefVal` is injective -/

mutual
/-- The IR value of a reference value in the image of `toRefVal`. -/
def ofRefVal : Silmaril.Wasm.Component.Value.Val → Option IVal
  | .bool b => some (.bool b)
  | .int .s8 n => some (.s8 (BitVec.ofInt 8 n))
  | .int .u8 n => some (.u8 (BitVec.ofInt 8 n))
  | .int .s16 n => some (.s16 (BitVec.ofInt 16 n))
  | .int .u16 n => some (.u16 (BitVec.ofInt 16 n))
  | .int .s32 n => some (.s32 (BitVec.ofInt 32 n))
  | .int .u32 n => some (.u32 (BitVec.ofInt 32 n))
  | .int .s64 n => some (.s64 (BitVec.ofInt 64 n))
  | .int .u64 n => some (.u64 (BitVec.ofInt 64 n))
  | .f32 b => some (.f32 b)
  | .f64 b => some (.f64 b)
  | .char c => some (.char c)
  | .record vs => (ofRefVals vs).map .record
  | .variant i p => (ofRefOpt p).map (.variant i)
  | _ => none

/-- `ofRefVal` on lists. -/
def ofRefVals : List Silmaril.Wasm.Component.Value.Val → Option (List IVal)
  | [] => some []
  | v :: vs => (ofRefVal v).bind fun w => (ofRefVals vs).map (w :: ·)

/-- `ofRefVal` on options. -/
def ofRefOpt : Option Silmaril.Wasm.Component.Value.Val → Option (Option IVal)
  | none => some none
  | some v => (ofRefVal v).map some
end

mutual
/-- `ofRefVal` inverts `toRefVal`. -/
theorem ofRefVal_toRefVal : ∀ v : IVal, ofRefVal (toRefVal v) = some v
  | .bool _ | .f32 _ | .f64 _ | .char _ => rfl
  | .s8 x | .s16 x | .s32 x | .s64 x => by
    simp only [toRefVal, ofRefVal, BitVec.ofInt_toInt]
  | .u8 x | .u16 x | .u32 x | .u64 x => by
    simp only [toRefVal, ofRefVal, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | .record vs => by simp only [toRefVal, ofRefVal, ofRefVals_toRefVals vs, Option.map_some]
  | .variant i p => by simp only [toRefVal, ofRefVal, ofRefOpt_toRefOpt p, Option.map_some]

/-- `ofRefVals` inverts `toRefVals`. -/
theorem ofRefVals_toRefVals : ∀ vs : List IVal, ofRefVals (toRefVals vs) = some vs
  | [] => rfl
  | v :: vs => by
    simp only [toRefVals, ofRefVals, ofRefVal_toRefVal v, ofRefVals_toRefVals vs,
      Option.bind_some, Option.map_some]

/-- `ofRefOpt` inverts `toRefOpt`. -/
theorem ofRefOpt_toRefOpt : ∀ p : Option IVal, ofRefOpt (toRefOpt p) = some p
  | none => rfl
  | some v => by simp only [toRefOpt, ofRefOpt, ofRefVal_toRefVal v, Option.map_some]
end

/-- **`toRefVal` is injective** on lists. -/
theorem map_toRefVal_inj {ws ws' : List IVal} (h : ws.map toRefVal = ws'.map toRefVal) :
    ws = ws' := by
  have e : ofRefVals (toRefVals ws) = ofRefVals (toRefVals ws') := by
    rw [toRefVals_eq, toRefVals_eq, h]
  rw [ofRefVals_toRefVals, ofRefVals_toRefVals] at e
  exact Option.some.inj e

/-! ## From the canonicalised specification to the IR -/

export Silmaril.Wasm.Component.Reference (IRObsF)

/-- An outcome of `liftOutcomeF` is the canonicalisation of the outcome of `liftOutcome`. -/
theorem liftOutcomeF_cases (ft : FuncTy) (r : Option (List Flat)) :
    (liftOutcomeF ft r = .traps ∧ liftOutcome ft r = .traps) ∨
      ∃ ws, liftOutcomeF ft r = .returns (some ((canonAtList ft.results ws).map toRefVal)) ∧
        liftOutcome ft r = .returns (some (ws.map toRefVal)) := by
  cases r with
  | none => exact .inl ⟨rfl, rfl⟩
  | some ys =>
    cases h : liftArgs ft.results ys with
    | none => exact .inl ⟨by simp only [liftOutcomeF, h], by simp only [liftOutcome, h]⟩
    | some ws => exact .inr ⟨ws, by simp only [liftOutcomeF, h], by simp only [liftOutcome, h]⟩

section Mem

variable {P : Profile} {c : Simple} {x : SimpleExport} {vs : List IVal}
  {b : Silmaril.Wasm.Component.Reference.Outcome}

theorem mem_exportSpecF_none (hl : checkLower x.ty.params vs = none) :
    b ∈ exportSpecF P c x vs ↔ b = .traps := by
  unfold exportSpecF
  rw [hl]
  rfl

theorem mem_exportSpec_none (hl : checkLower x.ty.params vs = none) :
    b ∈ exportSpec P c x vs ↔ b = .traps := by
  unfold exportSpec
  rw [hl]
  rfl

theorem mem_exportSpecF_some {xs : List Flat} (hl : checkLower x.ty.params vs = some xs) :
    b ∈ exportSpecF P c x vs ↔ (∃ r ∈ coreOut P c.mod x.core xs, b = liftOutcomeF x.ty r) ∨
      (b = .diverges ∧ coreDiverges P c.mod x.core xs) := by
  unfold exportSpecF
  rw [hl]
  rfl

theorem mem_exportSpec_some {xs : List Flat} (hl : checkLower x.ty.params vs = some xs) :
    b ∈ exportSpec P c x vs ↔ (∃ r ∈ coreOut P c.mod x.core xs, b = liftOutcome x.ty r) ∨
      (b = .diverges ∧ coreDiverges P c.mod x.core xs) := by
  unfold exportSpec
  rw [hl]
  rfl

end Mem

/-- **`exportSpecF` is `exportSpec` with canonicalised results.** -/
theorem exportSpecF_cases {P : Profile} {c : Simple} {x : SimpleExport} {vs : List IVal}
    {b : Silmaril.Wasm.Component.Reference.Outcome} (hb : b ∈ exportSpecF P c x vs) :
    (b = .traps ∧ .traps ∈ exportSpec P c x vs) ∨ b = .diverges ∨
      ∃ ws, b = .returns (some ((canonAtList x.ty.results ws).map toRefVal)) ∧
        .returns (some (ws.map toRefVal)) ∈ exportSpec P c x vs := by
  cases hl : checkLower x.ty.params vs with
  | none => exact .inl ⟨(mem_exportSpecF_none hl).mp hb, (mem_exportSpec_none hl).mpr rfl⟩
  | some xs =>
    have hb' : (∃ r ∈ coreOut P c.mod x.core xs, b = liftOutcomeF x.ty r) ∨
        (b = .diverges ∧ coreDiverges P c.mod x.core xs) := (mem_exportSpecF_some hl).mp hb
    have hs : ∀ b', (∃ r ∈ coreOut P c.mod x.core xs, b' = liftOutcome x.ty r) →
        b' ∈ exportSpec P c x vs := fun b' h => (mem_exportSpec_some hl).mpr (.inl h)
    rcases hb' with ⟨r, hr, rfl⟩ | ⟨rfl, -⟩
    · rcases liftOutcomeF_cases x.ty r with ⟨e₁, e₂⟩ | ⟨ws, e₁, e₂⟩
      · exact .inl ⟨e₁, hs _ ⟨r, hr, e₂.symm⟩⟩
      · exact .inr (.inr ⟨ws, e₁, hs _ ⟨r, hr, e₂.symm⟩⟩)
    · exact .inr (.inl rfl)

/-- **The IR side with floats.** -/
theorem specToIR_float {P : Profile} {c : Simple} (hc : c.Good) (j : Fin c.exports.length)
    (vs : List IVal) {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ exportSpecF P c c.exports[j] vs) :
    IRObsF (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results vs b := by
  rcases exportSpecF_cases hb with ⟨rfl, ht⟩ | rfl | ⟨ws, rfl, hr⟩
  · exact specToIR P c hc j vs .traps ht
  · trivial
  · obtain ⟨ws', e, hp⟩ := specToIR P c hc j vs _ hr
    have hw : ws = ws' := map_toRefVal_inj e
    subst hw
    exact ⟨ws, rfl, hp⟩

/-! ## The end-to-end theorem -/

/-- **The reference half with floats**: every behaviour of an export call is an admissible
outcome (`FloatOut`). -/
theorem refToSpec_float (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity) (j : Nat) (hj : j < c.exports.length)
    (vs : List IVal) (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name (vs.map toRefVal) ⊆
      FloatOut prof P c c.exports[j] vs := by
  obtain ⟨I, cs, hI, hcs, hinst⟩ := instPhase P prof c hc hi
  have hcall := floatCallPhase P prof c hc hf ha I cs hI hcs j hj vs hvs
  intro b hb
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · have he : InstResult.instance m₁ inst es = .instance (afterInst P cs
        (liftedFuncs P (fun k => I.addrs.getD k 0) c)) ⟨0⟩ (exportMap c) := hinst _ hr
    obtain ⟨rfl, rfl, rfl⟩ : m₁ = afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c) ∧
        inst = ⟨0⟩ ∧ es = exportMap c := by
      simpa only [InstResult.instance.injEq] using he
    have hf' : f = ⟨j⟩ := Option.some.inj (hl.symm.trans (exportMap_lookup hc j hj))
    exact hcall (hf' ▸ hb)
  · exact absurd (hinst _ hr) (by simp)
  · exact absurd (hinst _ hr) (by simp)

/-- **Soundness of the component IR with floats** (outside variant payloads): every behaviour
of the reference machine calling export `j` of `c.toRef` on the reference images of well-typed
IR values `vs`, over `core3P P` at the component choice profile `prof`, is the IR observation of
the call on an admissible lowering `vs'` of `vs`, with returned values canonicalised. -/
theorem Simple.sound_float (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List IVal) (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Silmaril.Wasm.Component.Reference.Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    ∃ vs', NanAtList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      IRObsF (k := c.toComp.exports.length) (c.toComp.den (modSem P))
        ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results vs' b := by
  obtain ⟨vs', hn, hck, hs⟩ := refToSpec_float P prof c hc hf hi ha j j.isLt vs hvs hb
  exact ⟨vs', hn, hck, specToIR_float hc j vs' hs⟩

/-- **Under the deterministic component profile** the arguments the IR is called on are the
canonicalisation of `vs`. -/
theorem Simple.sound_float_deterministic (P : Profile) (c : Simple) (hc : c.Good)
    (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List IVal) (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Silmaril.Wasm.Component.Reference.Outcome)
    (hb : b ∈ exportBehaviours .deterministic (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObsF (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results
      (canonAtList c.exports[j].ty.params vs) b := by
  obtain ⟨vs', hn, -, ho⟩ := Simple.sound_float P .deterministic c hc hf hi ha j vs hvs b hb
  rw [← nanAtList_deterministic _ _ _ hn]
  exact ho

end Silmaril.Proofs.Wasm.Component.Reference
