module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatVCall
public import Silmaril.Proofs.Wasm.Component.Reference.FloatSound
public import Silmaril.Proofs.Wasm.Component.Reference.InstRun
public import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR
public import Silmaril.Proofs.Wasm.Component.Reference.RefToSpec

/-!
# Soundness of the component IR with floats

Without `Simple.FloatFree` the reference machine and the IR differ in their treatment of NaNs:
lowering an argument NaN may choose another NaN (C7, admissible answers `NanLower prof`), and
lifting a result canonicalises NaNs. Core code can observe NaN payloads, so the reference call
is not the IR call on the same arguments. The precise relation (`Simple.sound_floatV`), for
floats at every type, variant payloads included (no hypothesis on the types; `FloatSound` is
the case without floats in variant payloads): every behaviour of the reference
machine calling export `j` on `vs.map toRefVal` is an IR observation of the call on **some**
admissible lowering `vs'` of `vs` (`NanAtVList prof ts vs vs'`), whose returned values `ws` the
reference reports **canonicalised** (`canonAtVList`):

* returned results `rs`: `rs = (canonAtVList results ws).map toRefVal` and the IR plays
  `ask (j, vals vs') · ans (vals ws)`;
* a trap: the IR plays `ask (j, vals vs') · ans none`.

Under the deterministic component profile the admissible lowering is unique, the
canonicalisation of the arguments (`nanAtVList_deterministic`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## From the canonicalised specification to the IR -/

/-- An outcome of `liftOutcomeFV` is the canonicalisation of the outcome of `liftOutcome`. -/
theorem liftOutcomeF_casesV (ft : FuncTy) (r : Option (List Flat)) :
    (liftOutcomeFV ft r = .traps ∧ liftOutcome ft r = .traps) ∨
      ∃ ws, liftOutcomeFV ft r = .returns (some ((canonAtVList ft.results ws).map toRefVal)) ∧
        liftOutcome ft r = .returns (some (ws.map toRefVal)) := by
  cases r with
  | none => exact .inl ⟨rfl, rfl⟩
  | some ys =>
    cases h : liftArgs ft.results ys with
    | none => exact .inl ⟨by simp only [liftOutcomeFV, h], by simp only [liftOutcome, h]⟩
    | some ws => exact .inr ⟨ws, by simp only [liftOutcomeFV, h], by simp only [liftOutcome, h]⟩

section Mem

variable {P : Profile} {c : Simple} {x : SimpleExport} {vs : List IVal}
  {b : Silmaril.Wasm.Component.Reference.Outcome}

theorem mem_exportSpecF_noneV (hl : checkLower x.ty.params vs = none) :
    b ∈ exportSpecFV P c x vs ↔ b = .traps := by
  unfold exportSpecFV
  rw [hl]
  rfl

theorem mem_exportSpecF_someV {xs : List Flat} (hl : checkLower x.ty.params vs = some xs) :
    b ∈ exportSpecFV P c x vs ↔ (∃ r ∈ coreOut P c.mod x.core xs, b = liftOutcomeFV x.ty r) ∨
      (b = .diverges ∧ coreDiverges P c.mod x.core xs) := by
  unfold exportSpecFV
  rw [hl]
  rfl

end Mem

/-- **`exportSpecFV` is `exportSpec` with canonicalised results.** -/
theorem exportSpecF_casesV {P : Profile} {c : Simple} {x : SimpleExport} {vs : List IVal}
    {b : Silmaril.Wasm.Component.Reference.Outcome} (hb : b ∈ exportSpecFV P c x vs) :
    (b = .traps ∧ .traps ∈ exportSpec P c x vs) ∨ b = .diverges ∨
      ∃ ws, b = .returns (some ((canonAtVList x.ty.results ws).map toRefVal)) ∧
        .returns (some (ws.map toRefVal)) ∈ exportSpec P c x vs := by
  cases hl : checkLower x.ty.params vs with
  | none => exact .inl ⟨(mem_exportSpecF_noneV hl).mp hb, (mem_exportSpec_none hl).mpr rfl⟩
  | some xs =>
    have hb' : (∃ r ∈ coreOut P c.mod x.core xs, b = liftOutcomeFV x.ty r) ∨
        (b = .diverges ∧ coreDiverges P c.mod x.core xs) := (mem_exportSpecF_someV hl).mp hb
    have hs : ∀ b', (∃ r ∈ coreOut P c.mod x.core xs, b' = liftOutcome x.ty r) →
        b' ∈ exportSpec P c x vs := fun b' h => (mem_exportSpec_some hl).mpr (.inl h)
    rcases hb' with ⟨r, hr, rfl⟩ | ⟨rfl, -⟩
    · rcases liftOutcomeF_casesV x.ty r with ⟨e₁, e₂⟩ | ⟨ws, e₁, e₂⟩
      · exact .inl ⟨e₁, hs _ ⟨r, hr, e₂.symm⟩⟩
      · exact .inr (.inr ⟨ws, e₁, hs _ ⟨r, hr, e₂.symm⟩⟩)
    · exact .inr (.inl rfl)

/-- **The IR side with floats.** -/
theorem specToIR_floatV {P : Profile} {c : Simple} (hc : c.Good) (j : Fin c.exports.length)
    (vs : List IVal) {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ exportSpecFV P c c.exports[j] vs) :
    IRObsFV (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results vs b := by
  rcases exportSpecF_casesV hb with ⟨rfl, ht⟩ | rfl | ⟨ws, rfl, hr⟩
  · exact specToIR P c hc j vs .traps ht
  · trivial
  · obtain ⟨ws', e, hp⟩ := specToIR P c hc j vs _ hr
    have hw : ws = ws' := map_toRefVal_inj e
    subst hw
    exact ⟨ws, rfl, hp⟩

/-! ## The end-to-end theorem -/

/-- **The reference half with floats**: every behaviour of an export call is an admissible
outcome (`FloatOutV`). -/
theorem refToSpec_floatV (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hi : c.Inst) (ha : c.Arity) (j : Nat) (hj : j < c.exports.length)
    (vs : List IVal) (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name (vs.map toRefVal) ⊆
      FloatOutV prof P c c.exports[j] vs := by
  obtain ⟨I, cs, hI, hcs, hinst⟩ := instPhase P prof c hc hi
  have hcall := floatCallPhaseV P prof c hc ha I cs hI hcs j hj vs hvs
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

/-- **Soundness of the component IR with floats** (at every type): every behaviour
of the reference machine calling export `j` of `c.toRef` on the reference images of well-typed
IR values `vs`, over `core3P P` at the component choice profile `prof`, is the IR observation of
the call on an admissible lowering `vs'` of `vs`, with returned values canonicalised. -/
theorem Simple.sound_floatV (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List IVal) (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Silmaril.Wasm.Component.Reference.Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    ∃ vs', NanAtVList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      IRObsFV (k := c.toComp.exports.length) (c.toComp.den (modSem P))
        ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results vs' b := by
  obtain ⟨vs', hn, hck, hs⟩ := refToSpec_floatV P prof c hc hi ha j j.isLt vs hvs hb
  exact ⟨vs', hn, hck, specToIR_floatV hc j vs' hs⟩

/-- **Under the deterministic component profile** the arguments the IR is called on are the
canonicalisation of `vs`. -/
theorem Simple.sound_floatV_deterministic (P : Profile) (c : Simple) (hc : c.Good)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List IVal) (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Silmaril.Wasm.Component.Reference.Outcome)
    (hb : b ∈ exportBehaviours .deterministic (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObsFV (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results
      (canonAtVList c.exports[j].ty.params vs) b := by
  obtain ⟨vs', hn, -, ho⟩ := Simple.sound_floatV P .deterministic c hc hi ha j vs hvs b hb
  rw [← nanAtVList_deterministic _ _ _ hn]
  exact ho

end Silmaril.Proofs.Wasm.Component.Reference
