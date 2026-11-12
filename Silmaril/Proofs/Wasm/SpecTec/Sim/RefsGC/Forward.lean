module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Read

/-!
# Family R: the forward obligations `Forward.reference` and `Forward.brOnCast*`

At `env := simEnv B`, from the family's assumptions (`RTyping`, `RFuns`, `RStoreFuns`,
`RefOkBridge`) and the encoding's `TypingFacts`. Provenance of every rule used is the pinned
transcription (`hasRefRules_wasm30`, `hasReadRules_wasm30`), transferred by `hasRuleAt_simEnv`;
the `otherwise` tag tables transfer by `simEnv_findRel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-! ## Provenance in `simEnv B` -/

/-- `relRules` in `simEnv B` is the pinned script's. -/
theorem relRules_simEnv (B : Builtins) (x : IL.Id) :
    relRules (simEnv B) x = relRules (envOfScript Specs.wasm30) x := by
  simp only [relRules, simEnv_findRel]

/-- The `Step_pure` tag table, in `simEnv B`. -/
theorem pureTable_simEnv (B : Builtins) :
    ((relRules (simEnv B) "Step_pure").map ruleTags).take 46 = pureTagTable := by
  rw [relRules_simEnv]
  exact pureTagTable_eq

/-- The `Step_read` tag table, in `simEnv B`. -/
theorem readTable_simEnv (B : Builtins) :
    ((relRules (simEnv B) "Step_read").map ruleTags).take 103 = readTagTable := by
  rw [relRules_simEnv]
  exact readTagTable_eq

variable {H : Type} {hn : H → String}

/-- A `Step_pure` reference rule, in `simEnv B`. -/
abbrev refRule (B : Builtins) {k : Nat} {r : Rule}
    (h : HasRuleAt (envOfScript Specs.wasm30) "Step_pure" "%~>%" k r) :
    HasRuleAt (simEnv B) "Step_pure" "%~>%" k r :=
  hasRuleAt_simEnv B h

/-- **`Forward.reference` at `simEnv B`**: every one of Core's 20 reference steps is a SpecTec
step of the images, between typed configurations. -/
theorem fwd_reference (B : Builtins) (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
    (F : RFuns (simEnv B)) (G : RStoreFuns (simEnv B)) (K : RefOkBridge (simEnv B)) :
    ∀ {c c' : Config H} (_ : RefStep c c'), FwdP (simEnv B) hn c c' := by
  have P : HasRuleAt (simEnv B) "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule :=
    (hasStepRules_simEnv B).pure
  have Q : HasRuleAt (simEnv B) "Step" "%~>%" 1 Equiv.ExecStepRules.readRule :=
    (hasStepRules_simEnv B).read
  have rr : Equiv.ExecRef.HasRefRules (envOfScript Specs.wasm30) := Equiv.ExecRef.hasRefRules_wasm30
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  have pt : ((relRules (simEnv B) "Step_pure").map ruleTags).take 46 = pureTagTable :=
    pureTable_simEnv B
  have rt : ((relRules (simEnv B) "Step_read").map ruleTags).take 103 = readTagTable :=
    readTable_simEnv B
  intro c c' h
  cases h with
  | refNull ht =>
      exact fwd_of_sread T Q fun hz hc => sread_refNull (hasRuleAt_simEnv B rd.refNull) R hz hc
  | refFunc ha =>
      exact fwd_of_sread T Q fun hz hc => sread_refFunc (hasRuleAt_simEnv B rd.refFunc) R G ha hz hc
  | refI31 i =>
      exact fwd_of_spure T P fun _ => spure_refI31 (refRule B rr.refI31) R F i
  | isNullTrue =>
      exact fwd_of_spure T P fun hc =>
        spure_isNullTrue (refRule B rr.refIsNullTrue) (R.ref _ (typed_head T hc))
  | isNullFalse hr =>
      exact fwd_of_spure T P fun hc => spure_isNullFalse (refRule B rr.refIsNullFalse)
        (refRule B rr.refIsNullTrue) pt hr (R.ref _ (typed_head T hc))
  | asNonNullNull =>
      exact fwd_of_spure T P fun hc =>
        spure_asNonNullNull (refRule B rr.refAsNonNullNull) (R.ref _ (typed_head T hc))
  | asNonNullAddr hr =>
      exact fwd_of_spure T P fun hc => spure_asNonNullAddr (refRule B rr.refAsNonNullAddr)
        (refRule B rr.refAsNonNullNull) pt hr (R.ref _ (typed_head T hc))
  | eqNull =>
      exact fwd_of_spure T P fun hc =>
        spure_eqNull (refRule B rr.refEqNull) (R.ref _ (typed_head T hc))
  | eqTrue hr =>
      exact fwd_of_spure T P fun hc => spure_eqTrue (refRule B rr.refEqTrue)
        (refRule B rr.refEqNull) pt hr (R.ref _ (typed_head T hc))
  | eqFalse hr =>
      exact fwd_of_spure T P fun hc => spure_eqFalse (refRule B rr.refEqFalse)
        (refRule B rr.refEqNull) (refRule B rr.refEqTrue) pt hr (R.ref _ (typed_head T hc))
        (R.ref _ (typed_head T (typed_tail T hc)))
  | testTrue hok =>
      exact fwd_of_sread T Q fun hz hc =>
        sread_refTestTrue (hasRuleAt_simEnv B rd.refTestTrue) T R G K hok hz hc
  | testFalse hok =>
      exact fwd_of_sread T Q fun hz hc => sread_refTestFalse (hasRuleAt_simEnv B rd.refTestFalse)
        (hasRuleAt_simEnv B rd.refTestTrue) rt T R G K hok hz hc
  | castSucceed hok =>
      exact fwd_of_sread T Q fun hz hc =>
        sread_refCastSucceed (hasRuleAt_simEnv B rd.refCastSucceed) T R G K hok hz hc
  | castFail hok =>
      exact fwd_of_sread T Q fun hz hc => sread_refCastFail (hasRuleAt_simEnv B rd.refCastFail)
        (hasRuleAt_simEnv B rd.refCastSucceed) rt T R G K hok hz hc
  | i31GetNull sx =>
      exact fwd_of_spure T P fun _ => spure_i31GetNull (refRule B rr.i31GetNull) R sx
  | i31GetNum sx i =>
      exact fwd_of_spure T P fun _ => spure_i31GetNum (refRule B rr.i31GetNum) R F sx i
  | externConvertNull =>
      exact fwd_of_spure T P fun hc =>
        spure_externConvertNull (refRule B rr.externConvertAnyNull) (R.ref _ (typed_head T hc))
  | externConvertAddr hr =>
      exact fwd_of_spure T P fun hc => spure_externConvertAddr
        (refRule B rr.externConvertAnyAddr) (refRule B rr.externConvertAnyNull) pt hr
        (R.ref _ (typed_head T hc))
  | anyConvertNull =>
      exact fwd_of_spure T P fun _ => spure_anyConvertNull (refRule B rr.anyConvertExternNull)
  | anyConvertAddr r =>
      exact fwd_of_spure T P fun hc =>
        spure_anyConvertAddr (refRule B rr.anyConvertExternAddr) (R.externArg r (typed_head T hc))

/-- **`Forward.brOnCastSucceed` at `simEnv B`.** -/
theorem fwd_brOnCastSucceed (B : Builtins) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B)) (K : RefOkBridge (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (_ : RefOk s r (f.module.instRef rt₂)),
    FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
      ⟨s, f, [.ref r, .plain (.br l)]⟩ :=
  fun hok => fwd_of_sread T (hasStepRules_simEnv B).read fun hz hc =>
    sread_brOnCastSucceed (hasRuleAt_simEnv B Equiv.ExecRead.hasReadRules_wasm30.brOnCastSucceed)
      T R G K hok hz hc

/-- **`Forward.brOnCastFail` at `simEnv B`.** -/
theorem fwd_brOnCastFail (B : Builtins) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B)) (K : RefOkBridge (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (_ : ¬ RefOk s r (f.module.instRef rt₂)),
    FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩ :=
  fun hok => fwd_of_sread T (hasStepRules_simEnv B).read fun hz hc =>
    sread_brOnCastFail (hasRuleAt_simEnv B Equiv.ExecRead.hasReadRules_wasm30.brOnCastFail)
      (hasRuleAt_simEnv B Equiv.ExecRead.hasReadRules_wasm30.brOnCastSucceed) (readTable_simEnv B)
      T R G K hok hz hc

/-- **`Forward.brOnCastFailSucceed` at `simEnv B`.** -/
theorem fwd_brOnCastFailSucceed (B : Builtins) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B)) (K : RefOkBridge (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (_ : RefOk s r (f.module.instRef rt₂)),
    FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩ :=
  fun hok => fwd_of_sread T (hasStepRules_simEnv B).read fun hz hc =>
    sread_brOnCastFailSucceed
      (hasRuleAt_simEnv B Equiv.ExecRead.hasReadRules_wasm30.brOnCastFailSucceed) T R G K hok hz hc

/-- **`Forward.brOnCastFailFail` at `simEnv B`.** -/
theorem fwd_brOnCastFailFail (B : Builtins) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B)) (K : RefOkBridge (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (_ : ¬ RefOk s r (f.module.instRef rt₂)),
    FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
      ⟨s, f, [.ref r, .plain (.br l)]⟩ :=
  fun hok => fwd_of_sread T (hasStepRules_simEnv B).read fun hz hc =>
    sread_brOnCastFailFail (hasRuleAt_simEnv B Equiv.ExecRead.hasReadRules_wasm30.brOnCastFailFail)
      (hasRuleAt_simEnv B Equiv.ExecRead.hasReadRules_wasm30.brOnCastFailSucceed)
      (readTable_simEnv B) T R G K hok hz hc

end Silmaril.Wasm.SpecTec.Sim.RefsGC
