module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.RefsCopy

/-!
# Round 5: the cast rules from `RefOkB`

`ref.test`, `ref.cast`, `br_on_cast` and `br_on_cast_fail`, forward, for the concrete `B`, from
`RefOkB` (the bridge on typed stores and bounded reference types). The store of a typed
configuration is typed, and the instantiated reference type `f.module.instRef rt` is bounded when
the frame's module is (`tyBnd_instRef`: source type indices are `u32`, and the module's defined
types are bounded). The statements match the four cast fields of `Rest`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded tyBnd ModuleBnd)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Instantiated reference types are bounded -/

/-- A source reference type, lifted, is bounded (its type indices are `u32`). -/
theorem tyBnd_liftRef (r : RefType) : tyBnd (liftRef r) = true := by
  obtain ⟨n, h⟩ := r
  cases h with
  | abstract a => rfl
  | typeIdx x =>
    show decide (x.toNat < Round4.bnd32) = true
    exact decide_eq_true x.value.isLt

/-- Substituting a bounded module's defined types is a bounded substitution. -/
theorem substBnd_all {m : ModuleInst} (hM : ModuleBnd m) :
    SubstBnd (Subst.all (m.types.map .dt)) := by
  intro v u hv
  cases v with
  | idx i =>
    have hu : u ∈ m.types.map Ty.dt := List.mem_of_getElem? (show (m.types.map Ty.dt)[i]? = some u
      from hv)
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hu
    exact hM.1 d hd
  | recv i => cases hv

/-- **A reference type instantiated in a bounded module is bounded.** -/
theorem tyBnd_instRef {m : ModuleInst} (hM : ModuleBnd m) (rt : RefType) :
    tyBnd (m.instRef rt) = true :=
  tyBnd_subst (liftRef rt) (substBnd_all hM) (tyBnd_liftRef rt)

/-- The bridge at the store and instantiated type of a step from a typed state. -/
theorem refOkAt_of {KB : RefOkB (simEnv (BI P hn host))} {s : Store H} {f : Frame}
    (hM : ModuleBnd f.module) (hz : TypedV (simEnv (BI P hn host)) stateT (stateV hn s f))
    (rt : RefType) : RefOkAt (simEnv (BI P hn host)) hn s (f.module.instRef rt) :=
  KB.refOk hn s _ ((Typing.typingFacts_simEnv (BI P hn host) hn).state s f |>.1 hz).1
    (tyBnd_instRef hM rt)

/-! ## The four cast rules -/

/-- `ref.test`, both outcomes. -/
theorem fwd_refTest5 (KB : RefOkB (simEnv (BI P hn host))) (s : Store H) (f : Frame) (r : Ref)
    (rt : RefType) (hM : ModuleBnd f.module) :
    (RefOk s r (f.module.instRef rt) →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩
        ⟨s, f, [constI32 1]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩
        ⟨s, f, [constI32 0]⟩) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := rStore_builtins hn host
  have Q : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 1 Equiv.ExecStepRules.readRule :=
    (hasStepRules_simEnv _).read
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  refine ⟨fun hok => RefsGC.fwd_of_sread T Q fun hz hc => ?_,
    fun hok => RefsGC.fwd_of_sread T Q fun hz hc => ?_⟩
  · exact sread_refTestTrueC (hasRuleAt_simEnv _ rd.refTestTrue) T R G
      (refOkAt_of (KB := KB) hM hz rt) hok hz hc
  · exact sread_refTestFalseC (hasRuleAt_simEnv _ rd.refTestFalse)
      (hasRuleAt_simEnv _ rd.refTestTrue) (RefsGC.readTable_simEnv _) T R G
      (refOkAt_of (KB := KB) hM hz rt) hok hz hc

/-- `ref.cast`, both outcomes. -/
theorem fwd_refCast5 (KB : RefOkB (simEnv (BI P hn host))) (s : Store H) (f : Frame) (r : Ref)
    (rt : RefType) (hM : ModuleBnd f.module) :
    (RefOk s r (f.module.instRef rt) →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := rStore_builtins hn host
  have Q : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 1 Equiv.ExecStepRules.readRule :=
    (hasStepRules_simEnv _).read
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  refine ⟨fun hok => RefsGC.fwd_of_sread T Q fun hz hc => ?_,
    fun hok => RefsGC.fwd_of_sread T Q fun hz hc => ?_⟩
  · exact sread_refCastSucceedC (hasRuleAt_simEnv _ rd.refCastSucceed) T R G
      (refOkAt_of (KB := KB) hM hz rt) hok hz hc
  · exact sread_refCastFailC (hasRuleAt_simEnv _ rd.refCastFail)
      (hasRuleAt_simEnv _ rd.refCastSucceed) (RefsGC.readTable_simEnv _) T R G
      (refOkAt_of (KB := KB) hM hz rt) hok hz hc

/-- `br_on_cast`, both outcomes. -/
theorem fwd_brOnCast5 (KB : RefOkB (simEnv (BI P hn host))) (s : Store H) (f : Frame) (r : Ref)
    (l : LabelIdx) (rt₁ rt₂ : RefType) (hM : ModuleBnd f.module) :
    (RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r]⟩) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := rStore_builtins hn host
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  refine ⟨fun hok => RefsGC.fwd_of_sread T (hasStepRules_simEnv _).read fun hz hc => ?_,
    fun hok => RefsGC.fwd_of_sread T (hasStepRules_simEnv _).read fun hz hc => ?_⟩
  · exact sread_brOnCastSucceedC (hasRuleAt_simEnv _ rd.brOnCastSucceed) T R G
      (refOkAt_of (KB := KB) hM hz rt₂) hok hz hc
  · exact sread_brOnCastFailC (hasRuleAt_simEnv _ rd.brOnCastFail)
      (hasRuleAt_simEnv _ rd.brOnCastSucceed) (RefsGC.readTable_simEnv _) T R G
      (refOkAt_of (KB := KB) hM hz rt₂) hok hz hc

/-- `br_on_cast_fail`, both outcomes. -/
theorem fwd_brOnCastFail5 (KB : RefOkB (simEnv (BI P hn host))) (s : Store H) (f : Frame)
    (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType) (hM : ModuleBnd f.module) :
    (RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := rStore_builtins hn host
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  refine ⟨fun hok => RefsGC.fwd_of_sread T (hasStepRules_simEnv _).read fun hz hc => ?_,
    fun hok => RefsGC.fwd_of_sread T (hasStepRules_simEnv _).read fun hz hc => ?_⟩
  · exact sread_brOnCastFailSucceedC (hasRuleAt_simEnv _ rd.brOnCastFailSucceed) T R G
      (refOkAt_of (KB := KB) hM hz rt₂) hok hz hc
  · exact sread_brOnCastFailFailC (hasRuleAt_simEnv _ rd.brOnCastFailFail)
      (hasRuleAt_simEnv _ rd.brOnCastFailSucceed) (RefsGC.readTable_simEnv _) T R G
      (refOkAt_of (KB := KB) hM hz rt₂) hok hz hc

/-- **`Rest` from `RefOkB` and the two remaining classes**: the non-bitwise SIMD operators and
the aggregate steps. -/
theorem rest_of (KB : RefOkB (simEnv (BI P hn host)))
    (vector : ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
      (∃ i, Admin.plain i ∈ is ∧ R4Fwd.VecArith i = true) → Bounded ⟨s, f, is⟩ →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩)
    (aggregate : ∀ c c' : Config H, AggregateStep c c' → Bounded c →
      FwdP (simEnv (BI P hn host)) hn c c') :
    Rest (BI P hn host) hn P host where
  vector := vector
  aggregate := aggregate
  refTest s f r rt hb := fwd_refTest5 KB s f r rt hb.frame
  refCast s f r rt hb := fwd_refCast5 KB s f r rt hb.frame
  brOnCast s f r l rt₁ rt₂ hb := fwd_brOnCast5 KB s f r l rt₁ rt₂ hb.frame
  brOnCastFail s f r l rt₁ rt₂ hb := fwd_brOnCastFail5 KB s f r l rt₁ rt₂ hb.frame

/-- **The forward conjunct on valid, bounded sources** (the `fwd` field of `Round4Int.Parts`),
from `TypesB`, `RefOkB`, a finite host respecting the encoding, and the two classes still open:
the non-bitwise SIMD operators and the aggregate steps. -/
theorem forward_valid_tb (TB : TypesB (simEnv (BI P hn host))) (KB : RefOkB (simEnv (BI P hn host)))
    (hf : HostFinite host) (hr : Prims.HostRespects hn host)
    (vector : ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
      (∃ i, Admin.plain i ∈ is ∧ R4Fwd.VecArith i = true) → Bounded ⟨s, f, is⟩ →
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩)
    (aggregate : ∀ c c' : Config H, AggregateStep c c' → Bounded c →
      FwdP (simEnv (BI P hn host)) hn c c') :
    R4Fwd.Forward (BI P hn host) hn P host Round4Int.Valid :=
  forward_valid_of TB hf hr (rest_of KB vector aggregate)

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
