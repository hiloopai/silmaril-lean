module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdStoreTop

/-!
# The scalar stores at the top of the code, and the widest forward fragment

* `StoreTop20`: V2's six scalar store steps (`storeIntTrap`, `storeIntVal`, `storeFloatTrap`,
  `storeFloatVal`, `storePackTrap`, `storePackVal`) at the top of the code.
  **`Task.wholeStepStoreTop20`** (stated and proved, `wholeStepStoreTop20`): at `storeB`, each is a
  step of the corrected script between the images from a configuration whose **state** is typed;
  the successor's state is typed too (`typedV_state_storeTop20`). The code is not asked to be
  typed, since a `STORE` never is.
* **`Task.wholeStepFwd20S`** (stated and proved, `wholeStepFwd20S`): at `storeB`, the nested
  fragment `Nest20 (FwdStep20L P)` (pass 1's base, the second pure fragment, `call`, and both
  vector stores) is matched forward from typed images with whole pages.
* `Good20S`: the configurations whose every V2 step is covered by one of the two statements.
  `fwd20_good20S` is the 2.0 forward obligation of `Sim10.composite10` on `Good20S`, proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The scalar stores at the top of the code -/

/-- **V2's six scalar store steps**, at the top of the code. -/
inductive StoreTop20 : Config H → Config H → Prop where
  | intTrap {s : Store H} {f : Frame} {t : IntType} {ao : V2.MemArg} {i : BitVec 32}
      {c : BitVec t.width} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
      StoreTop20 ⟨s, f, [constI32 i, .plain (.intConst t c), .plain (.intStore t none ao)]⟩
        ⟨s, f, [.trap]⟩
  | intVal {s : Store H} {f : Frame} {t : IntType} {ao : V2.MemArg} {i : BitVec 32}
      {c : BitVec t.width} {a : MemAddr} {mi mi' : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hw : mi.writeBytes? (effAddr i.toNat ao) (t.width / 8) (nbytes (.int t) c) = some mi') :
      StoreTop20 ⟨s, f, [constI32 i, .plain (.intConst t c), .plain (.intStore t none ao)]⟩
        ⟨s.setMemInst a mi', f, []⟩
  | floatTrap {s : Store H} {f : Frame} {t : FloatType} {ao : V2.MemArg} {i : BitVec 32}
      {c : BitVec t.width} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) :
      StoreTop20 ⟨s, f, [constI32 i, .plain (.floatConst t c), .plain (.floatStore t ao)]⟩
        ⟨s, f, [.trap]⟩
  | floatVal {s : Store H} {f : Frame} {t : FloatType} {ao : V2.MemArg} {i : BitVec 32}
      {c : BitVec t.width} {a : MemAddr} {mi mi' : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hw : mi.writeBytes? (effAddr i.toNat ao) (t.width / 8) (fbytes t c) = some mi') :
      StoreTop20 ⟨s, f, [constI32 i, .plain (.floatConst t c), .plain (.floatStore t ao)]⟩
        ⟨s.setMemInst a mi', f, []⟩
  | packTrap {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {ao : V2.MemArg}
      {i : BitVec 32} {c : BitVec t.width} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
      StoreTop20 ⟨s, f, [constI32 i, .plain (.intConst t c), .plain (.intStore t (some sz) ao)]⟩
        ⟨s, f, [.trap]⟩
  | packVal {s : Store H} {f : Frame} {t : IntType} {sz : PackSize} {ao : V2.MemArg}
      {i : BitVec 32} {c : BitVec t.width} {a : MemAddr} {mi mi' : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
        (ibytes sz.width (c.setWidth sz.width)) = some mi') :
      StoreTop20 ⟨s, f, [constI32 i, .plain (.intConst t c), .plain (.intStore t (some sz) ao)]⟩
        ⟨s.setMemInst a mi', f, []⟩

/-- Every top-level store step is a V2 step. -/
theorem StoreTop20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : StoreTop20 c c') : Step P host c c' := by
  cases h with
  | intTrap ha hm h => exact .storeIntTrap ha hm h
  | intVal ha hm hw => exact .storeIntVal ha hm hw
  | floatTrap ha hm h => exact .storeFloatTrap ha hm h
  | floatVal ha hm hw => exact .storeFloatVal ha hm hw
  | packTrap ha hm h => exact .storePackTrap ha hm h
  | packVal ha hm hw => exact .storePackVal ha hm hw

/-- **The top-level stores forward**, at builtins answering `$nbytes_`, `$ibytes_` and the float
primitives, from a typed state. -/
theorem fwd_storeTop20 {P : Profile} (hF : Sim.Floats.FloatB P B) (hL : LaneCalls20 B)
    (hN : NBytes20 B) {c c' : Config H}
    (hz : TypedV (simEnv20 B) stateT (stateV hn c.store c.frame)) (h : StoreTop20 c c') :
    SStepB (simEnv20S B) (configV hn c) (configV hn c') := by
  cases h with
  | intTrap ha hm h =>
    exact sstepB20S_of_fires (stepAgreeS B 11 (by decide) _
      (fires_storeNumTrap (storeNumV_int _ _) hz ha hm h))
  | intVal ha hm hw =>
    exact sstepB20S_of_fires (stepAgreeS B 12 (by decide) _
      (fires_storeNumVal hN (storeNumV_int _ _) hz ha hm hw))
  | floatTrap ha hm h =>
    exact sstepB20S_of_fires (stepAgreeS B 11 (by decide) _
      (fires_storeNumTrap (storeNumV_float _ _) hz ha hm h))
  | floatVal ha hm hw =>
    exact sstepB20S_of_fires (stepAgreeS B 12 (by decide) _
      (fires_storeNumVal hN (storeNumV_float _ _) hz ha hm hw))
  | packTrap ha hm h =>
    exact sstepB20S_of_fires (stepAgreeS B 13 (by decide) _ (fires_storePackTrap hz ha hm h))
  | packVal ha hm hw =>
    exact sstepB20S_of_fires (stepAgreeS B 14 (by decide) _ (fires_storePackVal hF hL hz ha hm hw))

/-- **Subject reduction for the state** of a top-level store step. -/
theorem typedV_state_storeTop20 {c c' : Config H}
    (hz : TypedV (simEnv20 B) stateT (stateV hn c.store c.frame)) (h : StoreTop20 c c') :
    TypedV (simEnv20 B) stateT (stateV hn c'.store c'.frame) := by
  obtain ⟨hs, hf⟩ := typedV_stateV_iff.1 hz
  cases h with
  | intTrap _ _ _ | floatTrap _ _ _ | packTrap _ _ _ => exact hz
  | intVal _ _ _ | floatVal _ _ _ | packVal _ _ _ =>
    exact typedV_stateV_iff.2 ⟨typedV_storeV_iff.2 (storeTy20_setMem (typedV_storeV_iff.1 hs) _ _),
      hf⟩

/-- **The scalar stores at the top of the code, forward, without an erratum** (stated and
proved): at `storeB`, each of V2's six scalar store steps at the top of the code, from a
configuration whose state is typed, is a step of the corrected script between the images, and
the successor's state is typed. -/
def Task.wholeStepStoreTop20 : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : RelaxedChoice) (c c' : Config H),
    TypedV (simEnv20 (storeB (Profile.spec nd r))) stateT (stateV hn c.store c.frame) →
    StoreTop20 c c' →
    TypedV (simEnv20 (storeB (Profile.spec nd r))) stateT (stateV hn c'.store c'.frame) ∧
      SStepB (simEnv20S (storeB (Profile.spec nd r))) (configV hn c) (configV hn c')

/-- **`Task.wholeStepStoreTop20` is proved.** -/
theorem wholeStepStoreTop20 : Task.wholeStepStoreTop20 := fun _ _ _ _ _ _ hz h =>
  ⟨typedV_state_storeTop20 hz h, fwd_storeTop20 (floatB_storeB _) (laneCalls20_storeB _)
    (nbytes20_storeB _) hz h⟩

/-! ## The widest nested fragment, at `storeB` -/

/-- **The nested fragment at `storeB`** (stated and proved): every step of
`Nest20 (FwdStep20L P)` from a configuration with typed image and whole pages is a step of the
corrected script between the images, with a typed successor image. -/
def Task.wholeStepFwd20S : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Profile) (c c' : Config H),
    Typed20 (simEnv20 (storeB P)) hn c → WholePages c.store → Nest20 (FwdStep20L P) c c' →
    Typed20 (simEnv20 (storeB P)) hn c' ∧
      SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20S` is proved**, at every profile. -/
theorem wholeStepFwd20S : Task.wholeStepFwd20S := by
  intro H hn P c c' hc hw h
  have F := floatB_storeB P
  exact fwd_nest20 (fwdBase20_fwdL (growCalls20_storeB _)
    (Pure.numAgree_simEnv20 (intB_storeB _) F) (Pure.cvtAgree_simEnv20 F) (vbytes20_storeB _)
    (laneCalls20_storeB _)) h hc hw

/-! ## The forward obligation on the covered configurations -/

/-- **The configurations the forward statements cover**, at profile `P`: either the image is
typed, the pages are whole and every V2 step is in the nested fragment, or the state is typed and
every V2 step is a top-level scalar store. -/
def Good20S (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  (Typed20 (simEnv20 (storeB P)) hn c ∧ WholePages c.store ∧
      ∀ c', Step P host c c' → Nest20 (FwdStep20L P) c c') ∨
    (TypedV (simEnv20 (storeB P)) stateT (stateV hn c.store c.frame) ∧
      ∀ c', Step P host c c' → StoreTop20 c c')

/-- **Every V2 step from a covered configuration is a corrected-script step.** -/
theorem fwd_good20S {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20S hn P host c) (h : Step P host c c') :
    SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c') := by
  rcases hg with ⟨hc, hw, hs⟩ | ⟨hz, hs⟩
  · exact (wholeStepFwd20S H hn P c c' hc hw (hs c' h)).2
  · exact fwd_storeTop20 (floatB_storeB P) (laneCalls20_storeB P) (nbytes20_storeB P) hz (hs c' h)

end Silmaril.Wasm.SpecTec.Sim20.Whole
