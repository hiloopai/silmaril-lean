module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapBase

/-!
# Re-encoding export lists commutes with V2 `Step` on host-free stores

Round 7's `step_strip20` for any re-encoding `F` of export lists. V2 never reads an export list
during reduction: every rule reaches a module through its other seven fields, and a call copies
the callee's module into the new frame. So

* `pureStep_exp`, `readStep_exp`: the two sub-relations;
* **`step_exp20`**: on a store without host functions (`NoHost20`), a step `c → c'` gives the step
  `expConfig20 F c → expConfig20 F c'`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Strip (NoHost20)

variable {H : Type} {F : ModuleInst → List ExportInst}

theorem pureStep_exp {P : Profile} {is is' : List Admin} (h : PureStep P is is') :
    PureStep P (expAdmins20 F is) (expAdmins20 F is') := by
  cases h <;> simp only [expAdmins20_cons, expAdmins20_nil, expAdmins20_append,
    expAdmins20_vals, expAdmins20_expression, expAdmin20_toAdmin, expAdmin20_plain,
    expAdmin20_trap, expAdmin20_label, expAdmin20_frame, constI32, vconst, aref] <;>
    first
      | exact .brTableGe ‹_›
      | exact .trapVals (by simpa using ‹_›)
      | (constructor! <;> assumption)

theorem readStep_exp {s : Store H} {f : Frame} {is is' : List Admin} (h : ReadStep s f is is') :
    ReadStep (expStore20 F s) (expFrame20 F f) (expAdmins20 F is) (expAdmins20 F is') := by
  cases h with
  | callIndirectCall ht hr hf hy =>
    exact .callIndirectCall (fi := expFI20 F _) ht hr (by rw [funcInst?_expStore20, hf]; rfl) hy
  | @callIndirectTrap _ y _ _ ht h =>
    refine .callIndirectTrap ht fun ⟨a, fi', hr, hf, hy⟩ => h ?_
    have hm : Option.map (expFI20 F) (s.funcInst? a) = some fi' :=
      (funcInst?_expStore20 s a).symm.trans hf
    obtain ⟨fi, hfi, he⟩ : ∃ fi, s.funcInst? a = some fi ∧ expFI20 F fi = fi' :=
      Option.map_eq_some_iff.1 hm
    have hy' : (⟨s, f⟩ : State H).type? y = some fi.type := by rw [← he] at hy; exact hy
    exact ⟨a, fi, hr, hfi, hy'⟩
  | @callAddr a _ fi _ hf hcode hk =>
    have hf' : (expStore20 F s).funcInst? a = some (expFI20 F fi) := by
      rw [funcInst?_expStore20, hf]; rfl
    simp only [expAdmins20_append, expAdmins20_vals, expAdmins20_cons, expAdmins20_nil,
      expAdmin20_callAddr, expAdmin20_frame, expAdmin20_label, expAdmins20_expression,
      expFrame20_forCall]
    exact ReadStep.callAddr (f := expFrame20 F f) hf' hcode hk
  | _ =>
    simp only [expAdmins20_cons, expAdmins20_nil, expAdmins20_append,
      expAdmins20_vals, expAdmins20_expression, expAdmin20_toAdmin, expAdmin20_plain,
      expAdmin20_trap, expAdmin20_label, expAdmin20_callAddr, expAdmin20_refFuncAddr,
      expAdmin20_store8, expAdmin20_load8u, constI32, vconst, aref]
    constructor! <;> assumption

/-- Unfold `expConfig20` on a literal configuration and apply a state rule at the re-encoded
store and frame. -/
local macro "expStep " t:term : tactic =>
  `(tactic| (simp only [expConfig20, expAdmins20_cons, expAdmins20_nil,
      expAdmin20_plain, expAdmin20_toAdmin, expAdmin20_trap]) <;> exact $t)

set_option linter.unusedSimpArgs false in
/-- **Re-encoding export lists, forward, for V2**: on a store without host functions, a step `c → c'` gives the
step `expConfig20 F c → expConfig20 F c'`. -/
theorem step_exp20 {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hs : NoHost20 c.store) :
    Step P host (expConfig20 F c) (expConfig20 F c') := by
  induction h with
  | pure h => exact .pure (pureStep_exp h)
  | read h => exact .read (readStep_exp h)
  | @ctxtInstrs _ _ _ _ vs _ _ rest _ hne ih =>
    have hne' : vs ≠ [] ∨ expAdmins20 F rest ≠ [] := by simpa only [ne_eq, expAdmins20_eq_nil] using hne
    simpa only [expConfig20, expAdmins20_append, expAdmins20_vals] using
      Step.ctxtInstrs (ih hs) hne'
  | ctxtLabel _ ih =>
    simpa only [expConfig20, expAdmins20_cons, expAdmins20_nil, expAdmin20_label] using
      Step.ctxtLabel (ih hs)
  | ctxtFrame _ ih =>
    simpa only [expConfig20, expAdmins20_cons, expAdmins20_nil, expAdmin20_frame] using
      Step.ctxtFrame (f := expFrame20 F _) (ih hs)
  | callAddrHost hf hcode => exact absurd hcode (hs _ _ _ hf)
  | callAddrHostDiv hf hcode => exact absurd hcode (hs _ _ _ hf)
  | localSet hx => expStep .localSet hx
  | globalSet ha hg => expStep .globalSet ha hg
  | tableSetTrap ha ht h => expStep .tableSetTrap ha ht h
  | tableSetVal ha ht h => expStep .tableSetVal ha ht h
  | tableGrowSucceed ha ht hg hp => expStep .tableGrowSucceed ha ht hg hp
  | tableGrowFail ha ht hp => expStep .tableGrowFail ha ht hp
  | elemDrop ha he => expStep .elemDrop ha he
  | storeIntTrap ha hm h => expStep .storeIntTrap ha hm h
  | storeIntVal ha hm hw => expStep .storeIntVal ha hm hw
  | storeFloatTrap ha hm h => expStep .storeFloatTrap ha hm h
  | storeFloatVal ha hm hw => expStep .storeFloatVal ha hm hw
  | storePackTrap ha hm h => expStep .storePackTrap ha hm h
  | storePackVal ha hm hw => expStep .storePackVal ha hm hw
  | vecStoreOob ha hm h => expStep .vecStoreOob ha hm h
  | vecStoreVal ha hm hw => expStep .vecStoreVal ha hm hw
  | vecStoreLaneOob ha hm h => expStep .vecStoreLaneOob ha hm h
  | vecStoreLaneVal ha hm hj hw => expStep .vecStoreLaneVal ha hm hj hw
  | memoryGrowSucceed ha hm hg hp => expStep .memoryGrowSucceed ha hm hg hp
  | memoryGrowFail ha hm hp => expStep .memoryGrowFail ha hm hp
  | dataDrop ha hd => expStep .dataDrop ha hd

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
