module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripBase

/-!
# Removing export lists commutes with V2 `Step` on host-free stores

The 2.0 analogue 's `Round7.step_strip`. V2 never reads an export list during
reduction: every rule looks a module up through its other seven fields, and a call copies the
callee's module into the new frame. So

* `pureStep_strip`: a `PureStep` of `is` gives one of `stripAdmins20 is`;
* `readStep_strip`: a `ReadStep` in `s; f` gives one in the stripped store and frame;
* **`step_strip20`**: on a store without host functions (`NoHost20`), a step `c → c'` gives the
  step `stripConfig20 c → stripConfig20 c'`. Host calls are excluded because the host relation
  sees the store, export lists included.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem pureStep_strip {P : Profile} {is is' : List Admin} (h : PureStep P is is') :
    PureStep P (stripAdmins20 is) (stripAdmins20 is') := by
  cases h <;> simp only [stripAdmins20_cons, stripAdmins20_nil, stripAdmins20_append,
    stripAdmins20_vals, stripAdmins20_expression, stripAdmin20_toAdmin, stripAdmin20_plain,
    stripAdmin20_trap, stripAdmin20_label, stripAdmin20_frame, constI32, vconst, aref] <;>
    first
      | exact .brTableGe ‹_›
      | exact .trapVals (by simpa using ‹_›)
      | (constructor! <;> assumption)

theorem readStep_strip {s : Store H} {f : Frame} {is is' : List Admin} (h : ReadStep s f is is') :
    ReadStep (stripStore20 s) (stripFrame20 f) (stripAdmins20 is) (stripAdmins20 is') := by
  cases h with
  | callIndirectCall ht hr hf hy =>
    exact .callIndirectCall (fi := stripFI20 _) ht hr (by rw [funcInst?_stripStore20, hf]; rfl) hy
  | @callIndirectTrap _ y _ _ ht h =>
    refine .callIndirectTrap ht fun ⟨a, fi', hr, hf, hy⟩ => h ?_
    have hm : Option.map stripFI20 (s.funcInst? a) = some fi' :=
      (funcInst?_stripStore20 s a).symm.trans hf
    obtain ⟨fi, hfi, he⟩ : ∃ fi, s.funcInst? a = some fi ∧ stripFI20 fi = fi' :=
      Option.map_eq_some_iff.1 hm
    have hy' : (⟨s, f⟩ : State H).type? y = some fi.type := by rw [← he] at hy; exact hy
    exact ⟨a, fi, hr, hfi, hy'⟩
  | @callAddr a _ fi _ hf hcode hk =>
    have hf' : (stripStore20 s).funcInst? a = some (stripFI20 fi) := by
      rw [funcInst?_stripStore20, hf]; rfl
    simp only [stripAdmins20_append, stripAdmins20_vals, stripAdmins20_cons, stripAdmins20_nil,
      stripAdmin20_callAddr, stripAdmin20_frame, stripAdmin20_label, stripAdmins20_expression,
      stripFrame20_forCall]
    exact ReadStep.callAddr (f := stripFrame20 f) hf' hcode hk
  | _ =>
    simp only [stripAdmins20_cons, stripAdmins20_nil, stripAdmins20_append,
      stripAdmins20_vals, stripAdmins20_expression, stripAdmin20_toAdmin, stripAdmin20_plain,
      stripAdmin20_trap, stripAdmin20_label, stripAdmin20_callAddr, stripAdmin20_refFuncAddr,
      stripAdmin20_store8, stripAdmin20_load8u, constI32, vconst, aref]
    constructor! <;> assumption

/-- Unfold `stripConfig20` on a literal configuration and apply a state rule at the stripped
store and frame. -/
local macro "stripStep " t:term : tactic =>
  `(tactic| (simp only [stripConfig20, stripAdmins20_cons, stripAdmins20_nil,
      stripAdmin20_plain, stripAdmin20_toAdmin, stripAdmin20_trap]) <;> exact $t)

set_option linter.unusedSimpArgs false in
/-- **Forward stripping for V2**: on a store without host functions, a step `c → c'` gives the
step `stripConfig20 c → stripConfig20 c'`. -/
theorem step_strip20 {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hs : NoHost20 c.store) :
    Step P host (stripConfig20 c) (stripConfig20 c') := by
  induction h with
  | pure h => exact .pure (pureStep_strip h)
  | read h => exact .read (readStep_strip h)
  | @ctxtInstrs _ _ _ _ vs _ _ rest _ hne ih =>
    have hne' : vs ≠ [] ∨ stripAdmins20 rest ≠ [] := by simpa only [ne_eq, stripAdmins20_eq_nil] using hne
    simpa only [stripConfig20, stripAdmins20_append, stripAdmins20_vals] using
      Step.ctxtInstrs (ih hs) hne'
  | ctxtLabel _ ih =>
    simpa only [stripConfig20, stripAdmins20_cons, stripAdmins20_nil, stripAdmin20_label] using
      Step.ctxtLabel (ih hs)
  | ctxtFrame _ ih =>
    simpa only [stripConfig20, stripAdmins20_cons, stripAdmins20_nil, stripAdmin20_frame] using
      Step.ctxtFrame (f := stripFrame20 _) (ih hs)
  | callAddrHost hf hcode => exact absurd hcode (hs _ _ _ hf)
  | callAddrHostDiv hf hcode => exact absurd hcode (hs _ _ _ hf)
  | localSet hx => stripStep .localSet hx
  | globalSet ha hg => stripStep .globalSet ha hg
  | tableSetTrap ha ht h => stripStep .tableSetTrap ha ht h
  | tableSetVal ha ht h => stripStep .tableSetVal ha ht h
  | tableGrowSucceed ha ht hg hp => stripStep .tableGrowSucceed ha ht hg hp
  | tableGrowFail ha ht hp => stripStep .tableGrowFail ha ht hp
  | elemDrop ha he => stripStep .elemDrop ha he
  | storeIntTrap ha hm h => stripStep .storeIntTrap ha hm h
  | storeIntVal ha hm hw => stripStep .storeIntVal ha hm hw
  | storeFloatTrap ha hm h => stripStep .storeFloatTrap ha hm h
  | storeFloatVal ha hm hw => stripStep .storeFloatVal ha hm hw
  | storePackTrap ha hm h => stripStep .storePackTrap ha hm h
  | storePackVal ha hm hw => stripStep .storePackVal ha hm hw
  | vecStoreOob ha hm h => stripStep .vecStoreOob ha hm h
  | vecStoreVal ha hm hw => stripStep .vecStoreVal ha hm hw
  | vecStoreLaneOob ha hm h => stripStep .vecStoreLaneOob ha hm h
  | vecStoreLaneVal ha hm hj hw => stripStep .vecStoreLaneVal ha hm hj hw
  | memoryGrowSucceed ha hm hg hp => stripStep .memoryGrowSucceed ha hm hg hp
  | memoryGrowFail ha hm hp => stripStep .memoryGrowFail ha hm hp
  | dataDrop ha hd => stripStep .dataDrop ha hd

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
