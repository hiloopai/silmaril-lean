module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.RMHost.Typed
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.RMHost.Step
public import Silmaril.Wasm.SpecTec.Sim.Round5Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Thms

/-!
# Round 8, memory SIMD: every `Step_pure` rule at memory-SIMD-free code, at any store

The `Step_pure` obligation of `NullHost.RestMSHC` at a configuration `⟨s, f, is⟩` whose code has
no memory SIMD instruction, for **every** rule, whatever the store's function bodies hold:

* the fired value reads only the code, and the primitives at `(hn, host)` and at
  `(hnU, nullHost)` over the host type `Unit` agree off `$hostcall` (`agreeOff_cross`);
* `⟨hostify s, f, is⟩` is typed (`typed_hostify`), so round 3–6's leaves apply there
  (`leafU`: `Round5.Bwd.fam_pure` for `Bwd.pureDone`, `MSRest.leaf` for `MSRest.pureVal`, and
  round 5's five vector leaves for `pureOpenR5`);
* the leaf's Core step at the host store, at the host with no outcome, is a step from
  `⟨s, f, is⟩` at any host (`step_setF`), and its result has no memory SIMD code
  (`MSPres.step_noMemSimd`), so its two encodings agree.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMHost

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS NoMemSimd StoreMS)
open Round7.MemSimd (adminsToVD TypedD)

variable {H : Type} {hn : H → String} {P : Profile}

/-! ## Primitives across host types -/

/-- `Prims.call` off `$hostcall` does not depend on the host type, the names or the host. -/
theorem call_cross {H' : Type} (P : Profile) (hn : H → String) (host : HostSemantics H)
    (hn' : H' → String) (host' : HostSemantics H') {x : String} (hx : x ≠ "hostcall")
    (ws : List ArgV) : Prims.call P hn host x ws = Prims.call P hn' host' x ws := by
  unfold Prims.call
  split
  · rfl
  split
  · rfl
  split
  · exact absurd rfl hx
  all_goals rfl

/-- **Round 6's primitives at two host types agree off `$vbytes_` and `$hostcall`.** -/
theorem agreeOff_cross {H' : Type} (P : Profile) (hn : H → String) (host : HostSemantics H)
    (hn' : H' → String) (host' : HostSemantics H') :
    Round7.HAgree.AgreeOff (Prims.builtins P hn host) (Prims.builtins P hn' host') :=
  fun _ ws _ hx => call_cross P hn host hn' host' hx ws

/-- The name of the host function `()`. -/
def hnU : Unit → String := fun _ => "host"

/-! ## The host store -/

theorem withFuncs_hostify (s : Store H) : withFuncs (hostify s) s.funcs = s := by
  cases s
  rfl

/-- The host store has no Wasm function body. -/
theorem storeMS_hostify (s : Store H) : StoreMS (hostify s) := by
  intro fi hfi fn hcode
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hfi
  cases hcode

/-- **A step at the host store, at the host with no outcome, is a step at `s`, at any host.** -/
theorem step_of_hostify {host : HostSemantics H} {s : Store H} {f f' : Frame}
    {is is' : List Admin}
    (h : Step P Round7.NullHost.nullHost (⟨hostify s, f, is⟩ : Config Unit) ⟨hostify s, f', is'⟩) :
    Step P host ⟨s, f, is⟩ ⟨s, f', is'⟩ := by
  have h' := (step_setF (host := host) h s.funcs rfl).1
  simp only [setF, withFuncs_hostify] at h'
  exact h'

/-! ## The leaves over `Unit` -/

/-- **Every `Step_pure` leaf, over the host type `Unit`**, at a typed configuration. -/
theorem leafU (i : Nat) (u : Store Unit) (f : Frame) (is : List Admin) (w : Value)
    (hT : Typed (simEnv (Prims.builtins P hnU Round7.NullHost.nullHost)) hnU ⟨u, f, is⟩)
    (hF : Fires (simEnv (Prims.builtins P hnU Round7.NullHost.nullHost)) "Step_pure" i
      (.tuple [.list (adminsToV is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P Round7.NullHost.nullHost ⟨u, f, is⟩ ⟨u, f, is'⟩ := by
  by_cases h₀ : i ∈ Round7.MSRest.pureVal
  · exact Round7.MSRest.leaf h₀ _ u f hF
  by_cases h₁ : i ∈ Bwd.pureDone
  · exact Round5.Simd.codeEq_of (Round5.Bwd.fam_pure i h₁ u f is w hT hF)
  have hlt := Round5.BwdStep.pure_lt hF
  have h₂ : i = 64 ∨ i = 70 ∨ i = 71 ∨ i = 72 ∨ i = 73 := by
    simp only [Round7.MSRest.pureVal, Bwd.pureDone, Integrate.floatDone, BwdPureStep.pureDone,
      Round5.BwdStep.pureVecDone, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at h₀ h₁
    omega
  rcases h₂ with rfl | rfl | rfl | rfl | rfl
  · exact Round5.Simd.codeEq_of (Round5.Simd.bwd_vtestop hF)
  · exact Round5.Simd.codeEq_of (Round5.Simd.bwd_vsplat hF)
  · exact Round5.Simd.codeEq_of (Round5.Simd.bwd_vextractLaneNum hF)
  · exact Round5.Simd.codeEq_of (Round5.Simd.bwd_vextractLanePack hF)
  · exact Round5.Simd.codeEq_of (Round5.Simd.bwd_vreplaceLane hF)

/-! ## The obligation -/

/-- **The `Step_pure` obligation of `RestMSHC` at memory-SIMD-free code, for every rule**, at
every store and host. -/
theorem pure_hostify {host : HostSemantics H} (i : Nat) (s : Store H) (f : Frame)
    {is : List Admin} {w : Value} (hms : AdminsMS is)
    (hT : TypedD (simEnv (Prims.builtins P hn host)) hn ⟨s, f, is⟩)
    (hF : Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i
      (.tuple [.list (adminsToVD is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have hB := agreeOff_cross P hn host hnU Round7.NullHost.nullHost
  rw [Round7.MemSimd.adminsToVD_eq is hms] at hF
  have hF₀ := (Round7.HAgree.fires_pure_iff hB i _).1 hF
  have hT₀ := typed_hostify hn hnU hms ((Round7.HAgree.typedD_iff hB hn _).1 hT)
  obtain ⟨is', js, hce, hw, hs⟩ := leafU i (hostify s) f is w hT₀ hF₀
  have hm : NoMemSimd (⟨hostify s, f, is'⟩ : Config Unit) :=
    Round7.MSPres.step_noMemSimd Round7.NullHost.nullHost_keepsMS hs ⟨storeMS_hostify s, hms⟩
  have hj : AdminsMS js := Round7.VInv.adminsMS_of_codeEq hce hm.code
  exact ⟨is', js, hce, by rw [hw, Round7.MemSimd.adminsToVD_eq js hj], step_of_hostify hs⟩

/-! ## The narrowed reduction -/

/-- **`RestMSHCP` gives `MSRest.RestMSHCR`.** -/
theorem restMSHCR_of_P {host : HostSemantics H} (h : RestMSHCP hn P host) :
    Round7.MSRest.RestMSHCR hn P host where
  pure i s f is w _ hV hT hF := by
    by_cases hms : AdminsMS is
    · exact pure_hostify i s f hms hT hF
    · exact h.pure i s f is w hms hV hT hF
  read := h.read
  step := h.step

/-- **`RestMSHCP` gives `NullHost.RestMSHC`.** -/
theorem restMSHC_of_P {host : HostSemantics H} (h : RestMSHCP hn P host) :
    Round7.NullHost.RestMSHC hn P host :=
  Round7.MSRest.restMSHC_of_R (restMSHCR_of_P h)

/-- **`OpenRMRestDPP` gives `MSRest.OpenRMRestDPR`.** -/
theorem openRMRestDPR_of_P {host : HostSemantics H} (O : OpenRMRestDPP hn P host) :
    Round7.MSRest.OpenRMRestDPR hn P host :=
  ⟨O.forward, restMSHCR_of_P O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPP`.** -/
theorem wholeStepValidRM_of_restDPP
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPP hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  Round7.MSRest.wholeStepValidRM_of_restDPR fun H hn hinj host hf hh nd r =>
    openRMRestDPR_of_P (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round8.RMHost
