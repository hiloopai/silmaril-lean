module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSRest.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.ConfigV
public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Thms

/-!
# Round 7, memory SIMD: a proved slice of `RestMSHC` (the value-level `Step_pure` leaves)

`NullHost.RestMSHC` asks for the per-rule backward obligations at configurations holding memory
SIMD code. This file proves its `Step_pure` part for the 42 rules whose round 3–6 backward leaves
read only the fired value (`pureVal`: `BwdPureStep.pureDone`, `Integrate.floatDone`,
`Round5.BwdStep.pureVecDone`), at configurations whose memory SIMD code is only in the store's
function bodies (the code itself is `AdminsMS`).

The leaves are generic in the store and give a Core step whose result they name only up to an
existential. The store-replacement argument:

* the leaf at the empty store and the host with no outcome gives a step from a
  memory-SIMD-free configuration, so its result `js₀` has no memory SIMD code
  (`MSPres.step_noMemSimd`), and the fired right-hand side `w = adminsToV js₀` has no memory SIMD
  atom (`MSAtoms.noAtomsV_of_adminsMS`);
* the leaf at the real store and host gives the Core step; its result `js₁` has the same image,
  so it has no memory SIMD code either (`MSAtoms.adminsMS_of_noAtomsV`), and `adminsToVD js₁ =
  adminsToV js₁`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSRest

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS NoMemSimd)
open Round7.MemSimd (adminsToVD)

variable {H : Type} {hn : H → String} {P : Profile}

/-- **The value-level leaves, at any host and store.** -/
theorem leaf {i : Nat} (hi : i ∈ pureVal) (host : HostSemantics H) (s : Store H) (f : Frame)
    {is : List Admin} {w : Value}
    (hF : Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i
      (.tuple [.list (adminsToV is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  simp only [pureVal, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact Bwd.pure_upTo (BwdPureStep.pure_done _ (BwdPureStep.bwdB_builtins hn host) i hi hF)
  · exact Integrate.pure_floatDone (Prims.intB_builtins hn host) (Prims.floatB_builtins hn host)
      hi hF
  · exact Round6.Target.pure_vecDoneNC i hi s f is w hF

/-- The empty store has no memory SIMD code. -/
theorem storeMS_empty : Round6.MemSimd.StoreMS ({} : Store H) := by
  intro fi hfi
  simp at hfi

/-- **The `Step_pure` obligation of `RestMSHC` for the value-level rules, at memory-SIMD-free
code**, whatever the store holds. -/
theorem pure_val {host : HostSemantics H} {i : Nat} (hi : i ∈ pureVal) (s : Store H) (f : Frame)
    {is : List Admin} {w : Value} (hms : AdminsMS is)
    (hF : Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i
      (.tuple [.list (adminsToVD is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have hF₁ : Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i
      (.tuple [.list (adminsToV is), w]) := by
    rwa [← Round7.MemSimd.adminsToVD_eq is hms]
  have hF₀ : Fires (simEnv (Prims.builtins P hn NullHost.nullHost)) "Step_pure" i
      (.tuple [.list (adminsToV is), w]) :=
    (HAgree.fires_pure_iff (NullHost.agreeOff_host P hn host NullHost.nullHost) i _).1 hF₁
  obtain ⟨is₀, js₀, hce₀, hw₀, hs₀⟩ := leaf hi NullHost.nullHost ({} : Store H) f hF₀
  have hm₀ : NoMemSimd (⟨{}, f, is₀⟩ : Config H) :=
    Round7.MSPres.step_noMemSimd NullHost.nullHost_keepsMS hs₀ ⟨storeMS_empty, hms⟩
  have hj₀ : AdminsMS js₀ := VInv.adminsMS_of_codeEq hce₀ hm₀.code
  obtain ⟨is₁, js₁, hce₁, hw₁, hs₁⟩ := leaf hi host s f hF₁
  have himg : Sim.adminsToV js₁ = Sim.adminsToV js₀ :=
    Value.list.inj (hw₁.symm.trans hw₀)
  have hj₁ : AdminsMS js₁ := MSAtoms.adminsMS_of_noAtomsV
    (himg ▸ MSAtoms.noAtomsV_of_adminsMS hj₀)
  exact ⟨is₁, js₁, hce₁, by rw [hw₁, Round7.MemSimd.adminsToVD_eq js₁ hj₁], hs₁⟩

/-! ## The narrowed reduction -/

/-- **`RestMSHCR` gives `NullHost.RestMSHC`.** -/
theorem restMSHC_of_R {host : HostSemantics H} (h : RestMSHCR hn P host) :
    NullHost.RestMSHC hn P host where
  pure i s f is w hV hT hF := by
    by_cases hv : i ∈ pureVal ∧ AdminsMS is
    · exact pure_val hv.1 s f hv.2 hF
    · exact h.pure i s f is w (by tauto) hV hT hF
  read := h.read
  step := h.step

/-- **`OpenRMRestDPR` gives `HPair.OpenRMRestDP`.** -/
theorem openRMRestDP_of_R {host : HostSemantics H} (O : OpenRMRestDPR hn P host) :
    HPair.OpenRMRestDP hn P host :=
  ⟨O.forward, restMSHC_of_R O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPR`.** -/
theorem wholeStepValidRM_of_restDPR
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPR hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  HPair.wholeStepValidRM_of_restDP fun H hn hinj host hf hh nd r =>
    openRMRestDP_of_R (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round7.MSRest
