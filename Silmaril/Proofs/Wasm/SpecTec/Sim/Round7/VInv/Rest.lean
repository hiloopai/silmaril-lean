module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Defs

/-!
# Round 7, memory SIMD: `OpenRMRest.rest` on the memory-SIMD-free domain

`OpenRMRest.rest` is `BackwardUpToDRestS NoCastVM (simEnv BM) hn P host`. By
`VDecl.backwardUpToDRestS_withVBytes_iff` it is the same obligation at `BI`. Round 6's per-rule
leaves (`Round6.Target.backwardUpToNC`) are stated at `configV`. The bridge between the two
encodings is `configVD_eq_of_noMemSimd`: off memory SIMD code they agree.

* `adminsMS_of_codeEq`: `CodeEq` keeps the absence of memory SIMD code (it only changes
  `CALL_REF` annotations).
* `backwardUpToDRestS_noMSDom`: the obligations hold, at `BI` and at `BM`, on `NoMSDom`: no memory
  SIMD code in the configuration or in any Core successor. The source's image and the successor's
  are `configV` images there, so round 6's leaves apply verbatim.
* `rest_of_restMS`: `OpenRMRest.rest` follows from `RestMS`, the same obligations at the
  `NoCastVM` configurations outside `NoMSDom`. That is all that is left of `rest`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminMS AdminsMS NoMemSimd)
open Round7.MemSimd (NoCastVM BackwardUpToDRestS TypedD configVD adminsToVD)

variable {H : Type}

/-! ## `CodeEq` keeps memory-SIMD-free code -/

theorem adminMS_of_isCallRef {b : Admin} (h : b.IsCallRef) : AdminMS b := by
  rcases b with i | _ | _ | _ | _ | _ | _ | _ <;> simp only [Admin.IsCallRef] at h
  · cases i <;> simp only at h
    simp [AdminMS, Round6.MemSimd.instrMS, Round6.MemSimd.memSimd]
  · simp [AdminMS]

mutual
/-- `AdminEq` keeps `AdminMS`. -/
theorem adminMS_of_adminEq : ∀ {a b : Admin}, Bwd.AdminEq a b → AdminMS a → AdminMS b
  | _, _, .refl _, h => h
  | _, _, .call _ hb, _ => adminMS_of_isCallRef hb
  | _, _, .label hc, h => by
      simp only [AdminMS] at h ⊢
      exact ⟨h.1, adminsMS_of_codeEq hc h.2⟩
  | _, _, .handler hc, h => by
      simp only [AdminMS] at h ⊢
      exact adminsMS_of_codeEq hc h
  | _, _, .frame hc, h => by
      simp only [AdminMS] at h ⊢
      exact adminsMS_of_codeEq hc h

/-- **`CodeEq` keeps `AdminsMS`.** -/
theorem adminsMS_of_codeEq : ∀ {is js : List Admin}, Bwd.CodeEq is js → AdminsMS is → AdminsMS js
  | _, _, .nil, h => h
  | _, _, .cons ha hc, h => by
      simp only [AdminsMS] at h ⊢
      exact ⟨adminMS_of_adminEq ha h.1, adminsMS_of_codeEq hc h.2⟩
end

theorem noMemSimd_of_configEq {c d : Config H} (h : Bwd.ConfigEq c d) (hc : NoMemSimd c) :
    NoMemSimd d :=
  ⟨h.1 ▸ hc.store, adminsMS_of_codeEq h.2.2 hc.code⟩

/-! ## The obligations on `NoMSDom` -/

section

variable {hn : H → String} {P : Profile} {host : HostSemantics H}

theorem typed_of_typedD {env : Env} {c : Config H} (hm : NoMemSimd c) (h : TypedD env hn c) :
    Typed env hn c := by
  unfold TypedD at h
  unfold Typed
  rwa [← Round7.MemSimd.configVD_eq_of_noMemSimd hn hm]

/-- A successor code without memory SIMD code has the same image under both encodings. -/
theorem adminsToVD_of_succ {c : Config H} {is' js : List Admin}
    (hsucc : ∀ c₁, Step P host c c₁ → NoMemSimd c₁) (hce : Bwd.CodeEq is' js)
    (hs : Step P host c ⟨c.store, c.frame, is'⟩) : adminsToVD js = adminsToV js :=
  Round7.MemSimd.adminsToVD_eq js (adminsMS_of_codeEq hce (hsucc _ hs).code)

theorem pure_noMSDom (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value)
    (hV : NoMSDom P host ⟨s, f, is⟩) (hT : TypedD (simEnv (Prims.builtins P hn host)) hn ⟨s, f, is⟩)
    (hF : Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i
      (.tuple [.list (adminsToVD is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨hcv, hm, hsucc⟩ := hV
  have hF' : Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i
      (.tuple [.list (adminsToV is), w]) := by
    rwa [← Round7.MemSimd.adminsToVD_eq is hm.code]
  obtain ⟨is', js, hce, rfl, hs⟩ := (Round6.Target.backwardUpToNC hinj hf hPs hPf).pure i s f is w
    (Round7.MemSimd.noCastV_of_noCastVM hcv hm.code) (typed_of_typedD hm hT) hF'
  exact ⟨is', js, hce, by rw [adminsToVD_of_succ hsucc hce hs], hs⟩

theorem read_noMSDom (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (i : Nat) (c : Config H) (w : Value) (hV : NoMSDom P host c)
    (hT : TypedD (simEnv (Prims.builtins P hn host)) hn c)
    (hF : Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  obtain ⟨hcv, hm, hsucc⟩ := hV
  have hF' : Fires (simEnv (Prims.builtins P hn host)) "Step_read" i
      (.tuple [configV hn c, w]) := by
    rwa [← Round7.MemSimd.configVD_eq_of_noMemSimd hn hm]
  obtain ⟨is', js, hce, rfl, hs⟩ := (Round6.Target.backwardUpToNC hinj hf hPs hPf).read i c w
    (Round7.MemSimd.noCastV_of_noCastVM hcv hm.code) (typed_of_typedD hm hT) hF'
  exact ⟨is', js, hce, by rw [adminsToVD_of_succ hsucc hce hs], hs⟩

theorem step_noMSDom (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (i : Nat) (h6 : 6 ≤ i) (c : Config H) (w : Value) (hV : NoMSDom P host c)
    (hT : TypedD (simEnv (Prims.builtins P hn host)) hn c)
    (hF : Fires (simEnv (Prims.builtins P hn host)) "Step" i (.tuple [configVD hn c, w])) :
    Round7.MemSimd.BwdUpToD hn P host c w := by
  obtain ⟨hcv, hm, hsucc⟩ := hV
  have hF' : Fires (simEnv (Prims.builtins P hn host)) "Step" i (.tuple [configV hn c, w]) := by
    rwa [← Round7.MemSimd.configVD_eq_of_noMemSimd hn hm]
  obtain ⟨c', d', hce, rfl, hs⟩ := (Round6.Target.backwardUpToNC hinj hf hPs hPf).step i h6 c w
    (Round7.MemSimd.noCastV_of_noCastVM hcv hm.code) (typed_of_typedD hm hT) hF'
  have hd : NoMemSimd d' := noMemSimd_of_configEq hce (hsucc _ hs)
  exact ⟨c', d', hce, by rw [Round7.MemSimd.configVD_eq_of_noMemSimd hn hd], hs⟩

/-- **The per-rule obligations off memory SIMD hold at `BI` on `NoMSDom`**, from round 6's leaves,
for an injective encoding, a finite host and a profile in which growth may both succeed and
fail. -/
theorem backwardUpToDRestS_noMSDom (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d) :
    BackwardUpToDRestS (NoMSDom P host) (simEnv (Prims.builtins P hn host)) hn P host where
  pure := pure_noMSDom hinj hf hPs hPf
  read i _ := read_noMSDom hinj hf hPs hPf i
  step i h6 _ := step_noMSDom hinj hf hPs hPf i h6

/-- **The same at `BM`**, the builtins `OpenRMRest.rest` is stated at. -/
theorem backwardUpToDRestS_noMSDom_BM (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d) :
    BackwardUpToDRestS (NoMSDom P host) (simEnv (Round7.MemSimd.BM P hn host)) hn P host :=
  (VDecl.backwardUpToDRestS_withVBytes_iff _ _ hn P host).2
    (backwardUpToDRestS_noMSDom hinj hf hPs hPf)

/-- Two obligations on the two halves of a split of `V` give the obligation on `V`. -/
theorem backwardUpToDRestS_split {V W : Config H → Prop} {env : Env}
    (h₁ : BackwardUpToDRestS (fun c => V c ∧ W c) env hn P host)
    (h₂ : BackwardUpToDRestS (fun c => V c ∧ ¬ W c) env hn P host) :
    BackwardUpToDRestS V env hn P host where
  pure i s f is w hV hT hF := by
    by_cases hW : W ⟨s, f, is⟩
    · exact h₁.pure i s f is w ⟨hV, hW⟩ hT hF
    · exact h₂.pure i s f is w ⟨hV, hW⟩ hT hF
  read i hi c w hV hT hF := by
    by_cases hW : W c
    · exact h₁.read i hi c w ⟨hV, hW⟩ hT hF
    · exact h₂.read i hi c w ⟨hV, hW⟩ hT hF
  step i h6 hi c w hV hT hF := by
    by_cases hW : W c
    · exact h₁.step i h6 hi c w ⟨hV, hW⟩ hT hF
    · exact h₂.step i h6 hi c w ⟨hV, hW⟩ hT hF

/-- A smaller predicate keeps the obligations. -/
theorem backwardUpToDRestS_mono {V W : Config H → Prop} {env : Env} (hVW : ∀ c, V c → W c)
    (h : BackwardUpToDRestS W env hn P host) : BackwardUpToDRestS V env hn P host where
  pure i s f is w hV hT hF := h.pure i s f is w (hVW _ hV) hT hF
  read i hi c w hV hT hF := h.read i hi c w (hVW _ hV) hT hF
  step i h6 hi c w hV hT hF := h.step i h6 hi c w (hVW _ hV) hT hF

/-- **`OpenRMRest.rest` from `RestMS`**: what is left of `rest` is its part at configurations with
memory SIMD code in the configuration or in a Core successor. -/
theorem rest_of_restMS (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (h : RestMS hn P host) :
    BackwardUpToDRestS NoCastVM (simEnv (Round7.MemSimd.BM P hn host)) hn P host := by
  refine (VDecl.backwardUpToDRestS_withVBytes_iff _ _ hn P host).2 ?_
  refine backwardUpToDRestS_split (W := NoMSDom P host) ?_ h
  exact backwardUpToDRestS_mono (fun _ hc => hc.2) (backwardUpToDRestS_noMSDom hinj hf hPs hPf)

/-- **`RestMS` is `rest`'s remainder, exactly**: `rest` implies it (both directions). -/
theorem restMS_of_rest
    (h : BackwardUpToDRestS NoCastVM (simEnv (Round7.MemSimd.BM P hn host)) hn P host) :
    RestMS hn P host :=
  backwardUpToDRestS_mono (fun _ hc => hc.1)
    ((VDecl.backwardUpToDRestS_withVBytes_iff _ _ hn P host).1 h)

end

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
