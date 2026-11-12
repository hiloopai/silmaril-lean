module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Runs.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Thms

/-!
# Round 7, runs: the export swap at a witness

`Round7.Task.swapEquiv` is stated at a valid configuration. Its proof
(`Round7.EraseDer.swapEquiv_holds`) uses only `StripInj c` and `NamesBnd c` of `c`
(`Round7.EraseDer.sStepB_QC_fwd`, `sStepB_QC_bwd` and the four excluded rules), and it works at
every input whose module records are in the swap set `QC c`. So it applies at the image of any
configuration `d` whose module instances are among those of `c`, in particular at a
`Bwd.ConfigEq` witness of `c` (`mods_configEq`), which need not be valid:

* `excRules_QC`: the four rules outside the kernel check commute with erasure on `QC c`, for any
  `c` with `StripInj c` and `NamesBnd c`;
* `swapAt_fwd`, `swapAt_bwd`: the two halves of `Round7.Task.swapEquiv` at such a `d`, un-stripping
  along `c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Runs

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (gdB)
open Round6.Reading (SStepB)

variable {H : Type}

/-! ## The module instances of a witness -/

theorem modsAdmin_callRef {a : Admin} (h : a.IsCallRef) : modsAdmin a = [] := by
  cases a with
  | plain i => rfl
  | callRefType _ => rfl
  | label => exact absurd h id
  | handler => exact absurd h id
  | frame => exact absurd h id
  | ref => exact absurd h id
  | returnCallRefType => exact absurd h id
  | trap => exact absurd h id

mutual
theorem modsAdmin_eq : ∀ {a b : Admin}, Bwd.AdminEq a b → modsAdmin b = modsAdmin a
  | _, _, .refl _ => rfl
  | _, _, .call ha hb => by rw [modsAdmin_callRef ha, modsAdmin_callRef hb]
  | _, _, .label h => by simp only [modsAdmin, modsAdmins_eq h]
  | _, _, .handler h => by simp only [modsAdmin, modsAdmins_eq h]
  | _, _, .frame h => by simp only [modsAdmin, modsAdmins_eq h]

theorem modsAdmins_eq : ∀ {l r : List Admin}, Bwd.CodeEq l r → modsAdmins r = modsAdmins l
  | _, _, .nil => rfl
  | _, _, .cons ha hl => by simp only [modsAdmins, modsAdmin_eq ha, modsAdmins_eq hl]
end

/-- **A `Bwd.ConfigEq` witness has the same module instances.** -/
theorem mods_configEq {c d : Config H} (h : Bwd.ConfigEq c d) : mods d = mods c := by
  obtain ⟨hs, hf, hc⟩ := h
  simp only [mods, hs, hf, modsAdmins_eq hc]

/-! ## The excluded rules at any configuration with `StripInj` and `NamesBnd` -/

/-- **The four rules outside the kernel check commute with erasure on `QC c`**, for every `c`
with `StripInj c` and `NamesBnd c` (no validity needed). -/
theorem excRules_QC {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
    (hf : HostFinite host) (hb : HostExportBlind host) (hp : HostExportParam host)
    (P : Profile) {c : Config H} (hi : StripInj c) (hnb : NamesBnd c) :
    ∀ nm ∈ excNames, RuleFwd (QC c) (utf8Env (Round4Int.BI P hn host)) nm ∧
      RuleBwd (QC c) (utf8Env (Round4Int.BI P hn host)) nm := by
  intro nm hnm
  have HE := EraseAll.hyps_BI hi P hn host
  have HB := EraseAll.hyps_B hi P hn host
  have H' := hyps_eImg_B hi P hn host
  obtain ⟨K, hK⟩ := qExp_QC (Round4Int.BI P hn host) hnb
  have hT := typFwd_gd (gd' := gdB) (typFwd_utf8Env HE)
  have hTb := typBwd_gd (gd' := gdB) (typBwd_utf8Env HE hK)
  rcases mem_excNames hnm with hh | hg
  · exact ⟨ruleFwd_host HB H' hT hTb hQA_QC hinj hf hp hb hh,
      ruleBwd_host HB H' hT hTb hQA_QC hi hinj hf hp hb hh⟩
  · exact ⟨ruleFwd_grow HE HB H' hT hTb hQA_QC hg, ruleBwd_grow HE HB H' hT hTb hQA_QC hg⟩

/-! ## The two halves of the swap at a configuration with the modules of `c` -/

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hb : HostExportBlind host) (hp : HostExportParam host) (P : Profile)
  {c d : Config H} (hi : StripInj c) (hnb : NamesBnd c) (hsub : ∀ m ∈ mods d, m ∈ mods c)
include hinj hf hb hp hi hnb hsub

/-- **Forward**: a step from the image of `stripConfig d` to the image of an export-free `e`
gives a step from the image of `d` to that of `mapConfig (unstrip c) e`. -/
theorem swapAt_fwd {e : Config H} (he : Stripped e)
    (h : SStepB (utf8Env (Round4Int.BI P hn host)) (configV hn (stripConfig d)) (configV hn e)) :
    SStepB (utf8Env (Round4Int.BI P hn host)) (configV hn d)
      (configV hn (mapConfig (unstrip c) e)) := by
  have ha : AllIn (QC c) (configV hn d) :=
    allIn_configV_of hn fun m hm => Or.inl ⟨m, hsub m hm, rfl⟩
  rw [← eraseV_configV] at h
  obtain ⟨h₁, h₂, h₃⟩ := sStepB_QC_bwd hi hnb P hn host
    (fun nm hnm => (excRules_QC hinj hf hb hp P hi hnb nm hnm).2) ha h
  rwa [← eq_configV_unstrip hn hi he h₁ h₂]

/-- **Backward**: a step from the image of `d` erases to a step from the image of
`stripConfig d`, and whenever that successor is the image of an export-free `e`, the original
one is the image of `mapConfig (unstrip c) e`. -/
theorem swapAt_bwd {w : Value}
    (h : SStepB (utf8Env (Round4Int.BI P hn host)) (configV hn d) w) :
    ∃ w₀, SStepB (utf8Env (Round4Int.BI P hn host)) (configV hn (stripConfig d)) w₀ ∧
      ∀ e : Config H, Stripped e → w₀ = configV hn e →
        w = configV hn (mapConfig (unstrip c) e) := by
  have ha : AllIn (QC c) (configV hn d) :=
    allIn_configV_of hn fun m hm => Or.inl ⟨m, hsub m hm, rfl⟩
  obtain ⟨h₁, h₂⟩ := sStepB_QC_fwd hi hnb P hn host
    (fun nm hnm => (excRules_QC hinj hf hb hp P hi hnb nm hnm).1) ha h
  rw [eraseV_configV] at h₁
  exact ⟨eraseV w, h₁, fun e he hw => eq_configV_unstrip hn hi he h₂ hw⟩

end

end Silmaril.Wasm.SpecTec.Sim.Round7.Runs
