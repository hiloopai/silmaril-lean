module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Chain2030Witness

/-!
# The chain wasm-2.0 → wasm-3.0 where one V2 step is one Core step

On `PairDom1` (`PairDom`, `OneFwd`, `OneBwd`) the V2 successors of the first component and the
Core successors of the second are related both ways by `SimV`, so the V2 step chart and the Core
step chart are equal on `SimV`-respecting sentences, universal, existential and value-sensitive
alike (`v2ToCore1`). Composed with `Wasm30.toModel`:

* `v2ToModel1`: V2 to the wasm-3.0 model, **equal** on sentences respecting `SimV` and `CfgRel`.
* `chainExist1`: the wasm-2.0 model to the wasm-3.0 model, preserving existential such sentences.
* `chainUniv1`: the wasm-2.0 model to the wasm-3.0 model, reflecting universal such sentences.

The wasm-2.0 model is only a sub-model of V2 (`Wasm20.model_subset_v2`), so from it the chain
stays one-directional per sentence kind. `progress_not_equal` shows that this cannot be helped on
`PairDom`: at `nop nop` the wasm-2.0 model is stuck and the wasm-3.0 model steps.

`CodeNil` (the encoded code is empty) is a value-sensitive predicate respecting `SimV` and
`CfgRel` (`codeNil_respects_simV`, `codeNil_respects_cfgRel`). At `nop`, `may () CodeNil` goes
from the wasm-2.0 model to the wasm-3.0 model and `always () CodeNil` comes back
(`nop1_codeNil`); neither sentence is value-blind.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Chain2030

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Institution

variable {H : Type}

/-! ## V2 and Core on the one-step sub-fragment -/

section One

variable {P : Profile} {host : Silmaril.Wasm.V2.Execution.HostSemantics H}
  {tgt : Silmaril.Wasm.Execution.Core.HostSemantics H} {hn : H → String}

/-- V2 successors are Core successors up to `SimV`. -/
theorem fwd1 {p : Pair H} (hp : PairDom1 P host tgt p) (u : Unit) :
    ∀ b ∈ Wasm20.v2Obs P host hn p.1 u,
      ∃ b' ∈ Atlas.SpecTec.coreObs P tgt hn p.2 u, SimV hn b b' := by
  rintro b ⟨c', hs, rfl⟩
  obtain ⟨cc', hs', hsim⟩ := hp.2.1 c' hs
  exact ⟨_, ⟨cc', hs', rfl⟩, c', cc', hsim, rfl, rfl⟩

/-- Core successors are V2 successors up to `SimV`. -/
theorem bwd1 {p : Pair H} (hp : PairDom1 P host tgt p) (u : Unit) :
    ∀ b' ∈ Atlas.SpecTec.coreObs P tgt hn p.2 u,
      ∃ b ∈ Wasm20.v2Obs P host hn p.1 u, SimV hn b b' := by
  rintro b' ⟨cc', hs, rfl⟩
  obtain ⟨c', hs', hsim⟩ := hp.2.2 cc' hs
  exact ⟨_, ⟨c', hs', rfl⟩, c', cc', hsim, rfl, rfl⟩

end One

/-- **V2 to Core on the one-step sub-fragment**: equal on every `SimV`-respecting sentence. -/
def v2ToCore1 (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (hn : H → String) :
    Transition (v2PChart1 P host tgt hn)
      (Atlas.SpecTec.coreChart P tgt hn (Wasm30.DomDet P tgt)) :=
  BTrans.ofUpTo (SimV hn) Prod.snd id (fun _ hp => hp.1.2.2)
    (fun _ hp u => fwd1 hp u) (fun _ hp u => bwd1 hp u)

/-- The wasm-2.0 model to V2 on the one-step sub-fragment, existential sentences
(`Wasm20.model_subset_v2`). -/
noncomputable def toV2Exist1 (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (hn : H → String) :
    Transition (m20Chart1 P host tgt hn) (v2PChart1 P host tgt hn) :=
  BTrans.ofSubsetExist id id (fun _ h => h)
    (fun p hp u => Wasm20.model_subset_v2 P host hn p.1 hp.1.1 u)

/-- The wasm-2.0 model to V2 on the one-step sub-fragment, universal sentences, reflected. -/
noncomputable def toV2Univ1 (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (hn : H → String) :
    Transition (m20Chart1 P host tgt hn) (v2PChart1 P host tgt hn) :=
  BTrans.ofSubsetUniv id id (fun _ h => h)
    (fun p hp u => Wasm20.model_subset_v2 P host hn p.1 hp.1.1 u)

section Chain

variable (hn : H → String) (hinj : Function.Injective hn)
  (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
  (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H)
  (hf : Silmaril.Wasm.SpecTec.Sim.HostFinite tgt) (hh : Silmaril.Wasm.Execution.Core.HostOk tgt)
  (nd : Bool) (r : RelaxedChoice)

/-- **V2 to the wasm-3.0 model on the one-step sub-fragment**: `v2ToCore1` and
`Wasm30.toModel`, equal on sentences respecting `SimV` and `CfgRel`. -/
noncomputable def v2ToModel1 :
    Transition (v2PChart1 (Profile.spec nd r) host tgt hn)
      (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))) :=
  (v2ToCore1 (Profile.spec nd r) host tgt hn).comp (Wasm30.toModel hn hinj tgt hf hh nd r)

/-- `v2ToModel1` is equal. -/
theorem v2ToModel1_dir : (v2ToModel1 hn hinj host tgt hf hh nd r).dir = Dir.equal := rfl

/-- **Existential sentences, wasm-2.0 model to wasm-3.0 model**, on the one-step sub-fragment. -/
noncomputable def chainExist1 :
    Transition (m20Chart1 (Profile.spec nd r) host tgt hn)
      (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))) :=
  (toV2Exist1 (Profile.spec nd r) host tgt hn).comp (v2ToModel1 hn hinj host tgt hf hh nd r)

/-- `chainExist1` preserves. -/
theorem chainExist1_dir : (chainExist1 hn hinj host tgt hf hh nd r).dir = Dir.preserves := rfl

/-- **Universal sentences, wasm-3.0 model to wasm-2.0 model**, on the one-step sub-fragment. -/
noncomputable def chainUniv1 :
    Transition (m20Chart1 (Profile.spec nd r) host tgt hn)
      (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))) :=
  (toV2Univ1 (Profile.spec nd r) host tgt hn).comp (v2ToModel1 hn hinj host tgt hf hh nd r)

/-- `chainUniv1` reflects. -/
theorem chainUniv1_dir : (chainUniv1 hn hinj host tgt hf hh nd r).dir = Dir.reflects := rfl

/-- **On the one-step sub-fragment, V2 and the wasm-3.0 model agree** on every sentence that
respects `SimV` and `CfgRel`, universal, existential or mixed. -/
theorem sat_iff_v2_model1 {p : Pair H} (hp : PairDom1 (Profile.spec nd r) host tgt p)
    {s : BSen Unit Value} (h₁ : s.Respects (SimV hn)) (h₂ : s.Respects (Atlas.SpecTec.CfgRel hn)) :
    (v2PChart1 (Profile.spec nd r) host tgt hn).Sat p s ↔
      (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))).Sat
        (Silmaril.Wasm.SpecTec.Sim.configV hn p.2) s := by
  have e := (v2ToModel1 hn hinj host tgt hf hh nd r).sat p s hp
    ⟨h₁, BSen.respects_rename id h₂⟩
  simp only [v2ToModel1, Transition.comp, v2ToCore1, BTrans.ofUpTo, Wasm30.toModel,
    BSen.rename_id] at e
  exact ⟨e.1 rfl, e.2 rfl⟩

/-- **Existential sentences go from the wasm-2.0 model to the wasm-3.0 model** on the one-step
sub-fragment, value-sensitive ones included. -/
theorem exist_chain1 {p : Pair H} (hp : PairDom1 (Profile.spec nd r) host tgt p)
    {s : BSen Unit Value} (he : s.Existential) (h₁ : s.Respects (SimV hn))
    (h₂ : s.Respects (Atlas.SpecTec.CfgRel hn))
    (h : (m20Chart1 (Profile.spec nd r) host tgt hn).Sat p s) :
    (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))).Sat
      (Silmaril.Wasm.SpecTec.Sim.configV hn p.2) s :=
  (sat_iff_v2_model1 hn hinj host tgt hf hh nd r hp h₁ h₂).1
    (BSen.sat_of_subset_exist (Wasm20.model_subset_v2 _ host hn p.1 hp.1.1) he h)

/-- **Universal sentences go from the wasm-3.0 model to the wasm-2.0 model** on the one-step
sub-fragment, value-sensitive ones included. -/
theorem univ_chain1 {p : Pair H} (hp : PairDom1 (Profile.spec nd r) host tgt p)
    {s : BSen Unit Value} (hu : s.Universal) (h₁ : s.Respects (SimV hn))
    (h₂ : s.Respects (Atlas.SpecTec.CfgRel hn))
    (h : (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))).Sat
      (Silmaril.Wasm.SpecTec.Sim.configV hn p.2) s) :
    (m20Chart1 (Profile.spec nd r) host tgt hn).Sat p s :=
  BSen.sat_of_subset_univ (Wasm20.model_subset_v2 _ host hn p.1 hp.1.1) hu
    ((sat_iff_v2_model1 hn hinj host tgt hf hh nd r hp h₁ h₂).2 h)

end Chain

/-! ## The chain is not equal on progress -/

open Silmaril.Wasm.SingleThreaded.Det (noHost)

section NotEqual

variable (hn : H → String) (hinj : Function.Injective hn)
  (hf : Silmaril.Wasm.SpecTec.Sim.HostFinite (noHost (H := H)))
  (hh : Silmaril.Wasm.Execution.Core.HostOk (noHost (H := H))) (nd : Bool) (r : RelaxedChoice)

/-- The wasm-2.0 model does not step at `nop nop`. -/
theorem m20_not_progress_nop (P : Profile) :
    ¬ (m20Chart P (noHost (H := H)) hn).Sat nopPair Wasm20.progress :=
  Wasm20.not_model_progress_nop _ hn

/-- **The wasm-3.0 model steps at `nop nop`**: Core does, and `nop nop` is in `DomDet`. -/
theorem model30_progress_nop :
    (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj noHost hf hh nd r))).Sat
      (Silmaril.Wasm.SpecTec.Sim.configV hn coreNop) Wasm20.progress :=
  (Wasm30.sat_iff_stepModel hn hinj noHost hf hh nd r (domDet_coreNop _)
    (s := Wasm20.progress) (fun _ _ _ => Iff.rfl)).1 ⟨_, ⟨coreNop1, step_coreNop _ _, rfl⟩, trivial⟩

/-- **No transition along the chain's point map reflects progress**: any transition from the
wasm-2.0 model's chart on `PairDom` to the wasm-3.0 model's chart that sends `nopPair` to the
image of `coreNop` (as `chain` does, `chain_pt`), fixes `progress` and has it in its class, does
not reflect. -/
theorem progress_not_bwd
    (T : Transition (m20Chart (Profile.spec nd r) noHost hn)
      (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj noHost hf hh nd r))))
    (hpt : T.pt nopPair = Silmaril.Wasm.SpecTec.Sim.configV hn coreNop)
    (hsen : T.sen Wasm20.progress = Wasm20.progress) (hcls : T.cls Wasm20.progress) :
    T.dir.bwd = false := by
  cases hd : T.dir.bwd
  · rfl
  · have hm := model30_progress_nop hn hinj hf hh nd r
    rw [← hpt, ← hsen] at hm
    exact absurd ((T.sat nopPair _ (pairDom_nop _) hcls).2 hd hm) (m20_not_progress_nop hn _)

/-- **So the chain cannot be upgraded to `equal` on progress.** -/
theorem progress_not_equal
    (T : Transition (m20Chart (Profile.spec nd r) noHost hn)
      (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj noHost hf hh nd r))))
    (hpt : T.pt nopPair = Silmaril.Wasm.SpecTec.Sim.configV hn coreNop)
    (hsen : T.sen Wasm20.progress = Wasm20.progress) (hcls : T.cls Wasm20.progress) :
    T.dir ≠ Dir.equal := fun h => by
  have := progress_not_bwd hn hinj hf hh nd r T hpt hsen hcls
  rw [h] at this
  exact absurd this (by decide)

/-- **At `nopPair` the chain's progress statement has no converse**: the wasm-3.0 model steps at
the chain's image of `nopPair`, the wasm-2.0 model does not step at `nopPair`. -/
theorem chain_progress_strict {host : Silmaril.Wasm.V2.Execution.HostSemantics H}
    (hc : Silmaril.Wasm.V2.Execution.HostCompatible host noHost) :
    (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj noHost hf hh nd r))).Sat
        ((chain hn hinj host noHost hf hh nd r hc).pt nopPair) Wasm20.progress ∧
      ¬ (m20Chart (Profile.spec nd r) noHost hn).Sat nopPair Wasm20.progress :=
  ⟨model30_progress_nop hn hinj hf hh nd r, m20_not_progress_nop hn _⟩

end NotEqual

/-! ## A value-sensitive example: the code is empty -/

/-- `CodeNil` of a Core configuration's image: its code is empty. -/
theorem codeNil_configV {hn : H → String} (c : Silmaril.Wasm.Execution.Core.Config H) :
    CodeNil (Silmaril.Wasm.SpecTec.Sim.configV hn c) ↔ c.code = [] := by
  rcases c with ⟨s, f, _ | ⟨a, l⟩⟩ <;>
    simp [CodeNil, Silmaril.Wasm.SpecTec.Sim.configV, Silmaril.Wasm.SpecTec.Sim.adminsToV]

/-- `CodeNil` of a V2 configuration's image: its code is empty. -/
theorem codeNil_configV20 {hn : H → String} (c : Silmaril.Wasm.V2.Execution.Config H) :
    CodeNil (Silmaril.Wasm.SpecTec.Sim20.configV hn c) ↔ c.code = [] := by
  rcases c with ⟨s, f, _ | ⟨a, l⟩⟩ <;>
    simp [CodeNil, Silmaril.Wasm.SpecTec.Sim20.configV, Silmaril.Wasm.SpecTec.Sim20.adminsToV]

/-- The Core image of a V2 instruction is never empty. -/
theorem admin_toCore_ne_nil {s : Silmaril.Wasm.V2.Execution.Store H}
    {a : Silmaril.Wasm.V2.Execution.Admin} {x : List Silmaril.Wasm.Execution.Core.Admin}
    (h : Silmaril.Wasm.V2.Execution.Admin.toCore s a = some x) : x ≠ [] := by
  rcases a <;> simp [Silmaril.Wasm.V2.Execution.Admin.toCore, Option.map_eq_some_iff,
    Option.bind_eq_some_iff] at h <;> grind

/-- The Core image of a V2 code sequence is empty exactly when the sequence is. -/
theorem listToCore_eq_nil {s : Silmaril.Wasm.V2.Execution.Store H} :
    ∀ {code : List Silmaril.Wasm.V2.Execution.Admin} {x : List Silmaril.Wasm.Execution.Core.Admin},
      Silmaril.Wasm.V2.Execution.Admin.listToCore s code = some x → (x = [] ↔ code = [])
  | [], x, h => by simp_all [Silmaril.Wasm.V2.Execution.Admin.listToCore]
  | a :: l, x, h => by
    simp only [Silmaril.Wasm.V2.Execution.Admin.listToCore, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨y, hy, z, -, rfl⟩ := h
    simp [admin_toCore_ne_nil hy]

/-- Normalisation keeps the code empty or nonempty. -/
theorem normList_eq_nil (m : Silmaril.Wasm.Execution.Core.ModuleInst) :
    ∀ {l : List Silmaril.Wasm.Execution.Core.Admin},
      Silmaril.Wasm.V2.Execution.ToCore.Admin.normList m l = [] ↔ l = []
  | [] => by simp [Silmaril.Wasm.V2.Execution.ToCore.Admin.normList]
  | _ :: _ => by simp [Silmaril.Wasm.V2.Execution.ToCore.Admin.normList]

/-- **`Sim` keeps the code empty or nonempty.** -/
theorem sim_code_nil {c : Silmaril.Wasm.V2.Execution.Config H}
    {cc : Silmaril.Wasm.Execution.Core.Config H} (h : Silmaril.Wasm.V2.Execution.Sim c cc) :
    c.code = [] ↔ cc.code = [] := by
  have h₁ := h.1
  simp only [Silmaril.Wasm.V2.Execution.Config.toCore, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at h₁
  obtain ⟨_, -, x, hx, he⟩ := h₁
  have hc : x = Silmaril.Wasm.V2.Execution.ToCore.Admin.normList cc.frame.module cc.code :=
    congrArg Silmaril.Wasm.Execution.Core.Config.code he
  rw [← listToCore_eq_nil hx, hc, normList_eq_nil]

/-- `CALL_REF`-annotation equivalence keeps the code empty or nonempty. -/
theorem codeEq_nil {l l' : List Silmaril.Wasm.Execution.Core.Admin}
    (h : Silmaril.Wasm.SpecTec.Sim.Bwd.CodeEq l l') : l = [] ↔ l' = [] := by
  cases h <;> simp

/-- **`CodeNil` respects `SimV`.** -/
theorem codeNil_respects_simV {hn : H → String} :
    ∀ b b', SimV hn b b' → (CodeNil b ↔ CodeNil b') := by
  rintro _ _ ⟨c, cc, hs, rfl, rfl⟩
  rw [codeNil_configV20, codeNil_configV]
  exact sim_code_nil hs

/-- **`CodeNil` respects `CfgRel`.** -/
theorem codeNil_respects_cfgRel {hn : H → String} :
    ∀ b b', Atlas.SpecTec.CfgRel hn b b' → (CodeNil b ↔ CodeNil b') := by
  rintro _ _ ⟨c, d, he, rfl, rfl⟩
  rw [codeNil_configV, codeNil_configV]
  exact codeEq_nil he.2.2

/-- `may () CodeNil` is not value-blind: `CodeNil` fails at the image of `nop`. -/
theorem not_blind_codeNil (hn : H → String) : ¬ Blind (.may () CodeNil) := fun h =>
  absurd ((codeNil_configV (hn := hn) coreNop1).1 (h _)) (by simp [coreNop1])

/-- **A value-sensitive sentence in both directions, at `nop`**: the wasm-2.0 model has a step
to empty code, so (by `exist_chain1`) the wasm-3.0 model has one; every step of the wasm-3.0
model is to empty code (Core's only step is, and `Wasm30.toModel`), so (by `univ_chain1`) every
step of the wasm-2.0 model is. Neither sentence is value-blind (`not_blind_codeNil`). -/
theorem nop1_codeNil (hn : H → String) (hinj : Function.Injective hn)
    (hf : Silmaril.Wasm.SpecTec.Sim.HostFinite (noHost (H := H)))
    (hh : Silmaril.Wasm.Execution.Core.HostOk (noHost (H := H))) (nd : Bool) (r : RelaxedChoice)
    {host : Silmaril.Wasm.V2.Execution.HostSemantics H}
    (hc : Silmaril.Wasm.V2.Execution.HostCompatible host noHost) :
    (m20Chart1 (Profile.spec nd r) host noHost hn).Sat nop1Pair (.may () CodeNil) ∧
    (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj noHost hf hh nd r))).Sat
      (Silmaril.Wasm.SpecTec.Sim.configV hn coreNop1) (.may () CodeNil) ∧
    (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj noHost hf hh nd r))).Sat
      (Silmaril.Wasm.SpecTec.Sim.configV hn coreNop1) (.always () CodeNil) ∧
    (m20Chart1 (Profile.spec nd r) host noHost hn).Sat nop1Pair (.always () CodeNil) := by
  have hp := pairDom1_nop1 (Profile.spec nd r) hc
  have h₁ : (BSen.may () CodeNil).Respects (SimV hn) := codeNil_respects_simV
  have h₂ : (BSen.may () CodeNil).Respects (Atlas.SpecTec.CfgRel hn) := codeNil_respects_cfgRel
  have hm : (m20Chart1 (Profile.spec nd r) host noHost hn).Sat nop1Pair (.may () CodeNil) :=
    ⟨_, Wasm20.model_step_nop1 _ hn, (codeNil_configV20 v2Done).2 rfl⟩
  have ha : (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj noHost hf hh nd r))).Sat
      (Silmaril.Wasm.SpecTec.Sim.configV hn coreNop1) (.always () CodeNil) := by
    refine (Wasm30.sat_iff_stepModel hn hinj noHost hf hh nd r (domDet_coreNop1 _)
      (s := .always () CodeNil) codeNil_respects_cfgRel).1 ?_
    rintro _ ⟨c', hs, rfl⟩
    rw [step_coreNop1_iff.1 hs, codeNil_configV]
    rfl
  exact ⟨hm, exist_chain1 hn hinj host noHost hf hh nd r hp trivial h₁ h₂ hm, ha,
    univ_chain1 hn hinj host noHost hf hh nd r hp trivial codeNil_respects_simV
      codeNil_respects_cfgRel ha⟩

end Silmaril.Wasm.SpecTec.Institution.Chain2030
