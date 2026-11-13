module

public import Silmaril.Wasm.Atlas.Wasmi.Defs
public import Silmaril.Wasm.Wasmi.Thms

/-!
# The wasmi and loose charts: transitions

* `coreToLooseUniv`, `coreToLooseExist`: Core → loose, inclusion of observations
  (`Silmaril.Wasm.Wasmi.Loose.core_le`): the loose chart's universal sentences are reflected,
  Core's existential sentences preserved;
* `toLooseUniv`, `toLooseExist`: wasmi → loose, the same on the wasmi domain
  (`Silmaril.Wasm.Wasmi.Loose.wasmi_le`);
* `disagree`: the reproducer's sentence `φ7` holds in the Core chart and fails in the wasmi
  chart (the reproducer is in the wasmi domain, `repro_dom`);
* `no_equal`: **there is no equality transition from Core to wasmi** that is the identity on
  points and sentences and covers `φ7`, even on the overlap `coreOn`;
* `toWasmiNF`: on the `NoFusedSelect` sub-domain the identity is an equality transition from
  Core to wasmi (`toWasmiNF_dir`), so the nonconformance is localised at the pattern;
* `transfer`: a universal sentence of the loose chart holds in Core and in wasmi.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Wasmi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Wasmi (φ7 reproPt)

variable {H : Type}

/-- **Core → loose, universal sentences.** -/
def coreToLooseUniv (P : Profile) (H : Type) : Transition (Core.chart P H) (looseChart P H) :=
  BTrans.ofSubsetUniv id id (fun _ _ => trivial) fun x _ c => Silmaril.Wasm.Wasmi.Loose.core_le P x c

/-- **Core → loose, existential sentences.** -/
def coreToLooseExist (P : Profile) (H : Type) : Transition (Core.chart P H) (looseChart P H) :=
  BTrans.ofSubsetExist id id (fun _ _ => trivial) fun x _ c => Silmaril.Wasm.Wasmi.Loose.core_le P x c

/-- **wasmi → loose, universal sentences.** -/
def toLooseUniv (P : Profile) (H : Type) : Transition (chart P H) (looseChart P H) :=
  BTrans.ofSubsetUniv id id (fun _ _ => trivial) fun _ hx c =>
    Silmaril.Wasm.Wasmi.Loose.wasmi_le P hx.2 c

/-- **wasmi → loose, existential sentences.** -/
def toLooseExist (P : Profile) (H : Type) : Transition (chart P H) (looseChart P H) :=
  BTrans.ofSubsetExist id id (fun _ _ => trivial) fun _ hx c =>
    Silmaril.Wasm.Wasmi.Loose.wasmi_le P hx.2 c

/-- The reproducer is in the wasmi domain. -/
theorem repro_dom : Dom reproPt :=
  ⟨Silmaril.Wasm.Wasmi.repro_supported, Silmaril.Wasm.Wasmi.repro_hostParametric⟩

/-- **Disagreement in the atlas**, every profile. -/
theorem disagree (P : Profile) :
    (Core.chart P Empty).Sat reproPt φ7 ∧ ¬ (chart P Empty).Sat reproPt φ7 :=
  Silmaril.Wasm.Wasmi.disagree P

/-- **No equality transition from Core to wasmi**: no transition from the Core chart on the
wasmi domain to the wasmi chart is the identity on points and sentences, records `equal`, and
covers the reproducer's sentence. -/
theorem no_equal (P : Profile) :
    ¬ ∃ T : Transition (coreOn P Empty) (chart P Empty),
      T.pt = id ∧ T.sen = id ∧ T.dir = .equal ∧ T.cls φ7 := by
  rintro ⟨T, hpt, hsen, hdir, hcls⟩
  have hrel : T.dir.Rel ((coreOn P Empty).Sat reproPt φ7)
      ((chart P Empty).Sat (T.pt reproPt) (T.sen φ7)) := T.sat reproPt φ7 repro_dom hcls
  have hfwd : (coreOn P Empty).Sat reproPt φ7 → (chart P Empty).Sat reproPt φ7 := by
    have h := hrel.1 (by rw [hdir]; rfl)
    rwa [hpt, hsen] at h
  exact (disagree P).2 (hfwd (disagree P).1)

/-- **Equality on the `NoFusedSelect` sub-domain**: the identity from Core to wasmi. -/
def toWasmiNF (P : Profile) (H : Type) : Transition (coreNF P H) (chart P H) :=
  BTrans.ofEq id id (fun _ hx => hx.1) fun _ hx c => Silmaril.Wasm.Wasmi.obs_of_patFree P hx.2 c

theorem toWasmiNF_dir (P : Profile) (H : Type) : (toWasmiNF P H).dir = .equal := rfl

/-- **Transfer** of universal sentences from the loose chart to Core and to wasmi. -/
theorem transfer (P : Profile) {x : Core.Pt H} (hx : Dom x) {φ : BSen Core.Call (Behaviour Val)}
    (hu : φ.Universal) (h : (looseChart P H).Sat x φ) :
    (Core.chart P H).Sat x φ ∧ (chart P H).Sat x φ :=
  Silmaril.Wasm.Wasmi.Loose.transfer P h hu hx.2

end Silmaril.Wasm.Atlas.Wasmi
