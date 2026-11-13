module

public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Config.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Oracle.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs
public import Silmaril.Foundations.InfiniteTrace.Deterministic
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Machine.Step`: laws of the component reference

Theorems of the component reference copy `Machine.Step`, refined out of
`Silmaril.Raw.Wasm.Component.Machine.Step`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
variable {E : CoreEngine} {σ : Type}
open StepDefs

namespace Steps

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

theorem cons_iff {m m' : Config E σ} {l : Label E σ} {tr : List (Label E σ)} :
    Steps prof hr dispatch m (l :: tr) m' ↔
      ∃ m₁, Step prof hr dispatch m l m₁ ∧ Steps prof hr dispatch m₁ tr m' := by
  constructor
  · rintro (_ | ⟨s, r⟩); exact ⟨_, s, r⟩
  · rintro ⟨_, s, r⟩; exact .cons s r

end Steps

section Basic

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

/-- Host events happen only when the host may act. -/
theorem Step.host_ready {m m' : Config E σ} {ev : HostEvent E σ}
    (h : Step prof hr dispatch m (.host ev) m') : HostReadyCfg m := by
  cases h <;> assumption

/-- With the host in control (`ctl = []`) the only steps are host events: `Resolved`,
`Trapped` and `Deadlocked` configurations have no internal step. -/
theorem Step.host_of_ctl_nil {m m' : Config E σ} {l : Label E σ} (hc : m.ctl = [])
    (h : Step prof hr dispatch m l m') : ∃ ev, l = .host ev := by
  cases h with
  | hostInvoke => exact ⟨_, rfl⟩
  | hostTick => exact ⟨_, rfl⟩
  | hostCancel => exact ⟨_, rfl⟩
  | hostRun => exact ⟨_, rfl⟩
  | fault f => cases f <;> simp_all
  | _ => simp_all

/-- No internal step from a host-in-control configuration. -/
theorem not_internalStep_of_ctl_nil {m m' : Config E σ} (hc : m.ctl = []) :
    ¬ InternalStep prof hr dispatch m m' := by
  rintro ⟨l, hl, h⟩
  obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc h
  exact hl ev rfl

/-- Host-in-control configurations do not diverge. -/
theorem not_diverges_of_ctl_nil {m : Config E σ} (hc : m.ctl = []) :
    ¬ Diverges prof hr dispatch m := by
  intro d
  obtain ⟨_, s, _⟩ := d.unfold
  exact not_internalStep_of_ctl_nil hc s

end Basic

end Silmaril.Wasm.Component.Machine
