module

public import Silmaril.Proofs.Wasm.Models.V2CoreSpec.Spec

/-!
# Single allocation is included in the spec's double allocation, with hosts blind to globals

`once_sub_spec` (`Spec.lean`) is host-free. Here the host is any Core host that keeps the
store's globals and functions and does not read them (`GlobalsBlind`):

* `noHostC_blind`, `pureHost_blind`: the empty host, and every host that leaves the store
  unchanged and answers from the host function and the arguments only, are blind;
* **`once_sub_spec_host`**: every single-allocation instantiation run has a spec
  `$instantiate` run with the same behaviours **with that host**, at every profile, for a
  store satisfying `GlobalsNamed`; the behaviours move by
  `Silmaril.Wasm.Game.spec_behaviours_eq_residue_host` (the step simulation with a host,
  `Silmaril.Proofs.Wasm.Game.SpecGlobals.stepH`);
* **`coreInstObsOnce_sub_spec_host`**: at points with a blind host, single-allocation
  instantiation observations are spec observations.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpec

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The empty host is blind to globals and functions. -/
theorem noHostC_blind : GlobalsBlind (noHostC : HostSemantics H) :=
  ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- Pure hosts are blind to globals and functions. -/
theorem pureHost_blind (F : H → List Val → Result → Prop) (G : H → List Val → Prop) :
    GlobalsBlind (pureHost F G) where
  keeps _ _ _ _ _ hh := by
    rcases hh with ⟨_, _, he⟩ | ⟨_, he⟩
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  ret _ _ _ _ _ _ _ hh := by
    rcases hh with ⟨r', hr, he⟩ | ⟨_, he⟩
    · cases he
      exact Or.inl ⟨_, hr, rfl⟩
    · cases he
  div _ _ _ _ _ hh := by
    rcases hh with ⟨_, _, he⟩ | ⟨hg, -⟩
    · cases he
    · exact Or.inr ⟨hg, rfl⟩

/-- **Single allocation is included in the spec's double allocation with a host blind to
globals**, with the same behaviours (with that host) at every profile. -/
theorem once_sub_spec_host {P : Profile} {host : HostSemantics Nat} (hb : GlobalsBlind host)
    {s : Store Nat} (hs : GlobalsNamed s) {m : Module} {xas : List ExternAddr} {C : Config Nat}
    (h : Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P host s m xas C) :
    ∃ C', Instantiate P host s m xas C' ∧
      ∀ P' : Profile, behavioursOf P' host C' = behavioursOf P' host C := by
  obtain ⟨xtE, xtI, -, hxas⟩ := h.1
  obtain ⟨s₁, f₁, vs, c₁, st, hg, hp, rfl⟩ := once_prepare h
  obtain ⟨c, hc, hbeh⟩ :=
    Silmaril.Wasm.Game.spec_behaviours_eq_residue_host hb.keeps hb.ret hb.div hs hxas hg hp
  have hI : Instantiate P host s m xas (c.withStart st) :=
    (prepare?_iff h.1).mp (by rw [hc]; rfl)
  exact ⟨c.withStart st, hI, hbeh⟩

/-- **Single-allocation instantiation observations are spec observations**, at points with a
host blind to globals. -/
theorem coreInstObsOnce_sub_spec_host (P : Profile) {s : Store Nat} {host : HostSemantics Nat}
    (hb : GlobalsBlind host) (hs : GlobalsNamed s) (cm : Module) (cxas : List ExternAddr) :
    Silmaril.Proofs.Wasm.Models.V2CoreInst.coreInstObsOnce P (s, host) (cm, cxas) ⊆
      Silmaril.Proofs.Wasm.Models.V2Core.coreInstObs P (s, host) (cm, cxas) := by
  rintro b ⟨C, hC, hbm⟩
  obtain ⟨C', hC', hbeh⟩ := once_sub_spec_host hb hs hC
  have hb' : b ∈ behavioursOf P host C' := by
    rw [hbeh P]
    exact hbm
  exact ⟨C', hC', hb'⟩

end Silmaril.Proofs.Wasm.Models.V2CoreSpec
