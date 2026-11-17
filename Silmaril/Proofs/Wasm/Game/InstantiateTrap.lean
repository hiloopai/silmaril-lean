module

public import Silmaril.Wasm.Execution.InstantiateTrap.Thms
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
public import Silmaril.Wasm.Game.SpecGlobals.Thms
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.SingleThreaded.Soundness

/-!
# Proofs: completeness of the trap-aware instantiation

`instantiateT?_ne_fail_iff`: for a valid module, imports of the import types and a typed store,
`instantiateT?` ends in a result or a trap exactly when an `Instantiate` derivation exists
(`exists_instantiate_iff_prepare?_isSome`, `Game.prepare_segments_not_fail`).
`instantiateCfg?_configOk`: the configuration of `instantiateCfg?` is typed (`Instantiate.ok`
carried along the run of `instantiateCfg?_sound`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.InstantiateTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

theorem instantiateT?_ne_fail_iff {P : Profile} {host : HostSemantics Nat} {s : Store Nat}
    {m : Module} {xas : List ExternAddr} {xtI xtE : List CExternType}
    (hm : ModuleOk m ⟨xtI, xtE⟩) (hs : StoreOk s) (hx : List.Forall₂ (ExternAddrOk s) xas xtI) :
    instantiateT? s m xas ≠ .fail ↔ ∃ c, Instantiate P host s m xas c := by
  have hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI :=
    ⟨xtE, xtI, hm, hx⟩
  constructor
  · intro hne
    cases h : instantiateT? s m xas with
    | ok s' f st =>
      obtain ⟨c, -, -, hI, -⟩ := instantiateT?_ok_sound (P := P) (host := host) hvalid h
      exact ⟨_, hI⟩
    | trap s' =>
      obtain ⟨c, st, -, -, hI, -⟩ := instantiateT?_trap_sound (P := P) (host := host) hvalid h
      exact ⟨_, hI⟩
    | fail => exact absurd h hne
  · intro hI hf
    have hp := (exists_instantiate_iff_prepare?_isSome hvalid).1 hI
    rcases instantiateT?_eq_fail_iff.1 hf with hn | ⟨c, st, hp', hseg⟩
    · rw [hn] at hp; cases hp
    · exact Game.prepare_segments_not_fail hm hs hx hp' hseg

theorem instantiateCfg?_configOk {s : Store Nat} {m : Module} {xas : List ExternAddr}
    {mt : CModuleType} {c : Config Nat} {mi : ModuleInst} (hs : StoreOk s) (hm : ModuleOk m mt)
    (hx : List.Forall₂ (ExternAddrOk s) xas mt.imports) (h : instantiateCfg? s m xas = some (c, mi)) :
    ConfigOk c [] := by
  obtain ⟨c₀, hI, -, hS⟩ := instantiateCfg?_sound (P := SingleThreaded.profile SingleThreaded.neverFail)
    (host := SingleThreaded.divHost) ⟨mt.exports, mt.imports, hm, hx⟩ h
  have hc₀ := Instantiate.ok SingleThreaded.divHost_ok hs hI
  clear hI h
  induction hS with
  | refl => exact hc₀
  | tail _ hst ih => exact (Step.preservation SingleThreaded.divHost_ok ih hst).1

end Silmaril.Proofs.Wasm.Game.InstantiateTrap

end
