module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.Step
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Round 7, memory SIMD: without a host condition, a Core step does not keep `NoMemSimd`

Core's host semantics is a relation, so a host call may return any store. The counterexample
reuses round 5's `srcCfg` (`ref.func 0; call_ref dt0` on `store0`, whose only function is a host
function of type `[] -> []`):

* `msFn`: a Wasm function of type `dt0` whose body is `v128.store`;
* `msHost`: the host whose every call returns `store0` with `msFn` appended, and no values. It is
  `HostFinite`, and not `HostKeepsMS`;
* `step_msSrc`: `srcCfg` steps (`call_ref-hostfunc-res`) to `⟨msStore, {}, []⟩`, at every
  profile. The source has no memory SIMD code, the successor has some in its store.

So `step_noMemSimd`'s host condition cannot be dropped, and `NoMSDom`'s successor condition is
not implied by `NoMemSimd` for every finite host.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Round5.Pos (dt0 hostFn store0 srcCfg srcCfg_eq expand_dt0)
open Round6.MemSimd (instrMS instrsMS AdminMS AdminsMS StoreMS NoMemSimd memSimd)
open Round7.MSPres (HostKeepsMS)

/-- A Wasm function of type `dt0` whose body is `v128.store` (memory 0, offset 0). -/
def msFn : FuncInst Unit :=
  { type := dt0, module := {}, code := .wasm ⟨⟨0⟩, [], [.vecStore ⟨0⟩ ⟨0, 0⟩]⟩ }

/-- `store0` with `msFn` appended. -/
def msStore : Store Unit := { funcs := [hostFn, msFn] }

/-- The host whose every call returns `msStore` and no values. -/
def msHost : HostSemantics Unit := fun _ _ _ o => o = .returned msStore (.values [])

theorem hostFinite_msHost : HostFinite msHost :=
  fun _ _ _ => ⟨[.returned msStore (.values [])], fun _ => by simp [msHost]⟩

/-- The successor of `srcCfg` under `msHost`. -/
def msDst : Config Unit := ⟨msStore, {}, []⟩

theorem step_msSrc (P : Profile) : Step P msHost srcCfg msDst :=
  Step.callRefHost (vs := []) (a := 0) (fi := hostFn) (ps := .nil) (rs := .nil) (h := ())
    (r := .values []) trivial rfl expand_dt0 rfl rfl rfl

theorem storeMS_store0 : StoreMS store0 := by
  intro fi hfi fn hc
  simp only [store0, List.mem_singleton] at hfi
  subst hfi
  cases hc

theorem noMemSimd_srcCfg : NoMemSimd srcCfg := by
  rw [srcCfg_eq]
  exact ⟨storeMS_store0, by simp [AdminsMS, AdminMS]⟩

theorem not_noMemSimd_msDst : ¬ NoMemSimd msDst := by
  intro h
  have := h.store msFn (by simp [msDst, msStore]) _ rfl
  simp [instrsMS, instrMS, memSimd] at this

theorem not_hostKeepsMS_msHost : ¬ HostKeepsMS msHost :=
  fun hh => not_noMemSimd_msDst
    ⟨hh () store0 [] msStore (.values []) rfl storeMS_store0, trivial⟩

/-- **A finite host can add memory SIMD code**: at every profile, a memory-SIMD-free
configuration steps to one with a memory SIMD function in its store. -/
theorem not_noMemSimd_preserved (P : Profile) :
    ∃ (host : HostSemantics Unit) (c c' : Config Unit), HostFinite host ∧ NoMemSimd c ∧
      Step P host c c' ∧ ¬ NoMemSimd c' :=
  ⟨msHost, srcCfg, msDst, hostFinite_msHost, noMemSimd_srcCfg, step_msSrc P,
    not_noMemSimd_msDst⟩

end Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres
