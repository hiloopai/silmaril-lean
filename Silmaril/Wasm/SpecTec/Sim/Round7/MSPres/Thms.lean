module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.Step
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.Refute
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.Rest
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.Host

/-!
# Round 7, memory SIMD: preservation of `NoMemSimd` by Core steps

* **Preservation** (`step_noMemSimd`, `steps_noMemSimd`): a Core step, at every profile, keeps
  `Round6.MemSimd.NoMemSimd` (no memory SIMD instruction in the code or in a Wasm function body of
  the store, at any depth) for a host that adds no memory SIMD code (`HostKeepsMS`). Code: every
  rule builds its result from values, constants, the bodies of the instruction it reduces, or a
  function body of the store (`call_ref-func`). Store: every rule but a returning host call keeps
  the function instances (`step_funcs`, from silmaril-lean's `framesLocal` lemmas).
* **The host condition is needed** (`not_noMemSimd_preserved`, `not_hostKeepsMS_msHost`): a
  finite host that returns a store with a `v128.store` function breaks preservation, at every
  profile.
* **Consequences for RM** (`noMSDom_of_noMemSimd`, `restMS_iff_restMSC`, `rest_of_restMSC`):
  for such a host `NoMSDom` is `NoCastVM ∧ NoMemSimd`, and `RestMS` is `RestMSC`, the obligations
  at configurations that themselves contain memory SIMD code. `wholeStepValidRMNoMSH_backend`:
  round 7's memory-SIMD-free restriction of the target holds without its successor condition.
* **`$hostcall` at `BM`** (`storeVD_ne_storeV`, `bm_hostcall_none`): a store with memory SIMD code
  in a Wasm function body has a `storeVD` image that is no `storeV` image, so `OpenRMRest`'s
  builtins `BM`, whose `$hostcall` answers only at `storeV` images, answer no host call made from
  such a store.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **A Core step keeps `NoMemSimd`** for a host that adds no memory SIMD code. -/
theorem step_noMemSimd {P : Profile} {host : HostSemantics H} (hh : HostKeepsMS host)
    {c c' : Config H} (h : Step P host c c') (hc : Round6.MemSimd.NoMemSimd c) :
    Round6.MemSimd.NoMemSimd c' :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.step_noMemSimd hh h hc

/-- **Runs keep `NoMemSimd`** for a host that adds no memory SIMD code. -/
theorem steps_noMemSimd {P : Profile} {host : HostSemantics H} (hh : HostKeepsMS host)
    {c c' : Config H} (h : Steps P host c c') (hc : Round6.MemSimd.NoMemSimd c) :
    Round6.MemSimd.NoMemSimd c' :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.steps_noMemSimd hh h hc

/-- **The host condition cannot be dropped.** -/
theorem not_noMemSimd_preserved (P : Profile) :
    ∃ (host : HostSemantics Unit) (c c' : Config Unit), HostFinite host ∧
      Round6.MemSimd.NoMemSimd c ∧ Step P host c c' ∧ ¬ Round6.MemSimd.NoMemSimd c' :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.not_noMemSimd_preserved P

/-- **`RestMS` is `RestMSC`** for a host that adds no memory SIMD code. -/
theorem restMS_iff_restMSC {hn : H → String} {P : Profile} {host : HostSemantics H}
    (hh : HostKeepsMS host) : Round7.VInv.RestMS hn P host ↔ RestMSC hn P host :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.restMS_iff_restMSC hh

/-- **The memory-SIMD-free restriction of the round-7 target without its successor
condition.** -/
theorem wholeStepValidRMNoMSH_backend : WholeStepValidRMNoMSH :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.wholeStepValidRMNoMSH_backend

/-- **A store with memory SIMD code has no `storeV` image at `storeVD`.** -/
theorem storeVD_ne_storeV (hn : H → String) {s : Store H} (hs : ¬ Round6.MemSimd.StoreMS s)
    (s' : Store H) : Round7.MemSimd.storeVD hn s ≠ storeV hn s' :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.storeVD_ne_storeV hn hs s'

/-- **`$hostcall` at `BM` is undefined at a store image with memory SIMD code.** -/
theorem bm_hostcall_none (P : Profile) (hn : H → String) (host : HostSemantics H) {s : Store H}
    (hs : ¬ Round6.MemSimd.StoreMS s) (x vs : Silmaril.SpecTec.Sem.Value) :
    (Round7.MemSimd.BM P hn host).call "hostcall"
      [.val x, .val (Round7.MemSimd.storeVD hn s), .val vs] = none :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.bm_hostcall_none P hn host hs x vs

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.step_noMemSimd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_noMemSimd

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.not_noMemSimd_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms not_noMemSimd_preserved

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.restMS_iff_restMSC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restMS_iff_restMSC

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.wholeStepValidRMNoMSH_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRMNoMSH_backend

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.bm_hostcall_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bm_hostcall_none

end Silmaril.Wasm.SpecTec.Sim.Round7.MSPres
