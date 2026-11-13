module

public import Silmaril.Wasm.JcoTool.KRead.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KRead.Main
public import Silmaril.Wasm.Component.Streams.NetGame.Thms
public import Silmaril.Wasm.JcoTool.KLive.Thms

/-!
# The game reading of the callback runtime: results

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KRead.{Obs,Step,Lift,Main}`.

* **`game_eq_den`** (no hypothesis): an observation that reads as `T` has the strategy reading
  `StreamGame.den T`; `reads_equiv`: the transformers one observation reads as are equivalent.
* **`unique_val`**: Core 3.0 with the built-ins as host calls (`HStep`) has unique value results
  in the deterministic profile, when distinct built-ins are distinct host functions.
* **`fwd_step`**: every drop-runtime step of a module whose callback is `CbSafe` is a step
  `CRStepU` of the runtime on Core 3.0. **`bwd_step`** (with unique value results, in the
  deterministic profile): conversely, every `CRStepU` step from a related Core store, where the
  callback is `CbSafe` and does not trap, is a drop-runtime step. So on Core the module does
  exactly what the model does.
* **`core_whole_iff`, `core_part_iff`** (for injective `hb` and a kernel whose bounds hold,
  `KLive.KFits`; the module then never traps, `KLive.genD_notrap_fits`): for the generated
  module `genD k N` on a Core store holding it
  (`Inst0`), the Core pipe has the same whole outputs and outputs so far as the model pipe.
* **`core_whole_correct`** (same hypotheses; no liveness): every finished Core pipe on `xs`
  holds `(trV k).run xs`.
* **`core_game`** (adding `FlushNil k`; liveness is `KLive.genD_reads_fits`): **the strategy reading
  of the Core runtime of `genD k N` is `StreamGame.den (trV k)`**, the stream game (and
  `NetGame.game`'s `den`) of the kernel. `core_game_comp`, `core_game_congr`: so the Core
  readings of generated modules compose as their kernels and equivalent kernels give equal
  readings.

Round 2's frozen targets `Task.genD_notrap`, `Task.genD_reads` are discharged for every kernel
whose bounds hold (`KLive.KFits`; e.g. every `KFit.Small` kernel). Not covered here: that Core
instantiation of `toModule (genD k N) name` gives an `Inst0` store, and the lift
`entry`, are not covered (as in `KCoreRun`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KRead

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core (Store ModuleInst)
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (BI Prog MS Mode trV)
open Silmaril.Wasm.JcoTool.KDrop (DRStep genD)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KLive (KFits)

variable {σ τ : Type} {H : Type} {hb : BI → H} {ma : Nat}

/-- **The strategy reading of an observation that reads as `T` is `den T`.** -/
theorem game_eq_den {O : Obs} {T : Tr σ Val Val} (h : O.Reads T) :
    O.game = Silmaril.Wasm.Component.Algebra.StreamGame.den T :=
  Silmaril.Proofs.Wasm.JcoTool.KRead.game_eq_den h

/-- The transformers one observation reads as are equivalent. -/
theorem reads_equiv {O : Obs} {T : Tr σ Val Val} {U : Tr τ Val Val} (hT : O.Reads T)
    (hU : O.Reads U) : T.Equiv U :=
  Silmaril.Proofs.Wasm.JcoTool.KRead.reads_equiv hT hU

/-- **A step of the drop runtime is a step of the runtime on Core** (result read unsigned). -/
theorem fwd_step (Pf : Profile) {P : Prog} {mi : ModuleInst} {a : Nat} {st st' : DStore}
    {ms ms' : MS} {cs : Store H} (hI : InstR hb ma cs mi ms.g ms.m) (hcb : CbAt cs mi P a)
    (hsafe : CbSafe P ms.g) (h : DRStep P st ms st' ms') :
    ∃ cs', CRStepU Pf hb ma a (st, cs, ms.rp, ms.mode) (st', cs', ms'.rp, ms'.mode) ∧
      InstR hb ma cs' mi ms'.g ms'.m ∧ CbAt cs' mi P a :=
  Silmaril.Proofs.Wasm.JcoTool.KRead.fwd_step Pf hI hcb hsafe h

/-- **Core with the built-ins as host calls has unique value results** (deterministic profile,
distinct built-ins distinct host functions). -/
theorem unique_val (hinj : Function.Injective hb) (o : GrowKind → Nat → Nat → Nat → Bool) :
    UniqueVal o hb ma := fun _ _ _ hy hz vy vz =>
  Silmaril.Proofs.Wasm.JcoTool.KRead.unique_val hinj o hy hz vy vz

/-- **A step of the runtime on Core is a step of the drop runtime** (with unique value results). -/
theorem bwd_step (o : GrowKind → Nat → Nat → Nat → Bool) (hu : UniqueVal o hb ma) {P : Prog}
    {mi : ModuleInst} {a : Nat} {st st' : DStore} {ms : MS} {cs cs' : Store H}
    {rp' : Option (Nat × Nat)} {md : Mode} (hI : InstR hb ma cs mi ms.g ms.m)
    (hcb : CbAt cs mi P a) (hsafe : CbSafe P ms.g) (hnt : NoTrap P st ms)
    (h : CRStepU (Profile.deterministic o) hb ma a (st, cs, ms.rp, ms.mode) (st', cs', rp', md)) :
    ∃ ms', DRStep P st ms st' ms' ∧ ms'.rp = rp' ∧ ms'.mode = md ∧ InstR hb ma cs' mi ms'.g ms'.m ∧
      CbAt cs' mi P a :=
  Silmaril.Proofs.Wasm.JcoTool.KRead.bwd_step o hu hI hcb hsafe hnt h

section
variable (hinj : Function.Injective hb) (o : GrowKind → Nat → Nat → Nat → Bool) {k : KM} {N : Nat}
  (hN : 0 < N ∧ N ≤ 256) (hfit : KFits k N)
  {mi : ModuleInst} {a : Nat} {cs₀ : Store H} (h0 : Inst0 hb ma a k N mi cs₀)
include hinj hN hfit h0

/-- **The Core pipe has the model pipe's whole outputs.** -/
theorem core_whole_iff (xs ys : List Val) :
    (coreObs (Profile.deterministic o) hb ma a k cs₀).whole xs ys ↔ (dropObs k N).whole xs ys :=
  Silmaril.Proofs.Wasm.JcoTool.KRead.core_whole_iff hinj
    (Silmaril.Wasm.JcoTool.KLive.genD_notrap_fits hN hfit) o hN h0 xs ys

/-- **The Core pipe has the model pipe's outputs so far.** -/
theorem core_part_iff (xs ys : List Val) :
    (coreObs (Profile.deterministic o) hb ma a k cs₀).part xs ys ↔ (dropObs k N).part xs ys :=
  Silmaril.Proofs.Wasm.JcoTool.KRead.core_part_iff hinj
    (Silmaril.Wasm.JcoTool.KLive.genD_notrap_fits hN hfit) o hN h0 xs ys

/-- **Every finished Core pipe of a generated module holds the kernel's whole output.** -/
theorem core_whole_correct {xs ys : List Val}
    (h : (coreObs (Profile.deterministic o) hb ma a k cs₀).whole xs ys) : ys = (trV k).run xs :=
  Silmaril.Proofs.Wasm.JcoTool.KRead.core_whole_correct hinj
    (Silmaril.Wasm.JcoTool.KLive.genD_notrap_fits hN hfit) o hN h0 h

/-- **The Core observation of `genD k N` reads as `trV k`.** -/
theorem core_reads (hk : FlushNil k) :
    (coreObs (Profile.deterministic o) hb ma a k cs₀).Reads (trV k) :=
  Silmaril.Proofs.Wasm.JcoTool.KRead.core_reads hinj
    (Silmaril.Wasm.JcoTool.KLive.genD_notrap_fits hN hfit) o hN h0
    (Silmaril.Wasm.JcoTool.KLive.genD_reads_fits hN hfit hk)

/-- **The game reading of the Core runtime of `genD k N` is the stream game of `trV k`.** -/
theorem core_game (hk : FlushNil k) :
    (coreObs (Profile.deterministic o) hb ma a k cs₀).game =
      Silmaril.Wasm.Component.Algebra.StreamGame.den (trV k) :=
  game_eq_den (core_reads hinj o hN hfit h0 hk)

end

/-- **The Core readings of two generated modules compose as their kernels.** -/
theorem core_game_comp (hinj : Function.Injective hb) (o : GrowKind → Nat → Nat → Nat → Bool)
    {k₁ k₂ : KM} {N₁ N₂ : Nat} (hN₁ : 0 < N₁ ∧ N₁ ≤ 256) (hN₂ : 0 < N₂ ∧ N₂ ≤ 256)
    (hf₁ : KFits k₁ N₁) (hf₂ : KFits k₂ N₂) (hk₁ : FlushNil k₁) (hk₂ : FlushNil k₂)
    {mi₁ mi₂ : ModuleInst} {a₁ a₂ : Nat} {cs₁ cs₂ : Store H}
    (h₁ : Inst0 hb ma a₁ k₁ N₁ mi₁ cs₁) (h₂ : Inst0 hb ma a₂ k₂ N₂ mi₂ cs₂) :
    ((coreObs (Profile.deterministic o) hb ma a₁ k₁ cs₁).game).comp
        (coreObs (Profile.deterministic o) hb ma a₂ k₂ cs₂).game =
      Silmaril.Wasm.Component.Algebra.StreamGame.den ((trV k₁).comp (trV k₂)) := by
  rw [core_game hinj o hN₁ hf₁ h₁ hk₁, core_game hinj o hN₂ hf₂ h₂ hk₂,
    Silmaril.Wasm.Component.Algebra.StreamGame.den_comp]

/-- **Generated modules of equivalent kernels have the same Core reading.** -/
theorem core_game_congr (hinj : Function.Injective hb) (o : GrowKind → Nat → Nat → Nat → Bool)
    {k₁ k₂ : KM} {N₁ N₂ : Nat} (hN₁ : 0 < N₁ ∧ N₁ ≤ 256) (hN₂ : 0 < N₂ ∧ N₂ ≤ 256)
    (hf₁ : KFits k₁ N₁) (hf₂ : KFits k₂ N₂) (hk₁ : FlushNil k₁) (hk₂ : FlushNil k₂)
    {mi₁ mi₂ : ModuleInst} {a₁ a₂ : Nat} {cs₁ cs₂ : Store H}
    (h₁ : Inst0 hb ma a₁ k₁ N₁ mi₁ cs₁) (h₂ : Inst0 hb ma a₂ k₂ N₂ mi₂ cs₂)
    (he : (trV k₁).Equiv (trV k₂)) :
    (coreObs (Profile.deterministic o) hb ma a₁ k₁ cs₁).game =
      (coreObs (Profile.deterministic o) hb ma a₂ k₂ cs₂).game := by
  rw [core_game hinj o hN₁ hf₁ h₁ hk₁, core_game hinj o hN₂ hf₂ h₂ hk₂]
  exact Silmaril.Wasm.Component.Algebra.StreamGame.den_congr he

end Silmaril.Wasm.JcoTool.KRead
