module

public import Silmaril.Wasm.Game.Start.Defs
public import Silmaril.Wasm.Game.DivAdequacy.Thms
public import Silmaril.Games.Inst.Thms
import Silmaril.Proofs.Wasm.Game.Start.Main

/-!
# Modules with a start function: theorems

For an **arbitrary** silmaril profile `P` (no determinism is used anywhere).

## Instances

* `isInstanceStart_none_iff`: `IsInstance` is `IsInstanceStart … none`.
* `IsInstanceStart.ok`: the instance before its start function is well formed
  and its start function has the type `[] → []`.

## Adequacy of instantiation and of the calls that follow

Let `I` be well formed at `s`, its start function (if any) typed `[] → []`,
and `K` an environment throwing only existing exceptions. The closed program
`I.closedInst P s start K` (divergence observed) satisfies:

* `ScalarInstance.adequacy_inst`: its instantiation observations (`ready` as
  `returns []`, `fail b` as `b`, divergence after `[askInst]` as `diverges`)
  are **exactly** the closed-world Core behaviours of the start phase,
  `startBehaviours P (hostOf I.imports K) s start` (for a start function at
  `a`: `behaviours P host s a []`, `startBehaviours_some`; without one:
  `{returns []}`, `startBehaviours_none`).
* `ScalarInstance.traces_after_inst`: after `[askInst, ansInst ready]` it
  plays `p` (relabelled by `liftMove`) exactly when, for some store `s'` the
  start phase may return at (`StartsTo`), `p` is a play of the closed program
  `K.strategy ≫ I.strategy P s'`; `ScalarInstance.div_after_inst`: the same for
  divergence and `I.closedD P s' K`. The store persists from the start
  function to the export calls.
* `ScalarInstance.adequacy_after_inst`: hence the observations of an export
  call `f` right after instantiation (`obsAfterInst`) are exactly the Core
  behaviours of `f` at the stores the start phase may return at: the Core
  reading "run the start function, then invoke `f`".
* `IsInstanceStart.adequacy_inst`, `IsInstanceStart.adequacy_after_inst`: the
  same for the instance of a module before its start function
  (`instantiateOnce?`).

## Arbitrary instantiation threads

`ScalarInstance.startT_result_cases`, `startT_wellFormed`, `adequacy_instT`,
`adequacy_after_instT`, `div_after_instT`: the same for an instantiation thread `t₀` whose
configuration is typed at `[]` (used for the spec's `$instantiate` configuration in
`Silmaril.Wasm.Game.SpecInst`); in particular the stores it returns at are well formed.

## The start-free special case

* `startsTo_none`: without a start function the start phase returns at `s`
  itself; `ScalarInstance.adequacy_after_inst_none`: the observations right
  after instantiation are those of `I.closedD P s K` (`adequacy_div`).
* `ScalarInstance.instSys_none_traces`: without a start function the plays of
  the instantiable system after `[askInst, ansInst ready]` are the plays of the
  old strategy `I.strategy P s`; the earlier theorems (`IsInstance.*`) are the
  start-free case.

## Not covered here

The Core side is `instantiateOnce?` (allocation and segment initialisation,
a function) followed by the start invocation. The spec's own instantiation
configuration (`Config.withStart`, segment initialisation run by Core
reduction, then `call x`) is the instantiation phase in
`Silmaril.Wasm.Game.SpecInst` (`IsSpecInstanceAt.adequacy_inst`, every profile),
through the thread-general start phase `instSysT` of `Start.Defs`. That the
two Core sides have the same behaviours under an arbitrary profile is not
shown.

Proofs: `Silmaril.Proofs.Wasm.Game.Start.*`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Games.Inst Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- **The instances without a start function are the start-free special case.** -/
theorem isInstanceStart_none_iff {m : Module} {mt : CModuleType} {I : ScalarInstance} :
    IsInstanceStart m mt I none ↔ IsInstance m mt I :=
  Silmaril.Proofs.Wasm.Game.isInstanceStart_none_iff

/-- **Instances before their start function are well formed**, and the start function has
the type `[] → []`. -/
theorem IsInstanceStart.ok {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {start : Option Nat} (h : IsInstanceStart m mt I start) :
    I.Ok ∧ ∀ a ∈ start, StartTyped I.store a :=
  ⟨Silmaril.Proofs.Wasm.Game.IsInstanceStart.ok_store h,
    Silmaril.Proofs.Wasm.Game.IsInstanceStart.startTyped h⟩

/-- The start phase of a start function at `a` is its invocation. -/
theorem startBehaviours_some (P : Profile) (host : HostSemantics Nat) (s : Store Nat) (a : Nat) :
    startBehaviours P host s (some a) = behaviours P host s a [] := rfl

/-- **Without a start function the start phase returns at the store unchanged.** -/
theorem startsTo_none {P : Profile} {host : HostSemantics Nat} {s s' : Store Nat} :
    StartsTo P host s none s' ↔ s' = s :=
  Silmaril.Proofs.Wasm.Game.Start.startsTo_none

/-- Without a start function the start phase returns `[]`. -/
theorem startBehaviours_none (P : Profile) (host : HostSemantics Nat) (s : Store Nat) :
    startBehaviours P host s none = {.returns []} := by
  ext b
  constructor
  · rintro (⟨c', r, hc', hr, rfl⟩ | ⟨-, hdiv⟩)
    · have hc : c' = startConfig s none := Silmaril.Proofs.Wasm.Game.Start.steps_startConfig_none hc'
      have hr' : r.toAdmin = (Result.values []).toAdmin := hr.symm.trans (hc ▸ rfl)
      rw [Silmaril.Proofs.Wasm.Game.result_toAdmin_injective hr']
      rfl
    · obtain ⟨c₁, hst, -⟩ := hdiv.unfold
      exact absurd hst (Silmaril.Proofs.Wasm.Game.Step.not_result
        Silmaril.Proofs.Wasm.Game.Start.startConfig_none_code)
  · rintro rfl
    exact mem_behavioursOf (r := .values []) .refl rfl

namespace ScalarInstance

variable {I : ScalarInstance}

/-- **Adequacy of instantiation, every profile.** The instantiation observations of the closed
program (`returns []` when ready, the trap or exception when failing, `diverges` when
diverging) are exactly the closed-world Core behaviours of the start phase. -/
theorem adequacy_inst {P : Profile} {s : Store Nat} {start : Option Nat} (hw : I.WellFormed s)
    (hst : ∀ a ∈ start, StartTyped s a) (K : Env I.E) (hK : ThrowsBelow K s.exns.length) :
    instObs (I.closedInst P s start K) = startBehaviours P (hostOf I.imports K) s start :=
  Silmaril.Proofs.Wasm.Game.Start.adequacy_inst hw hst hK

/-- **Plays after a successful instantiation, every profile**: those of the closed program at
a store the start phase may return at. -/
theorem traces_after_inst {P : Profile} {s : Store Nat} {start : Option Nat} {K : Env I.E}
    (p : List (Move Sig.empty I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (I.closedInstLTS P s start K).Traces ↔
      ∃ s', StartsTo P (hostOf I.imports K) s start s' ∧ p ∈ I.closedWith P s' K :=
  Silmaril.Proofs.Wasm.Game.Start.traces_after_inst p

/-- **Divergence after a successful instantiation, every profile**: that of the closed program
at a store the start phase may return at. -/
theorem div_after_inst {P : Profile} {s : Store Nat} {start : Option Nat} {K : Env I.E}
    (p : List (Move Sig.empty I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (I.closedInst P s start K).div ↔
      ∃ s', StartsTo P (hostOf I.imports K) s start s' ∧ p ∈ (I.closedD P s' K).div :=
  Silmaril.Proofs.Wasm.Game.Start.div_after_inst p

/-- **Adequacy of instantiation-then-invocation, every profile.** The observations of an export
call right after instantiation are its Core behaviours at the stores the start phase may return
at. -/
theorem adequacy_after_inst {P : Profile} {s : Store Nat} {start : Option Nat}
    (hw : I.WellFormed s) (hst : ∀ a ∈ start, StartTyped s a) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    obsAfterInst (I.closedInst P s start K) f =
      {b | ∃ s', StartsTo P (hostOf I.imports K) s start s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} :=
  Silmaril.Proofs.Wasm.Game.Start.adequacy_after_inst hw hst hK f

/-- **The start-free case of `adequacy_after_inst`**: right after instantiation the
observations are those of the closed program at `s` (M2, `adequacy_div`). -/
theorem adequacy_after_inst_none {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (K : Env I.E) (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    obsAfterInst (I.closedInst P s none K) f = dcompositeObs (I.closedD P s K) f := by
  rw [adequacy_after_inst hw (fun _ h => by cases h) K hK f, ← adequacy_div hw K hK f]
  ext b
  constructor
  · rintro ⟨s', hs', hb⟩
    exact startsTo_none.1 hs' ▸ hb
  · intro hb
    exact ⟨s, startsTo_none.2 rfl, hb⟩

/-- **Without a start function the module strategy extends the instance strategy**: after the
instantiation exchange, its plays are those of `I.strategy P s`. -/
theorem instSys_none_traces {P : Profile} {s : Store Nat} (p : List (Move I.E I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (I.instSys P s none).toLTS.Traces ↔
      p ∈ I.strategy P s :=
  Silmaril.Proofs.Wasm.Game.Start.instSys_none_traces p

/-! ### Arbitrary instantiation threads -/

/-- **Typed instantiation results**: a result reached by an instantiation thread typed at `[]`
is `values []`, a trap or an exception. -/
theorem startT_result_cases {P : Profile} {s : Store Nat} {t₀ : Thread} {K : Env I.E}
    (hw : I.WellFormed s) (hok : ConfigOk (t₀.config s) []) (hK : ThrowsBelow K s.exns.length)
    {c' : Config Nat} {r : Result} (run : Steps P (hostOf I.imports K) (t₀.config s) c')
    (final : c'.code = r.toAdmin) : r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x :=
  Silmaril.Proofs.Wasm.Game.Start.startT_result_cases hw hok hK run final

/-- **The stores an instantiation thread typed at `[]` returns at are well formed**, and the
environment still throws only existing exceptions there. -/
theorem startT_wellFormed {P : Profile} {s : Store Nat} {t₀ : Thread} {K : Env I.E}
    (hw : I.WellFormed s) (hok : ConfigOk (t₀.config s) []) (hK : ThrowsBelow K s.exns.length)
    {s' : Store Nat} (h : StartsToT P (hostOf I.imports K) s t₀ s') :
    I.WellFormed s' ∧ ThrowsBelow K s'.exns.length :=
  Silmaril.Proofs.Wasm.Game.Start.startT_wellFormed hw hok hK h

/-- **Adequacy of instantiation for an arbitrary instantiation thread typed at `[]`.** -/
theorem adequacy_instT {P : Profile} {s : Store Nat} {t₀ : Thread} {K : Env I.E}
    (hw : I.WellFormed s) (hok : ConfigOk (t₀.config s) []) (hK : ThrowsBelow K s.exns.length) :
    instObs (I.closedInstT P s t₀ K) = behavioursOf P (hostOf I.imports K) (t₀.config s) :=
  Silmaril.Proofs.Wasm.Game.Start.adequacy_instT hw hok hK

/-- **Adequacy of the calls after an arbitrary typed instantiation thread.** -/
theorem adequacy_after_instT {P : Profile} {s : Store Nat} {t₀ : Thread} {K : Env I.E}
    (hw : I.WellFormed s) (hok : ConfigOk (t₀.config s) []) (hK : ThrowsBelow K s.exns.length)
    (f : I.F.Op) :
    obsAfterInst (I.closedInstT P s t₀ K) f =
      {b | ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} :=
  Silmaril.Proofs.Wasm.Game.Start.adequacy_after_instT hw hok hK f

/-- **Divergence after a successful instantiation by an arbitrary thread.** -/
theorem div_after_instT {P : Profile} {s : Store Nat} {t₀ : Thread} {K : Env I.E}
    (p : List (Move Sig.empty I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (I.closedInstT P s t₀ K).div ↔
      ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧ p ∈ (I.closedD P s' K).div :=
  Silmaril.Proofs.Wasm.Game.Start.div_after_instT p

end ScalarInstance

/-- **Adequacy of instantiation for modules, every profile.** -/
theorem IsInstanceStart.adequacy_inst {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {start : Option Nat} (h : IsInstanceStart m mt I start) (P : Profile) (K : Env I.E)
    (hK : ThrowsBelow K I.store.exns.length) :
    instObs (I.closedInst P I.store start K) =
      startBehaviours P (hostOf I.imports K) I.store start :=
  ScalarInstance.adequacy_inst h.ok.1 h.ok.2 K hK

/-- **Adequacy of instantiation-then-invocation for modules, every profile.** -/
theorem IsInstanceStart.adequacy_after_inst {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {start : Option Nat} (h : IsInstanceStart m mt I start) (P : Profile) (K : Env I.E)
    (hK : ThrowsBelow K I.store.exns.length) (f : I.F.Op) :
    obsAfterInst (I.closedInst P I.store start K) f =
      {b | ∃ s', StartsTo P (hostOf I.imports K) I.store start s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} :=
  ScalarInstance.adequacy_after_inst h.ok.1 h.ok.2 K hK f

end Silmaril.Wasm.Game
