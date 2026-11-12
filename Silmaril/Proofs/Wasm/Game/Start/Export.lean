module

public import Silmaril.Proofs.Wasm.Game.Start.Bisim
public import Silmaril.Proofs.Wasm.Game.Start.Phase

/-!
# The export phase of the instantiable system is the instance system

After instantiation, the instantiable system `I.instSysT P s t₀` from the
ready state `ready s'` behaves exactly as the divergence-observing instance
system `I.dlts` from `idle s'`, export questions relabelled by `liftMove`
(`exportB`): idle states are ready states, running threads are running
configurations, and a thread waiting for the answer to `e` waits with the
continuation `resumeK`. The bisimulation lifts below the environment
(`cmpB`), relating the closed program of `I.dlts` (`Cmp`) with the export
phase of `I.closedInstLTS`.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Start

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.ScalarInstance Silmaril
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {I : ScalarInstance} {P : Profile} {s₀ : Store Nat} {t₀ : Thread}

/-- `liftEv` is injective. -/
theorem liftEv_injective {F : Sig.{0}} {R : Type} :
    Function.Injective (liftEv (F := F) (R := R)) := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

/-- The states of the instance system as states of the instantiable system. -/
noncomputable def phi (I : ScalarInstance) (P : Profile) (s₀ : Store Nat) (t₀ : Thread) :
    I.HState → (I.instSysT P s₀ t₀).St
  | .idle s => .ready s
  | .running f s t => .run f (s, t)
  | .waiting f s t e => .wait f e (I.resumeK s t e)

theorem export_step_ready {s : Store Nat}
    {l : Option (Move I.E (I.F.withInst (Behaviour Val)))} {z : (I.instSysT P s₀ t₀).St}
    (h : (I.instSysT P s₀ t₀).toLTS.step (.ready s) l z) :
    InstSystem.Step (I.instSysT P s₀ t₀) (.ready s) l z := h

theorem export_step_run {f : I.F.Op} {c : Store Nat × Thread}
    {l : Option (Move I.E (I.F.withInst (Behaviour Val)))} {z : (I.instSysT P s₀ t₀).St}
    (h : (I.instSysT P s₀ t₀).toLTS.step (.run f c) l z) :
    InstSystem.Step (I.instSysT P s₀ t₀) (.run f c) l z := h

theorem export_step_wait {f : I.F.Op} {e : I.E.Op} {k : I.E.Ar e → Store Nat × Thread}
    {l : Option (Move I.E (I.F.withInst (Behaviour Val)))} {z : (I.instSysT P s₀ t₀).St}
    (h : (I.instSysT P s₀ t₀).toLTS.step (.wait f e k) l z) :
    InstSystem.Step (I.instSysT P s₀ t₀) (.wait f e k) l z := h

/-- **The export phase is the instance system.** -/
noncomputable def exportBT (I : ScalarInstance) (P : Profile) (s₀ s : Store Nat)
    (t₀ : Thread) : FBisim (I.dlts P s) (I.instSysT P s₀ t₀).toLTS where
  φ := phi I P s₀ t₀
  ρ := liftMove
  inj := upperMap_injective liftEv_injective
  fwd := by
    intro x l y h
    cases h with
    | call s f => exact InstSystem.Step.askEx (S := I.instSysT P s₀ t₀) s f
    | tau h => exact InstSystem.Step.tau h
    | ucall callout op => exact InstSystem.Step.call ⟨⟨_, _, callout, op⟩, rfl⟩
    | uret v => exact InstSystem.Step.resume _ _ _ v
    | oret final answer => exact InstSystem.Step.ret ⟨_, final, answer, rfl⟩
  bwd := by
    intro x l z h
    cases x with
    | idle s =>
      cases export_step_ready h with
      | askEx _ q => exact ⟨some (.inr (.ask q)), .running q s (I.initThread q), rfl, rfl, Silmaril.Wasm.Game.ScalarInstance.DTrans.call s q⟩
    | running f s t =>
      cases export_step_run h with
      | tau hi => exact ⟨none, .running f _ _, rfl, rfl, Silmaril.Wasm.Game.ScalarInstance.DTrans.tau hi⟩
      | call hc =>
        obtain ⟨⟨_, _, hco, hop⟩, rfl⟩ := hc
        exact ⟨some (.inl (.ask _)), .waiting f s t _, rfl, rfl, Silmaril.Wasm.Game.ScalarInstance.DTrans.ucall hco hop⟩
      | ret hd =>
        obtain ⟨r, hr, hv, hst⟩ := hd
        exact ⟨some (.inr (.ans f _)), .idle s, rfl, by rw [hst]; rfl, Silmaril.Wasm.Game.ScalarInstance.DTrans.oret hr hv⟩
    | waiting f s t e =>
      cases export_step_wait h with
      | resume _ _ _ n =>
        exact ⟨some (.inl (.ans e n)),
          .running f s (resumeResult s t (Answer.toResult (ft := I.imports.get e.1) n)), rfl, rfl, Silmaril.Wasm.Game.ScalarInstance.DTrans.uret n⟩

/-- **The export phase of the closed program is the closed instance system.** -/
noncomputable def cmpB (I : ScalarInstance) (P : Profile) (s₀ s : Store Nat)
    (t₀ : Thread) (K : Silmaril.Wasm.Game.Env I.E) :
    FBisim (Cmp I P s K) (CI I P s₀ t₀ K) :=
  (exportBT I P s₀ s t₀).compLeft K.dlts liftEv liftEv_injective rfl

/-- **The export phase is the instance system**, for a start function. -/
noncomputable def exportB (I : ScalarInstance) (P : Profile) (s₀ s : Store Nat)
    (start : Option Nat) : FBisim (I.dlts P s) (I.instSys P s₀ start).toLTS :=
  exportBT I P s₀ s (startThread start)

theorem cmpB_init {s : Store Nat} {K : Silmaril.Wasm.Game.Env I.E} :
    (cmpB I P s₀ s t₀ K).φ (Cmp I P s K).init = (none, .ready s) := rfl

theorem cmpB_ρ {s : Store Nat} {K : Silmaril.Wasm.Game.Env I.E} :
    (cmpB I P s₀ s t₀ K).ρ = liftMove := rfl

end Silmaril.Proofs.Wasm.Game.Start
