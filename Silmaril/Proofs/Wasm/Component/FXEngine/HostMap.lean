module

public import Silmaril.Proofs.Wasm.Component.FXEngine.Lawful
public import Silmaril.Wasm.Component.Reference.Calls.Thms
public import Silmaril.Wasm.Execution.Core.Sim.SetFuncs
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Core threads of the FX engine in stores without FX functions

The game semantics runs engines in stores over host codes `Nat`. A Core 3.0 store `s : Store Nat`
is a store of the FX engine with no FX functions, `SFX s = Store.mapH FXCode.host s`. This
module relates the Core threads of the FX engine in such stores to the threads of `core3P P`:

* `decompose?_mapH'`, `config_mapH'`, `resume_mapH'`: host-call redexes, invocation
  configurations and resumption commute with renaming host code along any `g : H → H'` (the
  proofs of `Silmaril.Proofs.Wasm.Component.Reference.CalloutMap`, there for `g : H → Nat`);
* `step_funcs_eq`: a host-free Core step keeps the function instances, so a store reached from
  `SFX s` is `SFX` of a Core store (`SFX_unFX_of_funcs`);
* `internalP_SFX`, `internalP_of_SFX`: host-free steps of `s` and of `SFX s` correspond, both
  ways (`Step.mapH` along `FXCode.host` and along its left inverse `unFX`);
* `statusP_SFX`: the Core status in `SFX s` is the status in `s` with host code `h` renamed to
  `host h`; hence `statusFX_core_SFX`: **the FX engine status of a Core thread in `SFX s` is the
  `core3P P` status**, and `internalFX_core_SFX_iff`: **its internal steps are the `core3P P`
  steps** (a Core thread in `SFX s` never calls an FX function).

New proofs, except the copied redex lemmas noted above.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXEngine

open Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Game (statusP InternalP)
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH Config.mapH FuncInst.mapH FuncCode.mapH
  Store.mapH_funcs_getElem? invoke_mapH Step.mapH)
open Silmaril.Wasm.Execution.Core (Store Config Step Val Admin FuncInst)
open Silmaril.Wasm.SingleThreaded (Thread decompose? hostArity? topRedex decompHead decompTop
  splitVals splitVals_snd_sizeOf decompose?_eq Ctx)
open Silmaril.Wasm.Component.Reference (flatStatus core3P)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Redexes under a change of host type -/

section mapH

variable {H H' : Type} (g : H → H')

theorem hostArity?_mapH' (s : Store H) (a : Nat) :
    hostArity? (Store.mapH g s) a = (hostArity? s a).map fun p => (g p.1, p.2) := by
  unfold hostArity?
  rw [Store.mapH_funcs_getElem?]
  cases s.funcs[a]? with
  | none => rfl
  | some fi =>
    simp only [Option.map_some]
    cases hc : fi.code <;> cases hft : fi.type.funcType? <;>
      simp [FuncInst.mapH, hc, hft, FuncCode.mapH]

/-- The renaming of a redex. -/
def mapR' : Ctx × Nat × H × List Val → Ctx × Nat × H' × List Val :=
  fun x => (x.1, x.2.1, g x.2.2.1, x.2.2.2)

theorem topRedex_mapH' (s : Store H) (vs : List Val) (rest : List Admin) :
    topRedex (Store.mapH g s) vs rest = (topRedex s vs rest).map (mapR' g) := by
  unfold topRedex
  split
  · rw [hostArity?_mapH']
    cases hostArity? s _ with
    | none => rfl
    | some p =>
      show (if p.2 ≤ _ then _ else none) = Option.map _ (if p.2 ≤ _ then _ else none)
      split <;> rfl
  · rfl

/-- **Host-call redexes commute with renaming host code.** -/
theorem decompose?_mapH' (s : Store H) (code : List Admin) :
    decompose? (Store.mapH g s) code = (decompose? s code).map (mapR' g) := by
  rw [decompose?_eq, decompose?_eq]
  rcases hsp : splitVals code with ⟨vs, _ | ⟨d, rest⟩⟩
  · rfl
  · show decompHead (Store.mapH g s) vs d rest = (decompHead s vs d rest).map (mapR' g)
    cases d with
    | label n cont body =>
      simp only [decompHead, decompose?_mapH' s body, Option.map_map]
      rfl
    | handler n cs body =>
      simp only [decompHead, decompose?_mapH' s body, Option.map_map]
      rfl
    | frame n f body =>
      simp only [decompHead, decompose?_mapH' s body, Option.map_map]
      rfl
    | plain i =>
      simp only [decompHead]
      split
      · exact topRedex_mapH' g s vs rest
      · rfl
    | ref r => rfl
    | callRefType t => exact topRedex_mapH' g s vs rest
    | returnCallRefType t => rfl
    | trap => rfl
termination_by sizeOf code
decreasing_by
  all_goals
    have h := splitVals_snd_sizeOf code
    rw [hsp] at h
    simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec, Admin.handler.sizeOf_spec,
      Admin.frame.sizeOf_spec] at h
    omega

theorem config_mapH' (s : Store H) (t : Thread) :
    t.config (Store.mapH g s) = Config.mapH g (t.config s) := by
  cases t with
  | pending a args => exact (invoke_mapH g s a args).symm
  | active f code => rfl

/-- **Resumption does not read host code.** -/
theorem resume_mapH' (s : Store H) (t : Thread) (r : Silmaril.Wasm.SingleThreaded.CallResult) :
    Silmaril.Wasm.SingleThreaded.resume (Store.mapH g s) t r =
      Silmaril.Wasm.SingleThreaded.resume s t r := by
  unfold Silmaril.Wasm.SingleThreaded.resume
  dsimp only
  rw [config_mapH', show (Config.mapH g (t.config s)).code = (t.config s).code from rfl,
    decompose?_mapH']
  cases decompose? s (t.config s).code with
  | none => rfl
  | some x => rfl

end mapH

/-! ## Function instances are kept by host-free steps -/

/-- A host-free Core step keeps the function instances. -/
theorem step_funcs_eq {H : Type} {P : Profile} {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') : c'.store.funcs = c.store.funcs := by
  induction h with
  | «variable» h => exact Silmaril.Wasm.Execution.Core.VariableStep.funcs_eq h
  | table h => exact Silmaril.Wasm.Execution.Core.TableStep.funcs_eq h
  | memory h => exact Silmaril.Wasm.Execution.Core.MemoryStep.funcs_eq h
  | reference h => exact Silmaril.Wasm.Execution.Core.RefStep.funcs_eq h
  | aggregate h => exact Silmaril.Wasm.Execution.Core.AggregateStep.funcs_eq h
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | ctxtFrame _ ih => exact ih
  | callRefHost _ _ _ _ _ hh => exact hh.elim
  | callRefHostDiv _ _ _ _ _ hh => exact hh.elim
  | _ => rfl

/-! ## Core stores as FX stores -/

/-- A Core store as a store of the FX engine with no FX functions. -/
abbrev SFX (s : Store Nat) : Store (FXCode Nat) := Store.mapH FXCode.host s

/-- The left inverse of `FXCode.host` on `Nat`. -/
def unFX : FXCode Nat → Nat
  | .host h => h
  | .fx _ => 0

theorem mapH_unFX_host (fi : FuncInst Nat) : FuncInst.mapH unFX (FuncInst.mapH FXCode.host fi) = fi := by
  rcases fi with ⟨ty, md, code⟩
  cases code <;> rfl

theorem unFX_SFX (s : Store Nat) : Store.mapH unFX (SFX s) = s := by
  have hf : (Store.mapH unFX (SFX s)).funcs = s.funcs := by
    show (s.funcs.map (FuncInst.mapH FXCode.host)).map (FuncInst.mapH unFX) = s.funcs
    rw [List.map_map]
    exact List.map_id'' mapH_unFX_host s.funcs
  cases s
  simp only [Store.mapH] at hf ⊢
  rw [hf]

/-- A store with the function instances of `SFX s` is `SFX` of a Core store. -/
theorem SFX_unFX_of_funcs {s : Store Nat} {s₁ : Store (FXCode Nat)}
    (hf : s₁.funcs = (SFX s).funcs) : SFX (Store.mapH unFX s₁) = s₁ := by
  have hf' : (SFX (Store.mapH unFX s₁)).funcs = s₁.funcs := by
    show (s₁.funcs.map (FuncInst.mapH unFX)).map (FuncInst.mapH FXCode.host) = s₁.funcs
    rw [hf]
    show ((s.funcs.map (FuncInst.mapH FXCode.host)).map (FuncInst.mapH unFX)).map
      (FuncInst.mapH FXCode.host) = s.funcs.map (FuncInst.mapH FXCode.host)
    simp only [List.map_map, Function.comp_def, mapH_unFX_host]
  cases s₁
  simp only [Store.mapH] at hf' ⊢
  rw [hf']

/-! ## Host-free steps of `s` and of `SFX s` -/

variable {P : Profile}

/-- A host-free step of `s` is a host-free step of `SFX s`. -/
theorem internalP_SFX {s s' : Store Nat} {t t' : Thread} (h : InternalP P (s, t) (s', t')) :
    InternalP P (SFX s, t) (SFX s', t') := by
  obtain ⟨f', code', ht, hstep⟩ := h
  have hm : Step P (fun _ _ _ _ => False) (Config.mapH FXCode.host (t.config s))
      (Config.mapH FXCode.host ⟨s', f', code'⟩) := Step.mapH FXCode.host hstep
  refine ⟨f', code', ht, ?_⟩
  rw [config_mapH']
  exact hm

/-- A host-free step of `SFX s` is a host-free step of `s`, landing in `SFX` of a Core store. -/
theorem internalP_of_SFX {s : Store Nat} {s₁ : Store (FXCode Nat)} {t t' : Thread}
    (h : InternalP P (SFX s, t) (s₁, t')) :
    ∃ s', s₁ = SFX s' ∧ InternalP P (s, t) (s', t') := by
  obtain ⟨f', code', ht, hstep⟩ := h
  have hm : Step P (fun _ _ _ _ => False) (Config.mapH unFX (t.config (SFX s)))
      (Config.mapH unFX ⟨s₁, f', code'⟩) := Step.mapH unFX hstep
  have hc : Config.mapH unFX (t.config (SFX s)) = t.config s := by
    rw [← config_mapH', unFX_SFX]
  have hf : s₁.funcs = (SFX s).funcs := by
    have e := step_funcs_eq hstep
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at e
  refine ⟨Store.mapH unFX s₁, (SFX_unFX_of_funcs hf).symm, f', code', ht, ?_⟩
  rw [← hc]
  exact hm

theorem exists_internalP_SFX_iff {s : Store Nat} {t : Thread} :
    (∃ y, InternalP P (SFX s, t) y) ↔ ∃ y, InternalP P (s, t) y := by
  constructor
  · rintro ⟨⟨s₁, t'⟩, h⟩
    obtain ⟨s', -, h'⟩ := internalP_of_SFX h
    exact ⟨(s', t'), h'⟩
  · rintro ⟨⟨s', t'⟩, h⟩
    exact ⟨(SFX s', t'), internalP_SFX h⟩

/-! ## Statuses -/

/-- Rename the host code of a Core status to `FXCode Nat`. -/
def mapSt : Silmaril.Wasm.SingleThreaded.Status Nat →
    Silmaril.Wasm.SingleThreaded.Status (FXCode Nat)
  | .running => .running
  | .returned r => .returned r
  | .callout h args => .callout (.host h) args
  | .stuck => .stuck

/-- **The Core status in `SFX s`** is the status in `s`, host code renamed. -/
theorem statusP_SFX (s : Store Nat) (t : Thread) :
    statusP P (SFX s) t = mapSt (statusP P s t) := by
  have hc : (t.config (SFX s)).code = (t.config s).code := by
    rw [config_mapH']
    rfl
  have hd : decompose? (SFX s) (t.config s).code =
      (decompose? s (t.config s).code).map (mapR' FXCode.host) := decompose?_mapH' _ s _
  have hi := exists_internalP_SFX_iff (P := P) (s := s) (t := t)
  unfold statusP
  dsimp only
  rw [hc, hd]
  split_ifs
  all_goals first
    | rfl
    | cases decompose? s (t.config s).code <;>
        first | rfl | exact absurd (hi.1 ‹_›) ‹_› | exact absurd (hi.2 ‹_›) ‹_›

theorem liftR_mapSt (st : Silmaril.Wasm.SingleThreaded.Status Nat) :
    liftR (mapSt st) = flatStatus st := by
  rcases st with _ | (vs | _) | ⟨h, args⟩ | _
  · rfl
  · simp only [mapSt, liftR, flatStatus]
    cases List.mapM Silmaril.Wasm.SingleThreaded.toFlat? vs <;> rfl
  · rfl
  · simp only [mapSt, liftR, flatStatus]
    cases List.mapM Silmaril.Wasm.SingleThreaded.toFlat? args <;> rfl
  · rfl

/-- **The FX engine status of a Core thread in `SFX s` is its `core3P P` status.** -/
theorem statusFX_core_SFX (s : Store Nat) (t : Thread) :
    statusFX P (SFX s) (.core t) = (core3P P).status s t := by
  show liftR (statusP P (SFX s) t) = flatStatus (statusP P s t)
  rw [statusP_SFX, liftR_mapSt]

/-- **The internal steps of a Core thread in `SFX s` are the `core3P P` steps.** -/
theorem internalFX_core_SFX_iff {s : Store Nat} {t : Thread}
    {y : Store (FXCode Nat) × ThreadFX Nat} :
    InternalFX P (SFX s, .core t) y ↔
      ∃ s' t', y = (SFX s', .core t') ∧ InternalP P (s, t) (s', t') := by
  constructor
  · rintro (⟨t', ht, h⟩ | ⟨⟨F, args, e⟩, -⟩)
    · obtain ⟨s', hs, h'⟩ := internalP_of_SFX h
      exact ⟨s', t', Prod.ext hs ht, h'⟩
    · rw [statusP_SFX] at e
      revert e
      generalize statusP P s t = st
      rcases st with _ | _ | ⟨_, _⟩ | _ <;> simp [mapSt]
  · rintro ⟨s', t', rfl, h⟩
    exact Or.inl ⟨t', rfl, internalP_SFX h⟩

/-- Resumption of a Core thread in `SFX s` is its `core3P P` resumption. -/
theorem resumeFX_core_SFX (s : Store Nat) (t : Thread)
    (r : Silmaril.Wasm.Component.Engine.CallResult) :
    resumeFX (SFX s) (.core t) r = .core ((core3P P).resume s t r) := by
  show ThreadFX.core _ = ThreadFX.core _
  rw [resume_mapH']
  rfl

end Silmaril.Proofs.Wasm.Component.FXEngine
