module

public import Silmaril.Wasm.Component.FXEngine.Defs
public import Silmaril.Wasm.Component.Core3G.Thms
public import Silmaril.Wasm.Models.FX.Thms
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The WasmFX engine is lawful

Proofs for `Silmaril.Wasm.Component.FXEngine.Thms` (`fxE_lawful`).

* `stepFX_grows`: a `StepFX` step with no host grows the Core store (`Grows`): its `core` rule
  is a Core step, `resume_throw` allocates an exception, and every other rule keeps the store;
* `statusP_callout_prefix'`, `Grows.extendsFX`: growth is store extension of the FX engine.
  Callouts of Core threads persist (the argument of the Core 3.0 engine: `decompose?` reads the
  store only through function prefixes); an FX thread is never a callout; a parked thread is
  a callout whatever the store;
* `no_step_of_ne_running`: a thread whose status is not `running` takes no internal step. For a
  Core thread this is the law of `core3P P` (its status is the Core status), for an FX thread
  it holds by definition of `statusFX`, and a parked thread takes no step;
* `statusFX_allocHost_callout`: invoking an allocated host function is a callout (the law of
  `core3P P` at host type `FXCode H`).

Source: `statusP_callout_prefix'` and `Grows.extendsFX` follow
`Silmaril.Proofs.Wasm.Component.Core3G.Lawful` (`statusP_callout_prefix`, `Grows.extendsP`).
New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXEngine

open Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Game (statusP InternalP)
open Silmaril.Wasm.Execution.Core (Store Config Step Val Admin)
open Silmaril.Wasm.SingleThreaded (Thread decompose?)
open Silmaril.Wasm.Component.Engine.Core3 (Grows Step.grows_of_host decompose?_prefix
  Thread.config_code_prefix Thread.loaded_of_decompose?)
open Silmaril.Wasm.Models.FX (StepFX ofCore)
open Silmaril.Wasm.Numerics (Profile)

open Silmaril.Wasm.Component.Reference (flatStatus core3P)

variable {H : Type} {P : Profile}

/-! ## Growth -/

/-- **A `StepFX` step with no host grows the store.** -/
theorem stepFX_grows {x y : Silmaril.Wasm.Models.FX.ConfigFX (FXCode H)}
    (h : StepFX P (noHostFX H) fxOf x y) : Grows x.store y.store := by
  induction h with
  | core h => exact Step.grows_of_host (fun _ _ _ _ _ hh => hh.2.elim) h
  | seq _ _ ih => exact ih
  | ctxLabel _ ih => exact ih
  | ctxFrame _ ih => exact ih
  | ctxHandler _ ih => exact ih
  | resumeThrow => exact Grows.addExn _ _
  | _ => exact Grows.refl _

theorem internalP_grows {s s' : Store (FXCode H)} {t t' : Thread}
    (h : InternalP P (s, t) (s', t')) : Grows s s' := by
  obtain ⟨f', code', -, h⟩ := h
  have hg := Step.grows_of_host (fun _ _ _ _ _ hh => hh.elim) h
  rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hg

/-- **Internal steps of the FX engine grow the store.** -/
theorem internalFX_grows {s s' : Store (FXCode H)} {t t' : ThreadFX H}
    (h : InternalFX P (s, t) (s', t')) : Grows s s' := by
  cases t with
  | core t₀ =>
    rcases h with ⟨t₁, -, h⟩ | ⟨-, K, f, code, -, h⟩
    · exact internalP_grows h
    · have hg := stepFX_grows h
      simpa [ofCore, Silmaril.Wasm.SingleThreaded.Thread.config_store] using hg
  | fx K f code =>
    rcases h with ⟨K', f', code', -, h⟩ | ⟨hs, -⟩
    · exact stepFX_grows h
    · exact (show s' = s from hs) ▸ Grows.refl _
  | parked => exact h.elim

/-- Allocating FX functions grows the store. -/
theorem allocFX_grows (inst : Silmaril.Wasm.Execution.Core.ModuleInst) :
    ∀ (s : Store (FXCode H)) (ds : List FXDecl), Grows s (allocFX inst s ds).1
  | s, [] => Grows.refl s
  | _, _ :: ds =>
    (Silmaril.Wasm.Component.Engine.Core3.allocHost_grows (Prod.ext rfl rfl)).trans
      (allocFX_grows inst _ ds)

theorem prepareFX?_grows {s s' : Store (FXCode H)} {m : ModuleFX}
    {xas : List Silmaril.Wasm.Execution.Core.ExternAddr} {i : InstFX} {st : Option Nat}
    (h : prepareFX? s m xas = some (s', i, st)) : Grows s s' := by
  unfold prepareFX? at h
  split at h
  next s₁ i₁ st₁ he =>
    cases h
    exact (Silmaril.Wasm.Component.Engine.Core3.prepareE?_grows he).trans
      (allocFX_grows i₁ s₁ m.fxs)
  next => cases h

/-! ## Callouts persist -/

theorem decompose?_of_statusP_callout {s : Store (FXCode H)} {t : Thread} {hc : FXCode H}
    {args : List Val} (h : statusP P s t = .callout hc args) :
    ∃ E a, decompose? s (t.config s).code = some (E, a, hc, args) := by
  unfold statusP at h
  dsimp only at h
  split_ifs at h
  all_goals
    revert h
    rcases decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩
    all_goals simp

/-- A callout status of `statusP` persists in every store with more functions. -/
theorem statusP_callout_prefix' {s s' : Store (FXCode H)} (hg : s.funcs <+: s'.funcs)
    {t : Thread} {hc : FXCode H} {args : List Val} (h : statusP P s t = .callout hc args) :
    statusP P s' t = .callout hc args := by
  obtain ⟨E, a, hd⟩ := decompose?_of_statusP_callout h
  have hcode := Thread.config_code_prefix hg (Thread.loaded_of_decompose? hd)
  have hd' := decompose?_prefix hg hd
  unfold statusP at h ⊢
  dsimp only at h ⊢
  rw [hcode, hd']
  rw [hd] at h
  dsimp only at h ⊢
  exact h

/-! ## The status of Core threads -/

theorem liftR_eq_callout {st : Silmaril.Wasm.SingleThreaded.Status (FXCode H)} {h : H}
    {args : List Silmaril.Wasm.Component.Engine.FlatValue} (e : liftR st = .callout h args) :
    ∃ args', st = .callout (.host h) args' := by
  rcases st with _ | (vs | _) | ⟨c, args'⟩ | _
  · cases e
  · simp only [liftR, flatStatus] at e
    split at e <;> cases e
  · cases e
  · cases c with
    | host h' =>
      simp only [liftR, flatStatus] at e
      split at e
      · simp only [mapHostS, Silmaril.Wasm.Component.Engine.Status.callout.injEq] at e
        exact ⟨args', by rw [e.1]⟩
      · cases e
    | fx F => cases e
  · cases e

/-- `liftR` is the flat status renamed, off FX callouts. -/
theorem liftR_eq {st : Silmaril.Wasm.SingleThreaded.Status (FXCode H)}
    (hn : ∀ F args, st ≠ .callout (.fx F) args) : liftR st = mapHostS (flatStatus st) := by
  rcases st with _ | (vs | _) | ⟨c, args'⟩ | _
  · rfl
  · rfl
  · rfl
  · cases c with
    | host h' => rfl
    | fx F => exact absurd rfl (hn F args')
  · rfl

/-- A flat callout of a component host function is a callout of the FX engine. -/
theorem liftR_of_flat_host {st : Silmaril.Wasm.SingleThreaded.Status (FXCode H)} {h : H}
    {args : List Silmaril.Wasm.Component.Engine.FlatValue}
    (e : flatStatus st = .callout (.host h) args) : liftR st = .callout h args := by
  rw [liftR_eq, e]
  · rfl
  · rintro F args' rfl
    simp only [flatStatus] at e
    split at e <;> cases e

theorem mapHostS_eq_running {st : Silmaril.Wasm.Component.Engine.Status (FXCode H)}
    (e : mapHostS st = .running) : st = .running := by
  rcases st with _ | _ | ⟨c, _⟩ | _
  · rfl
  · cases e
  · cases c <;> cases e
  · cases e

/-! ## No step off `running` -/

/-- The status of an FX thread is `running` exactly when it can step. -/
theorem fxResult_ne_running (code : List Silmaril.Wasm.Models.FX.AdminFX) :
    (fxResult code : Silmaril.Wasm.Component.Engine.Status H) ≠ .running := by
  unfold fxResult
  split_ifs
  · split <;> simp
  all_goals simp

theorem fxResult_ne_callout (code : List Silmaril.Wasm.Models.FX.AdminFX) (h : H) args :
    (fxResult code : Silmaril.Wasm.Component.Engine.Status H) ≠ .callout h args := by
  unfold fxResult
  split_ifs
  · split <;> simp
  all_goals simp

/-- A Core thread whose status is not `running` takes no internal step. -/
theorem no_step_core_of_ne_running {s : Store (FXCode H)} {t₀ : Thread}
    (hr : statusFX P s (.core t₀) ≠ .running) (y : Store (FXCode H) × ThreadFX H) :
    ¬ InternalFX P (s, .core t₀) y := by
  have hfx : ∀ F args, statusP P s t₀ ≠ .callout (.fx F) args := by
    rintro F args e
    exact hr (by simp only [statusFX, e, liftR])
  have hcr : (core3P P).status s t₀ ≠ .running := by
    intro e
    apply hr
    show liftR (statusP P s t₀) = .running
    rw [liftR_eq hfx]
    exact (show flatStatus (statusP P s t₀) = .running from e) ▸ rfl
  have L := Silmaril.Wasm.Component.Param.core3P_lawful P
  rintro (⟨t', -, hstep⟩ | ⟨⟨F, args, e⟩, -⟩)
  · show False
    generalize hst : (core3P P).status s t₀ = st at hcr
    rcases st with _ | r | ⟨c, args⟩ | _
    · exact hcr rfl
    · exact L.returned_no_step hst hstep
    · exact L.callout_no_step hst hstep
    · exact L.stuck_no_step hst hstep
  · exact hfx F args e

/-- **A thread whose status is not `running` takes no internal step.** -/
theorem no_step_of_ne_running {s : Store (FXCode H)} {t : ThreadFX H}
    (hr : statusFX P s t ≠ .running) (y : Store (FXCode H) × ThreadFX H) :
    ¬ InternalFX P (s, t) y := by
  cases t with
  | core t₀ => exact no_step_core_of_ne_running hr y
  | fx K f code =>
    intro hy
    apply hr
    simp only [statusFX, show ∃ y, InternalFX P (s, .fx K f code) y from ⟨y, hy⟩, ite_true]
  | parked => exact fun h => h

/-! ## Growth is extension -/

/-- **Growth is store extension of the FX engine.** -/
theorem Grows.extendsFX {s s' : Store (FXCode H)} (hg : Grows s s') :
    (fxE P).Extends s s' where
  funcType _ _ h := hg.funcType h
  memAddrType _ _ h := hg.memAddrType h
  memSize _ _ h := hg.memSize h
  tableAddrType _ _ h := hg.tableAddrType h
  callout t hc args h := by
    change statusFX P s' t = .callout hc args
    change statusFX P s t = .callout hc args at h
    cases t with
    | core t₀ =>
      simp only [statusFX] at h ⊢
      obtain ⟨args', e⟩ := liftR_eq_callout h
      rw [statusP_callout_prefix' (P := P) hg.funcs e, ← e]
      exact h
    | fx K f code =>
      simp only [statusFX] at h
      split_ifs at h
      exact absurd h (fxResult_ne_callout code hc args)
    | parked => exact h

/-! ## Callouts of allocated host functions -/

/-- **Invoking an allocated host function is a callout.** -/
theorem statusFX_allocHost_callout {s s' : Store (FXCode H)} {ft : Silmaril.Wasm.V1.FuncType}
    {h : H} {a : Nat} {args : List Silmaril.Wasm.Component.Engine.FlatValue}
    (e : Silmaril.Wasm.SingleThreaded.allocHost s ft (FXCode.host h) = (s', a))
    (hn : args.length = ft.params.length) :
    statusFX P s' (.core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a args)) =
      .callout h args := by
  have hc := (Silmaril.Wasm.Component.Param.core3P_lawful P).allocHost_callout
    (H := FXCode H) (h := FXCode.host h) e hn
  exact liftR_of_flat_host hc

end Silmaril.Proofs.Wasm.Component.FXEngine
