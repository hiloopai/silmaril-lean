module

public import Silmaril.Wasm.Component.FXRes.ContEngine.Defs
public import Silmaril.Wasm.Component.FXRes.Engine.Thms
public import Silmaril.Wasm.Resource.Table.Thms

/-!
# The WasmFX engine with a continuation table: step lemmas

* `bstep_tab`, `internalC_tab`: a built-in call moves the table by its event (none for a
  trap); every other internal step keeps the table;
* `bstep_kstep`, `internalC_kstep`: every internal step changes the thread's continuation store
  by a `KStep` (`new` consumes, `take` appends, `drop` and traps keep it);
* `cRun_tab`, `cRun_ksteps`: along thread runs (`CRun`), the table moves by a successful table
  history and the store by a `KSteps`;
* `prepareC_tab`, `allocHostC_tab`, `memWriteC_tab`: the engine operations the machine uses
  besides internal steps keep the table.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContEngine

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (ContFX AdminFX)
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXRes
open Silmaril.Wasm.Component.Reference (core3P)
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- Runs of one thread of `fxCE P`: internal steps, and resumptions after which the engine store
may have changed in any way that keeps the table (as the engine operations other than internal
steps do). -/
inductive CRun (P : Profile) : EStore H × ThreadV (CH H) → EStore H × ThreadV (CH H) → Prop where
  | refl (x : EStore H × ThreadV (CH H)) : CRun P x x
  | step {x y z : EStore H × ThreadV (CH H)} (h : InternalC P x y) (r : CRun P y z) : CRun P x z
  | resume {s s' : EStore H} {t : ThreadV (CH H)} {res : Silmaril.Wasm.Component.Engine.CallResult}
      {z : EStore H × ThreadV (CH H)} (hs : s'.tab = s.tab) (r : CRun P (s', resumeV s.core t res) z) :
      CRun P (s, t) z

theorem steps_single {t t' : Table ContFX} {ev : Table.Event ContFX}
    (h : t.step? ev.op = some (ev, t')) : Table.Steps t [ev] t' :=
  .cons h (.nil _)

theorem steps_added {t t' : Table ContFX} {C : ContFX} {n : ℕ} (ht : t.add? C = some (n, t')) :
    Table.Steps t [.added n C] t' :=
  steps_single (by simp [Table.step?, Table.Event.op, ht])

theorem steps_removed {t t' : Table ContFX} {C : ContFX} {n : ℕ}
    (ht : t.remove? n = some (C, t')) : Table.Steps t [.removed n C] t' :=
  steps_single (by simp [Table.step?, Table.Event.op, ht])

/-- A built-in call moves the table by its event. -/
theorem bstep_tab {x y : EStore H × ThreadV (CH H)} {ev : Option (Table.Event ContFX)}
    (h : BStep x y ev) : Table.Steps x.1.tab ev.toList y.1.tab := by
  cases h with
  | new _ _ _ ht => exact steps_added ht
  | take _ _ ht => exact steps_removed ht
  | drop _ _ ht => exact steps_removed ht
  | newUsed => exact .nil _
  | newFull => exact .nil _
  | dead => exact .nil _

/-- Every internal step moves the table by a successful history of at most one event. -/
theorem internalC_tab {x y : EStore H × ThreadV (CH H)} (h : InternalC P x y) :
    ∃ evs, Table.Steps x.1.tab evs y.1.tab := by
  rcases h with ⟨ht, -, -⟩ | ⟨ev, hb⟩
  · exact ⟨[], ht ▸ .nil _⟩
  · exact ⟨_, bstep_tab hb⟩

/-- A built-in call changes the thread's store by a `KStep`. -/
theorem bstep_kstep {x y : EStore H × ThreadV (CH H)} {ev : Option (Table.Event ContFX)}
    (h : BStep x y ev) : ∃ evs, KStep (threadConts x.2) (threadConts y.2) evs := by
  cases h
  case new hk _ => exact ⟨_, .consume hk⟩
  case take => exact ⟨_, .alloc _ _⟩
  all_goals exact ⟨_, .same _⟩

/-- Every internal step changes the thread's store by a `KStep`. -/
theorem internalC_kstep {x y : EStore H × ThreadV (CH H)} (h : InternalC P x y) :
    ∃ evs, KStep (threadConts x.2) (threadConts y.2) evs := by
  rcases h with ⟨-, hv, -⟩ | ⟨ev, hb⟩
  · exact internalV_kstep hv
  · exact bstep_kstep hb

theorem steps_append' {t₁ t₂ t₃ : Table ContFX} {e₁ e₂ : List (Table.Event ContFX)}
    (h₁ : Table.Steps t₁ e₁ t₂) (h₂ : Table.Steps t₂ e₂ t₃) : Table.Steps t₁ (e₁ ++ e₂) t₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

/-- Along a thread run the table moves by a successful history. -/
theorem cRun_tab {x y : EStore H × ThreadV (CH H)} (h : CRun P x y) :
    ∃ evs, Table.Steps x.1.tab evs y.1.tab := by
  induction h with
  | refl => exact ⟨[], .nil _⟩
  | step hi _ ih =>
    obtain ⟨e₁, h₁⟩ := internalC_tab hi
    obtain ⟨e₂, h₂⟩ := ih
    exact ⟨_, steps_append' h₁ h₂⟩
  | resume hs _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨e, hs ▸ he⟩

/-- Along a thread run the store changes by a `KSteps`. -/
theorem cRun_ksteps {x y : EStore H × ThreadV (CH H)} (h : CRun P x y) :
    ∃ evs, KSteps (threadConts x.2) (threadConts y.2) evs := by
  induction h with
  | refl => exact ⟨[], .refl _⟩
  | step hi _ ih =>
    obtain ⟨e₁, h₁⟩ := internalC_kstep hi
    obtain ⟨e₂, h₂⟩ := ih
    exact ⟨_, .cons h₁ h₂⟩
  | @resume s s' t res z _ _ ih =>
    obtain ⟨e, he⟩ := ih
    have hc : threadConts (resumeV s.core t res) = threadConts t := resumeV_conts s.core t res
    exact ⟨e, hc ▸ he⟩

/-- Instantiation keeps the table. -/
theorem prepareC_tab {s s' : EStore H} {m : ModuleFX} {xas : List ExternAddr} {i : InstFX}
    {st : Option ℕ} (h : prepareC? s m xas = some (s', i, st)) : s'.tab = s.tab := by
  unfold prepareC? at h
  split at h
  · cases h; rfl
  · cases h

/-- Allocating a host function keeps the table. -/
theorem allocHostC_tab (s : EStore H) (ft : Silmaril.Wasm.V1.FuncType) (h : H) :
    ((fxCE P).allocHost s ft h).1.tab = s.tab := rfl

/-- Writing a memory keeps the table. -/
theorem memWriteC_tab {s s' : EStore H} {m st : ℕ} {bs : ByteArray}
    (h : (fxCE P).memWrite? s m st bs = some s') : s'.tab = s.tab := by
  change (((core3P P).memWrite? s.core m st bs).map fun c => (⟨c, s.tab⟩ : EStore H)) = some s'
    at h
  obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

end Silmaril.Wasm.Component.FXRes.ContEngine
