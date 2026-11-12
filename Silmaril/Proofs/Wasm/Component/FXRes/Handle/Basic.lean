module

public import Silmaril.Wasm.Component.FXRes.Handle.Defs
public import Silmaril.Wasm.Component.FXRes.Thms
public import Silmaril.Wasm.Resource.Table.Thms

/-!
# Continuations as Component Model resources: proofs

* `rstep_tab`, `rstep_store`: a built-in is one successful table operation and one store change;
  `jsteps_tab`, `jsteps_store`: a joint run's table history is a `Table.Steps` history and its
  store history a `KSteps` history.
* `client_run_own`: a history accepted by the client handle protocol, read as ownership events
  of handles that are all owned, is accepted by `obProto`.
* `remove?_dead`, `rstep_live`, `rstep_borrow`, `rstep_new`: a removed handle is dead, built-ins
  other than `new` need a live handle, `borrow` changes nothing, `new` moves the continuation.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

theorem rstep_tab {st st' : JState H} {o : ROp} {ev : Table.Event ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st o ev sevs st') : st.tab.step? ev.op = some (ev, st'.tab) := by
  cases h with
  | new _ ht => simp [Table.step?, Table.Event.op, ht]
  | take ht => simp [Table.step?, Table.Event.op, ht]
  | drop ht => simp [Table.step?, Table.Event.op, ht]
  | borrow ht => simp [Table.step?, Table.Event.op, ht]

theorem rstep_store {st st' : JState H} {o : ROp} {ev : Table.Event ContFX}
    {sevs : List (HEv ℕ)} (h : RStep st o ev sevs st') : KStep st.cfg.conts st'.cfg.conts sevs := by
  cases h with
  | new hk _ => exact .consume hk
  | take _ => exact .alloc _ _
  | drop _ => exact .same _
  | borrow _ => exact .same _

theorem table_steps_single {t t' : Table ContFX} {ev : Table.Event ContFX}
    (h : t.step? ev.op = some (ev, t')) : Table.Steps t [ev] t' :=
  .cons h (.nil t')

theorem table_steps_append {t₁ t₂ t₃ : Table ContFX} {e₁ e₂ : List (Table.Event ContFX)}
    (h₁ : Table.Steps t₁ e₁ t₂) (h₂ : Table.Steps t₂ e₂ t₃) : Table.Steps t₁ (e₁ ++ e₂) t₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem jstep_tab {st st' : JState H} {tevs : List (Table.Event ContFX)} {sevs : List (HEv ℕ)}
    (h : JStep P host fx st tevs sevs st') : Table.Steps st.tab tevs st'.tab := by
  cases h with
  | fx _ _ => exact .nil _
  | op h => exact table_steps_single (rstep_tab h)

theorem jstep_store {st st' : JState H} {tevs : List (Table.Event ContFX)}
    {sevs : List (HEv ℕ)} (h : JStep P host fx st tevs sevs st') :
    KSteps st.cfg.conts st'.cfg.conts sevs := by
  cases h with
  | fx _ hk => exact ksteps_single hk
  | op h => exact ksteps_single (rstep_store h)

theorem jsteps_tab {st st' : JState H} {tevs : List (Table.Event ContFX)} {sevs : List (HEv ℕ)}
    (h : JSteps P host fx st tevs sevs st') : Table.Steps st.tab tevs st'.tab := by
  induction h with
  | refl => exact .nil _
  | cons h₁ _ ih => exact table_steps_append (jstep_tab h₁) ih

theorem jsteps_store {st st' : JState H} {tevs : List (Table.Event ContFX)}
    {sevs : List (HEv ℕ)} (h : JSteps P host fx st tevs sevs st') :
    KSteps st.cfg.conts st'.cfg.conts sevs := by
  induction h with
  | refl => exact .refl _
  | cons h₁ _ ih => exact ksteps_trans (jstep_store h₁) ih

theorem jstep_of_fx {t : Table ContFX} {c c' : ConfigFX H} (h : StepFX' P host fx c c') :
    ∃ sevs, JStep P host fx ⟨t, c⟩ [] sevs ⟨t, c'⟩ := by
  obtain ⟨sevs, hk⟩ := kstep_of_stepFX' h
  exact ⟨sevs, .fx h hk⟩

/-! ## Ownership -/

/-- Every handle owned. -/
def owned (L : List ℕ) : List (ℕ × Mode) := L.map fun h => (h, .owned)

theorem held_owned (L : List ℕ) (h : ℕ) : held (owned L) h = decide (h ∈ L) := by
  rw [Bool.eq_iff_iff]
  simp [held, owned, List.any_eq_true]

theorem owns_owned (L : List ℕ) (h : ℕ) : owns (owned L) h = decide (h ∈ L) := by
  simp [owns, owned]

theorem release_owned {L : List ℕ} (hL : L.Nodup) (h : ℕ) :
    release (owned L) h = owned (L.erase h) := by
  rw [hL.erase_eq_filter]
  simp [release, owned, List.filter_map, Function.comp_def]

theorem own_alloc {L L' : List ℕ} {i : ℕ} (hL : L.Nodup)
    (h : handleStep .client (some L) (.alloc i) = some (some L')) :
    obStep (some (owned L)) (hevOwn (.alloc i)) = some (some (owned L')) ∧ L'.Nodup := by
  by_cases hi : i ∈ L
  · simp [handleStep, hi, fault] at h
  · have hL' : i :: L = L' := by simpa [handleStep, hi] using h
    have ho : obStep (some (owned L)) (.alloc i) = some (some (owned (i :: L))) := by
      show (if held (owned L) i then some none else some (some ((i, Mode.owned) :: owned L))) = _
      rw [held_owned, decide_eq_false hi]
      rfl
    exact hL' ▸ ⟨ho, List.nodup_cons.2 ⟨hi, hL⟩⟩

theorem own_use {L L' : List ℕ} {i : ℕ} (hL : L.Nodup)
    (h : handleStep .client (some L) (.use i) = some (some L')) :
    obStep (some (owned L)) (hevOwn (.use i)) = some (some (owned L')) ∧ L'.Nodup := by
  by_cases hi : i ∈ L
  · have hL' : L = L' := by simpa [handleStep, hi] using h
    have ho : obStep (some (owned L)) (.use i) = some (some (owned L)) := by
      show (if held (owned L) i then some (some (owned L)) else none) = _
      rw [held_owned, decide_eq_true hi]
      rfl
    exact hL' ▸ ⟨ho, hL⟩
  · simp [handleStep, hi, fault] at h

theorem own_free {L L' : List ℕ} {i : ℕ} (hL : L.Nodup)
    (h : handleStep .client (some L) (.free i) = some (some L')) :
    obStep (some (owned L)) (hevOwn (.free i)) = some (some (owned L')) ∧ L'.Nodup := by
  by_cases hi : i ∈ L
  · have hL' : L.erase i = L' := by simpa [handleStep, hi] using h
    have ho : obStep (some (owned L)) (.free i) = some (some (owned (L.erase i))) := by
      show (if owns (owned L) i then some (some (release (owned L) i)) else none) = _
      rw [owns_owned, decide_eq_true hi, release_owned hL]
      rfl
    exact hL' ▸ ⟨ho, hL.erase i⟩
  · simp [handleStep, hi, fault] at h

/-- One client handle step, read as an ownership step of owned handles. -/
theorem client_step_own {L L' : List ℕ} {e : HEv ℕ} (hL : L.Nodup)
    (h : handleStep .client (some L) e = some (some L')) :
    obStep (some (owned L)) (hevOwn e) = some (some (owned L')) ∧ L'.Nodup := by
  cases e with
  | alloc i => exact own_alloc hL h
  | use i => exact own_use hL h
  | free i => exact own_free hL h
  | skip =>
    have hL' : L = L' := by simpa [handleStep] using h
    exact hL' ▸ ⟨rfl, hL⟩

theorem run_none {r : Role} (t : List (HEv ℕ)) : (handleProto ℕ r).run none t = some none := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    rw [Protocol.run_cons]
    exact ih

/-- A successful client run of `e :: t` starts with a successful step. -/
theorem client_run_cons {L L' : List ℕ} {e : HEv ℕ} {t : List (HEv ℕ)}
    (h : (handleProto ℕ .client).run (some L) (e :: t) = some (some L')) :
    ∃ L₁, handleStep .client (some L) e = some (some L₁) ∧
      (handleProto ℕ .client).run (some L₁) t = some (some L') := by
  rw [Protocol.run_cons, step_eq] at h
  cases hs : handleStep .client (some L) e with
  | none => simp [hs] at h
  | some q =>
    rw [hs] at h
    cases q with
    | none =>
      have h' : (handleProto ℕ .client).run none t = some (some L') := h
      rw [run_none] at h'
      cases h'
    | some L₁ => exact ⟨L₁, rfl, h⟩

/-- **A client-accepted handle history is an ownership history of owned handles.** -/
theorem client_run_own {evs : List (HEv ℕ)} :
    ∀ {L L' : List ℕ}, L.Nodup →
      (handleProto ℕ .client).run (some L) evs = some (some L') →
      (obProto ℕ).run (some (owned L)) (evs.map hevOwn) = some (some (owned L')) := by
  induction evs with
  | nil =>
    intro L L' _ h
    have hL : L = L' := by simpa [Protocol.run] using h
    exact hL ▸ rfl
  | cons e t ih =>
    intro L L' hL h
    obtain ⟨L₁, hs, ht⟩ := client_run_cons h
    obtain ⟨ho, hL₁⟩ := client_step_own hL hs
    rw [List.map_cons, Protocol.run_cons]
    change (obStep (some (owned L)) (hevOwn e)).bind _ = _
    rw [ho]
    exact ih hL₁ ht

/-! ## Liveness of handles -/

theorem remove?_dead {t t' : Table ContFX} {i : ℕ} {C : ContFX} (h : t.remove? i = some (C, t')) :
    t'.get? i = none := by
  obtain ⟨hg, rfl⟩ := remove?_parts h
  obtain ⟨arr, fr⟩ := t
  have hlt : i < arr.size := lt_of_getElem?_eq_some (getElem?_of_get? hg)
  simp [Table.get?, hlt]

theorem rstep_live {st st' : JState H} {o : ROp} {ev : Table.Event ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st o ev sevs st') (ho : o ≠ .new) :
    ∃ i C, st.tab.get? i = some C ∧ (ev = .removed i C ∨ ev = .got i C) := by
  cases h with
  | new _ _ => exact absurd rfl ho
  | take ht => exact ⟨_, _, (remove?_parts ht).1, .inl rfl⟩
  | drop ht => exact ⟨_, _, (remove?_parts ht).1, .inl rfl⟩
  | borrow ht => exact ⟨_, _, ht, .inr rfl⟩

theorem rstep_removed {st st' : JState H} {o : ROp} {i : ℕ} {C : ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st o (.removed i C) sevs st') : st'.tab.get? i = none := by
  cases h with
  | take ht => exact remove?_dead ht
  | drop ht => exact remove?_dead ht

theorem rstep_borrow {st st' : JState H} {ev : Table.Event ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st .borrow ev sevs st') : st' = st ∧ sevs = [] := by
  cases h with
  | borrow _ => exact ⟨rfl, rfl⟩

theorem rstep_new {st st' : JState H} {ev : Table.Event ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st .new ev sevs st') :
    ∃ k i C, st.cfg.conts[k]? = some (some C) ∧ Consumed st'.cfg.conts k ∧ ev = .added i C ∧
      st.tab.add? C = some (i, st'.tab) := by
  cases h with
  | new hk ht =>
    rename_i K f k i C rest
    have hlt : k < K.length := (List.getElem?_eq_some_iff.1 hk).1
    have hc : Consumed (K.set k none) k := by simp [Consumed, hlt]
    exact ⟨k, i, C, hk, hc, rfl, ht⟩

end Silmaril.Wasm.Component.FXRes
