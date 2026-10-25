module

public import Silmaril.Wasm.SingleThreaded.Thread
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-! # Computable thread status and a fuelled runner

`status` (`SingleThreaded/Thread.lean`) is noncomputable only through three
propositional tests. `statusC` replaces them by Boolean tests (`splitVals`,
`isTrap?`, `isThrowing?`) and, for the existence of an internal step, by
`(stepC c).isSome` for a Core step function `stepC` supplied as a parameter
(so this file does not depend on a particular executable step function).

* `statusC_eq`: `statusC stepC s t = status o s t` when `stepC` is sound and
  complete at `t.config s` for the internal (host-free) step relation.
* `internalC`: a computable internal step, sound for `Internal o`.
* `runC`: iterate `internalC` while `statusC = .running`, with fuel;
  `runC_sound`: the result is reachable by internal steps, and a non-`running`
  result is the true `status` (given completeness at the final state).
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Boolean tests -/

def isTrap? : List Admin → Bool
  | [.trap] => true
  | _ => false

def isThrowing? : List Admin → Bool
  | [.ref (.exn _), .plain .throwRef] => true
  | _ => false

theorem isTrap?_iff (l : List Admin) : isTrap? l = true ↔ l = [.trap] := by
  constructor
  · intro h
    unfold isTrap? at h
    split at h
    · rfl
    · cases h
  · rintro rfl; rfl

theorem isThrowing?_iff (l : List Admin) : isThrowing? l = true ↔ ∃ a, l = throwing a := by
  constructor
  · intro h
    unfold isThrowing? at h
    split at h
    · exact ⟨_, rfl⟩
    · cases h
  · rintro ⟨a, rfl⟩; rfl

theorem exists_vals_iff (l : List Admin) : (∃ vs, l = vals vs) ↔ (splitVals l).2.isEmpty = true := by
  constructor
  · rintro ⟨vs, rfl⟩
    rw [splitVals_vals]; rfl
  · intro h
    refine ⟨(splitVals l).1, ?_⟩
    have := splitVals_spec l
    rw [List.isEmpty_iff.mp h, List.append_nil] at this
    exact this

/-! ## Computable status -/

/-- The computable status of a thread, relative to a Core step function. -/
def statusC (stepC : Config H → Option (Config H)) (s : Store H) (t : Thread) : Status H :=
  let c := t.config s
  if (splitVals c.code).2.isEmpty then .returned (.values (splitVals c.code).1)
  else if isTrap? c.code then .returned .trap
  else if isThrowing? c.code then .returned .trap
  else match decompose? s c.code with
    | some (_, _, h, args) => .callout h args
    | none => if (stepC c).isSome then .running else .stuck

theorem statusC_eq {stepC : Config H → Option (Config H)} {s : Store H} {t : Thread}
    (o : GrowOracle)
    (hsound : ∀ c', stepC (t.config s) = some c' →
      Step (profile o) (fun _ _ _ _ => False) (t.config s) c')
    (hcomplete : ∀ c', Step (profile o) (fun _ _ _ _ => False) (t.config s) c' →
      (stepC (t.config s)).isSome) :
    statusC stepC s t = status o s t := by
  unfold statusC status
  dsimp only
  by_cases h1 : ∃ vs, (t.config s).code = vals vs
  · rw [dite_eq_left h1, ite_eq_left ((exists_vals_iff _).mp h1)]
    congr 2
    have e1 := h1.choose_spec
    have e2 := splitVals_spec (t.config s).code
    rw [List.isEmpty_iff.mp ((exists_vals_iff _).mp h1), List.append_nil] at e2
    exact vals_injective (e2.symm.trans e1)
  rw [dite_eq_right h1, ite_eq_right (fun h => h1 ((exists_vals_iff _).mpr h))]
  by_cases h2 : (t.config s).code = [.trap]
  · rw [ite_eq_left h2, ite_eq_left ((isTrap?_iff _).mpr h2)]
  rw [ite_eq_right h2, ite_eq_right (fun h => h2 ((isTrap?_iff _).mp h))]
  by_cases h3 : ∃ a, (t.config s).code = throwing a
  · rw [ite_eq_left h3, ite_eq_left ((isThrowing?_iff _).mpr h3)]
  rw [ite_eq_right h3, ite_eq_right (fun h => h3 ((isThrowing?_iff _).mp h))]
  cases decompose? s (t.config s).code with
  | some x => rfl
  | none =>
    dsimp only
    have hiff : (stepC (t.config s)).isSome = true ↔ ∃ y, Internal o (s, t) y := by
      constructor
      · intro h
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp h
        refine ⟨(c'.store, .active c'.frame c'.code), c'.frame, c'.code, rfl, ?_⟩
        exact hsound c' hc'
      · rintro ⟨⟨s', t'⟩, f', code', _, hst⟩
        exact hcomplete _ hst
    by_cases h5 : ∃ y, Internal o (s, t) y
    · rw [ite_eq_left h5, ite_eq_left (hiff.mpr h5)]
    · rw [ite_eq_right h5, ite_eq_right (fun h => h5 (hiff.mp h))]

/-! ## Computable internal step -/

/-- A computable internal step: the successor configuration as an active thread. -/
def internalC (stepC : Config H → Option (Config H)) (p : Store H × Thread) :
    Option (Store H × Thread) :=
  (stepC (p.2.config p.1)).map fun c' => (c'.store, .active c'.frame c'.code)

theorem internalC_sound {stepC : Config H → Option (Config H)} {s : Store H} {t : Thread}
    (o : GrowOracle)
    (hsound : ∀ c', stepC (t.config s) = some c' →
      Step (profile o) (fun _ _ _ _ => False) (t.config s) c')
    {y : Store H × Thread} (h : internalC stepC (s, t) = some y) : Internal o (s, t) y := by
  unfold internalC at h
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨c'.frame, c'.code, rfl, hsound c' hc'⟩

/-! ## Fuelled runner -/

/-- Run internal steps while the thread is `running`, for at most `fuel` steps.
Returns the final store, thread and status (`.running` when fuel ran out). -/
def runC (stepC : Config H → Option (Config H)) : Nat → Store H → Thread →
    Store H × Thread × Status H
  | 0, s, t => (s, t, .running)
  | n + 1, s, t =>
    match statusC stepC s t with
    | .running =>
      match internalC stepC (s, t) with
      | some (s', t') => runC stepC n s' t'
      | none => (s, t, .running)
    | st => (s, t, st)

theorem runC_sound {stepC : Config H → Option (Config H)} (o : GrowOracle)
    (hsound : ∀ (s : Store H) (t : Thread) c', stepC (t.config s) = some c' →
      Step (profile o) (fun _ _ _ _ => False) (t.config s) c')
    (fuel : Nat) (s : Store H) (t : Thread) {s' : Store H} {t' : Thread} {st : Status H}
    (h : runC stepC fuel s t = (s', t', st)) :
    Relation.ReflTransGen (Internal o) (s, t) (s', t') ∧
      (st ≠ .running →
        (∀ c', Step (profile o) (fun _ _ _ _ => False) (t'.config s') c' →
          (stepC (t'.config s')).isSome) →
        st = status o s' t') := by
  induction fuel generalizing s t with
  | zero =>
    simp only [runC, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨.refl, fun hne => absurd rfl hne⟩
  | succ n ih =>
    have fin : ∀ st₀, statusC stepC s t = st₀ → (s, t, st₀) = (s', t', st) →
        Relation.ReflTransGen (Internal o) (s, t) (s', t') ∧
        (st ≠ .running →
          (∀ c', Step (profile o) (fun _ _ _ _ => False) (t'.config s') c' →
            (stepC (t'.config s')).isSome) →
          st = status o s' t') := by
      intro st₀ hs h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨.refl, fun _ hc => ?_⟩
      rw [← hs]
      exact statusC_eq o (hsound s t) hc
    unfold runC at h
    cases hs : statusC stepC s t with
    | running =>
      rw [hs] at h
      dsimp only at h
      cases hi : internalC stepC (s, t) with
      | none =>
        rw [hi] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨.refl, fun hne => absurd rfl hne⟩
      | some p =>
        obtain ⟨s₁, t₁⟩ := p
        rw [hi] at h
        obtain ⟨hr, hst⟩ := ih s₁ t₁ h
        exact ⟨.head (internalC_sound o (hsound s t) hi) hr, hst⟩
    | returned r => rw [hs] at h; exact fin _ hs h
    | callout hc args => rw [hs] at h; exact fin _ hs h
    | stuck => rw [hs] at h; exact fin _ hs h

end Silmaril.Wasm.SingleThreaded

