module

public import Silmaril.Wasm.Models.FXL.Defs

/-!
# `StepFXL` is deterministic: a finished run is the only behaviour

* `runN_stop_mono`: once a run stops, every longer run stops with the same outcome;
* **`beh_eq`**: if a run of `n` steps stops with outcome `o`, then `o` is the configuration's
  only behaviour (no other outcome, no divergence).

So a trace computed by `runN` (a closed evaluation, checked with `decide +kernel`) is *the*
observable behaviour of the program.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXL

variable {P : Prog} {ar : Nat → Nat}

/-- **Once a run stops, longer runs stop with the same outcome.** -/
theorem runN_stop_mono {o : Outcome} :
    ∀ {n : Nat} {c : Cfg}, runN P ar n c = .stop o → ∀ m, n ≤ m → runN P ar m c = .stop o := by
  intro n
  induction n with
  | zero => intro c h; exact absurd h (by simp [runN])
  | succ n ih =>
    intro c h m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold runN at h ⊢
    cases hs : step P ar c with
    | next c' =>
      rw [hs] at h
      exact ih h m (by omega)
    | stop o' =>
      rw [hs] at h
      exact h

/-- A result whose outcome is `o` stopped with `o`. -/
theorem Res.eq_of_out {r : Res} {o : Outcome} (h : r.out = some o) : r = .stop o := by
  cases r with
  | next c => exact absurd h (by simp [Res.out])
  | stop o' => exact congrArg Res.stop (Option.some.inj h)

/-- **A finished run is the only behaviour.** -/
theorem beh_eq {n : Nat} {c : Cfg} {o : Outcome} (h : runN P ar n c = .stop o) :
    beh P ar c = {o.toObs} := by
  ext b
  constructor
  · rintro (⟨m, o', hm, rfl⟩ | ⟨-, hdiv⟩)
    · have h₁ : runN P ar (max n m) c = .stop o := runN_stop_mono h _ (Nat.le_max_left n m)
      have h₂ : runN P ar (max n m) c = .stop o' := runN_stop_mono hm _ (Nat.le_max_right n m)
      have ho : o' = o := by
        rw [h₁] at h₂
        exact (Res.stop.inj h₂).symm
      rw [ho]
      rfl
    · obtain ⟨c', hc'⟩ := hdiv n
      rw [h] at hc'
      exact absurd hc' (by simp)
  · intro hb
    exact Or.inl ⟨n, o, h, hb⟩

/-- `beh_eq` from a computed outcome. -/
theorem beh_eq_of_out {n : Nat} {c : Cfg} {o : Outcome} (h : (runN P ar n c).out = some o) :
    beh P ar c = {o.toObs} :=
  beh_eq (Res.eq_of_out h)

end Silmaril.Wasm.Models.FXL
