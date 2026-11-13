module

public import Silmaril.Wasi.Versions.P2.Io.Defs
public import Silmaril.Wasi.Theory.Thms

@[expose] public section

/-!
# WASI 0.2 `wasi:io`: the strict reading refines the loose one, and strictly

* `ansOk_loose_of_strict`, `run_loose_of_strict`, `loose_of_strict`: every answer sequence the
  strict reading accepts, the loose one accepts (with the same states).
* `run_eq_fold`: the state of an accepted run is the fold of `ioNext`, whatever the reading.
* `sepTrace`, `loose_sepTrace`, `not_strict_sepTrace`, **`strict_ne_loose`**: a separating
  answer sequence. A stream's pollable answers `ready = true`, then `check-write` answers `ok(0)`:
  the loose reading accepts it, the strict one rejects it.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- Dropping the non-emptiness requirement of a read answer. -/
theorem bytesAns_of_nonempty {b : Nat} {ne : Bool} {res : Option (List Val)}
    (h : bytesAns b ne res = true) : bytesAns b false res = true := by
  unfold bytesAns at h ⊢
  split <;> simp_all

/-- An answer admissible in the strict reading is admissible in the loose one. -/
theorem ansOk_loose_of_strict {s : IoSt} {o : IoOp} {a : List Val} {res : Option (List Val)}
    (h : ansOk .strict s o a res = true) : ansOk .loose s o a res = true := by
  cases o
  case bread =>
    have h' : stickyOk s (selfOf a) res = true ∧
        bytesAns (lenOf a) (decide (0 < lenOf a)) res = true := by simpa [ansOk] using h
    have hb : (Reading.loose == Reading.strict) = false := rfl
    simpa [ansOk, hb] using And.intro h'.1 (bytesAns_of_nonempty h'.2)
  all_goals simp_all [ansOk]

/-- One strict step is a loose step. -/
theorem step_loose_of_strict {s s' : IoSt} {e : WEv} (h : ioStep .strict s e = some s') :
    ioStep .loose s e = some s' := by
  cases e
  case imp f a res =>
    by_cases hok : ansOk .strict s (ioOp f) a res = true
    · have hl : ansOk .loose s (ioOp f) a res = true := ansOk_loose_of_strict hok
      simpa [ioStep, hok, hl] using h
    · simp [ioStep, hok] at h
  all_goals exact h

/-- **Strict runs are loose runs.** -/
theorem run_loose_of_strict (t : List WEv) {s s' : IoSt} (h : ioStrict.run s t = some s') :
    ioLoose.run s t = some s' := by
  induction t generalizing s with
  | nil => exact h
  | cons e t ih =>
    obtain ⟨q, hq, hrun⟩ := Option.bind_eq_some_iff.1 h
    have hq' : ioStep .loose s e = some q := step_loose_of_strict hq
    show (ioStep .loose s e).bind (fun q => ioLoose.run q t) = some s'
    rw [hq']
    exact ih hrun

/-- **The strict reading refines the loose one.** -/
theorem loose_of_strict {t : List WEv} (h : ioStrict.Accepts t) : ioLoose.Accepts t := by
  obtain ⟨q, hq⟩ := (Protocol.accepts_iff_exists _ _).1 h
  exact (Protocol.accepts_iff_exists _ _).2 ⟨q, run_loose_of_strict t hq⟩

/-- A step of the theory is `ioNext`. -/
theorem step_eq_next {r : Reading} {s s' : IoSt} {e : WEv} (h : ioStep r s e = some s') :
    s' = ioNext s e := by
  cases e
  case imp f a res =>
    by_cases hok : ansOk r s (ioOp f) a res = true
    · simp only [ioStep, hok, ite_true, Option.some.injEq] at h
      exact h.symm
    · simp [ioStep, hok] at h
  all_goals exact (Option.some.inj h).symm

/-- **The state of an accepted run** is the fold of `ioNext`. -/
theorem run_eq_fold {r : Reading} (t : List WEv) {s s' : IoSt} (h : (ioTh r).run s t = some s') :
    s' = t.foldl ioNext s := by
  induction t generalizing s with
  | nil => exact (Option.some.inj h).symm
  | cons e t ih =>
    obtain ⟨q, hq, hrun⟩ := Option.bind_eq_some_iff.1 h
    have hqe : q = ioNext s e := step_eq_next hq
    rw [List.foldl_cons, ← hqe]
    exact ih hrun

/-! ## The separation -/

/-- A separating answer sequence: stream `0`'s pollable `1` is ready, then `check-write` on
stream `0` answers `ok(0)`. -/
def sepTrace : List WEv :=
  [.imp osSubscribe [.u32 0] (some [.u32 1]), .imp pollReady [.u32 1] (some [.bool true]),
   .imp osCheckWrite [.u32 0] (some [okV (some (.u64 0))])]

/-- The loose reading accepts `sepTrace`. -/
theorem loose_sepTrace : ioLoose.Accepts sepTrace := (Protocol.acceptsB_iff _ _).1 (by decide)

/-- The strict reading rejects `sepTrace`. -/
theorem not_strict_sepTrace : ¬ ioStrict.Accepts sepTrace := fun h =>
  absurd ((Protocol.acceptsB_iff _ _).2 h) (by decide)

/-- **The strict reading is strictly stronger than the loose one.** -/
theorem strict_ne_loose : ∃ t, ioLoose.Accepts t ∧ ¬ ioStrict.Accepts t :=
  ⟨sepTrace, loose_sepTrace, not_strict_sepTrace⟩

end Silmaril.Wasi.Versions.P2
