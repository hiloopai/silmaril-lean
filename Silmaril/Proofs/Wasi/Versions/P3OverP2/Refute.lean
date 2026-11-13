module

public import Silmaril.Wasi.Versions.P3OverP2.Theory.Defs
public import Silmaril.Wasi.Versions.P3.Thms
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# Proofs: why the 0.3 theories are corrected, and that the corrections are weakenings

REFUTED (each by an explicit run):

* `stdoutTh3_rejects_nullary`, `fsReadTh3_rejects_nullary`: `stdoutTh3` rejects every answer to a
  `stream.write` with no arguments, `fsReadTh3 F` every answer to a `read-via-stream` with no
  arguments; `host3_not_stdoutTh3`, `host3_not_fsReadTh3`: runs of `host3` with such calls.
* `host3_zero_read`: `host3` answers `stream.read r 0` with `COMPLETED 0` on a non-empty file,
  which `fsReadTh3` rejects.
* `host3_clock_overflow`: after `wait-for (2^64 - 1)`, `now = 2^64 - 1`, `wait-for 1`, `host3`
  answers `now = 2^64 - 1`; `clockTh3` owes `2^64` and rejects every `u64`. The saturated
  `clockTh3s` accepts this run.

PROVED (weakenings): `stdoutTh3w_of`, `clockTh3s_of`: every run accepted by the original theory
is accepted by the corrected one (`clockTh3s_of` by the simulation `ClockSim`). For
`fsReadTh3w F`: `fsReadTh3w_of` in `Silmaril.Proofs.Wasi.Versions.P3OverP2.Weaken`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult blocked)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Os (follows_snoc follows_nil)

/-! ## Ill-shaped calls -/

/-- `stdoutTh3` rejects every answer to a `stream.write` with no arguments. -/
theorem stdoutTh3_rejects_nullary (q : OutSt) (r : Option (List Val)) :
    outStep q (.imp cStreamWrite [] r) = none := by
  cases r <;> rfl

/-- `fsReadTh3 F` rejects every answer to a `read-via-stream` with no arguments. -/
theorem fsReadTh3_rejects_nullary (F : BitVec 32 → List (BitVec 8)) (q : RdSt)
    (r : Option (List Val)) : rdStep F q (.imp readVia3 [] r) = none := by
  cases r <;> rfl

/-- **`host3` is not a model of `stdoutTh3`**: it answers `stream.write()`. -/
theorem host3_not_stdoutTh3 (F : BitVec 32 → List (BitVec 8)) :
    ∃ t, Follows (host3 F) t ∧ ¬ stdoutTh3.Accepts t :=
  ⟨[.imp cStreamWrite [] (host3 F [] cStreamWrite [])],
    follows_snoc (follows_nil _) rfl, by unfold Protocol.Accepts; exact Bool.false_ne_true⟩

/-- **`host3` is not a model of `fsReadTh3`**: it answers `read-via-stream()`. -/
theorem host3_not_fsReadTh3 (F : BitVec 32 → List (BitVec 8)) :
    ∃ t, Follows (host3 F) t ∧ ¬ (fsReadTh3 F).Accepts t :=
  ⟨[.imp readVia3 [] (host3 F [] readVia3 [])],
    follows_snoc (follows_nil _) rfl, by unfold Protocol.Accepts; exact Bool.false_ne_true⟩

/-! ## Zero-length reads -/

/-- `read-via-stream(0, 0)` then `stream.read(1, 0)` on `hello`. -/
def zeroRun : List WEv :=
  [.imp readVia3 [.u32 0, .u64 0] (some [.record [natV 1, natV 2]]),
   .imp cStreamRead [natV 1, natV 0] (some [natV (packCopy .completed 0), bytesV []])]

/-- **REFUTED: `host3` and zero-length reads.** The run follows `host3 helloFile` and is
rejected by `fsReadTh3 helloFile`; the corrected theory accepts it. -/
theorem host3_zero_read : Follows (host3 helloFile) zeroRun ∧
    ¬ (fsReadTh3 helloFile).Accepts zeroRun ∧ (fsReadTh3w helloFile).Accepts zeroRun := by
  refine ⟨?_, by unfold Protocol.Accepts; exact Bool.false_ne_true, rfl⟩
  have h1 := follows_snoc (follows_nil (host3 helloFile)) (f := readVia3) (a := [.u32 0, .u64 0])
    (r := some [.record [natV 1, natV 2]]) rfl
  exact follows_snoc h1 (f := cStreamRead) (a := [natV 1, natV 0])
    (r := some [natV (packCopy .completed 0), bytesV []]) rfl

/-! ## Clock overflow -/

/-- `wait-for (2^64 - 1)`, `now`, `wait-for 1`, `now`, answered by `host3`. -/
def overflowRun : List WEv :=
  [.imp waitFor3 [.u64 (BitVec.ofNat 64 u64Max)] (some []),
   .imp now3 [] (some [.u64 (BitVec.ofNat 64 u64Max)]),
   .imp waitFor3 [.u64 1] (some []),
   .imp now3 [] (some [.u64 (BitVec.ofNat 64 u64Max)])]

/-- **REFUTED: `host3` and `clockTh3`.** The run follows `host3 F`; `clockTh3` rejects it (it
owes `2^64` after the second wait); the saturated `clockTh3s` accepts it. -/
theorem host3_clock_overflow (F : BitVec 32 → List (BitVec 8)) : Follows (host3 F) overflowRun ∧
    ¬ clockTh3.Accepts overflowRun ∧ clockTh3s.Accepts overflowRun := by
  refine ⟨?_, by unfold Protocol.Accepts; decide, by unfold Protocol.Accepts; decide⟩
  have h1 := follows_snoc (follows_nil (host3 F)) (f := waitFor3)
    (a := [.u64 (BitVec.ofNat 64 u64Max)]) (r := some []) rfl
  have h2 := follows_snoc h1 (f := now3) (a := []) (r := some [.u64 (BitVec.ofNat 64 u64Max)])
    rfl
  have h3 := follows_snoc h2 (f := waitFor3) (a := [.u64 1]) (r := some []) rfl
  exact follows_snoc h3 (f := now3) (a := []) (r := some [.u64 (BitVec.ofNat 64 u64Max)])
    rfl

/-! ## Weakenings -/

/-- Acceptance transfers along a simulation of protocol states. -/
theorem accepts_sim {S S' E : Type} {A : Protocol S E} {B : Protocol S' E} (R : S → S' → Prop)
    (h0 : R A.init B.init)
    (hs : ∀ q q' e q1, R q q' → A.step q e = some q1 → ∃ q1', B.step q' e = some q1' ∧ R q1 q1')
    {t : List E} (ht : A.Accepts t) : B.Accepts t := by
  unfold Protocol.Accepts at ht ⊢
  suffices ∀ t q q', R q q' → (A.run q t).isSome → (B.run q' t).isSome from this t _ _ h0 ht
  intro t
  induction t with
  | nil => intros; rfl
  | cons e t ih =>
    intro q q' hR h
    simp only [Protocol.run] at h ⊢
    cases hA : A.step q e with
    | none => simp [hA] at h
    | some q1 =>
      obtain ⟨q1', hB, hR'⟩ := hs q q' e q1 hR hA
      simp only [hA, Option.bind_some] at h
      simp only [hB, Option.bind_some]
      exact ih q1 q1' hR' h

/-- `outStep` rejects every ill-shaped call it constrains. -/
theorem outStep_illshaped (q : OutSt) {e : WEv} (h : outShaped e = false) : outStep q e = none := by
  cases e with
  | imp f a r =>
    unfold outShaped at h
    unfold outStep
    by_cases h1 : f = stdoutWrite3
    · subst h1
      simp (config := { decide := true }) only [↓reduceIte] at h ⊢
      split
      · simp at h
      · rfl
    · by_cases h2 : f = cStreamWrite
      · subst h2
        simp (config := { decide := true }) only [↓reduceIte] at h ⊢
        split
        · simp at h
        · rfl
      · simp [h1, h2] at h
  | _ => simp [outShaped] at h

/-- **The corrected stdout theory is a weakening.** -/
theorem stdoutTh3w_of {t : List WEv} (h : stdoutTh3.Accepts t) : stdoutTh3w.Accepts t := by
  refine accepts_sim (A := stdoutTh3) (B := stdoutTh3w) (fun q q' => q = q') rfl (fun q q' e q1 hR hs => ⟨q1, ?_, rfl⟩) h
  subst hR
  change outStep q e = some q1 at hs
  show (if outShaped e then outStep q e else some q) = some q1
  cases hsh : outShaped e
  · rw [outStep_illshaped q hsh] at hs; cases hs
  · exact hs

/-- The simulation of `clockTh3` by `clockTh3s`: the same last instant, a smaller bound. -/
def ClockSim (q q' : ClockSt) : Prop := q.last = q'.last ∧ q'.lb ≤ q.lb

/-- `now`: an answer `clockStep3` accepts is accepted by `clockStep3s`. -/
theorem clock_sim_now {q q' q1 : ClockSt} (hR : ClockSim q q') (a : List Val) (r : Option (List Val))
    (hs : clockStep3 q (.imp now3 a r) = some q1) :
    ∃ q1', clockStep3s q' (.imp now3 a r) = some q1' ∧ ClockSim q1 q1' := by
  obtain ⟨hl, hlb⟩ := hR
  simp only [clockStep3, clockStep3s, ↓reduceIte] at hs ⊢
  split at hs
  · split_ifs at hs with hc
    have hq1 : q1 = _ := (Option.some.inj hs).symm
    subst hq1
    have hc' : q'.last.all (fun l => decide (l ≤ _)) = true ∧ q'.lb ≤ _ :=
      ⟨hl ▸ hc.1, Nat.le_trans hlb hc.2⟩
    refine ⟨_, ?_, rfl, Nat.le_refl _⟩
    dsimp only
    rw [ite_eq_left hc']
  · cases hs

/-- `wait-for d`: the saturated bound is below the bound `clockStep3` owes. -/
theorem clock_sim_wait {q q' q1 : ClockSt} (hR : ClockSim q q') (a : List Val)
    (r : Option (List Val)) (hs : clockStep3 q (.imp waitFor3 a r) = some q1) :
    ∃ q1', clockStep3s q' (.imp waitFor3 a r) = some q1' ∧ ClockSim q1 q1' := by
  obtain ⟨hl, hlb⟩ := hR
  have hne : ¬ waitFor3 = now3 := by decide
  simp only [clockStep3, clockStep3s, hne, ↓reduceIte] at hs ⊢
  rw [← hl]
  split at hs
  · rename_i d l hql
    rw [hql]
    have hq1 : q1 = { q with lb := max q.lb (l.toNat + d.toNat) } := (Option.some.inj hs).symm
    subst hq1
    exact ⟨_, rfl, hql, by simp only; omega⟩
  · rename_i hnot
    have hq1 : q1 = q := (Option.some.inj hs).symm
    subst hq1
    refine ⟨q', ?_, hl, hlb⟩
    split
    · rename_i d l hql
      exact (hnot d l rfl hql).elim
    · rfl

/-- Other functions: both theories keep their state. -/
theorem clock_sim_other {q q' q1 : ClockSt} (hR : ClockSim q q') {f : FnName} (h1 : f ≠ now3)
    (h2 : f ≠ waitFor3) (a : List Val) (r : Option (List Val))
    (hs : clockStep3 q (.imp f a r) = some q1) :
    ∃ q1', clockStep3s q' (.imp f a r) = some q1' ∧ ClockSim q1 q1' := by
  simp only [clockStep3, clockStep3s, h1, h2, ↓reduceIte, Option.some.injEq] at hs ⊢
  subst hs
  exact ⟨_, rfl, hR⟩

/-- **The saturated clock theory is a weakening.** -/
theorem clockTh3s_of {t : List WEv} (h : clockTh3.Accepts t) : clockTh3s.Accepts t := by
  refine accepts_sim (A := clockTh3) (B := clockTh3s) ClockSim ⟨rfl, Nat.le_refl _⟩
    (fun q q' e q1 hR hs => ?_) h
  cases e with
  | imp f a r =>
    by_cases h1 : f = now3
    · subst h1; exact clock_sim_now hR a r hs
    · by_cases h2 : f = waitFor3
      · subst h2; exact clock_sim_wait hR a r hs
      · exact clock_sim_other hR h1 h2 a r hs
  | _ =>
    cases hs
    exact ⟨q', rfl, hR⟩

end Silmaril.Wasi.Versions.P3OverP2
