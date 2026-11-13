module

public import Silmaril.Wasi.Versions.Adapter.Defs
public import Silmaril.Wasi.Versions.Stateful.Thms

/-!
# Proofs: inversion of the 0.2 theory assumed by the adapter

Every answer accepted by `p2Th` has the WIT type of its import (`step_ok`, then a match on
`Imp.ok`), and the clock part of `p2Th` only moves forward.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- The name of an import determines it. -/
theorem Imp.ofName_name (i : Imp) : Imp.ofName i.name = some i := by cases i <;> decide

/-- Only `now` is the monotonic clock's `now`. -/
theorem Imp.name_ne_clockNow (i : Imp) (hi : i ≠ .now) : i.name ≠ clockNow := by
  cases i <;> first | exact absurd rfl hi | decide

variable {q q' : Unit × Option (BitVec 64)} {a : List Val} {n : Option (List Val)}

/-- An accepted answer is well typed, and the clock part steps. -/
theorem ok_of_step {e : WEv} (h : p2Th.step q e = some q') :
    p2Ok e = true ∧ clockTh.step q.2 e = some q'.2 := by
  simp only [p2Th, Protocol.prod, p2Typed, pointwise] at h
  by_cases hok : p2Ok e = true
  · rw [ite_eq_left hok] at h
    simp only [Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨hok, hb⟩
  · rw [ite_eq_right hok] at h
    cases h

/-- **An accepted answer of an import has its type.** -/
theorem step_ok {i : Imp} (h : p2Th.step q (.imp i.name a n) = some q') : i.ok a n = true := by
  have h1 := (ok_of_step h).1
  simpa only [p2Ok, Imp.ofName_name] using h1

/-- An answer of an import other than `now` keeps the clock. -/
theorem step_clock_ne {i : Imp} (hi : i ≠ .now) (h : p2Th.step q (.imp i.name a n) = some q') :
    q'.2 = q.2 := by
  have h2 := (ok_of_step h).2
  simp only [clockTh, clockStep, ite_eq_right (Imp.name_ne_clockNow i hi)] at h2
  exact (Option.some.inj h2).symm

/-- `get-stdin`, `get-stdout`, `get-stderr`. -/
theorem step_u32 {i : Imp} (hi : i = .getStdin ∨ i = .getStdout ∨ i = .getStderr)
    (h : p2Th.step q (.imp i.name a n) = some q') : ∃ x, n = some [.u32 x] := by
  have h1 := step_ok h
  rcases hi with rfl | rfl | rfl <;> (simp only [Imp.ok] at h1; split at h1 <;> simp_all)

/-- `get-directories`. -/
theorem step_dirs (h : p2Th.step q (.imp Imp.getDirs.name a n) = some q') :
    ∃ ds, n = some [.record ds] ∧ ds.all preopenOk = true ∧ ds.length ≤ maxPreopens := by
  have h1 := step_ok h
  simp only [Imp.ok] at h1
  split at h1 <;> simp_all

/-- `blocking-write-and-flush`. -/
theorem step_write (h : p2Th.step q (.imp Imp.write.name a n) = some q') :
    n = some [.variant 0 none] ∨ n = some [.variant 1 (some (.variant 1 none))] ∨
      ∃ err, n = some [.variant 1 (some (.variant 0 (some (.u32 err))))] := by
  have h1 := step_ok h
  simp only [Imp.ok] at h1
  split at h1
  · exact .inl rfl
  · rename_i e
    simp only [isStreamErr] at h1
    split at h1 <;> simp_all
  · simp at h1

/-- `blocking-read`. -/
theorem step_read {len : BitVec 64} {hd : Val}
    (h : p2Th.step q (.imp Imp.read.name [hd, .u64 len] n) = some q') :
    (∃ bs, n = some [.variant 0 (some (.record bs))] ∧ allU8 bs = true ∧ bs.length ≤ len.toNat) ∨
    n = some [.variant 1 (some (.variant 1 none))] ∨
    ∃ err, n = some [.variant 1 (some (.variant 0 (some (.u32 err))))] := by
  have h1 := step_ok h
  simp only [Imp.ok] at h1
  split at h1
  · simp_all
  · rename_i e _
    simp only [isStreamErr] at h1
    split at h1 <;> simp_all
  · simp at h1

/-- `filesystem-error-code`. -/
theorem step_errCode (h : p2Th.step q (.imp Imp.errCode.name a n) = some q') :
    n = some [.variant 0 none] ∨ ∃ k, n = some [.variant 1 (some (.variant k none))] := by
  have h1 := step_ok h
  simp only [Imp.ok] at h1
  split at h1 <;> simp_all

/-- `open-at`, `write-via-stream`, `read-via-stream`. -/
theorem step_handle {i : Imp} (hi : i = .openAt ∨ i = .writeVia ∨ i = .readVia)
    (h : p2Th.step q (.imp i.name a n) = some q') :
    (∃ x, n = some [.variant 0 (some (.u32 x))]) ∨ ∃ k, n = some [.variant 1 (some (.variant k none))] := by
  have h1 := step_ok h
  rcases hi with rfl | rfl | rfl <;>
    (simp only [Imp.ok, isHandleRes] at h1; split at h1 <;> simp_all)

/-- `get-type`. -/
theorem step_type (h : p2Th.step q (.imp Imp.getType.name a n) = some q') :
    (∃ k, n = some [.variant 0 (some (.variant k none))]) ∨
      ∃ k, n = some [.variant 1 (some (.variant k none))] := by
  have h1 := step_ok h
  simp only [Imp.ok] at h1
  split at h1 <;> simp_all

/-- `monotonic-clock.now`, `monotonic-clock.resolution`. -/
theorem step_u64 {i : Imp} (hi : i = .now ∨ i = .monoRes)
    (h : p2Th.step q (.imp i.name a n) = some q') : ∃ x, n = some [.u64 x] := by
  have h1 := step_ok h
  rcases hi with rfl | rfl <;> (simp only [Imp.ok] at h1; split at h1 <;> simp_all)

/-- `wall-clock.now`, `wall-clock.resolution`. -/
theorem step_wall {i : Imp} (hi : i = .wallNow ∨ i = .wallRes)
    (h : p2Th.step q (.imp i.name a n) = some q') :
    ∃ sec ns, n = some [.record [.u64 sec, .u32 ns]] := by
  have h1 := step_ok h
  rcases hi with rfl | rfl <;> (simp only [Imp.ok] at h1; split at h1 <;> simp_all)

/-- `get-random-bytes`. -/
theorem step_rand {len : BitVec 64} (h : p2Th.step q (.imp Imp.rand.name [.u64 len] n) = some q') :
    ∃ bs, n = some [.record bs] ∧ allU8 bs = true ∧ bs.length = len.toNat := by
  have h1 := step_ok h
  simp only [Imp.ok] at h1
  split at h1 <;> simp_all

/-- `get-arguments`. -/
theorem step_args (h : p2Th.step q (.imp Imp.getArgs.name a n) = some q') :
    ∃ ss, n = some [.record ss] ∧ ss.all P1.isStrV = true := by
  have h1 := step_ok h
  simp only [Imp.ok] at h1
  split at h1 <;> simp_all

/-- `get-environment`. -/
theorem step_env (h : p2Th.step q (.imp Imp.getEnv.name a n) = some q') :
    ∃ ps, n = some [.record ps] ∧ ps.all isEnvPair = true := by
  have h1 := step_ok h
  simp only [Imp.ok] at h1
  split at h1 <;> simp_all

/-! ## The clock part -/

/-- The preview1 clock state is behind the 0.2 clock state. -/
def clockLe : Option (BitVec 64) → Option (BitVec 64) → Prop
  | none, _ => True
  | some _, none => False
  | some x, some y => x ≤ y

theorem clockLe_trans' {c a b : Option (BitVec 64)} (h1 : clockLe c a) (h2 : clockLe a b) :
    clockLe c b := by
  rcases c with _ | x
  · trivial
  · rcases a with _ | y
    · exact h1.elim
    · rcases b with _ | z
      · exact h2.elim
      · exact BitVec.le_trans (show x ≤ y from h1) (show y ≤ z from h2)

theorem clockLe_refl : ∀ a : Option (BitVec 64), clockLe a a
  | none => trivial
  | some x => BitVec.le_refl x

/-- A step of the 0.2 clock theory only moves forward. -/
theorem clockLe_clockStep {a b : Option (BitVec 64)} {e : WEv} (h : clockStep a e = some b) :
    clockLe a b := by
  have hcases : b = a ∨ ∃ x, b = some x ∧ a.all (fun l => decide (l ≤ x)) = true := by
    cases e with
    | imp f a' r =>
      simp only [clockStep] at h
      split_ifs at h
      · simp only [nowStep] at h
        split at h
        · split_ifs at h with hle
          exact .inr ⟨_, (Option.some.inj h).symm, hle⟩
        · cases h
      · exact .inl (Option.some.inj h).symm
    | req _ _ | call _ _ | ret _ _ _ => exact .inl (Option.some.inj h).symm
  rcases hcases with rfl | ⟨x, rfl, hle⟩
  · exact clockLe_refl _
  · rcases a with _ | y
    · trivial
    · have hyx : y ≤ x := by simpa using hle
      exact hyx

/-- Every accepted answer keeps the preview1 clock behind. -/
theorem clockLe_step {c : Option (BitVec 64)} {e : WEv} (hc : clockLe c q.2)
    (h : p2Th.step q e = some q') : clockLe c q'.2 :=
  clockLe_trans' hc (clockLe_clockStep (ok_of_step h).2)

/-- An answer `x` of `now` is the new 0.2 clock state, after the old one. -/
theorem step_now_clock {x : BitVec 64} (h : p2Th.step q (.imp Imp.now.name a (some [.u64 x])) = some q') :
    q'.2 = some x ∧ clockLe q.2 (some x) := by
  have h2 := (ok_of_step h).2
  simp only [clockTh, clockStep, Imp.name, ite_true, nowStep] at h2
  split_ifs at h2 with hle
  refine ⟨(Option.some.inj h2).symm, ?_⟩
  rcases hq : q.2 with _ | y
  · trivial
  · rw [hq] at hle
    simpa [clockLe] using hle

end Silmaril.Wasi.Versions.Adapter
