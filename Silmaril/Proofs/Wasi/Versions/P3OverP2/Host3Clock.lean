module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Refute

/-!
# Proofs: every run of `host3` satisfies the saturated clock theory

`host3_clockTh3s`: for every `F`, every answer sequence of `host3 F` is accepted by `clockTh3s`
(`clockTh3` itself fails, `host3_clock_overflow`). Invariant: the last answered instant and the
owed bound are at most `min (clockVal p) (2^64 - 1)`, where `clockVal p` (the host's clock) only
grows, by `d` at each `wait-for d`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3

/-- The clock value is additive. -/
theorem clockVal_cons (e : WEv) (l : List WEv) : clockVal (e :: l) = clockVal [e] + clockVal l := by
  cases e with
  | imp f a r =>
    rcases a with _ | ⟨v, _ | ⟨u, l'⟩⟩
    · simp [clockVal]
    · cases v <;> simp [clockVal]
    · simp [clockVal]
  | _ => simp [clockVal]

theorem clockVal_append (p : List WEv) (e : WEv) : clockVal (p ++ [e]) = clockVal p + clockVal [e] := by
  induction p with
  | nil => simp [clockVal]
  | cons e' p ih => rw [List.cons_append, clockVal_cons, ih, clockVal_cons e' p]; omega

/-- The prefix of a run that follows an implementation follows it. -/
theorem follows_init {impl : Impl} {p : List WEv} {e : WEv} (h : Follows impl (p ++ [e])) :
    Follows impl p :=
  (prefixClosed_follows impl).2 (List.prefix_append p [e]) h

/-- The last answer of a run that follows an implementation is the implementation's. -/
theorem follows_last {impl : Impl} {p : List WEv} {f : FnName} {a : List Val}
    {r : Option (List Val)} (h : Follows impl (p ++ [.imp f a r])) : r = impl p f a :=
  h p f a r (List.prefix_refl _)

/-- The clock invariant of `host3`. -/
def H3ClockI (p : List WEv) (q : ClockSt) : Prop :=
  (∀ l, q.last = some l → l.toNat ≤ min (clockVal p) u64Max) ∧ q.lb ≤ min (clockVal p) u64Max

/-- The invariant survives a longer history. -/
theorem H3ClockI.mono {p : List WEv} {q : ClockSt} (h : H3ClockI p q) (e : WEv) :
    H3ClockI (p ++ [e]) q := by
  rw [H3ClockI, clockVal_append]
  exact ⟨fun l hl => by have := h.1 l hl; omega, by have := h.2; omega⟩

/-- The clock of `host3` as a `u64`. -/
theorem clockVal_toNat (p : List WEv) :
    (BitVec.ofNat 64 (min (clockVal p) u64Max)).toNat = min (clockVal p) u64Max := by
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simp only [u64Max]; omega)

/-- `now` of `host3`. -/
theorem host3_clock_now (F : BitVec 32 → List (BitVec 8)) {p : List WEv} {q : ClockSt}
    (hI : H3ClockI p q) (a : List Val) :
    ∃ q', clockStep3s q (.imp now3 a (host3 F p now3 a)) = some q' ∧
      H3ClockI (p ++ [.imp now3 a (host3 F p now3 a)]) q' := by
  have hx := clockVal_toNat p
  have hh : host3 F p now3 a = some [.u64 (BitVec.ofNat 64 (min (clockVal p) u64Max))] := rfl
  have hc : q.last.all (fun l => decide (l ≤ BitVec.ofNat 64 (min (clockVal p) u64Max))) = true ∧
      q.lb ≤ (BitVec.ofNat 64 (min (clockVal p) u64Max)).toNat := by
    refine ⟨?_, by rw [hx]; exact hI.2⟩
    cases hql : q.last with
    | none => rfl
    | some l =>
      simp only [BitVec.le_def, hx, Option.all_some, decide_eq_true_eq]
      exact hI.1 l hql
  rw [hh]
  refine ⟨{ last := some (BitVec.ofNat 64 (min (clockVal p) u64Max)), lb := 0 }, ?_,
    H3ClockI.mono ⟨fun l hl => ?_, Nat.zero_le _⟩ _⟩
  · simp only [clockStep3s, ↓reduceIte, hc, and_self]
  · simp only [Option.some.injEq] at hl; subst hl; rw [hx]

/-- `wait-for d`, answered `[]` (as `host3` does). -/
theorem host3_clock_waitd {p : List WEv} {q : ClockSt} (hI : H3ClockI p q) (d : BitVec 64) :
    ∃ q', clockStep3s q (.imp waitFor3 [.u64 d] (some [])) = some q' ∧
      H3ClockI (p ++ [.imp waitFor3 [.u64 d] (some [])]) q' := by
  have hcv : clockVal (p ++ [.imp waitFor3 [.u64 d] (some [])]) = clockVal p + d.toNat := by
    rw [clockVal_append]; simp [clockVal]
  have hne : ¬ waitFor3 = now3 := by decide
  cases hql : q.last with
  | none =>
    refine ⟨q, by simp only [clockStep3s, hne, ↓reduceIte, hql], ?_⟩
    rw [H3ClockI, hcv]
    exact ⟨fun l hl => (by rw [hql] at hl; cases hl), (by have := hI.2; omega)⟩
  | some l =>
    refine ⟨{ q with lb := max q.lb (min (l.toNat + d.toNat) u64Max) },
      by simp only [clockStep3s, hne, ↓reduceIte, hql], ?_⟩
    rw [H3ClockI, hcv]
    have hl : l.toNat ≤ min (clockVal p) u64Max := hI.1 l hql
    have hlb : q.lb ≤ min (clockVal p) u64Max := hI.2
    refine ⟨fun l' hl' => ?_, by simp only; omega⟩
    simp only [hql, Option.some.injEq] at hl'
    subst hl'
    omega

/-- `wait-for` of `host3`. -/
theorem host3_clock_wait (F : BitVec 32 → List (BitVec 8)) {p : List WEv} {q : ClockSt}
    (hI : H3ClockI p q) (a : List Val) :
    ∃ q', clockStep3s q (.imp waitFor3 a (host3 F p waitFor3 a)) = some q' ∧
      H3ClockI (p ++ [.imp waitFor3 a (host3 F p waitFor3 a)]) q' := by
  have hh : host3 F p waitFor3 a = some [] := rfl
  have hne : ¬ waitFor3 = now3 := by decide
  rw [hh]
  by_cases ha : ∃ d, a = [.u64 d]
  · obtain ⟨d, rfl⟩ := ha
    exact host3_clock_waitd hI d
  · refine ⟨q, ?_, hI.mono _⟩
    simp only [clockStep3s, hne, ↓reduceIte]
    split
    · exact absurd ⟨_, rfl⟩ ha
    · rfl

/-- One answer of `host3`. -/
theorem host3_clock_step (F : BitVec 32 → List (BitVec 8)) {p : List WEv} {q : ClockSt}
    (hI : H3ClockI p q) (f : FnName) (a : List Val) :
    ∃ q', clockStep3s q (.imp f a (host3 F p f a)) = some q' ∧
      H3ClockI (p ++ [.imp f a (host3 F p f a)]) q' := by
  by_cases h1 : f = now3
  · subst h1; exact host3_clock_now F hI a
  · by_cases h2 : f = waitFor3
    · subst h2; exact host3_clock_wait F hI a
    · exact ⟨q, by simp [clockStep3s, h1, h2], hI.mono _⟩

/-- **Every run of `host3 F` is accepted by the saturated clock theory.** -/
theorem host3_clockTh3s_run (F : BitVec 32 → List (BitVec 8)) :
    ∀ t, Follows (host3 F) t → ∃ q, clockTh3s.run clockTh3s.init t = some q ∧ H3ClockI t q := by
  intro t
  induction t using List.reverseRecOn with
  | nil => exact fun _ => ⟨{}, rfl, fun l hl => (by cases hl), Nat.zero_le _⟩
  | append_singleton p e ih =>
    intro ht
    obtain ⟨q, hq, hI⟩ := ih (follows_init ht)
    rw [Protocol.run_concat, hq, Option.bind_some]
    cases e with
    | imp f a r =>
      have hr := follows_last ht
      subst hr
      exact host3_clock_step F hI f a
    | _ => exact ⟨q, rfl, hI.mono _⟩

/-- **`host3 F` is a model of the saturated clock theory**, for every run. -/
theorem host3_clockTh3s {Y : Sig.{0}} {I : Set FnName} (F : BitVec 32 → List (BitVec 8)) :
    (hostSat clockTh3s.Accepts).holds (concrete (Y := Y) (I := I) (host3 F)) :=
  concrete_sat _ fun t ht => by
    obtain ⟨q, hq, -⟩ := host3_clockTh3s_run F t ht
    unfold Protocol.Accepts
    rw [hq]
    rfl

end Silmaril.Wasi.Versions.P3OverP2
