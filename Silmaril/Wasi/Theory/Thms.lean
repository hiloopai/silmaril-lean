module

public import Silmaril.Wasi.Theory.Defs
public import Silmaril.Wasi.Host.Thms

@[expose] public section

/-!
# WASI theories: the concrete hosts are models

* `pointwise_accepts_iff`, `follows_pointwise`: a concrete host satisfies a pointwise theory
  when each of its answers does.
* **`stdoutImpl_sat`**, **`fsImpl_sat`**: the concrete stdout and filesystem hosts satisfy their
  typing theories.
* **`clockImpl_sat`**: the tick clock satisfies the monotonic clock theory `clockTh`.
* `loose` hosts of each theory satisfy it (`loose_sat`), so each theory has a loose model and a
  concrete one.
-/

namespace Silmaril.Wasi

open Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Pointwise theories -/

/-- A pointwise protocol accepts exactly the lists of accepted events. -/
theorem pointwise_accepts_iff (ok : WEv → Bool) (t : List WEv) :
    (pointwise ok).Accepts t ↔ ∀ e ∈ t, ok e = true := by
  unfold Protocol.Accepts
  induction t with
  | nil => exact ⟨fun _ _ he => absurd he List.not_mem_nil, fun _ => rfl⟩
  | cons e t ih =>
    show ((if ok e then some () else none).bind fun q => (pointwise ok).run q t).isSome = true ↔ _
    cases he : ok e with
    | false => exact ⟨fun h => absurd h (by simp), fun h => absurd (h e List.mem_cons_self) (by simp [he])⟩
    | true =>
      rw [ite_eq_left rfl, Option.bind_some, ih]
      exact ⟨fun h e' he' => (List.mem_cons.1 he').elim (· ▸ he) (h e'),
        fun h e' he' => h e' (List.mem_cons_of_mem _ he')⟩

/-- **A concrete host satisfies a pointwise theory** when each of its answers is accepted and
the theory accepts every event that is not an answer. -/
theorem follows_pointwise {ok : WEv → Bool} {impl : Impl}
    (hans : ∀ p f a, ok (.imp f a (impl p f a)) = true) (hother : ∀ e, e.isImp = false → ok e = true)
    {t : List WEv} (ht : Follows impl t) : (pointwise ok).Accepts t := by
  refine (pointwise_accepts_iff ok t).2 fun e he => ?_
  obtain ⟨s, u, rfl⟩ := List.append_of_mem he
  cases e with
  | imp f a r =>
    have hr : r = impl s f a := ht s f a r ⟨u, by simp⟩
    exact hr ▸ hans s f a
  | req f a => exact hother _ rfl
  | call f a => exact hother _ rfl
  | ret f a r => exact hother _ rfl

/-- Every answer of the stdout host is well typed. -/
theorem stdoutImpl_ok (p : List WEv) (f : FnName) (a : List Val) :
    stdoutOk (.imp f a (stdoutImpl p f a)) = true := by
  simp only [stdoutOk, stdoutImpl]
  split_ifs <;> rfl

/-- **The stdout host satisfies the stdout typing theory.** -/
theorem stdoutImpl_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat stdoutTyped.Accepts).holds (concrete (Y := Y) (I := I) stdoutImpl) :=
  concrete_sat _ fun _ ht => follows_pointwise stdoutImpl_ok (fun e he => by
    cases e <;> first | rfl | exact absurd he (by simp [WEv.isImp])) ht

/-- Every answer of the filesystem host is well typed. -/
theorem fsImpl_ok (p : List WEv) (f : FnName) (a : List Val) :
    fsOk (.imp f a (fsImpl p f a)) = true := by
  simp only [fsOk, fsImpl]
  split_ifs <;>
    first
    | rfl
    | (rcases a with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> first | rfl | (cases x <;> rfl))

/-- **The filesystem host satisfies the filesystem typing theory.** -/
theorem fsImpl_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat fsTyped.Accepts).holds (concrete (Y := Y) (I := I) fsImpl) :=
  concrete_sat _ fun _ ht => follows_pointwise fsImpl_ok (fun e he => by
    cases e <;> first | rfl | exact absurd he (by simp [WEv.isImp])) ht

/-! ## The tick clock -/

/-- An event that is not an answer of `now` keeps the clock state. -/
theorem clockStep_of_ne (q : Option (BitVec 64)) {e : WEv}
    (he : ∀ a r, e ≠ .imp clockNow a r) : clockStep q e = some q := by
  cases e with
  | imp f a r =>
    have hf : f ≠ clockNow := fun hf => he a r (hf ▸ rfl)
    show (if f = clockNow then nowStep q r else some q) = some q
    rw [ite_eq_right hf]
  | req f a => rfl
  | call f a => rfl
  | ret f a r => rfl

/-- The tick answered after `n` answers. -/
def tick (n : Nat) : BitVec 64 := BitVec.ofNat 64 (min n u64Max)

theorem tick_toNat (n : Nat) : (tick n).toNat = min n u64Max := by
  unfold tick u64Max
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- The clock state after an answer sequence of the tick clock. -/
def ClockBound (t : List WEv) (q : Option (BitVec 64)) : Prop :=
  ∀ v, q = some v → v.toNat ≤ min t.length u64Max

/-- An answer of `now` by the tick clock keeps the bound. -/
theorem clockStep_tick {t : List WEv} {q : Option (BitVec 64)} (hq : ClockBound t q) (a : List Val) :
    clockStep q (.imp clockNow a (some [.u64 (tick t.length)])) = some (some (tick t.length)) := by
  have hle : q.all (fun l => decide (l ≤ tick t.length)) = true := by
    cases q with
    | none => rfl
    | some v =>
      have hv : v.toNat ≤ (tick t.length).toNat := (tick_toNat t.length).symm ▸ hq v rfl
      exact decide_eq_true (BitVec.le_def.2 hv)
  show (if clockNow = clockNow then nowStep q _ else some q) = _
  rw [ite_eq_left rfl]
  show (if _ then _ else _) = _
  rw [ite_eq_left hle]

/-- One more event of the tick clock. -/
theorem clock_snoc {t : List WEv} {e : WEv} {q : Option (BitVec 64)} (hq : ClockBound t q)
    (he : ∀ a r, e = .imp clockNow a r → r = clockImpl t clockNow a) :
    ∃ q', clockStep q e = some q' ∧ ClockBound (t ++ [e]) q' := by
  have hlen : min t.length u64Max ≤ min (t ++ [e]).length u64Max := by
    simp only [List.length_append, List.length_singleton]; omega
  by_cases hnow : ∃ a r, e = .imp clockNow a r
  · obtain ⟨a, r, rfl⟩ := hnow
    have hr : r = some [.u64 (tick t.length)] := by simpa [clockImpl, tick] using he a r rfl
    refine ⟨some (tick t.length), hr ▸ clockStep_tick hq a, fun v hv => ?_⟩
    have hv' : v = tick t.length := (Option.some.inj hv).symm
    exact hv' ▸ (tick_toNat t.length).symm ▸ hlen
  · have hne : ∀ a r, e ≠ .imp clockNow a r := fun a r h => hnow ⟨a, r, h⟩
    exact ⟨q, clockStep_of_ne q hne, fun v hv => (hq v hv).trans hlen⟩

/-- The tick clock's answer sequences keep the bound. -/
theorem clock_follows {t : List WEv} (ht : Follows clockImpl t) :
    ∃ q, clockTh.run clockTh.init t = some q ∧ ClockBound t q := by
  induction t using List.reverseRecOn with
  | nil => exact ⟨none, rfl, fun v hv => (Option.some_ne_none v hv.symm).elim⟩
  | append_singleton t e ih =>
    have ht' : Follows clockImpl t := (prefixClosed_follows clockImpl).2 (List.prefix_append t [e]) ht
    obtain ⟨q, hq, hb⟩ := ih ht'
    have he : ∀ a r, e = .imp clockNow a r → r = clockImpl t clockNow a :=
      fun a r h => ht t clockNow a r (h ▸ List.prefix_refl _)
    obtain ⟨q', hq', hb'⟩ := clock_snoc hb he
    refine ⟨q', ?_, hb'⟩
    rw [Protocol.run_concat, hq]
    exact hq'

/-- **The tick clock satisfies the monotonic clock theory.** -/
theorem clockImpl_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat clockTh.Accepts).holds (concrete (Y := Y) (I := I) clockImpl) :=
  concrete_sat _ fun _ ht =>
    let ⟨q, hq, _⟩ := clock_follows ht
    (Protocol.accepts_iff_exists _ _).2 ⟨q, hq⟩

end Silmaril.Wasi
