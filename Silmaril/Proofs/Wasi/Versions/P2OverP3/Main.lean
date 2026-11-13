module

public import Silmaril.Proofs.Wasi.Versions.P2OverP3.Ops
public import Silmaril.Proofs.Wasi.Versions.P2OverP3.Cli
public import Silmaril.Proofs.Wasi.Versions.P2OverP3.Fs

/-!
# Proofs: WASI 0.2 over 0.3 is a model of the loose 0.2 theory

* `prog_io`: every answer of a `wasi:io` export is admissible in the loose `wasi:io` theory.
* `p2_step`: the step of the loose 0.2 theory on an answer of the component.
* `wpInv`: the invariant method (`Silmaril.Wasi.Versions.Stateful`) with the invariant `J`: the
  `wasi:io` state of the 0.2 theory is the component's own record `s.io`, and the last instant
  the component answered is at most the last instant of the 0.3 clock (`ClkLe`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3 (clockTh3 clockStep3 ClockSt now3)

/-! ## `wasi:io` -/

/-- **Every answer of a `wasi:io` export is admissible** in the loose theory. -/
theorem prog_io (cap : Nat) (s : St) (f : FnName) (a : List Val) (hf : ioOp f ≠ .other) :
    Leaves (prog cap s f a) (Adm s.io (ioOp f) a) := by
  unfold prog
  split <;> rename_i hop <;> rw [hop]
  · exact cw_good cap s a
  · exact write_good s a _ (.inl rfl) rfl
  · exact write_good s a _ (.inr rfl) (by simp [writeLen])
  · exact bwf_good s a _ (.inl rfl) rfl
  · exact bwf_good s a _ (.inr rfl) (by simp [writeLen])
  · exact flush_good s a
  · exact bflush_good s a
  · exact splice_good s a (.inl rfl)
  · exact splice_good s a (.inr rfl)
  · exact sub_good s a _ (.inl rfl)
  · exact sub_good s a _ (.inr rfl)
  · exact read_good s a false (.inl rfl)
  · exact read_good s a true (.inr rfl)
  · exact skip_good s a false (.inl rfl)
  · exact skip_good s a true (.inr rfl)
  · exact ready_good s a
  · exact block_good s a
  · exact poll_good s a
  · exact pdrop_good s a
  · exact absurd hop hf

/-! ## `wasi:cli` and `wasi:clocks` -/

/-- The functions classified `other` answer with a lifted value. -/
theorem prog_other (cap : Nat) (s : St) (f : FnName) (a : List Val) (hf : ioOp f = .other) :
    Leaves (prog cap s f a) (fun x => cliOk f x.2 = true) := by
  unfold prog
  rw [hf]
  exact leaves_bind_of (fun x => leaves_pure (cliOk_fix f x.2)) _

/-- `now` forwards `monotonic-clock.now` of WASI 0.3. -/
theorem prog_now (cap : Nat) (s : St) (a : List Val) :
    prog cap s clockNow a = .call opNow fun r => .pure (s.impl, r) := by
  have hop : ioOp clockNow = .other := by decide
  have hother : otherP s.impl clockNow a = .call opNow fun r => .pure (s.impl, r) := by
    unfold otherP
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl]
  unfold prog
  rw [hop, hother]
  simp only [Prog.bind, cliFix_now]

/-! ## The 0.2 theory on the component's answers -/

/-- The step of the loose 0.2 theory on an answer other than `now`. -/
theorem p2_step {f : FnName} {a : List Val} {r : Option (List Val)} (io : IoSt)
    (g : Option (BitVec 64)) (h1 : ansOk .loose io (ioOp f) a r = true)
    (h2 : p2Ok (.imp f a r) = true) (h3 : fsOk (.imp f a r) = true) (hn : f ≠ clockNow) :
    (p2Th .loose).step (io, g, (), ()) (.imp f a r) = some (ioUpd io (ioOp f) a r, g, (), ()) := by
  simp [p2Th, Protocol.prod, ioTh, ioStep, h1, clockTh, clockStep, hn, pointwise, h2, fsTyped, h3]

/-- The 0.2 clock state is behind the 0.3 clock state. -/
def ClkLe (g l : Option (BitVec 64)) : Prop := ∀ x ∈ g, ∃ y ∈ l, x ≤ y

/-- An accepted answer of the 0.3 `now`. -/
theorem now3_step {q q' : ClockSt} {a : List Val} {n : Option (List Val)}
    (h : clockStep3 q (.imp now3 a n) = some q') :
    ∃ x, n = some [.u64 x] ∧ q.last.all (fun l => decide (l ≤ x)) = true ∧ q'.last = some x := by
  unfold clockStep3 at h
  dsimp only at h
  rw [ite_eq_left rfl] at h
  split at h
  next x =>
    split at h
    next hok =>
      cases h
      exact ⟨x, rfl, hok.1, rfl⟩
    next => exact absurd h (by simp)
  next => exact absurd h (by simp)

/-- An accepted step other than `now` keeps the last instant. -/
theorem clock3_last {q q' : ClockSt} {e : WEv} (h : clockStep3 q e = some q')
    (hn : ¬ ∃ a n, e = .imp now3 a n) : q'.last = q.last := by
  unfold clockStep3 at h
  split at h
  next f a r =>
    have hf : f ≠ now3 := fun hf => hn ⟨a, r, hf ▸ rfl⟩
    rw [ite_eq_right hf] at h
    split_ifs at h
    · split at h <;> (cases h; rfl)
    · cases h; rfl
  next => cases h; rfl

/-- The last instant of the 0.3 clock never decreases. -/
theorem clock3_mono {q q' : ClockSt} {e : WEv} (h : clockStep3 q e = some q') :
    ∀ y ∈ q.last, ∃ y' ∈ q'.last, y ≤ y' := by
  intro y hy
  by_cases hnow : ∃ a n, e = .imp now3 a n
  · obtain ⟨a, n, rfl⟩ := hnow
    obtain ⟨x, -, hle, hlast⟩ := now3_step h
    have hq : q.last = some y := hy
    rw [hq] at hle
    exact ⟨x, hlast, by simpa using hle⟩
  · have hlast : q'.last = q.last := clock3_last h hnow
    exact ⟨y, hlast ▸ hy, BitVec.le_refl _⟩

theorem clkLe_step {g : Option (BitVec 64)} {q q' : ClockSt} {e : WEv} (hg : ClkLe g q.last)
    (h : clockStep3 q e = some q') : ClkLe g q'.last := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hg x hx
  obtain ⟨y', hy', hyy⟩ := clock3_mono h y hy
  exact ⟨y', hy', BitVec.le_trans hxy hyy⟩

/-- The invariant: the 0.2 `wasi:io` state is the component's record, and the 0.2 clock is
behind the 0.3 clock. -/
def J (s : St) (qT : ClockSt) (qG : P2St) : Prop := qG.1 = s.io ∧ ClkLe qG.2.1 qT.last

end Silmaril.Wasi.Versions.P2OverP3
