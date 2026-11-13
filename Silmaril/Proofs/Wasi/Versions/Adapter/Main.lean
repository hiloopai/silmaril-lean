module

public import Silmaril.Proofs.Wasi.Versions.Adapter.Fns

/-!
# Proofs: the adapter is an implementation of preview1 over 0.2

* `wp_body`: every preview1 call answers well (typing, bounds, descriptors).
* `wp_body_clock`: the monotonic clock of preview1 stays behind that of 0.2.
* **`adapter_sat`**: the adapter satisfies `agP p2Th (retG P1.th)`: under the 0.2 theory, its
  returns satisfy the preview1 theory.
* **`adapter_model`**: linked over *any* host satisfying the 0.2 theory, the adapter is a host
  satisfying the preview1 theory.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P1 (FdSt fdStep fdOk typedOk boundsOk okAns errAns)

variable {s : ASt} {f : FdSt}

/-- An export call of the adapter is a preview1 function. -/
theorem fn_eq (q : (nsig P1.imports).Op) : q.1.1 = P1.fn q.1.1.fn := by
  obtain ⟨⟨⟨i, n⟩, hi⟩, a⟩ := q
  obtain ⟨hi1, -⟩ := hi
  simp only at hi1
  subst hi1
  rfl

theorem mem_of (q : (nsig P1.imports).Op) : q.1.1.fn ∈ P1.fnNames := q.1.2.2

/-- **Every preview1 call answers well.** -/
theorem wp_body (hJ : FdInv s f) (q : (nsig P1.imports).Op) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (body s q) (GoodQ q.1.1.fn q.2 f) qT := by
  have hb : ∀ {n : String}, n ≠ "fd_write" → n ≠ "fd_read" → n ≠ "random_get" →
      n ≠ "fd_write" ∧ n ≠ "fd_read" ∧ n ≠ "random_get" := fun h1 h2 h3 => ⟨h1, h2, h3⟩
  unfold body
  dsimp only
  have hn := fun {n : String} (h : n ∈ ["fd_write", "fd_read", "fd_close", "path_open",
      "clock_time_get", "clock_res_get", "random_get", "args_get", "args_sizes_get",
      "environ_get", "environ_sizes_get", "sched_yield", "proc_exit"]) => mem_fnNames h
  by_cases h0 : q.1.1.fn = "fd_write"
  · rw [ite_eq_left h0, h0]
    exact wp_fdWrite hJ _ _
  rw [ite_eq_right h0]
  by_cases h1 : q.1.1.fn = "fd_read"
  · rw [ite_eq_left h1, h1]
    exact wp_fdRead hJ _ _
  rw [ite_eq_right h1]
  by_cases h2 : q.1.1.fn = "fd_close"
  · rw [ite_eq_left h2, h2]
    exact wp_fdClose hJ _ _
  rw [ite_eq_right h2]
  by_cases h3 : q.1.1.fn = "path_open"
  · rw [ite_eq_left h3, h3]
    exact wp_pathOpen hJ _ _
  rw [ite_eq_right h3]
  by_cases h4 : q.1.1.fn = "clock_time_get"
  · rw [ite_eq_left h4, h4]
    exact wp_clockTimeGet hJ _ _
  rw [ite_eq_right h4]
  by_cases h5 : q.1.1.fn = "clock_res_get"
  · rw [ite_eq_left h5, h5]
    exact wp_clockResGet hJ _ _
  rw [ite_eq_right h5]
  by_cases h6 : q.1.1.fn = "random_get"
  · rw [ite_eq_left h6, h6]
    exact wp_randomGet hJ _ _
  rw [ite_eq_right h6]
  by_cases h7 : q.1.1.fn = "args_get"
  · rw [ite_eq_left h7, h7]
    exact wp_argsGet (n := "args_get") (hn (by simp)) (by decide) (by decide) (hb (by decide) (by decide)
      (by decide)) false (fun _ hss => hss) hJ _ _
  rw [ite_eq_right h7]
  by_cases h8 : q.1.1.fn = "args_sizes_get"
  · rw [ite_eq_left h8, h8]
    exact wp_argsGet (n := "args_sizes_get") (hn (by simp)) (by decide) (by decide) (hb (by decide) (by decide)
      (by decide)) true (fun _ _ => rfl) hJ _ _
  rw [ite_eq_right h8]
  by_cases h9 : q.1.1.fn = "environ_get"
  · rw [ite_eq_left h9, h9]
    exact wp_environGet (n := "environ_get") (hn (by simp)) (by decide) (by decide) (hb (by decide)
      (by decide) (by decide)) false (fun _ hss => hss) hJ _ _
  rw [ite_eq_right h9]
  by_cases h10 : q.1.1.fn = "environ_sizes_get"
  · rw [ite_eq_left h10, h10]
    exact wp_environGet (n := "environ_sizes_get") (hn (by simp)) (by decide) (by decide) (hb (by decide)
      (by decide) (by decide)) true (fun _ _ => rfl) hJ _ _
  rw [ite_eq_right h10]
  by_cases h11 : q.1.1.fn = "sched_yield"
  · rw [ite_eq_left h11, h11]
    exact good_ok_nonfd (hn (by simp)) (by decide) (by decide) rfl
      (hb (by decide) (by decide) (by decide)) hJ _
  rw [ite_eq_right h11]
  by_cases h12 : q.1.1.fn = "proc_exit"
  · rw [ite_eq_left h12, h12]
    exact wp_procExit hJ _ _
  rw [ite_eq_right h12]
  exact errQ (mem_of q) h12 ⟨by decide, by decide⟩ hJ _ qT

/-! ## The clock -/

theorem clockStep_err (c : Option (BitVec 64)) (g : FnName) (a : List Val) (e : Nat) :
    P1.clockStep c (.imp g a (errAns e)) = some c := by
  unfold P1.clockStep; split <;> simp_all [errAns, errV]

theorem clockStep_none (c : Option (BitVec 64)) (g : FnName) (a : List Val) :
    P1.clockStep c (.imp g a none) = some c := by
  unfold P1.clockStep; split <;> simp_all

theorem clockStep_fn {g : FnName} (hg : g ≠ P1.fn "clock_time_get") (c : Option (BitVec 64))
    (a : List Val) (r : Option (List Val)) : P1.clockStep c (.imp g a r) = some c := by
  unfold P1.clockStep; split <;> simp_all

theorem clockStep_id {id : BitVec 32} (hid : id ≠ P1.clockMonotonic) (c : Option (BitVec 64))
    (g : FnName) (a : List Val) (r : Option (List Val)) :
    P1.clockStep c (.imp g (.u32 id :: a) r) = some c := by
  unfold P1.clockStep; split <;> simp_all

/-- The clock post-condition. -/
abbrev ClockQ (c : Option (BitVec 64)) (g : FnName) (a : List Val) :
    ASt × Option (List Val) → Unit × Option (BitVec 64) → Prop :=
  fun r qT' => ∃ c', P1.clockStep c (.imp g a r.2) = some c' ∧ clockLe c' qT'.2

/-- A program that leaves the preview1 clock alone. -/
theorem wp_clock_frame {c : Option (BitVec 64)} {g : FnName} {a : List Val}
    (hfix : ∀ r : Option (List Val), P1.clockStep c (.imp g a r) = some c)
    (p : SProg ASt imports) {qT : Unit × Option (BitVec 64)} (hc : clockLe c qT.2) :
    Wp p2Th p (ClockQ c g a) qT :=
  Wp.stable (R := fun q => clockLe c q.2) (fun _ _ _ hq h => clockLe_step hq h)
    (fun r _ hq => ⟨c, hfix r.2, hq⟩) p hc

theorem clockLe_trans {a : Option (BitVec 64)} {b x : BitVec 64} (h1 : clockLe a (some b))
    (h2 : b ≤ x) : a.all (fun l => decide (l ≤ x)) = true := by
  rcases a with _ | a
  · rfl
  · simp only [Option.all_some, decide_eq_true_eq]; exact BitVec.le_trans h1 h2

/-- An answer `x` of `now` keeps the preview1 clock behind. -/
theorem clockStep_now {c : Option (BitVec 64)} {qT q : Unit × Option (BitVec 64)}
    (hc : clockLe c qT.2) {x : BitVec 64} (hle : clockLe qT.2 (some x)) (hq : q.2 = some x)
    {id : BitVec 32} (h1 : id = P1.clockMonotonic) (p : BitVec 64) :
    ClockQ c (P1.fn "clock_time_get") [.u32 id, .u64 p] (s, okAns (some (.u64 x))) q := by
  have hcx : clockLe c (some x) := clockLe_trans' hc hle
  have hall : c.all (fun l => decide (l ≤ x)) = true := by
    rcases c with _ | c
    · rfl
    · have hx : c ≤ x := hcx
      simpa using hx
  refine ⟨some x, ?_, ?_⟩
  · simp only [P1.clockStep, h1, and_self, ite_true, okAns, okV, hall]
  · show clockLe (some x) q.2
    rw [hq]; exact BitVec.le_refl x

/-- **`clock_time_get(monotonic)` stays behind the 0.2 clock.** -/
theorem wp_clockTimeGet_clock {c : Option (BitVec 64)} (a : List Val)
    {qT : Unit × Option (BitVec 64)} (hc : clockLe c qT.2) :
    Wp p2Th (clockTimeGet s a) (ClockQ c (P1.fn "clock_time_get") a) qT := by
  unfold clockTimeGet
  split
  · rename_i id p
    split_ifs with h1 h0
    · intro r q h
      obtain ⟨x, rfl⟩ := step_u64 (.inl rfl) h
      obtain ⟨hq, hle⟩ := step_now_clock h
      exact clockStep_now hc hle hq h1 p
    · exact wp_clock_frame (fun r => clockStep_id (by rw [h0]; decide) c _ _ r) _ hc
    · exact ⟨c, clockStep_err c _ _ _, hc⟩
  · exact ⟨c, clockStep_err c _ _ _, hc⟩

/-- **The preview1 clock stays behind the 0.2 clock** across every call. -/
theorem wp_body_clock {c : Option (BitVec 64)} (q : (nsig P1.imports).Op)
    {qT : Unit × Option (BitVec 64)} (hc : clockLe c qT.2) :
    Wp p2Th (body s q) (ClockQ c q.1.1 q.2) qT := by
  by_cases hct : q.1.1.fn = "clock_time_get"
  · have hb : body s q = clockTimeGet s q.2 := by
      simp +decide only [body, hct, ↓reduceIte]
    rw [hb, fn_eq q, hct]
    exact wp_clockTimeGet_clock q.2 hc
  · have hg : q.1.1 ≠ P1.fn "clock_time_get" := fun h => hct (by rw [h]; rfl)
    exact wp_clock_frame (fun r => clockStep_fn hg c _ r) _ hc

/-! ## The adapter implements preview1 -/

/-- The invariant: the preview1 clock is behind the 0.2 clock, and the descriptor invariant. -/
def J (s : ASt) (qT : Unit × Option (BitVec 64)) (qG : Unit × Option (BitVec 64) × Unit × FdSt) :
    Prop :=
  clockLe qG.2.1 qT.2 ∧ FdInv s qG.2.2.2

theorem th_step {qG : Unit × Option (BitVec 64) × Unit × FdSt} {e : WEv}
    {c' : Option (BitVec 64)} {f' : FdSt} (h1 : typedOk e = true)
    (h2 : P1.clockStep qG.2.1 e = some c') (h3 : boundsOk e = true)
    (h4 : fdStep qG.2.2.2 e = some f') : P1.th.step qG e = some ((), c', (), f') := by
  simp [P1.th, Protocol.prod, P1.typed, P1.bounds, pointwise, P1.clock, P1.fds, h1, h2, h3, h4]

/-- **The invariant method applies.** -/
theorem wpInv : WpInv body ASt.init p2Th P1.th J := by
  refine ⟨⟨trivial, fdInv_init⟩, fun s qT qG q hJ => ?_⟩
  have hg := Wp.and (wp_body hJ.2 q qT) (wp_body_clock q hJ.1)
  refine Wp.mono (fun r qT' ⟨⟨⟨ht, hb⟩, f', hf, hJf⟩, c', hc, hcl⟩ => ?_) hg
  rw [fn_eq q] at hc ⊢
  exact ⟨((), c', (), f'), th_step ht hc hb hf, hcl, hJf⟩

/-- **The adapter is correct under the 0.2 theory**: its returns satisfy the preview1 theory. -/
theorem adapter_sat : (agP p2Th (retG P1.th)).holds adapter := ag_of_wpInv wpInv

/-- **Preview1 over 0.2**: linked over any host satisfying the 0.2 theory, the adapter is a host
satisfying the preview1 theory. -/
theorem adapter_model {Y : Sig.{0}} {η : Host Y imports} (hη : (hostSat p2Th.Accepts).holds η) :
    (hostSat P1.th.Accepts).holds (link η adapter) :=
  link_model adapter_sat hη

end Silmaril.Wasi.Versions.Adapter
