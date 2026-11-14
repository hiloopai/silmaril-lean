module

public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsRvs

/-!
# Proofs (unrefined): reading a file stream

* `wp_readOnce`: one `stream.read(r, len)` under `t3F F` changes the 0.3 rest only of `r`'s end
  `k`, and its result is a prefix of what was left (`RStep`): data `ys` with
  `ys.take len = bs.take |ys.take len|` and rest `bs.drop |ys.take len|`; the end (`bs = []`); or
  nothing.
* `wp_waitR`, `wp_readLoopF`: the same for the blocking loop (waits read nothing).
* `RdInv.read`: the invariant after a read of the live file stream `h`.
* `wp_fsRead`: `read`/`blocking-read` of a live file stream keeps the invariant.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3OverP2 (fsReadTh3w fsRead2 rd2Step rdShaped rdStepZ)

variable {F : BitVec 32 → List (BitVec 8)}

/-! ## One read -/

/-- The rest of the end after a read result, from the rest `bs` before. -/
def RRes (len : Nat) (bs : List (BitVec 8)) : RdRes → Option (List (BitVec 8)) → Prop
  | .data ys, r' => ys.take len = bs.take (ys.take len).length ∧
      r' = some (bs.drop (ys.take len).length)
  | .eof, r' => bs = [] ∧ r' = some bs
  | .blocked, r' => r' = some bs

/-- A read of the end `k` from the theory state `q` to `q'` with the result `x`. -/
def RStep (k len : Nat) (q : ClockSt × RdSt) (x : RdRes) (q' : ClockSt × RdSt) : Prop :=
  (∀ g, ClkLe g q.1.last → ClkLe g q'.1.last) ∧ (∀ k', k' ≠ k → rest q'.2 k' = rest q.2 k') ∧
    ∀ bs, rest q.2 k = some bs → RRes len bs x (rest q'.2 k)

theorem drop_min (bs : List (BitVec 8)) (j : Nat) : bs.drop (min j bs.length) = bs.drop j := by
  rcases Nat.le_total j bs.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_length, List.drop_eq_nil_of_le h]

theorem rres_completed {len n j : Nat} {bs ys : List (BitVec 8)} (hn : n ≤ len) (hj : j ≤ n)
    (hys : ys = bs.take j) : RRes len bs (.data ys) (some (bs.drop j)) := by
  have hlen : ys.length ≤ len := by rw [hys, List.length_take]; omega
  have htake : ys.take len = ys := List.take_of_length_le hlen
  have hl : ys.length = min j bs.length := by rw [hys, List.length_take]
  refine ⟨?_, ?_⟩
  · rw [htake, hl, hys]
    rcases Nat.le_total j bs.length with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, List.take_length, List.take_of_length_le h]
  · rw [htake, hl, drop_min]

theorem natOf_natV (n : Nat) : natOf (natV n) = some (n % 2 ^ 32) := by
  simp [natOf, natV]

/-- The 0.3 read theory on the answer of a `stream.read` of an end with the rest `bs`. -/
theorem rres_of {q q' : RdSt} {r : Val} {k len : Nat} {bs : List (BitVec 8)}
    {n : Option (List Val)} (hz : rdStepZ F q (.imp cStreamRead [r, natV len] n) = some q')
    (hk : natOf r = some k) (hb : rest q k = some bs) : RRes len bs (readRes n) (rest q' k) := by
  have hne : cStreamRead ≠ readVia3 := by decide
  have hmod : len % 2 ^ 32 ≤ len := Nat.mod_le _ _
  have hkb : (natOf r >>= rest q) = some bs := by rw [hk]; exact hb
  rcases n with _ | ⟨_ | ⟨pv, _ | ⟨items, _ | ⟨x, l⟩⟩⟩⟩
  all_goals simp only [rdStepZ, hne, ite_false, ite_true] at hz
  all_goals try (cases hz; exact hb)
  simp only [hkb, natOf_natV] at hz
  show RRes len bs (match natOf pv >>= copyOf with
    | some (some (.completed, _)) => .data (bytesOf items)
    | some (some (.dropped, _)) => .eof
    | _ => .blocked) (rest q' k)
  split at hz
  · next _ _ _ bs' n' j hb' hn' hc' =>
    cases hb'; cases hn'
    rw [hc']
    split at hz
    · next hcond =>
      rw [hk] at hz
      cases hz
      rw [rest_setRest, ite_eq_left rfl]
      exact rres_completed hmod hcond.2.1 hcond.2.2
    · exact absurd hz (by simp)
  · next _ _ _ bs' n' hb' hn' hc' =>
    cases hb'
    rw [hc']
    split at hz
    · next hbs => cases hz; exact ⟨hbs, hb⟩
    · exact absurd hz (by simp)
  · next _ _ _ bs' n' hb' hn' hc' =>
    cases hz
    rw [hc']
    exact hb
  · exact absurd ‹some bs = none› (by simp)
  · exact absurd hz (by simp)

/-- **One `stream.read`.** -/
theorem wp_readOnce {r : Val} {k len : Nat} (hk : natOf r = some k) (q : ClockSt × RdSt) :
    Wp (t3F F) (readOnce r len) (fun x q' => RStep k len q x q') q := by
  intro n q' hs
  obtain ⟨h1, h2⟩ := t3_step (qC := q.1) (q3 := q.2) (qC' := q'.1) (q3' := q'.2) hs
  have h2' : (fsReadTh3w F).step q.2 (.imp cStreamRead [r, natV len] n) = some q'.2 := h2
  have hsh : rdShaped (.imp cStreamRead [r, natV len] n) = true := by
    simp [rdShaped, natOf_natV, show cStreamRead ≠ readVia3 by decide]
  have hz : rdStepZ F q.2 (.imp cStreamRead [r, natV len] n) = some q'.2 := by
    have h3 : (if rdShaped (.imp cStreamRead [r, natV len] n) then
        rdStepZ F q.2 (.imp cStreamRead [r, natV len] n) else some q.2) = some q'.2 := h2'
    rwa [ite_eq_left hsh] at h3
  have hother : ∀ k', k' ≠ k → rest q'.2 k' = rest q.2 k' := by
    intro k' hne
    rcases rd3_read_cases h2' with h | ⟨k'', v, hk', h⟩
    · rw [h]
    · simp only [keyOf, List.head?_cons, Option.bind_some, hk, Option.some.injEq] at hk'
      rw [h, rest_setRest, ite_eq_right (hk' ▸ hne)]
  exact ⟨fun g hg => clkLe_step hg h1, hother, fun bs hb => rres_of hz hk hb⟩

/-! ## The blocking loop -/

theorem rstep_refl (k len : Nat) (q : ClockSt × RdSt) : RStep k len q .blocked q :=
  ⟨fun _ h => h, fun _ _ => rfl, fun _ hb => hb⟩

theorem rstep_trans {k len : Nat} {q q1 q2 : ClockSt × RdSt} {x : RdRes}
    (h1 : RStep k len q .blocked q1) (h2 : RStep k len q1 x q2) : RStep k len q x q2 :=
  ⟨fun g hg => h2.1 g (h1.1 g hg), fun k' hk => (h2.2.1 k' hk).trans (h1.2.1 k' hk),
    fun bs hb => h2.2.2 bs (h1.2.2 bs hb)⟩

theorem rstep_empty {k len : Nat} {q q1 : ClockSt × RdSt}
    (h : RStep k len q (.data []) q1) : RStep k len q .blocked q1 := by
  refine ⟨h.1, h.2.1, fun bs hb => ?_⟩
  have := (h.2.2 bs hb).2
  simp only [List.take_nil, List.length_nil, List.drop_zero] at this
  exact this

theorem rstep_wait {k len : Nat} {q q1 : ClockSt × RdSt}
    (h : (∀ g, ClkLe g q.1.last → ClkLe g q1.1.last) ∧ q1.2 = q.2) : RStep k len q .blocked q1 :=
  ⟨h.1, fun _ _ => by rw [h.2], fun _ hb => by rw [h.2]; exact hb⟩

/-- **A wait reads nothing.** -/
theorem wp_waitR (st : ISt) (r : Val) (q : ClockSt × RdSt) :
    Wp (t3F F) (waitR st r)
      (fun _ (q' : ClockSt × RdSt) => (∀ g, ClkLe g q.1.last → ClkLe g q'.1.last) ∧ q'.2 = q.2)
      q := by
  refine Wp.of_leavesC (C := fun f a => badR f a = false)
    (R := fun (q' : ClockSt × RdSt) => (∀ g, ClkLe g q.1.last → ClkLe g q'.1.last) ∧ q'.2 = q.2)
    (fun q1 f a n q2 hq hC hs => ?_) (fun _ _ hq _ => hq) _
    (leavesC_san _ _ _ (leaves_of (P := fun _ => True) (fun _ => trivial) _))
    ⟨fun _ h => h, rfl⟩
  obtain ⟨h1, h2⟩ := t3_step (qC := q1.1) (q3 := q1.2) (qC' := q2.1) (q3' := q2.2) hs
  have hb : ¬ (f = readVia3 ∨ f = cStreamRead) := by simpa [badR] using hC
  exact ⟨fun g hg => clkLe_step (hq.1 g hg) h1,
    (rd3_keep h2 (fun h => hb (.inl h)) (fun h => hb (.inr h))).trans hq.2⟩

/-- **The blocking loop.** -/
theorem wp_readLoopF {r : Val} {k len : Nat} (hk : natOf r = some k) :
    ∀ (m : Nat) (st : ISt) (q : ClockSt × RdSt),
      Wp (t3F F) (readLoopF m st r len) (fun x q' => RStep k len q x.2 q') q
  | 0, st, q => rstep_refl k len q
  | m + 1, st, q => by
    unfold readLoopF
    rw [Wp.bind]
    refine Wp.mono (fun x q1 hx => ?_) (wp_readOnce hk q)
    have hloop : ∀ st', RStep k len q .blocked q1 →
        Wp (t3F F) ((waitR st' r).bind fun st'' => readLoopF m st'' r len)
          (fun x q' => RStep k len q x.2 q') q1 := fun st' hb => by
      rw [Wp.bind]
      exact Wp.mono (fun st'' q2 hw => Wp.mono (fun y q3 hy => rstep_trans
        (rstep_trans hb (rstep_wait hw)) hy) (wp_readLoopF hk m st'' q2)) (wp_waitR st' r q1)
    match x, hx with
    | .eof, hx => exact hx
    | .data bs, hx =>
      show Wp (t3F F) (if bs.isEmpty && decide (0 < len) then _ else _) _ q1
      split
      · next hc =>
        have hbs : bs = [] := List.isEmpty_iff.1 (Bool.and_eq_true _ _ ▸ hc).1
        subst hbs
        exact hloop st (rstep_empty hx)
      · exact hx
    | .blocked, hx => exact hloop st hx

end Silmaril.Wasi.Versions.P2OverP3
