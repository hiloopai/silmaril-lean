module

public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsMain

/-!
# Proofs (unrefined): pollables with probed input streams

* `rd3_zero`: a zero-length `stream.read` keeps every rest of the 0.3 read theory;
* `pollPI_good`: the answers of `ready`/`block`/`poll` are admissible, whatever the host answers;
* `wp_pollF`: these calls keep the invariant.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3OverP2 (fsReadTh3w fsRead2 rd2Step rdShaped rdStepZ)

variable {F : BitVec 32 → List (BitVec 8)}

/-- **A zero-length read keeps every rest.** -/
theorem rd3_zero {q q' : RdSt} {rv nv : Val} {n : Option (List Val)}
    (h : (fsReadTh3w F).step q (.imp cStreamRead [rv, nv] n) = some q') (hz : natOf nv = some 0) :
    ∀ k, rest q' k = rest q k := by
  have hne : cStreamRead ≠ readVia3 := by decide
  have hsh : rdShaped (.imp cStreamRead [rv, nv] n) = true := by simp [rdShaped, hz, hne]
  have hs : rdStepZ F q (.imp cStreamRead [rv, nv] n) = some q' := by
    have h3 : (if rdShaped (.imp cStreamRead [rv, nv] n) then
        rdStepZ F q (.imp cStreamRead [rv, nv] n) else some q) = some q' := h
    rwa [ite_eq_left hsh] at h3
  intro k
  simp only [rdStepZ, hne, ite_false, ite_true] at hs
  split at hs
  · next _ _ rv' nv' pv items heq =>
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [hz] at hs
    split at hs
    · next _ _ _ bs j j' hb hj hc =>
      cases hj
      split at hs
      · next hcond =>
        have hj0 : j' = 0 := Nat.le_zero.1 hcond.2.1
        subst hj0
        obtain ⟨r', hr', hq⟩ := Option.map_eq_some_iff.1 hs
        subst hq
        have hrest : rest q r' = some bs := by rw [hr'] at hb; exact hb
        rw [rest_setRest]
        split
        · next hk => rw [hk, hrest, List.drop_zero]
        · rfl
      · exact absurd hs (by simp)
    · split at hs
      · cases hs; rfl
      · exact absurd hs (by simp)
    · cases hs; rfl
    · cases hs; rfl
    · exact absurd hs (by simp)
  · cases hs; rfl

/-! ## Answers -/

theorem pollPI_good (t : FsTab) (s : St) {o : IoOp} (a : List Val)
    (ho : o = .ready ∨ o = .block ∨ o = .poll) :
    Leaves (pollPI t s o a) (fun x => ansOk .loose s.io o a x.2 = true) := by
  rcases ho with rfl | rfl | rfl
  · exact leaves_bind_of (P := fun x : ISt × Option (List Val) =>
      ansOk .loose s.io .ready a x.2 = true) (fun _ => leaves_pure rfl) _
  · exact leaves_bind_of (P := fun x : ISt × Option (List Val) =>
      ansOk .loose s.io .block a x.2 = true) (fun _ => leaves_pure rfl) _
  · show Leaves (match a with
      | [Val.record ps] =>
        if ps.isEmpty = true then Prog.pure (s.impl, none)
        else Prog.bind (pollLoopI t rounds s.impl (handlesOf ps)) fun x =>
          Prog.pure (x.1, some [pollAnsOf ps.length x.2])
      | _ => Prog.pure (s.impl, some [Val.record []])) _
    split
    · rename_i ps
      by_cases he : ps.isEmpty
      · rw [ite_eq_left he]
        exact leaves_pure (by simp [ansOk, pollAns, he])
      · rw [ite_eq_right he]
        have hn : 0 < ps.length := List.length_pos_iff.2 (by simpa using he)
        refine leaves_bind_of (fun x => leaves_pure ?_) _
        show pollAns [.record ps] (some [pollAnsOf ps.length x.2]) = true
        obtain ⟨js, hjs, hne, hall⟩ := pollAnsOf_ok hn x.2
        simp [pollAns, he, hjs, hne, List.all_eq_true.2 hall]
    · rename_i hne
      refine leaves_pure ?_
      show pollAns a (some [.record []]) = true
      unfold pollAns
      split
      · exact absurd rfl (hne _)
      · rfl

theorem isPollOp_cases {o : IoOp} (h : isPollOp o = true) : o = .ready ∨ o = .block ∨ o = .poll := by
  cases o <;> simp_all [isPollOp]

theorem badZ_false {f : FnName} {a : List Val} (h : badZ f a = false) :
    f ≠ readVia3 ∧ (f = cStreamRead → zeroRd a = true) := by
  simp only [badZ, Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_false_iff_not,
    decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_false] at h
  exact ⟨h.1, h.2⟩

theorem zeroRd_cases {a : List Val} (h : zeroRd a = true) :
    ∃ rv nv, a = [rv, nv] ∧ natOf nv = some 0 := by
  match a, h with
  | [rv, nv], h => exact ⟨rv, nv, rfl, by simpa [zeroRd] using h⟩

/-- **`ready`/`block`/`poll` keep the invariant.** -/
theorem wp_pollF {s : StF} {f : FnName} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} (hJ : JF s qT ((s.io, g, (), ()), q2)) (hp : isPollOp (ioOp f) = true)
    (hmem : f ∈ exp2) : Wp (t3F F) (pollF s f a) (PostF F s f a g q2) qT := by
  obtain ⟨-, hclk, hI⟩ := hJ
  have ho := isPollOp_cases hp
  have hother : ioOp f ≠ .other := by rcases ho with h | h | h <;> rw [h] <;> decide
  have hn : f ≠ clockNow := fun h => by subst h; exact hother (by decide)
  have hrd : f ≠ isRead ∧ f ≠ isBread := by
    constructor
    · intro he; subst he; rcases ho with h | h | h <;> exact absurd h (by decide)
    · intro he; subst he; rcases ho with h | h | h <;> exact absurd h (by decide)
  have hst : (ioOp f).isStream = false := by rcases ho with h | h | h <;> rw [h] <;> rfl
  unfold pollF
  rw [Wp.bind]
  refine Wp.of_leavesC (C := fun f a => badZ f a = false)
    (R := fun q => ClkLe g q.1.last ∧ ∀ k, rest q.2 k = rest qT.2 k)
    (fun q f' a' n q' hq hC hs => ?_) (fun x q hq hx => ?_) _
    (leavesC_san _ _ _ (pollPI_good s.fs ⟨s.io, s.impl⟩ a ho)) ⟨hclk, fun _ => rfl⟩
  · obtain ⟨h1, h2⟩ := t3_step (qC := q.1) (q3 := q.2) (qC' := q'.1) (q3' := q'.2) hs
    obtain ⟨hv, hz⟩ := badZ_false hC
    refine ⟨clkLe_step hq.1 h1, fun k => ?_⟩
    by_cases hr : f' = cStreamRead
    · subst hr
      obtain ⟨rv, nv, rfl, hnv⟩ := zeroRd_cases (hz rfl)
      rw [rd3_zero h2 hnv k, hq.2 k]
    · rw [rd3_keep h2 hv hr, hq.2 k]
  · refine postF_of (x := (x.1, s.fs, x.2)) hn hI ?_ (shrinks_refl _) hq.1 (fun k _ => hq.2 k)
    exact {
      ans := hx
      p2 := by simp [p2Ok, hother]
      fs := fsOk_of_mem hmem a _
      rd := ⟨q2, rd2_other q2 a _ (ne_fdReadStream_of_mem hmem) hrd.1 hrd.2, fun _ => rfl⟩
      closed := fun h hc => by
        rcases ioUpd_closed hc with hc | ⟨-, hs', -⟩
        · exact .inl hc
        · rw [hst] at hs'; exact absurd hs' (by decide) }

end Silmaril.Wasi.Versions.P2OverP3
