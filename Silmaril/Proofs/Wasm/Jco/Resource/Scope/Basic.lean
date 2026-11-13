module

public import Silmaril.Proofs.Wasm.Jco.Resource.Scope.Keeps

/-!
# Full handles: every operation keeps the invariant; the borrow-scope theorem

* `bind_ok`, `check_ok`: inverting returning runs;
* `keeps_fNew`, `keeps_fBorrow`, `keeps_fRep`, `keeps_fLend`, `keeps_fTake`, `keeps_fDrop`: the
  table operations keep `FSt.Inv` (`fDrop` when the destructors do);
* `keeps_execB`, `keeps_runB`: so does **every** adaptor function run with the built-ins
  `fullB R`;
* `keeps_lowerParamsF`, `keeps_liftResultF`;
* **`canonCallF_scope`**: a returning `canon lift` call ends with the invariant, no borrows
  outstanding and no borrow entry left in the table, for every callee that keeps the invariant.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res.Scope

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res Silmaril.Wasm.Jco.Res.Scope
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat)

variable {σ α β : Type}

theorem bind_ok {m : RM σ α} {k : α → RM σ β} {s : σ} {b : β} {s'' : σ}
    (h : (m >>= k) s (.ok b s'')) : ∃ a s', m s (.ok a s') ∧ k a s' (.ok b s'') := by
  rcases h with h | ⟨_, h⟩
  · exact h
  · cases h

theorem check_ok {b : Bool} {s s' : σ} (h : (check b : RM σ Unit) s (.ok () s')) :
    b = true ∧ s = s' := by
  cases b
  · cases h
  · exact ⟨rfl, (Out.ok.inj h).2.symm⟩

theorem pure_ok {a b : α} {s s' : σ} (h : (pure a : RM σ α) s (.ok b s')) : b = a ∧ s = s' := by
  have h' := Out.ok.inj h
  exact ⟨h'.1, h'.2.symm⟩

section Ops

variable (R : RTypes σ)

/-- The destructors keep the invariant. -/
def DtorsKeep : Prop := ∀ r d, R.dtor r = some d → ∀ x, Keeps FSt.Inv (d x)

theorem keeps_fNew (r : RtId) (rep : BitVec 32) : Keeps FSt.Inv (fNew r rep : RM (σ × FSt) _) := by
  refine keeps_ofTab fun t a t' hI h => ?_
  dsimp only at h
  split at h
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact inv_add_own hI rfl
  · cases h

theorem keeps_fBorrow (r : RtId) (rep : BitVec 32) :
    Keeps FSt.Inv (fBorrow r rep : RM (σ × FSt) _) := by
  refine keeps_ofTab fun t a t' hI h => ?_
  dsimp only at h
  split at h
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact inv_add_borrow hI rfl
  · cases h

theorem keeps_fRep (r : RtId) (h : BitVec 32) : Keeps FSt.Inv (fRep r h : RM (σ × FSt) _) := by
  refine keeps_ofTab fun t a t' hI hf => ?_
  split at hf
  · split at hf
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hf)
      exact hI
    · cases hf
  · cases hf

theorem keeps_fLend (r : RtId) (h : BitVec 32) : Keeps FSt.Inv (fLend r h : RM (σ × FSt) _) := by
  refine keeps_bind (keeps_fRep r h) fun rep => keeps_bind ?_ fun _ => keeps_pure rep
  refine keeps_ofTab fun t a t' hI hf => ?_
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hf)
  exact inv_modLends hI _ _

/-- The removal at the start of `fDrop` and `fTake`, with its checks: the state after it, and
what it says about the entry. -/
theorem remove_checks {st st1 : σ × FSt} {h : BitVec 32} {e : FEntry}
    (h1 : RM.ofTab (fun s : FSt => s.remove? h.toNat) st (.ok e st1)) (hI : st.2.Inv) :
    (∀ j, st1.2.next ≤ j → st1.2.tab j = none) ∧
      FSt.countB st1.2.tab st1.2.next + isB (some e) = st.2.borrows ∧
        st1.2.borrows = st.2.borrows := by
  obtain ⟨t', hft, rfl⟩ := ofTab_ok h1
  obtain ⟨-, h2, h3, h4⟩ := inv_remove hI hft
  exact ⟨h2, h3, h4⟩

theorem keeps_fTake (r : RtId) (h : BitVec 32) : Keeps FSt.Inv (fTake r h : RM (σ × FSt) _) := by
  intro st a st' hI hrun
  obtain ⟨e, st1, h1, h2⟩ := bind_ok hrun
  obtain ⟨_, st2, h3, h4⟩ := bind_ok h2
  obtain ⟨-, rfl⟩ := check_ok h3
  obtain ⟨_, st3, h5, h6⟩ := bind_ok h4
  obtain ⟨-, rfl⟩ := check_ok h5
  obtain ⟨_, st4, h7, h8⟩ := bind_ok h6
  obtain ⟨hown, rfl⟩ := check_ok h7
  obtain ⟨-, rfl⟩ := pure_ok h8
  obtain ⟨hn, hc, hb⟩ := remove_checks h1 hI
  refine ⟨hn, ?_⟩
  simp only [isB, hown, ↓reduceIte, Nat.add_zero] at hc
  rw [hb, hc]

/-- The end of `fDrop` on an `own` entry: the destructor, if any. -/
theorem drop_tail_own (hd : DtorsKeep R) {st st1 st' : σ × FSt} {e : FEntry} {r : RtId} {a : Unit}
    (hf : (∀ j, st1.2.next ≤ j → st1.2.tab j = none) ∧
      FSt.countB st1.2.tab st1.2.next + isB (some e) = st.2.borrows ∧ st1.2.borrows = st.2.borrows)
    (hown : e.own = true)
    (h6 : (match R.dtor r with | some d => d e.rep | none => pure ()) st1 (.ok a st')) :
    st'.2.Inv := by
  have hc : FSt.countB st1.2.tab st1.2.next = st.2.borrows := by
    simpa only [isB, hown, ↓reduceIte, Nat.add_zero] using hf.2.1
  have hI1 : st1.2.Inv := ⟨hf.1, hf.2.2.trans hc.symm⟩
  revert h6
  cases hdr : R.dtor r with
  | none => exact keeps_pure () st1 a st' hI1
  | some d => exact hd r d hdr e.rep st1 a st' hI1

/-- The end of `fDrop` on a borrow entry: `num_borrows -= 1`. -/
theorem drop_tail_borrow {st st1 st' : σ × FSt} {e : FEntry} {a : Unit}
    (hf : (∀ j, st1.2.next ≤ j → st1.2.tab j = none) ∧
      FSt.countB st1.2.tab st1.2.next + isB (some e) = st.2.borrows ∧ st1.2.borrows = st.2.borrows)
    (hown : e.own = false)
    (h6 : (RM.ofTab fun s : FSt => some ((), { s with borrows := s.borrows - 1 })) st1 (.ok a st')) :
    st'.2.Inv := by
  have hc : FSt.countB st1.2.tab st1.2.next + 1 = st.2.borrows := by
    simpa only [isB, hown, Bool.false_eq_true, ↓reduceIte] using hf.2.1
  obtain ⟨t', hft, hst⟩ := ofTab_ok h6
  have ht' : t' = { st1.2 with borrows := st1.2.borrows - 1 } := (Prod.mk.inj (Option.some.inj hft)).2.symm
  rw [hst, ht']
  refine ⟨hf.1, ?_⟩
  show st1.2.borrows - 1 = FSt.countB st1.2.tab st1.2.next
  omega

theorem keeps_fDrop (hd : DtorsKeep R) (r : RtId) (h : BitVec 32) :
    Keeps FSt.Inv (fDrop R r h) := by
  intro st a st' hI hrun
  obtain ⟨e, st1, h1, h2⟩ := bind_ok hrun
  obtain ⟨_, st2, h3, h4⟩ := bind_ok h2
  obtain ⟨-, rfl⟩ := check_ok h3
  obtain ⟨_, st3, h5, h6⟩ := bind_ok h4
  obtain ⟨-, rfl⟩ := check_ok h5
  have hf := remove_checks h1 hI
  cases hown : e.own
  · rw [hown] at h6
    exact drop_tail_borrow hf hown h6
  · rw [hown] at h6
    exact drop_tail_own R hd hf hown h6

theorem keeps_unary {f : BitVec 32 → RM (σ × FSt) (List Flat)}
    (hf : ∀ x, Keeps FSt.Inv (f x)) (xs : List Flat) : Keeps FSt.Inv (unary f xs) := by
  unfold unary
  split
  · exact hf _
  · exact keeps_fail

theorem keeps_new (r : RtId) (xs : List Flat) : Keeps FSt.Inv ((fullB R).new r xs) :=
  keeps_unary (fun x => keeps_bind (keeps_fNew r x) fun _ => keeps_pure _) xs

theorem keeps_rep (r : RtId) (xs : List Flat) : Keeps FSt.Inv ((fullB R).rep r xs) :=
  keeps_unary (fun x => keeps_bind (keeps_fRep r x) fun _ => keeps_pure _) xs

theorem keeps_drop (hd : DtorsKeep R) (r : RtId) (xs : List Flat) :
    Keeps FSt.Inv ((fullB R).drop r xs) :=
  keeps_unary (fun x => keeps_bind (keeps_fDrop R hd r x) fun _ => keeps_pure _) xs

end Ops

/-! ## Adaptor code -/

variable (M : CoreInst) (R : RTypes M.St)

theorem keeps_callTopB {b : List Flat → RM (M.St × FSt) (List Flat)}
    (hb : ∀ xs, Keeps FSt.Inv (b xs)) (f : Frame) : Keeps FSt.Inv (callTopB M b f) := by
  unfold callTopB
  split
  · exact keeps_bind (hb _) fun _ => keeps_pure _
  · exact keeps_fail

theorem keeps_stepB (hd : DtorsKeep R) (i : RInstr) (f : Frame) :
    Keeps FSt.Inv (i.stepB M (fullB R) f) := by
  cases i with
  | base i =>
    show Keeps FSt.Inv (i.step (withTab M FSt) f)
    rw [step_withTab]
    exact keeps_onFst _
  | resNew r => exact keeps_callTopB M (keeps_new R r) f
  | resRep r => exact keeps_callTopB M (keeps_rep R r) f
  | resDrop r => exact keeps_callTopB M (keeps_drop R hd r) f

theorem keeps_execB (hd : DtorsKeep R) :
    ∀ (is : List RInstr) (f : Frame), Keeps FSt.Inv (execB M (fullB R) is f)
  | [], _ => keeps_pure _
  | i :: is, f => keeps_bind (keeps_stepB M R hd i f) fun f' => keeps_execB hd is f'

/-- **Every adaptor function**, run with the built-ins `fullB R`, keeps the invariant. -/
theorem keeps_runB (hd : DtorsKeep R) (fn : RFn) (xs : List Flat) :
    Keeps FSt.Inv (fn.runB M (fullB R) xs) := by
  refine keeps_bind (keeps_execB M R hd _ _) fun f => keeps_bind (keeps_check _) fun _ => ?_
  refine keeps_bind ?_ fun rs => keeps_bind (keeps_execB M R hd _ _) fun _ => keeps_pure _
  rw [run_withTab]
  exact keeps_onFst _

/-! ## `canon lift` -/

theorem keeps_lowerParamF (rw : List Flat → RM M.St (List Flat)) (t : RTy) (v : RVal) :
    Keeps FSt.Inv (lowerParamF R M (fun xs => (rw xs).onFst) t v) := by
  cases t <;> cases v
  case base.base t v =>
    show Keeps FSt.Inv (lowerParam (withTab M FSt) _ t v)
    rw [lowerParam_withTab]
    exact keeps_onFst _
  case own.res r x => exact keeps_bind (keeps_fNew r x) fun _ => keeps_pure _
  case borrow.res r x =>
    show Keeps FSt.Inv (if R.impl r then _ else _)
    split
    · exact keeps_pure _
    · exact keeps_bind (keeps_fBorrow r x) fun _ => keeps_pure _
  all_goals exact keeps_fail

theorem keeps_lowerParamsF (rw : List Flat → RM M.St (List Flat)) :
    ∀ (ps : List RTy) (vs : List RVal),
      Keeps FSt.Inv (lowerParamsF R M (fun xs => (rw xs).onFst) ps vs)
  | [], [] => keeps_pure _
  | [], _ :: _ => keeps_fail
  | _ :: _, [] => keeps_fail
  | p :: ps, v :: vs => keeps_bind (keeps_lowerParamF M R rw p v) fun _ =>
      keeps_bind (keeps_lowerParamsF rw ps vs) fun _ => keeps_pure _

theorem keeps_liftResultF (res : Option RTy) (xs : List Flat) :
    Keeps FSt.Inv (liftResultF M res xs) := by
  rcases res with _ | (t | r | r)
  · refine keeps_bind ?_ fun _ => keeps_pure _
    rw [liftResult_withTab]
    exact keeps_onFst _
  · refine keeps_bind ?_ fun _ => keeps_pure _
    rw [liftResult_withTab]
    exact keeps_onFst _
  · rcases xs with _ | ⟨x, _ | _⟩
    · exact keeps_fail
    · exact keeps_bind (keeps_ofOption _) fun h => keeps_bind (keeps_fTake r h) fun _ => keeps_pure _
    · exact keeps_fail
  · exact keeps_fail

theorem exitCheck_ok {st st' : (withTab M FSt).St} {u : Unit} (h : exitCheck M st (.ok u st')) :
    st.2.borrows = 0 ∧ st = st' := by
  unfold exitCheck at h
  split at h
  · next hb => exact ⟨hb, (Out.ok.inj h).2.symm⟩
  · cases h

/-- **The borrow-scope theorem.** A returning `canon lift` call, from a state with the
invariant, whose callee keeps the invariant, ends with the invariant, `num_borrows = 0`, and
only `own` entries in the table: every borrow handle the call lent to the callee was dropped. -/
theorem canonCallF_scope (rw : List Flat → RM M.St (List Flat))
    {callee : List Flat → RM (withTab M FSt).St (List Flat)}
    (hc : ∀ xs, Keeps FSt.Inv (callee xs)) (sig : RSig) (vs : List RVal)
    {st : (withTab M FSt).St} {a : Option RVal} {st' : (withTab M FSt).St} (hI : st.2.Inv)
    (h : canonCallF R M (fun xs => (rw xs).onFst) callee sig vs st (.ok a st')) :
    st'.2.Inv ∧ st'.2.borrows = 0 ∧ ∀ j e, st'.2.tab j = some e → e.own = true := by
  obtain ⟨xs, st1, h1, h2⟩ := bind_ok h
  obtain ⟨rs, st2, h3, h4⟩ := bind_ok h2
  obtain ⟨r, st3, h5, h6⟩ := bind_ok h4
  obtain ⟨u, st4, h7, h8⟩ := bind_ok h6
  obtain ⟨-, rfl⟩ := pure_ok h8
  have hI1 := keeps_lowerParamsF M R rw sig.params vs st xs st1 hI h1
  have hI2 := hc xs st1 rs st2 hI1 h3
  have hI3 := keeps_liftResultF M sig.result rs st2 r st3 hI2 h5
  obtain ⟨hb, rfl⟩ := exitCheck_ok M h7
  refine ⟨hI3, hb, fun j e hj => ?_⟩
  by_cases hjn : j < st3.2.next
  · have hz := countB_zero (hI3.2 ▸ hb) j hjn
    rw [hj] at hz
    simpa [isB] using hz
  · rw [hI3.1 j (by omega)] at hj
    cases hj

/-- The borrow-scope theorem for **any adaptor function** as the callee. -/
theorem canonCallF_scope_runB (hd : DtorsKeep R) (rw : List Flat → RM M.St (List Flat))
    (fn : RFn) (sig : RSig) (vs : List RVal) {st : (withTab M FSt).St} {a : Option RVal}
    {st' : (withTab M FSt).St} (hI : st.2.Inv)
    (h : canonCallF R M (fun xs => (rw xs).onFst) (fn.runB M (fullB R)) sig vs st (.ok a st')) :
    st'.2.Inv ∧ st'.2.borrows = 0 ∧ ∀ j e, st'.2.tab j = some e → e.own = true :=
  canonCallF_scope M R rw (keeps_runB M R hd fn) sig vs hI h

end Silmaril.Proofs.Wasm.Jco.Res.Scope
