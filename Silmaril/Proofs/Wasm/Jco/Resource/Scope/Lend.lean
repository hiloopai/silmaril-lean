module

public import Silmaril.Proofs.Wasm.Jco.Resource.Scope.Basic

/-!
# Full handles: lends are released; destructors

* `foldl_modLends_tab`: lend-count changes along a list of handles, per index;
* `liftArgsF_ok`: lifting an import's arguments lends exactly the recorded handles;
* **`canonLowerF_lends`**: a returning `canon lower` leaves every entry that was live before
  exactly as it was (in particular its `num_lends`), and `num_borrows` unchanged;
* `fDrop_lent`, `fDrop_dtor`: dropping a lent handle traps and runs no destructor; dropping an
  unlent `own` handle with a destructor removes it and then runs the destructor on the rep.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res.Scope

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res Silmaril.Wasm.Jco.Res.Scope
open Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat)

/-! ## Lend counts along a list -/

theorem modLends_tab (s : FSt) (i : Nat) (f : Nat → Nat) (j : Nat) :
    (s.modLends i f).tab j =
      if j = i then (s.tab j).map (fun e => { e with lends := f e.lends }) else s.tab j := rfl

theorem foldl_modLends_next (f : Nat → Nat) : ∀ (ls : List Nat) (s : FSt),
    (ls.foldl (fun s i => s.modLends i f) s).next = s.next ∧
      (ls.foldl (fun s i => s.modLends i f) s).borrows = s.borrows
  | [], _ => ⟨rfl, rfl⟩
  | i :: ls, s => foldl_modLends_next f ls (s.modLends i f)

theorem foldl_modLends_tab (f : Nat → Nat) : ∀ (ls : List Nat) (s : FSt) (j : Nat),
    (ls.foldl (fun s i => s.modLends i f) s).tab j =
      (s.tab j).map (fun e => { e with lends := f^[ls.count j] e.lends })
  | [], s, j => by
    show s.tab j = _
    cases s.tab j <;> rfl
  | i :: ls, s, j => by
    rw [List.foldl_cons, foldl_modLends_tab f ls, modLends_tab, List.count_cons]
    by_cases hj : j = i
    · subst hj
      cases s.tab j with
      | none => simp
      | some e => simp [Function.iterate_succ_apply]
    · have hij : (i == j) = false := by simpa using Ne.symm hj
      simp only [hj, ↓reduceIte, hij, Bool.false_eq_true, Nat.add_zero]

theorem iterate_succ_eq (c x : Nat) : (fun n => n + 1)^[c] x = x + c := by
  induction c generalizing x with
  | zero => rfl
  | succ c ih => rw [Function.iterate_succ_apply, ih]; omega

theorem iterate_pred_eq (c x : Nat) : (fun n => n - 1)^[c] x = x - c := by
  induction c generalizing x with
  | zero => rfl
  | succ c ih => rw [Function.iterate_succ_apply, ih]; omega

/-- Lending and then releasing the same handles restores every entry. -/
theorem release_lend (ls : List Nat) (s : FSt) (j : Nat) :
    (ls.foldl (fun s i => s.modLends i (· - 1)) (ls.foldl (fun s i => s.modLends i (· + 1)) s)).tab j =
      s.tab j := by
  rw [foldl_modLends_tab, foldl_modLends_tab]
  cases s.tab j with
  | none => rfl
  | some e =>
    simp only [Option.map_some, iterate_succ_eq, iterate_pred_eq, Nat.add_sub_cancel]

/-! ## Lifting the arguments of an import -/

variable (M : CoreInst)

/-- The state after lifting: the handles recorded as lenders have one more lend each. -/
theorem liftArgsF_ok : ∀ (ps : List RTy) (xs : List Flat) {st : (withTab M FSt).St}
    {vs : List RVal} {ls : List Nat} {st' : (withTab M FSt).St},
    liftArgsF M ps xs st (.ok (vs, ls) st') →
      st' = (st.1, ls.foldl (fun s i => s.modLends i (· + 1)) st.2)
  | [], [], st, vs, ls, st', h => by
    obtain ⟨he, rfl⟩ := pure_ok h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    rfl
  | [], _ :: _, _, _, _, _, h => by cases h
  | .base (.val t) :: ts, xs, st, vs, ls, st', h => by
    simp only [liftArgsF] at h
    rcases hl : t.lift xs with _ | ⟨v, rest⟩
    · rw [hl] at h
      cases h
    · rw [hl] at h
      obtain ⟨⟨vs', ls'⟩, st1, h1, h2⟩ := bind_ok h
      obtain ⟨he, rfl⟩ := pure_ok h2
      obtain ⟨-, rfl⟩ := Prod.mk.inj he
      exact liftArgsF_ok ts _ h1
  | .base .string :: _, _, _, _, _, _, h => by cases h
  | .base .bytes :: _, _, _, _, _, _, h => by cases h
  | .own _ :: _, _, _, _, _, _, h => by cases h
  | .borrow _ :: _, [], _, _, _, _, h => by cases h
  | .borrow r :: ts, x :: rest, st, vs, ls, st', h => by
    obtain ⟨hh, st1, h1, h2⟩ := bind_ok h
    have hst1 : st = st1 := by
      cases hx : asI32? x with
      | none => rw [hx] at h1; cases h1
      | some b => rw [hx] at h1; exact (pure_ok h1).2
    subst hst1
    obtain ⟨rep, st2, h3, h4⟩ := bind_ok h2
    obtain ⟨⟨vs', ls'⟩, st3, h5, h6⟩ := bind_ok h4
    obtain ⟨he, rfl⟩ := pure_ok h6
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    obtain ⟨rep', st4, h7, h8⟩ := bind_ok h3
    obtain ⟨t4, hf4, rfl⟩ := ofTab_ok h7
    obtain ⟨u, st5, h9, h10⟩ := bind_ok h8
    obtain ⟨-, rfl⟩ := pure_ok h10
    obtain ⟨t5, hf5, rfl⟩ := ofTab_ok h9
    have ht4 : t4 = st.2 := by
      revert hf4
      cases st.2.tab hh.toNat with
      | none => intro hf4; cases hf4
      | some e =>
        intro hf4
        dsimp only at hf4
        split at hf4
        · exact (Prod.mk.inj (Option.some.inj hf4)).2.symm
        · cases hf4
    subst ht4
    have ht5 : t5 = st.2.modLends hh.toNat (· + 1) := (Prod.mk.inj (Option.some.inj hf5)).2.symm
    subst ht5
    rw [liftArgsF_ok ts rest h5]
    rfl

/-! ## `canon lower` -/

/-- `fNew` changes no entry below `next`, and not `num_borrows`. -/
theorem fNew_below {r : RtId} {x : BitVec 32} {st : (withTab M FSt).St} {hn : BitVec 32}
    {st' : (withTab M FSt).St} (h : (fNew r x : RM (withTab M FSt).St _) st (.ok hn st')) :
    (∀ j, j < st.2.next → st'.2.tab j = st.2.tab j) ∧ st'.2.borrows = st.2.borrows := by
  obtain ⟨t4, hf4, rfl⟩ := ofTab_ok h
  dsimp only at hf4
  split at hf4
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hf4)
    refine ⟨fun j hj => ?_, rfl⟩
    have hne : j ≠ st.2.next := by omega
    show (if j = st.2.next then _ else st.2.tab j) = _
    simp only [hne, ↓reduceIte]
  · cases hf4

/-- Lowering the host's result changes no entry below `next`, and not `num_borrows`. -/
theorem lowerResF_ok (res : Option RTy) (r : Option RVal) {st : (withTab M FSt).St}
    {ys : List Flat} {st' : (withTab M FSt).St} (h : lowerResF M res r st (.ok ys st')) :
    (∀ j, j < st.2.next → st'.2.tab j = st.2.tab j) ∧ st'.2.borrows = st.2.borrows := by
  unfold lowerResF at h
  split at h
  · obtain ⟨-, rfl⟩ := pure_ok h
    exact ⟨fun _ _ => rfl, rfl⟩
  · obtain ⟨_, st4, h7, h8⟩ := bind_ok h
    obtain ⟨-, rfl⟩ := check_ok h7
    obtain ⟨-, rfl⟩ := pure_ok h8
    exact ⟨fun _ _ => rfl, rfl⟩
  · obtain ⟨hn, st4, h7, h8⟩ := bind_ok h
    obtain ⟨-, rfl⟩ := pure_ok h8
    exact fNew_below M h7
  · cases h

/-- **Lends are released.** A returning `canon lower` call leaves every entry that was live
before unchanged, and `num_borrows` unchanged. -/
theorem canonLowerF_lends (host : List RVal → RM M.St (Option RVal)) (sig : RSig) (xs : List Flat)
    {st : (withTab M FSt).St} {ys : List Flat} {st' : (withTab M FSt).St}
    (h : canonLowerF M host sig xs st (.ok ys st')) :
    (∀ j, j < st.2.next → st'.2.tab j = st.2.tab j) ∧ st'.2.borrows = st.2.borrows := by
  obtain ⟨⟨vs, ls⟩, st1, h1, h2⟩ := bind_ok h
  obtain ⟨r, st2, h3, h4⟩ := bind_ok h2
  obtain ⟨u, st3, h5, h6⟩ := bind_ok h4
  have e1 := liftArgsF_ok M sig.params xs h1
  have e2 : st2.2 = st1.2 := h3.2
  obtain ⟨t3, hf3, rfl⟩ := ofTab_ok h5
  have e3 : t3 = ls.foldl (fun s i => s.modLends i (· - 1)) st2.2 :=
    (Prod.mk.inj (Option.some.inj hf3)).2.symm
  have hmid : ∀ j, t3.tab j = st.2.tab j := by
    intro j
    rw [e3, e2, e1]
    exact release_lend ls st.2 j
  have hnb : t3.next = st.2.next ∧ t3.borrows = st.2.borrows := by
    rw [e3, e2, e1]
    obtain ⟨h1', h2'⟩ := foldl_modLends_next (· - 1) ls (ls.foldl (fun s i => s.modLends i (· + 1)) st.2)
    obtain ⟨h3', h4'⟩ := foldl_modLends_next (· + 1) ls st.2
    exact ⟨h1'.trans h3', h2'.trans h4'⟩
  obtain ⟨hl, hb⟩ := lowerResF_ok M sig.result r h6
  refine ⟨fun j hj => ?_, hb.trans hnb.2⟩
  rw [hl j (hnb.1 ▸ hj)]
  exact hmid j

/-! ## Destructors -/

variable {σ : Type} (R : RTypes σ)

/-- Binding after a deterministic step. -/
theorem bind_det {τ α β : Type} {m : RM τ α} {k : α → RM τ β} {s : τ} {a : α} {s1 : τ}
    (hm : m s = fun o => o = .ok a s1) : (m >>= k) s = k a s1 := by
  funext o
  apply propext
  rw [bind_apply, hm]
  constructor
  · rintro (⟨a', s', h1, h2⟩ | ⟨h1, -⟩)
    · obtain ⟨rfl, rfl⟩ := Out.ok.inj h1
      exact h2
    · cases h1
  · intro h2
    exact Or.inl ⟨a, s1, rfl, h2⟩

theorem remove_det {h : BitVec 32} {s : σ} {t : FSt} {e : FEntry} (he : t.tab h.toNat = some e) :
    (RM.ofTab (fun s : FSt => s.remove? h.toNat) : RM (σ × FSt) FEntry) (s, t) =
      fun o => o = .ok e (s, t.removed h.toNat) := by
  funext o
  simp [RM.ofTab, FSt.remove?, he, FSt.removed]

/-- Dropping a lent handle traps, and runs no destructor. -/
theorem fDrop_lent {r : RtId} {h : BitVec 32} {s : σ} {t : FSt} {e : FEntry}
    (he : t.tab h.toNat = some e) (hr : e.rt = r) (hl : e.lends ≠ 0) :
    fDrop R r h (s, t) = fail (s, t.removed h.toNat) := by
  have hrt : (e.rt == r) = true := by simp [hr]
  have hln : (e.lends == 0) = false := by simpa using hl
  unfold fDrop
  rw [bind_det (remove_det he)]
  simp only [hrt, hln, check_true, check_false, pure_bind, fail_bind]

/-- Dropping an unlent `own` handle of a type with a destructor removes it, then runs the
destructor on its rep. -/
theorem fDrop_dtor {r : RtId} {h : BitVec 32} {s : σ} {t : FSt} {e : FEntry}
    {d : BitVec 32 → RM (σ × FSt) Unit} (he : t.tab h.toNat = some e) (hr : e.rt = r)
    (hl : e.lends = 0) (ho : e.own = true) (hd : R.dtor r = some d) :
    fDrop R r h (s, t) = d e.rep (s, t.removed h.toNat) := by
  have hrt : (e.rt == r) = true := by simp [hr]
  have hln : (e.lends == 0) = true := by simp [hl]
  unfold fDrop
  rw [bind_det (remove_det he)]
  simp only [hrt, hln, check_true, pure_bind, ho, ↓reduceIte, hd]

end Silmaril.Proofs.Wasm.Jco.Res.Scope
