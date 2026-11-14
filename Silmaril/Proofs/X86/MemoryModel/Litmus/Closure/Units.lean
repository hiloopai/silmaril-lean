module

public import Silmaril.X86.MemoryModel.Litmus.Closure.Defs

/-!
# Domain closure: units of traces, shapes and the domain chain

Proofs for `Silmaril/X86/MemoryModel/Litmus/Closure/Thms.lean`.

* `mem_uniq`, `chain_mono`, `chain_written`: the domain chain grows and contains every value a
  trace over the previous level writes;
* `threadUnits_mem`, `accUnits_mem`: where a unit of a choice of traces comes from (thread,
  action, program position);
* `accUnits_shape`, `tearAcc_shape`, `cellsOk_shape`: the units' shapes depend only on the
  traces' events, so the splitting and cell checks transfer between traces with the same
  skeleton.
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Closure

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec)
open Silmaril.X86.Litmus (Act Trace StepRec)

/-! ## Lists without repetition -/

theorem memB_iff {α : Type} [DecidableEq α] {a : α} : ∀ {l : List α}, memB a l = true ↔ a ∈ l
  | [] => by simp [memB]
  | b :: l => by
    by_cases h : a = b
    · subst h; simp [memB]
    · simp [memB, h, memB_iff]

theorem mem_addU {α : Type} [DecidableEq α] {a b : α} {l : List α} :
    a ∈ addU b l ↔ a = b ∨ a ∈ l := by
  unfold addU
  split
  · rename_i h
    rw [memB_iff] at h
    constructor
    · exact Or.inr
    · rintro (rfl | h') <;> assumption
  · simp

theorem mem_uniq {α : Type} [DecidableEq α] {a : α} : ∀ {l : List α}, a ∈ uniq l ↔ a ∈ l
  | [] => by simp [uniq]
  | b :: l => by
    have : uniq (b :: l) = addU b (uniq l) := rfl
    rw [this, mem_addU, mem_uniq]
    simp

/-! ## The domain chain -/

theorem domStep_sup (t : Test) (d : List Nat) {v : Nat} (h : v ∈ d) : v ∈ t.domStep d := by
  unfold Test.domStep
  split
  · exact h
  · exact mem_uniq.mpr (List.mem_append_left _ h)

theorem domStep_written {t : Test} {d : List Nat} {T : List (List XTrace)}
    (h : t.extractOver d = some T) {tr : XTrace} (htr : tr ∈ T.flatten) {v : Nat}
    (hv : v ∈ tr.written) : v ∈ t.domStep d := by
  unfold Test.domStep
  rw [h]
  exact mem_uniq.mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨tr, htr, hv⟩))

theorem chain_mono (t : Test) {k : Nat} {v : Nat} (h : v ∈ t.chain k) : v ∈ t.chain (k + 1) :=
  domStep_sup t _ h

theorem chain_le (t : Test) {a b : Nat} (hab : a ≤ b) {v : Nat} (h : v ∈ t.chain a) :
    v ∈ t.chain b := by
  induction hab with
  | refl => exact h
  | step _ ih => exact chain_mono t ih

theorem chain_ne_nil (t : Test) (h : t.dom0 ≠ []) : ∀ k, t.chain k ≠ []
  | 0 => h
  | k + 1 => by
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (chain_ne_nil t h k)
    exact List.ne_nil_of_mem (chain_mono t hv)

/-! ## Per-thread extraction -/

theorem mapM_id_getElem? {β : Type} :
    ∀ {L : List (Option β)} {T : List β}, L.mapM id = some T →
      ∀ (k : Nat) (o : Option β), L[k]? = some o → ∃ y, o = some y ∧ T[k]? = some y
  | [], _, _, k, o, hk => by simp at hk
  | a :: L, T, h, k, o, hk => by
    rw [List.mapM_cons] at h
    simp only [id, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, rfl, ys, hl, rfl⟩ := h
    cases k with
    | zero => simp at hk; exact ⟨y, hk.symm, rfl⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk ⊢
      exact mapM_id_getElem? hl k o hk

theorem mapM_id_length {β : Type} :
    ∀ {L : List (Option β)} {T : List β}, L.mapM id = some T → T.length = L.length
  | [], T, h => by simp at h; subst h; rfl
  | a :: L, T, h => by
    rw [List.mapM_cons] at h
    simp only [id, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, rfl, ys, hl, rfl⟩ := h
    simp [mapM_id_length hl]

theorem extractOver_thread {t : Test} {D : List Nat} {T : List (List XTrace)}
    (h : t.extractOver D = some T) {k : Nat} {th : Thread} (hk : t.threads[k]? = some th) :
    ∃ trs, T[k]? = some trs ∧
      Silmaril.X86.Litmus.extract (t.xthread k th) D t.fuel = some trs := by
  unfold Test.extractOver at h
  obtain ⟨trs, he, hT⟩ := mapM_id_getElem? h k
    (Silmaril.X86.Litmus.extract (t.xthread k th) D t.fuel)
    (by simp [List.getElem?_mapIdx, hk])
  exact ⟨trs, hT, he⟩

theorem extractOver_length {t : Test} {D : List Nat} {T : List (List XTrace)}
    (h : t.extractOver D = some T) : T.length = t.threads.length := by
  unfold Test.extractOver at h
  rw [mapM_id_length h, List.length_mapIdx]

/-! ## Units of actions -/

/-- The number of units of an action. -/
def actLen (a : XAct) : Nat :=
  match a.ev.kind with
  | .rmw => 2
  | _ => 1

theorem actUnits_length (i p : Nat) (a : XAct) : (actUnits i p a).length = actLen a := by
  unfold actUnits actLen
  split <;> simp_all

theorem actLen_pos (a : XAct) : 0 < actLen a := by
  unfold actLen; split <;> omega

/-- The program position of action `j`'s first unit (relative to the thread's start). -/
def posOff (acts : List XAct) (j : Nat) : Nat := ((acts.take j).map actLen).sum

theorem posOff_zero (acts : List XAct) : posOff acts 0 = 0 := by simp [posOff]

theorem posOff_cons_succ (a : XAct) (as : List XAct) (j : Nat) :
    posOff (a :: as) (j + 1) = actLen a + posOff as j := by
  simp [posOff]

theorem posOff_succ {acts : List XAct} {j : Nat} {a : XAct} (h : acts[j]? = some a) :
    posOff acts (j + 1) = posOff acts j + actLen a := by
  unfold posOff
  rw [List.take_add_one, h]
  simp

theorem posOff_le_succ (acts : List XAct) (j : Nat) : posOff acts j ≤ posOff acts (j + 1) := by
  unfold posOff
  rw [List.take_add_one, List.map_append, List.sum_append]
  omega

theorem posOff_mono (acts : List XAct) {j j' : Nat} (h : j' ≤ j) :
    posOff acts j' ≤ posOff acts j := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (posOff_le_succ acts _)

theorem posOff_lt {acts : List XAct} {j j' : Nat} {a : XAct} (h : acts[j']? = some a)
    (hlt : j' < j) : posOff acts j' + actLen a ≤ posOff acts j := by
  rw [← posOff_succ h]
  exact posOff_mono acts hlt

/-- Where a unit of a thread comes from. -/
theorem threadUnits_mem {i : Nat} :
    ∀ {acts : List XAct} {p : Nat} {u : Ev × List Byte}, u ∈ threadUnits i p acts ↔
      ∃ j a, acts[j]? = some a ∧ u ∈ actUnits i (p + posOff acts j) a
  | [], p, u => by simp [threadUnits]
  | a :: as, p, u => by
    simp only [threadUnits, List.mem_append, actUnits_length]
    rw [threadUnits_mem]
    constructor
    · rintro (h | ⟨j, a', hj, h⟩)
      · exact ⟨0, a, rfl, by simpa [posOff_zero] using h⟩
      · refine ⟨j + 1, a', by simpa using hj, ?_⟩
        rw [posOff_cons_succ, ← Nat.add_assoc]
        exact h
    · rintro ⟨j, a', hj, h⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        exact Or.inl (by simpa [posOff_zero] using h)
      | succ j =>
        refine Or.inr ⟨j, a', by simpa using hj, ?_⟩
        rw [posOff_cons_succ, ← Nat.add_assoc] at h
        exact h

/-- Where a unit of a choice of traces comes from. -/
theorem accUnits_mem {trs : List XTrace} {u : Ev × List Byte} :
    u ∈ accUnits trs ↔ ∃ i tr, trs[i]? = some tr ∧ u ∈ threadUnits i 0 tr.acts := by
  unfold accUnits
  simp only [List.mem_flatten, List.mem_mapIdx]
  constructor
  · rintro ⟨l, ⟨i, hi, rfl⟩, hu⟩
    exact ⟨i, trs[i], by simp [hi], hu⟩
  · rintro ⟨i, tr, hi, hu⟩
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
    exact ⟨_, ⟨i, hlt, rfl⟩, hu⟩

/-! ## What the units of an action are -/

theorem actUnits_tid {i p : Nat} {a : XAct} {u : Ev × List Byte} (h : u ∈ actUnits i p a) :
    u.1.tid = i := by
  unfold actUnits at h
  split at h <;> simp at h <;> (try rcases h with h | h) <;> (try subst h) <;> rfl

theorem actUnits_write {i p : Nat} {a : XAct} {u : Ev × List Byte} (h : u ∈ actUnits i p a)
    (hw : u.1.isW = true) :
    a.ev.kind.writes = true ∧ p ≤ u.1.pos ∧ (a.ev.kind.reads = true → p < u.1.pos) ∧
      u.1.data = a.wr ∧ u.1.addr = a.ev.addr ∧ u.1.size = a.ev.size := by
  unfold actUnits at h
  split at h <;> rename_i hk <;> simp at h <;> (try rcases h with h | h) <;> (try subst h) <;>
    simp_all [Ev.isW, Silmaril.X86.MemEvent.Kind.writes, Silmaril.X86.MemEvent.Kind.reads]

theorem actUnits_read {i p : Nat} {a : XAct} {u : Ev × List Byte} (h : u ∈ actUnits i p a)
    (hr : u.1.isR = true) : a.ev.kind.reads = true ∧ u.2 = a.rd := by
  unfold actUnits at h
  split at h <;> rename_i hk <;> simp at h <;> (try rcases h with h | h) <;> (try subst h) <;>
    simp_all [Ev.isR, Silmaril.X86.MemEvent.Kind.reads]

theorem actUnits_read_exists (i p : Nat) (a : XAct) (hr : a.ev.kind.reads = true) :
    ∃ u ∈ actUnits i p a, u.1.isR = true ∧ u.1.tid = i ∧ u.1.pos = p ∧ u.2 = a.rd := by
  unfold actUnits
  split <;> rename_i hk <;> simp_all [Ev.isR, Silmaril.X86.MemEvent.Kind.reads]

/-! ## Shapes -/

theorem actUnits_shape (i p : Nat) {a a' : XAct} (h : a.ev = a'.ev) :
    (actUnits i p a).map (shape ∘ Prod.fst) = (actUnits i p a').map (shape ∘ Prod.fst) := by
  unfold actUnits
  rw [h]
  split <;> simp [shape]

theorem threadUnits_shape (i : Nat) :
    ∀ {acts acts' : List XAct} (p : Nat), acts.map Act.ev = acts'.map Act.ev →
      (threadUnits i p acts).map (shape ∘ Prod.fst) = (threadUnits i p acts').map (shape ∘ Prod.fst)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, a' :: as', p, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hl : (actUnits i p a).length = (actUnits i p a').length := by
      rw [actUnits_length, actUnits_length]; unfold actLen; rw [h.1]
    simp only [threadUnits, List.map_append]
    rw [actUnits_shape i p h.1, hl, threadUnits_shape i _ h.2]

theorem accUnits_shape {trs trs' : List XTrace}
    (h : trs.map (fun tr => tr.acts.map Act.ev) = trs'.map (fun tr => tr.acts.map Act.ev)) :
    (accUnits trs).map (shape ∘ Prod.fst) = (accUnits trs').map (shape ∘ Prod.fst) := by
  unfold accUnits
  rw [List.map_flatten, List.map_flatten]
  congr 1
  have hlen : trs.length = trs'.length := by simpa using congrArg List.length h
  apply List.ext_getElem (by simp [hlen])
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_mapIdx]
  have hn : n < trs.length := by simpa using h1
  have := congrArg (·[n]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hn,
    List.getElem?_eq_getElem (hlen ▸ hn : n < trs'.length), Option.map_some,
    Option.some.injEq] at this
  exact threadUnits_shape n 0 this

theorem tearAcc_shape (us : List (Ev × List Byte)) (u : Ev) :
    tearAcc us u = tearAcc ((us.map (shape ∘ Prod.fst)).map fun e => (e, ([] : List Byte)))
      (shape u) := by
  simp only [tearAcc, List.any_map]
  rfl

theorem cellsOk_shape (evs : List Ev) : cellsOk evs = cellsOk (evs.map shape) := by
  simp only [cellsOk, List.filter_map, List.all_map]
  rfl

end Silmaril.Proofs.X86.MemoryModel.Litmus.Closure
