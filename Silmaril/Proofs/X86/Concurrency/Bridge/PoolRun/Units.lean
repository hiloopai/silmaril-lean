module

public import Silmaril.X86.Concurrency.Bridge.PoolRun.Defs
public import Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Transport

/-!
# The store-buffer machine units against the litmus units

For traces `trs`, the units the store-buffer machine gives the program `trs.mapIdx traceX`
(`OpAx.progUnits`) and the units the litmus translation gives the traces (`Litmus.accUnits`) are,
forgetting
positions and annotations (`strip`), the same lists once the litmus `lfence`/`sfence` units are
removed (`progUnits_strip`), when the actions are `ActOk`. Both lists order the units of one
thread by position (`posOrd_acc`, `posOrd_prog`); the litmus translation numbers them consecutively
(`consec_acc`)
and the store-buffer machine puts the write half of a locked read-modify-write right after its read
(`rmwNext_prog`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun

open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec Act)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace actX traceX actUnits accUnits Byte)
open Silmaril.X86.MemoryModel.Tso (XEvent)
open Silmaril.X86.MemoryModel.OpAx (evUnits progUnits)
open Silmaril.X86.Concurrency.Bridge.PoolRun
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte

/-- A unit without its position and annotation. -/
def strip (u : Ev × List Byte) : Nat × Act × Nat × Nat × Bool × List Byte × List Byte :=
  (u.1.tid, u.1.act, u.1.addr, u.1.size, u.1.locked, u.1.data, u.2)

/-- Not an `lfence`/`sfence` unit. -/
def realU (u : Ev × List Byte) : Bool := realE u.1

/-! ## Lists -/

theorem mapIdx_congr {α β : Type} {l : List α} {f g : Nat → α → β}
    (h : ∀ i (hi : i < l.length), f i l[i] = g i l[i]) : l.mapIdx f = l.mapIdx g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx]
  exact h i (by simpa using h1)

theorem map_mapIdx' {α β γ : Type} (l : List α) (f : Nat → α → β) (g : β → γ) :
    (l.mapIdx f).map g = l.mapIdx fun i a => g (f i a) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem mapIdx_const {α β : Type} {l : List α} {f : Nat → α → β} {g : α → β}
    (h : ∀ i (hi : i < l.length), f i l[i] = g l[i]) : l.mapIdx f = l.map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx, List.getElem_map]
  exact h i (by simpa using h1)

/-! ## Stripped units -/

theorem evUnits_strip (i k : Nat) (e : XEvent Nat) :
    (evUnits i k e).map strip = (evUnits i 0 e).map strip := by
  cases e <;> rfl

theorem threadUnitsK_strip (i : Nat) (es : List (XEvent Nat)) :
    (Silmaril.X86.MemoryModel.OpAx.threadUnits i es).map strip =
      es.flatMap fun e => (evUnits i 0 e).map strip := by
  simp only [Silmaril.X86.MemoryModel.OpAx.threadUnits, List.map_flatten, List.flatMap]
  congr 1
  rw [map_mapIdx']
  exact mapIdx_const fun k _ => evUnits_strip i k _

theorem actUnits_strip (i p : Nat) (a : XAct) :
    ((actUnits i p a).filter realU).map strip = ((actUnits i 0 a).filter realU).map strip := by
  unfold actUnits
  split <;> simp [List.filter_cons, strip, realU, realE, Ev.isFence]
  split <;> rfl

theorem actUnits_length (i p : Nat) (a : XAct) : (actUnits i p a).length = (actUnits i 0 a).length := by
  unfold actUnits
  split <;> rfl

theorem threadUnitsL_strip (i : Nat) :
    ∀ (p : Nat) (as : List XAct),
      ((Silmaril.X86.MemoryModel.Litmus.threadUnits i p as).filter realU).map strip =
        as.flatMap fun a => ((actUnits i 0 a).filter realU).map strip
  | _, [] => rfl
  | p, a :: as => by
    simp only [Silmaril.X86.MemoryModel.Litmus.threadUnits, List.filter_append, List.map_append,
      List.flatMap_cons]
    rw [actUnits_strip, threadUnitsL_strip]

/-- **One action, both encodings.** -/
theorem act_strip (i : Nat) (a : XAct) (h : ActOk a) :
    (actX i a).flatMap (fun e => (evUnits i 0 e).map strip) =
      ((actUnits i 0 a).filter realU).map strip := by
  obtain ⟨hl, hs, hr, hw, -⟩ := h
  cases a with
  | mk ev fl rd wr =>
    cases ev with
    | mk kind addr size locked =>
      cases kind with
      | load =>
        simp only [MemEvent.Kind.reads, forall_const] at hl hr
        subst hl hr
        simp [actX, actUnits, evUnits, strip, realU, realE, Ev.isFence]
      | store =>
        simp only [MemEvent.Kind.writes, forall_const] at hs hw
        subst hs hw
        simp [actX, actUnits, evUnits, strip, realU, realE, Ev.isFence]
      | rmw =>
        simp only [MemEvent.Kind.reads, MemEvent.Kind.writes, forall_const] at hr hw
        subst hr
        cases locked <;> simp [actX, actUnits, evUnits, strip, realU, realE, Ev.isFence, hw]
      | fence k =>
        cases k <;> simp [actX, actUnits, evUnits, strip, realU, realE, Ev.isFence]

/-- **The store-buffer machine units are the litmus units without `lfence`/`sfence`**, forgetting
positions. -/
theorem progUnits_strip {trs : List XTrace} (h : TracesOk trs) :
    (progUnits (trs.mapIdx traceX)).map strip = ((accUnits trs).filter realU).map strip := by
  simp only [progUnits, accUnits, List.map_flatten, List.filter_flatten, List.mapIdx_mapIdx,
    map_mapIdx']
  congr 1
  apply mapIdx_congr
  intro i hi
  simp only [Function.comp, threadUnitsK_strip, traceX, List.flatMap_assoc, threadUnitsL_strip]
  apply List.flatMap_congr
  intro a ha
  exact act_strip i a (h _ (List.getElem_mem hi) a ha)

/-! ## Positions -/

/-- The units of one thread are in increasing position order. -/
def PosOrd (l : List (Ev × List Byte)) : Prop :=
  l.Pairwise fun u v => u.1.tid = v.1.tid → u.1.pos < v.1.pos

/-- Consecutive positions of one thread are adjacent in the list. -/
def Consec (l : List (Ev × List Byte)) : Prop :=
  ∀ a b (ha : a < l.length) (hb : b < l.length), l[a].1.tid = l[b].1.tid →
    l[b].1.pos = l[a].1.pos + 1 → b = a + 1

/-- A locked read is followed in the list by the next position of its thread. -/
def RmwNext (l : List (Ev × List Byte)) : Prop :=
  ∀ k (hk : k < l.length), (l[k].1.isR && l[k].1.locked) = true →
    ∃ hk1 : k + 1 < l.length, l[k + 1].1.tid = l[k].1.tid ∧ l[k + 1].1.pos = l[k].1.pos + 1

/-- Blocks of pairwise different threads. -/
def TidDisj (L : List (List (Ev × List Byte))) : Prop :=
  L.Pairwise fun l₁ l₂ => ∀ u ∈ l₁, ∀ v ∈ l₂, u.1.tid ≠ v.1.tid

theorem posOrd_flatten {L : List (List (Ev × List Byte))} (h : ∀ l ∈ L, PosOrd l)
    (hd : TidDisj L) : PosOrd L.flatten :=
  List.pairwise_flatten.2 ⟨h, hd.imp fun h u hu v hv ht => absurd ht (h u hu v hv)⟩

theorem consec_append {l₁ l₂ : List (Ev × List Byte)} (h₁ : Consec l₁) (h₂ : Consec l₂)
    (hd : ∀ u ∈ l₁, ∀ v ∈ l₂, u.1.tid ≠ v.1.tid) : Consec (l₁ ++ l₂) := by
  intro a b ha hb ht hp
  simp only [List.length_append] at ha hb
  by_cases ha1 : a < l₁.length <;> by_cases hb1 : b < l₁.length
  · rw [List.getElem_append_left ha1, List.getElem_append_left hb1] at ht hp
    exact h₁ a b ha1 hb1 ht hp
  · rw [List.getElem_append_left ha1, List.getElem_append_right (by omega)] at ht
    exact absurd ht (hd _ (List.getElem_mem _) _ (List.getElem_mem _))
  · rw [List.getElem_append_right (by omega), List.getElem_append_left hb1] at ht
    exact absurd ht.symm (hd _ (List.getElem_mem _) _ (List.getElem_mem _))
  · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)] at ht hp
    have := h₂ (a - l₁.length) (b - l₁.length) (by omega) (by omega) ht hp
    omega

theorem consec_flatten : ∀ {L : List (List (Ev × List Byte))}, (∀ l ∈ L, Consec l) →
    TidDisj L → Consec L.flatten
  | [], _, _ => by intro a b ha; simp at ha
  | l :: L, h, hd => by
    rw [List.flatten_cons]
    rw [TidDisj, List.pairwise_cons] at hd
    refine consec_append (h l (List.mem_cons_self ..))
      (consec_flatten (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) hd.2) ?_
    intro u hu v hv
    obtain ⟨l', hl', hv'⟩ := List.mem_flatten.1 hv
    exact hd.1 l' hl' u hu v hv'

theorem rmwNext_append {l₁ l₂ : List (Ev × List Byte)} (h₁ : RmwNext l₁) (h₂ : RmwNext l₂) :
    RmwNext (l₁ ++ l₂) := by
  intro k hk hr
  simp only [List.length_append] at hk
  by_cases hk1 : k < l₁.length
  · rw [List.getElem_append_left hk1] at hr
    obtain ⟨h1, h2, h3⟩ := h₁ k hk1 hr
    refine ⟨by simp; omega, ?_⟩
    rw [List.getElem_append_left hk1, List.getElem_append_left h1]
    exact ⟨h2, h3⟩
  · rw [List.getElem_append_right (by omega)] at hr
    obtain ⟨h1, h2, h3⟩ := h₂ (k - l₁.length) (by omega) hr
    refine ⟨by simp; omega, ?_⟩
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    have : k + 1 - l₁.length = k - l₁.length + 1 := by omega
    simp only [this]
    exact ⟨h2, h3⟩

theorem rmwNext_flatten : ∀ {L : List (List (Ev × List Byte))}, (∀ l ∈ L, RmwNext l) →
    RmwNext L.flatten
  | [], _ => by intro k hk; simp at hk
  | l :: L, h => by
    rw [List.flatten_cons]
    exact rmwNext_append (h l (List.mem_cons_self ..))
      (rmwNext_flatten fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem tidDisj_mapIdx {α : Type} {l : List α} {f : Nat → α → List (Ev × List Byte)}
    (h : ∀ i a, ∀ u ∈ f i a, u.1.tid = i) : TidDisj (l.mapIdx f) := by
  rw [TidDisj, List.pairwise_iff_getElem]
  intro i j hi hj hij u hu v hv
  simp only [List.getElem_mapIdx] at hu hv
  rw [h _ _ u hu, h _ _ v hv]
  omega

/-! ### The litmus units -/

theorem actUnits_get (i p : Nat) (a : XAct) (k : Nat) (hk : k < (actUnits i p a).length) :
    (actUnits i p a)[k].1.tid = i ∧ (actUnits i p a)[k].1.pos = p + k := by
  unfold actUnits at hk ⊢
  split at hk <;> simp only [List.length_cons, List.length_nil] at hk
  all_goals rcases k with _ | _ | k
  all_goals first | omega | simp_all

theorem threadUnitsL_get (i : Nat) :
    ∀ (p : Nat) (as : List XAct) (k : Nat)
      (hk : k < (Silmaril.X86.MemoryModel.Litmus.threadUnits i p as).length),
      (Silmaril.X86.MemoryModel.Litmus.threadUnits i p as)[k].1.tid = i ∧
        (Silmaril.X86.MemoryModel.Litmus.threadUnits i p as)[k].1.pos = p + k
  | _, [], k, hk => by simp [Silmaril.X86.MemoryModel.Litmus.threadUnits] at hk
  | p, a :: as, k, hk => by
    have hk' : k < (actUnits i p a).length +
        (Silmaril.X86.MemoryModel.Litmus.threadUnits i (p + (actUnits i p a).length) as).length := by
      simpa [Silmaril.X86.MemoryModel.Litmus.threadUnits] using hk
    simp only [Silmaril.X86.MemoryModel.Litmus.threadUnits]
    by_cases h1 : k < (actUnits i p a).length
    · rw [List.getElem_append_left h1]
      exact actUnits_get i p a k h1
    · rw [List.getElem_append_right (by omega)]
      obtain ⟨h2, h3⟩ := threadUnitsL_get i (p + (actUnits i p a).length) as
        (k - (actUnits i p a).length) (by omega)
      exact ⟨h2, by rw [h3]; omega⟩

theorem threadUnitsL_tid (i p : Nat) (as : List XAct) :
    ∀ u ∈ Silmaril.X86.MemoryModel.Litmus.threadUnits i p as, u.1.tid = i := by
  intro u hu
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
  exact (threadUnitsL_get i p as k hk).1

theorem posOrd_threadUnitsL (i p : Nat) (as : List XAct) :
    PosOrd (Silmaril.X86.MemoryModel.Litmus.threadUnits i p as) := by
  rw [PosOrd, List.pairwise_iff_getElem]
  intro a b ha hb hab _
  rw [(threadUnitsL_get i p as a ha).2, (threadUnitsL_get i p as b hb).2]
  omega

theorem consec_threadUnitsL (i p : Nat) (as : List XAct) :
    Consec (Silmaril.X86.MemoryModel.Litmus.threadUnits i p as) := by
  intro a b ha hb _ hp
  rw [(threadUnitsL_get i p as a ha).2, (threadUnitsL_get i p as b hb).2] at hp
  omega

theorem posOrd_acc (trs : List XTrace) : PosOrd (accUnits trs) :=
  posOrd_flatten
    (by
      intro l hl
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      simp only [List.getElem_mapIdx]
      exact posOrd_threadUnitsL _ _ _)
    (tidDisj_mapIdx fun i tr => threadUnitsL_tid i 0 tr.acts)

theorem consec_acc (trs : List XTrace) : Consec (accUnits trs) :=
  consec_flatten
    (by
      intro l hl
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      simp only [List.getElem_mapIdx]
      exact consec_threadUnitsL _ _ _)
    (tidDisj_mapIdx fun i tr => threadUnitsL_tid i 0 tr.acts)

/-! ### The store-buffer machine units -/

theorem evUnits_mem (i k : Nat) (e : XEvent Nat) :
    ∀ u ∈ evUnits i k e, u.1.tid = i ∧ 2 * k ≤ u.1.pos ∧ u.1.pos ≤ 2 * k + 1 := by
  cases e <;> simp [evUnits]

theorem posOrd_evUnits (i k : Nat) (e : XEvent Nat) : PosOrd (evUnits i k e) := by
  cases e <;> simp [evUnits, PosOrd]

theorem rmwNext_evUnits (i k : Nat) (e : XEvent Nat) : RmwNext (evUnits i k e) := by
  intro j hj h
  cases e <;> simp only [evUnits, List.length_cons, List.length_nil] at hj
  all_goals rcases j with _ | _ | j
  all_goals first | omega | simp_all [evUnits, Ev.isR]

theorem threadUnitsK_tid (i : Nat) (es : List (XEvent Nat)) :
    ∀ u ∈ Silmaril.X86.MemoryModel.OpAx.threadUnits i es, u.1.tid = i := by
  intro u hu
  simp only [Silmaril.X86.MemoryModel.OpAx.threadUnits, List.mem_flatten] at hu
  obtain ⟨l, hl, hu⟩ := hu
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  simp only [List.getElem_mapIdx] at hu
  exact (evUnits_mem i k _ u hu).1

theorem posOrd_threadUnitsK (i : Nat) (es : List (XEvent Nat)) :
    PosOrd (Silmaril.X86.MemoryModel.OpAx.threadUnits i es) := by
  refine List.pairwise_flatten.2 ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    simp only [List.getElem_mapIdx]
    exact posOrd_evUnits _ _ _
  · rw [List.pairwise_iff_getElem]
    intro a b ha hb hab u hu v hv _
    simp only [List.getElem_mapIdx] at hu hv
    have h1 := evUnits_mem i a _ u hu
    have h2 := evUnits_mem i b _ v hv
    omega

theorem rmwNext_threadUnitsK (i : Nat) (es : List (XEvent Nat)) :
    RmwNext (Silmaril.X86.MemoryModel.OpAx.threadUnits i es) := by
  apply rmwNext_flatten
  intro l hl
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  simp only [List.getElem_mapIdx]
  exact rmwNext_evUnits _ _ _

theorem posOrd_prog (P : List (List (XEvent Nat))) : PosOrd (progUnits P) :=
  posOrd_flatten
    (by
      intro l hl
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      simp only [List.getElem_mapIdx]
      exact posOrd_threadUnitsK _ _)
    (tidDisj_mapIdx fun i es => threadUnitsK_tid i es)

theorem rmwNext_prog (P : List (List (XEvent Nat))) : RmwNext (progUnits P) := by
  apply rmwNext_flatten
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  simp only [List.getElem_mapIdx]
  exact rmwNext_threadUnitsK _ _

/-- In a `PosOrd` list, two units of one thread compare by position as by index. -/
theorem PosOrd.lt_iff {l : List (Ev × List Byte)} (h : PosOrd l) {a b : Nat} (ha : a < l.length)
    (hb : b < l.length) (ht : l[a].1.tid = l[b].1.tid) : l[a].1.pos < l[b].1.pos ↔ a < b := by
  rw [PosOrd, List.pairwise_iff_getElem] at h
  constructor
  · intro hp
    rcases Nat.lt_trichotomy a b with hab | rfl | hab
    · exact hab
    · omega
    · have := h b a hb ha hab ht.symm; omega
  · intro hab; exact h a b ha hb hab ht

theorem PosOrd.eq {l : List (Ev × List Byte)} (h : PosOrd l) {a b : Nat} (ha : a < l.length)
    (hb : b < l.length) (ht : l[a].1.tid = l[b].1.tid) (hp : l[a].1.pos = l[b].1.pos) : a = b := by
  have h1 := (h.lt_iff ha hb ht).not
  have h2 := (h.lt_iff hb ha ht.symm).not
  omega

theorem PosOrd.nodup {l : List (Ev × List Byte)} (h : PosOrd l) : l.Nodup :=
  h.imp fun {u v} h he => by subst he; have := h rfl; omega

end Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun
