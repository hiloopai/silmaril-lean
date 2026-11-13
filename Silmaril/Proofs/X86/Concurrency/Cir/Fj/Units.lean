module

public import Silmaril.X86.Concurrency.Cir.Fj.Defs
public import Silmaril.X86.MemoryModel.Xl.Defs

/-!
# Fork-join CIR: where the units of a choice of traces come from

Generic facts about the `units` (any number of threads):

* `units_src`: every unit, after tear splitting, comes from one action `a` of one thread `i`
  (`UnitOf i a`): same thread, `locked` bit, bytes inside the action's footprint, the bytes it
  writes are the action's, the bytes it expects are the action's;
* `units_exists_r`, `units_exists_w`: conversely, every byte of a reading (writing) action has a
  read (write) unit covering it;
* `threadUnits_pos_append`: the units of a later part of a thread's action list have later
  program positions.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Fj

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace actUnits threadUnits accUnits units
  splitUnit tearAcc)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec Act)
open Silmaril.X86.MemEvent (Kind)

/-- **Unit `q` comes from action `a` of thread `i`.** -/
structure UnitOf (i : Nat) (a : XAct) (q : Ev × List Byte) : Prop where
  tid : q.1.tid = i
  locked : q.1.isM = true → q.1.locked = a.ev.locked
  cov : ∀ y, q.1.covers y = true → a.ev.addr ≤ y ∧ y < a.ev.addr + a.ev.size
  wr : q.1.isW = true → ∀ y, q.1.covers y = true → q.1.byte y = a.wr.getD (y - a.ev.addr) 0
  rd : q.1.isR = true → ∀ y, q.1.covers y = true →
    q.2.getD (y - q.1.addr) 0 = a.rd.getD (y - a.ev.addr) 0
  kR : q.1.isR = true → a.ev.kind = .load ∨ a.ev.kind = .rmw
  kW : q.1.isW = true → a.ev.kind = .store ∨ a.ev.kind = .rmw

theorem covers_iff (e : Ev) (y : Nat) : e.covers y = true ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.covers]

theorem actUnits_src {i p : Nat} {a : XAct} {q : Ev × List Byte} (h : q ∈ actUnits i p a) :
    UnitOf i a q ∧ p ≤ q.1.pos ∧ q.1.pos < p + (actUnits i p a).length := by
  simp only [actUnits] at h ⊢
  rcases hk : a.ev.kind with _ | _ | _ | k <;> rw [hk] at h <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  · subst h
    refine ⟨⟨rfl, fun _ => rfl, fun y hy => (covers_iff _ _).mp hy, fun h => by simp [Ev.isW] at h,
      fun _ y _ => rfl, fun _ => .inl hk, fun h => by simp [Ev.isW] at h⟩, le_refl _, by simp⟩
  · subst h
    refine ⟨⟨rfl, fun _ => rfl, fun y hy => (covers_iff _ _).mp hy, fun _ y _ => rfl,
      fun h => by simp [Ev.isR] at h, fun h => by simp [Ev.isR] at h, fun _ => .inl hk⟩,
      le_refl _, by simp⟩
  · rcases h with rfl | rfl
    · refine ⟨⟨rfl, fun _ => rfl, fun y hy => (covers_iff _ _).mp hy,
        fun h => by simp [Ev.isW] at h,
        fun _ y _ => rfl, fun _ => .inr hk, fun h => by simp [Ev.isW] at h⟩, le_refl _, by simp⟩
    · refine ⟨⟨rfl, fun _ => rfl, fun y hy => (covers_iff _ _).mp hy, fun _ y _ => rfl,
        fun h => by simp [Ev.isR] at h, fun h => by simp [Ev.isR] at h, fun _ => .inr hk⟩,
        by simp, by simp⟩
  · subst h
    refine ⟨⟨rfl, fun h => by simp [Ev.isM, Ev.isR, Ev.isW] at h,
      fun y hy => by simp [Ev.covers] at hy, fun h => by simp [Ev.isW] at h,
      fun h => by simp [Ev.isR] at h, fun h => by simp [Ev.isR] at h,
      fun h => by simp [Ev.isW] at h⟩, le_refl _, by simp⟩

theorem threadUnits_src {i : Nat} : ∀ {p : Nat} {as : List XAct} {q : Ev × List Byte},
    q ∈ threadUnits i p as →
      (∃ a ∈ as, UnitOf i a q) ∧ p ≤ q.1.pos ∧ q.1.pos < p + (threadUnits i p as).length
  | _, [], _, h => by simp [threadUnits] at h
  | p, a :: as, q, h => by
    simp only [threadUnits, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨h1, h2, h3⟩ := actUnits_src h
      exact ⟨⟨a, List.mem_cons_self, h1⟩, h2, by simp; omega⟩
    · obtain ⟨⟨b, hb, h1⟩, h2, h3⟩ := threadUnits_src h
      exact ⟨⟨b, List.mem_cons_of_mem _ hb, h1⟩, by omega, by simp; omega⟩

theorem threadUnits_append (i : Nat) : ∀ (p : Nat) (l l' : List XAct),
    threadUnits i p (l ++ l') =
      threadUnits i p l ++ threadUnits i (p + (threadUnits i p l).length) l'
  | p, [], l' => by simp [threadUnits]
  | p, a :: l, l' => by
    simp only [List.cons_append, threadUnits, threadUnits_append i _ l l', List.append_assoc,
      List.length_append]
    congr 3
    omega

/-- **Later parts of the action list have later positions.** -/
theorem threadUnits_pos_append {i p : Nat} {l l' : List XAct} {q : Ev × List Byte}
    (h : q ∈ threadUnits i p (l ++ l')) :
    ((∃ a ∈ l, UnitOf i a q) ∧ q.1.pos < p + (threadUnits i p l).length) ∨
      ((∃ a ∈ l', UnitOf i a q) ∧ p + (threadUnits i p l).length ≤ q.1.pos) := by
  rw [threadUnits_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨h1, -, h3⟩ := threadUnits_src h; exact .inl ⟨h1, h3⟩
  · obtain ⟨h1, h2, -⟩ := threadUnits_src h; exact .inr ⟨h1, h2⟩

theorem threadUnits_exists {i : Nat} {P : Ev × List Byte → Prop} {a : XAct}
    (hP : ∀ p, ∃ u ∈ actUnits i p a, P u) : ∀ {p : Nat} {as : List XAct}, a ∈ as →
      ∃ u ∈ threadUnits i p as, P u
  | _, [], h => by simp at h
  | p, b :: as, h => by
    simp only [threadUnits, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · obtain ⟨u, hu, hPu⟩ := hP p; exact ⟨u, .inl hu, hPu⟩
    · obtain ⟨u, hu, hPu⟩ := threadUnits_exists hP h; exact ⟨u, .inr hu, hPu⟩

/-- A reading action has an unsplit read unit covering each of its bytes. -/
theorem actUnits_exists_r {i : Nat} {a : XAct} (hk : a.ev.kind = .load ∨ a.ev.kind = .rmw)
    {y : Nat} (hy : a.ev.addr ≤ y ∧ y < a.ev.addr + a.ev.size) (p : Nat) :
    ∃ u ∈ actUnits i p a, u.1.isR = true ∧ u.1.covers y = true := by
  simp only [actUnits]
  rcases hk with hk | hk <;> rw [hk] <;> simp [Ev.isR, Ev.covers, hy.1, hy.2]

/-- A writing action has an unsplit write unit covering each of its bytes. -/
theorem actUnits_exists_w {i : Nat} {a : XAct} (hk : a.ev.kind = .store ∨ a.ev.kind = .rmw)
    {y : Nat} (hy : a.ev.addr ≤ y ∧ y < a.ev.addr + a.ev.size) (p : Nat) :
    ∃ u ∈ actUnits i p a, u.1.isW = true ∧ u.1.covers y = true := by
  simp only [actUnits]
  rcases hk with hk | hk <;> rw [hk] <;> simp [Ev.isW, Ev.covers, hy.1, hy.2]

/-! ## Tear splitting -/

theorem piece_basic {u q : Ev × List Byte} (h : q ∈ splitUnit u) :
    q.1.pos = u.1.pos ∧ q.1.isR = u.1.isR ∧ q.1.isW = u.1.isW := by
  simp only [splitUnit, List.mem_map] at h
  obtain ⟨y0, -, rfl⟩ := h
  simp [Ev.isR, Ev.isW]

theorem piece_src {i : Nat} {a : XAct} {u q : Ev × List Byte} (hu : UnitOf i a u)
    (h : q ∈ splitUnit u) :
    UnitOf i a q ∧ q.1.pos = u.1.pos ∧ q.1.isR = u.1.isR ∧ q.1.isW = u.1.isW := by
  simp only [splitUnit, List.mem_map] at h
  obtain ⟨y0, hy0, rfl⟩ := h
  obtain ⟨hy1, hy2⟩ := List.mem_range'_1.mp hy0
  have hc0 : u.1.covers y0 = true := (covers_iff _ _).mpr ⟨hy1, hy2⟩
  refine ⟨⟨hu.tid, fun hM => hu.locked (by simpa [Ev.isM, Ev.isR, Ev.isW] using hM),
    fun y hy => ?_, fun hW y hy => ?_, fun hR y hy => ?_,
    fun hR => hu.kR (by simpa [Ev.isR] using hR),
    fun hW => hu.kW (by simpa [Ev.isW] using hW)⟩, rfl, by simp [Ev.isR], by simp [Ev.isW]⟩
  · have : y = y0 := by simp [Ev.covers] at hy; omega
    subst this; exact hu.cov y hc0
  · have : y = y0 := by simp [Ev.covers] at hy; omega
    subst this
    have hW' : u.1.isW = true := by simpa [Ev.isW] using hW
    have hact : (u.1.act == .write) = true := by simpa [Ev.isW] using hW'
    rw [← hu.wr hW' y hc0]
    simp [Ev.byte, hact]
  · have : y = y0 := by simp [Ev.covers] at hy; omega
    subst this
    have hR' : u.1.isR = true := by simpa [Ev.isR] using hR
    rw [← hu.rd hR' y hc0]
    simp [hR', List.getD]

theorem mem_accUnits {trs : List XTrace} {u : Ev × List Byte} :
    u ∈ accUnits trs ↔ ∃ i tr, trs[i]? = some tr ∧ u ∈ threadUnits i 0 tr.acts := by
  simp only [accUnits, List.mem_flatten, List.mem_mapIdx]
  constructor
  · rintro ⟨l, ⟨i, hi, rfl⟩, hu⟩
    exact ⟨i, trs[i], by simp [hi], hu⟩
  · rintro ⟨i, tr, htr, hu⟩
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp htr
    exact ⟨_, ⟨i, hi, rfl⟩, hu⟩

theorem mem_units {trs : List XTrace} {q : Ev × List Byte} :
    q ∈ units trs ↔
      ∃ u ∈ accUnits trs, q ∈ (if tearAcc (accUnits trs) u.1 then splitUnit u else [u]) := by
  simp [units, List.mem_flatMap]

/-- **Provenance**: a unit comes from a unit of one thread's action list. -/
theorem units_src {trs : List XTrace} {q : Ev × List Byte} (h : q ∈ units trs) :
    ∃ i tr, trs[i]? = some tr ∧ ∃ u ∈ threadUnits i 0 tr.acts,
      (∀ a, UnitOf i a u → UnitOf i a q) ∧ q.1.pos = u.1.pos ∧ q.1.isR = u.1.isR ∧
        q.1.isW = u.1.isW := by
  obtain ⟨u, hu, hq⟩ := mem_units.mp h
  obtain ⟨i, tr, htr, hu'⟩ := mem_accUnits.mp hu
  refine ⟨i, tr, htr, u, hu', ?_⟩
  split at hq
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    have hp : _ ∈ splitUnit u := List.mem_map.mpr ⟨y, hy, rfl⟩
    exact ⟨fun a ha => (piece_src ha hp).1, rfl, by simp [Ev.isR], by simp [Ev.isW]⟩
  · simp only [List.mem_singleton] at hq; subst hq
    exact ⟨fun _ h => h, rfl, rfl, rfl⟩

/-- **Existence**: a unit of a thread's action list covering `y` has a part in `units`. -/
theorem units_exists {trs : List XTrace} {i : Nat} {tr : XTrace} (htr : trs[i]? = some tr)
    {u : Ev × List Byte} (hu : u ∈ threadUnits i 0 tr.acts) {y : Nat} (hy : u.1.covers y = true) :
    ∃ q ∈ units trs, (∀ a, UnitOf i a u → UnitOf i a q) ∧ q.1.pos = u.1.pos ∧
      q.1.isR = u.1.isR ∧ q.1.isW = u.1.isW ∧ q.1.covers y = true := by
  have hacc : u ∈ accUnits trs := mem_accUnits.mpr ⟨i, tr, htr, hu⟩
  by_cases ht : tearAcc (accUnits trs) u.1 = true
  · obtain ⟨hy1, hy2⟩ := (covers_iff _ _).mp hy
    have hmem : y ∈ u.1.bytes := List.mem_range'_1.mpr ⟨hy1, hy2⟩
    obtain ⟨q, hp, hqy⟩ : ∃ q ∈ splitUnit u, q.1.covers y = true :=
      ⟨_, List.mem_map.mpr ⟨y, hmem, rfl⟩, by simp [Ev.covers]⟩
    obtain ⟨h2, h3, h4⟩ := piece_basic hp
    exact ⟨q, mem_units.mpr ⟨u, hacc, by simp [ht, hp]⟩, fun a ha => (piece_src ha hp).1,
      h2, h3, h4, hqy⟩
  · exact ⟨u, mem_units.mpr ⟨u, hacc, by simp [ht]⟩, fun _ h => h, rfl, rfl, rfl, hy⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Fj
