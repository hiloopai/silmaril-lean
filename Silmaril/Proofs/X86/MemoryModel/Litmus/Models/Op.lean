module

public import Silmaril.Proofs.X86.MemoryModel.Litmus.Models.Lists

/-!
# Litmus models: the operational TSO enumerator is exact

`opOut_spec`: when `Test.opOut` succeeds, its outcomes are exactly the outcomes of the final
states of `OpReach` (one trace per thread, run on `Tso.XStep`/`Tso.XFlush` to completion with
every buffer drained). The pieces:

* the association-list memory stands for `Tso.Mem` (`cget_cwrite`, `cget_initCMem`);
* one concrete successor is one abstract step (`fire_sound`, `flush_sound`), and every abstract
  step from a configuration's state is matched by a concrete successor (`fire_complete`,
  `flush_complete`);
* soundness (`reach_sound`): along a concrete path, any choice of one live candidate per thread
  comes from a choice at the start, by an abstract run;
* completeness (`reach_complete`): an abstract run from a choice of traces is followed by a
  concrete path that keeps the chosen traces live;
* `collect_spec`: the search visits every reachable configuration.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush)

/-! ## Configurations -/

theorem ceq_iff (c d : CCfg) : c.ceq d = true ↔ c = d := by
  cases c; cases d
  simp only [CCfg.ceq, Bool.and_eq_true, beq_iff_eq, CCfg.mk.injEq]
  tauto

/-! ## Association-list memory -/

theorem lookup_cons' {γ : Type} (k y : Nat) (v : γ) (l : List (Nat × γ)) :
    ((k, v) :: l).lookup y = if y = k then some v else l.lookup y := by
  by_cases h : y = k
  · subst h; simp [List.lookup]
  · have : (y == k) = false := by simpa using h
    simp [List.lookup, this, h]

theorem lookup_append {γ : Type} (l l' : List (Nat × γ)) (y : Nat) :
    (l ++ l').lookup y = (l.lookup y).or (l'.lookup y) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    rw [List.cons_append, lookup_cons', lookup_cons', ih]
    by_cases h : y = k <;> simp [h]

theorem lookup_map_upd (m : CMem) (x y : Nat) (b : Byte) :
    (m.map fun p => if p.1 == x then (x, b) else p).lookup y =
      if y = x then (if m.any (fun p => p.1 == x) then some b else none) else m.lookup y := by
  induction m with
  | nil => simp
  | cons p m ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = x
    · subst hk
      simp only [List.map_cons, beq_self_eq_true, ite_true, lookup_cons', ih, List.any_cons,
        Bool.true_or]
      by_cases hy : y = k <;> simp [hy]
    · have hk' : (k == x) = false := by simpa using hk
      simp only [List.map_cons, hk', Bool.false_eq_true, ite_false, lookup_cons', ih,
        List.any_cons, Bool.false_or]
      by_cases hy : y = k
      · subst hy; simp [hk]
      · simp [hy]

theorem lookup_none_of_not_any (m : CMem) (x : Nat) (h : m.any (fun p => p.1 == x) = false) :
    m.lookup x = none := by
  induction m with
  | nil => rfl
  | cons p m ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    have : x ≠ k := fun e => h.1 e.symm
    rw [lookup_cons', ih h.2]; simp [this]

theorem cget_cset (m : CMem) (x : Nat) (b : Byte) (y : Nat) :
    cget (cset m x b) y = if y = x then some b else cget m y := by
  unfold cset cget
  split
  · rename_i h
    rw [lookup_map_upd, h]
    simp
  · rename_i h
    rw [lookup_append]
    by_cases hy : y = x
    · subst hy
      simp only [Bool.not_eq_true] at h
      simp [lookup_none_of_not_any m y h]
    · simp [lookup_cons', hy]

theorem cget_cwrite (bs : List Byte) : ∀ (m : CMem) (a y : Nat),
    cget (cwrite m a bs) y = (Silmaril.X86.MemoryModel.Tso.entryByte a bs y).or (cget m y) := by
  induction bs with
  | nil => intro m a y; simp [cwrite, Silmaril.X86.MemoryModel.Tso.entryByte]
  | cons b bs ih =>
    intro m a y
    simp only [cwrite, ih, cget_cset, Silmaril.X86.MemoryModel.Tso.entryByte]
    by_cases h1 : y = a
    · subst h1; simp [show ¬ y + 1 ≤ y by omega]
    · by_cases h2 : a ≤ y
      · have h3 : a + 1 ≤ y := by omega
        have h4 : y - a = (y - (a + 1)) + 1 := by omega
        simp [h1, h2, h3, h4]
      · have h3 : ¬ a + 1 ≤ y := by omega
        simp [h1, h2, h3]

theorem lookup_range_map (addr : Nat) (v : Nat → Byte) (n y : Nat) :
    ((List.range n).map fun j => (addr + j, v j)).lookup y =
      if addr ≤ y ∧ y < addr + n then some (v (y - addr)) else none := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, lookup_append, ih]
    by_cases h : addr ≤ y ∧ y < addr + n
    · simp [h, show addr ≤ y ∧ y < addr + (n + 1) from ⟨h.1, by omega⟩]
    · by_cases h' : y = addr + n
      · subst h'; simp
      · have : ¬ (addr ≤ y ∧ y < addr + (n + 1)) := by omega
        simp [h, this, lookup_cons', h']

theorem cget_initCMem (locs : List Loc) (y : Nat) : cget (initCMem locs) y = initByte locs y := by
  unfold cget initCMem initByte
  induction locs with
  | nil => simp
  | cons l locs ih =>
    simp only [List.flatMap_cons, lookup_append, lookup_range_map, ih, List.find?_cons]
    by_cases h : l.addr ≤ y ∧ y < l.addr + l.size
    · simp [h]
    · have : (decide (l.addr ≤ y) && decide (y < l.addr + l.size)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp [h, this]

/-! ## Buffers -/

theorem getD_lt {γ : Type} (l : List γ) (i : Nat) (d : γ) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ge {γ : Type} (l : List γ) (i : Nat) (d : γ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_update {γ : Type} (l : List γ) (k : Nat) (v d : γ) (hk : k < l.length) :
    (fun j => (l.set k v).getD j d) = Function.update (fun j => l.getD j d) k v := by
  funext j
  by_cases h : j = k
  · subst h; simp [hk]
  · simp [Function.update, h, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem xs_eq {c : CCfg} {s : XState Nat} (hm : cget c.mem = s.memory)
    (hb : (fun k => c.bufs.getD k []) = s.buffer) : c.xs = s := by
  cases s; simp only [CCfg.xs] at *; subst hm; subst hb; rfl

/-! ## One step -/

theorem fire_sound {c c' : CCfg} {e : XEvent Nat} (h : c.fire e = some c') :
    XStep c.xs e c'.xs ∧ c'.cand = c.cand ∧ c'.bufs.length = c.bufs.length := by
  cases e with
  | load k a bs =>
    simp only [CCfg.fire] at h
    split at h
    · rename_i hc; cases h; exact ⟨XStep.load _ _ _ _ hc.2, rfl, rfl⟩
    · cases h
  | store k a bs =>
    simp only [CCfg.fire] at h
    split at h
    · rename_i hk
      cases h
      refine ⟨?_, rfl, by simp⟩
      have : ({ c with bufs := c.bufs.set k (c.bufs.getD k [] ++ [(a, bs)]) } : CCfg).xs =
          Silmaril.X86.MemoryModel.Tso.enqueue c.xs k a bs := by
        simp only [CCfg.xs, Silmaril.X86.MemoryModel.Tso.enqueue]
        rw [getD_set_update _ _ _ _ hk]
      rw [this]; exact XStep.store _ _ _ _
    · cases h
  | rmw k a old new =>
    simp only [CCfg.fire] at h
    split at h
    · rename_i hc
      obtain ⟨-, hemp, hrd, hlen⟩ := hc
      cases h
      refine ⟨?_, rfl, rfl⟩
      have : ({ c with mem := cwrite c.mem a new } : CCfg).xs =
          { c.xs with memory := Silmaril.X86.MemoryModel.Tso.writeMem c.xs.memory a new } := by
        simp only [CCfg.xs]
        congr 1; funext y; exact cget_cwrite _ _ _ _
      rw [this]; exact XStep.rmw _ _ _ _ _ hemp hrd hlen
    · cases h
  | fence k =>
    simp only [CCfg.fire] at h
    split at h
    · rename_i hc; cases h; exact ⟨XStep.fence _ _ hc.2, rfl, rfl⟩
    · cases h

theorem fire_complete {c : CCfg} {e : XEvent Nat} {s' : XState Nat} (h : XStep c.xs e s')
    (ht : e.thread < c.bufs.length) :
    ∃ c', c.fire e = some c' ∧ c'.xs = s' ∧ c'.cand = c.cand := by
  generalize hs : c.xs = s at h
  cases h with
  | load k a bs hv =>
    subst hs
    exact ⟨c, by simp [CCfg.fire, show k < c.bufs.length from ht, hv], rfl, rfl⟩
  | store k a bs =>
    subst hs
    have hk : k < c.bufs.length := ht
    refine ⟨{ c with bufs := c.bufs.set k (c.bufs.getD k [] ++ [(a, bs)]) },
      by simp [CCfg.fire, hk], ?_, rfl⟩
    simp only [CCfg.xs, Silmaril.X86.MemoryModel.Tso.enqueue]
    rw [getD_set_update _ _ _ _ hk]
  | rmw k a old new hemp hrd hlen =>
    subst hs
    have hk : k < c.bufs.length := ht
    have hemp' : c.bufs[k] = [] := by rw [← getD_lt _ _ [] hk]; exact hemp
    have hrd' : Silmaril.X86.MemoryModel.Tso.readMem (cget c.mem) a old.length = some old := hrd
    refine ⟨{ c with mem := cwrite c.mem a new }, by simp [CCfg.fire, hk, hemp', hrd', hlen],
      ?_, rfl⟩
    simp only [CCfg.xs]
    congr 1; funext y; exact cget_cwrite _ _ _ _
  | fence k hemp =>
    subst hs
    have hk : k < c.bufs.length := ht
    have hemp' : c.bufs[k] = [] := by rw [← getD_lt _ _ [] hk]; exact hemp
    exact ⟨c, by simp [CCfg.fire, hk, hemp'], rfl, rfl⟩

theorem flush_sound {c c' : CCfg} (h : c' ∈ c.flushes) :
    XFlush c.xs c'.xs ∧ c'.cand = c.cand ∧ c'.bufs.length = c.bufs.length := by
  simp only [CCfg.flushes, List.mem_filterMap, List.mem_range] at h
  obtain ⟨k, hk, hc⟩ := h
  split at hc
  · rename_i a bs rest hb
    cases hc
    refine ⟨?_, rfl, by simp⟩
    have : ({ c with mem := cwrite c.mem a bs, bufs := c.bufs.set k rest } : CCfg).xs =
        ⟨Silmaril.X86.MemoryModel.Tso.writeMem c.xs.memory a bs, Function.update c.xs.buffer k rest⟩ := by
      simp only [CCfg.xs]
      rw [getD_set_update _ _ _ _ hk]
      congr 1; funext y; exact cget_cwrite _ _ _ _
    rw [this]
    exact XFlush.head _ k a bs rest hb
  · cases hc

theorem flush_complete {c : CCfg} {s' : XState Nat} (h : XFlush c.xs s') :
    ∃ c' ∈ c.flushes, c'.xs = s' ∧ c'.cand = c.cand := by
  generalize hs : c.xs = s at h
  cases h with
  | head k a bs rest hb =>
    subst hs
    have hb' : c.bufs.getD k [] = (a, bs) :: rest := hb
    have hk : k < c.bufs.length := by
      by_contra hk
      rw [getD_ge _ _ _ (by omega)] at hb'
      cases hb'
    refine ⟨{ c with mem := cwrite c.mem a bs, bufs := c.bufs.set k rest }, ?_, ?_, rfl⟩
    · simp only [CCfg.flushes, List.mem_filterMap, List.mem_range]
      exact ⟨k, hk, by rw [hb']⟩
    · simp only [CCfg.xs]
      rw [getD_set_update _ _ _ _ hk]
      congr 1; funext y; exact cget_cwrite _ _ _ _

/-! ## Candidates -/

theorem mem_heads {cd : Cand} {e : XEvent Nat} : e ∈ heads cd ↔ ∃ p ∈ cd, p.1.head? = some e := by
  simp [heads, mem_uniq]

theorem mem_advance {cd : Cand} {e : XEvent Nat} {q : List (XEvent Nat) × RegObs} :
    q ∈ advance cd e ↔ (e :: q.1, q.2) ∈ cd := by
  simp only [advance, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hq⟩
    obtain ⟨l, o⟩ := p
    cases l with
    | nil => cases hq
    | cons e' r =>
      simp only at hq
      split at hq
      · rename_i he; subst he; cases hq; exact hp
      · cases hq
  · intro h
    exact ⟨_, h, by simp⟩

theorem mem_finished {cd : Cand} {o : RegObs} : o ∈ finished cd ↔ ([], o) ∈ cd := by
  simp only [finished, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hq⟩
    obtain ⟨l, o'⟩ := p
    cases l with
    | nil => simp at hq; subst hq; exact hp
    | cons => simp at hq
  · intro h; exact ⟨_, h, by simp⟩

theorem mem_events {c c' : CCfg} : c' ∈ c.events ↔ ∃ i < c.cand.length, ∃ e ∈ heads (c.cand.getD i []),
    ∃ c'', c.fire e = some c'' ∧ c' = { c'' with cand := c.cand.set i (advance (c.cand.getD i []) e) } := by
  simp only [CCfg.events, List.mem_flatMap, List.mem_range, List.mem_filterMap,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, hi, e, he, c'', hf, rfl⟩; exact ⟨i, hi, e, he, c'', hf, rfl⟩
  · rintro ⟨i, hi, e, he, c'', hf, rfl⟩; exact ⟨i, hi, e, he, c'', hf, rfl⟩

/-! ## Forall₂ helpers -/

theorem forall₂_set {γ δ : Type} {R : γ → δ → Prop} :
    ∀ {l : List γ} {m : List δ}, List.Forall₂ R l m → ∀ (i : Nat) {a : γ} {b : δ}, R a b →
      List.Forall₂ R (l.set i a) (m.set i b)
  | _, _, .nil, _, _, _, _ => by simp
  | _, _, .cons h t, 0, _, _, hab => by simpa using List.Forall₂.cons hab t
  | _, _, .cons h t, i + 1, _, _, hab => by simpa using List.Forall₂.cons h (forall₂_set t i hab)

theorem forall₂_get {γ δ : Type} {R : γ → δ → Prop} :
    ∀ {l : List γ} {m : List δ}, List.Forall₂ R l m → ∀ (i : Nat) (hl : i < l.length)
      (hm : i < m.length), R l[i] m[i]
  | _, _, .nil, _, hl, _ => by simp at hl
  | _, _, .cons h _, 0, _, _ => by simpa using h
  | _, _, .cons _ t, i + 1, hl, hm => by
    simpa using forall₂_get t i (by simpa using hl) (by simpa using hm)

/-! ## The invariant: events name existing threads -/

/-- Every event of every candidate names a thread with a buffer. -/
def Inv (c : CCfg) : Prop := ∀ cd ∈ c.cand, ∀ p ∈ cd, ∀ e ∈ p.1, e.thread < c.bufs.length

theorem inv_of_threadsOk {c : CCfg} (h : c.threadsOk = true) : Inv c := by
  intro cd hcd p hp e he
  simp only [CCfg.threadsOk, List.all_eq_true, decide_eq_true_eq] at h
  exact h cd hcd p hp e he

theorem inv_succ {c c' : CCfg} (hi : Inv c) (h : c' ∈ c.succ) : Inv c' := by
  simp only [CCfg.succ, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨-, hc, hl⟩ := flush_sound h
    intro cd hcd p hp e he
    rw [hc] at hcd; rw [hl]; exact hi cd hcd p hp e he
  · obtain ⟨i, hi', e, he, c'', hf, rfl⟩ := mem_events.mp h
    obtain ⟨-, hc, hl⟩ := fire_sound hf
    intro cd hcd p hp e' he'
    simp only at hcd ⊢
    rw [hl]
    rcases List.mem_or_eq_of_mem_set hcd with hcd | rfl
    · exact hi cd hcd p hp e' he'
    · have := mem_advance.mp hp
      have hmem : c.cand.getD i [] ∈ c.cand := by
        rw [getD_lt _ _ _ hi']; exact List.getElem_mem _
      exact hi _ hmem _ this e' (List.mem_cons_of_mem _ he')

theorem inv_reach {c c' : CCfg} (hi : Inv c)
    (h : Relation.ReflTransGen (fun x y => y ∈ CCfg.succ x) c c') : Inv c' := by
  induction h with
  | refl => exact hi
  | tail _ hs ih => exact inv_succ ih hs

/-! ## Soundness and completeness of the concrete search -/

/-- **Soundness**: along a concrete path, a choice of one live candidate per thread comes from a
choice of initial candidates, with the same final registers, by an abstract run. -/
theorem reach_sound {c0 c : CCfg} (h : Relation.ReflTransGen (fun x y => y ∈ CCfg.succ x) c0 c) :
    ∀ ro : List (List (XEvent Nat) × RegObs), List.Forall₂ (· ∈ ·) ro c.cand →
      ∃ ro0 : List (List (XEvent Nat) × RegObs), List.Forall₂ (· ∈ ·) ro0 c0.cand ∧
        ro0.map Prod.snd = ro.map Prod.snd ∧
        Relation.ReflTransGen AStep ⟨ro0.map Prod.fst, c0.xs⟩ ⟨ro.map Prod.fst, c.xs⟩ := by
  induction h with
  | refl => intro ro hro; exact ⟨ro, hro, rfl, .refl⟩
  | @tail c c' _ hs ih =>
    intro ro hro
    simp only [CCfg.succ, List.mem_append] at hs
    rcases hs with hs | hs
    · obtain ⟨hfl, hc, -⟩ := flush_sound hs
      rw [hc] at hro
      obtain ⟨ro0, h0, hsnd, hrun⟩ := ih ro hro
      exact ⟨ro0, h0, hsnd, hrun.tail (AStep.flush _ _ _ hfl)⟩
    · obtain ⟨i, hi, e, -, c'', hf, rfl⟩ := mem_events.mp hs
      obtain ⟨hst, hc, -⟩ := fire_sound hf
      have hlen : ro.length = c.cand.length := by
        have := hro.length_eq; simpa using this
      have hir : i < ro.length := by omega
      have hq : ro[i] ∈ advance (c.cand.getD i []) e := by
        have := forall₂_get hro i hir (by simpa using hi)
        simpa using this
      have hq' := mem_advance.mp hq
      set q := ro[i] with hqdef
      have hro' : List.Forall₂ (· ∈ ·) (ro.set i (e :: q.1, q.2)) c.cand := by
        have := forall₂_set hro i (b := c.cand.getD i []) hq'
        simp only at this
        rwa [List.set_set, getD_lt _ _ _ hi, List.set_getElem_self] at this
      obtain ⟨ro0, h0, hsnd, hrun⟩ := ih _ hro'
      refine ⟨ro0, h0, ?_, hrun.tail ?_⟩
      · rw [hsnd, List.map_set]
        have e2 : (e :: q.1, q.2).2 = (ro.map Prod.snd)[i]'(by simpa using hir) := by simp [hqdef]
        rw [e2, List.set_getElem_self]
      · have hstep := AStep.ev ((ro.set i (e :: q.1, q.2)).map Prod.fst) c.xs c''.xs i e q.1
          (by simp [hir]) hst
        have e1 : ((ro.set i (e :: q.1, q.2)).map Prod.fst).set i q.1 = ro.map Prod.fst := by
          rw [List.map_set, List.set_set, ← List.map_set]
          congr 1
          apply List.ext_getElem (by simp)
          intro j hj1 hj2
          by_cases hj : j = i
          · subst hj; simp [hqdef]
          · simp [Ne.symm hj]
        rw [e1] at hstep
        exact hstep

/-- **Completeness**: an abstract run from a choice of initial candidates is followed by a
concrete path that keeps the chosen candidates live. -/
theorem reach_complete {c0 : CCfg} (hinv : Inv c0) (ro0 : List (List (XEvent Nat) × RegObs))
    (h0 : List.Forall₂ (· ∈ ·) ro0 c0.cand) {a : ACfg}
    (h : Relation.ReflTransGen AStep ⟨ro0.map Prod.fst, c0.xs⟩ a) :
    ∃ c, Relation.ReflTransGen (fun x y => y ∈ CCfg.succ x) c0 c ∧ c.xs = a.st ∧
      ∃ ro : List (List (XEvent Nat) × RegObs), List.Forall₂ (· ∈ ·) ro c.cand ∧
        ro.map Prod.fst = a.rest ∧ ro.map Prod.snd = ro0.map Prod.snd := by
  induction h with
  | refl => exact ⟨c0, .refl, rfl, ro0, h0, rfl, rfl⟩
  | @tail a b _ hs ih =>
    obtain ⟨c, hc, hxs, ro, hro, hfst, hsnd⟩ := ih
    cases hs with
    | flush rest s s' hfl =>
      simp only at hxs hfst
      subst hxs
      obtain ⟨c', hc', hxs', hcand⟩ := flush_complete hfl
      refine ⟨c', hc.tail (by simp [CCfg.succ, hc']), hxs', ro, ?_, hfst, hsnd⟩
      rw [hcand]; exact hro
    | ev rest s s' i e es hget hst =>
      simp only at hxs hfst
      subst hxs
      have hlen : ro.length = c.cand.length := by simpa using hro.length_eq
      have hir : i < ro.length := by
        have : i < rest.length := (List.getElem?_eq_some_iff.mp hget).1
        rw [← hfst] at this; simpa using this
      have hic : i < c.cand.length := by omega
      have hq1 : ro[i].1 = e :: es := by
        have : (ro.map Prod.fst)[i]? = some (e :: es) := by rw [hfst]; exact hget
        simpa [hir] using this
      have hmem : ro[i] ∈ c.cand.getD i [] := by
        rw [getD_lt _ _ _ hic]; exact forall₂_get hro i hir hic
      have hhead : e ∈ heads (c.cand.getD i []) :=
        mem_heads.mpr ⟨ro[i], hmem, by simp [hq1]⟩
      have hth : e.thread < c.bufs.length := by
        have hi := inv_reach hinv hc
        have hcd : c.cand.getD i [] ∈ c.cand := by
          rw [getD_lt _ _ _ hic]; exact List.getElem_mem _
        exact hi _ hcd _ hmem e (by simp [hq1])
      obtain ⟨c'', hf, hxs'', hcand''⟩ := fire_complete hst hth
      refine ⟨{ c'' with cand := c.cand.set i (advance (c.cand.getD i []) e) },
        hc.tail ?_, ?_, ro.set i (es, ro[i].2), ?_, ?_, ?_⟩
      · simp only [CCfg.succ, List.mem_append]
        exact Or.inr (mem_events.mpr ⟨i, hic, e, hhead, c'', hf, rfl⟩)
      · simp only [CCfg.xs] at hxs'' ⊢; exact hxs''
      · apply forall₂_set hro
        apply mem_advance.mpr
        simp only
        rw [← hq1]
        exact hmem
      · simp only
        rw [List.map_set, hfst]
      · rw [List.map_set, ← hsnd]
        have e2 : (es, ro[i].2).2 = (ro.map Prod.snd)[i]'(by simpa using hir) := by simp
        rw [e2, List.set_getElem_self]

/-! ## The operational TSO outcomes -/

theorem map_mapIdx' {γ δ ε : Type} (l : List γ) (g : Nat → γ → δ) (f : δ → ε) :
    (l.mapIdx g).map f = l.mapIdx fun i a => f (g i a) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem forall₂_mapIdx {g : Nat → XTrace → List (XEvent Nat) × RegObs} :
    ∀ (T : List (List XTrace)) (ro : List (List (XEvent Nat) × RegObs)),
      List.Forall₂ (· ∈ ·) ro (T.mapIdx fun i trs => trs.map (g i)) ↔
        ∃ trs, List.Forall₂ (· ∈ ·) trs T ∧ ro = trs.mapIdx g := by
  intro T
  induction T generalizing g with
  | nil =>
    intro ro
    simp only [List.mapIdx_nil, List.forall₂_nil_right_iff]
    constructor
    · rintro rfl; exact ⟨[], rfl, rfl⟩
    · rintro ⟨trs, rfl, rfl⟩; rfl
  | cons trs0 T ih =>
    intro ro
    rw [List.mapIdx_cons]
    constructor
    · intro h
      cases h with
      | @cons p cd ro' cds hp hr =>
        obtain ⟨tr, htr, rfl⟩ := List.mem_map.mp hp
        obtain ⟨trs, htrs, rfl⟩ := (ih (g := fun i => g (i + 1)) ro').mp hr
        exact ⟨tr :: trs, .cons htr htrs, by rw [List.mapIdx_cons]⟩
    · rintro ⟨trs, htrs, rfl⟩
      cases htrs with
      | @cons tr trs1 trs' T' htr hrest =>
        rw [List.mapIdx_cons]
        exact .cons (List.mem_map_of_mem htr)
          ((ih (g := fun i => g (i + 1)) _).mpr ⟨trs', hrest, rfl⟩)

theorem c0_xs (t : Test) (T : List (List XTrace)) : (t.c0 T).xs = t.initX := by
  simp only [CCfg.xs, Test.c0, Test.initX]
  congr 1
  · funext y; exact cget_initCMem _ _
  · funext k
    by_cases hk : k < T.length <;> simp [List.getD_eq_getElem?_getD, hk]

theorem lookup_map_pair (rs : List Silmaril.X86.Reg) (v : Silmaril.X86.Reg → BitVec 64)
    (r : Silmaril.X86.Reg) (h : r ∈ rs) : (rs.map fun r => (r, v r)).lookup r = some (v r) := by
  induction rs with
  | nil => simp at h
  | cons r' rs ih =>
    by_cases hr : r = r'
    · subst hr; simp
    · have : (r == r') = false := by simpa using hr
      simp only [List.map_cons, List.lookup, this]
      exact ih (by simpa [hr] using h)

theorem outcome_obs (t : Test) (trs : List XTrace) (m : Nat → Option Byte) :
    t.outcome (obsFinal (trs.mapIdx fun i tr => (t.obsRegs i).map fun r => (r, tr.final.read r)) m) =
      t.outcome (finalOf trs m) := by
  unfold Test.outcome
  apply List.map_congr_left
  intro k hk
  cases k with
  | reg i r b =>
    have hr : r ∈ t.obsRegs i := by
      simp only [Test.obsRegs, List.mem_filterMap]
      exact ⟨.reg i r b, hk, by simp⟩
    simp only [Key.eval, obsFinal, finalOf]
    by_cases hi : i < trs.length
    · rw [getD_lt _ _ _ (by simpa using hi)]
      simp [List.getElem?_eq_getElem hi, lookup_map_pair _ _ _ hr]
    · rw [getD_ge _ _ _ (by simp; omega)]
      simp [List.getElem?_eq_none (by omega : trs.length ≤ i)]
  | mem a n => rfl

theorem bufs_nil_of_all {c : CCfg} (h : c.bufs.all List.isEmpty = true) (k : Nat) :
    c.bufs.getD k [] = [] := by
  by_cases hk : k < c.bufs.length
  · rw [getD_lt _ _ _ hk]
    have := List.all_eq_true.mp h _ (List.getElem_mem hk)
    simpa using this
  · exact getD_ge _ _ _ (by omega)

theorem mem_outs {t : Test} {c : CCfg} {o : Outcome} :
    o ∈ c.outs t ↔ c.bufs.all List.isEmpty = true ∧
      ∃ osel, List.Forall₂ (· ∈ ·) osel (c.cand.map finished) ∧
        t.outcome (obsFinal osel (cget c.mem)) = o := by
  unfold CCfg.outs
  split
  · rename_i hb
    simp only [List.mem_map, mem_seqL, hb, true_and]
  · rename_i hb
    simp [hb]

/-- **The operational TSO enumerator is exact**: when `Test.opOut` succeeds, its outcomes are
exactly the outcomes of `OpReach`. -/
theorem opOut_spec {t : Test} {T : List (List XTrace)} {os : List Outcome}
    (h : t.opOut T = some os) (o : Outcome) :
    o ∈ os ↔ ∃ f, OpReach t T f ∧ t.outcome f = o := by
  unfold Test.opOut at h
  split at h
  · rename_i hok
    obtain ⟨out, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [mem_uniq, collect_spec ceq_iff _ _ _ hc]
    simp only [List.mem_singleton, exists_eq_left]
    have hc0 : (t.c0 T).cand = T.mapIdx fun i trs => trs.map fun tr =>
        (traceX i tr, (t.obsRegs i).map fun r => (r, tr.final.read r)) := rfl
    constructor
    · rintro ⟨c, hreach, ho⟩
      obtain ⟨hb, osel, hosel, rfl⟩ := mem_outs.mp ho
      have hro : List.Forall₂ (· ∈ ·) (osel.map fun r => (([] : List (XEvent Nat)), r)) c.cand := by
        rw [List.forall₂_map_left_iff]
        rw [List.forall₂_map_right_iff] at hosel
        exact hosel.imp fun _ _ h => mem_finished.mp h
      obtain ⟨ro0, h0, hsnd, hrun⟩ := reach_sound hreach _ hro
      rw [hc0, forall₂_mapIdx] at h0
      obtain ⟨trs, htrs, rfl⟩ := h0
      have hosel' : osel = trs.mapIdx fun i tr => (t.obsRegs i).map fun r => (r, tr.final.read r) := by
        rw [map_mapIdx'] at hsnd
        have e : (osel.map fun r => (([] : List (XEvent Nat)), r)).map Prod.snd = osel := by
          simp [List.map_map, Function.comp_def]
        rw [← e, ← hsnd]
      have hlen : osel.length = trs.length := by rw [hosel']; simp
      refine ⟨finalOf trs (cget c.mem), ⟨trs, htrs, c.xs, ?_, ?_, rfl⟩, ?_⟩
      · rw [map_mapIdx', c0_xs] at hrun
        have e1 : (osel.map fun r => (([] : List (XEvent Nat)), r)).map Prod.fst =
            trs.map fun _ => [] := by
          rw [List.map_map]; simp only [Function.comp_def]
          rw [List.map_const', List.map_const', hlen]
        rw [e1] at hrun
        exact hrun
      · intro k; exact bufs_nil_of_all hb k
      · rw [hosel', outcome_obs]
    · rintro ⟨f, ⟨trs, htrs, s, hrun, hbuf, rfl⟩, rfl⟩
      have h0 : List.Forall₂ (· ∈ ·) (trs.mapIdx fun i tr =>
          (traceX i tr, (t.obsRegs i).map fun r => (r, tr.final.read r))) (t.c0 T).cand := by
        rw [hc0, forall₂_mapIdx]; exact ⟨trs, htrs, rfl⟩
      have hrun' : Relation.ReflTransGen AStep
          ⟨(trs.mapIdx fun i tr => (traceX i tr, (t.obsRegs i).map fun r => (r, tr.final.read r))).map
            Prod.fst, (t.c0 T).xs⟩ ⟨trs.map fun _ => [], s⟩ := by
        rw [map_mapIdx', c0_xs]; exact hrun
      obtain ⟨c, hreach, hxs, ro, hro, hfst, hsnd⟩ :=
        reach_complete (inv_of_threadsOk hok) _ h0 hrun'
      simp only at hxs hfst
      have hro_eq : ro = (ro.map Prod.snd).map fun r => (([] : List (XEvent Nat)), r) := by
        rw [List.map_map]
        conv_lhs => rw [← List.map_id ro]
        apply List.map_congr_left
        intro p hp
        have : p.1 ∈ ro.map Prod.fst := List.mem_map_of_mem hp
        rw [hfst] at this
        obtain ⟨_, _, he⟩ := List.mem_map.mp this
        obtain ⟨a, b⟩ := p
        simp only at he
        simp [← he]
      refine ⟨c, hreach, mem_outs.mpr ⟨?_, ro.map Prod.snd, ?_, ?_⟩⟩
      · rw [List.all_eq_true]
        intro b hb
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        have := congrArg (fun x => x.buffer k) hxs
        simp only [CCfg.xs] at this
        rw [getD_lt _ _ _ hk] at this
        simp [this, hbuf k]
      · rw [List.forall₂_map_right_iff]
        rw [hro_eq] at hro
        rw [List.forall₂_map_left_iff] at hro
        exact hro.imp fun _ _ h => mem_finished.mpr h
      · have hm : cget c.mem = s.memory := congrArg XState.memory hxs
        rw [hm, hsnd, map_mapIdx']
        exact outcome_obs t trs s.memory
  · cases h

end Silmaril.Proofs.X86.MemoryModel.Litmus
