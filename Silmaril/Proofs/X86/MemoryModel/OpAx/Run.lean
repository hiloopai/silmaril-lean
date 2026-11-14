module

public import Silmaril.X86.MemoryModel.OpAx.Defs
public import Silmaril.Proofs.X86.MemoryModel.OpAx.Timed

/-!
# Runs of the store-buffer machine are timed candidates: proofs

An instrumented copy of the run (`G`): the units executed so far (in execution order), `rf`
for the executed reads, execution and memory times on one global clock (one tick per step), the
write units in memory order `wo`, and the unit ids of each thread's buffered stores (`tb`). The
invariant `Inv` relates it to the machine configuration; every `AStep` preserves it
(`inv_step`). At the end of a complete run the timing is `TimedOk` (`timedOk_of_final`), so
`tso_of_timedOk` applies.
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.X86.MemoryModel.OpAx.Proofs

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.OpAx
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush Byte Mem readMem writeMem readBufByte
  entryByte viewMem readView enqueue)
open Silmaril.X86.MemoryModel.Litmus (ACfg AStep)

/-! ## Unit lists -/

/-- The unit at index `i` of a unit list (`dflt` out of range, as `Exec.evN`). -/
def uev (us : List (Ev × List Byte)) (i : Nat) : Ev := (us.map Prod.fst).getD i dflt

theorem uev_append_lt {us v : List (Ev × List Byte)} {i : Nat} (h : i < us.length) :
    uev (us ++ v) i = uev us i := by
  simp only [uev, List.getD_eq_getElem?_getD, List.map_append]
  rw [List.getElem?_append_left (by simpa using h)]

theorem uev_append_len {us v : List (Ev × List Byte)} {j : Nat} (h : j < v.length) :
    uev (us ++ v) (us.length + j) = (v[j]).1 := by
  simp only [uev, List.getD_eq_getElem?_getD, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp [h]

theorem uev_ge {us : List (Ev × List Byte)} {i : Nat} (h : us.length ≤ i) : uev us i = dflt := by
  simp only [uev, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simpa using h)]
  rfl

/-- The last unit of `l` that covers byte `y`. -/
def lastCov (us : List (Ev × List Byte)) (l : List Nat) (y : Nat) : Option Nat :=
  (l.filter fun w => (uev us w).covers y).getLast?

theorem getLast?_mem {l : List Nat} {w : Nat} (h : l.getLast? = some w) : w ∈ l :=
  List.mem_of_getLast? h

theorem lastCov_mem {us : List (Ev × List Byte)} {l : List Nat} {y w : Nat}
    (h : lastCov us l y = some w) : w ∈ l ∧ (uev us w).covers y = true := by
  have := List.mem_of_getLast? h
  simpa using List.mem_filter.mp this

theorem lastCov_none {us : List (Ev × List Byte)} {l : List Nat} {y w : Nat}
    (h : lastCov us l y = none) (hw : w ∈ l) (hc : (uev us w).covers y = true) : False := by
  simp only [lastCov, List.getLast?_eq_none_iff] at h
  have : w ∈ l.filter fun w => (uev us w).covers y := List.mem_filter.mpr ⟨hw, hc⟩
  rw [h] at this
  simp at this

/-- In a list sorted by `R`, every element is `R`-before or equal to the last one. -/
theorem pairwise_getLast {R : Nat → Nat → Prop} :
    ∀ {l : List Nat}, l.Pairwise R → ∀ {w v : Nat}, l.getLast? = some v → w ∈ l → w = v ∨ R w v
  | [], _, _, _, h, _ => by simp at h
  | a :: l, hp, w, v, h, hw => by
    rw [List.pairwise_cons] at hp
    rw [List.getLast?_cons] at h
    cases hl : l.getLast? with
    | none =>
      rw [hl] at h
      simp only [Option.getD_none, Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hw with rfl | hw
      · exact .inl rfl
      · simp only [List.getLast?_eq_none_iff] at hl; subst hl; simp at hw
    | some u =>
      rw [hl] at h
      simp only [Option.getD_some, Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hw with rfl | hw
      · exact .inr (hp.1 _ (List.mem_of_getLast? hl))
      · exact pairwise_getLast hp.2 hl hw

theorem lastCov_max {us : List (Ev × List Byte)} {R : Nat → Nat → Prop} {l : List Nat}
    (hp : l.Pairwise R) {y v w : Nat} (h : lastCov us l y = some v) (hw : w ∈ l)
    (hc : (uev us w).covers y = true) : w = v ∨ R w v :=
  pairwise_getLast (hp.filter _) h (List.mem_filter.mpr ⟨hw, hc⟩)

/-! ## Memory lemmas -/

theorem readMem_some {m : Tso.Mem} : ∀ {n a : Nat} {bs : List Byte}, readMem m a n = some bs →
    bs.length = n ∧ ∀ j < n, m (a + j) = bs[j]?
  | 0, a, bs, h => by
    simp only [readMem, Option.some.injEq] at h
    subst h; simp
  | n + 1, a, bs, h => by
    simp only [readMem] at h
    split at h
    · rename_i b bs' hb hbs
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hl, hj⟩ := readMem_some hbs
      refine ⟨by simp [hl], fun j hj' => ?_⟩
      cases j with
      | zero => simpa using hb
      | succ j =>
        have := hj j (by omega)
        rw [show a + (j + 1) = a + 1 + j by omega, this]
        simp
    · cases h

theorem covers_iff {e : Ev} {y : Nat} : e.covers y = true ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.covers]

theorem entryByte_eq {e : Ev} (hd : e.data.length = e.size) (y : Nat) :
    entryByte e.addr e.data y = if e.covers y then some (e.byte y) else none := by
  unfold entryByte
  by_cases hc : e.covers y = true
  · simp only [hc, ↓reduceIte]
    obtain ⟨h1, h2⟩ := covers_iff.mp hc
    simp only [h1, ↓reduceIte]
    have : y - e.addr < e.data.length := by omega
    simp [Ev.byte, List.getElem?_eq_getElem this]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, ite_eq_right_iff]
    intro h1
    rw [covers_iff] at hc
    rw [List.getElem?_eq_none]
    omega

theorem writeMem_eq {m : Tso.Mem} {e : Ev} (hd : e.data.length = e.size) (y : Nat) :
    writeMem m e.addr e.data y = if e.covers y then some (e.byte y) else m y := by
  unfold writeMem
  rw [entryByte_eq hd]
  split <;> simp

theorem readBufByte_eq {us : List (Ev × List Byte)} (y : Nat) : ∀ (l : List Nat),
    (∀ w ∈ l, (uev us w).data.length = (uev us w).size) →
    readBufByte y (l.map fun w => ((uev us w).addr, (uev us w).data)) =
      (lastCov us l y).map fun w => (uev us w).byte y
  | [], _ => by simp [readBufByte, lastCov]
  | w :: l, hd => by
    simp only [List.map_cons, readBufByte]
    rw [readBufByte_eq y l (fun v hv => hd v (List.mem_cons_of_mem _ hv)),
      entryByte_eq (hd w List.mem_cons_self)]
    simp only [lastCov, List.filter_cons]
    by_cases hc : (uev us w).covers y = true
    · simp only [hc, ↓reduceIte, List.getLast?_cons]
      cases (l.filter fun w => (uev us w).covers y).getLast? <;> simp
    · simp [hc]

/-! ## Units of events -/

theorem evUnits_tid {i k : Nat} {ev : XEvent Nat} {p : Ev × List Byte} (h : p ∈ evUnits i k ev) :
    p.1.tid = i := by
  cases ev <;> simp only [evUnits, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;> rfl

theorem evUnits_pos {i k : Nat} {ev : XEvent Nat} {p : Ev × List Byte} (h : p ∈ evUnits i k ev) :
    2 * k ≤ p.1.pos ∧ p.1.pos < 2 * (k + 1) := by
  cases ev <;> simp only [evUnits, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;> (simp; try omega)

theorem evUnits_data {i k : Nat} {ev : XEvent Nat} {p : Ev × List Byte} (h : p ∈ evUnits i k ev)
    (hw : p.1.isW = true) : p.1.data.length = p.1.size := by
  cases ev <;> simp only [evUnits, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;>
    simp_all [Ev.isW]

theorem evUnits_foot {i k : Nat} {ev : XEvent Nat} {p : Ev × List Byte} (h : p ∈ evUnits i k ev)
    (hm : p.1.isM = true) : (p.1.addr, p.1.size) ∈ footOf ev := by
  cases ev <;> simp only [evUnits, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;>
    simp_all [Ev.isM, Ev.isR, Ev.isW, footOf]

theorem threadUnits_concat (i : Nat) (l : List (XEvent Nat)) (ev : XEvent Nat) :
    threadUnits i (l ++ [ev]) = threadUnits i l ++ evUnits i l.length ev := by
  simp [threadUnits, List.mapIdx_concat]

theorem mem_threadUnits {i : Nat} {l : List (XEvent Nat)} {p : Ev × List Byte}
    (h : p ∈ threadUnits i l) : ∃ k, ∃ ev ∈ l, p ∈ evUnits i k ev := by
  simp only [threadUnits, List.mem_flatten, List.mem_mapIdx] at h
  obtain ⟨_, ⟨k, hk, rfl⟩, hp⟩ := h
  exact ⟨k, l[k], List.getElem_mem hk, hp⟩

theorem threadUnits_tid {i : Nat} {l : List (XEvent Nat)} {p : Ev × List Byte}
    (h : p ∈ threadUnits i l) : p.1.tid = i := by
  obtain ⟨k, ev, -, hp⟩ := mem_threadUnits h
  exact evUnits_tid hp

theorem progUnits_filter_aux (i : Nat) : ∀ (P : List (List (XEvent Nat))) (o : Nat),
    ((P.mapIdx fun j es => threadUnits (j + o) es).flatten.filter fun p => p.1.tid == i) =
      if o ≤ i then threadUnits i (P[i - o]?.getD []) else []
  | [], o => by split <;> simp [threadUnits]
  | es :: P, o => by
    rw [List.mapIdx_cons, List.flatten_cons, List.filter_append]
    have ih := progUnits_filter_aux i P (o + 1)
    simp only [show ∀ j, j + 1 + o = j + (o + 1) by intro j; omega]
    rw [ih]
    have hf : ((threadUnits (0 + o) es).filter fun p => p.1.tid == i) =
        if o = i then threadUnits i es else [] := by
      split
      · subst_vars
        rw [List.filter_eq_self.mpr]
        · simp
        · intro p hp; simp [threadUnits_tid hp]
      · rw [List.filter_eq_nil_iff.mpr]
        intro p hp
        simp only [threadUnits_tid hp, beq_iff_eq]
        omega
    rw [hf]
    by_cases h1 : o = i
    · subst h1; simp [threadUnits]
    · by_cases h2 : o + 1 ≤ i
      · have h3 : o ≤ i := by omega
        simp only [h1, h2, h3, ↓reduceIte, List.nil_append]
        rw [show i - o = (i - (o + 1)) + 1 by omega]
        simp
      · have h3 : ¬ o ≤ i := by omega
        simp [h1, h2, h3]

theorem progUnits_filter (P : List (List (XEvent Nat))) (i : Nat) :
    (progUnits P).filter (fun p => p.1.tid == i) = threadUnits i (P[i]?.getD []) := by
  have := progUnits_filter_aux i P 0
  simp only [Nat.add_zero, Nat.zero_le, ↓reduceIte, Nat.sub_zero] at this
  exact this

/-- Two unit lists with the same units in each thread are permutations of each other. -/
theorem perm_of_filter {l₁ l₂ : List (Ev × List Byte)}
    (h : ∀ i, l₁.filter (fun p => p.1.tid == i) = l₂.filter (fun p => p.1.tid == i)) :
    l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro p
  have h1 := List.count_filter (p := fun q : Ev × List Byte => q.1.tid == p.1.tid) (a := p) (l := l₁)
    (by simp)
  have h2 := List.count_filter (p := fun q : Ev × List Byte => q.1.tid == p.1.tid) (a := p) (l := l₂)
    (by simp)
  rw [← h1, ← h2, h p.1.tid]

/-! ## The instrumented run -/

/-- The history of a run so far: units in execution order, `rf`, locked pairs, execution and
memory times, the writes in memory order, each thread's buffered write units, each thread's
number of executed events, and the clock. -/
structure G where
  us : List (Ev × List Byte)
  rf : Nat → Nat → Option Nat
  rmw : List (Nat × Nat)
  e : Nat → Nat
  f : Nat → Nat
  wo : List Nat
  tb : Nat → List Nat
  cnt : Nat → Nat
  clk : Nat

/-- The candidate execution of a history. -/
def G.x (g : G) : Exec where
  evs := g.us.map Prod.fst
  rf := g.rf
  co := fun y => g.wo.filter fun w => (uev g.us w).covers y
  rmw := g.rmw

/-- The timing of a history. -/
def G.T (g : G) : Timing := ⟨g.e, g.f, g.wo⟩

/-- Write `w` reached memory before time `t`. -/
def FB (g : G) (w t : Nat) : Prop := w ∈ g.wo ∧ g.f w < t

/-- `RfSpec`, with "reached memory before" in place of a comparison of memory times (which
the writes still buffered do not have yet). -/
def RfInv (g : G) (r y : Nat) : Prop :=
  match g.rf r y with
  | some s =>
    s < g.us.length ∧ (uev g.us s).isW = true ∧ (uev g.us s).covers y = true ∧
      ((((uev g.us s).tid = (uev g.us r).tid ∧ (uev g.us s).pos < (uev g.us r).pos ∧
          ¬ FB g s (g.e r)) ∧
          ∀ w < g.us.length, (uev g.us w).isW = true → (uev g.us w).covers y = true →
            (uev g.us w).tid = (uev g.us r).tid → (uev g.us w).pos < (uev g.us r).pos →
              ¬ FB g w (g.e r) → (uev g.us w).pos ≤ (uev g.us s).pos) ∨
        (FB g s (g.e r) ∧
          (∀ w < g.us.length, (uev g.us w).isW = true → (uev g.us w).covers y = true →
            FB g w (g.e r) → g.f w ≤ g.f s) ∧
          ∀ w < g.us.length, (uev g.us w).isW = true → (uev g.us w).covers y = true →
            (uev g.us w).tid = (uev g.us r).tid → (uev g.us w).pos < (uev g.us r).pos →
              FB g w (g.e r)))
  | none =>
    ∀ w < g.us.length, (uev g.us w).isW = true → (uev g.us w).covers y = true →
      ¬ FB g w (g.e r) ∧ ¬ ((uev g.us w).tid = (uev g.us r).tid ∧
        (uev g.us w).pos < (uev g.us r).pos)

/-- The bookkeeping part of the invariant: the remaining events, the units executed per thread,
positions, and the data of write units. -/
structure Book (P : List (List (XEvent Nat))) (rest : List (List (XEvent Nat)))
    (us : List (Ev × List Byte)) (cnt : Nat → Nat) : Prop where
  rest : ∀ i, rest[i]? = P[i]?.map (List.drop (cnt i))
  filt : ∀ i, us.filter (fun p => p.1.tid == i) = threadUnits i ((P[i]?.getD []).take (cnt i))
  posLt : ∀ u < us.length, (uev us u).pos < 2 * cnt (uev us u).tid
  uniq : ∀ a < us.length, ∀ b < us.length, (uev us a).tid = (uev us b).tid →
    (uev us a).pos = (uev us b).pos → a = b
  dataLen : ∀ w < us.length, (uev us w).isW = true → (uev us w).data.length = (uev us w).size

/-- The invariant relating a history to a machine configuration. -/
structure Inv (P : List (List (XEvent Nat))) (init : Tso.Mem) (c : ACfg) (g : G) : Prop where
  book : Book P c.rest g.us g.cnt
  poE : ∀ a < g.us.length, ∀ b < g.us.length, (uev g.us a).tid = (uev g.us b).tid →
    (uev g.us a).pos < (uev g.us b).pos → g.e a < g.e b
  eLt : ∀ u < g.us.length, g.e u < g.clk
  woW : ∀ w ∈ g.wo, w < g.us.length ∧ (uev g.us w).isW = true
  woF : ∀ w ∈ g.wo, g.f w < g.clk ∧ g.e w ≤ g.f w
  woSorted : g.wo.Pairwise fun a b => g.f a < g.f b
  fifo : ∀ a < g.us.length, ∀ b < g.us.length, (uev g.us a).isW = true →
    (uev g.us b).isW = true → (uev g.us a).tid = (uev g.us b).tid →
    (uev g.us a).pos < (uev g.us b).pos → b ∈ g.wo → a ∈ g.wo ∧ g.f a < g.f b
  tbOk : ∀ t, ∀ w ∈ g.tb t, w < g.us.length ∧ (uev g.us w).isW = true ∧ (uev g.us w).tid = t ∧
    (uev g.us w).locked = false ∧ w ∉ g.wo
  tbSorted : ∀ t, (g.tb t).Pairwise fun a b => (uev g.us a).pos < (uev g.us b).pos
  wAll : ∀ w < g.us.length, (uev g.us w).isW = true → w ∈ g.wo ∨ w ∈ g.tb (uev g.us w).tid
  buf : ∀ t, c.st.buffer t = (g.tb t).map fun w => ((uev g.us w).addr, (uev g.us w).data)
  mem : ∀ y, c.st.memory y = match lastCov g.us g.wo y with
    | none => init y
    | some w => some ((uev g.us w).byte y)
  lockedW : ∀ w < g.us.length, (uev g.us w).isW = true → (uev g.us w).locked = true →
    w ∈ g.wo ∧ g.f w = g.e w
  drain : ∀ u < g.us.length, ∀ w < g.us.length, (uev g.us w).isW = true →
    (uev g.us w).tid = (uev g.us u).tid → (uev g.us w).pos < (uev g.us u).pos →
    ((uev g.us u).isFence .mfence = true ∨ (uev g.us u).isA = true) → w ∈ g.wo ∧ g.f w < g.e u
  rmwOk : ∀ p ∈ g.rmw, p.1 < g.us.length ∧ p.2 < g.us.length ∧ (uev g.us p.1).isR = true ∧
    (uev g.us p.2).isW = true ∧ (uev g.us p.1).tid = (uev g.us p.2).tid ∧ p.2 ∈ g.wo ∧
    g.f p.2 = g.e p.1 + 1
  clash : ∀ r < g.us.length, (uev g.us r).isR = true → ∀ w ∈ g.wo, g.f w ≠ g.e r
  rfW : ∀ r y w, g.rf r y = some w →
    w < g.us.length ∧ (uev g.us w).isW = true ∧ (uev g.us w).covers y = true
  rfInv : ∀ r < g.us.length, (uev g.us r).isR = true → ∀ y ∈ (uev g.us r).bytes, RfInv g r y
  vals : ∀ r < g.us.length, (uev g.us r).isR = true →
    g.x.readBytes (fun y => (init y).getD 0) r = (g.us.getD r (dflt, [])).2

/-- The empty history. -/
def G.init : G := ⟨[], fun _ _ => none, [], fun _ => 0, fun _ => 0, [], fun _ => [], fun _ => 0, 0⟩

theorem inv_init (P : List (List (XEvent Nat))) (init : Tso.Mem) :
    Inv P init ⟨P, ⟨init, fun _ => []⟩⟩ G.init := by
  refine ⟨⟨fun i => ?_, fun i => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> simp [G.init, threadUnits, lastCov]
  cases P[i]? <;> simp

/-! ## Bookkeeping under a step -/

theorem uev_cases {us v : List (Ev × List Byte)} {u : Nat} (hu : u < (us ++ v).length) :
    (u < us.length ∧ uev (us ++ v) u = uev us u) ∨
      ∃ j, ∃ hj : j < v.length, u = us.length + j ∧ uev (us ++ v) u = (v[j]).1 := by
  by_cases h : u < us.length
  · exact .inl ⟨h, uev_append_lt h⟩
  · simp only [List.length_append] at hu
    refine .inr ⟨u - us.length, by omega, by omega, ?_⟩
    rw [← uev_append_len (us := us) (v := v) (by omega)]
    congr 1; omega

theorem evUnits_inj {i k : Nat} {ev : XEvent Nat} {j₁ j₂ : Nat} (h₁ : j₁ < (evUnits i k ev).length)
    (h₂ : j₂ < (evUnits i k ev).length)
    (h : ((evUnits i k ev)[j₁]).1.pos = ((evUnits i k ev)[j₂]).1.pos) : j₁ = j₂ := by
  cases ev with
  | rmw t a old new =>
    simp only [evUnits, List.length_cons, List.length_nil] at h₁ h₂
    match j₁, j₂, h₁, h₂ with
    | 0, 0, _, _ => rfl
    | 1, 1, _, _ => rfl
    | 0, 1, _, _ => simp [evUnits] at h
    | 1, 0, _, _ => simp [evUnits] at h
  | _ => simp only [evUnits, List.length_cons, List.length_nil] at h₁ h₂; omega

/-- The bump of thread `i`'s event counter. -/
def bump (cnt : Nat → Nat) (i : Nat) : Nat → Nat := fun j => if j = i then cnt i + 1 else cnt j

theorem rest_head {P rest : List (List (XEvent Nat))} {us : List (Ev × List Byte)}
    {cnt : Nat → Nat} (hb : Book P rest us cnt) {i : Nat} {ev : XEvent Nat}
    {es : List (XEvent Nat)} (hr : rest[i]? = some (ev :: es)) :
    ∃ ps, P[i]? = some ps ∧ ev ∈ ps ∧ cnt i < ps.length ∧ ps[cnt i]? = some ev ∧
      ps.drop (cnt i + 1) = es := by
  rw [hb.rest i] at hr
  cases hp : P[i]? with
  | none => rw [hp] at hr; cases hr
  | some ps =>
    rw [hp] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    have hlt : cnt i < ps.length := by
      by_contra hge
      rw [List.drop_eq_nil_of_le (by omega)] at hr
      cases hr
    rw [List.drop_eq_getElem_cons hlt] at hr
    simp only [List.cons.injEq] at hr
    refine ⟨ps, rfl, hr.1 ▸ List.getElem_mem hlt, hlt, by rw [List.getElem?_eq_getElem hlt, hr.1],
      hr.2⟩

theorem book_exec {P rest : List (List (XEvent Nat))} {us : List (Ev × List Byte)}
    {cnt : Nat → Nat} (hb : Book P rest us cnt) {i : Nat} {ev : XEvent Nat}
    {es : List (XEvent Nat)} (hr : rest[i]? = some (ev :: es)) :
    Book P (rest.set i es) (us ++ evUnits i (cnt i) ev) (bump cnt i) := by
  obtain ⟨ps, hps, -, hlt, hget, hdrop⟩ := rest_head hb hr
  have hi : i < rest.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hr; cases hr
  -- old positions of thread `i` are below `2 * cnt i`
  have oldpos : ∀ u < us.length, (uev us u).tid = i → (uev us u).pos < 2 * cnt i := by
    intro u hu ht
    have := hb.posLt u hu
    rwa [ht] at this
  refine ⟨fun j => ?_, fun j => ?_, ?_, ?_, ?_⟩
  · rw [List.getElem?_set]
    by_cases hj : i = j
    · subst hj
      simp only [hi, ↓reduceIte, hps, Option.map_some, bump]
      exact congrArg some hdrop.symm
    · simp only [hj, ↓reduceIte, bump, show ¬ j = i from fun h => hj h.symm]
      exact hb.rest j
  · rw [List.filter_append, hb.filt j]
    by_cases hj : j = i
    · subst hj
      simp only [bump, ↓reduceIte, hps, Option.getD_some]
      rw [List.take_add_one, hget]
      simp only [Option.toList_some]
      rw [threadUnits_concat, List.length_take_of_le (by omega)]
      congr 1
      rw [List.filter_eq_self.mpr]
      intro p hp; simp [evUnits_tid hp]
    · simp only [bump, hj, ↓reduceIte]
      rw [List.filter_eq_nil_iff.mpr, List.append_nil]
      intro p hp
      simp only [evUnits_tid hp, beq_iff_eq]
      exact fun h => hj h.symm
  · intro u hu
    rcases uev_cases hu with ⟨hu, he⟩ | ⟨j, hj, rfl, he⟩
    · rw [he]
      have := hb.posLt u hu
      simp only [bump]
      split
      · next h => rw [h] at this; omega
      · omega
    · rw [he]
      have hm := List.getElem_mem hj
      have := evUnits_pos hm
      simp only [evUnits_tid hm, bump, ↓reduceIte]
      omega
  · intro a ha b hb' ht hp
    rcases uev_cases ha with ⟨ha, hea⟩ | ⟨ja, hja, rfl, hea⟩ <;>
      rcases uev_cases hb' with ⟨hb', heb⟩ | ⟨jb, hjb, rfl, heb⟩ <;> rw [hea, heb] at ht hp
    · exact hb.uniq a ha b hb' ht hp
    · have hm := List.getElem_mem hjb
      have := oldpos a ha (ht.trans (evUnits_tid hm))
      have := (evUnits_pos hm).1
      omega
    · have hm := List.getElem_mem hja
      have := oldpos b hb' (ht.symm.trans (evUnits_tid hm))
      have := (evUnits_pos hm).1
      omega
    · rw [evUnits_inj hja hjb hp]
  · intro w hw hW
    rcases uev_cases hw with ⟨hw, he⟩ | ⟨j, hj, rfl, he⟩
    · rw [he] at hW ⊢; exact hb.dataLen w hw hW
    · rw [he] at hW ⊢; exact evUnits_data (List.getElem_mem hj) hW

/-! ## Extending a history -/

theorem lastCov_append {us v : List (Ev × List Byte)} {l : List Nat} (y : Nat)
    (h : ∀ w ∈ l, w < us.length) : lastCov (us ++ v) l y = lastCov us l y := by
  unfold lastCov
  congr 1
  apply List.filter_congr
  intro w hw
  rw [uev_append_lt (h w hw)]

theorem getD_append_lt {us v : List (Ev × List Byte)} {r : Nat} (h : r < us.length) :
    (us ++ v).getD r (dflt, []) = us.getD r (dflt, []) := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left h]

/-- `FB` at an old time only sees old writes, unchanged. -/
theorem fb_ext {g g' : G} {t : Nat} (ht : t ≤ g.clk)
    (hwo : ∀ w ∈ g.wo, w ∈ g'.wo ∧ g'.f w = g.f w)
    (hnew : ∀ w ∈ g'.wo, w ∈ g.wo ∨ g.clk ≤ g'.f w)
    (hlt : ∀ w ∈ g.wo, w < g.us.length) (w : Nat) :
    FB g' w t ↔ w < g.us.length ∧ FB g w t := by
  constructor
  · rintro ⟨hw, hf⟩
    rcases hnew w hw with hw' | hge
    · rw [(hwo w hw').2] at hf
      exact ⟨hlt w hw', hw', hf⟩
    · omega
  · rintro ⟨-, hw, hf⟩
    exact ⟨(hwo w hw).1, by rw [(hwo w hw).2]; exact hf⟩

theorem rfInv_ext {g g' : G} {v : List (Ev × List Byte)} (hus : g'.us = g.us ++ v) {r : Nat}
    (hr : r < g.us.length) {y : Nat} (hrf : g'.rf r y = g.rf r y) (he : g'.e r = g.e r)
    (hFB : ∀ w, FB g' w (g.e r) ↔ w < g.us.length ∧ FB g w (g.e r))
    (hf : ∀ w ∈ g.wo, g'.f w = g.f w)
    (hnew : ∀ w < g'.us.length, g.us.length ≤ w → (uev g'.us w).tid = (uev g.us r).tid →
      (uev g.us r).pos < (uev g'.us w).pos)
    (h : RfInv g r y) : RfInv g' r y := by
  have hE : ∀ u < g.us.length, uev g'.us u = uev g.us u := fun u hu => by
    rw [hus, uev_append_lt hu]
  have hlen : g.us.length ≤ g'.us.length := by rw [hus]; simp
  unfold RfInv at h ⊢
  rw [hrf, he, hE r hr]
  revert h
  cases g.rf r y with
  | some s =>
    intro h
    obtain ⟨hs, hW, hc, hcase⟩ := h
    refine ⟨by omega, by rw [hE s hs]; exact hW, by rw [hE s hs]; exact hc, ?_⟩
    rw [hE s hs]
    rcases hcase with ⟨⟨ht, hp, hnf⟩, hmax⟩ | ⟨hfb, hmax, hall⟩
    · refine .inl ⟨⟨ht, hp, fun h' => hnf ((hFB s).mp h').2⟩, ?_⟩
      intro w hw hW' hc' ht' hp' hnf'
      by_cases hwo : w < g.us.length
      · rw [hE w hwo] at hW' hc' ht' hp' ⊢
        exact hmax w hwo hW' hc' ht' hp' (fun h' => hnf' ((hFB w).mpr ⟨hwo, h'⟩))
      · have := hnew w hw (by omega) ht'
        omega
    · refine .inr ⟨(hFB s).mpr ⟨hs, hfb⟩, ?_, ?_⟩
      · intro w hw hW' hc' hfb'
        obtain ⟨hwo, hfb''⟩ := (hFB w).mp hfb'
        rw [hE w hwo] at hW' hc'
        rw [hf w hfb''.1, hf s hfb.1]
        exact hmax w hwo hW' hc' hfb''
      · intro w hw hW' hc' ht' hp'
        by_cases hwo : w < g.us.length
        · rw [hE w hwo] at hW' hc' ht' hp'
          exact (hFB w).mpr ⟨hwo, hall w hwo hW' hc' ht' hp'⟩
        · have := hnew w hw (by omega) ht'
          omega
  | none =>
    intro h w hw hW' hc'
    by_cases hwo : w < g.us.length
    · rw [hE w hwo] at hW' hc' ⊢
      obtain ⟨h1, h2⟩ := h w hwo hW' hc'
      exact ⟨fun h' => h1 ((hFB w).mp h').2, h2⟩
    · refine ⟨fun h' => hwo ((hFB w).mp h').1, fun ⟨ht', hp'⟩ => ?_⟩
      have := hnew w hw (by omega) ht'
      omega

theorem vals_ext {g g' : G} {v : List (Ev × List Byte)} (hus : g'.us = g.us ++ v) {r : Nat}
    (hr : r < g.us.length) (hrf : g'.rf r = g.rf r)
    (hrfW : ∀ y w, g.rf r y = some w → w < g.us.length) (init : Nat → Byte) :
    g'.x.readBytes init r = g.x.readBytes init r ∧
      g'.us.getD r (dflt, []) = g.us.getD r (dflt, []) := by
  have hE : ∀ u < g.us.length, uev g'.us u = uev g.us u := fun u hu => by
    rw [hus, uev_append_lt hu]
  refine ⟨?_, by rw [hus, getD_append_lt hr]⟩
  have hx : ∀ u < g.us.length, g'.x.evN u = g.x.evN u := hE
  simp only [Exec.readBytes]
  rw [hx r hr]
  apply List.map_congr_left
  intro y _
  change (match g'.rf r y with | none => init y | some w => (g'.x.evN w).byte y) =
    (match g.rf r y with | none => init y | some w => (g.x.evN w).byte y)
  rw [hrf]
  cases h : g.rf r y with
  | none => rfl
  | some w => simp only; rw [hx w (hrfW y w h)]

/-! ## Steps -/

theorem uev_cases1 {us : List (Ev × List Byte)} {p : Ev × List Byte} {u : Nat}
    (hu : u < (us ++ [p]).length) :
    (u < us.length ∧ uev (us ++ [p]) u = uev us u) ∨ (u = us.length ∧ uev (us ++ [p]) u = p.1) := by
  rcases uev_cases hu with h | ⟨j, hj, rfl, he⟩
  · exact .inl h
  · simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    exact .inr ⟨rfl, by simpa using he⟩

/-- Executing event `ev` of thread `i` as a load. -/
def G.load (g : G) (i : Nat) (ev : XEvent Nat) : G :=
  { g with
    us := g.us ++ evUnits i (g.cnt i) ev
    rf := fun r y => if r = g.us.length then (lastCov g.us (g.tb i) y).or (lastCov g.us g.wo y)
      else g.rf r y
    e := fun u => if u = g.us.length then g.clk else g.e u
    cnt := bump g.cnt i
    clk := g.clk + 1 }

theorem fb_lt {P : List (List (XEvent Nat))} {init : Tso.Mem} {c : ACfg} {g : G}
    (H : Inv P init c g) {w : Nat} : FB g w g.clk ↔ w ∈ g.wo :=
  ⟨fun h => h.1, fun h => ⟨h, (H.woF w h).1⟩⟩

theorem inv_load {P : List (List (XEvent Nat))} {init : Tso.Mem} {c : ACfg} {g : G}
    (H : Inv P init c g) {i t a : Nat} {bs : List Byte} {es : List (XEvent Nat)}
    (hr : c.rest[i]? = some (.load t a bs :: es)) (ht : t = i)
    (hv : readView c.st t a bs.length = some bs) :
    Inv P init ⟨c.rest.set i es, c.st⟩ (g.load i (.load t a bs)) := by
  subst ht
  set n := g.us.length with hn
  set R : Ev := { tid := t, pos := 2 * g.cnt t, act := .read, addr := a, size := bs.length }
    with hR
  have hus : (g.load t (.load t a bs)).us = g.us ++ [(R, bs)] := rfl
  have hE : ∀ u < n, uev (g.load t (.load t a bs)).us u = uev g.us u := fun u hu => by
    rw [hus, uev_append_lt hu]
  have hEn : uev (g.load t (.load t a bs)).us n = R := by
    rw [hus]; simpa using uev_append_len (us := g.us) (v := [(R, bs)]) (j := 0) (by simp)
  have hRR : R.isR = true := rfl
  have hRW : R.isW = false := rfl
  have hRl : R.locked = false := rfl
  have oldpos : ∀ u < n, (uev g.us u).tid = t → (uev g.us u).pos < R.pos := by
    intro u hu ht
    have := H.book.posLt u hu
    rw [ht] at this; exact this
  have hlen : (g.load t (.load t a bs)).us.length = n + 1 := by rw [hus]; simp [hn]
  have woLt : ∀ w ∈ g.wo, w < n := fun w hw => (H.woW w hw).1
  have tbLt : ∀ t' w, w ∈ g.tb t' → w < n := fun t' w hw => (H.tbOk t' w hw).1
  -- cases on a unit index of the new history
  have cases' : ∀ u < (g.load t (.load t a bs)).us.length,
      (u < n ∧ uev (g.load t (.load t a bs)).us u = uev g.us u) ∨
        (u = n ∧ uev (g.load t (.load t a bs)).us u = R) := fun u hu => by
    rw [hus] at hu ⊢; exact uev_cases1 hu
  have he_old : ∀ u < n, (g.load t (.load t a bs)).e u = g.e u := fun u hu => by
    simp [G.load, ← hn, show u ≠ n by omega]
  have he_new : (g.load t (.load t a bs)).e n = g.clk := by simp [G.load, ← hn]
  have hrf_old : ∀ r < n, (g.load t (.load t a bs)).rf r = g.rf r := fun r hr => by
    funext y; simp [G.load, ← hn, show r ≠ n by omega]
  have hrfn : ∀ y, (g.load t (.load t a bs)).rf n y =
      (lastCov g.us (g.tb t) y).or (lastCov g.us g.wo y) := fun y => by simp [G.load, ← hn]
  have hFB : ∀ r < n, ∀ w, FB (g.load t (.load t a bs)) w (g.e r) ↔
      w < n ∧ FB g w (g.e r) := fun r hr w =>
    fb_ext (le_of_lt (H.eLt r hr)) (fun w hw => ⟨hw, rfl⟩) (fun w hw => .inl hw) woLt w
  refine ⟨book_exec H.book hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- poE
    intro u hu w hw htd hp
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨hu, heu⟩
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨hw, hew⟩
      · rw [heu, hew] at htd hp
        rw [he_old u hu, he_old w hw]; exact H.poE u hu w hw htd hp
      · subst hw; rw [he_old u hu, he_new]; exact H.eLt u hu
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨hw, hew⟩
      · rw [heu, hew] at htd hp
        have := oldpos w hw htd.symm; omega
      · subst hu hw; omega
  · -- eLt
    intro u hu
    rcases cases' u hu with ⟨hu, -⟩ | ⟨rfl, -⟩
    · rw [he_old u hu]; have := H.eLt u hu; simp only [G.load]; omega
    · rw [he_new]; simp [G.load]
  · -- woW
    intro w hw
    have := H.woW w hw
    exact ⟨by omega, by rw [hE w this.1]; exact this.2⟩
  · -- woF
    intro w hw
    have := H.woF w hw
    refine ⟨by simp only [G.load]; omega, ?_⟩
    rw [he_old w (woLt w hw)]; exact this.2
  · exact H.woSorted
  · -- fifo
    intro u hu w hw hWu hWw htd hp hwo
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨rfl, heu⟩
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
      · simp only [heu, hew] at hWu hWw htd hp
        exact H.fifo u hu w hw hWu hWw htd hp hwo
      · rw [hew] at hWw; simp [hRW] at hWw
    · rw [heu] at hWu; simp [hRW] at hWu
  · -- tbOk
    intro t' w hw
    obtain ⟨h1, h2, h3, h4, h5⟩ := H.tbOk t' w hw
    exact ⟨by omega, by rw [hE w h1]; exact h2, by rw [hE w h1]; exact h3,
      by rw [hE w h1]; exact h4, h5⟩
  · -- tbSorted
    intro t'
    refine (H.tbSorted t').imp_of_mem ?_
    intro u w hu hw h
    rw [hE u (tbLt t' u hu), hE w (tbLt t' w hw)]; exact h
  · -- wAll
    intro w hw hW
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW ⊢; exact H.wAll w hw hW
    · rw [hew] at hW; simp [hRW] at hW
  · -- buf
    intro t'
    rw [H.buf t']
    apply List.map_congr_left
    intro w hw
    rw [hE w (tbLt t' w hw)]
  · -- mem
    intro y
    rw [H.mem y]
    show _ = match lastCov (g.us ++ [(R, bs)]) g.wo y with
      | none => init y
      | some w => some ((uev (g.us ++ [(R, bs)]) w).byte y)
    rw [lastCov_append y woLt]
    cases h : lastCov g.us g.wo y with
    | none => rfl
    | some w => simp only; rw [uev_append_lt (woLt w (lastCov_mem h).1)]
  · -- lockedW
    intro w hw hW hL
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW hL
      have := H.lockedW w hw hW hL
      exact ⟨this.1, by rw [he_old w hw]; exact this.2⟩
    · rw [hew] at hW; simp [hRW] at hW
  · -- drain
    intro u hu w hw hW htd hp hk
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨rfl, heu⟩
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
      · simp only [heu, hew] at hW htd hp hk
        rw [he_old u hu]
        exact H.drain u hu w hw hW htd hp hk
      · rw [hew] at hW; simp [hRW] at hW
    · rw [heu] at hk; simp [R, Ev.isFence, Ev.isA] at hk
  · -- rmwOk
    intro q hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H.rmwOk q hq
    exact ⟨by omega, by omega, by rw [hE _ h1]; exact h3, by rw [hE _ h2]; exact h4,
      by rw [hE _ h1, hE _ h2]; exact h5, h6, by rw [he_old _ h1]; exact h7⟩
  · -- clash
    intro r hr hR' w hw
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, -⟩
    · rw [her] at hR'; rw [he_old r hr]; exact H.clash r hr hR' w hw
    · rw [he_new]; exact Nat.ne_of_lt (H.woF w hw).1
  · -- rfW
    intro r y w hrw
    simp only [G.load] at hrw
    split at hrw
    · cases h1 : lastCov g.us (g.tb t) y with
      | some s =>
        rw [h1] at hrw; cases hrw
        obtain ⟨hm, hc⟩ := lastCov_mem h1
        obtain ⟨h1, h2, -⟩ := H.tbOk t _ hm
        exact ⟨by omega, by rw [hE _ h1]; exact h2, by rw [hE _ h1]; exact hc⟩
      | none =>
        rw [h1] at hrw
        simp only [Option.none_or] at hrw
        obtain ⟨hm, hc⟩ := lastCov_mem hrw
        obtain ⟨h1, h2⟩ := H.woW _ hm
        exact ⟨by omega, by rw [hE _ h1]; exact h2, by rw [hE _ h1]; exact hc⟩
    · obtain ⟨h1, h2, h3⟩ := H.rfW r y w hrw
      exact ⟨by omega, by rw [hE _ h1]; exact h2, by rw [hE _ h1]; exact h3⟩
  · -- rfInv
    intro r hr hR' y hy
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR' hy
      refine rfInv_ext hus hr (by rw [hrf_old r hr]) (he_old r hr) (hFB r hr) (fun _ _ => rfl)
        ?_ (H.rfInv r hr hR' y hy)
      intro w hw hge htd
      rcases cases' w hw with ⟨hw, -⟩ | ⟨rfl, hew⟩
      · omega
      · rw [hew] at htd ⊢; have := oldpos r hr htd.symm; exact this
    · -- the new read
      rw [her] at hy
      have hFBn : ∀ w, FB (g.load t (.load t a bs)) w g.clk ↔ w ∈ g.wo := fun w =>
        ⟨fun h => h.1, fun h => ⟨h, (H.woF w h).1⟩⟩
      unfold RfInv
      rw [her, he_new, hlen]
      rw [hrfn]
      -- old writes of thread `t` are in memory or in `t`'s buffer
      have own : ∀ w < n + 1, (uev (g.load t (.load t a bs)).us w).isW = true →
          (uev (g.load t (.load t a bs)).us w).tid = t →
          w < n ∧ (w ∈ g.wo ∨ w ∈ g.tb t) := by
        intro w hw hW htd
        rcases cases' w (by omega) with ⟨hw, hew⟩ | ⟨rfl, hew⟩
        · rw [hew] at hW htd
          have := H.wAll w hw hW
          rw [htd] at this; exact ⟨hw, this⟩
        · rw [hew] at hW; simp [hRW] at hW
      cases h1 : lastCov g.us (g.tb t) y with
      | some s =>
        simp only [Option.some_or]
        obtain ⟨hm, hc⟩ := lastCov_mem h1
        obtain ⟨hs, hW, htd, -, hnwo⟩ := H.tbOk t s hm
        refine ⟨by omega, by rw [hE s hs]; exact hW, by rw [hE s hs]; exact hc, .inl ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
        · rw [hE s hs]; exact htd
        · rw [hE s hs]; exact oldpos s hs htd
        · rw [hFBn]; exact hnwo
        · intro w hw hW' hc' htd' hp' hnf
          obtain ⟨hw', hmem⟩ := own w hw hW' htd'
          rw [hFBn] at hnf
          rcases hmem with hmem | hmem
          · exact absurd hmem hnf
          · rw [hE w hw'] at hc' ⊢; rw [hE s hs]
            rcases lastCov_max (H.tbSorted t) h1 hmem hc' with rfl | hlt
            · exact le_refl _
            · exact le_of_lt hlt
      | none =>
        simp only [Option.none_or]
        cases h2 : lastCov g.us g.wo y with
        | some s =>
          obtain ⟨hm, hc⟩ := lastCov_mem h2
          obtain ⟨hs, hW⟩ := H.woW s hm
          refine ⟨by omega, by rw [hE s hs]; exact hW, by rw [hE s hs]; exact hc,
            .inr ⟨(hFBn s).mpr hm, ?_, ?_⟩⟩
          · intro w hw hW' hc' hfb
            rw [hFBn] at hfb
            have hw' := woLt w hfb
            rw [hE w hw'] at hc'
            rcases lastCov_max H.woSorted h2 hfb hc' with rfl | hlt
            · exact le_refl _
            · exact le_of_lt hlt
          · intro w hw hW' hc' htd' hp'
            obtain ⟨hw', hmem⟩ := own w hw hW' htd'
            rw [hFBn]
            rcases hmem with hmem | hmem
            · exact hmem
            · rw [hE w hw'] at hc'; exact (lastCov_none h1 hmem hc').elim
        | none =>
          intro w hw hW' hc'
          refine ⟨fun hfb => ?_, fun hh => ?_⟩
          · rw [hFBn] at hfb
            rw [hE w (woLt w hfb)] at hc'
            exact lastCov_none h2 hfb hc'
          · obtain ⟨hw', hmem⟩ := own w hw hW' hh.1
            rw [hE w hw'] at hc'
            rcases hmem with hmem | hmem
            · exact lastCov_none h2 hmem hc'
            · exact lastCov_none h1 hmem hc'
  · -- vals
    intro r hr hR'
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR'
      obtain ⟨h1, h2⟩ := vals_ext hus hr (hrf_old r hr) (fun y w h => (H.rfW r y w h).1)
        (fun y => (init y).getD 0)
      rw [h1, h2]; exact H.vals r hr hR'
    · -- the new read returns what the machine read
      have hgd : (g.load t (.load t a bs)).us.getD n (dflt, []) = (R, bs) := by
        rw [hus]; simp [List.getD_eq_getElem?_getD, ← hn]
      rw [hgd]
      obtain ⟨hl, hj⟩ := readMem_some hv
      simp only [Exec.readBytes]
      have hEn' : (g.load t (.load t a bs)).x.evN n = R := hEn
      rw [hEn']
      -- unfold the view of thread `t`
      have hview : ∀ y, viewMem c.st t y = ((lastCov g.us (g.tb t) y).map fun w =>
          (uev g.us w).byte y).or (c.st.memory y) := by
        intro y
        simp only [viewMem]
        rw [H.buf t, readBufByte_eq y _ (fun w hw =>
          H.book.dataLen w (tbLt t w hw) (H.tbOk t w hw).2.1)]
      apply List.ext_getElem
      · simp [R, Ev.bytes]
      intro j hj1 hj2
      simp only [List.getElem_map, R, Ev.bytes, List.getElem_range', Nat.one_mul]
      have hjv := hj j (by omega)
      rw [hview] at hjv
      simp only [Exec.readByte]
      change (match (g.load t (.load t a bs)).rf n (a + j) with
        | none => (init (a + j)).getD 0
        | some w => (uev (g.load t (.load t a bs)).us w).byte (a + j)) = _
      rw [hrfn]
      rw [List.getElem?_eq_getElem (by omega)] at hjv
      cases h1 : lastCov g.us (g.tb t) (a + j) with
      | some s =>
        rw [h1] at hjv
        simp only [Option.map_some, Option.some_or, Option.some.injEq] at hjv
        simp only [Option.some_or]
        rw [hE s (tbLt t s (lastCov_mem h1).1), hjv]
      | none =>
        rw [h1] at hjv
        simp only [Option.map_none, Option.none_or] at hjv
        rw [H.mem] at hjv
        simp only [Option.none_or]
        cases h2 : lastCov g.us g.wo (a + j) with
        | some s =>
          rw [h2] at hjv
          simp only [Option.some.injEq] at hjv
          simp only
          rw [hE s (woLt s (lastCov_mem h2).1), hjv]
        | none =>
          rw [h2] at hjv
          simp only at hjv
          rw [hjv]; rfl

/-- Executing event `ev` of thread `i` as a store (it enters `i`'s buffer). -/
def G.store (g : G) (i : Nat) (ev : XEvent Nat) : G :=
  { g with
    us := g.us ++ evUnits i (g.cnt i) ev
    tb := fun t => if t = i then g.tb i ++ [g.us.length] else g.tb t
    e := fun u => if u = g.us.length then g.clk else g.e u
    cnt := bump g.cnt i
    clk := g.clk + 1 }

theorem inv_store {P : List (List (XEvent Nat))} {init : Tso.Mem} {c : ACfg} {g : G}
    (H : Inv P init c g) {i t a : Nat} {bs : List Byte} {es : List (XEvent Nat)}
    (hr : c.rest[i]? = some (.store t a bs :: es)) (ht : t = i) :
    Inv P init ⟨c.rest.set i es, enqueue c.st t a bs⟩ (g.store i (.store t a bs)) := by
  subst ht
  set n := g.us.length with hn
  set W : Ev :=
    { tid := t, pos := 2 * g.cnt t, act := .write, addr := a, size := bs.length, data := bs }
    with hW
  set g' := g.store t (.store t a bs) with hg'
  have hus : g'.us = g.us ++ [(W, [])] := rfl
  have hE : ∀ u < n, uev g'.us u = uev g.us u := fun u hu => by
    rw [hus, uev_append_lt hu]
  have hWW : W.isW = true := rfl
  have hWR : W.isR = false := rfl
  have hWl : W.locked = false := rfl
  have oldpos : ∀ u < n, (uev g.us u).tid = t → (uev g.us u).pos < W.pos := by
    intro u hu ht
    have := H.book.posLt u hu
    rw [ht] at this; exact this
  have hlen : g'.us.length = n + 1 := by rw [hus]; simp [hn]
  have woLt : ∀ w ∈ g.wo, w < n := fun w hw => (H.woW w hw).1
  have tbLt : ∀ t' w, w ∈ g.tb t' → w < n := fun t' w hw => (H.tbOk t' w hw).1
  have cases' : ∀ u < g'.us.length,
      (u < n ∧ uev g'.us u = uev g.us u) ∨ (u = n ∧ uev g'.us u = W) := fun u hu => by
    rw [hus] at hu ⊢; exact uev_cases1 hu
  have he_old : ∀ u < n, g'.e u = g.e u := fun u hu => by
    simp [hg', G.store, ← hn, show u ≠ n by omega]
  have he_new : g'.e n = g.clk := by simp [hg', G.store, ← hn]
  have htb : ∀ t', g'.tb t' = if t' = t then g.tb t ++ [n] else g.tb t' := fun t' => rfl
  have hFB : ∀ r < n, ∀ w, FB g' w (g.e r) ↔ w < n ∧ FB g w (g.e r) := fun r hr w =>
    fb_ext (le_of_lt (H.eLt r hr)) (fun w hw => ⟨hw, rfl⟩) (fun w hw => .inl hw) woLt w
  refine ⟨book_exec H.book hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- poE
    intro u hu w hw htd hp
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨hu, heu⟩
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨hw, hew⟩
      · rw [heu, hew] at htd hp
        rw [he_old u hu, he_old w hw]; exact H.poE u hu w hw htd hp
      · subst hw; rw [he_old u hu, he_new]; exact H.eLt u hu
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨hw, hew⟩
      · rw [heu, hew] at htd hp
        have := oldpos w hw htd.symm; omega
      · subst hu hw; omega
  · -- eLt
    intro u hu
    rcases cases' u hu with ⟨hu, -⟩ | ⟨rfl, -⟩
    · rw [he_old u hu]; have := H.eLt u hu; simp only [hg', G.store]; omega
    · rw [he_new]; simp [hg', G.store]
  · -- woW
    intro w hw
    have := H.woW w hw
    exact ⟨by omega, by rw [hE w this.1]; exact this.2⟩
  · -- woF
    intro w hw
    have := H.woF w hw
    refine ⟨by simp only [hg', G.store]; omega, ?_⟩
    rw [he_old w (woLt w hw)]; exact this.2
  · exact H.woSorted
  · -- fifo
    intro u hu w hw hWu hWw htd hp hwo
    have hw' := woLt w hwo
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨hu, heu⟩
    · simp only [heu, hE w hw'] at hWu hWw htd hp
      exact H.fifo u hu w hw' hWu hWw htd hp hwo
    · subst hu
      simp only [heu, hE w hw'] at htd hp
      have := oldpos w hw' htd.symm; omega
  · -- tbOk
    intro t' w hw
    rw [htb] at hw
    split at hw
    · next h =>
      subst h
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨h1, h2, h3, h4, h5⟩ := H.tbOk t' w hw
        exact ⟨by omega, by rw [hE w h1]; exact h2, by rw [hE w h1]; exact h3,
          by rw [hE w h1]; exact h4, h5⟩
      · simp only [List.mem_singleton] at hw
        subst hw
        have hEn : uev g'.us n = W := by
          rcases cases' n (by omega) with ⟨h, -⟩ | ⟨-, h⟩
          · omega
          · exact h
        exact ⟨by omega, by rw [hEn]; exact hWW, by rw [hEn], by rw [hEn],
          fun h => by have := woLt _ h; omega⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := H.tbOk t' w hw
      exact ⟨by omega, by rw [hE w h1]; exact h2, by rw [hE w h1]; exact h3,
        by rw [hE w h1]; exact h4, h5⟩
  · -- tbSorted
    intro t'
    rw [htb]
    have old : (g.tb t').Pairwise fun a b => (uev g'.us a).pos < (uev g'.us b).pos := by
      refine (H.tbSorted t').imp_of_mem ?_
      intro u w hu hw h
      rw [hE u (tbLt t' u hu), hE w (tbLt t' w hw)]; exact h
    split
    · next h =>
      subst h
      rw [List.pairwise_append]
      refine ⟨old, by simp, ?_⟩
      intro u hu w hw
      simp only [List.mem_singleton] at hw
      subst hw
      have hEn : uev g'.us n = W := by
        rcases cases' n (by omega) with ⟨h, -⟩ | ⟨-, h⟩
        · omega
        · exact h
      have hu' := tbLt t' u hu
      rw [hEn, hE u hu']
      exact oldpos u hu' (H.tbOk t' u hu).2.2.1
    · exact old
  · -- wAll
    intro w hw hW'
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW' ⊢
      rw [htb]
      rcases H.wAll w hw hW' with h | h
      · exact .inl h
      · right; split
        · next h' => rw [h'] at h; exact List.mem_append_left _ h
        · exact h
    · rw [hew, htb]; right; simp [W]
  · -- buf
    intro t'
    show Function.update c.st.buffer t (c.st.buffer t ++ [(a, bs)]) t' = _
    rw [htb]
    by_cases h : t' = t
    · subst h
      rw [Function.update_self]
      simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
      rw [H.buf t']
      have hEn : uev g'.us n = W := by
        rcases cases' n (by omega) with ⟨h, -⟩ | ⟨-, h⟩
        · omega
        · exact h
      rw [hEn]
      congr 1
      apply List.map_congr_left
      intro w hw
      rw [hE w (tbLt t' w hw)]
    · rw [Function.update_of_ne h]
      simp only [h, ↓reduceIte]
      rw [H.buf t']
      apply List.map_congr_left
      intro w hw
      rw [hE w (tbLt t' w hw)]
  · -- mem
    intro y
    rw [show (enqueue c.st t a bs).memory = c.st.memory from rfl, H.mem y]
    show _ = match lastCov (g.us ++ [(W, [])]) g.wo y with
      | none => init y
      | some w => some ((uev (g.us ++ [(W, [])]) w).byte y)
    rw [lastCov_append y woLt]
    cases h : lastCov g.us g.wo y with
    | none => rfl
    | some w => simp only; rw [uev_append_lt (woLt w (lastCov_mem h).1)]
  · -- lockedW
    intro w hw hW' hL
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW' hL
      have := H.lockedW w hw hW' hL
      exact ⟨this.1, by rw [he_old w hw]; exact this.2⟩
    · rw [hew] at hL; simp [hWl] at hL
  · -- drain
    intro u hu w hw hW' htd hp hk
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨hu, heu⟩
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨hw, hew⟩
      · simp only [heu, hew] at hW' htd hp hk
        rw [he_old u hu]
        exact H.drain u hu w hw hW' htd hp hk
      · subst hw
        simp only [heu, hew] at htd hp
        have := oldpos u hu htd.symm; omega
    · rw [heu] at hk; simp [W, Ev.isFence, Ev.isA] at hk
  · -- rmwOk
    intro q hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H.rmwOk q hq
    exact ⟨by omega, by omega, by rw [hE _ h1]; exact h3, by rw [hE _ h2]; exact h4,
      by rw [hE _ h1, hE _ h2]; exact h5, h6, by rw [he_old _ h1]; exact h7⟩
  · -- clash
    intro r hr hR' w hw
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR'; rw [he_old r hr]; exact H.clash r hr hR' w hw
    · rw [her] at hR'; simp [hWR] at hR'
  · -- rfW
    intro r y w hrw
    obtain ⟨h1, h2, h3⟩ := H.rfW r y w hrw
    exact ⟨by omega, by rw [hE _ h1]; exact h2, by rw [hE _ h1]; exact h3⟩
  · -- rfInv
    intro r hr hR' y hy
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR' hy
      refine rfInv_ext hus hr rfl (he_old r hr) (hFB r hr) (fun _ _ => rfl)
        ?_ (H.rfInv r hr hR' y hy)
      intro w hw hge htd
      rcases cases' w hw with ⟨hw, -⟩ | ⟨rfl, hew⟩
      · omega
      · rw [hew] at htd ⊢; exact oldpos r hr htd.symm
    · rw [her] at hR'; simp [hWR] at hR'
  · -- vals
    intro r hr hR'
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR'
      obtain ⟨h1, h2⟩ := vals_ext hus hr rfl (fun y w h => (H.rfW r y w h).1)
        (fun y => (init y).getD 0)
      rw [h1, h2]; exact H.vals r hr hR'
    · rw [her] at hR'; simp [hWR] at hR'

/-- Executing event `ev` of thread `i` as an `mfence`. -/
def G.fence (g : G) (i : Nat) (ev : XEvent Nat) : G :=
  { g with
    us := g.us ++ evUnits i (g.cnt i) ev
    e := fun u => if u = g.us.length then g.clk else g.e u
    cnt := bump g.cnt i
    clk := g.clk + 1 }

theorem inv_fence {P : List (List (XEvent Nat))} {init : Tso.Mem} {c : ACfg} {g : G}
    (H : Inv P init c g) {i t : Nat} {es : List (XEvent Nat)}
    (hr : c.rest[i]? = some (.fence t :: es)) (ht : t = i) (hb : c.st.buffer t = []) :
    Inv P init ⟨c.rest.set i es, c.st⟩ (g.fence i (.fence t)) := by
  subst ht
  set n := g.us.length with hn
  set F : Ev := { tid := t, pos := 2 * g.cnt t, act := .fence .mfence } with hF
  set g' := g.fence t (.fence t) with hg'
  have hus : g'.us = g.us ++ [(F, [])] := rfl
  have hE : ∀ u < n, uev g'.us u = uev g.us u := fun u hu => by
    rw [hus, uev_append_lt hu]
  have hFW : F.isW = false := rfl
  have hFR : F.isR = false := rfl
  have oldpos : ∀ u < n, (uev g.us u).tid = t → (uev g.us u).pos < F.pos := by
    intro u hu ht
    have := H.book.posLt u hu
    rw [ht] at this; exact this
  have woLt : ∀ w ∈ g.wo, w < n := fun w hw => (H.woW w hw).1
  have tbLt : ∀ t' w, w ∈ g.tb t' → w < n := fun t' w hw => (H.tbOk t' w hw).1
  have htbt : g.tb t = [] := by
    have := H.buf t; rw [hb] at this
    exact List.map_eq_nil_iff.mp this.symm
  have cases' : ∀ u < g'.us.length,
      (u < n ∧ uev g'.us u = uev g.us u) ∨ (u = n ∧ uev g'.us u = F) := fun u hu => by
    rw [hus] at hu ⊢; exact uev_cases1 hu
  have he_old : ∀ u < n, g'.e u = g.e u := fun u hu => by
    simp [hg', G.fence, ← hn, show u ≠ n by omega]
  have he_new : g'.e n = g.clk := by simp [hg', G.fence, ← hn]
  have hFB : ∀ r < n, ∀ w, FB g' w (g.e r) ↔ w < n ∧ FB g w (g.e r) := fun r hr w =>
    fb_ext (le_of_lt (H.eLt r hr)) (fun w hw => ⟨hw, rfl⟩) (fun w hw => .inl hw) woLt w
  refine ⟨book_exec H.book hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- poE
    intro u hu w hw htd hp
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨hu, heu⟩
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨hw, hew⟩
      · rw [heu, hew] at htd hp
        rw [he_old u hu, he_old w hw]; exact H.poE u hu w hw htd hp
      · subst hw; rw [he_old u hu, he_new]; exact H.eLt u hu
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨hw, hew⟩
      · rw [heu, hew] at htd hp
        have := oldpos w hw htd.symm; omega
      · subst hu hw; omega
  · -- eLt
    intro u hu
    rcases cases' u hu with ⟨hu, -⟩ | ⟨rfl, -⟩
    · rw [he_old u hu]; have := H.eLt u hu; simp only [hg', G.fence]; omega
    · rw [he_new]; simp [hg', G.fence]
  · -- woW
    intro w hw
    have := H.woW w hw
    exact ⟨by simp [hus]; omega, by rw [hE w this.1]; exact this.2⟩
  · -- woF
    intro w hw
    have := H.woF w hw
    refine ⟨by simp only [hg', G.fence]; omega, ?_⟩
    rw [he_old w (woLt w hw)]; exact this.2
  · exact H.woSorted
  · -- fifo
    intro u hu w hw hWu hWw htd hp hwo
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨rfl, heu⟩
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
      · simp only [heu, hew] at hWu hWw htd hp
        exact H.fifo u hu w hw hWu hWw htd hp hwo
      · rw [hew] at hWw; simp [hFW] at hWw
    · rw [heu] at hWu; simp [hFW] at hWu
  · -- tbOk
    intro t' w hw
    obtain ⟨h1, h2, h3, h4, h5⟩ := H.tbOk t' w hw
    exact ⟨by simp [hus]; omega, by rw [hE w h1]; exact h2, by rw [hE w h1]; exact h3,
      by rw [hE w h1]; exact h4, h5⟩
  · -- tbSorted
    intro t'
    refine (H.tbSorted t').imp_of_mem ?_
    intro u w hu hw h
    rw [hE u (tbLt t' u hu), hE w (tbLt t' w hw)]; exact h
  · -- wAll
    intro w hw hW'
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW' ⊢; exact H.wAll w hw hW'
    · rw [hew] at hW'; simp [hFW] at hW'
  · -- buf
    intro t'
    rw [H.buf t']
    apply List.map_congr_left
    intro w hw
    rw [hE w (tbLt t' w hw)]
  · -- mem
    intro y
    rw [H.mem y]
    show _ = match lastCov (g.us ++ [(F, [])]) g.wo y with
      | none => init y
      | some w => some ((uev (g.us ++ [(F, [])]) w).byte y)
    rw [lastCov_append y woLt]
    cases h : lastCov g.us g.wo y with
    | none => rfl
    | some w => simp only; rw [uev_append_lt (woLt w (lastCov_mem h).1)]
  · -- lockedW
    intro w hw hW' hL
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW' hL
      have := H.lockedW w hw hW' hL
      exact ⟨this.1, by rw [he_old w hw]; exact this.2⟩
    · rw [hew] at hW'; simp [hFW] at hW'
  · -- drain
    intro u hu w hw hW' htd hp hk
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨hu, heu⟩
    · rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
      · simp only [heu, hew] at hW' htd hp hk
        rw [he_old u hu]
        exact H.drain u hu w hw hW' htd hp hk
      · rw [hew] at hW'; simp [hFW] at hW'
    · -- the fence: its thread's buffer is empty
      subst hu
      rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩
      · simp only [heu, hew] at hW' htd
        rcases H.wAll w hw hW' with h | h
        · rw [he_new]; exact ⟨h, (H.woF w h).1⟩
        · rw [htd, htbt] at h; simp at h
      · rw [hew] at hW'; simp [hFW] at hW'
  · -- rmwOk
    intro q hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H.rmwOk q hq
    exact ⟨by simp [hus]; omega, by simp [hus]; omega, by rw [hE _ h1]; exact h3,
      by rw [hE _ h2]; exact h4, by rw [hE _ h1, hE _ h2]; exact h5, h6,
      by rw [he_old _ h1]; exact h7⟩
  · -- clash
    intro r hr hR' w hw
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR'; rw [he_old r hr]; exact H.clash r hr hR' w hw
    · rw [her] at hR'; simp [hFR] at hR'
  · -- rfW
    intro r y w hrw
    obtain ⟨h1, h2, h3⟩ := H.rfW r y w hrw
    exact ⟨by simp [hus]; omega, by rw [hE _ h1]; exact h2, by rw [hE _ h1]; exact h3⟩
  · -- rfInv
    intro r hr hR' y hy
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR' hy
      refine rfInv_ext hus hr rfl (he_old r hr) (hFB r hr) (fun _ _ => rfl)
        ?_ (H.rfInv r hr hR' y hy)
      intro w hw hge htd
      rcases cases' w hw with ⟨hw, -⟩ | ⟨rfl, hew⟩
      · omega
      · rw [hew] at htd ⊢; exact oldpos r hr htd.symm
    · rw [her] at hR'; simp [hFR] at hR'
  · -- vals
    intro r hr hR'
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR'
      obtain ⟨h1, h2⟩ := vals_ext hus hr rfl (fun y w h => (H.rfW r y w h).1)
        (fun y => (init y).getD 0)
      rw [h1, h2]; exact H.vals r hr hR'
    · rw [her] at hR'; simp [hFR] at hR'

theorem lastCov_snoc (us : List (Ev × List Byte)) (l : List Nat) (w y : Nat) :
    lastCov us (l ++ [w]) y = if (uev us w).covers y then some w else lastCov us l y := by
  unfold lastCov
  rw [List.filter_append]
  by_cases h : (uev us w).covers y = true
  · simp [h]
  · simp [h]

theorem uev_cases2 {us : List (Ev × List Byte)} {p q : Ev × List Byte} {u : Nat}
    (hu : u < (us ++ [p, q]).length) :
    (u < us.length ∧ uev (us ++ [p, q]) u = uev us u) ∨
      (u = us.length ∧ uev (us ++ [p, q]) u = p.1) ∨
      (u = us.length + 1 ∧ uev (us ++ [p, q]) u = q.1) := by
  rcases uev_cases hu with h | ⟨j, hj, rfl, he⟩
  · exact .inl h
  · simp only [List.length_cons, List.length_nil] at hj
    match j, hj with
    | 0, _ => exact .inr (.inl ⟨rfl, by simpa using he⟩)
    | 1, _ => exact .inr (.inr ⟨rfl, by simpa using he⟩)

/-- Executing event `ev` of thread `i` as a locked read-modify-write: the read at the current
tick, the write executing and reaching memory at the next. -/
def G.rmwStep (g : G) (i : Nat) (ev : XEvent Nat) : G :=
  { g with
    us := g.us ++ evUnits i (g.cnt i) ev
    rf := fun r y => if r = g.us.length then lastCov g.us g.wo y else g.rf r y
    rmw := g.rmw ++ [(g.us.length, g.us.length + 1)]
    e := fun u => if u = g.us.length then g.clk else if u = g.us.length + 1 then g.clk + 1
      else g.e u
    f := fun u => if u = g.us.length + 1 then g.clk + 1 else g.f u
    wo := g.wo ++ [g.us.length + 1]
    cnt := bump g.cnt i
    clk := g.clk + 2 }

theorem inv_rmw {P : List (List (XEvent Nat))} {init : Tso.Mem} {c : ACfg} {g : G}
    (H : Inv P init c g) {i t a : Nat} {old new : List Byte} {es : List (XEvent Nat)}
    (hr : c.rest[i]? = some (.rmw t a old new :: es)) (ht : t = i) (hb : c.st.buffer t = [])
    (hm : readMem c.st.memory a old.length = some old) :
    Inv P init ⟨c.rest.set i es, { c.st with memory := writeMem c.st.memory a new }⟩
      (g.rmwStep i (.rmw t a old new)) := by
  subst ht
  set n := g.us.length with hn
  set Rd : Ev :=
    { tid := t, pos := 2 * g.cnt t, act := .read, addr := a, size := old.length, locked := true }
    with hRd
  set Wr : Ev :=
    { tid := t, pos := 2 * g.cnt t + 1, act := .write, addr := a, size := new.length,
      locked := true, data := new }
    with hWr
  set g' := g.rmwStep t (.rmw t a old new) with hg'
  have hus : g'.us = g.us ++ [(Rd, old), (Wr, [])] := rfl
  have hE : ∀ u < n, uev g'.us u = uev g.us u := fun u hu => by
    rw [hus, uev_append_lt hu]
  have hlen : g'.us.length = n + 2 := by rw [hus]; simp [hn]
  have oldpos : ∀ u < n, (uev g.us u).tid = t → (uev g.us u).pos < 2 * g.cnt t := by
    intro u hu ht
    have := H.book.posLt u hu
    rw [ht] at this; exact this
  have woLt : ∀ w ∈ g.wo, w < n := fun w hw => (H.woW w hw).1
  have tbLt : ∀ t' w, w ∈ g.tb t' → w < n := fun t' w hw => (H.tbOk t' w hw).1
  have htbt : g.tb t = [] := by
    have := H.buf t; rw [hb] at this
    exact List.map_eq_nil_iff.mp this.symm
  have cases' : ∀ u < g'.us.length,
      (u < n ∧ uev g'.us u = uev g.us u) ∨ (u = n ∧ uev g'.us u = Rd) ∨
        (u = n + 1 ∧ uev g'.us u = Wr) := fun u hu => by
    rw [hus] at hu ⊢; exact uev_cases2 hu
  have hEn : uev g'.us n = Rd := by
    rcases cases' n (by omega) with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · exact h
    · omega
  have hEn1 : uev g'.us (n + 1) = Wr := by
    rcases cases' (n + 1) (by omega) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · omega
    · exact h
  have he_old : ∀ u < n, g'.e u = g.e u := fun u hu => by
    simp [hg', G.rmwStep, ← hn, show u ≠ n by omega, show u ≠ n + 1 by omega]
  have he_n : g'.e n = g.clk := by simp [hg', G.rmwStep, ← hn]
  have he_n1 : g'.e (n + 1) = g.clk + 1 := by simp [hg', G.rmwStep, ← hn]
  have hf_old : ∀ u < n, g'.f u = g.f u := fun u hu => by
    simp [hg', G.rmwStep, ← hn, show u ≠ n + 1 by omega]
  have hf_n1 : g'.f (n + 1) = g.clk + 1 := by simp [hg', G.rmwStep, ← hn]
  have hwo : g'.wo = g.wo ++ [n + 1] := rfl
  have hrf_old : ∀ r < n, g'.rf r = g.rf r := fun r hr => by
    funext y; simp [hg', G.rmwStep, ← hn, show r ≠ n by omega]
  have hrfn : ∀ y, g'.rf n y = lastCov g.us g.wo y := fun y => by simp [hg', G.rmwStep, ← hn]
  have hclk : g'.clk = g.clk + 2 := rfl
  have hFB : ∀ r < n, ∀ w, FB g' w (g.e r) ↔ w < n ∧ FB g w (g.e r) := fun r hr w =>
    fb_ext (le_of_lt (H.eLt r hr)) (fun w hw => ⟨by rw [hwo]; exact List.mem_append_left _ hw,
      hf_old w (woLt w hw)⟩)
      (fun w hw => by
        rw [hwo] at hw
        rcases List.mem_append.mp hw with h | h
        · exact .inl h
        · simp only [List.mem_singleton] at h; subst h; right; rw [hf_n1]; omega) woLt w
  -- own earlier writes are in memory
  have ownwo : ∀ w < n, (uev g.us w).isW = true → (uev g.us w).tid = t → w ∈ g.wo := by
    intro w hw hW htd
    rcases H.wAll w hw hW with h | h
    · exact h
    · rw [htd, htbt] at h; simp at h
  have hWrd : Wr.data.length = Wr.size := rfl
  have hWrW : Wr.isW = true := rfl
  have hRdR : Rd.isR = true := rfl
  refine ⟨book_exec H.book hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- poE
    intro u hu w hw htd hp
    rcases cases' u hu with ⟨hu, heu⟩ | ⟨rfl, heu⟩ | ⟨rfl, heu⟩ <;>
      rcases cases' w hw with ⟨hw, hew⟩ | ⟨hw, hew⟩ | ⟨hw, hew⟩
    · simp only [heu, hew] at htd hp
      rw [he_old u hu, he_old w hw]; exact H.poE u hu w hw htd hp
    · subst hw; rw [he_old u hu, he_n]; exact H.eLt u hu
    · subst hw; rw [he_old u hu, he_n1]; have := H.eLt u hu; omega
    · simp only [heu, hew] at htd hp
      have := oldpos w hw htd.symm; simp [hRd] at hp; omega
    · subst hw; simp only [heu] at hp; omega
    · subst hw; rw [he_n, he_n1]; omega
    · simp only [heu, hew] at htd hp
      have := oldpos w hw htd.symm; simp [hWr] at hp; omega
    · subst hw; simp only [hEn, hEn1, hRd, hWr] at hp; omega
    · subst hw; simp only [heu] at hp; omega
  · -- eLt
    intro u hu
    rw [hclk]
    rcases cases' u hu with ⟨hu, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [he_old u hu]; have := H.eLt u hu; omega
    · rw [he_n]; omega
    · rw [he_n1]; omega
  · -- woW
    intro w hw
    rw [hwo] at hw
    rcases List.mem_append.mp hw with h | h
    · have := H.woW w h
      exact ⟨by omega, by rw [hE w this.1]; exact this.2⟩
    · simp only [List.mem_singleton] at h; subst h
      exact ⟨by omega, hEn1 ▸ hWrW⟩
  · -- woF
    intro w hw
    rw [hwo] at hw
    rw [hclk]
    rcases List.mem_append.mp hw with h | h
    · have := H.woF w h
      have hw' := woLt w h
      rw [hf_old w hw', he_old w hw']; omega
    · simp only [List.mem_singleton] at h; subst h
      rw [hf_n1, he_n1]; omega
  · -- woSorted
    rw [hwo, List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · refine H.woSorted.imp_of_mem ?_
      intro u w hu hw h
      rw [hf_old u (woLt u hu), hf_old w (woLt w hw)]; exact h
    · intro u hu w hw
      simp only [List.mem_singleton] at hw; subst hw
      rw [hf_old u (woLt u hu), hf_n1]
      have := (H.woF u hu).1; omega
  · -- fifo
    intro u hu w hw hWu hWw htd hp hwo'
    rw [hwo] at hwo'
    rcases List.mem_append.mp hwo' with hw' | hw'
    · have hwn := woLt w hw'
      rcases cases' u hu with ⟨hu, heu⟩ | ⟨rfl, heu⟩ | ⟨rfl, heu⟩
      · simp only [heu, hE w hwn] at hWu hWw htd hp
        obtain ⟨h1, h2⟩ := H.fifo u hu w hwn hWu hWw htd hp hw'
        exact ⟨by rw [hwo]; exact List.mem_append_left _ h1,
          by rw [hf_old u hu, hf_old w hwn]; exact h2⟩
      · simp only [heu, hE w hwn] at htd hp
        have := oldpos w hwn htd.symm; simp [hRd] at hp; omega
      · simp only [heu, hE w hwn] at htd hp
        have := oldpos w hwn htd.symm; simp [hWr] at hp; omega
    · simp only [List.mem_singleton] at hw'; subst hw'
      rcases cases' u hu with ⟨hu, heu⟩ | ⟨rfl, heu⟩ | ⟨rfl, heu⟩
      · simp only [heu, hEn1] at hWu htd
        have h1 := ownwo u hu hWu htd
        exact ⟨by rw [hwo]; exact List.mem_append_left _ h1,
          by rw [hf_old u hu, hf_n1]; have := (H.woF u h1).1; omega⟩
      · rw [heu] at hWu; simp [hRd, Ev.isW] at hWu
      · omega
  · -- tbOk
    intro t' w hw
    obtain ⟨h1, h2, h3, h4, h5⟩ := H.tbOk t' w hw
    refine ⟨by omega, by rw [hE w h1]; exact h2, by rw [hE w h1]; exact h3,
      by rw [hE w h1]; exact h4, ?_⟩
    rw [hwo]; simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨h5, by omega⟩
  · -- tbSorted
    intro t'
    refine (H.tbSorted t').imp_of_mem ?_
    intro u w hu hw h
    rw [hE u (tbLt t' u hu), hE w (tbLt t' w hw)]; exact h
  · -- wAll
    intro w hw hW'
    rw [hwo]
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW' ⊢
      rcases H.wAll w hw hW' with h | h
      · exact .inl (List.mem_append_left _ h)
      · exact .inr h
    · rw [hew] at hW'; simp [hRd, Ev.isW] at hW'
    · exact .inl (List.mem_append_right _ (List.mem_singleton_self _))
  · -- buf
    intro t'
    rw [show ({ c.st with memory := writeMem c.st.memory a new } : XState Nat).buffer t' =
      c.st.buffer t' from rfl, H.buf t']
    apply List.map_congr_left
    intro w hw
    rw [hE w (tbLt t' w hw)]
  · -- mem
    intro y
    show writeMem c.st.memory a new y = match lastCov g'.us g'.wo y with
      | none => init y
      | some w => some ((uev g'.us w).byte y)
    rw [hwo, lastCov_snoc, hEn1]
    rw [show writeMem c.st.memory a new y = writeMem c.st.memory Wr.addr Wr.data y from rfl,
      writeMem_eq hWrd]
    split
    · simp only; rw [hEn1]
    · rw [hus, lastCov_append y woLt, H.mem y]
      cases h : lastCov g.us g.wo y with
      | none => rfl
      | some w => simp only; rw [uev_append_lt (woLt w (lastCov_mem h).1)]
  · -- lockedW
    intro w hw hW' hL
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW' hL
      have := H.lockedW w hw hW' hL
      exact ⟨by rw [hwo]; exact List.mem_append_left _ this.1,
        by rw [hf_old w hw, he_old w hw]; exact this.2⟩
    · rw [hew] at hW'; simp [hRd, Ev.isW] at hW'
    · exact ⟨by rw [hwo]; exact List.mem_append_right _ (List.mem_singleton_self _), by rw [hf_n1, he_n1]⟩
  · -- drain
    intro u hu w hw hW' htd hp hk
    rcases cases' w hw with ⟨hw, hew⟩ | ⟨rfl, hew⟩ | ⟨rfl, hew⟩
    · rw [hew] at hW' htd hp
      rcases cases' u hu with ⟨hu, heu⟩ | ⟨rfl, heu⟩ | ⟨rfl, heu⟩
      · simp only [heu] at htd hp hk
        obtain ⟨h1, h2⟩ := H.drain u hu w hw hW' htd hp hk
        exact ⟨by rw [hwo]; exact List.mem_append_left _ h1,
          by rw [hf_old w hw, he_old u hu]; exact h2⟩
      · rw [heu] at htd
        have h1 := ownwo w hw hW' htd
        exact ⟨by rw [hwo]; exact List.mem_append_left _ h1,
          by rw [hf_old w hw, he_n]; exact (H.woF w h1).1⟩
      · rw [heu] at htd
        have h1 := ownwo w hw hW' htd
        exact ⟨by rw [hwo]; exact List.mem_append_left _ h1,
          by rw [hf_old w hw, he_n1]; have := (H.woF w h1).1; omega⟩
    · rw [hew] at hW'; simp [hRd, Ev.isW] at hW'
    · rw [hew] at htd hp
      rcases cases' u hu with ⟨hu, heu⟩ | ⟨rfl, heu⟩ | ⟨rfl, heu⟩
      · rw [heu] at htd hp
        have := oldpos u hu htd.symm; simp [hWr] at hp; omega
      · rw [heu] at hp; simp only [hRd, hWr] at hp; omega
      · rw [hEn1] at hp; omega
  · -- rmwOk
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H.rmwOk q hq
      exact ⟨by omega, by omega, by rw [hE _ h1]; exact h3, by rw [hE _ h2]; exact h4,
        by rw [hE _ h1, hE _ h2]; exact h5, by rw [hwo]; exact List.mem_append_left _ h6,
        by rw [hf_old _ h2, he_old _ h1]; exact h7⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨by omega, by omega, hEn ▸ hRdR, hEn1 ▸ hWrW, by rw [hEn, hEn1],
        by rw [hwo]; exact List.mem_append_right _ (List.mem_singleton_self _), by rw [hf_n1, he_n]⟩
  · -- clash
    intro r hr hR' w hw
    rw [hwo] at hw
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR'
      rw [he_old r hr]
      rcases List.mem_append.mp hw with hw | hw
      · rw [hf_old w (woLt w hw)]; exact H.clash r hr hR' w hw
      · simp only [List.mem_singleton] at hw; subst hw
        rw [hf_n1]; have := H.eLt r hr; omega
    · rw [he_n]
      rcases List.mem_append.mp hw with hw | hw
      · rw [hf_old w (woLt w hw)]; exact Nat.ne_of_lt (H.woF w hw).1
      · simp only [List.mem_singleton] at hw; subst hw
        rw [hf_n1]; omega
    · rw [her] at hR'; simp [hWr, Ev.isR] at hR'
  · -- rfW
    intro r y w hrw
    by_cases hrn : r = n
    · subst hrn
      rw [hrfn] at hrw
      obtain ⟨hm, hc⟩ := lastCov_mem hrw
      obtain ⟨h1, h2⟩ := H.woW _ hm
      exact ⟨by omega, by rw [hE _ h1]; exact h2, by rw [hE _ h1]; exact hc⟩
    · have : g'.rf r y = g.rf r y := by simp [hg', G.rmwStep, ← hn, hrn]
      rw [this] at hrw
      obtain ⟨h1, h2, h3⟩ := H.rfW r y w hrw
      exact ⟨by omega, by rw [hE _ h1]; exact h2, by rw [hE _ h1]; exact h3⟩
  · -- rfInv
    intro r hr hR' y hy
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR' hy
      refine rfInv_ext hus hr (by rw [hrf_old r hr]) (he_old r hr) (hFB r hr)
        (fun w hw => hf_old w (woLt w hw)) ?_ (H.rfInv r hr hR' y hy)
      intro w hw hge htd
      rcases cases' w hw with ⟨hw, -⟩ | ⟨rfl, hew⟩ | ⟨rfl, hew⟩
      · omega
      · rw [hew] at htd ⊢; exact oldpos r hr htd.symm
      · rw [hew] at htd ⊢; have := oldpos r hr htd.symm; simp [hWr]; omega
    · -- the locked read: from memory
      rw [her] at hy
      have hFBn : ∀ w, FB g' w g.clk ↔ w ∈ g.wo := fun w => by
        constructor
        · rintro ⟨hw, hf⟩
          rw [hwo] at hw
          rcases List.mem_append.mp hw with hw | hw
          · exact hw
          · simp only [List.mem_singleton] at hw; subst hw; rw [hf_n1] at hf; omega
        · intro hw
          exact ⟨by rw [hwo]; exact List.mem_append_left _ hw,
            by rw [hf_old w (woLt w hw)]; exact (H.woF w hw).1⟩
      unfold RfInv
      rw [her, he_n, hlen, hrfn]
      have own : ∀ w < n + 2, (uev g'.us w).isW = true → (uev g'.us w).tid = t →
          (uev g'.us w).pos < Rd.pos → w < n ∧ w ∈ g.wo := by
        intro w hw hW htd hp
        rcases cases' w (by omega) with ⟨hw, hew⟩ | ⟨rfl, hew⟩ | ⟨rfl, hew⟩
        · rw [hew] at hW htd; exact ⟨hw, ownwo w hw hW htd⟩
        · rw [hew] at hW; simp [hRd, Ev.isW] at hW
        · rw [hew] at hp; simp only [hRd, hWr] at hp; omega
      cases h2 : lastCov g.us g.wo y with
      | some s =>
        obtain ⟨hm, hc⟩ := lastCov_mem h2
        obtain ⟨hs, hW⟩ := H.woW s hm
        refine ⟨by omega, by rw [hE s hs]; exact hW, by rw [hE s hs]; exact hc,
          .inr ⟨(hFBn s).mpr hm, ?_, ?_⟩⟩
        · intro w hw hW' hc' hfb
          rw [hFBn] at hfb
          have hw' := woLt w hfb
          rw [hE w hw'] at hc'
          rw [hf_old w hw', hf_old s hs]
          rcases lastCov_max H.woSorted h2 hfb hc' with rfl | hlt
          · exact le_refl _
          · exact le_of_lt hlt
        · intro w hw hW' hc' htd' hp'
          exact (hFBn w).mpr (own w hw hW' htd' hp').2
      | none =>
        intro w hw hW' hc'
        refine ⟨fun hfb => ?_, fun hh => ?_⟩
        · rw [hFBn] at hfb
          rw [hE w (woLt w hfb)] at hc'
          exact lastCov_none h2 hfb hc'
        · obtain ⟨hw', hmem⟩ := own w hw hW' hh.1 hh.2
          rw [hE w hw'] at hc'
          exact lastCov_none h2 hmem hc'
    · rw [her] at hR'; simp [hWr, Ev.isR] at hR'
  · -- vals
    intro r hr hR'
    rcases cases' r hr with ⟨hr, her⟩ | ⟨rfl, her⟩ | ⟨rfl, her⟩
    · rw [her] at hR'
      obtain ⟨h1, h2⟩ := vals_ext hus hr (hrf_old r hr) (fun y w h => (H.rfW r y w h).1)
        (fun y => (init y).getD 0)
      rw [h1, h2]; exact H.vals r hr hR'
    · have hgd : g'.us.getD n (dflt, []) = (Rd, old) := by
        rw [hus]; simp [List.getD_eq_getElem?_getD, ← hn]
      rw [hgd]
      obtain ⟨hl, hj⟩ := readMem_some hm
      simp only [Exec.readBytes]
      have hEn' : g'.x.evN n = Rd := hEn
      rw [hEn']
      apply List.ext_getElem
      · simp [Rd, Ev.bytes]
      intro j hj1 hj2
      simp only [List.getElem_map, Rd, Ev.bytes, List.getElem_range', Nat.one_mul]
      have hjv := hj j (by omega)
      simp only [Exec.readByte]
      change (match g'.rf n (a + j) with
        | none => (init (a + j)).getD 0
        | some w => (uev g'.us w).byte (a + j)) = _
      rw [hrfn]
      rw [List.getElem?_eq_getElem (by omega), H.mem] at hjv
      cases h2 : lastCov g.us g.wo (a + j) with
      | some s =>
        rw [h2] at hjv
        simp only [Option.some.injEq] at hjv
        simp only
        rw [hE s (woLt s (lastCov_mem h2).1), hjv]
      | none =>
        rw [h2] at hjv
        simp only at hjv
        simp only
        rw [hjv]; rfl
    · rw [her] at hR'; simp [hWr, Ev.isR] at hR'

/-- Thread `t`'s oldest buffered write `w` reaches memory. -/
def G.flush (g : G) (t w : Nat) : G :=
  { g with
    f := fun u => if u = w then g.clk else g.f u
    wo := g.wo ++ [w]
    tb := fun t' => if t' = t then (g.tb t).tail else g.tb t'
    clk := g.clk + 1 }

theorem inv_flush {P : List (List (XEvent Nat))} {init : Tso.Mem} {c : ACfg} {g : G}
    (H : Inv P init c g) {t a : Nat} {bs : List Byte} {rest : List (Nat × List Byte)}
    (hb : c.st.buffer t = (a, bs) :: rest) :
    ∃ g', Inv P init ⟨c.rest, ⟨writeMem c.st.memory a bs, Function.update c.st.buffer t rest⟩⟩ g' ∧
      g'.us = g.us ∧ g'.rmw = g.rmw := by
  have hbt := H.buf t
  rw [hb] at hbt
  cases htb : g.tb t with
  | nil => rw [htb] at hbt; cases hbt
  | cons w tbr =>
  rw [htb] at hbt
  simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hbt
  obtain ⟨⟨ha, hbs⟩, hrest⟩ := hbt
  refine ⟨g.flush t w, ?_, rfl, rfl⟩
  set n := g.us.length with hn
  set g' := g.flush t w with hg'
  have hwtb : w ∈ g.tb t := by rw [htb]; exact List.mem_cons_self
  obtain ⟨hwn, hwW, hwt, -, hwnwo⟩ := H.tbOk t w hwtb
  have woLt : ∀ v ∈ g.wo, v < n := fun v hv => (H.woW v hv).1
  have tbLt : ∀ t' v, v ∈ g.tb t' → v < n := fun t' v hv => (H.tbOk t' v hv).1
  have hus : g'.us = g.us := rfl
  have hwo : g'.wo = g.wo ++ [w] := rfl
  have hf_old : ∀ v ∈ g.wo, g'.f v = g.f v := fun v hv => by
    have hne : v ≠ w := by rintro rfl; exact hwnwo hv
    simp [hg', G.flush, hne]
  have hf_w : g'.f w = g.clk := by simp [hg', G.flush]
  have htb' : ∀ t', g'.tb t' = if t' = t then tbr else g.tb t' := fun t' => by
    simp only [hg', G.flush, htb, List.tail_cons]
  have hsorted := H.tbSorted t
  rw [htb, List.pairwise_cons] at hsorted
  have hwtbr : w ∉ tbr := fun h => by have := hsorted.1 w h; omega
  have hFB : ∀ r < n, ∀ v, FB g' v (g.e r) ↔ v < n ∧ FB g v (g.e r) := fun r hr v =>
    fb_ext (le_of_lt (H.eLt r hr))
      (fun v hv => ⟨by rw [hwo]; exact List.mem_append_left _ hv, hf_old v hv⟩)
      (fun v hv => by
        rw [hwo] at hv
        rcases List.mem_append.mp hv with h | h
        · exact .inl h
        · simp only [List.mem_singleton] at h; subst h; right; rw [hf_w]) woLt v
  have hwd : (uev g.us w).data.length = (uev g.us w).size := H.book.dataLen w hwn hwW
  refine ⟨H.book, H.poE, fun u hu => by have := H.eLt u hu; simp only [hg', G.flush]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- woW
    intro v hv
    rw [hwo] at hv
    rcases List.mem_append.mp hv with h | h
    · exact H.woW v h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨hwn, hwW⟩
  · -- woF
    intro v hv
    rw [hwo] at hv
    simp only [hg', G.flush]
    rcases List.mem_append.mp hv with h | h
    · have := H.woF v h
      have hne : v ≠ w := by rintro rfl; exact hwnwo h
      simp only [hne, ↓reduceIte]; omega
    · simp only [List.mem_singleton] at h; subst h
      simp only [↓reduceIte]
      have := H.eLt v hwn; omega
  · -- woSorted
    rw [hwo, List.pairwise_append]
    refine ⟨H.woSorted.imp_of_mem fun hu hv h => by rw [hf_old _ hu, hf_old _ hv]; exact h,
      by simp, ?_⟩
    intro u hu v hv
    simp only [List.mem_singleton] at hv; subst hv
    rw [hf_old u hu, hf_w]; exact (H.woF u hu).1
  · -- fifo
    intro u hu v hv hWu hWv htd hp hvwo
    simp only [hus] at hu hv hWu hWv htd hp
    rw [hwo] at hvwo
    rcases List.mem_append.mp hvwo with h | h
    · obtain ⟨h1, h2⟩ := H.fifo u hu v hv hWu hWv htd hp h
      exact ⟨by rw [hwo]; exact List.mem_append_left _ h1, by rw [hf_old u h1, hf_old v h]; exact h2⟩
    · simp only [List.mem_singleton] at h; subst h
      rcases H.wAll u hu hWu with h1 | h1
      · exact ⟨by rw [hwo]; exact List.mem_append_left _ h1,
          by rw [hf_old u h1, hf_w]; exact (H.woF u h1).1⟩
      · rw [htd, hwt, htb] at h1
        rcases List.mem_cons.mp h1 with h1 | h1
        · subst h1; omega
        · have := hsorted.1 u h1; omega
  · -- tbOk
    intro t' v hv
    rw [htb'] at hv
    split at hv
    · next h =>
      subst h
      have hv' : v ∈ g.tb t' := by rw [htb]; exact List.mem_cons_of_mem _ hv
      obtain ⟨h1, h2, h3, h4, h5⟩ := H.tbOk t' v hv'
      refine ⟨h1, h2, h3, h4, ?_⟩
      rw [hwo]; simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨h5, fun h => hwtbr (h ▸ hv)⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := H.tbOk t' v hv
      refine ⟨h1, h2, h3, h4, ?_⟩
      rw [hwo]; simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨h5, fun h => ?_⟩
      subst h
      rename_i hne
      exact hne (h3.symm.trans hwt)
  · -- tbSorted
    intro t'
    rw [htb']
    split
    · exact hsorted.2
    · exact H.tbSorted t'
  · -- wAll
    intro v hv hW'
    simp only [hus] at hv hW' ⊢
    rw [hwo, htb']
    rcases H.wAll v hv hW' with h | h
    · exact .inl (List.mem_append_left _ h)
    · split
      · next h' =>
        rw [h', htb] at h
        rcases List.mem_cons.mp h with h | h
        · subst h; exact .inl (List.mem_append_right _ (List.mem_singleton_self _))
        · exact .inr h
      · exact .inr h
  · -- buf
    intro t'
    simp only [hus]
    rw [htb']
    by_cases h : t' = t
    · subst h; rw [Function.update_self]; simp only [↓reduceIte]; exact hrest
    · rw [Function.update_of_ne h]; simp only [h, ↓reduceIte]; exact H.buf t'
  · -- mem
    intro y
    simp only [hus]
    rw [hwo, lastCov_snoc, ha, hbs, writeMem_eq hwd]
    split
    · rfl
    · exact H.mem y
  · -- lockedW
    intro v hv hW' hL
    obtain ⟨h1, h2⟩ := H.lockedW v hv hW' hL
    exact ⟨by rw [hwo]; exact List.mem_append_left _ h1, by rw [hf_old v h1]; exact h2⟩
  · -- drain
    intro u hu v hv hW' htd hp hk
    obtain ⟨h1, h2⟩ := H.drain u hu v hv hW' htd hp hk
    exact ⟨by rw [hwo]; exact List.mem_append_left _ h1, by rw [hf_old v h1]; exact h2⟩
  · -- rmwOk
    intro q hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H.rmwOk q hq
    exact ⟨h1, h2, h3, h4, h5, by rw [hwo]; exact List.mem_append_left _ h6,
      by rw [hf_old _ h6]; exact h7⟩
  · -- clash
    intro r hr hR' v hv
    rw [hwo] at hv
    rcases List.mem_append.mp hv with h | h
    · rw [hf_old v h]; exact H.clash r hr hR' v h
    · simp only [List.mem_singleton] at h; subst h
      rw [hf_w]; have := H.eLt r hr; show g.clk ≠ g.e r; omega
  · exact H.rfW
  · -- rfInv
    intro r hr hR' y hy
    exact rfInv_ext (g := g) (g' := g') (v := []) (by rw [hus, List.append_nil]) hr rfl rfl (hFB r hr)
      hf_old (fun v hv hge => by rw [hus] at hv; omega) (H.rfInv r hr hR' y hy)
  · exact H.vals

/-! ## Runs -/

theorem inv_step {P : List (List (XEvent Nat))} (hT : ThreadsOk P) {init : Tso.Mem} {c c' : ACfg}
    {g : G} (H : Inv P init c g) (h : AStep c c') : ∃ g', Inv P init c' g' := by
  cases h with
  | ev rest s s' i ev es hr hs =>
    obtain ⟨ps, hps, hmem, -⟩ := rest_head H.book hr
    have hti := hT i ps hps ev hmem
    cases hs with
    | load t a bs hv => exact ⟨_, inv_load H hr hti hv⟩
    | store t a bs => exact ⟨_, inv_store H hr hti⟩
    | rmw t a old new hemp hm _ => exact ⟨_, inv_rmw H hr hti hemp hm⟩
    | fence t hemp => exact ⟨_, inv_fence H hr hti hemp⟩
  | flush rest s s' hf =>
    cases hf with
    | head t a bs rest' hold => exact (inv_flush H hold).imp fun _ h => h.1

theorem inv_run {P : List (List (XEvent Nat))} (hT : ThreadsOk P) {init : Tso.Mem} {c c' : ACfg}
    (h : Relation.ReflTransGen AStep c c') {g : G} (H : Inv P init c g) :
    ∃ g', Inv P init c' g' := by
  induction h with
  | refl => exact ⟨g, H⟩
  | tail _ hstep ih =>
    obtain ⟨g', H'⟩ := ih
    exact inv_step hT H' hstep

/-! ## The end of a complete run -/

theorem x_n (g : G) : g.x.n = g.us.length := by simp [Exec.n, G.x]

theorem uev_mem {us : List (Ev × List Byte)} {u : Nat} (hu : u < us.length) :
    ∃ p ∈ us, p.1 = uev us u := by
  refine ⟨us[u], List.getElem_mem hu, ?_⟩
  simp [uev, List.getD_eq_getElem?_getD, hu]

section Final
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {g : G}
  (H : Inv P init ⟨P.map fun _ => [], s⟩ g) (hdrain : ∀ t, s.buffer t = [])
include H hdrain

theorem final_tb (t : Nat) : g.tb t = [] := by
  have := H.buf t
  rw [hdrain t] at this
  exact List.map_eq_nil_iff.mp this.symm

theorem final_wo {w : Nat} (hw : w < g.us.length) (hW : (uev g.us w).isW = true) : w ∈ g.wo := by
  rcases H.wAll w hw hW with h | h
  · exact h
  · rw [final_tb H hdrain] at h; simp at h

omit hdrain in
theorem final_take (i : Nat) : (P[i]?.getD []).take (g.cnt i) = P[i]?.getD [] := by
  have := H.book.rest i
  simp only [List.getElem?_map] at this
  cases hp : P[i]? with
  | none => simp
  | some ps =>
    rw [hp] at this
    simp only [Option.map_some, Option.some.injEq] at this
    simp only [Option.getD_some]
    exact List.take_of_length_le (List.drop_eq_nil_iff.mp this.symm)

omit hdrain in
theorem final_filter (i : Nat) :
    g.us.filter (fun p => p.1.tid == i) = threadUnits i (P[i]?.getD []) := by
  rw [H.book.filt i, final_take H i]

omit hdrain in
theorem final_perm : g.us.Perm (progUnits P) :=
  perm_of_filter fun i => by rw [final_filter H i, progUnits_filter]

omit hdrain in
theorem final_foot {u : Nat} (hu : u < g.us.length) (hm : (uev g.us u).isM = true) :
    ∃ ps, P[(uev g.us u).tid]? = some ps ∧ ∃ ev ∈ ps,
      ((uev g.us u).addr, (uev g.us u).size) ∈ footOf ev := by
  obtain ⟨p, hp, hpe⟩ := uev_mem hu
  have hf : p ∈ g.us.filter (fun q => q.1.tid == (uev g.us u).tid) :=
    List.mem_filter.mpr ⟨hp, by simp [hpe]⟩
  rw [final_filter H] at hf
  obtain ⟨k, ev, hev, hpu⟩ := mem_threadUnits hf
  cases hps : P[(uev g.us u).tid]? with
  | none => rw [hps] at hev; simp at hev
  | some ps =>
    rw [hps] at hev
    refine ⟨ps, rfl, ev, hev, ?_⟩
    rw [← hpe]
    exact evUnits_foot hpu (hpe ▸ hm)

theorem final_timedOk (hC : ThreadCells P) : TimedOk g.x g.T := by
  have hn := x_n g
  have hE : ∀ u, g.x.evN u = uev g.us u := fun _ => rfl
  have fb : ∀ w t, w < g.us.length → (uev g.us w).isW = true → (FB g w t ↔ g.f w < t) :=
    fun w t hw hW => ⟨fun h => h.2, fun h => ⟨final_wo H hdrain hw hW, h⟩⟩
  refine ⟨?_, ?_, fun y => rfl, ?_, H.woSorted, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb; rw [hn] at ha hb; exact H.book.uniq a ha b hb
  · intro a ha b hb; rw [hn] at ha hb; exact H.poE a ha b hb
  · intro w hw; rw [hn]; exact H.woW w hw
  · intro w hw hW; rw [hn] at hw; exact (H.woF w (final_wo H hdrain hw hW)).2
  · intro a ha b hb hWa hWb ht hp
    rw [hn] at ha hb
    exact (H.fifo a ha b hb hWa hWb ht hp (final_wo H hdrain hb hWb)).2
  · intro w hw hW hL; rw [hn] at hw; exact (H.lockedW w hw hW hL).2
  · intro u hu w hw hW ht hp hk; rw [hn] at hu hw; exact (H.drain u hu w hw hW ht hp hk).2
  · intro q hq
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := H.rmwOk q hq
    exact ⟨by rw [hn]; exact h1, by rw [hn]; exact h2, h3, h4, h5, h7⟩
  · intro r hr w hw hR hW; rw [hn] at hr hw
    exact H.clash r hr hR w (final_wo H hdrain hw hW)
  · -- rfOk
    intro r hr hR y hy
    rw [hn] at hr
    have hI := H.rfInv r hr hR y hy
    have hne : ∀ w < g.us.length, (uev g.us w).isW = true → g.f w ≠ g.e r := fun w hw hW =>
      H.clash r hr hR w (final_wo H hdrain hw hW)
    unfold RfInv at hI
    unfold RfSpec
    change (match g.rf r y with
      | some s => _
      | none => _)
    revert hI
    cases g.rf r y with
    | some s =>
      intro hI
      obtain ⟨hs, hW, hc, hcase⟩ := hI
      refine ⟨by rw [hn]; exact hs, hW, hc, ?_⟩
      rcases hcase with ⟨⟨ht, hp, hnf⟩, hmax⟩ | ⟨hfb, hmax, hall⟩
      · left
        refine ⟨⟨ht, hp, ?_⟩, ?_⟩
        · rw [fb s _ hs hW] at hnf
          have := hne s hs hW
          show g.e r < g.f s; omega
        · intro w hw hW' hc' ht' hp' hlt
          rw [hn] at hw
          exact hmax w hw hW' hc' ht' hp' (by rw [fb w _ hw hW']; show ¬ g.f w < g.e r; simp only [G.T] at hlt; omega)
      · right
        refine ⟨(fb s _ hs hW).mp hfb, ?_, ?_⟩
        · intro w hw hW' hc' hlt
          rw [hn] at hw
          exact hmax w hw hW' hc' ((fb w _ hw hW').mpr hlt)
        · intro w hw hW' hc' ht' hp'
          rw [hn] at hw
          exact (fb w _ hw hW').mp (hall w hw hW' hc' ht' hp')
    | none =>
      intro hI w hw hW' hc'
      rw [hn] at hw
      obtain ⟨h1, h2⟩ := hI w hw hW' hc'
      exact ⟨fun h => h1 ((fb w _ hw hW').mpr h), h2⟩
  · -- cells
    intro a ha b hb ht hma hmb hov
    rw [hn] at ha hb
    change (uev g.us a).tid = (uev g.us b).tid at ht
    change (uev g.us a).isM = true at hma
    change (uev g.us b).isM = true at hmb
    change Ev.overlap (uev g.us a) (uev g.us b) = true at hov
    change (uev g.us a).addr = (uev g.us b).addr ∧ (uev g.us a).size = (uev g.us b).size
    obtain ⟨ps, hps, eva, heva, hfa⟩ := final_foot H ha hma
    obtain ⟨ps', hps', evb, hevb, hfb⟩ := final_foot H hb hmb
    rw [← ht, hps] at hps'
    cases hps'
    have hfo : footOverlap ((uev g.us a).addr, (uev g.us a).size)
        ((uev g.us b).addr, (uev g.us b).size) := by
      obtain ⟨y, h1, h2⟩ := overlap_iff.mp hov
      rw [covers_iff] at h1 h2
      exact ⟨y, h1.1, h1.2, h2.1, h2.2⟩
    have := hC _ ps hps eva heva evb hevb _ hfa _ hfb hfo
    simp only [Prod.mk.injEq] at this
    exact this

theorem final_explains (hC : ThreadCells P) : Explains Exec.Tso P init s g.x := by
  have hn := x_n g
  refine ⟨g.us, final_perm H, rfl, tso (final_timedOk H hdrain hC), ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr hR; rw [hn] at hr; exact H.vals r hr hR
  · intro r y w h; rw [hn]; exact H.rfW r y w h
  · intro y w
    show w ∈ g.wo.filter _ ↔ _
    rw [List.mem_filter, hn]
    constructor
    · rintro ⟨hw, hc⟩
      obtain ⟨h1, h2⟩ := H.woW w hw
      exact ⟨h1, h2, hc⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨final_wo H hdrain h1 h2, h3⟩
  · intro y
    have hnd : g.wo.Nodup := H.woSorted.imp fun h => Nat.ne_of_lt h ∘ congrArg g.f
    exact hnd.filter _
  · intro y
    exact H.mem y

end Final

/-- **op-TSO ⊆ ax-TSO.** A complete run of the store-buffer machine on a program whose threads
have cells is explained by an x86-TSO-consistent candidate execution. -/
theorem run_explains {P : List (List (XEvent Nat))} (hT : ThreadsOk P) (hC : ThreadCells P)
    {init : Tso.Mem} {s : XState Nat} (h : Run P init s) : ∃ x, Explains Exec.Tso P init s x := by
  obtain ⟨g, H⟩ := inv_run hT h.1 (inv_init P init)
  exact ⟨g.x, final_explains H h.2 hC⟩

end Silmaril.X86.MemoryModel.OpAx.Proofs
