module

public import Silmaril.Proofs.X86.Concurrency.Cir.Domain.Run
public import Silmaril.X86.MemoryModel.Xl.Defs

/-!
# Domain closure on CIR: the units of a uniform program

Proofs for `Silmaril/X86/Concurrency/Cir/Domain/Thms.lean`.

* `locsFacts`: what `locsOk` says, as propositions;
* `units_eq`, `cellsOk_units`: in a uniform program no access tears (the `units` are the
  unsplit `accUnits`), and two memory units are in one cell or disjoint;
* `threadUnits_append`, `threadUnits_pos`, `labUnits_split`: positions of the units of a
  thread's labels;
* `lab_reads`, `lab_write_after`, `lab_write_val`: per label, the read units below the ghost
  bytes return its read values, they precede its write units below the ghost bytes, and those
  write a value the label writes (`Lab.written`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Domain

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace Loc actUnits threadUnits accUnits units tearAcc
  splitUnit cellsOk)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec)

/-! ## Locations -/

/-- What `locsOk` says. -/
structure LocsFacts (locs : List Loc) : Prop where
  size : ∀ l ∈ locs, l.size = 1 ∨ l.size = 2 ∨ l.size = 4 ∨ l.size = 8
  align : ∀ l ∈ locs, l.addr % l.size = 0
  init : ∀ l ∈ locs, l.init < 2 ^ (8 * l.size)
  below : ∀ l ∈ locs, l.addr + l.size ≤ ctlAddr 0
  disj : ∀ l ∈ locs, ∀ l' ∈ locs, l = l' ∨ l.addr + l.size ≤ l'.addr ∨ l'.addr + l'.size ≤ l.addr

theorem locsFacts {locs : List Loc} (h : locsOk locs = true) : LocsFacts locs := by
  simp only [locsOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_cons,
    List.not_mem_nil, or_false, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun l hl => (h1 l hl).1.1.1, fun l hl => (h1 l hl).1.1.2, fun l hl => (h1 l hl).1.2,
    fun l hl => (h1 l hl).2, ?_⟩
  intro l hl l' hl'
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl'
  have := h2 i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
  simp only [Bool.or_eq_true, beq_iff_eq, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, decide_eq_true_eq] at this
  rcases this with rfl | h
  · exact .inl rfl
  · exact .inr h

/-- The cells of the locations. -/
def cellsOf (locs : List Loc) : List (Nat × Nat) := locs.map fun l => (l.addr, l.size)

theorem cellsOf_lt {locs : List Loc} (hl : LocsFacts locs) : ∀ c ∈ cellsOf locs, c.1 < 2 ^ 64 := by
  intro c hc
  obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hc
  have := hl.below l hlm
  simp only [ctlAddr] at this
  simp only; omega

theorem cell_facts {locs : List Loc} (_hl : LocsFacts locs) {c : Nat × Nat} (hc : c ∈ cellsOf locs) :
    ∃ l ∈ locs, l.addr = c.1 ∧ l.size = c.2 := by
  obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, hlm, rfl, rfl⟩

/-! ## Units of uniform programs -/

/-- A unit of a uniform program: a memory unit is unsplit and is a location's cell or a ghost
byte. -/
def UOk (cs : List (Nat × Nat)) (u : Ev) : Prop :=
  u.isM = true → u.accAddr = u.addr ∧ u.accSize = u.size ∧
    ((u.addr, u.size) ∈ cs ∨ (u.size = 1 ∧ ctlAddr 0 ≤ u.addr))

/-- An action of a uniform program: a memory action is on a location's cell or a ghost byte. -/
def AOk (cs : List (Nat × Nat)) (a : XAct) : Prop :=
  match a.ev.kind with
  | .fence _ => True
  | _ => (a.ev.addr, a.ev.size) ∈ cs ∨ (a.ev.size = 1 ∧ ctlAddr 0 ≤ a.ev.addr)

theorem actUnits_ok {cs : List (Nat × Nat)} {a : XAct} (h : AOk cs a) (i p : Nat) :
    ∀ u ∈ actUnits i p a, UOk cs u.1 := by
  unfold AOk at h
  unfold actUnits
  split <;> rename_i hk <;> rw [hk] at h <;> simp only at h <;>
    simp [UOk, Ev.isM, Ev.isR, Ev.isW, h]

theorem ghost_q (a : Nat) : ctlAddr 0 ≤ qAddr a := by simp [ctlAddr, qAddr]; omega
theorem ghost_ctl (t : Nat) : ctlAddr 0 ≤ ctlAddr t := by simp [ctlAddr]
theorem ghost_end (t : Nat) : ctlAddr 0 ≤ endAddr t := by simp [endAddr, ctlAddr]; omega

/-- **The actions of a label of a uniform run are uniform.** -/
theorem lab_acts_ok {cs : List (Nat × Nat)} {bs : List Block} {l : Lab} (hl : LabOk cs bs l) :
    ∀ a ∈ l.acts, AOk cs a := by
  cases l with
  | rd m fl a sz v => simp [Lab.acts, AOk, ldAct, hl.1]
  | wr m fl a sz v => simp [Lab.acts, AOk, stAct, hl.1]
  | rmw m a sz o n => simp [Lab.acts, AOk, rmwAct, hl.1]
  | fence k => simp [Lab.acts, AOk, fenceAct]
  | fwait a e seen r =>
    simp only [LabOk] at hl
    simp only [Lab.acts]
    split <;> simp [AOk, fenceAct, stAct, ldAct, rmwAct, hl.1, ghost_q]
  | fwake a n q => simp [Lab.acts, AOk, fenceAct, rmwAct, ghost_q]
  | fblock a e => simp [LabOk] at hl
  | spawn t => simp [Lab.acts, AOk, ctlAct, rmwAct, ghost_ctl]
  | join t => simp [Lab.acts, AOk, endAct, rmwAct, ghost_end]
  | blk n ins outs rvs =>
    simp only [LabOk] at hl
    intro a ha
    simp only [Lab.acts, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · simp [AOk, ldAct, (hl.1 c (List.mem_append_left _ hc)).1]
    · simp [AOk, stAct, (hl.1 c (List.mem_append_right _ hc)).1]

theorem threadUnits_ok {cs : List (Nat × Nat)} (i : Nat) : ∀ (p : Nat) (as : List XAct),
    (∀ a ∈ as, AOk cs a) → ∀ u ∈ threadUnits i p as, UOk cs u.1
  | _, [], _ => by simp [threadUnits]
  | p, a :: as, h => by
    intro u hu
    simp only [threadUnits, List.mem_append] at hu
    rcases hu with hu | hu
    · exact actUnits_ok (h a List.mem_cons_self) i p u hu
    · exact threadUnits_ok i _ as (fun b hb => h b (List.mem_cons_of_mem _ hb)) u hu

/-- The actions of thread `i`'s run `p` in a uniform program are uniform. -/
theorem thread_acts_ok {cs : List (Nat × Nat)} {bs : List Block} (th : Thread) (i : Nat)
    (tr : List Lab) (h : ∀ l ∈ tr, LabOk cs bs l) : ∀ a ∈ th.acts i tr, AOk cs a := by
  intro a ha
  simp only [Thread.acts, List.mem_append, List.mem_flatMap] at ha
  rcases ha with (ha | ⟨l, hl, ha⟩) | ha
  · split at ha
    · simp only [List.mem_singleton] at ha; subst ha
      simp [AOk, ctlAct, rmwAct, ghost_ctl]
    · simp at ha
  · exact lab_acts_ok (h l hl) a ha
  · split at ha
    · simp only [List.mem_singleton] at ha; subst ha
      simp [AOk, endAct, rmwAct, ghost_end]
    · simp at ha

/-- Two memory units of a uniform program are in one cell or touch disjoint bytes. -/
theorem uok_cell {locs : List Loc} (hl : LocsFacts locs) {u v : Ev} (hu : UOk (cellsOf locs) u)
    (hv : UOk (cellsOf locs) v) (huM : u.isM = true) (hvM : v.isM = true) :
    (u.addr = v.addr ∧ u.size = v.size) ∨ u.addr + u.size ≤ v.addr ∨ v.addr + v.size ≤ u.addr := by
  obtain ⟨-, -, hu⟩ := hu huM
  obtain ⟨-, -, hv⟩ := hv hvM
  rcases hu with hu | ⟨hu1, hu2⟩ <;> rcases hv with hv | ⟨hv1, hv2⟩
  · obtain ⟨l, hlm, hla, hls⟩ := cell_facts hl hu
    obtain ⟨l', hlm', hla', hls'⟩ := cell_facts hl hv
    simp only at hla hls hla' hls'
    rcases hl.disj l hlm l' hlm' with rfl | h | h
    · exact .inl ⟨hla.symm.trans hla', hls.symm.trans hls'⟩
    · exact .inr (.inl (by omega))
    · exact .inr (.inr (by omega))
  · obtain ⟨l, hlm, hla, hls⟩ := cell_facts hl hu
    have := hl.below l hlm
    simp only at hla hls
    exact .inr (.inl (by omega))
  · obtain ⟨l, hlm, hla, hls⟩ := cell_facts hl hv
    have := hl.below l hlm
    simp only at hla hls
    exact .inr (.inr (by omega))
  · by_cases h : u.addr = v.addr
    · exact .inl ⟨h, by omega⟩
    · omega

theorem uok_single {locs : List Loc} (hl : LocsFacts locs) {u : Ev} (hu : UOk (cellsOf locs) u)
    (huM : u.isM = true) : u.singleCopy = true ∧ 0 < u.size := by
  obtain ⟨ha, hs, hu⟩ := hu huM
  simp only [Ev.singleCopy, ha, hs, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rcases hu with hu | ⟨hu1, -⟩
  · obtain ⟨l, hlm, hla, hls⟩ := cell_facts hl hu
    simp only at hla hls
    have h1 := hl.size l hlm
    have h2 := hl.align l hlm
    rw [← hla, ← hls]
    refine ⟨⟨by omega, h2⟩, by omega⟩
  · rw [hu1]; exact ⟨⟨by omega, Nat.mod_one _⟩, by omega⟩

/-- **No access tears**: in a list of uniform units, `tearAcc` is false. -/
theorem tear_false {locs : List Loc} (hl : LocsFacts locs) {us : List (Ev × List Byte)}
    (h : ∀ u ∈ us, UOk (cellsOf locs) u.1) : ∀ u ∈ us, tearAcc us u.1 = false := by
  intro u hu
  simp only [tearAcc, Bool.and_eq_false_iff]
  by_cases hM : u.1.isM = true
  · right
    obtain ⟨hsc, -⟩ := uok_single hl (h u hu) hM
    simp only [hsc, Bool.not_true, Bool.false_or, List.any_eq_false, Bool.and_eq_true,
      bne_iff_ne, ne_eq, not_and, Bool.or_eq_true]
    intro v hv ⟨hvM, hov⟩ hne
    obtain ⟨ha, hs, -⟩ := h u hu hM
    obtain ⟨ha', hs', -⟩ := h v hv hvM
    simp only [Ev.accOverlap, ha, hs, ha', hs', Bool.and_eq_true, decide_eq_true_eq] at hov
    rcases uok_cell hl (h u hu) (h v hv) hM hvM with ⟨e1, e2⟩ | h' | h'
    · rcases hne with hne | hne
      · exact hne e1
      · exact hne e2
    · omega
    · omega
  · left; simpa using hM

theorem flatMap_eq_self {us : List (Ev × List Byte)} {p : Ev → Bool}
    (h : ∀ u ∈ us, p u.1 = false) : us.flatMap (fun u => if p u.1 then splitUnit u else [u]) = us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons, h u List.mem_cons_self, Bool.false_eq_true, ite_false,
      List.singleton_append]
    rw [ih fun v hv => h v (List.mem_cons_of_mem _ hv)]

/-- **The units of uniform traces are their unsplit units.** -/
theorem units_eq {locs : List Loc} (hl : LocsFacts locs) {trs : List XTrace}
    (h : ∀ u ∈ accUnits trs, UOk (cellsOf locs) u.1) : units trs = accUnits trs := by
  unfold units
  exact flatMap_eq_self (tear_false hl h)

/-- **Units of uniform traces are in one cell or disjoint.** -/
theorem cellsOk_of {locs : List Loc} (hl : LocsFacts locs) {evs : List Ev}
    (h : ∀ u ∈ evs, UOk (cellsOf locs) u) : cellsOk evs = true := by
  simp only [cellsOk, List.all_eq_true, List.mem_filter, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  intro a ⟨ha, haM⟩ b ⟨hb, hbM⟩
  rcases uok_cell hl (h a ha) (h b hb) haM hbM with e | e | e
  · exact .inl e
  · omega
  · omega

/-! ## Positions -/

theorem actUnits_tid_pos (i p : Nat) (a : XAct) :
    ∀ u ∈ actUnits i p a, u.1.tid = i ∧ p ≤ u.1.pos ∧ u.1.pos < p + (actUnits i p a).length := by
  unfold actUnits
  split <;> simp

theorem threadUnits_append (i : Nat) : ∀ (p : Nat) (as bs : List XAct),
    threadUnits i p (as ++ bs) =
      threadUnits i p as ++ threadUnits i (p + (threadUnits i p as).length) bs
  | p, [], bs => by simp [threadUnits]
  | p, a :: as, bs => by
    simp only [List.cons_append, threadUnits, List.length_append, List.append_assoc]
    rw [threadUnits_append i _ as bs, Nat.add_assoc]

theorem threadUnits_pos (i : Nat) : ∀ (p : Nat) (as : List XAct), ∀ u ∈ threadUnits i p as,
    u.1.tid = i ∧ p ≤ u.1.pos ∧ u.1.pos < p + (threadUnits i p as).length
  | p, [], u, h => by simp [threadUnits] at h
  | p, a :: as, u, h => by
    simp only [threadUnits, List.mem_append, List.length_append] at h ⊢
    rcases h with h | h
    · obtain ⟨h1, h2, h3⟩ := actUnits_tid_pos i p a u h
      exact ⟨h1, h2, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := threadUnits_pos i _ as u h
      exact ⟨h1, by omega, by omega⟩

theorem act_mem (i : Nat) : ∀ (p : Nat) (a : XAct) {as : List XAct}, a ∈ as →
    ∃ p', ∀ u ∈ actUnits i p' a, u ∈ threadUnits i p as := by
  intro p a as ha
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ha
  refine ⟨p + (threadUnits i p A).length, fun u hu => ?_⟩
  rw [threadUnits_append]
  exact List.mem_append_right _ (by simp only [threadUnits, List.mem_append]; exact .inl hu)

/-- The units of thread `i`'s actions before label list `L1`, from position `q`. -/
def labBase (i q : Nat) (L1 : List Lab) : Nat := q + (threadUnits i q (L1.flatMap Lab.acts)).length

/-- **Every unit of a list of labels belongs to one label.** -/
theorem labUnits_split (i : Nat) : ∀ (q : Nat) (L : List Lab) (u : Ev × List Byte),
    u ∈ threadUnits i q (L.flatMap Lab.acts) →
      ∃ L1 l L2, L = L1 ++ l :: L2 ∧ u ∈ threadUnits i (labBase i q L1) l.acts
  | q, [], u, h => by simp [threadUnits] at h
  | q, l :: L, u, h => by
    rw [List.flatMap_cons, threadUnits_append, List.mem_append] at h
    rcases h with h | h
    · exact ⟨[], l, L, rfl, by simpa [labBase, threadUnits] using h⟩
    · obtain ⟨L1, l', L2, rfl, h'⟩ := labUnits_split i _ L u h
      refine ⟨l :: L1, l', L2, rfl, ?_⟩
      have : labBase i q (l :: L1) =
          labBase i (q + (threadUnits i q l.acts).length) L1 := by
        simp only [labBase, List.flatMap_cons, threadUnits_append, List.length_append,
          Nat.add_assoc]
      rw [this]; exact h'

theorem labUnits_mem (i q : Nat) (L1 : List Lab) (l : Lab) (L2 : List Lab) :
    ∀ u ∈ threadUnits i (labBase i q L1) l.acts,
      u ∈ threadUnits i q ((L1 ++ l :: L2).flatMap Lab.acts) := by
  intro u hu
  rw [List.flatMap_append, threadUnits_append, List.flatMap_cons, threadUnits_append]
  exact List.mem_append_right _ (List.mem_append_left _ hu)

theorem labUnits_pre_mem (i q : Nat) (L1 L2 : List Lab) :
    ∀ u ∈ threadUnits i q (L1.flatMap Lab.acts), u ∈ threadUnits i q ((L1 ++ L2).flatMap Lab.acts) := by
  intro u hu
  rw [List.flatMap_append, threadUnits_append]
  exact List.mem_append_left _ hu

/-- The units of each label of `L` lie among the units of `L`. -/
theorem labUnits_each (i : Nat) : ∀ (q : Nat) (L : List Lab), ∀ l ∈ L, ∃ q',
    ∀ u ∈ threadUnits i q' l.acts, u ∈ threadUnits i q (L.flatMap Lab.acts) := by
  intro q L l hl
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hl
  exact ⟨labBase i q L1, labUnits_mem i q L1 l L2⟩

/-! ## Bytes -/

theorem natBytes_succ (v sz : Nat) :
    natBytes v (sz + 1) = BitVec.ofNat 8 v :: natBytes (v / 256) sz := by
  simp only [natBytes, List.range_succ_eq_map, List.map_cons, List.map_map, pow_zero, Nat.div_one]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp [Function.comp, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem length_natBytes (v sz : Nat) : (natBytes v sz).length = sz := by simp [natBytes]

theorem natBytes_inj : ∀ (sz v w : Nat), v < 2 ^ (8 * sz) → w < 2 ^ (8 * sz) →
    natBytes v sz = natBytes w sz → v = w
  | 0, v, w, hv, hw, _ => by simp at hv hw; omega
  | sz + 1, v, w, hv, hw, h => by
    rw [natBytes_succ, natBytes_succ, List.cons.injEq] at h
    have hdiv : ∀ u, u < 2 ^ (8 * (sz + 1)) → u / 256 < 2 ^ (8 * sz) := by
      intro u hu
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      calc u < 2 ^ (8 * (sz + 1)) := hu
        _ = 2 ^ (8 * sz) * 256 := by rw [Nat.mul_succ, Nat.pow_add]
    have h2 := natBytes_inj sz _ _ (hdiv v hv) (hdiv w hw) h.2
    have h1 := congrArg BitVec.toNat h.1
    simp only [BitVec.toNat_ofNat] at h1
    omega

theorem bytes_byte_data {e : Ev} (h : e.data.length = e.size) : e.bytes.map e.byte = e.data := by
  apply List.ext_getElem
  · simp [Ev.bytes, h]
  · intro j h1 h2
    simp only [Ev.bytes, List.getElem_map, List.getElem_range', Ev.byte]
    simp [List.getElem?_eq_getElem h2]

/-! ## Per-label facts -/

/-- A unit below the ghost bytes. -/
def low (e : Ev) : Prop := e.addr < ctlAddr 0

/-- The read values a label took from memory: loads, the old value of a read-modify-write,
the value a futex wait saw, and the inputs of a block. -/
def ReadsIn (dom : List Nat) : Lab → Prop
  | .rd _ _ _ _ v => v ∈ dom
  | .rmw _ _ _ o _ => o ∈ dom
  | .fwait _ _ seen _ => seen ∈ dom
  | .blk _ ins _ _ => ∀ c ∈ ins, c.2.2 ∈ dom
  | _ => True

/-- A good unit: a read unit below the ghost bytes returns the bytes of a value of `dom`. -/
def QP (dom : List Nat) (u : Ev × List Byte) : Prop :=
  u.1.isR = true → low u.1 → ∃ v ∈ dom, v < 2 ^ (8 * u.1.size) ∧ u.2 = natBytes v u.1.size

theorem low_of_cell {locs : List Loc} (hl : LocsFacts locs) {a sz : Nat}
    (h : (a, sz) ∈ cellsOf locs) : a < ctlAddr 0 := by
  obtain ⟨l, hlm, hla, hls⟩ := cell_facts hl h
  have := hl.below l hlm
  have := hl.size l hlm
  simp only at hla hls
  omega

theorem read_val {locs : List Loc} (hl : LocsFacts locs) {dom : List Nat} {a sz v : Nat} {e : Ev}
    (he : e.isR = true) (hea : e.addr = a) (hes : e.size = sz) (hc : (a, sz) ∈ cellsOf locs)
    (hv : v < 2 ^ (8 * sz)) (hq : QP dom (e, natBytes v sz)) : v ∈ dom := by
  obtain ⟨w, hw, hwb, heq⟩ := hq he (by unfold low; rw [hea]; exact low_of_cell hl hc)
  rw [hes] at hwb heq
  rwa [natBytes_inj sz v w hv hwb heq]

theorem loads_units (i : Nat) (cs : List (Nat × Nat × Nat)) : ∀ q,
    ∀ c ∈ cs, ∃ u ∈ threadUnits i q (cs.map fun c => ldAct .wb c.1 c.2.1 c.2.2),
      u.1.isR = true ∧ u.1.addr = c.1 ∧ u.1.size = c.2.1 ∧ u.2 = natBytes c.2.2 c.2.1 := by
  induction cs with
  | nil => simp
  | cons d cs ih =>
    intro q c hc
    simp only [List.map_cons, threadUnits, List.mem_append]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, .inl (by simp [actUnits, ldAct]; rfl), by simp [Ev.isR]⟩
    · obtain ⟨u, hu, h⟩ := ih _ c hc
      exact ⟨u, .inr hu, h⟩

theorem loads_units_R (i : Nat) (cs : List (Nat × Nat × Nat)) : ∀ q,
    ∀ u ∈ threadUnits i q (cs.map fun c => ldAct .wb c.1 c.2.1 c.2.2), u.1.isR = true := by
  induction cs with
  | nil => simp [threadUnits]
  | cons d cs ih =>
    intro q u hu
    simp only [List.map_cons, threadUnits, List.mem_append] at hu
    rcases hu with hu | hu
    · simp [actUnits, ldAct] at hu; subst hu; simp [Ev.isR]
    · exact ih _ u hu

theorem stores_units (i : Nat) (cs : List (Nat × Nat × Nat)) : ∀ q,
    ∀ u ∈ threadUnits i q (cs.map fun c => stAct .wb c.1 c.2.1 c.2.2),
      u.1.isW = true ∧ u.1.isR = false ∧ ∃ c ∈ cs, u.1.addr = c.1 ∧ u.1.size = c.2.1 ∧
        u.1.data = natBytes c.2.2 c.2.1 := by
  induction cs with
  | nil => simp [threadUnits]
  | cons d cs ih =>
    intro q u hu
    simp only [List.map_cons, threadUnits, List.mem_append] at hu
    rcases hu with hu | hu
    · simp [actUnits, stAct] at hu; subst hu
      exact ⟨by simp [Ev.isW], by simp [Ev.isR], d, List.mem_cons_self, rfl, rfl, rfl⟩
    · obtain ⟨h1, h2, c, hc, h3⟩ := ih _ u hu
      exact ⟨h1, h2, c, List.mem_cons_of_mem _ hc, h3⟩

/-- **The read values of a label are good** when its read units are. -/
theorem lab_reads {locs : List Loc} (hl : LocsFacts locs) {bs : List Block} {dom : List Nat}
    {l : Lab} (hok : LabOk (cellsOf locs) bs l) (i q : Nat)
    (h : ∀ u ∈ threadUnits i q l.acts, QP dom u) : ReadsIn dom l := by
  cases l with
  | rd m fl a sz v =>
    simp only [LabOk] at hok
    have := h _ (by simp [Lab.acts, threadUnits, actUnits, ldAct]; rfl)
    exact read_val hl (by simp [Ev.isR]) rfl rfl hok.1 hok.2 this
  | rmw m a sz o n =>
    simp only [LabOk] at hok
    have := h _ (by simp [Lab.acts, threadUnits, actUnits, rmwAct]; exact .inl rfl)
    exact read_val hl (by simp [Ev.isR]) rfl rfl hok.1 hok.2.1 this
  | fwait a e seen r =>
    simp only [LabOk] at hok
    simp only [ReadsIn]
    simp only [Lab.acts] at h
    split at h
    · obtain ⟨p', hp'⟩ := act_mem i q (ldAct .wb a 4 seen)
        (as := [fenceAct .mfence, stAct .wb (qAddr a) 1 1, fenceAct .mfence, ldAct .wb a 4 seen,
          rmwAct (qAddr a) 1 r 0]) (by simp)
      have hu : ∀ u ∈ actUnits i p' (ldAct .wb a 4 seen), QP dom u := fun u hu => h u (hp' u hu)
      simp only [actUnits, ldAct, List.mem_singleton, forall_eq] at hu
      exact read_val hl rfl rfl rfl hok.1 hok.2.1 hu
    · obtain ⟨p', hp'⟩ := act_mem i q (ldAct .wb a 4 seen)
        (as := [fenceAct .mfence, ldAct .wb a 4 seen, fenceAct .mfence]) (by simp)
      have hu : ∀ u ∈ actUnits i p' (ldAct .wb a 4 seen), QP dom u := fun u hu => h u (hp' u hu)
      simp only [actUnits, ldAct, List.mem_singleton, forall_eq] at hu
      exact read_val hl rfl rfl rfl hok.1 hok.2.1 hu
  | blk n ins outs rvs =>
    simp only [LabOk] at hok
    simp only [ReadsIn]
    intro c hc
    simp only [Lab.acts] at h
    obtain ⟨u, hu, hR, ha, hs, hb⟩ := loads_units i ins q c hc
    have hq := h u (by rw [threadUnits_append]; exact List.mem_append_left _ hu)
    have hcell := hok.1 c (List.mem_append_left _ hc)
    obtain ⟨u1, u2⟩ := u
    simp only at hR ha hs hb
    subst hb
    exact read_val hl hR ha hs hcell.1 hcell.2 hq
  | wr _ _ _ _ _ => trivial
  | fence _ => trivial
  | fwake _ _ _ => trivial
  | fblock _ _ => trivial
  | spawn _ => trivial
  | join _ => trivial

/-- **The write units of a label below the ghost bytes come after its read units.** -/
theorem lab_write_after {locs : List Loc} (_hl : LocsFacts locs) {bs : List Block} {l : Lab}
    (hok : LabOk (cellsOf locs) bs l) (i q : Nat) {w : Ev × List Byte}
    (hw : w ∈ threadUnits i q l.acts) (hW : w.1.isW = true) (hlow : low w.1) :
    ∀ r ∈ threadUnits i q l.acts, r.1.isR = true → r.1.pos < w.1.pos := by
  have hq : ∀ a, ¬ qAddr a < ctlAddr 0 := fun a => Nat.not_lt.mpr (ghost_q a)
  unfold low at hlow
  cases l with
  | rd m fl a sz v =>
    simp [Lab.acts, threadUnits, actUnits, ldAct] at hw; subst hw; simp [Ev.isW] at hW
  | wr m fl a sz v =>
    intro r hr hR
    simp [Lab.acts, threadUnits, actUnits, stAct] at hr; subst hr; simp [Ev.isR] at hR
  | rmw m a sz o n =>
    intro r hr hR
    simp [Lab.acts, threadUnits, actUnits, rmwAct] at hw hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl <;> simp_all [Ev.isW, Ev.isR]
  | fence k =>
    simp [Lab.acts, threadUnits, actUnits, fenceAct] at hw; subst hw; simp [Ev.isW] at hW
  | fwait a e seen r =>
    simp only [Lab.acts] at hw
    split at hw <;>
      simp [threadUnits, actUnits, fenceAct, stAct, ldAct, rmwAct] at hw <;>
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (exfalso; have := ghost_q a; simp only at hlow; omega) | simp_all [Ev.isW]
  | fwake a n q' =>
    simp [Lab.acts, threadUnits, actUnits, fenceAct, rmwAct] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      first | (exfalso; have := ghost_q a; simp only at hlow; omega) | simp_all [Ev.isW]
  | fblock a e => simp [LabOk] at hok
  | spawn t =>
    simp [Lab.acts, threadUnits, actUnits, ctlAct, rmwAct] at hw
    have := ghost_ctl t
    rcases hw with rfl | rfl <;> (exfalso; simp only at hlow; omega)
  | join t =>
    simp [Lab.acts, threadUnits, actUnits, endAct, rmwAct] at hw
    have := ghost_end t
    rcases hw with rfl | rfl <;> (exfalso; simp only at hlow; omega)
  | blk n ins outs rvs =>
    intro r hr hR
    simp only [Lab.acts, threadUnits_append, List.mem_append] at hw hr
    have hRs := loads_units_R i ins q
    rcases hw with hw | hw
    · exact absurd (hRs w hw) (by simp [Ev.isR, Ev.isW] at hW ⊢; simp [hW])
    · rcases hr with hr | hr
      · have h1 := (threadUnits_pos i _ _ r hr).2.2
        have h2 := (threadUnits_pos i _ _ w hw).2.1
        omega
      · have := (stores_units i outs _ r hr).2.1
        rw [hR] at this; cases this

/-- **A write unit of a label below the ghost bytes writes a value the label writes.** -/
theorem lab_write_val {locs : List Loc} (_hl : LocsFacts locs) {bs : List Block} {l : Lab}
    (hok : LabOk (cellsOf locs) bs l) (i q : Nat) {w : Ev × List Byte}
    (hw : w ∈ threadUnits i q l.acts) (hW : w.1.isW = true) (hlow : low w.1) :
    ∃ v ∈ l.written, v < 2 ^ (8 * w.1.size) ∧ w.1.data = natBytes v w.1.size := by
  unfold low at hlow
  cases l with
  | rd m fl a sz v =>
    simp [Lab.acts, threadUnits, actUnits, ldAct] at hw; subst hw; simp [Ev.isW] at hW
  | wr m fl a sz v =>
    simp only [LabOk] at hok
    simp [Lab.acts, threadUnits, actUnits, stAct] at hw; subst hw
    exact ⟨v, by simp [Lab.written], hok.2, rfl⟩
  | rmw m a sz o n =>
    simp only [LabOk] at hok
    simp [Lab.acts, threadUnits, actUnits, rmwAct] at hw
    rcases hw with rfl | rfl
    · simp [Ev.isW] at hW
    · exact ⟨n, by simp [Lab.written], hok.2.2, rfl⟩
  | fence k =>
    simp [Lab.acts, threadUnits, actUnits, fenceAct] at hw; subst hw; simp [Ev.isW] at hW
  | fwait a e seen r =>
    have hq := ghost_q a
    simp only [Lab.acts] at hw
    split at hw <;>
      simp [threadUnits, actUnits, fenceAct, stAct, ldAct, rmwAct] at hw <;>
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (exfalso; simp only at hlow; omega) | simp_all [Ev.isW]
  | fwake a n q' =>
    have hq := ghost_q a
    simp [Lab.acts, threadUnits, actUnits, fenceAct, rmwAct] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      first | (exfalso; simp only at hlow; omega) | simp_all [Ev.isW]
  | fblock a e => simp [LabOk] at hok
  | spawn t =>
    simp [Lab.acts, threadUnits, actUnits, ctlAct, rmwAct] at hw
    have := ghost_ctl t
    rcases hw with rfl | rfl <;> (exfalso; simp only at hlow; omega)
  | join t =>
    simp [Lab.acts, threadUnits, actUnits, endAct, rmwAct] at hw
    have := ghost_end t
    rcases hw with rfl | rfl <;> (exfalso; simp only at hlow; omega)
  | blk n ins outs rvs =>
    simp only [LabOk] at hok
    simp only [Lab.acts, threadUnits_append, List.mem_append] at hw
    rcases hw with hw | hw
    · have := loads_units_R i ins q w hw
      simp [Ev.isR, Ev.isW] at hW this; simp [hW] at this
    · obtain ⟨-, -, c, hc, ha, hs, hd⟩ := stores_units i outs _ w hw
      refine ⟨c.2.2, ?_, ?_, ?_⟩
      · simp only [Lab.written, List.mem_append, List.mem_map]
        exact .inl ⟨c, hc, rfl⟩
      · rw [hs]; exact (hok.1 c (List.mem_append_right _ hc)).2
      · rw [hd, hs]

end Silmaril.Proofs.X86.Concurrency.Cir.Domain
