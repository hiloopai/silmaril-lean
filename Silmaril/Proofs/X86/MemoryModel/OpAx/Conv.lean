module

public import Silmaril.X86.MemoryModel.OpAx.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms
public import Silmaril.Proofs.X86.MemoryModel.OpAx.Run

/-!
# Axiomatic x86-TSO candidates are reached by the store-buffer machine: proofs

The converse of `Run.lean` (`Task.axToOp`). Given an x86-TSO-consistent candidate `x` explaining
a final state of a program, we build a clock `κ` on the units from a linear extension of `ghb`
(the locked write of each read-modify-write placed one tick after its read), and then a machine
run that, at tick `t`, performs the action of the unit with clock `t`: a load or a locked
read-modify-write executes (after the thread's pending stores and fences are executed), a store
is flushed (and executed first if it is still pending). The machine state after tick `t` is
given in closed form (`cfg`), so each tick is a check of a few state equations.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.OpAx.Proofs.Conv

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.OpAx
open Silmaril.X86.MemoryModel.OpAx.Proofs (readMem_some covers_iff entryByte_eq writeMem_eq
  evUnits_tid evUnits_pos evUnits_data)
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush Byte Mem readMem writeMem readBufByte
  entryByte viewMem readView enqueue)
open Silmaril.X86.MemoryModel.Litmus (ACfg AStep)
open Relation

/-! ## The hypotheses -/

/-- Everything `Task.axToOp` assumes, with `Explains` unpacked. -/
structure Hyp (P : List (List (XEvent Nat))) (init : Tso.Mem) (s : XState Nat) (x : Exec)
    (us : List (Ev × List Byte)) : Prop where
  hT : ThreadsOk P
  hS : RmwSized P
  hI : InitCovers P init
  hd : ∀ t, s.buffer t = []
  hp : RmwPaired x
  perm : us.Perm (progUnits P)
  evs : x.evs = us.map Prod.fst
  tso : x.Tso
  reads : ∀ r < x.n, (x.evN r).isR = true →
    x.readBytes (fun y => (init y).getD 0) r = (us.getD r (dflt, [])).2
  rfW : ∀ r y w, x.rf r y = some w → w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true
  coM : ∀ y w, w ∈ x.co y ↔ w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true
  coN : ∀ y, (x.co y).Nodup
  fin : ∀ y, s.memory y = match (x.co y).getLast? with
    | none => init y
    | some w => some ((x.evN w).byte y)

/-- Event `c` of thread `i`. -/
def E (P : List (List (XEvent Nat))) (i c : Nat) : Option (XEvent Nat) := (P[i]?.getD [])[c]?

theorem mem_progUnits {P : List (List (XEvent Nat))} {p : Ev × List Byte} :
    p ∈ progUnits P ↔ ∃ i c ev, E P i c = some ev ∧ p ∈ evUnits i c ev := by
  constructor
  · intro hm
    simp only [progUnits, List.mem_flatten, List.mem_mapIdx] at hm
    obtain ⟨_, ⟨i, hi, rfl⟩, hp⟩ := hm
    simp only [threadUnits, List.mem_flatten, List.mem_mapIdx] at hp
    obtain ⟨_, ⟨c, hc, rfl⟩, hp⟩ := hp
    exact ⟨i, c, _, by simp [E, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hc], hp⟩
  · rintro ⟨i, c, ev, he, hp⟩
    have hi : i < P.length := by
      by_contra hn
      simp [E, List.getElem?_eq_none (show P.length ≤ i by omega)] at he
    simp only [E, List.getElem?_eq_getElem hi, Option.getD_some] at he
    have hc : c < P[i].length := by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at he
      simp at he
    rw [List.getElem?_eq_getElem hc, Option.some.injEq] at he
    subst he
    simp only [progUnits, List.mem_flatten, List.mem_mapIdx]
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    simp only [threadUnits, List.mem_flatten, List.mem_mapIdx]
    exact ⟨_, ⟨c, hc, rfl⟩, hp⟩

section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

theorem Hyp.n_eq (h : Hyp P init s x us) : x.n = us.length := by
  simp [Exec.n, h.evs]

theorem Hyp.evN_eq (h : Hyp P init s x us) {u : Nat} (hu : u < us.length) :
    x.evN u = (us[u]).1 := by
  simp [Exec.evN, h.evs, List.getD_eq_getElem?_getD, hu]

theorem Hyp.getD_eq {u : Nat} (hu : u < us.length) : us.getD u (dflt, []) = us[u] := by
  simp [List.getD_eq_getElem?_getD, hu]

/-- Every unit comes from an event of the program. -/
theorem Hyp.unit (h : Hyp P init s x us) {u : Nat} (hu : u < x.n) :
    ∃ c ev, E P (x.evN u).tid c = some ev ∧
      (x.evN u, (us.getD u (dflt, [])).2) ∈ evUnits (x.evN u).tid c ev := by
  rw [h.n_eq] at hu
  have hm : us[u] ∈ progUnits P := h.perm.subset (List.getElem_mem hu)
  obtain ⟨i, c, ev, he, hp⟩ := mem_progUnits.mp hm
  have ht := evUnits_tid hp
  rw [h.evN_eq hu, Hyp.getD_eq hu, ht]
  exact ⟨c, ev, he, hp⟩

/-- Every unit of the program is a unit of the candidate. -/
theorem Hyp.ofEvent (h : Hyp P init s x us) {i c : Nat} {ev : XEvent Nat}
    (he : E P i c = some ev) {p : Ev × List Byte} (hp : p ∈ evUnits i c ev) :
    ∃ u < x.n, x.evN u = p.1 ∧ (us.getD u (dflt, [])).2 = p.2 := by
  have hm : p ∈ us := h.perm.symm.subset (mem_progUnits.mpr ⟨i, c, ev, he, hp⟩)
  obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hm
  exact ⟨u, by rw [h.n_eq]; exact hu, h.evN_eq hu, by rw [Hyp.getD_eq hu]⟩

/-- Units of one event have distinct positions. -/
theorem evUnits_pairwise (i c : Nat) (ev : XEvent Nat) :
    (evUnits i c ev).Pairwise fun p q => (p.1.tid, p.1.pos) ≠ (q.1.tid, q.1.pos) := by
  cases ev <;> simp [evUnits]

theorem threadUnits_pairwise (i : Nat) (l : List (XEvent Nat)) :
    (threadUnits i l).Pairwise fun p q => (p.1.tid, p.1.pos) ≠ (q.1.tid, q.1.pos) := by
  unfold threadUnits
  rw [List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro l' hl
    obtain ⟨c, hc, rfl⟩ := List.mem_mapIdx.mp hl
    exact evUnits_pairwise i c _
  · rw [List.pairwise_iff_getElem]
    intro a b ha hb hab p hp q hq
    simp only [List.getElem_mapIdx] at hp hq
    have h1 := evUnits_pos hp
    have h2 := evUnits_pos hq
    simp only [List.length_mapIdx] at ha hb
    intro he
    simp only [Prod.mk.injEq] at he
    omega

theorem progUnits_pairwise (P : List (List (XEvent Nat))) :
    (progUnits P).Pairwise fun p q => (p.1.tid, p.1.pos) ≠ (q.1.tid, q.1.pos) := by
  unfold progUnits
  rw [List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro l' hl
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hl
    exact threadUnits_pairwise i _
  · rw [List.pairwise_iff_getElem]
    intro a b ha hb hab p hp q hq
    simp only [List.getElem_mapIdx] at hp hq
    have h1 := Proofs.threadUnits_tid hp
    have h2 := Proofs.threadUnits_tid hq
    intro he
    simp only [Prod.mk.injEq] at he
    omega

/-- Units are determined by their thread and position. -/
theorem Hyp.uniq (h : Hyp P init s x us) {a b : Nat} (ha : a < x.n) (hb : b < x.n)
    (ht : (x.evN a).tid = (x.evN b).tid) (hp : (x.evN a).pos = (x.evN b).pos) : a = b := by
  have hpw := (h.perm.symm.pairwise (progUnits_pairwise P) (fun h e => h e.symm))
  rw [List.pairwise_iff_getElem] at hpw
  rw [h.n_eq] at ha hb
  rw [h.evN_eq ha, h.evN_eq hb] at ht hp
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hpw a b ha hb hlt (by rw [ht, hp])
  · exact hpw b a hb ha hlt (by rw [ht, hp])

end

/-! ## Edges of the relations, on `Nat` indices -/

section
variable {x : Exec}

theorem ev_eq (a : Fin x.n) : x.ev a = x.evN a.val := by
  simp [Exec.ev, Exec.evN, List.getD_eq_getElem?_getD]

theorem mem_bytes {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.covers y = true := by
  simp [Ev.bytes, Ev.covers, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨y - e.addr, by omega, by omega⟩

theorem po_iff {a b : Fin x.n} : x.po a b = true ↔
    (x.evN a.val).tid = (x.evN b.val).tid ∧ (x.evN a.val).pos < (x.evN b.val).pos := by
  simp [Exec.po, ev_eq]

theorem rfR_mk {w r : Fin x.n} {y : Nat} (hw : (x.evN w.val).isW = true)
    (hr : (x.evN r.val).isR = true) (hcr : (x.evN r.val).covers y = true)
    (hcw : (x.evN w.val).covers y = true) (hrf : x.rf r.val y = some w.val) :
    x.rfR w r = true := by
  simp only [Exec.rfR, ev_eq, hw, hr, Bool.true_and, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq]
  exact ⟨y, mem_bytes.mpr hcr, hrf, hcw⟩

theorem coR_mk {a b : Fin x.n} {y : Nat} (ha : (x.evN a.val).isW = true)
    (hb : (x.evN b.val).isW = true) (hca : (x.evN a.val).covers y = true)
    (hcb : (x.evN b.val).covers y = true) (hbe : before (x.co y) a.val b.val = true) :
    x.coR a b = true := by
  simp only [Exec.coR, ev_eq, ha, hb, Bool.true_and, List.any_eq_true, Bool.and_eq_true]
  exact ⟨y, mem_bytes.mpr hca, hcb, hbe⟩

theorem frR_mk {r w : Fin x.n} {y : Nat} (hr : (x.evN r.val).isR = true)
    (hw : (x.evN w.val).isW = true) (hcr : (x.evN r.val).covers y = true)
    (hcw : (x.evN w.val).covers y = true)
    (hm : match x.rf r.val y with
      | none => True
      | some v => before (x.co y) v w.val = true) :
    x.frR r w = true := by
  simp only [Exec.frR, ev_eq, hr, hw, Bool.true_and, List.any_eq_true, Bool.and_eq_true]
  refine ⟨y, mem_bytes.mpr hcr, hcw, ?_⟩
  revert hm
  cases x.rf r.val y <;> simp

theorem frR_elim {r w : Fin x.n} (h : x.frR r w = true) :
    (x.evN r.val).isR = true ∧ (x.evN w.val).isW = true ∧ ∃ y,
      (x.evN r.val).covers y = true ∧ (x.evN w.val).covers y = true ∧
      match x.rf r.val y with
      | none => True
      | some v => before (x.co y) v w.val = true := by
  simp only [Exec.frR, ev_eq, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨h1, h2⟩, y, hy, h3, h4⟩ := h
  refine ⟨h1, h2, y, mem_bytes.mp hy, h3, ?_⟩
  revert h4
  cases x.rf r.val y <;> simp

theorem com_of_rfR {a b : Fin x.n} (h : x.rfR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union, h]

theorem com_of_coR {a b : Fin x.n} (h : x.coR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union, h]

theorem com_of_frR {a b : Fin x.n} (h : x.frR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union, h]

theorem uniproc_of_com {a b : Fin x.n} (h : x.com a b = true) : x.uniproc a b = true := by
  simp only [Exec.uniproc, BRel.union_iff]
  exact .inr (BRel.seq_of_left x.sm_refl h)

theorem uniproc_of_poLoc {a b : Fin x.n} (hpo : x.po a b = true)
    (hma : (x.evN a.val).isM = true) (hmb : (x.evN b.val).isM = true) {y : Nat}
    (hca : (x.evN a.val).covers y = true) (hcb : (x.evN b.val).covers y = true) :
    x.uniproc a b = true := by
  simp only [Exec.uniproc, BRel.union_iff]
  left
  simp only [Exec.poLoc, BRel.inter_iff, hpo, true_and, Exec.loc, ev_eq, hma, hmb,
    Bool.true_and, List.any_eq_true]
  exact ⟨y, mem_bytes.mpr hca, hcb⟩

theorem ghb_of_comGhb {a b : Fin x.n} (h : (x.rfe.union (x.frR.union x.coR)) a b = true) :
    x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  exact .inr (.inr (.inr (BRel.seq_of_left x.sm_refl h)))

theorem ghb_of_frR {a b : Fin x.n} (h : x.frR a b = true) : x.ghb a b = true :=
  ghb_of_comGhb (by simp [BRel.union, h])

theorem ghb_of_coR {a b : Fin x.n} (h : x.coR a b = true) : x.ghb a b = true :=
  ghb_of_comGhb (by simp [BRel.union, h])

theorem ghb_of_rfe {a b : Fin x.n} (h : x.rfR a b = true)
    (ht : (x.evN a.val).tid ≠ (x.evN b.val).tid) : x.ghb a b = true :=
  ghb_of_comGhb (by simp [BRel.union, BRel.inter, Exec.rfe, Exec.ext, ev_eq, h, ht])

theorem ghb_of_ppo {a b : Fin x.n} (hpo : x.po a b = true)
    (hk : ((x.evN a.val).isW = true ∧ (x.evN b.val).isW = true) ∨
      ((x.evN a.val).isR = true ∧ (x.evN b.val).isM = true)) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  refine .inr (.inr (.inl ?_))
  simp only [Exec.ppo, hpo, ev_eq, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
  exact hk

theorem ghb_of_implied {a b : Fin x.n} (hpo : x.po a b = true) (ha : (x.evN a.val).isW = true)
    (hb : (x.evN b.val).isR = true)
    (hl : (x.evN a.val).isA = true ∨ (x.evN b.val).isA = true) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  refine .inr (.inl ?_)
  simp only [Exec.implied, hpo, ev_eq, ha, hb, Bool.true_and, Bool.or_eq_true]
  exact hl

theorem ghb_of_mfence {a b f : Fin x.n} (hf : (x.evN f.val).isFence .mfence = true)
    (h1 : x.po a f = true) (h2 : x.po f b = true) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  refine .inl ?_
  simp only [Exec.mfence, Exec.fencerel, List.any_eq_true, Bool.and_eq_true, ev_eq]
  exact ⟨f, List.mem_finRange f, ⟨hf, h1⟩, h2⟩

/-- The `ghb` edges, case by case. -/
theorem ghb_cases (hsm : ∀ c d : Fin x.n, x.sm c d = true → c = d) {a b : Fin x.n}
    (h : x.ghb a b = true) :
    (∃ f : Fin x.n, (x.evN f.val).isFence .mfence = true ∧ x.po a f = true ∧ x.po f b = true) ∨
    (x.po a b = true ∧ (x.evN a.val).isW = true ∧ (x.evN b.val).isR = true ∧
      ((x.evN a.val).isA = true ∨ (x.evN b.val).isA = true)) ∨
    (x.po a b = true ∧ (((x.evN a.val).isW = true ∧ (x.evN b.val).isW = true) ∨
      ((x.evN a.val).isR = true ∧ (x.evN b.val).isM = true))) ∨
    (x.rfR a b = true ∧ (x.evN a.val).tid ≠ (x.evN b.val).tid) ∨ x.frR a b = true ∨
      x.coR a b = true := by
  simp only [Exec.ghb, BRel.union_iff] at h
  rcases h with h | h | h | h
  · simp only [Exec.mfence, Exec.fencerel, List.any_eq_true, Bool.and_eq_true, ev_eq] at h
    obtain ⟨f, -, ⟨hf, h1⟩, h2⟩ := h
    exact .inl ⟨f, hf, h1, h2⟩
  · simp only [Exec.implied, ev_eq, Bool.and_eq_true, Bool.or_eq_true] at h
    exact .inr (.inl ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
  · simp only [Exec.ppo, ev_eq, Bool.and_eq_true, Bool.or_eq_true] at h
    exact .inr (.inr (.inl ⟨h.1, h.2⟩))
  · obtain ⟨c, hc, hsm'⟩ := BRel.seq_elim h
    obtain rfl := hsm c b hsm'
    simp only [BRel.union_iff, Exec.rfe, BRel.inter_iff, Exec.ext, ev_eq, bne_iff_ne, ne_eq] at hc
    rcases hc with hc | hc | hc
    · exact .inr (.inr (.inr (.inl hc)))
    · exact .inr (.inr (.inr (.inr (.inl hc))))
    · exact .inr (.inr (.inr (.inr (.inr hc))))

end


/-! ## `before` -/

theorem before_mem : ∀ {l : List Nat} {a b : Nat}, before l a b = true → a ∈ l ∧ b ∈ l
  | [], _, _, h => by simp [before] at h
  | c :: l, a, b, h => by
    simp only [before] at h
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc
      subst hc
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (by simpa using h)⟩
    · obtain ⟨h1, h2⟩ := before_mem h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem before_total : ∀ {l : List Nat} {a b : Nat}, a ∈ l → b ∈ l → a ≠ b →
    before l a b = true ∨ before l b a = true
  | [], _, _, h, _, _ => by simp at h
  | c :: l, a, b, ha, hb, hab => by
    simp only [before]
    by_cases hca : c = a
    · subst hca
      have : b ∈ l := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h.symm hab
        · exact h
      simp [this]
    · by_cases hcb : c = b
      · subst hcb
        have : a ∈ l := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h.symm hca
          · exact h
        simp [this]
      · have ha' : a ∈ l := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h.symm hca
          · exact h
        have hb' : b ∈ l := by
          rcases List.mem_cons.mp hb with h | h
          · exact absurd h.symm hcb
          · exact h
        simp only [beq_iff_eq, hca, hcb, ↓reduceIte]
        exact before_total ha' hb' hab

theorem last_filter {p : Nat → Bool} : ∀ {l : List Nat} {s : Nat}, s ∈ l → p s = true →
    (∀ w ∈ l, before l s w = true → p w = false) → (l.filter p).getLast? = some s
  | [], _, h, _, _ => by simp at h
  | c :: l, s, hs, hp, hw => by
    by_cases hcs : c = s
    · subst hcs
      have : l.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro w hwl
        simp [hw w (List.mem_cons_of_mem _ hwl) (by simp [before, hwl])]
      simp [hp, this]
    · have hs' : s ∈ l := by
        rcases List.mem_cons.mp hs with h | h
        · exact absurd h.symm hcs
        · exact h
      have ih := last_filter (p := p) hs' hp fun w hwl hb =>
        hw w (List.mem_cons_of_mem _ hwl) (by simp [before, hcs, hb])
      rw [List.filter_cons]
      split
      · rw [List.getLast?_cons, ih]; rfl
      · exact ih

theorem last_filter_none {p : Nat → Bool} {l : List Nat} (h : ∀ w ∈ l, p w = false) :
    (l.filter p).getLast? = none := by
  rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff]
  intro w hw; simp [h w hw]

/-! ## Consequences of the hypotheses -/

section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

theorem Hyp.sm (h : Hyp P init s x us) (c d : Fin x.n) (hsm : x.sm c d = true) : c = d := by
  simp only [Exec.sm, ev_eq, Bool.and_eq_true, beq_iff_eq] at hsm
  exact Fin.ext (h.uniq c.isLt d.isLt hsm.1 hsm.2)

theorem Hyp.unip2 (h : Hyp P init s x us) {a b : Fin x.n} (h1 : x.uniproc a b = true)
    (h2 : x.uniproc b a = true) : False :=
  h.tso.2.1 a (TransGen.tail (TransGen.single h1) h2)

theorem Hyp.ghb2 (h : Hyp P init s x us) {a b : Fin x.n} (h1 : x.ghb a b = true)
    (h2 : x.ghb b a = true) : False :=
  h.tso.2.2 a (TransGen.tail (TransGen.single h1) h2)

theorem Hyp.ghb1 (h : Hyp P init s x us) {a : Fin x.n} (h1 : x.ghb a a = true) : False :=
  h.tso.2.2 a (TransGen.single h1)

theorem Hyp.atomic (h : Hyp P init s x us) {r w c : Fin x.n} (hrw : (r.val, w.val) ∈ x.rmw)
    (h1 : x.frR r c = true) (h1e : (x.evN r.val).tid ≠ (x.evN c.val).tid)
    (h2 : x.coR c w = true) (h2e : (x.evN c.val).tid ≠ (x.evN w.val).tid) : False := by
  have ha := h.tso.1
  rw [Exec.atomicB, BRel.emptyB_iff] at ha
  have := ha r w
  have hc : x.rmw.contains (r.val, w.val) = true := by simpa using hrw
  have hs : (x.fre.seq x.coe) r w = true := by
    simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
    refine ⟨c, List.mem_finRange c, ?_, ?_⟩
    · simp [Exec.fre, BRel.inter, Exec.ext, ev_eq, h1, h1e]
    · simp [Exec.coe, BRel.inter, Exec.ext, ev_eq, h2, h2e]
  simp [BRel.inter, Exec.rmwR, hs] at this
  exact this hrw

theorem E_mem {P : List (List (XEvent Nat))} {i c : Nat} {ev : XEvent Nat}
    (he : E P i c = some ev) : ∃ es, P[i]? = some es ∧ ev ∈ es := by
  unfold E at he
  cases hp : P[i]? with
  | none => rw [hp] at he; simp at he
  | some es =>
    rw [hp] at he
    exact ⟨es, rfl, List.mem_of_getElem? he⟩

theorem Hyp.thread (h : Hyp P init s x us) {i c : Nat} {ev : XEvent Nat}
    (he : E P i c = some ev) : XEvent.thread ev = i := by
  obtain ⟨es, hes, hev⟩ := E_mem he
  exact h.hT i es hes ev hev

/-- The unit of a load. -/
def loadU (i c a n : Nat) : Ev := { tid := i, pos := 2 * c, act := .read, addr := a, size := n }
/-- The unit of a store. -/
def storeU (i c a : Nat) (bs : List Byte) : Ev :=
  { tid := i, pos := 2 * c, act := .write, addr := a, size := bs.length, data := bs }
/-- The read unit of a locked read-modify-write. -/
def rmwRU (i c a n : Nat) : Ev :=
  { tid := i, pos := 2 * c, act := .read, addr := a, size := n, locked := true }
/-- The write unit of a locked read-modify-write. -/
def rmwWU (i c a : Nat) (bs : List Byte) : Ev :=
  { tid := i, pos := 2 * c + 1, act := .write, addr := a, size := bs.length, locked := true,
    data := bs }
/-- The unit of a fence. -/
def fenceU (i c : Nat) : Ev := { tid := i, pos := 2 * c, act := .fence .mfence }

/-- The five shapes of a unit. -/
theorem Hyp.kind (h : Hyp P init s x us) {u : Nat} (hu : u < x.n) :
    (∃ c a bs, E P (x.evN u).tid c = some (.load (x.evN u).tid a bs) ∧
      x.evN u = loadU (x.evN u).tid c a bs.length ∧ (us.getD u (dflt, [])).2 = bs) ∨
    (∃ c a bs, E P (x.evN u).tid c = some (.store (x.evN u).tid a bs) ∧
      x.evN u = storeU (x.evN u).tid c a bs) ∨
    (∃ c a old new, E P (x.evN u).tid c = some (.rmw (x.evN u).tid a old new) ∧
      new.length = old.length ∧
      ((x.evN u = rmwRU (x.evN u).tid c a old.length ∧ (us.getD u (dflt, [])).2 = old) ∨
        x.evN u = rmwWU (x.evN u).tid c a new)) ∨
    (∃ c, E P (x.evN u).tid c = some (.fence (x.evN u).tid) ∧
      x.evN u = fenceU (x.evN u).tid c) := by
  obtain ⟨c, ev, he, hp⟩ := h.unit hu
  have ht := h.thread he
  obtain ⟨es, hes, hev⟩ := E_mem he
  cases ev with
  | load t a bs =>
    simp only [XEvent.thread] at ht; subst ht
    simp only [evUnits, List.mem_singleton, Prod.mk.injEq] at hp
    exact .inl ⟨c, a, bs, he, hp.1, hp.2⟩
  | store t a bs =>
    simp only [XEvent.thread] at ht; subst ht
    simp only [evUnits, List.mem_singleton, Prod.mk.injEq] at hp
    exact .inr (.inl ⟨c, a, bs, he, hp.1⟩)
  | rmw t a old new =>
    simp only [XEvent.thread] at ht; subst ht
    have hl := h.hS _ es hes _ hev _ a old new rfl
    simp only [evUnits, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp
    · exact .inr (.inr (.inl ⟨c, a, old, new, he, hl, .inl ⟨hp.1, hp.2⟩⟩))
    · exact .inr (.inr (.inl ⟨c, a, old, new, he, hl, .inr hp.1⟩))
  | fence t =>
    simp only [XEvent.thread] at ht; subst ht
    simp only [evUnits, List.mem_singleton, Prod.mk.injEq] at hp
    exact .inr (.inr (.inr ⟨c, he, hp.1⟩))

end


/-! ## Read-modify-write blocks -/

/-- The index of the unit of thread `i` at position `p`. -/
def pidx (x : Exec) (i p : Nat) : Nat := x.evs.findIdx fun e => e.tid == i && e.pos == p

/-- A locked read. -/
def isLR (e : Ev) : Bool := e.isR && e.locked
/-- A locked write. -/
def isLW (e : Ev) : Bool := e.isW && e.locked

/-- The first unit of `u`'s block: the read of a locked write, else `u`. -/
def fstU (x : Exec) (u : Nat) : Nat :=
  if isLW (x.evN u) then pidx x (x.evN u).tid ((x.evN u).pos - 1) else u

/-- The last unit of `u`'s block: the write of a locked read, else `u`. -/
def lstU (x : Exec) (u : Nat) : Nat :=
  if isLR (x.evN u) then pidx x (x.evN u).tid ((x.evN u).pos + 1) else u

/-- `ghb` on `Nat` indices. -/
def GN (x : Exec) (a b : Nat) : Prop := ∃ (ha : a < x.n) (hb : b < x.n), x.ghb ⟨a, ha⟩ ⟨b, hb⟩ = true

theorem GN.lt {x : Exec} {a b : Nat} (h : TransGen (GN x) a b) : a < x.n ∧ b < x.n := by
  induction h with
  | single h => exact ⟨h.1, h.2.1⟩
  | tail _ h ih => exact ⟨ih.1, h.2.1⟩

theorem GN.fin {x : Exec} {a b : Nat} (h : TransGen (GN x) a b) (ha : a < x.n) (hb : b < x.n) :
    TransGen x.ghb.Holds ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | single h => obtain ⟨_, _, h⟩ := h; exact .single h
  | tail h1 h ih =>
    obtain ⟨hc, _, h⟩ := h
    exact .tail (ih hc) h

section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

theorem Hyp.gnAcyc (h : Hyp P init s x us) {a : Nat} (hc : TransGen (GN x) a a) : False := by
  have := GN.lt hc
  exact h.tso.2.2 ⟨a, this.1⟩ (GN.fin hc this.1 this.1)

theorem Hyp.pidx_eq (h : Hyp P init s x us) {u : Nat} (hu : u < x.n) :
    pidx x (x.evN u).tid (x.evN u).pos = u := by
  set q := (fun e : Ev => e.tid == (x.evN u).tid && e.pos == (x.evN u).pos) with hq
  have hex : ∃ e ∈ x.evs, q e = true :=
    ⟨x.evN u, by
      simp only [Exec.evN, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem hu]; simp, by simp [hq]⟩
  have hlt : x.evs.findIdx q < x.evs.length := List.findIdx_lt_length_of_exists hex
  have hp := List.findIdx_getElem (w := hlt)
  simp only [hq, Bool.and_eq_true, beq_iff_eq] at hp
  have hev : x.evN (pidx x (x.evN u).tid (x.evN u).pos) = x.evs[x.evs.findIdx q] := by
    show x.evs.getD (x.evs.findIdx q) _ = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
  exact h.uniq hlt hu (by rw [hev]; exact hp.1) (by rw [hev]; exact hp.2)

/-- The write half of a locked read. -/
theorem Hyp.partnerR (h : Hyp P init s x us) {r : Nat} (hr : r < x.n)
    (hl : isLR (x.evN r) = true) : ∃ w < x.n, (x.evN w).tid = (x.evN r).tid ∧
      (x.evN w).pos = (x.evN r).pos + 1 ∧ isLW (x.evN w) = true ∧
      (x.evN w).addr = (x.evN r).addr ∧ (x.evN w).size = (x.evN r).size := by
  rcases h.kind hr with ⟨c, a, bs, he, hev, -⟩ | ⟨c, a, bs, he, hev⟩ |
      ⟨c, a, old, new, he, hlen, ⟨hev, -⟩ | hev⟩ | ⟨c, he, hev⟩ <;>
    rw [hev] at hl <;> simp [isLR, loadU, storeU, rmwRU, rmwWU, fenceU, Ev.isR] at hl
  obtain ⟨w, hw, hwe, -⟩ := h.ofEvent he (p := (rmwWU (x.evN r).tid c a new, []))
    (by simp [evUnits, rmwWU])
  refine ⟨w, hw, ?_⟩
  rw [hwe, hev]
  simp [rmwWU, rmwRU, isLW, Ev.isW, hlen]

/-- The read half of a locked write. -/
theorem Hyp.partnerW (h : Hyp P init s x us) {w : Nat} (hw : w < x.n)
    (hl : isLW (x.evN w) = true) : ∃ r < x.n, (x.evN r).tid = (x.evN w).tid ∧
      (x.evN w).pos = (x.evN r).pos + 1 ∧ isLR (x.evN r) = true ∧
      (x.evN w).addr = (x.evN r).addr ∧ (x.evN w).size = (x.evN r).size := by
  rcases h.kind hw with ⟨c, a, bs, he, hev, -⟩ | ⟨c, a, bs, he, hev⟩ |
      ⟨c, a, old, new, he, hlen, ⟨hev, -⟩ | hev⟩ | ⟨c, he, hev⟩ <;>
    rw [hev] at hl <;> simp [isLW, loadU, storeU, rmwRU, rmwWU, fenceU, Ev.isW] at hl
  obtain ⟨r, hr, hre, -⟩ := h.ofEvent he (p := (rmwRU (x.evN w).tid c a old.length, old))
    (by simp [evUnits, rmwRU])
  refine ⟨r, hr, ?_⟩
  rw [hre, hev]
  simp [rmwWU, rmwRU, isLR, Ev.isR, hlen]

theorem Hyp.fst_lw (h : Hyp P init s x us) {w r : Nat} (hl : isLW (x.evN w) = true) (hr : r < x.n)
    (ht : (x.evN r).tid = (x.evN w).tid) (hp : (x.evN w).pos = (x.evN r).pos + 1) :
    fstU x w = r := by
  simp only [fstU, hl, ↓reduceIte]
  rw [← ht, hp, Nat.add_sub_cancel]
  exact h.pidx_eq hr

theorem Hyp.lst_lr (h : Hyp P init s x us) {w r : Nat} (hl : isLR (x.evN r) = true) (hw : w < x.n)
    (ht : (x.evN w).tid = (x.evN r).tid) (hp : (x.evN w).pos = (x.evN r).pos + 1) :
    lstU x r = w := by
  simp only [lstU, hl, ↓reduceIte]
  rw [← ht, ← hp]
  exact h.pidx_eq hw

theorem fst_of {x : Exec} {u : Nat} (h : isLW (x.evN u) = false) : fstU x u = u := by
  simp [fstU, h]

theorem lst_of {x : Exec} {u : Nat} (h : isLR (x.evN u) = false) : lstU x u = u := by
  simp [lstU, h]

theorem lr_lw {e : Ev} (h : isLR e = true) : isLW e = false := by
  simp only [isLR, isLW, Ev.isR, Ev.isW, Bool.and_eq_true, beq_iff_eq] at h ⊢
  simp [h.1]

theorem lw_lr {e : Ev} (h : isLW e = true) : isLR e = false := by
  simp only [isLR, isLW, Ev.isR, Ev.isW, Bool.and_eq_true, beq_iff_eq] at h ⊢
  simp [h.1]

/-- Atomicity, as the shape of the `ghb` successors of a locked read: every one except its write
half is a successor of the write half. -/
theorem Hyp.lemA (h : Hyp P init s x us) {r w b : Nat} (hr : r < x.n) (hw : w < x.n)
    (hb : b < x.n) (hlr : isLR (x.evN r) = true) (ht : (x.evN w).tid = (x.evN r).tid)
    (hp : (x.evN w).pos = (x.evN r).pos + 1) (hlw : isLW (x.evN w) = true)
    (ha : (x.evN w).addr = (x.evN r).addr) (hs : (x.evN w).size = (x.evN r).size)
    (hg : x.ghb ⟨r, hr⟩ ⟨b, hb⟩ = true) (hne : b ≠ w) : x.ghb ⟨w, hw⟩ ⟨b, hb⟩ = true := by
  have hrR : (x.evN r).isR = true := by simp_all [isLR]
  have hrW : (x.evN r).isW = false := by
    simp only [isLR, Ev.isR, Bool.and_eq_true, beq_iff_eq] at hlr; simp [Ev.isW, hlr.1]
  have hwW : (x.evN w).isW = true := by simp_all [isLW]
  have hwA : (x.evN w).isA = true := by
    simp only [isLW, Bool.and_eq_true] at hlw; simp [Ev.isA, Ev.isM, hlw]
  have hwR : (x.evN w).isR = false := by
    simp only [isLW, Ev.isW, Bool.and_eq_true, beq_iff_eq] at hlw; simp [Ev.isR, hlw.1]
  -- `b` after `r` in program order is after `w`
  have after : (x.evN b).tid = (x.evN r).tid → (x.evN r).pos < (x.evN b).pos →
      (x.evN w).pos < (x.evN b).pos := by
    intro htb hpb
    rw [hp]
    rcases Nat.lt_or_ge (x.evN r).pos ((x.evN b).pos - 1) with h1 | h1
    · omega
    · exfalso; exact hne (h.uniq hb hw (by rw [htb, ht]) (by omega))
  rcases ghb_cases h.sm hg with ⟨f, hf, h1, h2⟩ | ⟨-, hW, -⟩ | ⟨hpo, hk⟩ | ⟨hrf, -⟩ | hfr | hco
  · rw [po_iff] at h1
    simp only at h1
    have hfw : f.val ≠ w := by
      rintro hfw
      have : (x.evN f.val).isFence .mfence = false := by
        rw [hfw]; simp only [isLW, Ev.isW, Bool.and_eq_true, beq_iff_eq] at hlw
        simp [Ev.isFence, hlw.1]
      rw [this] at hf; cases hf
    have : (x.evN w).pos < (x.evN f.val).pos := by
      rw [hp]
      rcases Nat.lt_or_ge ((x.evN r).pos + 1) (x.evN f.val).pos with h3 | h3
      · exact h3
      · exfalso; exact hfw (h.uniq f.isLt hw (by rw [← h1.1, ht]) (by omega))
    exact ghb_of_mfence hf (po_iff.mpr ⟨by rw [ht, h1.1], this⟩) h2
  · simp only at hW; rw [hrW] at hW; cases hW
  · rw [po_iff] at hpo
    have hpo' : x.po ⟨w, hw⟩ ⟨b, hb⟩ = true :=
      po_iff.mpr ⟨by simp only; rw [ht, hpo.1], after hpo.1.symm hpo.2⟩
    rcases hk with ⟨hk, -⟩ | ⟨-, hbM⟩
    · simp only at hk; rw [hrW] at hk; cases hk
    · simp only at hbM
      cases hbW : (x.evN b).isW
      · have hbR : (x.evN b).isR = true := by simpa [Ev.isM, hbW] using hbM
        exact ghb_of_implied hpo' hwW hbR (.inl hwA)
      · exact ghb_of_ppo hpo' (.inl ⟨hwW, hbW⟩)
  · simp only [Exec.rfR, ev_eq, Bool.and_eq_true] at hrf
    rw [hrW] at hrf; simp at hrf
  · obtain ⟨-, hbW, y, hcr, hcb, hm⟩ := frR_elim hfr
    simp only at hbW hcr hcb hm
    have hcw : (x.evN w).covers y = true := by
      simp only [covers_iff, ha, hs] at hcr ⊢; exact hcr
    have hbco : b ∈ x.co y := (h.coM y b).mpr ⟨hb, hbW, hcb⟩
    have hwco : w ∈ x.co y := (h.coM y w).mpr ⟨hw, hwW, hcw⟩
    rcases before_total hwco hbco (Ne.symm hne) with hwb | hbw
    · exact ghb_of_coR (coR_mk (a := ⟨w, hw⟩) (b := ⟨b, hb⟩) hwW hbW hcw hcb hwb)
    · exfalso
      have hcbw : x.coR ⟨b, hb⟩ ⟨w, hw⟩ = true := coR_mk hbW hwW hcb hcw hbw
      by_cases htb : (x.evN b).tid = (x.evN r).tid
      · rcases Nat.lt_trichotomy (x.evN b).pos (x.evN r).pos with h1 | h1 | h1
        · exact h.unip2 (a := ⟨b, hb⟩) (b := ⟨r, hr⟩)
            (uniproc_of_poLoc (po_iff.mpr ⟨htb, h1⟩) (by simp [Ev.isM, hbW])
              (by simp [Ev.isM, hrR]) hcb hcr) (uniproc_of_com (com_of_frR hfr))
        · have := h.uniq hb hr htb h1
          subst this; rw [hrW] at hbW; cases hbW
        · have h2 := after htb h1
          exact h.unip2 (a := ⟨w, hw⟩) (b := ⟨b, hb⟩)
            (uniproc_of_poLoc (po_iff.mpr ⟨by simp only; rw [ht, htb], h2⟩)
              (by simp [Ev.isM, hwW]) (by simp [Ev.isM, hbW]) hcw hcb)
            (uniproc_of_com (com_of_coR hcbw))
      · have hrw : (r, w) ∈ x.rmw := h.hp r hr w hw hrR hwW
          (by simp_all [isLR]) (by simp_all [isLW]) ht.symm hp
        exact h.atomic (r := ⟨r, hr⟩) (w := ⟨w, hw⟩) (c := ⟨b, hb⟩) hrw hfr (Ne.symm htb) hcbw
          (by simp only; rw [ht]; exact htb)
  · simp only [Exec.coR, ev_eq, Bool.and_eq_true] at hco
    rw [hrW] at hco; simp at hco

end


/-! ## The clock -/

/-- Block order: the block of `d` is `ghb`-before the block of `c` (compared at their last units). -/
def QB (x : Exec) (d c : Nat) : Prop := TransGen (GN x) (lstU x d) (lstU x c)

open Classical in
/-- The number of blocks before `c`'s (a linear extension of `QB`). -/
noncomputable def gH (x : Exec) (c : Nat) : Nat := ((Finset.range x.n).filter fun d => QB x d c).card

/-- `1` on locked writes. -/
def bit (x : Exec) (u : Nat) : Nat := if isLW (x.evN u) then 1 else 0

/-- **The clock**: blocks in the order `gH` (ties broken by index), the locked write of a block
one tick after its read. -/
noncomputable def κ (x : Exec) (u : Nat) : Nat := 2 * (gH x (fstU x u) * x.n + fstU x u) + bit x u

section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

theorem Hyp.gH_lt (h : Hyp P init s x us) {a b : Nat} (ha : a < x.n) (hq : QB x a b) :
    gH x a < gH x b := by
  classical
  unfold gH
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ha, hq⟩
    · simp only [Finset.mem_filter, Finset.mem_range, not_and]
      intro _ hq'
      exact h.gnAcyc hq'
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢
    exact ⟨hd.1, hd.2.trans hq⟩

theorem Hyp.fst_spec (h : Hyp P init s x us) {u : Nat} (hu : u < x.n) :
    fstU x u < x.n ∧ isLW (x.evN (fstU x u)) = false ∧ fstU x (fstU x u) = fstU x u := by
  cases hl : isLW (x.evN u)
  · rw [fst_of hl]; exact ⟨hu, hl, fst_of hl⟩
  · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hu hl
    rw [h.fst_lw hl hr ht hp]
    exact ⟨hr, lr_lw hlr, fst_of (lr_lw hlr)⟩

theorem Hyp.κ_fst (h : Hyp P init s x us) {u : Nat} (hu : u < x.n) :
    κ x (fstU x u) + bit x u = κ x u := by
  obtain ⟨-, h2, h3⟩ := h.fst_spec hu
  simp only [κ, h3, bit, h2]; simp

theorem Hyp.κ_even (h : Hyp P init s x us) {u : Nat} (hu : u < x.n) :
    κ x (fstU x u) % 2 = 0 := by
  obtain ⟨-, h2, h3⟩ := h.fst_spec hu
  simp only [κ, h3, bit, h2]; simp

theorem Hyp.κ_inj (h : Hyp P init s x us) {u v : Nat} (hu : u < x.n) (hv : v < x.n)
    (he : κ x u = κ x v) : u = v := by
  obtain ⟨fu, -, -⟩ := h.fst_spec hu
  obtain ⟨fv, -, -⟩ := h.fst_spec hv
  have hb : bit x u = bit x v := by
    have h1 : κ x u % 2 = bit x u := by simp only [κ, bit]; split <;> omega
    have h2 : κ x v % 2 = bit x v := by simp only [κ, bit]; split <;> omega
    rw [← h1, ← h2, he]
  have hm : gH x (fstU x u) * x.n + fstU x u = gH x (fstU x v) * x.n + fstU x v := by
    simp only [κ] at he; omega
  have hf : fstU x u = fstU x v := by
    have := congrArg (· % x.n) hm
    simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt fu, Nat.mod_eq_of_lt fv] at this
    exact this
  cases hlu : isLW (x.evN u)
  · have hlv : isLW (x.evN v) = false := by
      simp only [bit, hlu] at hb; split at hb <;> simp_all
    rwa [fst_of hlu, fst_of hlv] at hf
  · have hlv : isLW (x.evN v) = true := by
      simp only [bit, hlu] at hb; split at hb <;> simp_all
    obtain ⟨r, hr, ht, hp, -, -⟩ := h.partnerW hu hlu
    obtain ⟨r', hr', ht', hp', -, -⟩ := h.partnerW hv hlv
    rw [h.fst_lw hlu hr ht hp, h.fst_lw hlv hr' ht' hp'] at hf
    subst hf
    exact h.uniq hu hv (by rw [← ht, ← ht']) (by rw [hp, hp'])

/-- **The clock extends `ghb`.** -/
theorem Hyp.κ_ghb (h : Hyp P init s x us) {a b : Nat} (ha : a < x.n) (hb : b < x.n)
    (hg : x.ghb ⟨a, ha⟩ ⟨b, hb⟩ = true) : κ x a < κ x b := by
  obtain ⟨fa, -, -⟩ := h.fst_spec ha
  by_cases hfe : fstU x a = fstU x b
  · by_cases hab : a = b
    · subst hab; exact absurd hg (by intro hg; exact h.ghb1 hg)
    · cases hla : isLW (x.evN a)
      · rw [fst_of hla] at hfe
        cases hlb : isLW (x.evN b)
        · rw [fst_of hlb] at hfe; exact absurd hfe hab
        · have := h.κ_fst hb
          rw [← hfe] at this; simp only [bit, hlb, ↓reduceIte] at this; omega
      · exfalso
        obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW ha hla
        rw [h.fst_lw hla hr ht hp] at hfe
        cases hlb : isLW (x.evN b)
        · rw [fst_of hlb] at hfe
          subst hfe
          have hrR : (x.evN r).isR = true := by simp_all [isLR]
          have haM : (x.evN a).isM = true := by simp_all [isLW, Ev.isM]
          exact h.ghb2 hg (ghb_of_ppo (po_iff.mpr ⟨by simp only; exact ht, by simp only; omega⟩)
            (.inr ⟨hrR, haM⟩))
        · obtain ⟨r', hr', ht', hp', -, -⟩ := h.partnerW hb hlb
          rw [h.fst_lw hlb hr' ht' hp'] at hfe
          subst hfe
          exact hab (h.uniq ha hb (by rw [← ht, ← ht']) (by rw [hp, hp']))
  · -- a path from the last unit of `a`'s block to the last unit of `b`'s block
    have step1 : GN x (lstU x (fstU x a)) b := by
      cases hla : isLW (x.evN a)
      · cases hlr : isLR (x.evN a)
        · rw [fst_of hla, lst_of hlr]; exact ⟨ha, hb, hg⟩
        · obtain ⟨w, hw, ht, hp, hlw, had, hsz⟩ := h.partnerR ha hlr
          rw [fst_of hla, h.lst_lr hlr hw ht hp]
          refine ⟨hw, hb, h.lemA ha hw hb hlr ht hp hlw had hsz hg ?_⟩
          rintro rfl
          rw [fst_of hla, h.fst_lw hlw ha ht.symm hp] at hfe
          exact hfe rfl
      · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW ha hla
        rw [h.fst_lw hla hr ht hp, h.lst_lr hlr ha ht.symm hp]
        exact ⟨ha, hb, hg⟩
    have step2 : TransGen (GN x) (lstU x (fstU x a)) (lstU x (fstU x b)) := by
      cases hlb : isLW (x.evN b)
      · cases hlr : isLR (x.evN b)
        · rw [fst_of hlb, lst_of hlr]; exact .single step1
        · obtain ⟨w, hw, ht, hp, hlw, -, -⟩ := h.partnerR hb hlr
          rw [fst_of hlb, h.lst_lr hlr hw ht hp]
          have hbR : (x.evN b).isR = true := by simp_all [isLR]
          have hwM : (x.evN w).isM = true := by simp_all [isLW, Ev.isM]
          exact .tail (.single step1) ⟨hb, hw, ghb_of_ppo (po_iff.mpr ⟨ht.symm, by simp only; omega⟩)
            (.inr ⟨hbR, hwM⟩)⟩
      · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hb hlb
        rw [h.fst_lw hlb hr ht hp, h.lst_lr hlr hb ht.symm hp]
        exact .single step1
    have hlt := h.gH_lt fa step2
    have hm : (gH x (fstU x a) + 1) * x.n ≤ gH x (fstU x b) * x.n := Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at hm
    have hb1 : bit x a ≤ 1 := by simp only [bit]; split <;> omega
    simp only [κ]
    omega

end


/-! ## Machine-side lemmas -/

theorem readMem_of {m : Tso.Mem} : ∀ {n a : Nat} {bs : List Byte}, bs.length = n →
    (∀ j < n, m (a + j) = bs[j]?) → readMem m a n = some bs
  | 0, a, bs, hl, _ => by simp_all [readMem]
  | n + 1, a, bs, hl, hj => by
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have h0 := hj 0 (by omega)
      simp only [Nat.add_zero, List.getElem?_cons_zero] at h0
      have ih := readMem_of (m := m) (a := a + 1) hl fun j hj' => by
        have := hj (j + 1) (by omega)
        rw [show a + (j + 1) = a + 1 + j by omega] at this
        simpa using this
      simp [readMem, h0, ih]

theorem readBufByte_snoc (y : Nat) (e : Nat × List Byte) : ∀ (l : List (Nat × List Byte)),
    readBufByte y (l ++ [e]) = (entryByte e.1 e.2 y).or (readBufByte y l)
  | [] => by simp [readBufByte]
  | (a, bs) :: l => by
    simp only [List.cons_append, readBufByte, readBufByte_snoc y e l, Option.or_assoc]

/-- Store forwarding from a buffer given as `filterMap` over event indices: the newest entry
covering the byte wins. -/
theorem rbb_newest (y : Nat) (f : Nat → Option (Nat × List Byte)) {c : Nat} {e : Nat × List Byte}
    (hc : f c = some e) {b : Byte} (hb : entryByte e.1 e.2 y = some b) :
    ∀ k, c < k → (∀ c' e', c < c' → c' < k → f c' = some e' → entryByte e'.1 e'.2 y = none) →
      readBufByte y ((List.range k).filterMap f) = some b
  | 0, h, _ => by omega
  | k + 1, h, hlater => by
    rw [List.range_succ, List.filterMap_append]
    by_cases hk : c = k
    · subst hk; simp [hc, readBufByte_snoc, hb]
    · have ih := rbb_newest y f hc hb k (by omega) fun c' e' h1 h2 => hlater c' e' h1 (by omega)
      cases hf : f k with
      | none => simp only [List.filterMap_cons, hf, List.filterMap_nil, List.append_nil]; exact ih
      | some e' =>
        simp only [List.filterMap_cons, hf, List.filterMap_nil, readBufByte_snoc,
          hlater k e' (by omega) (by omega) hf, Option.none_or]
        exact ih

theorem rbb_none (y : Nat) (f : Nat → Option (Nat × List Byte)) :
    ∀ k, (∀ c < k, ∀ e, f c = some e → entryByte e.1 e.2 y = none) →
      readBufByte y ((List.range k).filterMap f) = none
  | 0, _ => by simp [readBufByte]
  | k + 1, h => by
    rw [List.range_succ, List.filterMap_append]
    have ih := rbb_none y f k fun c hc => h c (by omega)
    cases hf : f k with
    | none => simp only [List.filterMap_cons, hf, List.filterMap_nil, List.append_nil]; exact ih
    | some e' =>
      simp only [List.filterMap_cons, hf, List.filterMap_nil, readBufByte_snoc,
        h k (by omega) e' hf, Option.none_or]
      exact ih

/-- Splitting a buffer at its oldest entry. -/
theorem filterMap_split (f g : Nat → Option (Nat × List Byte)) {c0 : Nat} {e : Nat × List Byte}
    (hlt : ∀ c < c0, f c = none ∧ g c = none) (hf : f c0 = some e) (hg : g c0 = none)
    (hgt : ∀ c, c0 < c → f c = g c) :
    ∀ k, c0 < k → (List.range k).filterMap f = e :: (List.range k).filterMap g
  | 0, h => by omega
  | k + 1, h => by
    rw [List.range_succ, List.filterMap_append, List.filterMap_append]
    by_cases hk : c0 = k
    · subst hk
      have h1 : (List.range c0).filterMap f = [] := by
        rw [List.filterMap_eq_nil_iff]; intro c hc; exact (hlt c (List.mem_range.mp hc)).1
      have h2 : (List.range c0).filterMap g = [] := by
        rw [List.filterMap_eq_nil_iff]; intro c hc; exact (hlt c (List.mem_range.mp hc)).2
      simp [h1, h2, hf, hg]
    · rw [filterMap_split f g hlt hf hg hgt k (by omega)]
      simp only [List.filterMap_cons, List.filterMap_nil, hgt k (by omega), List.cons_append]

/-! ## The configurations of the run -/

/-- The memory at tick `t`: each byte holds the coherence-last write whose block started before
`t`, else its initial value. -/
noncomputable def memAt (x : Exec) (init : Tso.Mem) (t : Nat) : Tso.Mem := fun y =>
  match ((x.co y).filter fun w => decide (κ x (fstU x w) < t)).getLast? with
  | none => init y
  | some w => some ((x.evN w).byte y)

/-- The buffer entry of event `c` of thread `i` at tick `t`: a store whose clock is not before
`t`. -/
noncomputable def entAt (P : List (List (XEvent Nat))) (x : Exec) (t i c : Nat) :
    Option (Nat × List Byte) :=
  match E P i c with
  | some (.store _ a bs) => if t ≤ κ x (pidx x i (2 * c)) then some (a, bs) else none
  | _ => none

/-- Thread `i`'s buffer at tick `t`, when it has executed `cnt i` events: its executed stores
whose clock is not before `t`, oldest first. -/
noncomputable def bufAt (P : List (List (XEvent Nat))) (x : Exec) (t : Nat) (cnt : Nat → Nat)
    (i : Nat) : List (Nat × List Byte) :=
  (List.range (cnt i)).filterMap (entAt P x t i)

/-- The remaining events when thread `i` has executed `cnt i` events. -/
def restOf (P : List (List (XEvent Nat))) (cnt : Nat → Nat) : List (List (XEvent Nat)) :=
  P.mapIdx fun i es => es.drop (cnt i)

/-- The configuration at tick `t`. -/
noncomputable def cfg (P : List (List (XEvent Nat))) (x : Exec) (init : Tso.Mem) (t : Nat)
    (cnt : Nat → Nat) : ACfg :=
  ⟨restOf P cnt, ⟨memAt x init t, bufAt P x t cnt⟩⟩

theorem restOf_get (P : List (List (XEvent Nat))) (cnt : Nat → Nat) (i : Nat) :
    (restOf P cnt)[i]? = P[i]?.map (List.drop (cnt i)) := by
  simp [restOf, List.getElem?_mapIdx]

theorem E_lt {P : List (List (XEvent Nat))} {i c : Nat} {ev : XEvent Nat}
    (he : E P i c = some ev) : c < (P[i]?.getD []).length := by
  unfold E at he
  by_contra hn
  rw [List.getElem?_eq_none (by omega)] at he; cases he

theorem E_drop {P : List (List (XEvent Nat))} {i c : Nat} {ev : XEvent Nat}
    (he : E P i c = some ev) :
    (P[i]?.getD []).drop c = ev :: (P[i]?.getD []).drop (c + 1) := by
  have hl := E_lt he
  unfold E at he
  rw [List.drop_eq_getElem_cons hl, List.getElem?_eq_getElem hl] at *
  simp_all

theorem E_isSome {P : List (List (XEvent Nat))} {i c : Nat} {ev : XEvent Nat}
    (he : E P i c = some ev) : ∃ es, P[i]? = some es := by
  obtain ⟨es, h, -⟩ := E_mem he; exact ⟨es, h⟩

/-- One event of thread `i` as a machine step. -/
theorem astep_ev {P : List (List (XEvent Nat))} {cnt : Nat → Nat} {i : Nat} {ev : XEvent Nat}
    (he : E P i (cnt i) = some ev) {st st' : XState Nat} (hs : XStep st ev st') :
    AStep ⟨restOf P cnt, st⟩ ⟨restOf P (Function.update cnt i (cnt i + 1)), st'⟩ := by
  obtain ⟨es, hes⟩ := E_isSome he
  have hr : (restOf P cnt)[i]? = some (ev :: (P[i]?.getD []).drop (cnt i + 1)) := by
    have hd := E_drop he
    rw [hes] at hd; simp only [Option.getD_some] at hd
    rw [restOf_get, hes]; simp [hd]
  have := AStep.ev _ st st' i ev _ hr hs
  convert this using 2
  apply List.ext_getElem?
  intro j
  rw [restOf_get, List.getElem?_set]
  by_cases hj : i = j
  · subst hj
    simp only [Function.update_self, hes, Option.map_some, restOf, List.length_mapIdx,
      List.getElem?_mapIdx]
    have : i < P.length := by
      by_contra hn; rw [List.getElem?_eq_none (by omega)] at hes; cases hes
    simp [this]
  · simp [Function.update_of_ne (Ne.symm hj), restOf_get, hj]


theorem before_ne : ∀ {l : List Nat}, l.Nodup → ∀ {a b : Nat}, before l a b = true → a ≠ b
  | [], _, _, _, h => by simp [before] at h
  | c :: l, hn, a, b, h => by
    simp only [before] at h
    rw [List.nodup_cons] at hn
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc; subst hc
      rintro rfl; exact hn.1 (by simpa using h)
    · exact before_ne hn.2 h

/-! ### Buffers -/

theorem entAt_store {P : List (List (XEvent Nat))} {x : Exec} {t i c t' a : Nat}
    {bs : List Byte} (he : E P i c = some (.store t' a bs)) :
    entAt P x t i c = if t ≤ κ x (pidx x i (2 * c)) then some (a, bs) else none := by
  simp [entAt, he]

theorem entAt_nonstore {P : List (List (XEvent Nat))} {x : Exec} {t i c : Nat}
    (hn : ∀ t' a bs, E P i c ≠ some (.store t' a bs)) : entAt P x t i c = none := by
  unfold entAt
  split
  · rename_i t' a bs he; exact absurd he (hn t' a bs)
  · rfl

theorem bufAt_bump (P : List (List (XEvent Nat))) (x : Exec) (t : Nat) (cnt : Nat → Nat)
    (i j : Nat) : bufAt P x t (Function.update cnt i (cnt i + 1)) j =
      if j = i then bufAt P x t cnt i ++ (entAt P x t i (cnt i)).toList else bufAt P x t cnt j := by
  unfold bufAt
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self, List.range_succ, List.filterMap_append, ↓reduceIte]
    cases he : entAt P x t j (cnt j) <;> simp [he]
  · simp [hj]

theorem bufAt_same {P : List (List (XEvent Nat))} {x : Exec} {t : Nat} {cnt : Nat → Nat} {i : Nat}
    (hn : ∀ c t' a bs, E P i c = some (.store t' a bs) → κ x (pidx x i (2 * c)) ≠ t) :
    bufAt P x (t + 1) cnt i = bufAt P x t cnt i := by
  unfold bufAt
  congr 1
  funext c
  unfold entAt
  split
  · rename_i t' a bs he
    have := hn c t' a bs he
    by_cases h1 : t + 1 ≤ κ x (pidx x i (2 * c))
    · simp [h1, show t ≤ κ x (pidx x i (2 * c)) by omega]
    · simp [h1, show ¬ t ≤ κ x (pidx x i (2 * c)) by omega]
  · rfl

theorem bufAt_nil {P : List (List (XEvent Nat))} {x : Exec} {t : Nat} {cnt : Nat → Nat} {i : Nat}
    (hn : ∀ c < cnt i, ∀ t' a bs, E P i c = some (.store t' a bs) → κ x (pidx x i (2 * c)) < t) :
    bufAt P x t cnt i = [] := by
  unfold bufAt
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  unfold entAt
  split
  · rename_i t' a bs he
    have := hn c (List.mem_range.mp hc) t' a bs he
    simp [show ¬ t ≤ κ x (pidx x i (2 * c)) by omega]
  · rfl

theorem bufAt_flush {P : List (List (XEvent Nat))} {x : Exec} {t : Nat} {cnt : Nat → Nat}
    {i c0 t0 a : Nat} {bs : List Byte} (he : E P i c0 = some (.store t0 a bs))
    (hκ : κ x (pidx x i (2 * c0)) = t) (hc : c0 < cnt i)
    (hlt : ∀ c < c0, ∀ t' a bs, E P i c = some (.store t' a bs) → κ x (pidx x i (2 * c)) < t)
    (hgt : ∀ c, c0 < c → ∀ t' a bs, E P i c = some (.store t' a bs) →
      κ x (pidx x i (2 * c)) ≠ t) :
    bufAt P x t cnt i = (a, bs) :: bufAt P x (t + 1) cnt i := by
  unfold bufAt
  refine filterMap_split _ _ (fun c hc => ?_) ?_ ?_ (fun c hc => ?_) _ hc
  · unfold entAt
    split
    · rename_i t' a' bs' he'
      have := hlt c hc t' a' bs' he'
      simp [show ¬ t ≤ κ x (pidx x i (2 * c)) by omega,
        show ¬ t + 1 ≤ κ x (pidx x i (2 * c)) by omega]
    · simp
  · simp [entAt, he, hκ]
  · simp [entAt, he, hκ]
  · unfold entAt
    split
    · rename_i t' a' bs' he'
      have := hgt c hc t' a' bs' he'
      by_cases h1 : t + 1 ≤ κ x (pidx x i (2 * c))
      · simp [h1, show t ≤ κ x (pidx x i (2 * c)) by omega]
      · simp [h1, show ¬ t ≤ κ x (pidx x i (2 * c)) by omega]
    · rfl

section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

/-- The unit of an event, by its position. -/
theorem Hyp.evIdx (h : Hyp P init s x us) {i c : Nat} {ev : XEvent Nat} (he : E P i c = some ev)
    {p : Ev × List Byte} (hp : p ∈ evUnits i c ev) :
    pidx x i p.1.pos < x.n ∧ x.evN (pidx x i p.1.pos) = p.1 ∧
      (us.getD (pidx x i p.1.pos) (dflt, [])).2 = p.2 := by
  obtain ⟨u, hu, he1, he2⟩ := h.ofEvent he hp
  have ht : (x.evN u).tid = i := by rw [he1]; exact evUnits_tid hp
  have := h.pidx_eq hu
  rw [ht, he1] at this
  rw [this]
  exact ⟨hu, he1, he2⟩

theorem Hyp.storeIdx (h : Hyp P init s x us) {i c t0 a : Nat} {bs : List Byte}
    (he : E P i c = some (.store t0 a bs)) :
    pidx x i (2 * c) < x.n ∧ x.evN (pidx x i (2 * c)) = storeU i c a bs := by
  have := h.evIdx he (p := (storeU i c a bs, [])) (by simp [evUnits, storeU])
  exact ⟨this.1, this.2.1⟩

theorem Hyp.dataLen (h : Hyp P init s x us) {w : Nat} (hw : w < x.n)
    (hW : (x.evN w).isW = true) : (x.evN w).data.length = (x.evN w).size := by
  rcases h.kind hw with ⟨c, a, bs, he, hev, -⟩ | ⟨c, a, bs, he, hev⟩ |
      ⟨c, a, old, new, he, hlen, ⟨hev, -⟩ | hev⟩ | ⟨c, he, hev⟩ <;>
    rw [hev] at hW ⊢ <;> simp [loadU, storeU, rmwRU, rmwWU, fenceU, Ev.isW] at hW ⊢

theorem Hyp.fst_inj (h : Hyp P init s x us) {u w : Nat} (hu : u < x.n) (hw : w < x.n)
    (huW : (x.evN u).isW = true) (hwW : (x.evN w).isW = true) (he : fstU x u = fstU x w) :
    u = w := by
  cases hlu : isLW (x.evN u) <;> cases hlw : isLW (x.evN w)
  · rwa [fst_of hlu, fst_of hlw] at he
  · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hw hlw
    rw [fst_of hlu, h.fst_lw hlw hr ht hp] at he
    subst he
    simp only [isLR, Ev.isR, Bool.and_eq_true, beq_iff_eq] at hlr
    simp [Ev.isW, hlr.1] at huW
  · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hu hlu
    rw [fst_of hlw, h.fst_lw hlu hr ht hp] at he
    subst he
    simp only [isLR, Ev.isR, Bool.and_eq_true, beq_iff_eq] at hlr
    simp [Ev.isW, hlr.1] at hwW
  · obtain ⟨r, hr, ht, hp, -, -⟩ := h.partnerW hu hlu
    obtain ⟨r', hr', ht', hp', -, -⟩ := h.partnerW hw hlw
    rw [h.fst_lw hlu hr ht hp, h.fst_lw hlw hr' ht' hp'] at he
    subst he
    exact h.uniq hu hw (by rw [← ht, ← ht']) (by rw [hp, hp'])

theorem bit_le (x : Exec) (u : Nat) : bit x u ≤ 1 := by simp only [bit]; split <;> omega

/-- A write coherence-after `u` (with `u`'s block at tick `t`) starts its block after `t`. -/
theorem Hyp.co_after (h : Hyp P init s x us) {u w y : Nat} (hu : u < x.n)
    (huW : (x.evN u).isW = true) (hcu : (x.evN u).covers y = true) (hw : w ∈ x.co y)
    (hb : before (x.co y) u w = true) : κ x (fstU x u) < κ x (fstU x w) := by
  obtain ⟨hw, hwW, hcw⟩ := (h.coM y w).mp hw
  have hg := h.κ_ghb hu hw (ghb_of_coR (coR_mk (a := ⟨u, hu⟩) (b := ⟨w, hw⟩) huW hwW hcu hcw hb))
  have h1 := h.κ_fst hu
  have h2 := h.κ_fst hw
  have h3 := bit_le x u
  have h4 := bit_le x w
  have hne : κ x (fstU x w) ≠ κ x (fstU x u) := by
    intro he
    have := h.fst_inj hw hu hwW huW
      (h.κ_inj (h.fst_spec hw).1 (h.fst_spec hu).1 he)
    exact before_ne (h.coN y) hb this.symm
  omega

/-! ### Memory -/

theorem Hyp.memAt_write (h : Hyp P init s x us) {u t : Nat} (hu : u < x.n)
    (huW : (x.evN u).isW = true) (hκ : κ x (fstU x u) = t) :
    memAt x init (t + 1) = writeMem (memAt x init t) (x.evN u).addr (x.evN u).data := by
  funext y
  rw [writeMem_eq (h.dataLen hu huW)]
  by_cases hc : (x.evN u).covers y = true
  · simp only [hc, ↓reduceIte, memAt]
    rw [last_filter (s := u) ((h.coM y u).mpr ⟨hu, huW, hc⟩) (by simp [hκ])]
    intro w hw hb
    have := h.co_after hu huW hc hw hb
    simp; omega
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, memAt]
    have : ((x.co y).filter fun w => decide (κ x (fstU x w) < t + 1)) =
        ((x.co y).filter fun w => decide (κ x (fstU x w) < t)) := by
      apply List.filter_congr
      intro w hw
      obtain ⟨hw', hwW, hcw⟩ := (h.coM y w).mp hw
      have hne : κ x (fstU x w) ≠ t := by
        intro he
        rw [← hκ] at he
        have := h.fst_inj hw' hu hwW huW (h.κ_inj (h.fst_spec hw').1 (h.fst_spec hu).1 he)
        subst this; exact hc hcw
      simp only [decide_eq_decide]; omega
    rw [this]

theorem Hyp.memAt_same (h : Hyp P init s x us) {t : Nat}
    (hn : ∀ w < x.n, (x.evN w).isW = true → κ x (fstU x w) ≠ t) :
    memAt x init (t + 1) = memAt x init t := by
  funext y
  simp only [memAt]
  have : ((x.co y).filter fun w => decide (κ x (fstU x w) < t + 1)) =
      ((x.co y).filter fun w => decide (κ x (fstU x w) < t)) := by
    apply List.filter_congr
    intro w hw
    obtain ⟨hw', hwW, -⟩ := (h.coM y w).mp hw
    have := hn w hw' hwW
    simp only [decide_eq_decide]; omega
  rw [this]

theorem memAt_read {x : Exec} {init : Tso.Mem} {t y w : Nat} (hs : w ∈ x.co y)
    (h1 : κ x (fstU x w) < t) (h2 : ∀ v ∈ x.co y, before (x.co y) w v = true → t ≤ κ x (fstU x v)) :
    memAt x init t y = some ((x.evN w).byte y) := by
  simp only [memAt]
  rw [last_filter hs (by simp [h1])]
  intro v hv hb
  have := h2 v hv hb
  simp; omega

theorem memAt_init {x : Exec} {init : Tso.Mem} {t y : Nat}
    (h2 : ∀ v ∈ x.co y, t ≤ κ x (fstU x v)) : memAt x init t y = init y := by
  simp only [memAt]
  rw [last_filter_none]
  intro v hv
  have := h2 v hv
  simp; omega

end


/-! ### Reads -/

section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

theorem ent_info {t i c : Nat} {e : Nat × List Byte} (he : entAt P x t i c = some e) :
    ∃ t0 a bs, E P i c = some (.store t0 a bs) ∧ e = (a, bs) ∧ t ≤ κ x (pidx x i (2 * c)) := by
  unfold entAt at he
  split at he
  · rename_i t0 a bs hE
    split at he
    · rename_i hle
      simp only [Option.some.injEq] at he
      exact ⟨t0, a, bs, hE, he.symm, hle⟩
    · cases he
  · cases he

theorem entryByte_store (i c a : Nat) (bs : List Byte) (y : Nat) :
    entryByte a bs y = if (storeU i c a bs).covers y then some ((storeU i c a bs).byte y)
      else none :=
  entryByte_eq (e := storeU i c a bs) (by simp [storeU]) y

theorem Hyp.initSome (h : Hyp P init s x us) {u y : Nat} (hu : u < x.n)
    (hM : (x.evN u).isM = true) (hc : (x.evN u).covers y = true) : (init y).isSome = true := by
  obtain ⟨c, ev, he, hp⟩ := h.unit hu
  obtain ⟨es, hes, hev⟩ := E_mem he
  have hf := Proofs.evUnits_foot hp hM
  rw [covers_iff] at hc
  exact h.hI _ es hes ev hev _ hf y hc.1 hc.2

theorem isR_isW {e : Ev} (h1 : e.isR = true) (h2 : e.isW = true) : False := by
  simp only [Ev.isR, Ev.isW, beq_iff_eq] at h1 h2; rw [h1] at h2; cases h2

/-- **The value a read sees.** At its tick, with its thread's earlier events executed, the
thread's view of byte `y` is the byte the candidate's `rf` gives. -/
theorem Hyp.readOK (h : Hyp P init s x us) {u t : Nat} {cnt : Nat → Nat} (hu : u < x.n)
    (hR : (x.evN u).isR = true) (hκ : κ x u = t) (hc : 2 * cnt (x.evN u).tid = (x.evN u).pos)
    {y : Nat} (hcy : (x.evN u).covers y = true) :
    viewMem ⟨memAt x init t, bufAt P x t cnt⟩ (x.evN u).tid y =
      some (x.readByte (fun y => (init y).getD 0) u y) := by
  have huM : (x.evN u).isM = true := by simp [Ev.isM, hR]
  -- facts about a buffered store
  have bufd : ∀ c < cnt (x.evN u).tid, ∀ e, entAt P x t (x.evN u).tid c = some e →
      ∃ w < x.n, (x.evN w).isW = true ∧ (x.evN w).tid = (x.evN u).tid ∧
        (x.evN w).pos < (x.evN u).pos ∧ (x.evN w).pos = 2 * c ∧ t ≤ κ x w ∧
        entryByte e.1 e.2 y = if (x.evN w).covers y then some ((x.evN w).byte y) else none := by
    intro c hcl e he
    obtain ⟨t0, a, bs, hE, rfl, hle⟩ := ent_info he
    obtain ⟨hw, hev⟩ := h.storeIdx hE
    refine ⟨_, hw, by rw [hev]; rfl, by rw [hev]; rfl, by rw [hev]; simp [storeU]; omega,
      by rw [hev]; rfl, hle, ?_⟩
    rw [hev]; exact entryByte_store _ _ _ _ y
  have poLocU : ∀ w (hw : w < x.n), (x.evN w).isW = true → (x.evN w).tid = (x.evN u).tid →
      (x.evN w).pos < (x.evN u).pos → (x.evN w).covers y = true →
      x.uniproc ⟨w, hw⟩ ⟨u, hu⟩ = true := by
    intro w hw hwW ht hp hcw
    exact uniproc_of_poLoc (po_iff.mpr ⟨ht, hp⟩) (by simp [Ev.isM, hwW]) huM hcw hcy
  simp only [viewMem, Exec.readByte]
  cases hrf : x.rf u y with
  | none =>
    have hb : readBufByte y (bufAt P x t cnt (x.evN u).tid) = none := by
      apply rbb_none
      intro c hcl e he
      obtain ⟨w, hw, hwW, ht, hp, -, -, hent⟩ := bufd c hcl e he
      rw [hent]
      split
      · rename_i hcw
        exfalso
        exact h.unip2 (poLocU w hw hwW ht hp hcw) (uniproc_of_com (com_of_frR
          (frR_mk (r := ⟨u, hu⟩) (w := ⟨w, hw⟩) hR hwW hcy hcw (by simp [hrf]))))
      · rfl
    have hm : memAt x init t y = init y := by
      apply memAt_init
      intro v hv
      obtain ⟨hv', hvW, hcv⟩ := (h.coM y v).mp hv
      have := h.κ_ghb hu hv' (ghb_of_frR (frR_mk (r := ⟨u, hu⟩) (w := ⟨v, hv'⟩) hR hvW hcy hcv
        (by simp [hrf])))
      have := h.κ_fst hv'
      have := bit_le x v
      omega
    simp only [hb, hm, Option.none_or]
    have := h.initSome hu huM hcy
    cases hi : init y with
    | none => rw [hi] at this; cases this
    | some b => rfl
  | some w0 =>
    obtain ⟨hw0, hw0W, hcw0⟩ := h.rfW u y w0 hrf
    have hrfR : x.rfR ⟨w0, hw0⟩ ⟨u, hu⟩ = true := rfR_mk hw0W hR hcy hcw0 hrf
    have hco0 : w0 ∈ x.co y := (h.coM y w0).mpr ⟨hw0, hw0W, hcw0⟩
    -- a later write in coherence is `fr`-after `u`
    have frAfter : ∀ v ∈ x.co y, before (x.co y) w0 v = true →
        ∃ hv : v < x.n, x.frR ⟨u, hu⟩ ⟨v, hv⟩ = true := by
      intro v hv hb
      obtain ⟨hv', hvW, hcv⟩ := (h.coM y v).mp hv
      exact ⟨hv', frR_mk hR hvW hcy hcv (by simp [hrf, hb])⟩
    by_cases hlt : κ x w0 < t
    · have hb : readBufByte y (bufAt P x t cnt (x.evN u).tid) = none := by
        apply rbb_none
        intro c hcl e he
        obtain ⟨w, hw, hwW, ht, hp, -, hle, hent⟩ := bufd c hcl e he
        rw [hent]
        split
        · rename_i hcw
          exfalso
          have hne : w0 ≠ w := by rintro rfl; omega
          rcases before_total hco0 ((h.coM y w).mpr ⟨hw, hwW, hcw⟩) hne with hb | hb
          · obtain ⟨_, hfr⟩ := frAfter w ((h.coM y w).mpr ⟨hw, hwW, hcw⟩) hb
            exact h.unip2 (poLocU w hw hwW ht hp hcw) (uniproc_of_com (com_of_frR hfr))
          · have := h.κ_ghb hw hw0 (ghb_of_coR (coR_mk (a := ⟨w, hw⟩) (b := ⟨w0, hw0⟩)
              hwW hw0W hcw hcw0 hb))
            omega
        · rfl
      have hm : memAt x init t y = some ((x.evN w0).byte y) := by
        apply memAt_read hco0
        · have := h.κ_fst hw0; omega
        · intro v hv hb
          obtain ⟨hv', hfr⟩ := frAfter v hv hb
          have := h.κ_ghb hu hv' (ghb_of_frR hfr)
          have := h.κ_fst hv'
          have := bit_le x v
          omega
      simp [hb, hm]
    · have hne : κ x w0 ≠ t := by
        intro he
        rw [← hκ] at he
        have := h.κ_inj hw0 hu he
        subst this; exact isR_isW hR hw0W
      have ht : (x.evN w0).tid = (x.evN u).tid := by
        by_contra hn
        have := h.κ_ghb hw0 hu (ghb_of_rfe hrfR hn)
        omega
      have hp : (x.evN w0).pos < (x.evN u).pos := by
        rcases Nat.lt_trichotomy (x.evN w0).pos (x.evN u).pos with h1 | h1 | h1
        · exact h1
        · have := h.uniq hw0 hu ht h1
          subst this; exact absurd hw0W (fun h' => isR_isW hR h')
        · exfalso
          exact h.unip2 (uniproc_of_poLoc (a := ⟨u, hu⟩) (b := ⟨w0, hw0⟩)
            (po_iff.mpr ⟨ht.symm, h1⟩) huM (by simp [Ev.isM, hw0W]) hcy hcw0)
            (uniproc_of_com (com_of_rfR hrfR))
      have hnl : isLW (x.evN w0) = false := by
        cases hl : isLW (x.evN w0)
        · rfl
        · exfalso
          obtain ⟨r, hr, htr, hpr, hlr, -⟩ := h.partnerW hw0 hl
          have hrR : (x.evN r).isR = true := by simp_all [isLR]
          have := h.κ_ghb hr hu (ghb_of_ppo (po_iff.mpr ⟨by simp only; rw [htr, ht], by
            simp only; omega⟩) (.inr ⟨hrR, huM⟩))
          have h2 := h.κ_fst hw0
          rw [h.fst_lw hl hr htr hpr] at h2
          simp only [bit, hl, ↓reduceIte] at h2
          omega
      -- so `w0` is a store of `u`'s thread, still buffered
      obtain ⟨c, a, bs, hE, hev⟩ : ∃ c a bs, E P (x.evN u).tid c =
          some (.store (x.evN u).tid a bs) ∧ x.evN w0 = storeU (x.evN u).tid c a bs := by
        rcases h.kind hw0 with ⟨c, a, bs, he, hev, -⟩ | ⟨c, a, bs, he, hev⟩ |
            ⟨c, a, old, new, he, hlen, ⟨hev, -⟩ | hev⟩ | ⟨c, he, hev⟩
        · rw [hev] at hw0W; simp [loadU, Ev.isW] at hw0W
        · rw [ht] at he hev; exact ⟨c, a, bs, he, hev⟩
        · rw [hev] at hw0W; simp [rmwRU, Ev.isW] at hw0W
        · rw [hev] at hnl; simp [rmwWU, isLW, Ev.isW] at hnl
        · rw [hev] at hw0W; simp [fenceU, Ev.isW] at hw0W
      have hpw : (x.evN w0).pos = 2 * c := by rw [hev]; rfl
      have hidx : pidx x (x.evN u).tid (2 * c) = w0 := by
        rw [← ht, ← hpw]; exact h.pidx_eq hw0
      have hb : readBufByte y (bufAt P x t cnt (x.evN u).tid) = some ((x.evN w0).byte y) := by
        refine rbb_newest y _ (c := c) (e := (a, bs)) ?_ ?_ _ (by omega) ?_
        · rw [entAt_store hE, hidx]; simp; omega
        · simp only
          rw [entryByte_store (x.evN u).tid c a bs y, ← hev]
          simp [hcw0]
        · intro c' e' hcc hcl he'
          · obtain ⟨w, hw, hwW, ht', hp', hpw', -, hent⟩ := bufd c' hcl e' he'
            rw [hent]
            split
            · rename_i hcw
              exfalso
              have hne : w0 ≠ w := by rintro rfl; omega
              rcases before_total hco0 ((h.coM y w).mpr ⟨hw, hwW, hcw⟩) hne with hb | hb
              · obtain ⟨_, hfr⟩ := frAfter w ((h.coM y w).mpr ⟨hw, hwW, hcw⟩) hb
                exact h.unip2 (poLocU w hw hwW ht' hp' hcw) (uniproc_of_com (com_of_frR hfr))
              · exact h.unip2 (uniproc_of_poLoc (a := ⟨w0, hw0⟩) (b := ⟨w, hw⟩)
                  (po_iff.mpr ⟨by simp only; rw [ht, ht'], by simp only; omega⟩)
                  (by simp [Ev.isM, hw0W]) (by simp [Ev.isM, hwW]) hcw0 hcw)
                  (uniproc_of_com (com_of_coR (coR_mk hwW hw0W hcw hcw0 hb)))
            · rfl
      simp [hb]

end


/-! ## The run, tick by tick -/

/-- The invariant at tick `t` with event counts `cnt`: the counts are in range, every memory unit
with an earlier clock has been executed, and every executed read has an earlier clock. -/
structure Inv (P : List (List (XEvent Nat))) (x : Exec) (t : Nat) (cnt : Nat → Nat) : Prop where
  le : ∀ i, cnt i ≤ (P[i]?.getD []).length
  done : ∀ v < x.n, (x.evN v).isM = true → κ x v < t → (x.evN v).pos / 2 < cnt (x.evN v).tid
  rd : ∀ v < x.n, (x.evN v).isR = true → (x.evN v).pos / 2 < cnt (x.evN v).tid → κ x v < t

section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

/-- Execute thread `i`'s pending stores and fences, as long as each fence finds the buffer
empty. -/
theorem Hyp.catchup (h : Hyp P init s x us) {t i : Nat} : ∀ (d : Nat) (cnt : Nat → Nat),
    (∀ c, cnt i ≤ c → c < cnt i + d →
      (∃ a bs, E P i c = some (.store i a bs) ∧ t ≤ κ x (pidx x i (2 * c))) ∨
      (E P i c = some (.fence i) ∧
        ∀ c' < c, ∀ t' a bs, E P i c' = some (.store t' a bs) → κ x (pidx x i (2 * c')) < t)) →
    ReflTransGen AStep (cfg P x init t cnt) (cfg P x init t (Function.update cnt i (cnt i + d)))
  | 0, cnt, _ => by simp only [Nat.add_zero, Function.update_eq_self]; exact .refl
  | d + 1, cnt, hev => by
    have hstep : ReflTransGen AStep (cfg P x init t cnt)
        (cfg P x init t (Function.update cnt i (cnt i + 1))) := by
      rcases hev (cnt i) (le_refl _) (by omega) with ⟨a, bs, he, hle⟩ | ⟨he, hemp⟩
      · refine .single ?_
        have := astep_ev he (XStep.store ⟨memAt x init t, bufAt P x t cnt⟩ i a bs)
        have heq : enqueue ⟨memAt x init t, bufAt P x t cnt⟩ i a bs =
            ⟨memAt x init t, bufAt P x t (Function.update cnt i (cnt i + 1))⟩ := by
          simp only [enqueue, XState.mk.injEq, true_and]
          funext j
          rw [bufAt_bump]
          by_cases hj : j = i
          · subst hj; simp [entAt_store he, hle]
          · simp [hj]
        rw [heq] at this
        exact this
      · refine .single ?_
        have := astep_ev he (XStep.fence ⟨memAt x init t, bufAt P x t cnt⟩ i (bufAt_nil hemp))
        have heq : (⟨memAt x init t, bufAt P x t cnt⟩ : XState Nat) =
            ⟨memAt x init t, bufAt P x t (Function.update cnt i (cnt i + 1))⟩ := by
          simp only [XState.mk.injEq, true_and]
          funext j
          rw [bufAt_bump]
          split
          · subst_vars
            rw [entAt_nonstore (by intro t' a bs; rw [he]; simp)]; simp
          · rfl
        nth_rewrite 2 [heq] at this
        exact this
    have ih := h.catchup d (Function.update cnt i (cnt i + 1)) (by
      intro c h1 h2
      rw [Function.update_self] at h1 h2
      exact hev c (by omega) (by omega))
    rw [Function.update_self, Function.update_idem] at ih
    rw [show cnt i + (d + 1) = cnt i + 1 + d by omega]
    exact hstep.trans ih

theorem Hyp.R_even (h : Hyp P init s x us) {v : Nat} (hv : v < x.n) (hR : (x.evN v).isR = true) :
    (x.evN v).pos % 2 = 0 := by
  rcases h.kind hv with ⟨c, a, bs, he, hev, -⟩ | ⟨c, a, bs, he, hev⟩ |
      ⟨c, a, old, new, he, hlen, ⟨hev, -⟩ | hev⟩ | ⟨c, he, hev⟩ <;>
    rw [hev] at hR ⊢ <;> simp [loadU, storeU, rmwRU, rmwWU, fenceU, Ev.isR] at hR ⊢

/-- The pending events before a memory unit's event are stores not yet flushed and fences
whose thread has flushed every earlier store. -/
theorem Hyp.pending (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat} (hI : Inv P x t cnt)
    {u k c : Nat} (hu : u < x.n) (hκ : κ x u = t) (huM : (x.evN u).isM = true)
    (hpos : (x.evN u).pos = 2 * k) (hkl : k < (P[(x.evN u).tid]?.getD []).length)
    (hc : cnt (x.evN u).tid ≤ c) (hck : c < k) :
    (∃ a bs, E P (x.evN u).tid c = some (.store (x.evN u).tid a bs) ∧
      t ≤ κ x (pidx x (x.evN u).tid (2 * c))) ∨
    (E P (x.evN u).tid c = some (.fence (x.evN u).tid) ∧
      ∀ c' < c, ∀ t' a bs, E P (x.evN u).tid c' = some (.store t' a bs) →
        κ x (pidx x (x.evN u).tid (2 * c')) < t) := by
  set i := (x.evN u).tid with hi
  have hE : E P i c = some ((P[i]?.getD [])[c]'(by omega)) := by
    simp [E, List.getElem?_eq_getElem (show c < (P[i]?.getD []).length by omega)]
  -- a read at event `c` would precede `u`
  have noRead : ∀ v < x.n, (x.evN v).tid = i → (x.evN v).pos = 2 * c →
      (x.evN v).isR = true → False := by
    intro v hv ht hp hR
    have := h.κ_ghb hv hu (ghb_of_ppo (po_iff.mpr ⟨ht, by simp only; omega⟩) (.inr ⟨hR, huM⟩))
    have := hI.done v hv (by simp [Ev.isM, hR]) (by omega)
    rw [ht, hp] at this; omega
  generalize hev : (P[i]?.getD [])[c]'(by omega) = ev at hE
  have hth := h.thread hE
  cases ev with
  | load t' a bs =>
    simp only [XEvent.thread] at hth; subst hth
    have := h.evIdx hE (p := (loadU i c a bs.length, bs)) (by simp [evUnits, loadU])
    exact absurd (noRead _ this.1 (by rw [this.2.1]; rfl) (by rw [this.2.1]; rfl)
      (by rw [this.2.1]; rfl)) id
  | rmw t' a old new =>
    simp only [XEvent.thread] at hth; subst hth
    have := h.evIdx hE (p := (rmwRU i c a old.length, old)) (by simp [evUnits, rmwRU])
    exact absurd (noRead _ this.1 (by rw [this.2.1]; rfl) (by rw [this.2.1]; rfl)
      (by rw [this.2.1]; rfl)) id
  | store t' a bs =>
    simp only [XEvent.thread] at hth; subst hth
    refine .inl ⟨a, bs, hE, ?_⟩
    obtain ⟨hv, hev⟩ := h.storeIdx hE
    by_contra hlt
    have := hI.done _ hv (by rw [hev]; rfl) (by omega)
    rw [hev] at this; simp [storeU] at this; omega
  | fence t' =>
    simp only [XEvent.thread] at hth; subst hth
    refine .inr ⟨hE, fun c' hc' t'' a bs he' => ?_⟩
    obtain ⟨hw, hev⟩ := h.storeIdx he'
    have hf := h.evIdx hE (p := (fenceU i c, [])) (by simp [evUnits, fenceU])
    simp only [fenceU] at hf
    refine h.κ_ghb hw hu (ghb_of_mfence (f := ⟨_, hf.1⟩) ?_ ?_ ?_) |>.trans_eq hκ
    · simp only; rw [hf.2.1]; rfl
    · rw [po_iff]; simp only; rw [hev, hf.2.1]; simp [storeU]; omega
    · rw [po_iff]; simp only; rw [hf.2.1]; simp; omega

/-- The invariant after the tick of a memory unit `u` at event `k`, with its thread's count
raised to cover `k`. -/
theorem Hyp.inv_tick (h : Hyp P init s x us) {t : Nat} {cnt cnt' : Nat → Nat} (hI : Inv P x t cnt)
    {u k : Nat} (hu : u < x.n) (hκ : κ x u = t) (hpos : (x.evN u).pos / 2 = k)
    (hother : ∀ j, j ≠ (x.evN u).tid → cnt' j = cnt j)
    (hi : cnt' (x.evN u).tid = max (cnt (x.evN u).tid) (k + 1))
    (hle : cnt' (x.evN u).tid ≤ (P[(x.evN u).tid]?.getD []).length)
    (huM : (x.evN u).isM = true) (hpu : (x.evN u).pos % 2 = 0) : Inv P x (t + 1) cnt' := by
  have hge : ∀ j, cnt j ≤ cnt' j := by
    intro j; by_cases hj : j = (x.evN u).tid
    · subst hj; omega
    · rw [hother j hj]
  refine ⟨fun j => ?_, fun v hv hM hlt => ?_, fun v hv hR hp => ?_⟩
  · by_cases hj : j = (x.evN u).tid
    · subst hj; exact hle
    · rw [hother j hj]; exact hI.le j
  · rcases Nat.lt_or_ge (κ x v) t with h1 | h1
    · exact Nat.lt_of_lt_of_le (hI.done v hv hM h1) (hge _)
    · have := h.κ_inj hv hu (by omega)
      subst this; omega
  · by_cases hj : (x.evN v).tid = (x.evN u).tid
    · rw [hj, hi] at hp
      rcases Nat.lt_or_ge ((x.evN v).pos / 2) (cnt (x.evN u).tid) with h1 | h1
      · have := hI.rd v hv hR (by rw [hj]; exact h1); omega
      · have hve := h.R_even hv hR
        rcases Nat.lt_or_ge (x.evN v).pos (x.evN u).pos with h2 | h2
        · have := h.κ_ghb hv hu (ghb_of_ppo (po_iff.mpr ⟨hj, h2⟩) (.inr ⟨hR, huM⟩))
          omega
        · have := h.uniq hv hu hj (by omega)
          subst this; omega
    · rw [hother _ hj] at hp
      have := hI.rd v hv hR hp; omega

end


section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

/-- A read sees the bytes it must return. -/
theorem Hyp.readAll (h : Hyp P init s x us) {u t : Nat} {cnt : Nat → Nat} (hu : u < x.n)
    (hR : (x.evN u).isR = true) (hκ : κ x u = t) (hc : 2 * cnt (x.evN u).tid = (x.evN u).pos) :
    readMem (viewMem ⟨memAt x init t, bufAt P x t cnt⟩ (x.evN u).tid) (x.evN u).addr
      (x.evN u).size = some (us.getD u (dflt, [])).2 := by
  rw [← h.reads u hu hR]
  apply readMem_of
  · simp [Exec.readBytes, Ev.bytes]
  · intro j hj
    rw [h.readOK hu hR hκ hc (by rw [covers_iff]; omega)]
    simp [Exec.readBytes, Ev.bytes, hj]

/-- The first unit of a write's block is a write that is not locked, or a locked read. -/
theorem Hyp.fst_w (h : Hyp P init s x us) {w : Nat} (hw : w < x.n) (hW : (x.evN w).isW = true) :
    ((x.evN (fstU x w)).isW = true ∧ isLW (x.evN (fstU x w)) = false) ∨
      isLR (x.evN (fstU x w)) = true := by
  cases hl : isLW (x.evN w)
  · rw [fst_of hl]; exact .inl ⟨hW, hl⟩
  · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hw hl
    rw [h.fst_lw hl hr ht hp]; exact .inr hlr

theorem Hyp.bufAt_succ (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat} {i : Nat}
    (hs : ∀ v < x.n, (x.evN v).isW = true → isLW (x.evN v) = false → (x.evN v).tid = i →
      κ x v ≠ t) : bufAt P x (t + 1) cnt i = bufAt P x t cnt i := by
  apply bufAt_same
  intro c t' a bs he
  obtain ⟨hv, hev⟩ := h.storeIdx he
  exact hs _ hv (by rw [hev]; rfl) (by rw [hev]; rfl) (by rw [hev]; rfl)

theorem Hyp.cfg_succ (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat}
    (hw : ∀ w < x.n, (x.evN w).isW = true → κ x (fstU x w) ≠ t) :
    cfg P x init t cnt = cfg P x init (t + 1) cnt := by
  simp only [cfg, ACfg.mk.injEq, XState.mk.injEq, true_and]
  refine ⟨(h.memAt_same hw).symm, ?_⟩
  funext i
  refine (h.bufAt_succ fun v hv hW hl _ => ?_).symm
  have := hw v hv hW
  rwa [fst_of hl] at this

theorem Inv.same {P : List (List (XEvent Nat))} {x : Exec} {t : Nat} {cnt : Nat → Nat}
    (hI : Inv P x t cnt)
    (hd : ∀ v < x.n, (x.evN v).isM = true → κ x v = t → (x.evN v).pos / 2 < cnt (x.evN v).tid) :
    Inv P x (t + 1) cnt := by
  refine ⟨hI.le, fun v hv hM hlt => ?_, fun v hv hR hp => ?_⟩
  · rcases Nat.lt_or_ge (κ x v) t with h1 | h1
    · exact hI.done v hv hM h1
    · exact hd v hv hM (by omega)
  · have := hI.rd v hv hR hp; omega

/-- Catch thread `i` up to the event of a memory unit `u` with clock `t`. -/
theorem Hyp.catchupTo (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat} (hI : Inv P x t cnt)
    {u k : Nat} (hu : u < x.n) (hκ : κ x u = t) (huM : (x.evN u).isM = true)
    (hpos : (x.evN u).pos = 2 * k) (hkl : k < (P[(x.evN u).tid]?.getD []).length)
    (hk : cnt (x.evN u).tid ≤ k) :
    ReflTransGen AStep (cfg P x init t cnt)
      (cfg P x init t (Function.update cnt (x.evN u).tid k)) := by
  have := h.catchup (t := t) (i := (x.evN u).tid) (k - cnt (x.evN u).tid) cnt
    (fun c h1 h2 => h.pending hI hu hκ huM hpos hkl h1 (by omega))
  rwa [show cnt (x.evN u).tid + (k - cnt (x.evN u).tid) = k by omega] at this

theorem upd_upd (cnt : Nat → Nat) (i k : Nat) :
    Function.update (Function.update cnt i k) i (Function.update cnt i k i + 1) =
      Function.update cnt i (k + 1) := by
  simp

theorem max_upd {cnt : Nat → Nat} {i k : Nat} (hk : cnt i ≤ k) :
    Function.update cnt i (k + 1) i = max (cnt i) (k + 1) := by
  simp; omega

/-- **Tick of a load.** -/
theorem Hyp.tick_load (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat} (hI : Inv P x t cnt)
    {u : Nat} (hu : u < x.n) (hκ : κ x u = t) {k a : Nat} {bs : List Byte}
    (he : E P (x.evN u).tid k = some (.load (x.evN u).tid a bs))
    (hev : x.evN u = loadU (x.evN u).tid k a bs.length) (hbs : (us.getD u (dflt, [])).2 = bs) :
    ∃ cnt', Inv P x (t + 1) cnt' ∧
      ReflTransGen AStep (cfg P x init t cnt) (cfg P x init (t + 1) cnt') := by
  set i := (x.evN u).tid with hi
  have hR : (x.evN u).isR = true := by rw [hev]; rfl
  have huM : (x.evN u).isM = true := by simp [Ev.isM, hR]
  have hpos : (x.evN u).pos = 2 * k := by rw [hev]; rfl
  have hkl := E_lt he
  have hk : cnt i ≤ k := by
    by_contra hn
    have := hI.rd u hu hR (by rw [hpos, ← hi]; omega); omega
  have h1 := h.catchupTo hI hu hκ huM hpos hkl hk
  have hc1i : Function.update cnt i k i = k := by simp
  have hread : readView ⟨memAt x init t, bufAt P x t (Function.update cnt i k)⟩ i a bs.length =
      some bs := by
    have := h.readAll (cnt := Function.update cnt i k) hu hR hκ (by rw [← hi, hc1i, hpos])
    rwa [hev, hbs] at this
  have hstep := astep_ev (cnt := Function.update cnt i k) (by rw [hc1i]; exact he)
    (XStep.load _ i a bs hread)
  rw [hc1i, Function.update_idem] at hstep
  refine ⟨Function.update cnt i (k + 1), ?_, h1.tail ?_⟩
  · refine h.inv_tick hI hu hκ (by rw [hpos]; omega) (fun j hj => Function.update_of_ne hj _ _)
      (max_upd hk) (by rw [← hi, Function.update_self]; omega) huM (by rw [hpos]; omega)
  · have heq : (⟨memAt x init t, bufAt P x t (Function.update cnt i k)⟩ : XState Nat) =
        ⟨memAt x init (t + 1), bufAt P x (t + 1) (Function.update cnt i (k + 1))⟩ := by
      simp only [XState.mk.injEq]
      refine ⟨(h.memAt_same fun w hw hW he' => ?_).symm, ?_⟩
      · rw [← hκ] at he'
        have := h.κ_inj (h.fst_spec hw).1 hu he'
        rcases h.fst_w hw hW with ⟨hW', -⟩ | hl
        · rw [this] at hW'; exact isR_isW hR hW'
        · rw [this, hev] at hl; simp [isLR, loadU] at hl
      · funext j
        rw [h.bufAt_succ fun v hv hW _ _ he' => by
          rw [← hκ] at he'; have := h.κ_inj hv hu he'; subst this; exact isR_isW hR hW]
        have hb := bufAt_bump P x t (Function.update cnt i k) i j
        rw [hc1i, Function.update_idem] at hb
        rw [hb]
        split
        · subst_vars
          rw [entAt_nonstore (by intro t' a' bs'; rw [he]; simp)]; simp
        · rfl
    nth_rewrite 2 [heq] at hstep
    exact hstep

end


section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

/-- Flush a store at its tick. -/
theorem Hyp.flushStep (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat}
    {u : Nat} (hu : u < x.n) (hκ : κ x u = t) {k a : Nat} {bs : List Byte}
    (he : E P (x.evN u).tid k = some (.store (x.evN u).tid a bs))
    (hev : x.evN u = storeU (x.evN u).tid k a bs) (hk : k < cnt (x.evN u).tid) :
    AStep (cfg P x init t cnt) (cfg P x init (t + 1) cnt) := by
  have huW : (x.evN u).isW = true := by rw [hev]; rfl
  have hnl : isLW (x.evN u) = false := by rw [hev]; rfl
  have hidx : pidx x (x.evN u).tid (2 * k) = u := by
    have := h.pidx_eq hu; rwa [show (x.evN u).pos = 2 * k by rw [hev]; rfl] at this
  have hbuf := bufAt_flush (P := P) (x := x) (cnt := cnt) he (by rw [hidx, hκ]) hk
    (fun c hc t' a' bs' he' => by
      obtain ⟨hv, hev'⟩ := h.storeIdx he'
      rw [← hκ]
      refine h.κ_ghb hv hu (ghb_of_ppo (po_iff.mpr ⟨?_, ?_⟩) (.inl ⟨?_, huW⟩))
      · simp only; rw [hev']; rfl
      · simp only; rw [hev', hev]; simp [storeU]; omega
      · simp only; rw [hev']; rfl)
    (fun c hc t' a' bs' he' hκ' => by
      obtain ⟨hv, hev'⟩ := h.storeIdx he'
      rw [← hκ] at hκ'
      have := h.κ_inj hv hu hκ'
      rw [this, hev] at hev'
      simp [storeU] at hev'; omega)
  have hfl := XFlush.head ⟨memAt x init t, bufAt P x t cnt⟩ (x.evN u).tid a bs _ hbuf
  have key : cfg P x init (t + 1) cnt = ⟨restOf P cnt, ⟨writeMem (memAt x init t) a bs,
      Function.update (bufAt P x t cnt) (x.evN u).tid (bufAt P x (t + 1) cnt (x.evN u).tid)⟩⟩ := by
    simp only [cfg, ACfg.mk.injEq, XState.mk.injEq, true_and]
    constructor
    · have := h.memAt_write hu huW (by rw [fst_of hnl, hκ])
      rw [this, hev]; rfl
    · funext j
      by_cases hj : j = (x.evN u).tid
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        refine h.bufAt_succ fun v hv hW _ htv he' => ?_
        rw [← hκ] at he'
        have := h.κ_inj hv hu he'
        subst this; exact hj htv.symm
  rw [key]
  exact AStep.flush (restOf P cnt) _ _ hfl

/-- **Tick of a store.** -/
theorem Hyp.tick_store (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat} (hI : Inv P x t cnt)
    {u : Nat} (hu : u < x.n) (hκ : κ x u = t) {k a : Nat} {bs : List Byte}
    (he : E P (x.evN u).tid k = some (.store (x.evN u).tid a bs))
    (hev : x.evN u = storeU (x.evN u).tid k a bs) :
    ∃ cnt', Inv P x (t + 1) cnt' ∧
      ReflTransGen AStep (cfg P x init t cnt) (cfg P x init (t + 1) cnt') := by
  have huW : (x.evN u).isW = true := by rw [hev]; rfl
  have huM : (x.evN u).isM = true := by simp [Ev.isM, huW]
  have hpos : (x.evN u).pos = 2 * k := by rw [hev]; rfl
  have hkl := E_lt he
  have hidx : pidx x (x.evN u).tid (2 * k) = u := by
    have := h.pidx_eq hu; rwa [hpos] at this
  by_cases hk : cnt (x.evN u).tid ≤ k
  · have h1 := h.catchupTo hI hu hκ huM hpos hkl hk
    have hc1i : Function.update cnt (x.evN u).tid k (x.evN u).tid = k := by simp
    have hstep := astep_ev (cnt := Function.update cnt (x.evN u).tid k) (by rw [hc1i]; exact he)
      (XStep.store ⟨memAt x init t, bufAt P x t (Function.update cnt (x.evN u).tid k)⟩
        (x.evN u).tid a bs)
    rw [hc1i, Function.update_idem] at hstep
    have heq : enqueue ⟨memAt x init t, bufAt P x t (Function.update cnt (x.evN u).tid k)⟩
        (x.evN u).tid a bs =
        ⟨memAt x init t, bufAt P x t (Function.update cnt (x.evN u).tid (k + 1))⟩ := by
      simp only [enqueue, XState.mk.injEq, true_and]
      funext j
      have hb := bufAt_bump P x t (Function.update cnt (x.evN u).tid k) (x.evN u).tid j
      rw [hc1i, Function.update_idem] at hb
      rw [hb]
      by_cases hj : j = (x.evN u).tid
      · subst hj; simp [entAt_store he, hidx, hκ]
      · simp [hj]
    rw [heq] at hstep
    refine ⟨Function.update cnt (x.evN u).tid (k + 1), ?_, (h1.tail hstep).tail ?_⟩
    · exact h.inv_tick hI hu hκ (by rw [hpos]; omega) (fun j hj => Function.update_of_ne hj _ _)
        (max_upd hk) (by rw [Function.update_self]; omega) huM (by rw [hpos]; omega)
    · exact h.flushStep hu hκ he hev (by simp)
  · refine ⟨cnt, ?_, .single (h.flushStep hu hκ he hev (by omega))⟩
    exact h.inv_tick (k := k) hI hu hκ (by rw [hpos]; omega) (fun _ _ => rfl) (by omega) (hI.le _) huM
      (by rw [hpos]; omega)

/-- **Tick of a locked read-modify-write** (at its read; its write is one tick later). -/
theorem Hyp.tick_rmw (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat} (hI : Inv P x t cnt)
    {u : Nat} (hu : u < x.n) (hκ : κ x u = t) {k a : Nat} {old new : List Byte}
    (he : E P (x.evN u).tid k = some (.rmw (x.evN u).tid a old new))
    (hlen : new.length = old.length)
    (hev : x.evN u = rmwRU (x.evN u).tid k a old.length) (hbs : (us.getD u (dflt, [])).2 = old) :
    ∃ cnt', Inv P x (t + 1) cnt' ∧
      ReflTransGen AStep (cfg P x init t cnt) (cfg P x init (t + 1) cnt') := by
  have hR : (x.evN u).isR = true := by rw [hev]; rfl
  have huM : (x.evN u).isM = true := by simp [Ev.isM, hR]
  have huA : (x.evN u).isA = true := by rw [hev]; rfl
  have hpos : (x.evN u).pos = 2 * k := by rw [hev]; rfl
  have hkl := E_lt he
  have hk : cnt (x.evN u).tid ≤ k := by
    by_contra hn
    have := hI.rd u hu hR (by rw [hpos]; omega); omega
  have h1 := h.catchupTo hI hu hκ huM hpos hkl hk
  have hc1i : Function.update cnt (x.evN u).tid k (x.evN u).tid = k := by simp
  -- the write half
  obtain ⟨hw, hwev, -⟩ := h.evIdx he (p := (rmwWU (x.evN u).tid k a new, []))
    (by simp [evUnits, rmwWU])
  simp only [rmwWU] at hw hwev
  set w := pidx x (x.evN u).tid (2 * k + 1) with hwdef
  have hwW : (x.evN w).isW = true := by rw [hwev]; rfl
  have hwl : isLW (x.evN w) = true := by rw [hwev]; rfl
  have hfw : fstU x w = u :=
    h.fst_lw hwl hu (by rw [hwev]) (by rw [hwev, hpos])
  -- the buffer is empty
  have hemp : bufAt P x t (Function.update cnt (x.evN u).tid k) (x.evN u).tid = [] := by
    apply bufAt_nil
    intro c hc t' a' bs' he'
    rw [hc1i] at hc
    obtain ⟨hv, hev'⟩ := h.storeIdx he'
    rw [← hκ]
    refine h.κ_ghb hv hu (ghb_of_implied (po_iff.mpr ⟨?_, ?_⟩) ?_ hR (.inr huA))
    · simp only; rw [hev']; rfl
    · simp only; rw [hev', hpos]; simp [storeU]; omega
    · simp only; rw [hev']; rfl
  have hview : viewMem ⟨memAt x init t, bufAt P x t (Function.update cnt (x.evN u).tid k)⟩
      (x.evN u).tid = memAt x init t := by
    funext y; simp [viewMem, hemp, readBufByte]
  have hread : readMem (memAt x init t) a old.length = some old := by
    have := h.readAll (cnt := Function.update cnt (x.evN u).tid k) hu hR hκ (by rw [hc1i, hpos])
    rwa [hview, hev, hbs] at this
  have hstep := astep_ev (cnt := Function.update cnt (x.evN u).tid k) (by rw [hc1i]; exact he)
    (XStep.rmw ⟨memAt x init t, bufAt P x t (Function.update cnt (x.evN u).tid k)⟩
      (x.evN u).tid a old new hemp hread hlen)
  rw [hc1i, Function.update_idem] at hstep
  refine ⟨Function.update cnt (x.evN u).tid (k + 1), ?_, h1.tail ?_⟩
  · exact h.inv_tick hI hu hκ (by rw [hpos]; omega) (fun j hj => Function.update_of_ne hj _ _)
      (max_upd hk) (by rw [Function.update_self]; omega) huM (by rw [hpos]; omega)
  · have key : cfg P x init (t + 1) (Function.update cnt (x.evN u).tid (k + 1)) =
        ⟨restOf P (Function.update cnt (x.evN u).tid (k + 1)), ⟨writeMem (memAt x init t) a new,
          bufAt P x t (Function.update cnt (x.evN u).tid k)⟩⟩ := by
      simp only [cfg, ACfg.mk.injEq, XState.mk.injEq, true_and]
      constructor
      · have := h.memAt_write hw hwW (by rw [hfw, hκ])
        rw [this, hwev]
      · funext j
        rw [h.bufAt_succ fun v hv hW _ _ he' => by
          rw [← hκ] at he'; have := h.κ_inj hv hu he'; subst this; exact isR_isW hR hW]
        have hb := bufAt_bump P x t (Function.update cnt (x.evN u).tid k) (x.evN u).tid j
        rw [hc1i, Function.update_idem] at hb
        rw [hb]
        split
        · subst_vars
          rw [entAt_nonstore (by intro t' a' bs'; rw [he]; simp)]; simp
        · rfl
    rw [key]
    exact hstep

end


section
variable {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
  {us : List (Ev × List Byte)}

/-- **One tick.** -/
theorem Hyp.tick (h : Hyp P init s x us) {t : Nat} {cnt : Nat → Nat} (hI : Inv P x t cnt) :
    ∃ cnt', Inv P x (t + 1) cnt' ∧
      ReflTransGen AStep (cfg P x init t cnt) (cfg P x init (t + 1) cnt') := by
  by_cases hex : ∃ u < x.n, κ x u = t
  · obtain ⟨u, hu, hκ⟩ := hex
    -- every write whose block starts at `t` has `u` as its first unit
    have fstEq : ∀ w < x.n, (x.evN w).isW = true → κ x (fstU x w) = t → fstU x w = u :=
      fun w hw _ he => h.κ_inj (h.fst_spec hw).1 hu (he.trans hκ.symm)
    rcases h.kind hu with ⟨c, a, bs, he, hev, hbs⟩ | ⟨c, a, bs, he, hev⟩ |
        ⟨c, a, old, new, he, hlen, ⟨hev, hbs⟩ | hev⟩ | ⟨c, he, hev⟩
    · exact h.tick_load hI hu hκ he hev hbs
    · exact h.tick_store hI hu hκ he hev
    · exact h.tick_rmw hI hu hκ he hlen hev hbs
    · -- the write half of a locked read-modify-write: nothing to do
      have hl : isLW (x.evN u) = true := by rw [hev]; rfl
      refine ⟨cnt, hI.same fun v hv hM hv' => ?_, ?_⟩
      · have := h.κ_inj hv hu (hv'.trans hκ.symm)
        subst this
        obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hv hl
        have h1 := h.κ_fst hv
        rw [h.fst_lw hl hr ht hp] at h1
        simp only [bit, hl, ↓reduceIte] at h1
        have hrR : (x.evN r).isR = true := by
          simp only [isLR, Bool.and_eq_true] at hlr; exact hlr.1
        have hd := hI.done r hr (by simp [Ev.isM, hrR]) (by omega)
        have he2 := h.R_even hr hrR
        rw [ht] at hd; rw [hp]; omega
      · rw [h.cfg_succ (fun w hw hW he' => by
          have := fstEq w hw hW he'
          have h2 := (h.fst_spec hw).2.1
          rw [this, hl] at h2; cases h2)]
    · -- a fence: nothing to do at its tick
      have hnM : (x.evN u).isM = false := by rw [hev]; rfl
      refine ⟨cnt, hI.same fun v hv hM hv' => ?_, ?_⟩
      · have := h.κ_inj hv hu (hv'.trans hκ.symm)
        subst this; rw [hnM] at hM; cases hM
      · rw [h.cfg_succ (fun w hw hW he' => by
          have := fstEq w hw hW he'
          rcases h.fst_w hw hW with ⟨h2, -⟩ | h2
          · rw [this, hev] at h2; simp [fenceU, Ev.isW] at h2
          · rw [this, hev] at h2; simp [isLR, fenceU, Ev.isR] at h2)]
  · have hno : ∀ v < x.n, κ x v ≠ t := fun v hv he => hex ⟨v, hv, he⟩
    refine ⟨cnt, hI.same fun v hv _ he => absurd he (hno v hv), ?_⟩
    rw [h.cfg_succ (fun w hw _ he => hno _ (h.fst_spec hw).1 he)]

/-- A tick after every unit's clock. -/
def tEnd (x : Exec) : Nat := 2 * (x.n * x.n + x.n) + 2

theorem Hyp.κ_lt (h : Hyp P init s x us) {u : Nat} (hu : u < x.n) : κ x u < tEnd x := by
  classical
  have hg : gH x (fstU x u) ≤ x.n := by
    unfold gH
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hm : gH x (fstU x u) * x.n ≤ x.n * x.n := Nat.mul_le_mul_right _ hg
  have := (h.fst_spec hu).1
  have := bit_le x u
  simp only [κ, tEnd]
  omega

theorem Hyp.run_to (h : Hyp P init s x us) : ∀ t, ∃ cnt, Inv P x t cnt ∧
    ReflTransGen AStep (cfg P x init 0 fun _ => 0) (cfg P x init t cnt)
  | 0 => ⟨fun _ => 0, ⟨fun _ => Nat.zero_le _, fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩, .refl⟩
  | t + 1 => by
    obtain ⟨cnt, hI, hr⟩ := h.run_to t
    obtain ⟨cnt', hI', hr'⟩ := h.tick hI
    exact ⟨cnt', hI', hr.trans hr'⟩

/-- After the last tick only fences remain; each finds its buffer empty. -/
theorem Hyp.finish (h : Hyp P init s x us) {cnt : Nat → Nat} (hI : Inv P x (tEnd x) cnt) :
    ∀ m ≤ P.length, ReflTransGen AStep (cfg P x init (tEnd x) cnt)
      (cfg P x init (tEnd x) fun j => if j < m then (P[j]?.getD []).length else cnt j)
  | 0, _ => by simp only [Nat.not_lt_zero, ↓reduceIte]; exact .refl
  | m + 1, hm => by
    have ih := h.finish hI m (by omega)
    set cm : Nat → Nat := fun j => if j < m then (P[j]?.getD []).length else cnt j with hcm
    have hcmm : cm m = cnt m := by simp [hcm]
    have := h.catchup (t := tEnd x) (i := m) ((P[m]?.getD []).length - cnt m) cm (by
      intro c h1 h2
      rw [hcmm] at h1 h2
      have hc : c < (P[m]?.getD []).length := by have := hI.le m; omega
      have hE : E P m c = some ((P[m]?.getD [])[c]'hc) := by
        simp [E, List.getElem?_eq_getElem hc]
      generalize hev : (P[m]?.getD [])[c]'hc = ev at hE
      have hth := h.thread hE
      -- a memory event at `c` would have been executed
      have noMem : ∀ p ∈ evUnits m c ev, p.1.isM = true → False := by
        intro p hp hM
        obtain ⟨hv, hev', -⟩ := h.evIdx hE hp
        have := hI.done _ hv (by rw [hev']; exact hM) (h.κ_lt hv)
        rw [hev', evUnits_tid hp] at this
        have := evUnits_pos hp
        omega
      cases ev with
      | load t' a bs =>
        exact absurd (noMem (loadU m c a bs.length, bs) (by simp [evUnits, loadU]) rfl) id
      | store t' a bs =>
        exact absurd (noMem (storeU m c a bs, []) (by simp [evUnits, storeU]) rfl) id
      | rmw t' a old new =>
        exact absurd (noMem (rmwRU m c a old.length, old) (by simp [evUnits, rmwRU]) rfl) id
      | fence t' =>
        simp only [XEvent.thread] at hth; subst hth
        exact .inr ⟨hE, fun c' _ t'' a bs he' => h.κ_lt (h.storeIdx he').1⟩)
    rw [hcmm, show cnt m + ((P[m]?.getD []).length - cnt m) = (P[m]?.getD []).length by
      have := hI.le m; omega] at this
    have heq : Function.update cm m (P[m]?.getD []).length =
        fun j => if j < m + 1 then (P[j]?.getD []).length else cnt j := by
      funext j
      by_cases hj : j = m
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        simp only [hcm]
        by_cases h1 : j < m
        · simp [h1, show j < m + 1 by omega]
        · simp [h1, show ¬ j < m + 1 by omega]
    rw [heq] at this
    exact ih.trans this

/-- **ax-TSO ⊆ op-TSO.** -/
theorem Hyp.run (h : Hyp P init s x us) : Run P init s := by
  obtain ⟨cnt, hI, hr⟩ := h.run_to (tEnd x)
  have hf := h.finish hI P.length le_rfl
  have h0 : cfg P x init 0 (fun _ => 0) = ⟨P, ⟨init, fun _ => []⟩⟩ := by
    simp only [cfg, ACfg.mk.injEq, XState.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · apply List.ext_getElem?; intro j; rw [restOf_get]; cases P[j]? <;> simp
    · funext y; exact memAt_init fun v _ => Nat.zero_le _
    · funext i; simp [bufAt]
  have h1 : cfg P x init (tEnd x)
      (fun j => if j < P.length then (P[j]?.getD []).length else cnt j) =
      ⟨P.map fun _ => [], s⟩ := by
    cases s with
    | mk mem buf =>
    simp only [cfg, ACfg.mk.injEq, XState.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · apply List.ext_getElem?; intro j; rw [restOf_get]
      by_cases hj : j < P.length
      · simp [hj]
      · have hj' : P.length ≤ j := by omega
        simp [hj']
    · funext y
      have := h.fin y
      simp only at this
      rw [this]
      simp only [memAt]
      rw [List.filter_eq_self.mpr]
      intro w hw
      have := h.κ_lt (h.fst_spec ((h.coM y w).mp hw).1).1
      simpa using this
    · funext i
      rw [bufAt_nil fun c _ t' a bs he => h.κ_lt (h.storeIdx he).1]
      exact (h.hd i).symm
  rw [h0] at hr
  rw [h1] at hf
  exact ⟨hr.trans hf, h.hd⟩

end

/-- **ax-TSO ⊆ op-TSO**, with the hypotheses of `Task.axToOp` (`ThreadCells` is not needed). -/
theorem axToOp {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
    (hT : ThreadsOk P) (hS : RmwSized P) (hI : InitCovers P init) (hd : ∀ t, s.buffer t = [])
    (hp : RmwPaired x) (hx : Explains Exec.Tso P init s x) : Run P init s := by
  obtain ⟨us, hperm, hevs, htso, hreads, hrf, hco, hnd, hfin⟩ := hx
  exact Hyp.run (us := us) ⟨hT, hS, hI, hd, hp, hperm, hevs, htso, hreads, hrf, hco, hnd, hfin⟩


end Silmaril.X86.MemoryModel.OpAx.Proofs.Conv
