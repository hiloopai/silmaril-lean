module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Units

/-!
# The XL bridge: a clock extending `ghb`

Proofs for `Csl.Task.cirXlOpAx`. This is the clock construction
(`Silmaril/Proofs/X86/MemoryModel/OpAx/Conv.lean`, sections "Edges", "`before`", "Consequences",
"Read-modify-write blocks" and "The clock"), **copied** and restated over the CIR hypotheses `H`
(another topic's proof modules may not be imported). The atomicity lemma `H.lemA` and the clock
`κ`, which strictly extends `ghb` (`H.κ_ghb`), is injective (`H.κ_inj`) and puts the locked
write of each read-modify-write one tick after its read (`H.κ_fst`), are unchanged.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte rmwPairs)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff WfFacts mem_touched)
open Relation

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
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

theorem H.sm (h : H P L x U) (c d : Fin x.n) (hsm : x.sm c d = true) : c = d := by
  simp only [Exec.sm, ev_eq, Bool.and_eq_true, beq_iff_eq] at hsm
  exact Fin.ext (h.uniq c.isLt d.isLt hsm.1 hsm.2)

theorem H.unip2 (h : H P L x U) {a b : Fin x.n} (h1 : x.uniproc a b = true)
    (h2 : x.uniproc b a = true) : False :=
  h.tso.2.1 a (TransGen.tail (TransGen.single h1) h2)

theorem H.ghb2 (h : H P L x U) {a b : Fin x.n} (h1 : x.ghb a b = true)
    (h2 : x.ghb b a = true) : False :=
  h.tso.2.2 a (TransGen.tail (TransGen.single h1) h2)

theorem H.ghb1 (h : H P L x U) {a : Fin x.n} (h1 : x.ghb a a = true) : False :=
  h.tso.2.2 a (TransGen.single h1)

theorem H.atomic (h : H P L x U) {r w c : Fin x.n} (hrw : (r.val, w.val) ∈ x.rmw)
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
end

/-! ## Read-modify-write blocks -/

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


/-! ## The CIR hypotheses as the clock's -/

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

theorem H.evs_get (_h : H P L x U) {a : Nat} (ha : a < x.n) : x.evN a = x.evs[a] := by
  simp [Exec.evN, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]

/-- Paired halves of a locked read-modify-write are in `x.rmw`. -/
theorem H.hp (h : H P L x U) (a : Nat) (ha : a < x.n) (b : Nat) (hb : b < x.n)
    (h1 : (x.evN a).isR = true) (h2 : (x.evN b).isW = true) (h3 : (x.evN a).locked = true)
    (h4 : (x.evN b).locked = true) (h5 : (x.evN a).tid = (x.evN b).tid)
    (h6 : (x.evN b).pos = (x.evN a).pos + 1) (h7 : (x.evN a).addr = (x.evN b).addr)
    (h8 : (x.evN a).size = (x.evN b).size) : (a, b) ∈ x.rmw := by
  rw [h.rmw, ← h.evs]
  rw [h.evs_get ha] at h1 h3 h5 h6 h7 h8
  rw [h.evs_get hb] at h2 h4 h5 h6 h7 h8
  simp only [rmwPairs, List.mem_flatMap]
  refine ⟨(x.evs[a], a), List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [ha]), ?_⟩
  simp only [h1, h3, Bool.and_self, ↓reduceIte, List.mem_filterMap]
  refine ⟨(x.evs[b], b), List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hb]), ?_⟩
  simp [h2, h4, h5, h6, h7, h8]

theorem H.coIn (h : H P L x U) {w : Nat} (hw : w < x.n) (hW : (x.evN w).isW = true) {y : Nat}
    (hc : (x.evN w).covers y = true) : w ∈ x.co y := by
  have hev : x.ev ⟨w, hw⟩ = x.evN w := by rw [h.evs_get hw]; rfl
  refine h.wf.coAll y (mem_touched.mpr ⟨x.evN w, ?_, ?_, ?_⟩) ⟨w, hw⟩ (by rw [hev]; exact hW)
    (by rw [hev]; exact hc)
  · rw [h.evs_get hw]; exact List.getElem_mem _
  · simp [Ev.isM, hW]
  · rw [Silmaril.Proofs.X86.Concurrency.Cir.Domain.mem_bytes]
    rwa [covers_iff] at hc

theorem role_isLR {r : Role} {i p : Nat} (h : isLR (r.ev i p) = true) :
    ∃ a sz v, r = .lr a sz v := by
  cases r <;> simp_all [isLR, Role.ev, Ev.isR]

theorem role_isLW {r : Role} {i p : Nat} (h : isLW (r.ev i p) = true) :
    ∃ a sz v, r = .lw a sz v := by
  cases r <;> simp_all [isLW, Role.ev, Ev.isW]

/-- The write half of a locked read. -/
theorem H.partnerR (h : H P L x U) {r : Nat} (hr : r < x.n)
    (hl : isLR (x.evN r) = true) : ∃ w < x.n, (x.evN w).tid = (x.evN r).tid ∧
      (x.evN w).pos = (x.evN r).pos + 1 ∧ isLW (x.evN w) = true ∧
      (x.evN w).addr = (x.evN r).addr ∧ (x.evN w).size = (x.evN r).size := by
  obtain ⟨i, hi, p, hp, he, -⟩ := h.unit hr
  rw [he] at hl ⊢
  obtain ⟨a, sz, v, hrole⟩ := role_isLR hl
  obtain ⟨c, hc, k, hk, rfl⟩ := pos_lab hp
  obtain ⟨hp', hget⟩ := RL_get (L := L) hc hk
  have h1 : (labRoles (L i)[c])[k]? = some (.lr a sz v) := by
    rw [List.getElem?_eq_getElem hk, ← hget]; simp only [hrole]
  obtain ⟨w, hw⟩ := roles_lr h1
  have hk1 : k + 1 < (labRoles (L i)[c]).length := by
    by_contra hn; rw [List.getElem?_eq_none (by omega)] at hw; cases hw
  obtain ⟨hp1, hget1⟩ := RL_get (L := L) hc hk1
  obtain ⟨hu, he1, -⟩ := h.atPos hi hp1
  refine ⟨_, hu, ?_⟩
  rw [he1, hget1, show base L i c + (k + 1) = base L i c + k + 1 by omega]
  have : (labRoles (L i)[c])[k + 1] = .lw a sz w := by
    rw [List.getElem?_eq_getElem hk1] at hw; exact Option.some.inj hw
  simp [this, hrole, Role.ev, isLW, Ev.isW]

/-- The read half of a locked write. -/
theorem H.partnerW (h : H P L x U) {w : Nat} (hw : w < x.n)
    (hl : isLW (x.evN w) = true) : ∃ r < x.n, (x.evN r).tid = (x.evN w).tid ∧
      (x.evN w).pos = (x.evN r).pos + 1 ∧ isLR (x.evN r) = true ∧
      (x.evN w).addr = (x.evN r).addr ∧ (x.evN w).size = (x.evN r).size := by
  obtain ⟨i, hi, p, hp, he, -⟩ := h.unit hw
  rw [he] at hl ⊢
  obtain ⟨a, sz, v, hrole⟩ := role_isLW hl
  obtain ⟨c, hc, k, hk, rfl⟩ := pos_lab hp
  obtain ⟨hp', hget⟩ := RL_get (L := L) hc hk
  have h1 : (labRoles (L i)[c])[k]? = some (.lw a sz v) := by
    rw [List.getElem?_eq_getElem hk, ← hget]; simp only [hrole]
  obtain ⟨k', rfl, o, ho⟩ := roles_lw h1
  have hk1 : k' < (labRoles (L i)[c]).length := by omega
  obtain ⟨hp1, hget1⟩ := RL_get (L := L) hc hk1
  obtain ⟨hu, he1, -⟩ := h.atPos hi hp1
  refine ⟨_, hu, ?_⟩
  rw [he1, hget1]
  have : (labRoles (L i)[c])[k'] = .lr a sz o := by
    rw [List.getElem?_eq_getElem hk1] at ho; exact Option.some.inj ho
  simp [this, hrole, Role.ev, isLR, Ev.isR]
  omega

end

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

theorem H.gnAcyc (h : H P L x U) {a : Nat} (hc : TransGen (GN x) a a) : False := by
  have := GN.lt hc
  exact h.tso.2.2 ⟨a, this.1⟩ (GN.fin hc this.1 this.1)

theorem H.fst_lw (h : H P L x U) {w r : Nat} (hl : isLW (x.evN w) = true) (hr : r < x.n)
    (ht : (x.evN r).tid = (x.evN w).tid) (hp : (x.evN w).pos = (x.evN r).pos + 1) :
    fstU x w = r := by
  simp only [fstU, hl, ↓reduceIte]
  rw [← ht, hp, Nat.add_sub_cancel]
  exact h.pidx_eq hr

theorem H.lst_lr (h : H P L x U) {w r : Nat} (hl : isLR (x.evN r) = true) (hw : w < x.n)
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
theorem H.lemA (h : H P L x U) {r w b : Nat} (hr : r < x.n) (hw : w < x.n)
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
    have hbco : b ∈ x.co y := h.coIn hb hbW hcb
    have hwco : w ∈ x.co y := h.coIn hw hwW hcw
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
          (by simp_all [isLR]) (by simp_all [isLW]) ht.symm hp ha.symm hs.symm
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
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)}

theorem H.gH_lt (h : H P L x U) {a b : Nat} (ha : a < x.n) (hq : QB x a b) :
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

theorem H.fst_spec (h : H P L x U) {u : Nat} (hu : u < x.n) :
    fstU x u < x.n ∧ isLW (x.evN (fstU x u)) = false ∧ fstU x (fstU x u) = fstU x u := by
  cases hl : isLW (x.evN u)
  · rw [fst_of hl]; exact ⟨hu, hl, fst_of hl⟩
  · obtain ⟨r, hr, ht, hp, hlr, -⟩ := h.partnerW hu hl
    rw [h.fst_lw hl hr ht hp]
    exact ⟨hr, lr_lw hlr, fst_of (lr_lw hlr)⟩

theorem H.κ_fst (h : H P L x U) {u : Nat} (hu : u < x.n) :
    κ x (fstU x u) + bit x u = κ x u := by
  obtain ⟨-, h2, h3⟩ := h.fst_spec hu
  simp only [κ, h3, bit, h2]; simp

theorem H.κ_even (h : H P L x U) {u : Nat} (hu : u < x.n) :
    κ x (fstU x u) % 2 = 0 := by
  obtain ⟨-, h2, h3⟩ := h.fst_spec hu
  simp only [κ, h3, bit, h2]; simp

theorem H.κ_inj (h : H P L x U) {u v : Nat} (hu : u < x.n) (hv : v < x.n)
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
theorem H.κ_ghb (h : H P L x U) {a b : Nat} (ha : a < x.n) (hb : b < x.n)
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

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
