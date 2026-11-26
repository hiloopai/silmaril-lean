module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.SurgKeep

/-!
# Localisation: consistency of the new candidate

Edges between the block's units go forward in program order; an edge
between a kept unit and a block unit is a program-order edge (they share no byte), entering from
before the fragment and leaving to after it. A detour through the block is therefore short-cut
by an old edge: `po` (SC, `thinAir`), `mfence`, `implied` or `ppo` (TSO), `mfence`, `ppoXl`,
`lockXl` or `sfenceXl` (XL; with a non-temporal store after an `sfence` the read-to-store order
needs the store to be write-back, hypothesis `hweak`).

* `Surg.sc`, `Surg.tso`, `Surg.xl`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte rmwPairs)
open Relation

namespace Surg

variable {S : Surg} {x : Exec} {ib : Nat → Byte}

/-- A communication edge joins memory units that share a byte. -/
theorem com_bytes {z : Exec} {a b : Fin z.n} (h : z.com a b = true) :
    ∃ y, (z.ev a).covers y = true ∧ (z.ev b).covers y = true ∧ (z.ev a).isM = true ∧
      (z.ev b).isM = true := by
  simp only [Exec.com, BRel.union_iff] at h
  rcases h with h | h | h
  · simp only [Exec.rfR, Bool.and_eq_true] at h
    obtain ⟨⟨hW, hR⟩, h⟩ := h
    obtain ⟨y, hy, hp⟩ := any_bytes.mp h
    simp only [Bool.and_eq_true] at hp
    exact ⟨y, hp.2, hy, isM_of_W hW, isM_of_R hR⟩
  · simp only [Exec.coR, Bool.and_eq_true] at h
    obtain ⟨⟨hW, hW'⟩, h⟩ := h
    obtain ⟨y, hy, hp⟩ := any_bytes.mp h
    simp only [Bool.and_eq_true] at hp
    exact ⟨y, hy, hp.1, isM_of_W hW, isM_of_W hW'⟩
  · simp only [Exec.frR, Bool.and_eq_true] at h
    obtain ⟨⟨hR, hW⟩, h⟩ := h
    obtain ⟨y, hy, hp⟩ := any_bytes.mp h
    simp only [Bool.and_eq_true] at hp
    exact ⟨y, hy, hp.1, isM_of_R hR, isM_of_W hW⟩

theorem gW_sorted (y : Nat) : (S.gW y).Pairwise (· < ·) := by
  unfold gW
  exact List.Pairwise.map _ (fun a b (h : a < b) => by omega) ((List.pairwise_lt_range).filter _)

theorem mem_gW {y w : Nat} (h : w ∈ S.gW y) :
    ∃ k, ∃ hk : k < S.G.length, w = S.A.length + k ∧ (S.G[k]).1.isW = true ∧
      (S.G[k]).1.covers y = true := by
  simp only [gW, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨k, ⟨hk, hc⟩, rfl⟩ := h
  rw [List.getElem?_eq_getElem hk] at hc
  simp only [Option.map_some, Option.getD_some, Bool.and_eq_true] at hc
  exact ⟨k, hk, rfl, hc.1, hc.2⟩

theorem gW_of {y k : Nat} (hk : k < S.G.length) (hW : (S.G[k]).1.isW = true)
    (hc : (S.G[k]).1.covers y = true) : S.A.length + k ∈ S.gW y := by
  simp only [gW, List.mem_map, List.mem_filter, List.mem_range]
  refine ⟨k, ⟨hk, ?_⟩, rfl⟩
  rw [List.getElem?_eq_getElem hk]
  simp [hW, hc]

/-- An edge `po | com;(sm or smT)`. -/
def PoCom (a b : Fin (S.exec x).n) : Prop :=
  (S.exec x).po a b = true ∨ ∃ c, (S.exec x).com a c = true ∧ (c = b ∨ (S.exec x).sm c b = true)

theorem pc_seq {r : BRel (S.exec x).n} (hr : ∀ u v, r u v = true → (S.exec x).com u v = true)
    {a b : Fin (S.exec x).n} (h : (r.seq (S.exec x).sm) a b = true) : PoCom a b := by
  obtain ⟨c, h1, h2⟩ := BRel.seq_elim h
  exact .inr ⟨c, hr _ _ h1, .inr h2⟩

theorem pc_seqT {r : BRel (S.exec x).n} (hr : ∀ u v, r u v = true → (S.exec x).com u v = true)
    {a b : Fin (S.exec x).n} (h : (r.seq (S.exec x).smT) a b = true) : PoCom a b := by
  obtain ⟨c, h1, h2⟩ := BRel.seq_elim h
  simp only [Exec.smT, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h2
  rcases h2 with rfl | ⟨h2, -⟩
  · exact .inr ⟨c, hr _ _ h1, .inl rfl⟩
  · exact .inr ⟨c, hr _ _ h1, .inr h2⟩

theorem comGhb_com {z : Exec} {u v : Fin z.n} (h : (z.rfe.union (z.frR.union z.coR)) u v = true) :
    z.com u v = true := z.comGhb_part h

/-! ## The relations, as `po` or communication -/

theorem scRel_pc {a b : Fin (S.exec x).n} (h : (S.exec x).scRel a b = true) : PoCom a b := by
  simp only [Exec.scRel, BRel.union_iff] at h
  rcases h with h | h
  · exact .inl h
  · exact pc_seq (fun _ _ h => h) h

theorem uniproc_pc {a b : Fin (S.exec x).n} (h : (S.exec x).uniproc a b = true) :
    PoCom a b := by
  simp only [Exec.uniproc, BRel.union_iff] at h
  rcases h with h | h
  · exact .inl ((S.exec x).poLoc_po h)
  · exact pc_seq (fun _ _ h => h) h

theorem ghb_pc {a b : Fin (S.exec x).n} (h : (S.exec x).ghb a b = true) : PoCom a b := by
  simp only [Exec.ghb, BRel.union_iff] at h
  rcases h with h | h | h | h
  · exact .inl ((S.exec x).fencerel_po h)
  · simp only [Exec.implied, Bool.and_eq_true] at h; exact .inl h.1.1.1
  · simp only [Exec.ppo, Bool.and_eq_true] at h; exact .inl h.1
  · exact pc_seq (fun _ _ h => comGhb_com h) h

theorem uniprocXl_pc {a b : Fin (S.exec x).n} (h : (S.exec x).uniprocXl a b = true) :
    PoCom a b := by
  simp only [Exec.uniprocXl, BRel.union_iff] at h
  rcases h with h | h
  · exact .inl ((S.exec x).poLoc_po h)
  · exact pc_seqT (fun _ _ h => h) h

theorem thinAir_pc {a b : Fin (S.exec x).n} (h : (S.exec x).thinAir a b = true) :
    PoCom a b := by
  simp only [Exec.thinAir, BRel.union_iff] at h
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨b, by simp [Exec.com, BRel.union, h], .inl rfl⟩

theorem ghbXl_pc {a b : Fin (S.exec x).n} (h : (S.exec x).ghbXl a b = true) : PoCom a b := by
  simp only [Exec.ghbXl, BRel.union_iff] at h
  rcases h with h | h | h | h | h
  · exact .inl ((S.exec x).fencerel_po h)
  · simp only [Exec.ppoXl, Exec.ppo, Bool.and_eq_true] at h; exact .inl h.1.1.1
  · simp only [Exec.lockXl, Bool.and_eq_true] at h; exact .inl h.1.2
  · simp only [Exec.sfenceXl, Bool.and_eq_true] at h; exact .inl ((S.exec x).fencerel_po h.2)
  · exact pc_seqT (fun _ _ h => comGhb_com h) h

theorem fence_notM {z : Exec} {k} {f : Fin z.n} (h : (z.ev f).isFence k = true) :
    (z.ev f).isM = false := by
  simp only [Ev.isFence, beq_iff_eq] at h
  simp [Ev.isM, Ev.isR, Ev.isW, h]

/-- The propositional core of the TSO short-cut. -/
theorem tso_short : ∀ (aR aW aA bR bW bA b'R b'W b'A cR cW cA : Bool),
    bA = false → b'A = false → (bR || bW) = true → (bR && bW) = false →
    (b'R || b'W) = true → (b'R && b'W) = false → (bW = true → b'W = true) →
    ((aW && bR && (aA || bA)) = true ∨ ((aW && bW) || (aR && (bR || bW))) = true) →
    ((b'W && cR && (b'A || cA)) = true ∨ ((b'W && cW) || (b'R && (cR || cW))) = true) →
    ((aW && cR && (aA || cA)) = true ∨ ((aW && cW) || (aR && (cR || cW))) = true) := by
  decide

/-- The propositional core of the XL short-cut through two `ppoXl` edges. -/
theorem xl_short : ∀ (aR aW bR bW b'R b'W cR cW : Bool),
    (bR || bW) = true → (bR && bW) = false →
    (b'R || b'W) = true → (b'R && b'W) = false → (bW = true → b'W = true) →
    ((aW && bW) || (aR && (bR || bW))) = true →
    ((b'W && cW) || (b'R && (cR || cW))) = true →
    ((aW && cW) || (aR && (cR || cW))) = true := by
  decide


variable (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst)
include H hx

/-- A block unit: its index, thread and position. -/
theorem block_pos {b : Fin (S.exec x).n} (h : κ hx b = none) :
    ∃ k, ∃ hk : k < S.G.length, b.val = S.A.length + k ∧ ((S.exec x).ev b).tid = S.i ∧
      ((S.exec x).ev b).pos = S.p1 + k ∧ (S.exec x).ev b = (S.G[k]).1 := by
  obtain ⟨k, hk, hb, he⟩ := block_ev h
  obtain ⟨t, p⟩ := H.posG k hk
  exact ⟨k, hk, hb, by rw [he, t], by rw [he, p], he⟩

/-- No communication between a kept unit and a block unit. -/
theorem cross_com {a b : Fin (S.exec x).n} {a0 : Fin x.n} (ha : κ hx a = some a0)
    (hb : κ hx b = none) : (S.exec x).com a b = false ∧ (S.exec x).com b a = false := by
  constructor
  · cases h : (S.exec x).com a b
    · rfl
    · obtain ⟨y, h1, h2, h3, -⟩ := com_bytes h
      have := off_kept H hx ha h3 h1
      rw [on_block H hb h2] at this; cases this
  · cases h : (S.exec x).com b a
    · rfl
    · obtain ⟨y, h1, h2, -, h4⟩ := com_bytes h
      have := off_kept H hx ha h4 h2
      rw [on_block H hb h1] at this; cases this

/-- A unit of the same access as a block unit is that unit. -/
theorem sm_block {b c : Fin (S.exec x).n} (hb : κ hx b = none) (h : (S.exec x).sm c b = true) :
    c = b := by
  obtain ⟨k, hk, hbk, tb, pb, -⟩ := block_pos H hx hb
  simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq, tb, pb] at h
  obtain ⟨h1, h2⟩ := h
  cases hc : κ hx c with
  | none =>
    obtain ⟨k', hk', hck, -, pc, -⟩ := block_pos H hx hc
    apply Fin.ext; omega
  | some c0 =>
    exfalso
    obtain ⟨tc, pc⟩ := kept_pos H hx hc
    have hi : (x.ev c0).tid = S.i := tc ▸ h1
    rcases pc with ⟨-, pc1, pc2⟩ | ⟨-, pc1, -⟩
    · have := pc2 hi; omega
    · have := (pc1 hi).1; have := (pc1 hi).2; omega

theorem smT_block {b c : Fin (S.exec x).n} (hb : κ hx b = none) (h : (S.exec x).smT c b = true) :
    c = b := by
  simp only [Exec.smT, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact sm_block H hx hb h

/-- Between block units, edges go forward. -/
theorem block_fwd {a b : Fin (S.exec x).n} (ha : κ hx a = none) (hb : κ hx b = none)
    (h : PoCom a b) : ((S.exec x).ev a).pos < ((S.exec x).ev b).pos := by
  rcases h with h | ⟨c, h1, h2⟩
  · simp only [Exec.po, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  · have hc : c = b := by
      rcases h2 with h2 | h2
      · exact h2
      · exact sm_block H hx hb h2
    subst hc
    obtain ⟨k, hk, hak, -, pa, ea⟩ := block_pos H hx ha
    obtain ⟨k', hk', hbk, -, pb, eb⟩ := block_pos H hx hb
    rw [pa, pb]
    simp only [Exec.com, BRel.union_iff] at h1
    rcases h1 with h1 | h1 | h1
    · exfalso
      simp only [Exec.rfR, Bool.and_eq_true] at h1
      obtain ⟨-, h1⟩ := h1
      obtain ⟨y, -, h1⟩ := any_bytes.mp h1
      simp only [Bool.and_eq_true] at h1
      have : (S.exec x).rf c.val y = none := by
        simp only [exec, show ¬ c.val < S.A.length by omega,
          show c.val < S.A.length + S.G.length by omega, ite_true, ite_false]
      rw [this] at h1; cases h1.1
    · simp only [Exec.coR, Bool.and_eq_true] at h1
      obtain ⟨-, h1⟩ := h1
      obtain ⟨y, hy, hbf⟩ := any_bytes.mp h1
      simp only [Bool.and_eq_true] at hbf
      replace hbf := hbf.2
      have hcb := on_block H ha hy
      simp only [exec, hcb, ite_true] at hbf
      have := before_sorted (gW_sorted y) hbf
      omega
    · simp only [Exec.frR, Bool.and_eq_true] at h1
      obtain ⟨⟨hR, hW⟩, -⟩ := h1
      rw [ea] at hR
      rw [eb] at hW
      by_contra hlt
      have := H.rwG k' k hk' hk (by omega) hW
      exact W_ne_R this hR

theorem smK_kept {b c : Fin (S.exec x).n} {b0} (hb : κ hx b = some b0)
    (h : (S.exec x).sm c b = true) : (κ hx c).isSome := by
  apply isSome_of_ne
  intro hn
  have := sm_block H hx (b := c) (c := b) hn (by
    simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq] at h ⊢; exact ⟨h.1.symm, h.2.symm⟩)
  subst this; rw [hn] at hb; cases hb

/-- Across kept and block units, a `PoCom` edge is a `po` edge. -/
theorem cross_po {a b : Fin (S.exec x).n} (hc : (κ hx a = none) ≠ (κ hx b = none))
    (h : PoCom a b) : (S.exec x).po a b = true := by
  rcases h with h | ⟨c, h1, h2⟩
  · exact h
  · exfalso
    cases hb : κ hx b with
    | none =>
      have hcb : c = b := by
        rcases h2 with h2 | h2
        · exact h2
        · exact sm_block H hx hb h2
      subst hcb
      cases ha : κ hx a with
      | none => exact hc (by rw [ha, hb])
      | some a0 => rw [(cross_com H hx ha hb).1] at h1; cases h1
    | some b0 =>
      have ha : κ hx a = none := by
        cases ha : κ hx a with
        | none => rfl
        | some _ => exact absurd (by rw [ha, hb]; simp) hc
      have hcs : (κ hx c).isSome := by
        rcases h2 with rfl | h2
        · simp [hb]
        · exact smK_kept H hx hb h2
      obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hcs
      rw [(cross_com H hx hc0 ha).2] at h1; cases h1

/-! ## Entering and leaving the block -/

/-- A kept unit before a block unit is before the fragment, in thread `i`. -/
theorem entry {a b : Fin (S.exec x).n} {a0 : Fin x.n} (ha : κ hx a = some a0)
    (hb : κ hx b = none) (h : (S.exec x).po a b = true) :
    (x.ev a0).tid = S.i ∧ (x.ev a0).pos < S.p1 := by
  obtain ⟨k, hk, -, tb, pb, -⟩ := block_pos H hx hb
  obtain ⟨ta, pa⟩ := kept_pos H hx ha
  simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, tb, pb, ta] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rcases pa with ⟨-, pa1, pa2⟩ | ⟨-, pa1, -⟩
  · exact pa2 h1
  · have := (pa1 h1).1; have := (pa1 h1).2; omega

/-- A kept unit after a block unit is after the fragment, in thread `i`. -/
theorem exit {b c : Fin (S.exec x).n} {c0 : Fin x.n} (hc : κ hx c = some c0)
    (hb : κ hx b = none) (h : (S.exec x).po b c = true) :
    (x.ev c0).tid = S.i ∧ S.p1 + S.F.length ≤ (x.ev c0).pos := by
  obtain ⟨k, hk, -, tb, pb, -⟩ := block_pos H hx hb
  obtain ⟨tc, pc⟩ := kept_pos H hx hc
  simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, tb, pb, tc] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.symm, ?_⟩
  rcases pc with ⟨-, pc1, pc2⟩ | ⟨-, pc1, -⟩
  · have := pc2 h1.symm; omega
  · exact (pc1 h1.symm).1

omit H hx in
theorem po_across {a0 c0 : Fin x.n} (ha : (x.ev a0).tid = S.i ∧ (x.ev a0).pos < S.p1)
    (hc : (x.ev c0).tid = S.i ∧ S.p1 + S.F.length ≤ (x.ev c0).pos) : x.po a0 c0 = true := by
  simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨ha.1.trans hc.1.symm, by omega⟩

/-- Along a path of block units, a write is followed by writes. -/
theorem bpath_W {R' : BRel (S.exec x).n} (hR : ∀ u v, R' u v = true → PoCom u v)
    {b b' : Fin (S.exec x).n} (h : BPath R' (κ hx) b b') (hW : ((S.exec x).ev b).isW = true) :
    ((S.exec x).ev b').isW = true := by
  induction h with
  | refl => exact hW
  | tail _ huv ih =>
    obtain ⟨hu, hv, huv⟩ := huv
    have hlt := block_fwd H hx hu hv (hR _ _ huv)
    obtain ⟨k, hk, -, -, pk, ek⟩ := block_pos H hx hu
    obtain ⟨k', hk', -, -, pk', ek'⟩ := block_pos H hx hv
    rw [ek] at ih; rw [ek']
    exact H.rwG k k' hk hk' (by omega) ih

/-- Block units: memory, not locked, write-back. -/
theorem block_attr {b : Fin (S.exec x).n} (hb : κ hx b = none) :
    ((S.exec x).ev b).isM = true ∧ ((S.exec x).ev b).isA = false ∧
      ((S.exec x).ev b).weak = false ∧ (((S.exec x).ev b).isR || ((S.exec x).ev b).isW) = true ∧
      (((S.exec x).ev b).isR && ((S.exec x).ev b).isW) = false := by
  obtain ⟨h1, h2, h3⟩ := block_mem H hb
  refine ⟨block_isM H hb, by simp [Ev.isA, h2], by simp [Ev.weak, h3], by
    rcases h1 with h | h <;> simp [h], ?_⟩
  cases hR : ((S.exec x).ev b).isR <;> cases hW : ((S.exec x).ev b).isW <;> simp
  exact W_ne_R hW hR

/-! ## The models -/

variable (hwf : x.Wf = true) (hrmw : x.rmw = rmwPairs x.evs)
include hwf hrmw

theorem sc (hsc : x.Sc) : (S.exec x).Sc := by
  have E := emb H hwf hx hrmw
  refine ⟨E.atomic hsc.1, acyclic_of_shortcut hsc.2
    (fun a b a0 b0 ha hb h => .single (E.scRel ha hb h)) (fun a => ((S.exec x).ev a).pos)
    (fun a b ha hb h => block_fwd H hx ha hb (scRel_pc h)) ?_⟩
  intro a b b' c a0 c0 ha hc hb hb' h1 _ h2
  have p1 := cross_po H hx (by simp [ha, hb]) (scRel_pc h1)
  have p2 := cross_po H hx (by simp [hc, hb']) (scRel_pc h2)
  exact .single (BRel.union_iff.mpr (.inl (po_across (entry H hx ha hb p1) (exit H hx hc hb' p2))))

/-- `po` from a kept unit to a fence before a block unit. -/
theorem fence_entry {a b f : Fin (S.exec x).n} {a0 : Fin x.n} (ha : κ hx a = some a0)
    (hb : κ hx b = none) (hf : ((S.exec x).ev f).isM = false) (h1 : (S.exec x).po a f = true)
    (h2 : (S.exec x).po f b = true) :
    ∃ f0, κ hx f = some f0 ∧ x.po a0 f0 = true ∧
      ((x.ev f0).tid = S.i ∧ (x.ev f0).pos < S.p1) := by
  have E := emb H hwf hx hrmw
  obtain ⟨f0, hf0⟩ := Emb.some_of (E.fence f hf)
  exact ⟨f0, hf0, by rw [← E.po a f a0 f0 ha hf0]; exact h1, entry H hx hf0 hb h2⟩

theorem fence_exit {b c f : Fin (S.exec x).n} {c0 : Fin x.n} (hc : κ hx c = some c0)
    (hb : κ hx b = none) (hf : ((S.exec x).ev f).isM = false) (h1 : (S.exec x).po b f = true)
    (h2 : (S.exec x).po f c = true) :
    ∃ f0, κ hx f = some f0 ∧ x.po f0 c0 = true ∧
      ((x.ev f0).tid = S.i ∧ S.p1 + S.F.length ≤ (x.ev f0).pos) := by
  have E := emb H hwf hx hrmw
  obtain ⟨f0, hf0⟩ := Emb.some_of (E.fence f hf)
  exact ⟨f0, hf0, by rw [← E.po f c f0 c0 hf0 hc]; exact h2, exit H hx hf0 hb h1⟩

/-- `fencerel` from a kept unit into the block becomes a `fencerel` to a unit after it. -/
theorem fencerel_entry {k} {a b : Fin (S.exec x).n} {a0 c0 : Fin x.n} (ha : κ hx a = some a0)
    (hb : κ hx b = none) (hc : (x.ev c0).tid = S.i ∧ S.p1 + S.F.length ≤ (x.ev c0).pos)
    (h : (S.exec x).fencerel k a b = true) : x.fencerel k a0 c0 = true := by
  have E := emb H hwf hx hrmw
  simp only [Exec.fencerel, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨f, -, ⟨hf, h1⟩, h2⟩ := h
  obtain ⟨f0, hf0, h3, h4⟩ := fence_entry H hx hwf hrmw ha hb (fence_notM hf) h1 h2
  exact ⟨f0, List.mem_finRange _, ⟨by rw [← (E.same f f0 hf0).isFence]; exact hf, h3⟩,
    po_across h4 hc⟩

theorem fencerel_exit {k} {b c : Fin (S.exec x).n} {a0 c0 : Fin x.n} (hc : κ hx c = some c0)
    (hb : κ hx b = none) (ha : (x.ev a0).tid = S.i ∧ (x.ev a0).pos < S.p1)
    (h : (S.exec x).fencerel k b c = true) : x.fencerel k a0 c0 = true := by
  have E := emb H hwf hx hrmw
  simp only [Exec.fencerel, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨f, -, ⟨hf, h1⟩, h2⟩ := h
  obtain ⟨f0, hf0, h3, h4⟩ := fence_exit H hx hwf hrmw hc hb (fence_notM hf) h1 h2
  exact ⟨f0, List.mem_finRange _, ⟨by rw [← (E.same f f0 hf0).isFence]; exact hf,
    po_across ha h4⟩, h3⟩

omit hwf hrmw in
/-- A `comGhb`/`comGhbXl`-style edge never crosses between kept and block units. -/
theorem cross_seq {r : BRel (S.exec x).n} (hr : ∀ u v, r u v = true → (S.exec x).com u v = true)
    {u v : Fin (S.exec x).n} (huv : (κ hx u = none) ≠ (κ hx v = none))
    (h : PoCom u v) (hpc : ∃ c', r u c' = true ∧ (c' = v ∨ (S.exec x).sm c' v = true)) : False := by
  obtain ⟨c', h3, h4⟩ := hpc
  have h5 := hr _ _ h3
  cases hv : κ hx v with
  | none =>
    have : c' = v := by
      rcases h4 with h4 | h4
      · exact h4
      · exact sm_block H hx hv h4
    subst this
    cases hu : κ hx u with
    | none => exact huv (by rw [hu, hv])
    | some u0 => rw [(cross_com H hx hu hv).1] at h5; cases h5
  | some v0 =>
    have hu : κ hx u = none := by
      cases hu : κ hx u with
      | none => rfl
      | some _ => exact absurd (by rw [hu, hv]; simp) huv
    have hcs : (κ hx c').isSome := by
      rcases h4 with rfl | h4
      · simp [hv]
      · exact smK_kept H hx hv h4
    obtain ⟨c0', hc0'⟩ := Option.isSome_iff_exists.mp hcs
    rw [(cross_com H hx hc0' hu).2] at h5; cases h5

omit H hx hwf hrmw in
theorem seq_wit {z : Exec} {r : BRel z.n} {u v : Fin z.n} (h : (r.seq z.sm) u v = true) :
    ∃ c', r u c' = true ∧ (c' = v ∨ z.sm c' v = true) := by
  obtain ⟨c', h3, h4⟩ := BRel.seq_elim h
  exact ⟨c', h3, .inr h4⟩

omit H hx hwf hrmw in
theorem seqT_wit {z : Exec} {r : BRel z.n} {u v : Fin z.n} (h : (r.seq z.smT) u v = true) :
    ∃ c', r u c' = true ∧ (c' = v ∨ z.sm c' v = true) := by
  obtain ⟨c', h3, h4⟩ := BRel.seq_elim h
  simp only [Exec.smT, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h4
  rcases h4 with rfl | ⟨h4, -⟩
  · exact ⟨c', h3, .inl rfl⟩
  · exact ⟨c', h3, .inr h4⟩

omit hwf hrmw in
/-- No `po-loc` edge between a kept unit and a block unit. -/
theorem cross_poLoc {a b : Fin (S.exec x).n} {a0 : Fin x.n} (ha : κ hx a = some a0)
    (hb : κ hx b = none) : (S.exec x).poLoc a b = false ∧ (S.exec x).poLoc b a = false := by
  constructor
  · cases h : (S.exec x).poLoc a b
    · rfl
    · simp only [Exec.poLoc, BRel.inter_iff, Exec.loc, Bool.and_eq_true] at h
      obtain ⟨-, ⟨hM, -⟩, hy⟩ := h
      obtain ⟨y, hy1, hy2⟩ := any_bytes.mp hy
      have := off_kept H hx ha hM hy1
      rw [on_block H hb hy2] at this; cases this
  · cases h : (S.exec x).poLoc b a
    · rfl
    · simp only [Exec.poLoc, BRel.inter_iff, Exec.loc, Bool.and_eq_true] at h
      obtain ⟨-, ⟨-, hM⟩, hy⟩ := h
      obtain ⟨y, hy1, hy2⟩ := any_bytes.mp hy
      have := off_kept H hx ha hM hy2
      rw [on_block H hb hy1] at this; cases this

theorem tso (htso : x.Tso) : (S.exec x).Tso := by
  have E := emb H hwf hx hrmw
  obtain ⟨hat, hu, hg⟩ := htso
  refine ⟨E.atomic hat, ?_, ?_⟩
  · refine acyclic_of_shortcut hu (fun a b a0 b0 ha hb h => .single (E.uniproc ha hb h))
      (fun a => ((S.exec x).ev a).pos)
      (fun a b ha hb h => block_fwd H hx ha hb (uniproc_pc h)) ?_
    intro a b b' c a0 c0 ha hc hb hb' h1 _ _
    exfalso
    simp only [Exec.uniproc, BRel.union_iff] at h1
    rcases h1 with h1 | h1
    · rw [(cross_poLoc H hx ha hb).1] at h1; cases h1
    · exact cross_seq H hx (fun _ _ h => h) (by simp [ha, hb]) (uniproc_pc (BRel.union_iff.mpr
        (.inr h1))) (seq_wit h1)
  · refine acyclic_of_shortcut hg (fun a b a0 b0 ha hb h => .single (E.ghb ha hb h))
      (fun a => ((S.exec x).ev a).pos)
      (fun a b ha hb h => block_fwd H hx ha hb (ghb_pc h)) ?_
    intro a b b' c a0 c0 ha hc hb hb' h1 hp h2
    have p1 := cross_po H hx (by simp [ha, hb]) (ghb_pc h1)
    have p2 := cross_po H hx (by simp [hc, hb']) (ghb_pc h2)
    have en := entry H hx ha hb p1
    have ex := exit H hx hc hb' p2
    have hpo := po_across en ex
    have sa := E.same a a0 ha
    have sc := E.same c c0 hc
    obtain ⟨-, hbA, -, hbRW, hbx⟩ := block_attr H hx hb
    obtain ⟨-, hb'A, -, hb'RW, hb'x⟩ := block_attr H hx hb'
    have h1' := ghb_pc h1
    have h2' := ghb_pc h2
    apply TransGen.single
    show x.ghb a0 c0 = true
    simp only [Exec.ghb, BRel.union_iff] at h1 h2 ⊢
    rcases h1 with h1 | h1 | h1 | h1
    · exact .inl (fencerel_entry H hx hwf hrmw ha hb ex h1)
    rotate_left
    rotate_left
    · exact (cross_seq H hx (fun _ _ h => comGhb_com h) (by simp [ha, hb]) h1' (seq_wit h1)).elim
    all_goals
      rcases h2 with h2 | h2 | h2 | h2
      · exact .inl (fencerel_exit H hx hwf hrmw hc hb' en h2)
      rotate_left
      rotate_left
      · exact (cross_seq H hx (fun _ _ h => comGhb_com h) (by simp [hc, hb']) h2' (seq_wit h2)).elim
    all_goals
      right
      have e1 : ((S.exec x).implied a b = true ∨ (S.exec x).ppo a b = true) := by
        first | exact .inl h1 | exact .inr h1
      have e2 : ((S.exec x).implied b' c = true ∨ (S.exec x).ppo b' c = true) := by
        first | exact .inl h2 | exact .inr h2
      simp only [Exec.implied, Exec.ppo, Ev.isM, p1, p2, Bool.true_and] at e1 e2
      have k := tso_short _ _ _ _ _ _ _ _ _ _ _ _ hbA hb'A hbRW hbx hb'RW hb'x
        (bpath_W H hx (fun _ _ h => ghb_pc h) hp) e1 e2
      have goal : (x.implied a0 c0 = true ∨ x.ppo a0 c0 = true) := by
        simp only [Exec.implied, Exec.ppo, Ev.isM, hpo, Bool.true_and, ← sa.isR, ← sa.isW,
          ← sa.isA, ← sc.isR, ← sc.isW, ← sc.isA]
        exact k
      rcases goal with g | g
      · exact .inl g
      · exact .inr (.inl g)

/-- `lockXl` from a kept unit into the block, continued to a memory unit after it. -/
theorem lock_entry {a b : Fin (S.exec x).n} {a0 c0 : Fin x.n} (ha : κ hx a = some a0)
    (hb : κ hx b = none) (hc : (x.ev c0).tid = S.i ∧ S.p1 + S.F.length ≤ (x.ev c0).pos)
    (hcM : (x.ev c0).isM = true) (hpo : x.po a0 c0 = true)
    (h : (S.exec x).lockXl a b = true) : x.lockXl a0 c0 = true := by
  have E := emb H hwf hx hrmw
  have sa := E.same a a0 ha
  obtain ⟨-, hbA, -⟩ := block_attr H hx hb
  simp only [Exec.lockXl, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h ⊢
  obtain ⟨⟨⟨haM, -⟩, -⟩, h⟩ := h
  refine ⟨⟨⟨by rw [← sa.isM]; exact haM, hcM⟩, hpo⟩, ?_⟩
  rcases h with (h | h) | ⟨l, -, ⟨hl, h1⟩, h2⟩
  · exact .inl (.inl (by rw [← sa.isA]; exact h))
  · rw [hbA] at h; cases h
  · obtain ⟨l0, hl0⟩ := Emb.some_of (E.locked l hl)
    exact .inr ⟨l0, List.mem_finRange _, ⟨by rw [← (E.same l l0 hl0).isA]; exact hl,
      by rw [← E.po a l a0 l0 ha hl0]; exact h1⟩, po_across (entry H hx hl0 hb h2) hc⟩

theorem lock_exit {b c : Fin (S.exec x).n} {a0 c0 : Fin x.n} (hc : κ hx c = some c0)
    (hb : κ hx b = none) (ha : (x.ev a0).tid = S.i ∧ (x.ev a0).pos < S.p1)
    (haM : (x.ev a0).isM = true) (hpo : x.po a0 c0 = true)
    (h : (S.exec x).lockXl b c = true) : x.lockXl a0 c0 = true := by
  have E := emb H hwf hx hrmw
  have sc := E.same c c0 hc
  obtain ⟨-, hbA, -⟩ := block_attr H hx hb
  simp only [Exec.lockXl, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h ⊢
  obtain ⟨⟨⟨-, hcM⟩, -⟩, h⟩ := h
  refine ⟨⟨⟨haM, by rw [← sc.isM]; exact hcM⟩, hpo⟩, ?_⟩
  rcases h with (h | h) | ⟨l, -, ⟨hl, h1⟩, h2⟩
  · rw [hbA] at h; cases h
  · exact .inl (.inr (by rw [← sc.isA]; exact h))
  · obtain ⟨l0, hl0⟩ := Emb.some_of (E.locked l hl)
    exact .inr ⟨l0, List.mem_finRange _, ⟨by rw [← (E.same l l0 hl0).isA]; exact hl,
      po_across ha (exit H hx hl0 hb h1)⟩, by rw [← E.po l c l0 c0 hl0 hc]; exact h2⟩

theorem xl (hxl : x.Xl)
    (hweak : ∀ u ∈ S.C, u.1.tid = S.i → u.1.isW = true → u.1.weak = false) :
    (S.exec x).Xl := by
  have E := emb H hwf hx hrmw
  obtain ⟨hat, hu, hta, hg⟩ := hxl
  refine ⟨E.atomic hat, ?_, ?_, ?_⟩
  · refine acyclic_of_shortcut hu (fun a b a0 b0 ha hb h => .single (E.uniprocXl ha hb h))
      (fun a => ((S.exec x).ev a).pos)
      (fun a b ha hb h => block_fwd H hx ha hb (uniprocXl_pc h)) ?_
    intro a b b' c a0 c0 ha hc hb hb' h1 _ _
    exfalso
    simp only [Exec.uniprocXl, BRel.union_iff] at h1
    rcases h1 with h1 | h1
    · rw [(cross_poLoc H hx ha hb).1] at h1; cases h1
    · exact cross_seq H hx (fun _ _ h => h) (by simp [ha, hb]) (uniprocXl_pc (BRel.union_iff.mpr
        (.inr h1))) (seqT_wit h1)
  · refine acyclic_of_shortcut hta (fun a b a0 b0 ha hb h => .single (E.thinAir ha hb h))
      (fun a => ((S.exec x).ev a).pos)
      (fun a b ha hb h => block_fwd H hx ha hb (thinAir_pc h)) ?_
    intro a b b' c a0 c0 ha hc hb hb' h1 _ h2
    have p1 := cross_po H hx (by simp [ha, hb]) (thinAir_pc h1)
    have p2 := cross_po H hx (by simp [hc, hb']) (thinAir_pc h2)
    exact .single (BRel.union_iff.mpr (.inl (po_across (entry H hx ha hb p1)
      (exit H hx hc hb' p2))))
  · refine acyclic_of_shortcut hg (fun a b a0 b0 ha hb h => .single (E.ghbXl ha hb h))
      (fun a => ((S.exec x).ev a).pos)
      (fun a b ha hb h => block_fwd H hx ha hb (ghbXl_pc h)) ?_
    intro a b b' c a0 c0 ha hc hb hb' h1 hp h2
    have p1 := cross_po H hx (by simp [ha, hb]) (ghbXl_pc h1)
    have p2 := cross_po H hx (by simp [hc, hb']) (ghbXl_pc h2)
    have en := entry H hx ha hb p1
    have ex := exit H hx hc hb' p2
    have hpo := po_across en ex
    have sa := E.same a a0 ha
    have sc := E.same c c0 hc
    obtain ⟨-, hbA, hbK, hbRW, hbx⟩ := block_attr H hx hb
    obtain ⟨-, hb'A, hb'K, hb'RW, hb'x⟩ := block_attr H hx hb'
    have hmono := bpath_W H hx (fun _ _ h => ghbXl_pc h) hp
    have h1' := ghbXl_pc h1
    have h2' := ghbXl_pc h2
    -- `c` is a write of thread `i` after the fragment: write-back
    have hcK : (x.ev c0).isW = true → (x.ev c0).weak = false := by
      intro hW
      obtain ⟨u, hu, hue⟩ := ((kept_ev hx hc).resolve_left (fun h => by
        have := (exit H hx hc hb' p2)
        rcases kept_pos H hx hc with ⟨-, h' | h'⟩
        · have := h'.2.2 this.1; omega
        · omega)).2.2.2
      rw [← hue]; exact hweak u hu (by rw [hue]; exact ex.1) (by rw [hue]; exact hW)
    apply TransGen.single
    show x.ghbXl a0 c0 = true
    simp only [Exec.ghbXl, BRel.union_iff] at h1 h2 ⊢
    have aM_of : ((S.exec x).ppoXl a b = true ∨ (S.exec x).lockXl a b = true ∨
        (S.exec x).sfenceXl a b = true) → (x.ev a0).isM = true := by
      rw [← sa.isM]; rintro (h | h | h)
      · simp only [Exec.ppoXl, Exec.ppo, Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h.1.1.2 with ⟨h, -⟩ | ⟨h, -⟩
        · exact isM_of_W h
        · exact isM_of_R h
      · simp only [Exec.lockXl, Bool.and_eq_true] at h; exact h.1.1.1
      · simp only [Exec.sfenceXl, Bool.and_eq_true] at h; exact isM_of_W h.1.1
    have cM_of : ((S.exec x).ppoXl b' c = true ∨ (S.exec x).lockXl b' c = true ∨
        (S.exec x).sfenceXl b' c = true) → (x.ev c0).isM = true := by
      rw [← sc.isM]; rintro (h | h | h)
      · simp only [Exec.ppoXl, Exec.ppo, Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h.1.1.2 with ⟨-, h⟩ | ⟨-, h⟩
        · exact isM_of_W h
        · exact h
      · simp only [Exec.lockXl, Bool.and_eq_true] at h; exact h.1.1.2
      · simp only [Exec.sfenceXl, Bool.and_eq_true] at h; exact isM_of_W h.1.2
    have hppo : ∀ {u v : Fin (S.exec x).n}, (S.exec x).po u v = true →
        (S.exec x).ppoXl u v = true →
        (((((S.exec x).ev u).isW && ((S.exec x).ev v).isW) ||
          (((S.exec x).ev u).isR && (((S.exec x).ev v).isR || ((S.exec x).ev v).isW))) = true ∧
          ((S.exec x).ev u).weak = false ∧ ((S.exec x).ev v).weak = false) := by
      intro u v hp h
      simp only [Exec.ppoXl, Exec.ppo, Ev.isM, hp, Bool.true_and, Bool.and_eq_true,
        Bool.not_eq_true'] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have goal_ppo : (((x.ev a0).isW && (x.ev c0).isW) ||
        ((x.ev a0).isR && ((x.ev c0).isR || (x.ev c0).isW))) = true → (x.ev a0).weak = false →
        (x.ev c0).weak = false → x.ppoXl a0 c0 = true := by
      intro h1 h2 h3
      simp only [Exec.ppoXl, Exec.ppo, Ev.isM, hpo, h1, h2, h3, Bool.not_false,
        Bool.and_true]
    have goal_sf : (x.ev a0).isW = true → (x.ev c0).isW = true →
        x.fencerel .sfence a0 c0 = true → x.sfenceXl a0 c0 = true := by
      intro h1 h2 h3
      simp only [Exec.sfenceXl, h1, h2, h3, Bool.and_self]
    have pp : (S.exec x).ppoXl a b = true → (S.exec x).ppoXl b' c = true →
        x.ppoXl a0 c0 = true := by
      intro e1 e2
      obtain ⟨k1, ka, -⟩ := hppo p1 e1
      obtain ⟨k2, -, kc⟩ := hppo p2 e2
      have k := xl_short _ _ _ _ _ _ _ _ hbRW hbx hb'RW hb'x hmono k1 k2
      refine goal_ppo ?_ (by rw [← sa.weak]; exact ka) (by rw [← sc.weak]; exact kc)
      rw [← sa.isR, ← sa.isW, ← sc.isR, ← sc.isW]; exact k
    have ps : (S.exec x).ppoXl a b = true → (S.exec x).sfenceXl b' c = true →
        x.ppoXl a0 c0 = true ∨ x.sfenceXl a0 c0 = true := by
      intro e1 e2
      obtain ⟨k1, ka, -⟩ := hppo p1 e1
      simp only [Exec.sfenceXl, Bool.and_eq_true] at e2
      obtain ⟨⟨-, hcW⟩, hf⟩ := e2
      have hcW0 : (x.ev c0).isW = true := by rw [← sc.isW]; exact hcW
      cases haW : ((S.exec x).ev a).isW
      · left
        simp only [haW, Bool.false_and, Bool.false_or, Bool.and_eq_true] at k1
        refine goal_ppo ?_ (by rw [← sa.weak]; exact ka) (hcK hcW0)
        simp [← sa.isR, k1.1, hcW0]
      · right
        exact goal_sf (by rw [← sa.isW]; exact haW) hcW0
          (fencerel_exit H hx hwf hrmw hc hb' en hf)
    have sp : (S.exec x).sfenceXl a b = true → (S.exec x).ppoXl b' c = true →
        x.sfenceXl a0 c0 = true := by
      intro e1 e2
      simp only [Exec.sfenceXl, Bool.and_eq_true] at e1
      obtain ⟨⟨haW, hbW⟩, hf⟩ := e1
      obtain ⟨k2, -, -⟩ := hppo p2 e2
      have hb'W := hmono hbW
      have hb'R : ((S.exec x).ev b').isR = false := by
        cases h : ((S.exec x).ev b').isR
        · rfl
        · rw [h, hb'W] at hb'x; cases hb'x
      simp only [hb'W, hb'R, Bool.true_and, Bool.false_and, Bool.or_false] at k2
      exact goal_sf (by rw [← sa.isW]; exact haW) (by rw [← sc.isW]; exact k2)
        (fencerel_entry H hx hwf hrmw ha hb ex hf)
    have ss : (S.exec x).sfenceXl a b = true → (S.exec x).sfenceXl b' c = true →
        x.sfenceXl a0 c0 = true := by
      intro e1 e2
      simp only [Exec.sfenceXl, Bool.and_eq_true] at e1 e2
      exact goal_sf (by rw [← sa.isW]; exact e1.1.1) (by rw [← sc.isW]; exact e2.1.2)
        (fencerel_entry H hx hwf hrmw ha hb ex e1.2)
    have cr1 : (S.exec x).comGhbXl a b = true → False := fun h =>
      cross_seq H hx (fun _ _ h => comGhb_com h) (by simp [ha, hb]) h1' (seqT_wit h)
    have cr2 : (S.exec x).comGhbXl b' c = true → False := fun h =>
      cross_seq H hx (fun _ _ h => comGhb_com h) (by simp [hc, hb']) h2' (seqT_wit h)
    rcases h1 with h1 | h1 | h1 | h1 | h1
    · exact .inl (fencerel_entry H hx hwf hrmw ha hb ex h1)
    · rcases h2 with h2 | h2 | h2 | h2 | h2
      · exact .inl (fencerel_exit H hx hwf hrmw hc hb' en h2)
      · exact .inr (.inl (pp h1 h2))
      · exact .inr (.inr (.inl (lock_exit H hx hwf hrmw hc hb' en (aM_of (.inl h1)) hpo h2)))
      · rcases ps h1 h2 with g | g
        · exact .inr (.inl g)
        · exact .inr (.inr (.inr (.inl g)))
      · exact (cr2 h2).elim
    · have le : (x.ev c0).isM = true → x.mfence a0 c0 = true ∨ x.ppoXl a0 c0 = true ∨
          x.lockXl a0 c0 = true ∨ x.sfenceXl a0 c0 = true ∨ x.comGhbXl a0 c0 = true :=
        fun hcM => .inr (.inr (.inl (lock_entry H hx hwf hrmw ha hb ex hcM hpo h1)))
      rcases h2 with h2 | h2 | h2 | h2 | h2
      · exact .inl (fencerel_exit H hx hwf hrmw hc hb' en h2)
      · exact le (cM_of (.inl h2))
      · exact le (cM_of (.inr (.inl h2)))
      · exact le (cM_of (.inr (.inr h2)))
      · exact (cr2 h2).elim
    · rcases h2 with h2 | h2 | h2 | h2 | h2
      · exact .inl (fencerel_exit H hx hwf hrmw hc hb' en h2)
      · exact .inr (.inr (.inr (.inl (sp h1 h2))))
      · exact .inr (.inr (.inl (lock_exit H hx hwf hrmw hc hb' en (aM_of (.inr (.inr h1))) hpo h2)))
      · exact .inr (.inr (.inr (.inl (ss h1 h2))))
      · exact (cr2 h2).elim
    · exact (cr1 h1).elim

end Surg

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
