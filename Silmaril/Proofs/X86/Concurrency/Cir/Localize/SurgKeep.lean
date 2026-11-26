module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Surgery

/-!
# Localisation: the kept units of a surgery

The partial map `Surg.κ` from the new units to the old ones (the block's
units are not kept), and `Surg.emb`: it is an `Emb`, so every model edge between kept units is
an old edge.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte dummyEv rmwPairs writtenByte)

namespace Surg

variable (S : Surg)

/-- The old index of a new unit (`none` for the block's units). -/
def κN (k : Nat) : Option Nat :=
  if k < S.A.length then some k
  else if k < S.A.length + S.G.length then none
  else some (k - S.G.length + S.F.length)

theorem κN_some {k k0 : Nat} (h : S.κN k = some k0) :
    (k < S.A.length ∧ k0 = k) ∨
      (S.A.length + S.G.length ≤ k ∧ k0 = k - S.G.length + S.F.length) := by
  unfold κN at h
  split at h
  · cases h; exact .inl ⟨‹_›, rfl⟩
  · split at h
    · cases h
    · cases h; exact .inr ⟨by omega, rfl⟩

theorem κN_none {k : Nat} : S.κN k = none ↔ S.A.length ≤ k ∧ k < S.A.length + S.G.length := by
  unfold κN
  split
  · simp; omega
  · split
    · simp; omega
    · simp; omega

theorem length_new' : S.new.length = S.A.length + S.G.length + S.C.length := by
  simpa using S.length_new

theorem length_old' : S.old.length = S.A.length + S.F.length + S.C.length := by
  simpa using S.length_old

theorem σ_eq_iff {a a0 : Nat} (ha : a < S.new.length) (h : S.κN a = some a0) (c : Nat) :
    S.σ c = a ↔ c = a0 := by
  have hn := S.length_new'
  unfold σ
  rcases S.κN_some h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · split
    · rfl
    · split <;> omega
  · split
    · omega
    · split <;> omega

theorem σ_kept {v : Nat} (hv : v < S.old.length)
    (hF : ¬ (S.A.length ≤ v ∧ v < S.A.length + S.F.length)) :
    S.σ v < S.new.length ∧ S.κN (S.σ v) = some v := by
  have hn := S.length_new'
  have ho := S.length_old'
  unfold σ κN
  by_cases h1 : v < S.A.length
  · exact ⟨by simp only [h1, ite_true]; omega, by simp [h1]⟩
  · have h2 : ¬ v < S.A.length + S.F.length := by omega
    simp only [h1, h2, ite_false]
    refine ⟨by omega, ?_⟩
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    congr 1; omega

/-! ## The map on units -/

variable {S} {x : Exec}

theorem n_old (hx : x.evs = S.old.map Prod.fst) : x.n = S.A.length + S.F.length + S.C.length := by
  rw [Exec.n, hx]; exact S.length_old

theorem n_new : (S.exec x).n = S.A.length + S.G.length + S.C.length := S.length_new

/-- **The kept units.** -/
def κ (hx : x.evs = S.old.map Prod.fst) (a : Fin (S.exec x).n) : Option (Fin x.n) :=
  (S.κN a.val).pmap (fun k hk => ⟨k, hk⟩) (by
    intro k hk
    have := lt_of_lt_of_eq a.2 n_new
    rw [n_old hx]
    rcases S.κN_some hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> omega)

theorem κ_some {hx : x.evs = S.old.map Prod.fst} {a : Fin (S.exec x).n} {a0 : Fin x.n} :
    κ hx a = some a0 ↔ S.κN a.val = some a0.val := by
  simp only [κ, Option.pmap_eq_some_iff]
  constructor
  · rintro ⟨k, hk, h1, rfl⟩; exact h1
  · intro h; exact ⟨a0.val, a0.2, h, rfl⟩

theorem κ_none {hx : x.evs = S.old.map Prod.fst} {a : Fin (S.exec x).n} :
    κ hx a = none ↔ S.A.length ≤ a.val ∧ a.val < S.A.length + S.G.length := by
  simp only [κ, Option.pmap_eq_none_iff, S.κN_none]

theorem ev_old (hx : x.evs = S.old.map Prod.fst) (a0 : Fin x.n) :
    x.ev a0 = (S.old.map Prod.fst)[a0.val]'(by rw [← hx]; exact a0.2) := by
  simp only [Exec.ev, Fin.getElem_fin]
  exact List.getElem_of_eq hx _

/-- A kept unit: in `A` (unchanged) or in `C` (moved). -/
theorem kept_ev (hx : x.evs = S.old.map Prod.fst) {a : Fin (S.exec x).n} {a0 : Fin x.n}
    (h : κ hx a = some a0) :
    (a.val < S.A.length ∧ a0.val = a.val ∧ (S.exec x).ev a = x.ev a0 ∧ ∃ u ∈ S.A, u.1 = x.ev a0) ∨
      (S.A.length + S.G.length ≤ a.val ∧ a0.val = a.val - S.G.length + S.F.length ∧
        (S.exec x).ev a = S.mv (x.ev a0) ∧ ∃ u ∈ S.C, u.1 = x.ev a0) := by
  have ha := lt_of_lt_of_eq a.2 n_new
  rcases S.κN_some (κ_some.mp h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine .inl ⟨h1, h2, ?_, ?_⟩
    · rw [ev_old hx, ev_eq, S.old_A (by omega)]
      simp only [h2]
      exact S.new_A h1 _
    · refine ⟨S.A[a.val], List.getElem_mem _, ?_⟩
      rw [ev_old hx, S.old_A (by omega)]; simp [h2]
  · refine .inr ⟨h1, h2, ?_, ?_⟩
    · rw [ev_old hx, S.old_C (by omega)]
      refine (S.new_C h1 _).trans ?_
      congr 3; omega
    · refine ⟨S.C[a.val - S.A.length - S.G.length]'(by omega), List.getElem_mem _, ?_⟩
      rw [ev_old hx, S.old_C (by omega)]
      congr 2; omega

/-- A block unit. -/
theorem block_ev {hx : x.evs = S.old.map Prod.fst} {b : Fin (S.exec x).n} (h : κ hx b = none) :
    ∃ k, ∃ hk : k < S.G.length, b.val = S.A.length + k ∧ (S.exec x).ev b = (S.G[k]).1 := by
  obtain ⟨h1, h2⟩ := κ_none.mp h
  refine ⟨b.val - S.A.length, by omega, by omega, ?_⟩
  rw [ev_eq]; exact S.new_G h1 h2 _

theorem same_kept (hx : x.evs = S.old.map Prod.fst) {a : Fin (S.exec x).n} {a0 : Fin x.n}
    (h : κ hx a = some a0) : Same ((S.exec x).ev a) (x.ev a0) := by
  rcases kept_ev hx h with ⟨-, -, he, -⟩ | ⟨-, -, he, -⟩
  · rw [he]; exact Same.refl _
  · rw [he]; exact S.same_mv _

theorem mv_tid (e : Ev) : (S.mv e).tid = e.tid := by unfold Surg.mv; split <;> rfl

theorem mv_pos (e : Ev) :
    (S.mv e).pos = if e.tid = S.i then e.pos + S.G.length - S.F.length else e.pos := by
  unfold Surg.mv; split <;> rfl

/-! ## Positions of kept units -/

variable {ib : Nat → Byte}

/-- The thread and position of a kept unit, old and new. -/
theorem kept_pos (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) {a : Fin (S.exec x).n}
    {a0 : Fin x.n} (h : κ hx a = some a0) :
    ((S.exec x).ev a).tid = (x.ev a0).tid ∧
      ((a.val < S.A.length ∧ ((S.exec x).ev a).pos = (x.ev a0).pos ∧
        ((x.ev a0).tid = S.i → (x.ev a0).pos < S.p1)) ∨
      (S.A.length + S.G.length ≤ a.val ∧ ((x.ev a0).tid = S.i →
        S.p1 + S.F.length ≤ (x.ev a0).pos ∧
        ((S.exec x).ev a).pos = (x.ev a0).pos + S.G.length - S.F.length) ∧
        ((x.ev a0).tid ≠ S.i → ((S.exec x).ev a).pos = (x.ev a0).pos))) := by
  rcases kept_ev hx h with ⟨h1, -, he, u, hu, hue⟩ | ⟨h1, -, he, u, hu, hue⟩
  · rw [he]
    exact ⟨rfl, .inl ⟨h1, rfl, fun ht => hue ▸ H.posA u hu (hue ▸ ht)⟩⟩
  · rw [he, mv_tid, mv_pos]
    refine ⟨rfl, .inr ⟨h1, fun ht => ⟨hue ▸ H.posC u hu (hue ▸ ht), by simp [ht]⟩,
      fun ht => by simp [ht]⟩⟩

/-- Kept units of one thread keep their position order. -/
theorem pos_rel (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) {a b : Fin (S.exec x).n}
    {a0 b0 : Fin x.n} (ha : κ hx a = some a0) (hb : κ hx b = some b0)
    (hab : (x.ev a0).tid = (x.ev b0).tid) :
    (((S.exec x).ev a).pos < ((S.exec x).ev b).pos ↔ (x.ev a0).pos < (x.ev b0).pos) ∧
      (((S.exec x).ev a).pos = ((S.exec x).ev b).pos ↔ (x.ev a0).pos = (x.ev b0).pos) := by
  obtain ⟨-, pa⟩ := kept_pos H hx ha
  obtain ⟨-, pb⟩ := kept_pos H hx hb
  by_cases hi : (x.ev b0).tid = S.i
  · have hi' : (x.ev a0).tid = S.i := hab ▸ hi
    rcases pa with ⟨-, pa1, pa2⟩ | ⟨-, pa1, -⟩ <;> rcases pb with ⟨-, pb1, pb2⟩ | ⟨-, pb1, -⟩
    · omega
    · have := pa2 hi'; have := pb1 hi; omega
    · have := pa1 hi'; have := pb2 hi; omega
    · have := pa1 hi'; have := pb1 hi; omega
  · have hi' : (x.ev a0).tid ≠ S.i := hab ▸ hi
    rcases pa with ⟨-, pa1, -⟩ | ⟨-, -, pa3⟩ <;> rcases pb with ⟨-, pb1, -⟩ | ⟨-, -, pb3⟩
    · omega
    · rw [pa1, pb3 hi]; omega
    · rw [pa3 hi', pb1]; omega
    · rw [pa3 hi', pb3 hi]; omega

theorem po_kept (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) {a b : Fin (S.exec x).n}
    {a0 b0 : Fin x.n} (ha : κ hx a = some a0) (hb : κ hx b = some b0) :
    (S.exec x).po a b = x.po a0 b0 := by
  have ta := (kept_pos H hx ha).1
  have tb := (kept_pos H hx hb).1
  rw [Bool.eq_iff_iff]
  simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ta, tb]
  constructor
  · rintro ⟨hab, hlt⟩; exact ⟨hab, ((pos_rel H hx ha hb hab).1).mp hlt⟩
  · rintro ⟨hab, hlt⟩; exact ⟨hab, ((pos_rel H hx ha hb hab).1).mpr hlt⟩

theorem sm_kept (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) {a b : Fin (S.exec x).n}
    {a0 b0 : Fin x.n} (ha : κ hx a = some a0) (hb : κ hx b = some b0) :
    (S.exec x).sm a b = x.sm a0 b0 := by
  have ta := (kept_pos H hx ha).1
  have tb := (kept_pos H hx hb).1
  rw [Bool.eq_iff_iff]
  simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq, ta, tb]
  constructor
  · rintro ⟨hab, hlt⟩; exact ⟨hab, ((pos_rel H hx ha hb hab).2).mp hlt⟩
  · rintro ⟨hab, hlt⟩; exact ⟨hab, ((pos_rel H hx ha hb hab).2).mpr hlt⟩

theorem ext_kept (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) {a b : Fin (S.exec x).n}
    {a0 b0 : Fin x.n} (ha : κ hx a = some a0) (hb : κ hx b = some b0) :
    (S.exec x).ext a b = x.ext a0 b0 := by
  simp only [Exec.ext, (kept_pos H hx ha).1, (kept_pos H hx hb).1]

theorem kept_mem (hx : x.evs = S.old.map Prod.fst) {a : Fin (S.exec x).n} {a0 : Fin x.n}
    (h : κ hx a = some a0) : ∃ u ∈ S.A ++ S.C, u.1 = x.ev a0 := by
  rcases kept_ev hx h with ⟨-, -, -, u, hu, he⟩ | ⟨-, -, -, u, hu, he⟩
  · exact ⟨u, List.mem_append_left _ hu, he⟩
  · exact ⟨u, List.mem_append_right _ hu, he⟩

/-- A kept memory unit touches no cell byte. -/
theorem off_kept (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) {a : Fin (S.exec x).n}
    {a0 : Fin x.n} (h : κ hx a = some a0) (hM : ((S.exec x).ev a).isM = true) {y : Nat}
    (hy : ((S.exec x).ev a).covers y = true) : S.cb y = false := by
  obtain ⟨u, hu, he⟩ := kept_mem hx h
  have hs := same_kept hx h
  exact H.offAC u hu (by rw [he, ← hs.isM]; exact hM) y (by rw [he, ← hs.covers]; exact hy)

/-- A block unit touches only cell bytes. -/
theorem on_block (H : S.Hyp ib) {hx : x.evs = S.old.map Prod.fst} {b : Fin (S.exec x).n}
    (h : κ hx b = none) {y : Nat} (hy : ((S.exec x).ev b).covers y = true) : S.cb y = true := by
  obtain ⟨k, hk, -, he⟩ := block_ev h
  rw [he] at hy
  exact H.onG _ (List.getElem_mem _) y hy

theorem block_mem (H : S.Hyp ib) {hx : x.evs = S.old.map Prod.fst} {b : Fin (S.exec x).n}
    (h : κ hx b = none) :
    (((S.exec x).ev b).isR = true ∨ ((S.exec x).ev b).isW = true) ∧
      ((S.exec x).ev b).locked = false ∧ ((S.exec x).ev b).ann = .wb := by
  obtain ⟨k, hk, -, he⟩ := block_ev h
  rw [he]
  obtain ⟨h1, h2, h3, -⟩ := H.memG _ (List.getElem_mem (h := hk))
  exact ⟨h1, h2, h3⟩

theorem block_isM (H : S.Hyp ib) {hx : x.evs = S.old.map Prod.fst} {b : Fin (S.exec x).n}
    (h : κ hx b = none) : ((S.exec x).ev b).isM = true := by
  rcases (block_mem H h).1 with h1 | h1
  · exact isM_of_R h1
  · exact isM_of_W h1

theorem isSome_of_ne {o : Option (Fin x.n)} (h : o ≠ none) : o.isSome = true := by
  cases o <;> simp_all

/-! ## Reads-from, coherence and from-reads of kept units -/

theorem rf_kept (hx : x.evs = S.old.map Prod.fst) {r : Fin (S.exec x).n} {r0 : Fin x.n}
    (h : κ hx r = some r0) (y : Nat) : (S.exec x).rf r.val y = (x.rf r0.val y).map S.σ := by
  rcases kept_ev hx h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · simp only [exec, h1, ite_true, h2]
  · simp only [exec, show ¬ r.val < S.A.length by omega,
      show ¬ r.val < S.A.length + S.G.length by omega, ite_false, h2]

theorem co_off (y : Nat) (hy : S.cb y = false) : (S.exec x).co y = (x.co y).map S.σ := by
  simp [exec, hy]

theorem σ_iff (hx : x.evs = S.old.map Prod.fst) {a : Fin (S.exec x).n} {a0 : Fin x.n}
    (h : κ hx a = some a0) (c : Nat) : S.σ c = a.val ↔ c = a0.val :=
  S.σ_eq_iff (by have := lt_of_lt_of_eq a.2 n_new; rw [S.length_new']; exact this)
    (κ_some.mp h) c

theorem map_σ_eq (hx : x.evs = S.old.map Prod.fst) {a : Fin (S.exec x).n} {a0 : Fin x.n}
    (h : κ hx a = some a0) (o : Option Nat) : (o.map S.σ == some a.val) = (o == some a0.val) := by
  cases o with
  | none => rfl
  | some c =>
    rw [Option.map_some]
    by_cases h1 : c = a0.val
    · subst h1; have := (σ_iff hx h a0.val).mpr rfl; simp [this]
    · have : S.σ c ≠ a.val := fun h' => h1 ((σ_iff hx h c).mp h')
      simp [this, h1]

theorem any_congr' {l : List Nat} {p q : Nat → Bool} (h : ∀ y ∈ l, p y = q y) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.any_cons]
    rw [h c List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem rfR_kept (hx : x.evs = S.old.map Prod.fst) {a b : Fin (S.exec x).n} {a0 b0 : Fin x.n}
    (ha : κ hx a = some a0) (hb : κ hx b = some b0) :
    (S.exec x).rfR a b = x.rfR a0 b0 := by
  have sa := same_kept hx ha
  have sb := same_kept hx hb
  simp only [Exec.rfR, sa.isW, sb.isR, sb.bytes, sa.covers]
  congr 1
  refine any_congr' fun y _ => ?_
  rw [rf_kept hx hb, map_σ_eq hx ha]

theorem coR_kept (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) {a b : Fin (S.exec x).n}
    {a0 b0 : Fin x.n} (ha : κ hx a = some a0) (hb : κ hx b = some b0) :
    (S.exec x).coR a b = x.coR a0 b0 := by
  have sa := same_kept hx ha
  have sb := same_kept hx hb
  by_cases hW : ((S.exec x).ev a).isW = true
  · simp only [Exec.coR, ← sa.isW, ← sb.isW, ← sa.bytes, ← sb.covers, hW, Bool.true_and]
    congr 1
    refine any_congr' fun y hy => ?_
    rw [co_off y (off_kept H hx ha (isM_of_W hW) (mem_bytes.mp hy)),
      before_map (σ_iff hx ha) (σ_iff hx hb)]
  · simp only [Exec.coR, ← sa.isW, Bool.not_eq_true] at hW ⊢
    simp [hW]

theorem frR_kept (H : S.Hyp ib) (hwf : x.Wf = true) (hx : x.evs = S.old.map Prod.fst)
    {a b : Fin (S.exec x).n} {a0 b0 : Fin x.n} (ha : κ hx a = some a0) (hb : κ hx b = some b0) :
    (S.exec x).frR a b = x.frR a0 b0 := by
  have sa := same_kept hx ha
  have sb := same_kept hx hb
  by_cases hR : ((S.exec x).ev a).isR = true
  · simp only [Exec.frR, ← sa.isR, ← sb.isW, ← sa.bytes, ← sb.covers, hR, Bool.true_and]
    congr 1
    refine any_congr' fun y hy => ?_
    have hy' := mem_bytes.mp hy
    rw [co_off y (off_kept H hx ha (isM_of_R hR) hy'), rf_kept hx ha]
    congr 1
    cases hr : x.rf a0.val y with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      have hR0 : (x.evs[a0.val]).isR = true := by rw [← ev_eq, ← sa.isR]; exact hR
      have hy0 : (x.evs[a0.val]).covers y = true := by rw [← ev_eq, ← sa.covers]; exact hy'
      obtain ⟨hv, hvW, hvC⟩ := wf_rf hwf a0.2 hR0 hy0 hr
      have hvF : ¬ (S.A.length ≤ v ∧ v < S.A.length + S.F.length) := by
        rintro ⟨h1, h2⟩
        have hcb := off_kept H hx ha (isM_of_R hR) hy'
        have hv' : v < (S.old.map Prod.fst).length := by rw [← hx]; exact hv
        have he : x.evs[v] = (S.old.map Prod.fst)[v] := List.getElem_of_eq hx _
        rw [he, S.old_F h1 h2] at hvW hvC
        have := H.onF _ (List.getElem_mem _) (isM_of_W hvW) y hvC
        rw [hcb] at this; cases this
      have hvo : v < S.old.length := by
        have := lt_of_lt_of_eq hv (n_old hx); rw [S.length_old']; exact this
      obtain ⟨h1, h2⟩ := S.σ_kept hvo hvF
      exact before_map (S.σ_eq_iff h1 h2) (σ_iff hx hb) _
  · simp only [Exec.frR, ← sa.isR, Bool.not_eq_true] at hR ⊢
    simp [hR]

/-! ## The embedding -/

theorem rmw_kept (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst)
    (hrmw : x.rmw = rmwPairs x.evs) (a b : Fin (S.exec x).n) (h : (S.exec x).rmwR a b = true) :
    ∃ a0 b0, κ hx a = some a0 ∧ κ hx b = some b0 ∧ x.rmwR a0 b0 = true := by
  simp only [Exec.rmwR, List.contains_iff_mem] at h
  obtain ⟨ha', hb', hR, hla, hW, hlb, ht, hp, haddr, hsz⟩ := mem_rmwPairs_iff.mp h
  change ((S.exec x).ev a).isR = true at hR
  change ((S.exec x).ev a).locked = true at hla
  change ((S.exec x).ev b).isW = true at hW
  change ((S.exec x).ev b).locked = true at hlb
  change ((S.exec x).ev a).tid = ((S.exec x).ev b).tid at ht
  change ((S.exec x).ev b).pos = ((S.exec x).ev a).pos + 1 at hp
  change ((S.exec x).ev a).addr = ((S.exec x).ev b).addr at haddr
  change ((S.exec x).ev a).size = ((S.exec x).ev b).size at hsz
  have hka : κ hx a ≠ none := by
    intro hn; rw [(block_mem H hn).2.1] at hla; cases hla
  have hkb : κ hx b ≠ none := by
    intro hn; rw [(block_mem H hn).2.1] at hlb; cases hlb
  obtain ⟨a0, ha0⟩ := Option.ne_none_iff_exists'.mp hka
  obtain ⟨b0, hb0⟩ := Option.ne_none_iff_exists'.mp hkb
  refine ⟨a0, b0, ha0, hb0, ?_⟩
  have sa := same_kept hx ha0
  have sb := same_kept hx hb0
  simp only [Exec.rmwR, List.contains_iff_mem, hrmw]
  refine mem_rmwPairs_iff.mpr ⟨a0.2, b0.2, ?_⟩
  obtain ⟨ta, pa⟩ := kept_pos H hx ha0
  obtain ⟨tb, pb⟩ := kept_pos H hx hb0
  have hab : (x.ev a0).tid = (x.ev b0).tid := by rw [← ta, ← tb]; exact ht
  refine ⟨show (x.ev a0).isR = true by rw [← sa.isR]; exact hR,
    show (x.ev a0).locked = true by rw [← Same.app (g := Ev.locked) (fun _ => rfl) sa]; exact hla,
    show (x.ev b0).isW = true by rw [← sb.isW]; exact hW,
    show (x.ev b0).locked = true by rw [← Same.app (g := Ev.locked) (fun _ => rfl) sb]; exact hlb,
    show (x.ev a0).tid = (x.ev b0).tid from hab,
    show (x.ev b0).pos = (x.ev a0).pos + 1 from ?_,
    show (x.ev a0).addr = (x.ev b0).addr by
      rw [← Same.app (g := Ev.addr) (fun _ => rfl) sa, ← Same.app (g := Ev.addr) (fun _ => rfl) sb]
      exact haddr,
    show (x.ev a0).size = (x.ev b0).size by
      rw [← Same.app (g := Ev.size) (fun _ => rfl) sa, ← Same.app (g := Ev.size) (fun _ => rfl) sb]
      exact hsz⟩
  by_cases hi : (x.ev b0).tid = S.i
  · have hi' : (x.ev a0).tid = S.i := hab ▸ hi
    rcases pa with ⟨-, pa1, pa2⟩ | ⟨-, pa1, -⟩ <;> rcases pb with ⟨-, pb1, pb2⟩ | ⟨hbC, pb1, -⟩
    · omega
    · exfalso
      obtain ⟨u, hu, hue⟩ := ((kept_ev hx hb0).resolve_left (fun h => by omega)).2.2.2
      have hW0 : (x.ev b0).isW = true := by rw [← sb.isW]; exact hW
      have hl0 : (x.ev b0).locked = true := by
        rw [← Same.app (g := Ev.locked) (fun _ => rfl) sb]; exact hlb
      have := H.lockC u hu (hue ▸ hi) (hue ▸ hW0) (hue ▸ hl0)
      rw [hue] at this
      have := pa2 hi'; have := (pb1 hi).2; omega
    · have := pa1 hi'; have := pb2 hi; omega
    · have := pa1 hi'; have := pb1 hi; omega
  · have hi' : (x.ev a0).tid ≠ S.i := hab ▸ hi
    rcases pa with ⟨-, pa1, -⟩ | ⟨-, -, pa3⟩ <;> rcases pb with ⟨-, pb1, -⟩ | ⟨-, -, pb3⟩
    · omega
    · rw [pa1, pb3 hi] at hp; exact hp
    · rw [pa3 hi', pb1] at hp; exact hp
    · rw [pa3 hi', pb3 hi] at hp; exact hp

theorem tear_kept (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) {a : Fin (S.exec x).n}
    {a0 : Fin x.n} (ha : κ hx a = some a0) (ht : x.tearable a0 = true) :
    (S.exec x).tearable a = true := by
  have sa := same_kept hx ha
  simp only [Exec.tearable, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at ht ⊢
  obtain ⟨hM, ht⟩ := ht
  refine ⟨by rw [sa.isM]; exact hM, ?_⟩
  rcases ht with ht | ⟨b0, -, ⟨hbM, hov⟩, hne⟩
  · exact .inl (by rw [sa.singleCopy]; exact ht)
  · right
    obtain ⟨u, hu, hue⟩ := kept_mem hx ha
    have hbF : ¬ (S.A.length ≤ b0.val ∧ b0.val < S.A.length + S.F.length) := by
      rintro ⟨h1, h2⟩
      have hb' : b0.val < (S.old.map Prod.fst).length := by rw [← hx]; exact b0.2
      have he : x.ev b0 = (S.F[b0.val - S.A.length]'(by omega)).1 := by
        rw [ev_old hx, S.old_F h1 h2]
      rw [he] at hbM hov
      have := H.ovF u hu _ (List.getElem_mem _) (hue ▸ hM) hbM
      rw [hue, hov] at this; cases this
    have hbo : b0.val < S.old.length := by
      have := lt_of_lt_of_eq b0.2 (n_old hx); rw [S.length_old']; exact this
    obtain ⟨h1, h2⟩ := S.σ_kept hbo hbF
    let b : Fin (S.exec x).n := ⟨S.σ b0.val, by
      have := h1; rw [S.length_new'] at this; exact lt_of_lt_of_eq this n_new.symm⟩
    have hb : κ hx b = some b0 := κ_some.mpr h2
    have sb := same_kept hx hb
    refine ⟨b, List.mem_finRange _, ⟨by rw [sb.isM]; exact hbM, by rw [Same.accOverlap sa sb]; exact hov⟩,
      ?_⟩
    simpa only [sa.accAddr, sb.accAddr, sa.accSize, sb.accSize] using hne

/-- **The kept units embed.** -/
theorem emb (H : S.Hyp ib) (hwf : x.Wf = true) (hx : x.evs = S.old.map Prod.fst)
    (hrmw : x.rmw = rmwPairs x.evs) : Emb x (S.exec x) (κ hx) where
  same _ _ h := same_kept hx h
  po _ _ _ _ ha hb := po_kept H hx ha hb
  sm _ _ _ _ ha hb := sm_kept H hx ha hb
  ext _ _ _ _ ha hb := ext_kept H hx ha hb
  rf _ _ _ _ ha hb := rfR_kept hx ha hb
  co _ _ _ _ ha hb := coR_kept H hx ha hb
  fr _ _ _ _ ha hb := frR_kept H hwf hx ha hb
  rmw a b h := rmw_kept H hx hrmw a b h
  fence f hf := isSome_of_ne fun hn => by rw [block_isM H hn] at hf; cases hf
  locked l hl := isSome_of_ne fun hn => by
    simp only [Ev.isA, (block_mem H hn).2.1, Bool.false_and] at hl; cases hl
  smK c b hb h := isSome_of_ne fun hn => by
    obtain ⟨k, hk, hc, he⟩ := block_ev hn
    obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp hb
    obtain ⟨tb, pb⟩ := kept_pos H hx hb0
    obtain ⟨tg, pg⟩ := H.posG k hk
    simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq, he, tb] at h
    obtain ⟨h1, h2⟩ := h
    have hi : (x.ev b0).tid = S.i := h1 ▸ tg
    rcases pb with ⟨-, pb1, pb2⟩ | ⟨-, pb1, -⟩
    · have := pb2 hi; omega
    · have := (pb1 hi).1; have := (pb1 hi).2; omega
  locK a c ha h := isSome_of_ne fun hn => by
    obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp ha
    simp only [Exec.loc, Bool.and_eq_true] at h
    obtain ⟨⟨hM, -⟩, hy⟩ := h
    obtain ⟨y, hy1, hy2⟩ := any_bytes.mp hy
    have := off_kept H hx ha0 hM hy1
    rw [on_block H hn hy2] at this; cases this
  tear _ _ ha ht := tear_kept H hx ha ht

end Surg

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
