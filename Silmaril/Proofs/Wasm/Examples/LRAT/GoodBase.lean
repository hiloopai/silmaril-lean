module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Mem

@[expose] public section

/-!
# The invariant: frame lemmas

Helpers for the preservation proofs of `Good` (`GoodInput`, `GoodHint`):

* `Same B B' lo hi`: the words of `B'` in `[lo, hi)` are those of `B`; it survives writes
  outside the range (`Same.wr`) and gives back the word lists (`Same.words`), the literal values
  (`Same.lit`), the clause tables (`Same.entryStart`, `Same.entryLen`) and the step's clause
  (`Same.bufWords`);
* stored clauses after such writes or a larger `cstart` (`EntryOk.congr`, `EntryOk.weaken`,
  `entries_of`, `entries_same`), and after recording a new clause (`entries_record`);
* the clause database `dbOf` and its models (`mem_dbOf`, `models_iff`, `SameDb`,
  `Models.congr`, `models_record`);
* assigning a literal and its negation (`wd_assign`, `Agrees.assign`, `stale_assign`);
* DIMACS: implications and models of the formula as the stream grows.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Logic.SAT

variable {B B' B'' : ByteArray}

/-! ## Words after a write -/

theorem wd_wr_of {p a : Nat} (v : BitVec 32) (hs : B.size = memSize) (hp : p + 4 ≤ memSize)
    (hd : p + 4 ≤ a ∨ a + 4 ≤ p) : wd (wr B p v) a = wd B a :=
  wd_wr_ne v (by rw [hs]; exact hp) hd

theorem wd_wr_self {p : Nat} (v : BitVec 32) (hs : B.size = memSize) (hp : p + 4 ≤ memSize) :
    wd (wr B p v) p = v :=
  wd_wr_same v (by rw [hs]; exact hp)

theorem size_wr_of {p : Nat} (v : BitVec 32) (hs : B.size = memSize) (hp : p + 4 ≤ memSize) :
    (wr B p v).size = memSize := by
  rw [size_wr v (by rw [hs]; exact hp), hs]

/-! ## Unchanged ranges -/

/-- The words of `B'` in `[lo, hi)` are those of `B`. -/
def Same (B B' : ByteArray) (lo hi : Nat) : Prop := ∀ a, lo ≤ a → a + 4 ≤ hi → wd B' a = wd B a

theorem Same.refl (lo hi : Nat) : Same B B lo hi := fun _ _ _ => rfl

theorem Same.trans {lo hi : Nat} (h : Same B B' lo hi) (h' : Same B' B'' lo hi) :
    Same B B'' lo hi :=
  fun a h1 h2 => (h' a h1 h2).trans (h a h1 h2)

theorem Same.mono {lo hi lo' hi' : Nat} (h : Same B B' lo hi) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    Same B B' lo' hi' :=
  fun a h1 h2 => h a (by omega) (by omega)

theorem Same.of_wr {lo hi p : Nat} (v : BitVec 32) (hs : B.size = memSize) (hp : p + 4 ≤ memSize)
    (hd : p + 4 ≤ lo ∨ hi ≤ p) : Same B (wr B p v) lo hi :=
  fun _ h1 h2 => wd_wr_of v hs hp (by omega)

theorem Same.words {lo hi p n : Nat} (h : Same B B' lo hi) (hlo : lo ≤ p) (hhi : p + 4 * n ≤ hi) :
    words B' p n = words B p n := by
  unfold LRAT.words
  exact List.map_congr_left fun k hk => h _ (by omega) (by have := List.mem_range.1 hk; omega)

theorem Same.lit {x : BitVec 32} (h : Same B B' 4 startBase) (hx : ValidLit x) :
    wd B' (litAddr x) = wd B (litAddr x) :=
  h _ hx.addr.1 hx.addr.2

theorem Same.stale {k : Nat} (h : Same B B' 4 startBase)
    (hst : ∀ x, ValidLit x → (wd B (litAddr x)).toNat ≤ k) :
    ∀ x, ValidLit x → (wd B' (litAddr x)).toNat ≤ k :=
  fun x hx => by rw [h.lit hx]; exact hst x hx

theorem Same.agrees {τ : Assignment} {S : BitVec 32} (h : Same B B' 4 startBase)
    (ha : Agrees τ B S) : Agrees τ B' S :=
  fun x hx => by rw [h.lit hx]; exact ha x hx

theorem Same.entryStart {hi id : Nat} (h : Same B B' startBase hi) (hhi : covBase ≤ hi)
    (hid : id < maxId) : entryStart B' id = entryStart B id := by
  unfold LRAT.entryStart
  rw [h _ (Nat.le_add_right _ _) (by simp only [covBase, maxId, startBase] at *; omega)]

theorem Same.entryLen {hi id : Nat} (h : Same B B' startBase hi) (hhi : covBase ≤ hi)
    (hid : id < maxId) : entryLen B' id = entryLen B id := by
  unfold LRAT.entryLen
  rw [h _ (by simp only [lenBase, startBase] at *; omega)
    (by simp only [covBase, maxId, lenBase] at *; omega)]

theorem Same.bufWords {G : List (BitVec 32)}
    (h : Same B B' (gv G gCstart).toNat (gv G gTop).toNat)
    (hct : (gv G gCstart).toNat ≤ (gv G gTop).toNat) : bufWords G B' = bufWords G B :=
  h.words le_rfl (by omega)

/-! ## Stored clauses -/

theorem EntryOk.congr {cs id : Nat} (h : EntryOk B cs id)
    (hs : entryStart B' id = entryStart B id) (hl : entryLen B' id = entryLen B id)
    (ha : Same B B' arenaBase cs) : EntryOk B' cs id ∧ entryWords B' id = entryWords B id := by
  have hw : entryWords B' id = entryWords B id := by
    unfold LRAT.entryWords
    rw [hs, hl]
    exact ha.words h.base_le (by have := h.end_le; omega)
  have hb := h.base_le
  have he := h.end_le
  have hd := h.dvd
  rw [← hs] at hb he
  rw [← hl] at he hd
  exact ⟨⟨hb, he, hd, hw ▸ h.valid⟩, hw⟩

theorem EntryOk.weaken {cs cs' id : Nat} (h : EntryOk B cs id) (hcs : cs ≤ cs') :
    EntryOk B cs' id :=
  ⟨h.base_le, by have := h.end_le; omega, h.dvd, h.valid⟩

/-- The stored clauses of `B'` are those of `B`, at the same places. -/
def SameDb (B B' : ByteArray) : Prop :=
  ∀ id < maxId, entryLen B' id = entryLen B id ∧ entryWords B' id = entryWords B id

theorem dbOf_congr (h : SameDb B B') : dbOf B' = dbOf B := by
  unfold LRAT.dbOf LRAT.entryClause
  have hf : (List.range maxId).filter (fun id => entryLen B' id != 0) =
      (List.range maxId).filter (fun id => entryLen B id != 0) :=
    List.filter_congr fun id hid => by rw [(h id (List.mem_range.1 hid)).1]
  rw [hf]
  exact List.map_congr_left fun id hid => by
    rw [(h id (List.mem_range.1 (List.mem_filter.1 hid).1)).2]

theorem Models.congr {τ : Assignment} (h : SameDb B B') (hm : Models τ B) : Models τ B' := by
  unfold LRAT.Models at *
  rw [dbOf_congr h]
  exact hm

theorem mem_dbOf {D : Clause} :
    D ∈ dbOf B ↔ ∃ id < maxId, entryLen B id ≠ 0 ∧ entryClause B id = D := by
  unfold LRAT.dbOf
  simp only [List.mem_map, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨id, ⟨hid, hl⟩, rfl⟩
    exact ⟨id, hid, hl, rfl⟩
  · rintro ⟨id, hid, hl, rfl⟩
    exact ⟨id, ⟨hid, hl⟩, rfl⟩

theorem models_iff {τ : Assignment} :
    Models τ B ↔ ∀ id < maxId, entryLen B id ≠ 0 → (entryClause B id).eval τ = true := by
  unfold LRAT.Models
  rw [CNF.eval_eq_true_iff]
  constructor
  · intro h id hid hl
    exact h _ (mem_dbOf.2 ⟨id, hid, hl, rfl⟩)
  · intro h D hD
    obtain ⟨id, hid, hl, rfl⟩ := mem_dbOf.1 hD
    exact h id hid hl

/-- A model of the database satisfies every stored clause. -/
theorem Models.entry {τ : Assignment} (h : Models τ B) {id : Nat} (hid : id < maxId)
    (hl : entryLen B id ≠ 0) : (entryClause B id).eval τ = true :=
  models_iff.1 h id hid hl

theorem SameDb.of_same {cs : Nat} (h : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id)
    (ht : Same B B' startBase covBase) (ha : Same B B' arenaBase cs) : SameDb B B' := by
  intro id hid
  have hl : entryLen B' id = entryLen B id := ht.entryLen le_rfl hid
  refine ⟨hl, ?_⟩
  by_cases h0 : entryLen B id = 0
  · unfold LRAT.entryWords
    rw [hl, h0]
    rfl
  · exact ((h id hid h0).congr (ht.entryStart le_rfl hid) hl ha).2

theorem entries_of {cs cs' : Nat}
    (h : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) (hcs : cs ≤ cs')
    (ht : ∀ id < maxId, entryLen B' id ≠ 0 →
      entryStart B' id = entryStart B id ∧ entryLen B' id = entryLen B id)
    (ha : Same B B' arenaBase cs) :
    ∀ id < maxId, entryLen B' id ≠ 0 → EntryOk B' cs' id := by
  intro id hid hl
  obtain ⟨hs, hl'⟩ := ht id hid hl
  exact ((h id hid (hl' ▸ hl)).congr hs hl' ha).1.weaken hcs

theorem entries_same {cs cs' : Nat}
    (h : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) (hcs : cs ≤ cs')
    (ht : Same B B' startBase covBase) (ha : Same B B' arenaBase cs) :
    ∀ id < maxId, entryLen B' id ≠ 0 → EntryOk B' cs' id :=
  entries_of h hcs (fun _ hid _ => ⟨ht.entryStart le_rfl hid, ht.entryLen le_rfl hid⟩) ha

/-- The table words of `sid` after recording a clause there. -/
theorem record_tables {c d : BitVec 32} {sid : Nat} (hs : B.size = memSize) (hsid : sid < maxId) :
    entryStart (wr (wr B (startBase + 4 * sid) c) (lenBase + 4 * sid) d) sid = c.toNat ∧
    entryLen (wr (wr B (startBase + 4 * sid) c) (lenBase + 4 * sid) d) sid = d.toNat := by
  have h1 : startBase + 4 * sid + 4 ≤ memSize := by
    simp only [startBase, memSize, maxId] at *; omega
  have h2 : lenBase + 4 * sid + 4 ≤ memSize := by
    simp only [lenBase, memSize, maxId] at *; omega
  have hs1 := size_wr_of (B := B) c hs h1
  unfold LRAT.entryStart LRAT.entryLen
  rw [wd_wr_of d hs1 h2 (by simp only [lenBase, startBase]; omega), wd_wr_self c hs h1,
    wd_wr_self d hs1 h2]
  exact ⟨rfl, rfl⟩

/-- The table words of other ids after recording a clause under `sid`. -/
theorem record_tables_ne {c d : BitVec 32} {sid id : Nat} (hs : B.size = memSize)
    (hsid : sid < maxId) (hid : id < maxId) (hne : id ≠ sid) :
    entryStart (wr (wr B (startBase + 4 * sid) c) (lenBase + 4 * sid) d) id = entryStart B id ∧
    entryLen (wr (wr B (startBase + 4 * sid) c) (lenBase + 4 * sid) d) id = entryLen B id := by
  have h1 : startBase + 4 * sid + 4 ≤ memSize := by
    simp only [startBase, memSize, maxId] at *; omega
  have h2 : lenBase + 4 * sid + 4 ≤ memSize := by
    simp only [lenBase, memSize, maxId] at *; omega
  have hs1 := size_wr_of (B := B) c hs h1
  unfold LRAT.entryStart LRAT.entryLen
  simp only [lenBase, startBase, maxId] at *
  rw [wd_wr_of d hs1 h2 (by omega), wd_wr_of c hs h1 (by omega), wd_wr_of d hs1 h2 (by omega),
    wd_wr_of c hs h1 (by omega)]
  exact ⟨rfl, rfl⟩

theorem Same.record {c d : BitVec 32} {sid : Nat} (hs : B.size = memSize) (hsid : sid < maxId) :
    Same B (wr (wr B (startBase + 4 * sid) c) (lenBase + 4 * sid) d) 4 startBase ∧
    Same B (wr (wr B (startBase + 4 * sid) c) (lenBase + 4 * sid) d) covBase memSize := by
  have h1 : startBase + 4 * sid + 4 ≤ memSize := by
    simp only [startBase, memSize, maxId] at *; omega
  have h2 : lenBase + 4 * sid + 4 ≤ memSize := by
    simp only [lenBase, memSize, maxId] at *; omega
  have hs1 := size_wr_of (B := B) c hs h1
  simp only [lenBase, startBase, maxId, covBase, memSize] at *
  exact ⟨(Same.of_wr c hs h1 (by omega)).trans (Same.of_wr d hs1 h2 (by omega)),
    (Same.of_wr c hs h1 (by omega)).trans (Same.of_wr d hs1 h2 (by omega))⟩

/-- The memory after recording the clause `[c, t)` under `sid`. -/
abbrev recordB (B : ByteArray) (sid c t : BitVec 32) : ByteArray :=
  wr (wr B (startBase + 4 * sid.toNat) c) (lenBase + 4 * sid.toNat) (t - c)

/-- Recording the clause `[c, t)` under `sid`, with `cstart` moving to `t`: the entries, and
the clause of `sid`. -/
theorem entries_record {c t sid : BitVec 32}
    (h : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B c.toNat id)
    (hs : B.size = memSize) (hb : arenaBase ≤ c.toNat) (hct : c.toNat ≤ t.toNat)
    (htm : t.toNat ≤ memSize) (hcd : 4 ∣ c.toNat) (htd : 4 ∣ t.toNat) (hsid : sid.toNat < maxId)
    (hv : ∀ w ∈ words B c.toNat ((t.toNat - c.toNat) / 4), ValidLit w) :
    (∀ id < maxId, entryLen (recordB B sid c t) id ≠ 0 → EntryOk (recordB B sid c t) t.toNat id) ∧
    entryWords (recordB B sid c t) sid.toNat = words B c.toNat ((t.toNat - c.toNat) / 4) := by
  have hsa := (Same.record (c := c) (d := t - c) hs hsid).2
  obtain ⟨h1, h2⟩ := record_tables (c := c) (d := t - c) hs hsid
  have hd : (t - c).toNat = t.toNat - c.toNat := by bv_omega
  have hw : entryWords (recordB B sid c t) sid.toNat = words B c.toNat ((t.toNat - c.toNat) / 4) := by
    unfold LRAT.entryWords
    rw [h1, h2, hd]
    exact (hsa.mono (by simp only [covBase, arenaBase] at *; omega) le_rfl).words hb (by omega)
  refine ⟨fun id hid hl => ?_, hw⟩
  by_cases he : id = sid.toNat
  · subst he
    rw [hd] at h2
    exact ⟨by rw [h1]; exact hb, by rw [h1, h2]; omega, by rw [h2]; omega, hw ▸ hv⟩
  · obtain ⟨h1', h2'⟩ := record_tables_ne (c := c) (d := t - c) hs hsid hid he
    exact ((h id hid (h2' ▸ hl)).congr h1' h2'
      (hsa.mono (by simp only [covBase, arenaBase]; omega) (by omega))).1.weaken hct

/-- A model of the database satisfying the recorded clause is a model after recording it. -/
theorem models_record {c t sid : BitVec 32} {τ : Assignment}
    (h : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B c.toNat id)
    (hs : B.size = memSize) (hsid : sid.toNat < maxId) (hcm : c.toNat ≤ memSize)
    (hm : Models τ B) (hC : Clause.eval τ (toClause (entryWords (recordB B sid c t) sid.toNat)) = true) :
    Models τ (recordB B sid c t) := by
  have hsa := (Same.record (c := c) (d := t - c) hs hsid).2
  refine models_iff.2 fun id hid hl => ?_
  by_cases he : id = sid.toNat
  · subst he
    exact hC
  · obtain ⟨h1', h2'⟩ := record_tables_ne (c := c) (d := t - c) hs hsid hid he
    have hl' : entryLen B id ≠ 0 := h2' ▸ hl
    have hw := ((h id hid hl').congr h1' h2'
      (hsa.mono (by simp only [covBase, arenaBase]; omega) hcm)).2
    unfold LRAT.entryClause
    rw [hw]
    exact hm.entry hid hl'

/-! ## Assigning a literal -/

theorem wd_assign {l y a b : BitVec 32} (hs : B.size = memSize) (hl : ValidLit l)
    (hy : ValidLit y) :
    wd (wr (wr B (litAddr l) a) (negAddr l) b) (litAddr y) =
      if y = -l then b else if y = l then a else wd B (litAddr y) := by
  have hla := hl.addr
  have hna := hl.neg.addr
  have hm1 : litAddr l + 4 ≤ memSize := by simp only [startBase, memSize] at hla ⊢; omega
  have hm : litAddr (-l) + 4 ≤ memSize := by simp only [startBase, memSize] at hna ⊢; omega
  have hs1 := size_wr_of (B := B) a hs hm1
  rw [negAddr_eq]
  by_cases h1 : y = -l
  · subst h1
    rw [ite_eq_left rfl, wd_wr_self b hs1 hm]
  · by_cases h2 : y = l
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl, wd_wr_of b hs1 hm (hl.neg.disj hl (Ne.symm h1)),
        wd_wr_self a hs hm1]
    · rw [ite_eq_right h1, ite_eq_right h2, wd_wr_of b hs1 hm (hl.neg.disj hy (Ne.symm h1)),
        wd_wr_of a hs hm1 (hl.disj hy (Ne.symm h2))]

theorem stale_assign {l a b : BitVec 32} {k : Nat} (hs : B.size = memSize) (hl : ValidLit l)
    (hst : ∀ x, ValidLit x → (wd B (litAddr x)).toNat ≤ k) (ha : a.toNat ≤ k) (hb : b.toNat ≤ k) :
    ∀ x, ValidLit x → (wd (wr (wr B (litAddr l) a) (negAddr l) b) (litAddr x)).toNat ≤ k := by
  intro x hx
  rw [wd_assign hs hl hx]
  split
  · exact hb
  · split
    · exact ha
    · exact hst x hx

theorem stamp_ne (S : BitVec 32) : S * 2#32 ≠ S * 2#32 + 1#32 := by bv_omega

/-- Assigning `l` (value `a`) and `-l` (value `b`) consistently with `τ`. -/
theorem Agrees.assign {τ : Assignment} {S l a b : BitVec 32} (h : Agrees τ B S)
    (hs : B.size = memSize) (hl : ValidLit l)
    (ha : a = S * 2#32 → Lit.eval τ l.toInt = false)
    (ha' : a = S * 2#32 + 1#32 → Lit.eval τ l.toInt = true)
    (hb : b = S * 2#32 → Lit.eval τ l.toInt = true)
    (hb' : b = S * 2#32 + 1#32 → Lit.eval τ l.toInt = false) :
    Agrees τ (wr (wr B (litAddr l) a) (negAddr l) b) S := by
  intro y hy
  rw [wd_assign hs hl hy]
  by_cases h1 : y = -l
  · subst h1
    rw [ite_eq_left rfl, hl.eval_neg τ]
    exact ⟨fun e => by rw [hb e]; rfl, fun e => by rw [hb' e]; rfl⟩
  · by_cases h2 : y = l
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl]
      exact ⟨ha, ha'⟩
    · rw [ite_eq_right h1, ite_eq_right h2]
      exact h y hy

/-! ## DIMACS -/

theorem cnf_implies_append {xs ys : List Int} {C : Clause} (h : (Dimacs.cnf xs).Implies C) :
    (Dimacs.cnf (xs ++ ys)).Implies C := by
  obtain ⟨G, hG⟩ := Dimacs.cnf_append xs ys
  rw [hG]
  exact h.append G

theorem cnf_eval_append {xs ys : List Int} {τ : Assignment}
    (h : (Dimacs.cnf (xs ++ ys)).eval τ = true) : (Dimacs.cnf xs).eval τ = true := by
  obtain ⟨G, hG⟩ := Dimacs.cnf_append xs ys
  rw [hG] at h
  exact CNF.eval_of_append h

theorem cnf_sat_append {xs ys : List Int} (h : (Dimacs.cnf (xs ++ ys)).Sat) :
    (Dimacs.cnf xs).Sat := by
  obtain ⟨τ, hτ⟩ := h
  exact ⟨τ, cnf_eval_append hτ⟩

/-- The empty step clause. -/
theorem bufWords_nil {m t S cf sid u n : BitVec 32} :
    bufWords [m, t, t, S, cf, sid, u, n] B = [] := by
  show LRAT.words B t.toNat ((t.toNat - t.toNat) / 4) = []
  rw [Nat.sub_self, Nat.zero_div]
  rfl

theorem cnf_unsat_append {xs ys : List Int} (h : (Dimacs.cnf xs).Unsat) :
    (Dimacs.cnf (xs ++ ys)).Unsat := by
  obtain ⟨G, hG⟩ := Dimacs.cnf_append xs ys
  rw [hG]
  exact h.append G

/-- After a `0`, the input clause is empty. -/
theorem input_nil {xs : List Int} {m t S cf sid u n : BitVec 32} :
    (∀ w ∈ bufWords [m, t, t, S, cf, sid, u, n] B, ValidLit w) ∧
      toClause (bufWords [m, t, t, S, cf, sid, u, n] B) = Dimacs.pending (xs ++ [0]) := by
  rw [bufWords_nil, Dimacs.pending_snoc_zero]
  exact ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩

/-- Appending the word at `top` to the clause `[c, t)`. -/
theorem words_snoc {c t : BitVec 32} {x : BitVec 32} (hs : Same B B' c.toNat t.toNat)
    (hct : c.toNat ≤ t.toNat) (hcd : 4 ∣ c.toNat) (htd : 4 ∣ t.toNat) (hx : wd B' t.toNat = x)
    (ht : t.toNat + 4 < 2 ^ 32) :
    words B' c.toNat (((t + 4#32).toNat - c.toNat) / 4) =
      words B c.toNat ((t.toNat - c.toNat) / 4) ++ [x] := by
  have htt : (t + 4#32).toNat = t.toNat + 4 := by bv_omega
  have hk : ((t + 4#32).toNat - c.toNat) / 4 = (t.toNat - c.toNat) / 4 + 1 := by omega
  rw [hk, words_succ, hs.words le_rfl (by omega),
    show c.toNat + 4 * ((t.toNat - c.toNat) / 4) = t.toNat by omega, hx]

theorem size_assign {l a b : BitVec 32} (hs : B.size = memSize) (hl : ValidLit l) :
    (wr (wr B (litAddr l) a) (negAddr l) b).size = memSize := by
  have hla := hl.addr
  have hna := hl.neg.addr
  rw [negAddr_eq]
  exact size_wr_of b (size_wr_of a hs (by simp only [startBase, memSize] at hla ⊢; omega))
    (by simp only [startBase, memSize] at hna ⊢; omega)

/-- Assigning a literal leaves everything from `startBase` on unchanged. -/
theorem Same.assign {l a b : BitVec 32} (hs : B.size = memSize) (hl : ValidLit l) :
    Same B (wr (wr B (litAddr l) a) (negAddr l) b) startBase memSize := by
  have hla := hl.addr
  have hna := hl.neg.addr
  have hm1 : litAddr l + 4 ≤ memSize := by simp only [startBase, memSize] at hla ⊢; omega
  have hm : litAddr (-l) + 4 ≤ memSize := by simp only [startBase, memSize] at hna ⊢; omega
  rw [negAddr_eq]
  exact (Same.of_wr a hs hm1 (Or.inl hla.2)).trans
    (Same.of_wr b (size_wr_of a hs hm1) hm (Or.inl hna.2))

/-! ## Writes to the literal values only -/

/-- `B'` differs from `B` at most below `startBase` (the literal values): the tables, the RAT
words and the arena are unchanged. -/
structure HiSame (B B' : ByteArray) : Prop where
  size : B.size = memSize
  size' : B'.size = memSize
  same : Same B B' startBase memSize

theorem HiSame.wd (h : HiSame B B') {a : Nat} (ha : startBase ≤ a) : LRAT.wd B' a = LRAT.wd B a := by
  by_cases hb : a + 4 ≤ memSize
  · exact h.same a ha hb
  · have h1 : B.size < a + 4 := by rw [h.size]; omega
    have h2 : B'.size < a + 4 := by rw [h.size']; omega
    rw [LRAT.wd, LRAT.wd, Silmaril.Wasm.Logic.Core.load_eq_none h1,
      Silmaril.Wasm.Logic.Core.load_eq_none h2]

theorem HiSame.trans (h : HiSame B B') (h' : HiSame B' B'') : HiSame B B'' :=
  ⟨h.size, h'.size', h.same.trans h'.same⟩

theorem HiSame.refl (hs : B.size = memSize) : HiSame B B := ⟨hs, hs, Same.refl _ _⟩

theorem HiSame.words (h : HiSame B B') {p n : Nat} (hp : startBase ≤ p) :
    words B' p n = words B p n := by
  unfold LRAT.words
  exact List.map_congr_left fun k _ => h.wd (by omega)

theorem HiSame.sameDb (h : HiSame B B') {cs : Nat}
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) : SameDb B B' := by
  intro id hid
  have hl : entryLen B' id = entryLen B id := by
    unfold LRAT.entryLen; rw [h.wd (by simp only [lenBase, startBase]; omega)]
  have hst : entryStart B' id = entryStart B id := by
    unfold LRAT.entryStart; rw [h.wd (by simp only [startBase]; omega)]
  refine ⟨hl, ?_⟩
  by_cases h0 : entryLen B id = 0
  · unfold LRAT.entryWords; rw [hl, h0]; rfl
  · have hb := (hent id hid h0).base_le
    unfold LRAT.entryWords
    rw [hl, hst]
    exact h.words (by simp only [arenaBase, startBase] at *; omega)

theorem HiSame.models (h : HiSame B B') {cs : Nat}
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) {τ : Assignment} :
    Models τ B' ↔ Models τ B := by
  unfold LRAT.Models
  rw [dbOf_congr (h.sameDb hent)]

theorem HiSame.entries (h : HiSame B B') {cs : Nat}
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) :
    ∀ id < maxId, entryLen B' id ≠ 0 → EntryOk B' cs id := by
  intro id hid hl
  have hs := h.sameDb hent id hid
  have he := hent id hid (hs.1 ▸ hl)
  have hst : entryStart B' id = entryStart B id := by
    unfold LRAT.entryStart; rw [h.wd (by simp only [startBase]; omega)]
  refine ⟨hst ▸ he.base_le, by rw [hst, hs.1]; exact he.end_le, hs.1 ▸ he.dvd, ?_⟩
  rw [hs.2]; exact he.valid

/-- Everything the step depends on except the literal values. -/
theorem HiSame.step (h : HiSame B B') {G : List (BitVec 32)} {cs : Nat}
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id)
    (hbase : startBase ≤ (gv G gCstart).toNat) (hc : candOf B ≠ 0 → candOf B - 1 < maxId) :
    bufWords G B' = bufWords G B ∧ candOf B' = candOf B ∧ tagOf B' = tagOf B ∧
      (∀ id, covOf B' id = covOf B id) ∧ targetOf G B' = targetOf G B ∧
      ∀ id < maxId, resolventOf G B' id = resolventOf G B id := by
  have hbuf : bufWords G B' = bufWords G B := h.words hbase
  have hcand : candOf B' = candOf B := by
    unfold candOf; rw [h.wd (by simp only [candAddr, startBase]; omega)]
  have hpiv : pivotOf G B' = pivotOf G B := h.wd hbase
  have hres : ∀ id < maxId, resolventOf G B' id = resolventOf G B id := by
    intro id hid
    unfold resolventOf resPart LRAT.entryClause
    rw [hbuf, hpiv, (h.sameDb hent id hid).2]
  refine ⟨hbuf, hcand, ?_, fun id => ?_, ?_, hres⟩
  · unfold tagOf; rw [h.wd (by simp only [tagAddr, startBase]; omega)]
  · unfold covOf; rw [h.wd (by simp only [covBase, startBase]; omega)]
  · unfold targetOf
    rw [hcand, hbuf]
    by_cases h0 : candOf B = 0
    · simp only [h0, ite_true]
    · simp only [h0, ite_false]
      exact hres _ (hc h0)

/-- A step after writes to the literal values only, given the new agreement. -/
theorem StepOk.hiSame {G : List (BitVec 32)} {cs : Nat} (st : StepOk G B) (h : HiSame B B')
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id)
    (hbase : startBase ≤ (gv G gCstart).toNat)
    (hag : ∀ τ, Models τ B → Clause.eval τ (targetOf G B) = false → Agrees τ B' (gv G gStamp)) :
    StepOk G B' := by
  obtain ⟨hbuf, hcand, htag, hcov, htgt, hres⟩ := h.step hent hbase fun hc => (st.cand hc).1
  have hm : ∀ τ, Models τ B' ↔ Models τ B := fun τ => h.models hent
  have hl : ∀ id < maxId, entryLen B' id = entryLen B id := fun id hid => (h.sameDb hent id hid).1
  refine ⟨st.id_lt, hbuf ▸ st.valid, fun hc => ?_, fun hc τ hτ => ?_, fun τ hτ hf => ?_,
    fun id hid hc => ?_⟩
  · rw [hcand] at hc ⊢
    obtain ⟨h1, h2, h3⟩ := st.cand hc
    exact ⟨h1, by rw [hl _ h1]; exact h2, h3⟩
  · rw [htgt]; exact st.confl hc τ ((hm τ).1 hτ)
  · rw [htgt] at hf; exact hag τ ((hm τ).1 hτ) hf
  · rw [hcov, htag] at hc
    obtain ⟨h1, h2, h3⟩ := st.cov id hid hc
    exact ⟨by rw [hl id hid]; exact h1, h2, fun τ hτ => by
      rw [hres id hid]; exact h3 τ ((hm τ).1 hτ)⟩

theorem HiSame.assign {l a b : BitVec 32} (hs : B.size = memSize) (hl : ValidLit l) :
    HiSame B (wr (wr B (litAddr l) a) (negAddr l) b) :=
  ⟨hs, size_assign hs hl, Same.assign hs hl⟩

/-- The bounds of `Good` on the explicit globals. -/
theorem Good.facts {xs : List Int} {m t c S cf sid u n : BitVec 32}
    (hG : Good xs [m, t, c, S, cf, sid, u, n] B) :
    B.size = memSize ∧ arenaBase ≤ c.toNat ∧ c.toNat ≤ t.toNat ∧ t.toNat ≤ memSize ∧
      4 ∣ c.toNat ∧ 4 ∣ t.toNat ∧ S.toNat ≤ maxStamp :=
  ⟨hG.size, hG.base_le, hG.cstart_le, hG.top_le, hG.cstart_dvd, hG.top_dvd, hG.stamp_le⟩

end Silmaril.Wasm.Examples.LRAT
