module

public import Silmaril.Elf.Lookup.Defs

/-! # On a well-formed GNU hash table, ld.so's hash walk is the declarative lookup

`gnuLookup_eq_scanLookup : A.GnuHashOk → A.gnuLookup r plt = A.scanLookup r plt`.

The argument: every `.dynsym` entry whose name is not the reference's is rejected by
`check_match` (`checkMatch_of_ne`); every entry whose name is the reference's has the
reference's hash, so (by `GnuHash.wf`, through `symFacts`) it lies in the run that starts at the
reference's bucket, its chain value passes the hash test, and the Bloom filter answers yes. So
the walk over that run (`chainWalk_eq`) and the scan over all hashed symbols see the same
accepting entries in the same order.
-/

public section

namespace Silmaril.Elf

open Silmaril.Formats.ELF (NameBytes ObjectSymbol)

/-! ## `firstMatch` -/

theorem firstMatch_cons (p : Nat → Option Bool) (i : Nat) (is : List Nat) :
    firstMatch p (i :: is) = (p i).bind fun b => if b then some (some i) else firstMatch p is := by
  simp only [firstMatch]
  cases p i with
  | none => rfl
  | some b => cases b <;> rfl

theorem firstMatch_allFalse {p : Nat → Option Bool} :
    ∀ {l : List Nat}, (∀ i ∈ l, p i = some false) → firstMatch p l = some none
  | [], _ => rfl
  | i :: is, h => by
    rw [firstMatch_cons, h i (by simp)]
    exact firstMatch_allFalse fun j hj => h j (by simp [hj])

theorem firstMatch_append_false {p : Nat → Option Bool} :
    ∀ {l₁ : List Nat} (l₂ : List Nat), (∀ i ∈ l₁, p i = some false) →
      firstMatch p (l₁ ++ l₂) = firstMatch p l₂
  | [], _, _ => rfl
  | i :: is, l₂, h => by
    rw [List.cons_append, firstMatch_cons, h i (by simp)]
    exact firstMatch_append_false l₂ fun j hj => h j (by simp [hj])

/-! ## `check_match` rejects other names -/

theorem checkMatch_of_ne {A : File} {r : Ref} {plt : Bool} {i : Nat} {s : ObjectSymbol}
    (hs : A.dynsyms[i]? = some s) (hn : s.name ≠ r.name) : A.checkMatch r plt i = some false := by
  simp [File.checkMatch, hs, hn]

/-! ## What `GnuHash.wf` says about each hashed symbol -/

/-- The facts the walk needs about hashed symbol `k` (named `n`), in chain `c`. -/
def SymFacts (g : GnuHash) (k : Nat) (n : NameBytes) : Prop :=
  ∃ hv, g.chain[k - g.symoffset]? = some hv ∧ hv >>> 1 = gnuHashOf n >>> 1 ∧
    g.bloomYes (gnuHashOf n) = true ∧
    ∃ b, g.buckets[gnuHashOf n % g.nbuckets]? = some b ∧ g.symoffset ≤ b ∧ b ≤ k ∧
      ∀ j, b ≤ j → j < k → ∃ hj, g.chain[j - g.symoffset]? = some hj ∧ hj % 2 = 0

theorem runsOk_facts (g : GnuHash) (syms : List ObjectSymbol) :
    ∀ (ss : List ObjectSymbol) (cs : List Nat) (st i : Nat),
      g.symoffset ≤ st → st ≤ i →
      (∀ t, ss[t]? = syms[i + t]?) → (∀ t, cs[t]? = g.chain[i - g.symoffset + t]?) →
      ss.length = cs.length →
      (∀ j, st ≤ j → j < i → ∃ hj, g.chain[j - g.symoffset]? = some hj ∧ hj % 2 = 0) →
      g.runsOk st i ss cs = true →
      ∀ k s, i ≤ k → syms[k]? = some s → SymFacts g k s.name
  | [], _, st, i, _, _, hss, _, _, _, _, k, s, hk, hs => by
    have := hss (k - i)
    rw [Nat.add_sub_cancel' hk, hs] at this
    simp at this
  | _ :: _, [], _, _, _, _, _, _, hlen, _, _, _, _, _, _ => by simp at hlen
  | s0 :: ss, hv :: cs, st, i, hso, hst, hss, hcs, hlen, hinv, hok, k, s, hk, hs => by
    simp only [GnuHash.runsOk, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hhash, hbucket⟩, hbloom⟩, hrest⟩ := hok
    have hs0 : syms[i]? = some s0 := by have := hss 0; simpa using this.symm
    have hhv : g.chain[i - g.symoffset]? = some hv := by have := hcs 0; simpa using this.symm
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · rw [hs0] at hs; cases hs
      exact ⟨hv, hhv, hhash, hbloom, st, hbucket, hso, hst, hinv⟩
    · refine runsOk_facts g syms ss cs (if hv % 2 = 1 then i + 1 else st) (i + 1) ?_ ?_ ?_ ?_
        (by simpa using hlen) ?_ hrest k s hlt hs
      · split <;> omega
      · split <;> omega
      · intro t; have := hss (t + 1); simpa [Nat.add_assoc, Nat.add_comm 1 t] using this
      · intro t; have := hcs (t + 1)
        have e : i + 1 - g.symoffset + t = i - g.symoffset + (t + 1) := by omega
        simpa [e] using this
      · intro j hj1 hj2
        split at hj1
        · omega
        · rcases Nat.lt_or_ge j i with h | h
          · exact hinv j hj1 h
          · have : j = i := by omega
            subst this
            refine ⟨hv, hhv, ?_⟩
            rename_i hodd
            simpa using hodd

/-- The facts `GnuHash.wf` gives about a file's hash table. -/
structure WfFacts (g : GnuHash) (syms : List ObjectSymbol) : Prop where
  so_pos : 0 < g.symoffset
  nb_pos : 0 < g.nbuckets
  bloom_pos : 0 < g.bloom.length
  buckets_len : g.buckets.length = g.nbuckets
  chain_len : g.symoffset + g.chain.length = syms.length
  buckets_ok : ∀ b ∈ g.buckets, b = 0 ∨ (g.symoffset ≤ b ∧ b < syms.length)
  last_odd : ∀ hv, g.chain.getLast? = some hv → hv % 2 = 1
  sym : ∀ k s, g.symoffset ≤ k → syms[k]? = some s → SymFacts g k s.name

theorem wfFacts {g : GnuHash} {syms : List ObjectSymbol} (h : g.wf syms = true) :
    WfFacts g syms := by
  simp only [GnuHash.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun b hb => ?_, fun hv hl => ?_, fun k s hk hs => ?_⟩
  · rcases h6 b hb with h | h
    · exact .inl (by simpa using h)
    · exact .inr (by simpa using h)
  · rw [hl] at h7; simpa using h7
  · refine runsOk_facts g syms _ _ g.symoffset g.symoffset (Nat.le_refl _) (Nat.le_refl _)
      (fun t => by simp [List.getElem?_drop]) (fun t => by simp) (by simp; omega)
      (fun j h1 h2 => by omega) h8 k s hk hs

/-! ## The walk over one run -/

section Walk

variable (A : File) (g : GnuHash) (r : Ref) (plt : Bool)

theorem hash_test {hv n : Nat} (h : hv >>> 1 = n >>> 1) : (hv ^^^ n) >>> 1 = 0 := by
  rw [Nat.shiftRight_xor_distrib, h, Nat.xor_self]

theorem chainWalk_eq (W : WfFacts g A.dynsyms) :
    ∀ n j fuel, A.dynsyms.length - j = n → g.symoffset ≤ j → j < A.dynsyms.length → n ≤ fuel →
      (∀ i s, j ≤ i → A.dynsyms[i]? = some s → s.name = r.name →
        ∀ j', j ≤ j' → j' < i → ∃ hj, g.chain[j' - g.symoffset]? = some hj ∧ hj % 2 = 0) →
      A.chainWalk g r plt (gnuHashOf r.name) fuel j =
        firstMatch (A.checkMatch r plt) (List.range' j n)
  | 0, j, _, hn, _, hj, _, _ => by omega
  | n + 1, j, 0, _, _, _, hf, _ => by omega
  | n + 1, j, fuel + 1, hn, hso, hj, hf, hpre => by
    obtain ⟨s, hs⟩ : ∃ s, A.dynsyms[j]? = some s := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨hv, hhv⟩ : ∃ hv, g.chain[j - g.symoffset]? = some hv :=
      ⟨_, List.getElem?_eq_getElem (by have := W.chain_len; omega)⟩
    -- the continuation after a rejected entry
    have hcont : (if hv % 2 = 1 then some none
        else A.chainWalk g r plt (gnuHashOf r.name) fuel (j + 1)) =
        firstMatch (A.checkMatch r plt) (List.range' (j + 1) n) := by
      split
      · rename_i hodd
        symm
        apply firstMatch_allFalse
        intro i hi
        simp only [List.mem_range'_1] at hi
        obtain ⟨si, hsi⟩ : ∃ s, A.dynsyms[i]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        refine checkMatch_of_ne hsi fun he => ?_
        obtain ⟨hj', hj'1, hj'2⟩ := hpre i si (by omega) hsi he j (Nat.le_refl _) (by omega)
        rw [hhv] at hj'1; cases hj'1; omega
      · rename_i heven
        have hj1 : j + 1 < A.dynsyms.length := by
          rcases Nat.lt_or_ge (j + 1) A.dynsyms.length with h | h
          · exact h
          · exfalso
            have hlast : g.chain.getLast? = some hv := by
              rw [List.getLast?_eq_getElem?]
              have : g.chain.length - 1 = j - g.symoffset := by have := W.chain_len; omega
              rw [this, hhv]
            exact heven (W.last_odd hv hlast)
        exact chainWalk_eq W n (j + 1) fuel (by omega) (by omega) hj1 (by omega)
          fun i s hj hs he j' h1 h2 => hpre i s (by omega) hs he j' (by omega) h2
    rw [List.range'_succ, firstMatch_cons, ← hcont]
    by_cases hname : s.name = r.name
    · obtain ⟨hv', hhv', hh, -⟩ := W.sym j s hso hs
      rw [hhv] at hhv'; cases hhv'
      rw [hname] at hh
      have ht := hash_test hh
      simp only [File.chainWalk, hhv]
      cases A.checkMatch r plt j with
      | none => simp [ht]
      | some b => cases b <;> simp [ht]
    · have hf := checkMatch_of_ne (plt := plt) hs hname
      simp [File.chainWalk, hhv, hf]

end Walk

/-! ## The theorem -/

theorem gnuLookup_eq_scanLookup {A : File} (hok : A.GnuHashOk) (r : Ref) (plt : Bool) :
    A.gnuLookup r plt = A.scanLookup r plt := by
  obtain ⟨g, hg, hw⟩ := hok
  have W := wfFacts hw
  have hlen := W.chain_len
  -- the scan
  have hscan : A.scanLookup r plt =
      firstMatch (A.checkMatch r plt)
        (List.range' g.symoffset (A.dynsyms.length - g.symoffset)) := by
    simp [File.scanLookup, hg]
  rw [hscan]
  -- is there a hashed symbol with the reference's name?
  by_cases hex : ∃ i s, g.symoffset ≤ i ∧ A.dynsyms[i]? = some s ∧ s.name = r.name
  · obtain ⟨i, s, hi, hs, hn⟩ := hex
    obtain ⟨hv, -, -, hbloom, b, hb, hbso, hbi, -⟩ := W.sym i s hi hs
    rw [hn] at hbloom hb
    have hilt : i < A.dynsyms.length := (List.getElem?_eq_some_iff.mp hs).1
    -- every symbol named like the reference lies in the run of bucket `b`
    have hrun : ∀ i' s', A.dynsyms[i']? = some s' → s'.name = r.name → g.symoffset ≤ i' →
        b ≤ i' ∧ ∀ j', b ≤ j' → j' < i' →
          ∃ hj, g.chain[j' - g.symoffset]? = some hj ∧ hj % 2 = 0 := by
      intro i' s' hs' hn' hi'
      obtain ⟨_, -, -, -, b', hb', -, hb'i, hev⟩ := W.sym i' s' hi' hs'
      rw [hn', hb] at hb'; cases hb'
      exact ⟨hb'i, hev⟩
    have hwalk := chainWalk_eq A g r plt W (A.dynsyms.length - b) b (A.dynsyms.length + 1) rfl
      hbso (by omega) (by omega) fun i' s' h1 hs' hn' => (hrun i' s' hs' hn' (by omega)).2
    have hsplit : List.range' g.symoffset (A.dynsyms.length - g.symoffset) =
        List.range' g.symoffset (b - g.symoffset) ++ List.range' b (A.dynsyms.length - b) := by
      have := List.range'_append_1 (s := g.symoffset) (m := b - g.symoffset)
        (n := A.dynsyms.length - b)
      rw [Nat.add_sub_cancel' hbso] at this
      rw [this]; congr 1; omega
    rw [hsplit, firstMatch_append_false]
    · rw [← hwalk]
      have hwi : (gnuHashOf r.name / 64) &&& (g.bloom.length - 1) < g.bloom.length :=
        Nat.lt_of_le_of_lt Nat.and_le_right (by have := W.bloom_pos; omega)
      obtain ⟨w, hw'⟩ : ∃ w, g.bloom[(gnuHashOf r.name / 64) &&& (g.bloom.length - 1)]? = some w :=
        ⟨_, List.getElem?_eq_getElem hwi⟩
      simp only [GnuHash.bloomYes, hw', beq_iff_eq] at hbloom
      have hB : ¬ ((w >>> (gnuHashOf r.name % 64)) &&& (w >>> ((gnuHashOf r.name >>> g.bloomShift) % 64))
          &&& 1 = 0) := by rw [hbloom]; decide
      simp only [Nat.and_one_is_mod] at hB
      have hb0 : b ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le W.so_pos hbso)
      simp [File.gnuLookup, hg, W.nb_pos, W.bloom_pos, hw', hb, hB, hb0, hbso, guard]
    · intro j hj
      simp only [List.mem_range'_1] at hj
      obtain ⟨sj, hsj⟩ : ∃ s, A.dynsyms[j]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      refine checkMatch_of_ne hsj fun he => ?_
      have := (hrun j sj hsj he hj.1).1
      omega
  · -- no hashed symbol has the name: both answer "not found"
    have hall : ∀ j, g.symoffset ≤ j → j < A.dynsyms.length → A.checkMatch r plt j = some false := by
      intro j h1 h2
      obtain ⟨sj, hsj⟩ : ∃ s, A.dynsyms[j]? = some s := ⟨_, List.getElem?_eq_getElem h2⟩
      exact checkMatch_of_ne hsj fun he => hex ⟨j, sj, h1, hsj, he⟩
    rw [firstMatch_allFalse fun j hj => by simp only [List.mem_range'_1] at hj; exact hall j hj.1 (by omega)]
    have hbi : gnuHashOf r.name % g.nbuckets < g.buckets.length := by
      rw [W.buckets_len]; exact Nat.mod_lt _ W.nb_pos
    obtain ⟨b, hb⟩ : ∃ b, g.buckets[gnuHashOf r.name % g.nbuckets]? = some b :=
      ⟨_, List.getElem?_eq_getElem hbi⟩
    have hwi : (gnuHashOf r.name / 64) &&& (g.bloom.length - 1) < g.bloom.length :=
      Nat.lt_of_le_of_lt Nat.and_le_right (by have := W.bloom_pos; omega)
    obtain ⟨w, hw'⟩ : ∃ w, g.bloom[(gnuHashOf r.name / 64) &&& (g.bloom.length - 1)]? = some w :=
      ⟨_, List.getElem?_eq_getElem hwi⟩
    rcases W.buckets_ok b (List.mem_of_getElem? hb) with h0 | ⟨hbso, hblt⟩
    · simp [File.gnuLookup, hg, W.nb_pos, W.bloom_pos, hw', hb, h0, guard]
    · have hwalk := chainWalk_eq A g r plt W (A.dynsyms.length - b) b (A.dynsyms.length + 1) rfl
        hbso hblt (by omega) fun i s _ hs he => absurd ⟨i, s, by omega, hs, he⟩ hex
      rw [firstMatch_allFalse (l := List.range' b (A.dynsyms.length - b))
        fun j hj => by simp only [List.mem_range'_1] at hj; exact hall j (by omega) (by omega)] at hwalk
      have hb0 : b ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le W.so_pos hbso)
      simp [File.gnuLookup, hg, W.nb_pos, W.bloom_pos, hw', hb, hb0, hbso, hwalk, guard]

end Silmaril.Elf
