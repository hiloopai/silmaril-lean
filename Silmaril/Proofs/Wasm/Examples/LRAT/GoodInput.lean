module

public import Silmaril.Proofs.Wasm.Examples.LRAT.GoodBase

@[expose] public section

/-!
# The invariant across the input exports and the step bookkeeping

`Good xs G B` (`Silmaril.Wasm.Examples.LRAT.Defs`) is preserved by every path of the exports other
than the hint scan, stated on the abstract view (eight globals `[m, t, c, S, cf, sid, u, n]` and
the memory `B`):

* input (`add_lit`, `end_clause`): `Good.extend` (input closed: later integers do not matter),
  `Good.append`, `Good.close`, `Good.endEmpty`, `Good.endRecord`, `Good.endDrop`;
* steps: `Good.begin`, `Good.stepLit`, `Good.abort`, `Good.endConflEmpty`, `Good.endCommit`;
* `Good.delete`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Logic.SAT

variable {xs : List Int} {m t c S cf sid u n : BitVec 32} {B : ByteArray}

/-- The tables after `delete(id)`: only `len[id]` changes, to `0`. -/
theorem delete_tables {id : BitVec 32} {i : Nat} (hs : B.size = memSize)
    (hp : lenBase + 4 * id.toNat + 4 ≤ memSize) (hid : id.toNat < maxId) (hi : i < maxId)
    (hl : entryLen (wr B (lenBase + 4 * id.toNat) 0#32) i ≠ 0) :
    entryStart (wr B (lenBase + 4 * id.toNat) 0#32) i = entryStart B i ∧
      entryLen (wr B (lenBase + 4 * id.toNat) 0#32) i = entryLen B i := by
  have hne : i ≠ id.toNat := by
    rintro rfl
    exact hl (by unfold entryLen; rw [wd_wr_self _ hs hp]; rfl)
  have h1 : lenBase + 4 * id.toNat + 4 ≤ startBase + 4 * i ∨
      startBase + 4 * i + 4 ≤ lenBase + 4 * id.toNat := by
    simp only [lenBase, startBase, maxId] at *; omega
  have h2 : lenBase + 4 * id.toNat + 4 ≤ lenBase + 4 * i ∨
      lenBase + 4 * i + 4 ≤ lenBase + 4 * id.toNat := by omega
  unfold entryStart entryLen
  rw [wd_wr_of _ hs hp h1, wd_wr_of _ hs hp h2]
  exact ⟨rfl, rfl⟩

/-- The target after appending `x` to the step's clause: false only if the target before was
false and `x` is false. -/
theorem target_snoc {G G' : List (BitVec 32)} {B' : ByteArray} {x : BitVec 32} {τ : Assignment}
    (hbuf : bufWords G' B' = bufWords G B ++ [x]) (hcand : candOf B' = candOf B)
    (hres : candOf B ≠ 0 → resPart B' (pivotOf G' B') (candOf B - 1) =
      resPart B (pivotOf G B) (candOf B - 1))
    (hf : Clause.eval τ (targetOf G' B') = false) :
    Clause.eval τ (targetOf G B) = false ∧ Lit.eval τ x.toInt = false := by
  unfold targetOf resolventOf at *
  rw [hcand, hbuf] at hf
  by_cases h0 : candOf B = 0
  · simp only [h0, ite_true, toClause, List.map_append, List.map_cons, List.map_nil,
      Clause.eval_append, Clause.eval_cons, Clause.eval_nil, Bool.or_false,
      Bool.or_eq_false_iff] at hf ⊢
    exact hf
  · simp only [h0, ite_false, hres h0, toClause, List.map_append, List.map_cons,
      List.map_nil, Clause.eval_append, Clause.eval_cons, Clause.eval_nil, Bool.or_false,
      Bool.or_eq_false_iff] at hf ⊢
    exact ⟨⟨hf.1.1, hf.2⟩, hf.1.2⟩

/-- The resolvent after appending `x` to the step's clause is weaker. -/
theorem resolvent_snoc {G G' : List (BitVec 32)} {B' : ByteArray} {x : BitVec 32}
    {τ : Assignment} {id : Nat} (hbuf : bufWords G' B' = bufWords G B ++ [x])
    (hres : resPart B' (pivotOf G' B') id = resPart B (pivotOf G B) id)
    (h : Clause.eval τ (resolventOf G B id) = true) :
    Clause.eval τ (resolventOf G' B' id) = true := by
  unfold resolventOf at *
  rw [hbuf, hres]
  simp only [toClause, List.map_append, Clause.eval_append, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

/-- The step after `step_lit(x)`, from the facts about the new memory `B₃`. -/
theorem StepOk.stepLit {x : BitVec 32} {B₁ B₃ : ByteArray}
    (st : StepOk [2#32, t, c, S, cf, sid, u, n] B) (hv : ValidLit x)
    (hbuf : bufWords [2#32, t + 4#32, c, S, cf, sid, u, n] B₃ =
      bufWords [2#32, t, c, S, cf, sid, u, n] B ++ [x])
    (hct4 : t + 4#32 ≠ c)
    (hdb : SameDb B B₃) (hcand : candOf B₃ = candOf B) (htag : tagOf B₃ = tagOf B)
    (hcov : ∀ id < maxId, covOf B₃ id = covOf B id)
    (hpiv : t ≠ c → pivotOf [2#32, t + 4#32, c, S, cf, sid, u, n] B₃ =
      pivotOf [2#32, t, c, S, cf, sid, u, n] B)
    (hval : Same B B₁ 4 startBase) (hs₁ : B₁.size = memSize)
    (hB₃ : B₃ = wr (wr B₁ (litAddr x) (S * 2#32)) (negAddr x) (S * 2#32 + 1#32)) :
    StepOk [2#32, t + 4#32, c, S, cf, sid, u, n] B₃ := by
  have hvalid : ∀ w ∈ bufWords [2#32, t + 4#32, c, S, cf, sid, u, n] B₃, ValidLit w := by
    rw [hbuf]
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact st.valid w hw
    · rw [List.mem_singleton.1 hw]; exact hv
  have hm : ∀ τ, Models τ B₃ → Models τ B := fun τ h => Models.congr (fun id hid =>
    ⟨(hdb id hid).1.symm, (hdb id hid).2.symm⟩) h
  have hres : ∀ id < maxId, t ≠ c →
      resPart B₃ (pivotOf [2#32, t + 4#32, c, S, cf, sid, u, n] B₃) id =
      resPart B (pivotOf [2#32, t, c, S, cf, sid, u, n] B) id := by
    intro id hid htc
    unfold resPart entryClause
    rw [(hdb id hid).2, hpiv htc]
  have hres' : candOf B ≠ 0 → resPart B₃ (pivotOf [2#32, t + 4#32, c, S, cf, sid, u, n] B₃)
      (candOf B - 1) = resPart B (pivotOf [2#32, t, c, S, cf, sid, u, n] B) (candOf B - 1) :=
    fun h0 => hres _ (st.cand h0).1 (st.cand h0).2.2
  refine ⟨st.id_lt, hvalid, fun h0 => ?_, fun hc τ hτ => ?_, fun τ hτ hf => ?_,
    fun id hid hc => ?_⟩
  · rw [hcand] at h0 ⊢
    obtain ⟨h1, h2, -⟩ := st.cand h0
    exact ⟨h1, by rw [(hdb _ h1).1]; exact h2, hct4⟩
  · by_contra hf
    have := (target_snoc hbuf hcand hres' (Bool.eq_false_iff.2 hf)).1
    rw [st.confl hc τ (hm τ hτ)] at this
    cases this
  · obtain ⟨hf', hx⟩ := target_snoc hbuf hcand hres' hf
    rw [hB₃]
    exact (hval.agrees (st.agrees τ (hm τ hτ) hf')).assign hs₁ hv (fun _ => hx)
      (fun e => absurd e (stamp_ne S)) (fun e => absurd e.symm (stamp_ne S)) (fun _ => hx)
  · rw [hcov id hid, htag] at hc
    obtain ⟨h1, h2, h3⟩ := st.cov id hid hc
    exact ⟨by rw [(hdb id hid).1]; exact h1, hct4, fun τ hτ =>
      resolvent_snoc hbuf (hres id hid h2) (h3 τ (hm τ hτ))⟩

/-- The RAT words after writes outside `[covBase, arenaBase)`. -/
theorem same_rat {B' : ByteArray} (h : Same B B' covBase arenaBase) :
    candOf B' = candOf B ∧ tagOf B' = tagOf B ∧ ∀ id < maxId, covOf B' id = covOf B id := by
  refine ⟨?_, ?_, fun id hid => ?_⟩
  · unfold candOf; rw [h _ (by decide) (by decide)]
  · unfold tagOf; rw [h _ (by decide) (by decide)]
  · unfold covOf; rw [h _ (by simp only [covBase]; omega)
      (by simp only [covBase, arenaBase, maxId] at *; omega)]

/-- `step_lit(x)`, with the memory written out. -/
theorem Good.stepLit' {x : BitVec 32} (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B)
    (hv : ValidLit x) (ht : t.toNat < memSize) :
    Good xs [2#32, t + 4#32, c, S, cf, sid, u, n]
      (wr (wr (wr B t.toNat x) (litAddr x) (S * 2#32)) (negAddr x) (S * 2#32 + 1#32)) := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have ht4 : t.toNat + 4 ≤ memSize := by simp only [memSize] at *; omega
  have htt : (t + 4#32).toNat = t.toNat + 4 := by simp only [memSize] at *; bv_omega
  have hs₁ : (wr B t.toNat x).size = memSize := size_wr_of x hs ht4
  have hsame₁ : Same B (wr B t.toNat x) 0 t.toNat := Same.of_wr x hs ht4 (Or.inr le_rfl)
  have hsa : Same (wr B t.toNat x)
      (wr (wr (wr B t.toNat x) (litAddr x) (S * 2#32)) (negAddr x) (S * 2#32 + 1#32))
      startBase memSize := Same.assign hs₁ hv
  have hsame : Same B
      (wr (wr (wr B t.toNat x) (litAddr x) (S * 2#32)) (negAddr x) (S * 2#32 + 1#32))
      startBase t.toNat := (hsame₁.mono (Nat.zero_le _) le_rfl).trans (hsa.mono le_rfl htm)
  have hx : wd (wr (wr (wr B t.toNat x) (litAddr x) (S * 2#32)) (negAddr x) (S * 2#32 + 1#32))
      t.toNat = x := by
    rw [hsa t.toNat (by simp only [startBase, arenaBase] at *; omega) ht4, wd_wr_self x hs ht4]
  have hbuf := words_snoc (hsame.mono (by simp only [startBase, arenaBase] at *; omega) le_rfl)
    hct hcd htd hx (by simp only [memSize] at *; omega)
  have hval : Same B (wr B t.toNat x) 4 startBase :=
    hsame₁.mono (Nat.zero_le _) (by simp only [arenaBase, startBase] at *; omega)
  have hstale := stale_assign (a := S * 2#32) (b := S * 2#32 + 1#32) hs₁ hv (hval.stale hG.stale)
    (by simp only [maxStamp] at hSm; show (S * 2#32).toNat ≤ 2 * S.toNat + 1; bv_omega)
    (by simp only [maxStamp] at hSm; show (S * 2#32 + 1#32).toNat ≤ 2 * S.toNat + 1; bv_omega)
  have hrat := same_rat (hsame.mono (by simp only [startBase, covBase]; omega)
    (by simp only [arenaBase] at *; omega))
  have hdb := SameDb.of_same hG.entries (hsame.mono le_rfl (by simp only [covBase, arenaBase] at *; omega))
    (hsame.mono (by simp only [startBase, arenaBase]; omega) hct)
  have hpiv : t ≠ c → pivotOf [2#32, t + 4#32, c, S, cf, sid, u, n]
      (wr (wr (wr B t.toNat x) (litAddr x) (S * 2#32)) (negAddr x) (S * 2#32 + 1#32)) =
      pivotOf [2#32, t, c, S, cf, sid, u, n] B := by
    intro htc
    have hlt : c.toNat + 4 ≤ t.toNat := by
      have : c.toNat ≠ t.toNat := fun h => htc (BitVec.eq_of_toNat_eq h).symm
      omega
    have hcb : startBase ≤ c.toNat := by simp only [startBase, arenaBase] at hbc ⊢; omega
    exact hsame _ hcb hlt
  refine ⟨size_assign hs₁ hv, hG.mode_le, hbc, (by show c.toNat ≤ (t + 4#32).toNat; omega),
    (by show (t + 4#32).toNat ≤ memSize; omega), hcd, (by show 4 ∣ (t + 4#32).toNat; omega),
    hSm, hstale, by rw [hrat.2.1]; exact hG.tag_le,
    fun id hid => by rw [hrat.2.2 id hid, hrat.2.1]; exact hG.cov_le id hid,
    entries_same hG.entries le_rfl (hsame.mono le_rfl (by simp only [covBase, arenaBase] at *; omega))
      (hsame.mono (by simp only [startBase, arenaBase]; omega) hct),
    fun hF => ?_, hG.unsat,
    fun h => absurd (show (2#32 : BitVec 32) = 0#32 from h) (by decide),
    fun _ => (hG.step rfl).stepLit hv hbuf (fun h => ?_) hdb hrat.1 hrat.2.1 hrat.2.2 hpiv hval hs₁ rfl⟩
  · obtain ⟨τ, hτ⟩ := hG.sat hF
    exact ⟨τ, Models.congr hdb hτ⟩
  · have : (t + 4#32).toNat = c.toNat := by rw [h]
    omega

/-- `delete(id)` outside a step, any globals: the database loses at most clause `id`. -/
theorem Good.delete' {G : List (BitVec 32)} {id : BitVec 32} (hG : Good xs G B)
    (hm : gv G gMode ≠ 2#32) (hid : id.toNat < maxId) :
    Good xs G (wr B (lenBase + 4 * id.toNat) 0#32) := by
  have hs := hG.size
  have hp : lenBase + 4 * id.toNat + 4 ≤ memSize := by
    simp only [lenBase, maxId, memSize] at *; omega
  have hsa : Same B (wr B (lenBase + 4 * id.toNat) 0#32) 4 startBase :=
    Same.of_wr _ hs hp (Or.inr (by simp only [lenBase, startBase]; omega))
  have hsb : Same B (wr B (lenBase + 4 * id.toNat) 0#32) covBase memSize :=
    Same.of_wr _ hs hp (Or.inl (by simp only [lenBase, maxId, covBase] at *; omega))
  have hbuf : bufWords G (wr B (lenBase + 4 * id.toNat) 0#32) = bufWords G B :=
    (hsb.mono (by have := hG.base_le; simp only [covBase, arenaBase] at *; omega)
      hG.top_le).bufWords hG.cstart_le
  have ht : ∀ i < maxId, entryLen (wr B (lenBase + 4 * id.toNat) 0#32) i ≠ 0 →
      entryStart (wr B (lenBase + 4 * id.toNat) 0#32) i = entryStart B i ∧
      entryLen (wr B (lenBase + 4 * id.toNat) 0#32) i = entryLen B i :=
    fun i hi hl => delete_tables hs hp hid hi hl
  have hca : Same B (wr B (lenBase + 4 * id.toNat) 0#32) arenaBase (gv G gCstart).toNat :=
    hsb.mono (by simp only [covBase, arenaBase]; omega) (Nat.le_trans hG.cstart_le hG.top_le)
  have hmod : ∀ τ, Models τ B → Models τ (wr B (lenBase + 4 * id.toNat) 0#32) := by
    intro τ hτ
    refine models_iff.2 fun i hi hl => ?_
    obtain ⟨h1, h2⟩ := ht i hi hl
    have hl' : entryLen B i ≠ 0 := h2 ▸ hl
    unfold entryClause
    rw [((hG.entries i hi hl').congr h1 h2 hca).2]
    exact hτ.entry hi hl'
  have hrat := same_rat (hsb.mono le_rfl (by decide))
  refine ⟨size_wr_of _ hs hp, hG.mode_le, hG.base_le, hG.cstart_le, hG.top_le, hG.cstart_dvd,
    hG.top_dvd, hG.stamp_le, hsa.stale hG.stale, by rw [hrat.2.1]; exact hG.tag_le,
    fun i hi => by rw [hrat.2.2 i hi, hrat.2.1]; exact hG.cov_le i hi,
    entries_of hG.entries le_rfl ht hca, fun hF => ?_, hG.unsat,
    fun h => ?_, fun h => absurd h hm⟩
  · obtain ⟨τ, hτ⟩ := hG.sat hF
    exact ⟨τ, hmod τ hτ⟩
  · obtain ⟨h1, h2, h3⟩ := hG.input h
    exact ⟨by rw [hbuf]; exact h1, by rw [hbuf]; exact h2, fun τ hτ => hmod τ (h3 τ hτ)⟩

/-- With the input phase over, later DIMACS integers keep the invariant. -/
theorem Good.extend (hG : Good xs [m, t, c, S, cf, sid, u, n] B) (hm : m ≠ 0#32) (ys : List Int) :
    Good (xs ++ ys) [m, t, c, S, cf, sid, u, n] B := by
  have hu : gv [m, t, c, S, cf, sid, u, n] gUnsat ≠ 0 → (Dimacs.cnf (xs ++ ys)).Unsat := by
    intro h
    obtain ⟨Gs, hGs⟩ := Dimacs.cnf_append xs ys
    rw [hGs]
    exact (hG.unsat h).append Gs
  exact ⟨hG.size, hG.mode_le, hG.base_le, hG.cstart_le, hG.top_le, hG.cstart_dvd, hG.top_dvd,
    hG.stamp_le, hG.stale, hG.tag_le, hG.cov_le, hG.entries,
    fun hF => hG.sat (cnf_sat_append hF), hu, fun h0 => absurd h0 hm, hG.step⟩

/-- `add_lit(x)` in the input phase, `x` in range, room in the arena: append `x`. -/
theorem Good.append {x : BitVec 32} (hG : Good xs [0#32, t, c, S, cf, sid, u, n] B)
    (hv : ValidLit x) (ht : t.toNat < memSize) :
    Good (xs ++ [x.toInt]) [0#32, t + 4#32, c, S, cf, sid, u, n] (wr B t.toNat x) := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have ht4 : t.toNat + 4 ≤ memSize := by simp only [memSize] at *; omega
  have htt : (t + 4#32).toNat = t.toNat + 4 := by simp only [memSize] at *; bv_omega
  have hF : Dimacs.cnf (xs ++ [x.toInt]) = Dimacs.cnf xs := Dimacs.cnf_snoc_ne xs hv.toInt_ne
  have hsame : Same B (wr B t.toNat x) 0 t.toNat := Same.of_wr x hs ht4 (Or.inr le_rfl)
  have hbuf : bufWords [0#32, t + 4#32, c, S, cf, sid, u, n] (wr B t.toNat x) =
      bufWords [0#32, t, c, S, cf, sid, u, n] B ++ [x] :=
    words_snoc (hsame.mono (Nat.zero_le _) le_rfl) hct hcd htd (wd_wr_self x hs ht4)
      (by simp only [memSize] at *; omega)
  have hdb : SameDb B (wr B t.toNat x) := SameDb.of_same hG.entries
    (hsame.mono (Nat.zero_le _) (by simp only [covBase, arenaBase] at *; omega))
    (hsame.mono (Nat.zero_le _) hct)
  have hrat := same_rat (hsame.mono (Nat.zero_le _) (by simp only [arenaBase] at *; omega))
  have hinput : 0#32 = 0#32 → (∀ w ∈ bufWords [0#32, t + 4#32, c, S, cf, sid, u, n]
      (wr B t.toNat x), ValidLit w) ∧ toClause (bufWords [0#32, t + 4#32, c, S, cf, sid, u, n]
      (wr B t.toNat x)) = Dimacs.pending (xs ++ [x.toInt]) ∧
      ∀ τ, (Dimacs.cnf (xs ++ [x.toInt])).eval τ = true → Models τ (wr B t.toNat x) := by
    intro _
    obtain ⟨hv0, hp, hmod⟩ := hG.input rfl
    rw [hbuf, Dimacs.pending_snoc_ne xs hv.toInt_ne, ← hp, hF]
    refine ⟨fun w hw => ?_, by simp [toClause], fun τ hτ => Models.congr hdb (hmod τ hτ)⟩
    rcases List.mem_append.1 hw with hw | hw
    · exact hv0 w hw
    · rw [List.mem_singleton.1 hw]; exact hv
  have hval : Same B (wr B t.toNat x) 4 startBase :=
    hsame.mono (Nat.zero_le _) (by simp only [arenaBase, startBase] at *; omega)
  refine ⟨size_wr_of x hs ht4, hG.mode_le, hbc, (by show c.toNat ≤ (t + 4#32).toNat; omega),
    (by show (t + 4#32).toNat ≤ memSize; omega), hcd, (by show 4 ∣ (t + 4#32).toNat; omega),
    hSm, hval.stale hG.stale, by rw [hrat.2.1]; exact hG.tag_le,
    fun i hi => by rw [hrat.2.2 i hi, hrat.2.1]; exact hG.cov_le i hi,
    entries_same hG.entries le_rfl
      (hsame.mono (Nat.zero_le _) (by simp only [covBase, arenaBase] at *; omega))
      (hsame.mono (Nat.zero_le _) hct), fun hF' => ?_, (by rw [hF]; exact hG.unsat), hinput,
    fun h => absurd (show (0#32 : BitVec 32) = 2#32 from h) (by decide)⟩
  rw [hF] at hF'
  obtain ⟨τ, hτ⟩ := hG.sat hF'
  exact ⟨τ, Models.congr hdb hτ⟩

/-- `add_lit(x)`, `x ≠ 0`, that cannot be appended: the input phase ends. -/
theorem Good.close {x : BitVec 32} (hG : Good xs [0#32, t, c, S, cf, sid, u, n] B)
    (hx : x ≠ 0#32) :
    Good (xs ++ [x.toInt]) [1#32, t, c, S, cf, sid, u, n] B := by
  have hx' : x.toInt ≠ 0 := fun h => hx (BitVec.toInt_inj.1 (by simpa using h))
  have hF : Dimacs.cnf (xs ++ [x.toInt]) = Dimacs.cnf xs := Dimacs.cnf_snoc_ne xs hx'
  refine ⟨hG.size, (by show (1#32 : BitVec 32).toNat ≤ 2; decide), hG.base_le, hG.cstart_le,
    hG.top_le, hG.cstart_dvd, hG.top_dvd, hG.stamp_le, hG.stale, hG.tag_le, hG.cov_le,
    hG.entries, ?_, ?_,
    fun h => absurd (show (1#32 : BitVec 32) = 0#32 from h) (by decide),
    fun h => absurd (show (1#32 : BitVec 32) = 2#32 from h) (by decide)⟩
  · rw [hF]; exact hG.sat
  · rw [hF]; exact hG.unsat

/-- The end of an empty input clause: the formula is unsatisfiable. -/
theorem Good.endEmpty (hG : Good xs [0#32, t, t, S, cf, sid, u, n] B) :
    Good (xs ++ [0]) [0#32, t, t, S, cf, sid, 1#32, n] B := by
  obtain ⟨-, hp, hmod⟩ := hG.input rfl
  have hp' : Dimacs.pending xs = [] := by rw [← hp, bufWords_nil]; rfl
  have hF : Dimacs.cnf (xs ++ [0]) = Dimacs.cnf xs ++ [[]] := by
    rw [Dimacs.cnf_snoc_zero, hp']
  have hun : (Dimacs.cnf (xs ++ [0])).Unsat :=
    CNF.Unsat.of_implies_nil (CNF.Implies.of_mem (by rw [hF]; simp))
  refine ⟨hG.size, hG.mode_le, hG.base_le, hG.cstart_le, hG.top_le, hG.cstart_dvd, hG.top_dvd,
    hG.stamp_le, hG.stale, hG.tag_le, hG.cov_le, hG.entries,
    fun hF' => absurd hF' (CNF.not_sat_of_unsat hun), fun _ => hun, fun _ => ?_,
    fun h => absurd (show (0#32 : BitVec 32) = 2#32 from h) (by decide)⟩
  rw [bufWords_nil, Dimacs.pending_snoc_zero]
  exact ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun τ hτ => hmod τ (cnf_eval_append hτ)⟩

/-- The end of a nonempty input clause, stored as clause `n`. -/
theorem Good.endRecord (hG : Good xs [0#32, t, c, S, cf, sid, u, n] B) (htc : t ≠ c)
    (hn : n.toNat < maxId) :
    Good (xs ++ [0]) [0#32, t, t, S, cf, sid, u, n + 1#32] (recordB B n c t) := by
  have _ := htc
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  obtain ⟨hv0, hp, hmod⟩ := hG.input rfl
  have hsr : Same B (recordB B n c t) 4 startBase ∧ Same B (recordB B n c t) covBase memSize :=
    Same.record hs hn
  obtain ⟨hent, hw⟩ : (∀ id < maxId, entryLen (recordB B n c t) id ≠ 0 →
      EntryOk (recordB B n c t) t.toNat id) ∧
      entryWords (recordB B n c t) n.toNat = words B c.toNat ((t.toNat - c.toNat) / 4) :=
    entries_record hG.entries hs hbc hct htm hcd htd hn hv0
  have hrat : candOf (recordB B n c t) = candOf B ∧ tagOf (recordB B n c t) = tagOf B ∧
      ∀ id < maxId, covOf (recordB B n c t) id = covOf B id :=
    same_rat (hsr.2.mono le_rfl (by decide))
  have hmod' : ∀ τ, (Dimacs.cnf (xs ++ [0])).eval τ = true → Models τ (recordB B n c t) := by
    intro τ hτ
    have hτ' : (Dimacs.cnf xs ++ [Dimacs.pending xs]).eval τ = true := by
      rw [← Dimacs.cnf_snoc_zero]; exact hτ
    have hτ'' : (Dimacs.cnf xs).eval τ = true ∧ CNF.eval τ [Dimacs.pending xs] = true := by
      simpa only [CNF.eval_append, Bool.and_eq_true] using hτ'
    refine models_record hG.entries hs hn (Nat.le_trans hct htm) (hmod τ hτ''.1) ?_
    rw [hw, show toClause (words B c.toNat ((t.toNat - c.toNat) / 4)) = Dimacs.pending xs from hp]
    simpa [CNF.eval] using hτ''.2
  exact ⟨size_wr_of _ (size_wr_of _ hs (by simp only [startBase, maxId, memSize] at *; omega))
      (by simp only [lenBase, maxId, memSize] at *; omega), hG.mode_le,
    (show arenaBase ≤ t.toNat by omega), (show t.toNat ≤ t.toNat from le_rfl), hG.top_le,
    hG.top_dvd, hG.top_dvd, hSm, hsr.1.stale hG.stale, by rw [hrat.2.1]; exact hG.tag_le,
    fun i hi => by rw [hrat.2.2 i hi, hrat.2.1]; exact hG.cov_le i hi, hent,
    fun ⟨τ, hτ⟩ => ⟨τ, hmod' τ hτ⟩, fun h => cnf_unsat_append (hG.unsat h),
    fun _ => ⟨(input_nil (xs := xs)).1, (input_nil (xs := xs)).2, hmod'⟩,
    fun h => absurd (show (0#32 : BitVec 32) = 2#32 from h) (by decide)⟩

/-- The end of an input clause that is not stored. -/
theorem Good.endDrop (hG : Good xs [0#32, t, c, S, cf, sid, u, n] B) :
    Good (xs ++ [0]) [0#32, t, t, S, cf, sid, u, n] B := by
  have hun : gv [0#32, t, t, S, cf, sid, u, n] gUnsat ≠ 0 → (Dimacs.cnf (xs ++ [0])).Unsat := by
    intro h
    obtain ⟨Gs, hGs⟩ := Dimacs.cnf_append xs [0]
    rw [hGs]
    exact (hG.unsat h).append Gs
  obtain ⟨_, hbc, hct, -⟩ := hG.facts
  obtain ⟨-, -, hmod⟩ := hG.input rfl
  refine ⟨hG.size, hG.mode_le, (show arenaBase ≤ t.toNat by omega),
    (show t.toNat ≤ t.toNat from le_rfl), hG.top_le, hG.top_dvd, hG.top_dvd, hG.stamp_le,
    hG.stale, hG.tag_le, hG.cov_le, fun id hid hl => (hG.entries id hid hl).weaken hG.cstart_le,
    fun hF => hG.sat (cnf_sat_append hF), hun, fun _ => ?_,
    fun h => absurd (show (0#32 : BitVec 32) = 2#32 from h) (by decide)⟩
  rw [bufWords_nil, Dimacs.pending_snoc_zero]
  exact ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun τ hτ => hmod τ (cnf_eval_append hτ)⟩

/-- The memory after `step_begin`: no candidate, the new tag. -/
abbrev beginB (B : ByteArray) (S : BitVec 32) : ByteArray :=
  wr (wr B candAddr 0#32) tagAddr (S + 1#32)

/-- `step_begin(id)`: a new step with an empty clause, a fresh stamp and a fresh tag. -/
theorem Good.begin {id : BitVec 32} (hG : Good xs [m, t, c, S, cf, sid, u, n] B) (hm : m ≠ 2#32)
    (hid : id.toNat < maxId) (hS : S.toNat < maxStamp) :
    Good xs [2#32, c, c, S + 1#32, 0#32, id, u, n] (beginB B S) := by
  have _ := hm
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have hS1 : (S + 1#32).toNat = S.toNat + 1 := by simp only [maxStamp] at *; bv_omega
  have h1 : candAddr + 4 ≤ memSize := by decide
  have h2 : tagAddr + 4 ≤ memSize := by decide
  have hs1 : (wr B candAddr 0#32).size = memSize := size_wr_of _ hs h1
  have hlo : Same B (beginB B S) 0 candAddr :=
    (Same.of_wr _ hs h1 (Or.inr le_rfl)).trans
      (Same.of_wr _ hs1 h2 (Or.inr (by decide)))
  have hhi : Same B (beginB B S) arenaBase memSize :=
    (Same.of_wr _ hs h1 (Or.inl (by decide))).trans
      (Same.of_wr _ hs1 h2 (Or.inl (by decide)))
  have htag : tagOf (beginB B S) = S + 1#32 := wd_wr_self _ hs1 h2
  have hcand : candOf (beginB B S) = 0 := by
    unfold candOf
    rw [wd_wr_of _ hs1 h2 (Or.inr (by decide)), wd_wr_self _ hs h1]
    rfl
  have hcov : ∀ i < maxId, covOf (beginB B S) i = covOf B i := fun i hi =>
    hlo _ (Nat.zero_le _) (by simp only [covBase, candAddr, maxId] at *; omega)
  have hdb : SameDb B (beginB B S) := SameDb.of_same hG.entries
    (hlo.mono (Nat.zero_le _) (by decide))
    (hhi.mono le_rfl (Nat.le_trans hct htm))
  have hval : Same B (beginB B S) 4 startBase :=
    hlo.mono (Nat.zero_le _) (by decide)
  have hbuf : bufWords [2#32, c, c, S + 1#32, 0#32, id, u, n] (beginB B S) = [] := bufWords_nil
  have hagree : ∀ τ : Assignment, Agrees τ (beginB B S) (S + 1#32) := by
    intro τ y hy
    have hst : (wd (beginB B S) (litAddr y)).toNat ≤ 2 * S.toNat + 1 := by
      rw [hval.lit hy]; exact hG.stale y hy
    constructor <;> intro h <;> rw [h] at hst <;> (simp only [maxStamp] at *; bv_omega)
  have hstep : StepOk [2#32, c, c, S + 1#32, 0#32, id, u, n] (beginB B S) := by
    refine ⟨hid, by rw [hbuf]; exact fun _ h => absurd h List.not_mem_nil,
      fun h => absurd hcand h, fun h => absurd rfl h, fun τ _ _ => hagree τ, fun i hi h => ?_⟩
    have hle : (covOf B i).toNat ≤ S.toNat := Nat.le_trans (hG.cov_le i hi) hG.tag_le
    rw [hcov i hi, htag] at h
    rw [h] at hle
    omega
  refine ⟨size_wr_of _ hs1 h2, (by show (2#32 : BitVec 32).toNat ≤ 2; decide), hbc,
    (show c.toNat ≤ c.toNat from le_rfl), (show c.toNat ≤ memSize by omega), hcd, hcd,
    (show (S + 1#32).toNat ≤ maxStamp by simp only [maxStamp] at *; omega), ?_,
    by rw [htag]; show (S + 1#32).toNat ≤ (S + 1#32).toNat; exact le_rfl,
    fun i hi => ?_, entries_same hG.entries le_rfl
      (hlo.mono (Nat.zero_le _) (by decide))
      (hhi.mono le_rfl (Nat.le_trans hct htm)),
    fun hF => ?_, hG.unsat, fun h => absurd (show (2#32 : BitVec 32) = 0#32 from h) (by decide),
    fun _ => hstep⟩
  · intro y hy
    have : (wd B (litAddr y)).toNat ≤ 2 * S.toNat + 1 := hG.stale y hy
    show (wd (beginB B S) (litAddr y)).toNat ≤ 2 * (S + 1#32).toNat + 1
    rw [hval.lit hy]
    omega
  · rw [hcov i hi, htag]
    have : (covOf B i).toNat ≤ S.toNat := Nat.le_trans (hG.cov_le i hi) hG.tag_le
    show (covOf B i).toNat ≤ (S + 1#32).toNat
    omega
  · obtain ⟨τ, hτ⟩ := hG.sat hF
    exact ⟨τ, Models.congr hdb hτ⟩

/-- `step_lit(x)`: `x` is appended to the step's clause and assigned false (`-x` true). -/
theorem Good.stepLit {x : BitVec 32} (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B)
    (hv : ValidLit x) (ht : t.toNat < memSize) :
    Good xs [2#32, t + 4#32, c, S, cf, sid, u, n]
      (wr (wr (wr B t.toNat x) (litAddr x) (S * 2#32)) (negAddr x) (S * 2#32 + 1#32)) := by
  exact hG.stepLit' hv ht

/-- Leaving a step without storing its clause (abort, or `step_end` without a conflict). -/
theorem Good.abort (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) :
    Good xs [1#32, c, c, S, cf, sid, u, n] B := by
  obtain ⟨_, _, hct, htm, -⟩ := hG.facts
  refine ⟨hG.size, (by show (1#32 : BitVec 32).toNat ≤ 2; decide), hG.base_le,
    (show c.toNat ≤ c.toNat from le_rfl), (show c.toNat ≤ memSize by omega),
    hG.cstart_dvd, hG.cstart_dvd, hG.stamp_le, hG.stale, hG.tag_le, hG.cov_le, hG.entries,
    hG.sat, hG.unsat, fun h => absurd (show (1#32 : BitVec 32) = 0#32 from h) (by decide),
    fun h => absurd (show (1#32 : BitVec 32) = 2#32 from h) (by decide)⟩

/-- A conflict outside a RAT group: the database implies the step's clause. -/
theorem StepOk.implies {G : List (BitVec 32)} (st : StepOk G B) (hcf : gv G gConfl ≠ 0)
    (hc0 : candOf B = 0) {τ : Assignment} (hτ : Models τ B) :
    Clause.eval τ (toClause (bufWords G B)) = true := by
  have h := st.confl hcf τ hτ
  unfold targetOf at h
  rw [hc0, ite_eq_left rfl] at h
  exact h

/-- `step_end` after a conflict, empty clause, no candidate: the formula is unsatisfiable. -/
theorem Good.endConflEmpty (hG : Good xs [2#32, t, t, S, cf, sid, u, n] B) (hcf : cf ≠ 0#32)
    (hc0 : candOf B = 0) :
    Good xs [1#32, t, t, S, cf, sid, 1#32, n] B := by
  have hun : (Dimacs.cnf xs).Unsat := by
    intro τ
    cases hτ : (Dimacs.cnf xs).eval τ with
    | false => rfl
    | true =>
      obtain ⟨τ', hτ'⟩ := hG.sat ⟨τ, hτ⟩
      have h := (hG.step rfl).implies hcf hc0 hτ'
      rw [show bufWords [2#32, t, t, S, cf, sid, u, n] B = [] from bufWords_nil] at h
      cases h
  refine ⟨hG.size, (by show (1#32 : BitVec 32).toNat ≤ 2; decide), hG.base_le, hG.cstart_le,
    hG.top_le, hG.cstart_dvd, hG.top_dvd, hG.stamp_le, hG.stale, hG.tag_le, hG.cov_le,
    hG.entries, hG.sat, fun _ => hun,
    fun h => absurd (show (1#32 : BitVec 32) = 0#32 from h) (by decide),
    fun h => absurd (show (1#32 : BitVec 32) = 2#32 from h) (by decide)⟩

/-- Leaving a step by storing its clause, given that it keeps the database satisfiable. -/
theorem Good.commit (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B)
    (hsat : ∀ τ, Models τ B → ∃ τ', Models τ' B ∧
      Clause.eval τ' (toClause (bufWords [2#32, t, c, S, cf, sid, u, n] B)) = true) :
    Good xs [1#32, t, t, S, cf, sid, u, n] (recordB B sid c t) := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have hst : StepOk [2#32, t, c, S, cf, sid, u, n] B := hG.step rfl
  have hsid : sid.toNat < maxId := hst.id_lt
  have hsr : Same B (recordB B sid c t) 4 startBase ∧ Same B (recordB B sid c t) covBase memSize :=
    Same.record (c := c) (d := t - c) hs hsid
  obtain ⟨hent, hw⟩ : (∀ id < maxId, entryLen (recordB B sid c t) id ≠ 0 →
      EntryOk (recordB B sid c t) t.toNat id) ∧
      entryWords (recordB B sid c t) sid.toNat = words B c.toNat ((t.toNat - c.toNat) / 4) :=
    entries_record hG.entries hs hbc hct htm hcd htd hsid hst.valid
  have hrat : candOf (recordB B sid c t) = candOf B ∧ tagOf (recordB B sid c t) = tagOf B ∧
      ∀ id < maxId, covOf (recordB B sid c t) id = covOf B id :=
    same_rat (hsr.2.mono le_rfl (by decide))
  refine ⟨size_wr_of _ (size_wr_of _ hs (by simp only [startBase, maxId, memSize] at *; omega))
      (by simp only [lenBase, maxId, memSize] at *; omega),
    (by show (1#32 : BitVec 32).toNat ≤ 2; decide), (show arenaBase ≤ t.toNat by omega),
    (show t.toNat ≤ t.toNat from le_rfl), hG.top_le, hG.top_dvd, hG.top_dvd, hSm,
    hsr.1.stale hG.stale, by rw [hrat.2.1]; exact hG.tag_le,
    fun i hi => by rw [hrat.2.2 i hi, hrat.2.1]; exact hG.cov_le i hi, hent, fun hF => ?_,
    hG.unsat, fun h => absurd (show (1#32 : BitVec 32) = 0#32 from h) (by decide),
    fun h => absurd (show (1#32 : BitVec 32) = 2#32 from h) (by decide)⟩
  obtain ⟨τ, hτ⟩ := hG.sat hF
  obtain ⟨τ', hτ', hC⟩ := hsat τ hτ
  refine ⟨τ', models_record hG.entries hs hsid (Nat.le_trans hct htm) hτ' ?_⟩
  rw [hw]
  exact hC

/-- `step_end` after a conflict, nonempty clause, no candidate: it is stored as clause `sid`. -/
theorem Good.endCommit (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) (hcf : cf ≠ 0#32)
    (hc0 : candOf B = 0) :
    Good xs [1#32, t, t, S, cf, sid, u, n] (recordB B sid c t) :=
  hG.commit fun τ hτ => ⟨τ, hτ, (hG.step rfl).implies hcf hc0 hτ⟩

/-- `delete(id)` outside a step. -/
theorem Good.delete {G : List (BitVec 32)} {id : BitVec 32} (hG : Good xs G B)
    (hm : gv G gMode ≠ 2#32) (hid : id.toNat < maxId) :
    Good xs G (wr B (lenBase + 4 * id.toNat) 0#32) := by
  exact hG.delete' hm hid

end Silmaril.Wasm.Examples.LRAT
