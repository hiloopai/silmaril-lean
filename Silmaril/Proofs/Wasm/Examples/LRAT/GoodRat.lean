module

public import Silmaril.Proofs.Wasm.Examples.LRAT.GoodHint
public import Silmaril.Proofs.Wasm.Examples.LRAT.GoodInput
public import Silmaril.Logic.SAT.LRAT.Thms

@[expose] public section

/-!
# The invariant across RAT steps

* `Good.closeGroup`: closing a RAT group that reached a conflict marks its candidate covered
  (`cov[cand - 1] := tag`): the database implies the candidate's resolvent;
* `AsgOk`: the literal assignments of a group so far (the memory differs from the group's start
  in the literal values only, and every model of the database making the assigned literals
  false agrees with them); `AsgOk.start`, `AsgOk.assign`;
* `Good.ratGroup`: the group of candidate `j` once the step's clause and the literals of clause
  `j` other than `-p` are assigned false;
* `Good.ratCommit`: when every stored clause containing `-p` is covered, storing the step's
  clause keeps the database satisfiable, by the RAT lemma `CNF.sat_cons_of_rat`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Logic.SAT

variable {xs : List Int} {t c S cf sid u n : BitVec 32} {B B' : ByteArray}

/-! ## Writes to the RAT region -/

/-- The address of `cov[k]`. -/
abbrev covAddr (k : Nat) : Nat := covBase + 4 * k

/-- `B'` differs from `B` at most in the RAT region `[covBase, arenaBase)`. -/
structure RatSame (B B' : ByteArray) : Prop where
  size : B.size = memSize
  size' : B'.size = memSize
  lo : Same B B' 0 covBase
  hi : Same B B' arenaBase memSize

theorem RatSame.of_wr {a : Nat} (v : BitVec 32) (hs : B.size = memSize) (ha1 : covBase ≤ a)
    (ha2 : a + 4 ≤ arenaBase) : RatSame B (wr B a v) := by
  have ha : a + 4 ≤ memSize := by simp only [arenaBase, memSize] at *; omega
  exact ⟨hs, size_wr_of v hs ha, Same.of_wr v hs ha (Or.inr ha1), Same.of_wr v hs ha (Or.inl ha2)⟩

theorem RatSame.wd_hi (h : RatSame B B') {a : Nat} (ha : arenaBase ≤ a) : wd B' a = wd B a := by
  by_cases hb : a + 4 ≤ memSize
  · exact h.hi a ha hb
  · have h1 : B.size < a + 4 := by rw [h.size]; omega
    have h2 : B'.size < a + 4 := by rw [h.size']; omega
    rw [wd, wd, Silmaril.Wasm.Logic.Core.load_eq_none h1, Silmaril.Wasm.Logic.Core.load_eq_none h2]

theorem RatSame.bufWords (h : RatSame B B') {G : List (BitVec 32)}
    (hb : arenaBase ≤ (gv G gCstart).toNat) : bufWords G B' = bufWords G B := by
  unfold LRAT.bufWords LRAT.words
  exact List.map_congr_left fun k _ => h.wd_hi (by omega)

theorem RatSame.sameDb (h : RatSame B B') {cs : Nat}
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) (hcs : cs ≤ memSize) :
    SameDb B B' :=
  SameDb.of_same hent (h.lo.mono (by simp only [startBase]; omega) le_rfl) (h.hi.mono le_rfl hcs)

theorem RatSame.entries (h : RatSame B B') {cs : Nat}
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) (hcs : cs ≤ memSize) :
    ∀ id < maxId, entryLen B' id ≠ 0 → EntryOk B' cs id :=
  entries_same hent le_rfl (h.lo.mono (by simp only [startBase]; omega) le_rfl) (h.hi.mono le_rfl hcs)

theorem RatSame.models (h : RatSame B B') {cs : Nat}
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) (hcs : cs ≤ memSize)
    {τ : Assignment} : Models τ B' ↔ Models τ B :=
  ⟨Models.congr fun id hid => ⟨((h.sameDb hent hcs) id hid).1.symm,
    ((h.sameDb hent hcs) id hid).2.symm⟩, Models.congr (h.sameDb hent hcs)⟩

theorem RatSame.trans (h : RatSame B B') {B'' : ByteArray} (h' : RatSame B' B'') : RatSame B B'' :=
  ⟨h.size, h'.size', h.lo.trans h'.lo, h.hi.trans h'.hi⟩

/-- The target of a group: the resolvent of its candidate. -/
theorem targetOf_cand {G : List (BitVec 32)} (hc : candOf B ≠ 0) :
    targetOf G B = resolventOf G B (candOf B - 1) := by
  unfold targetOf
  simp only [hc, ite_false]

/-- The step's view after a write to the RAT region that keeps the candidate. -/
theorem RatSame.view (h : RatSame B B') {G : List (BitVec 32)} {cs : Nat}
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B cs id) (hcs : cs ≤ memSize)
    (hb : arenaBase ≤ (gv G gCstart).toNat) :
    LRAT.bufWords G B' = LRAT.bufWords G B ∧ pivotOf G B' = pivotOf G B ∧
      ∀ id < maxId, resolventOf G B' id = resolventOf G B id := by
  have hbuf : LRAT.bufWords G B' = LRAT.bufWords G B := h.bufWords hb
  have hpiv : pivotOf G B' = pivotOf G B := h.wd_hi hb
  refine ⟨hbuf, hpiv, fun id hid => ?_⟩
  unfold resolventOf resPart entryClause
  rw [hbuf, hpiv, ((h.sameDb hent hcs) id hid).2]

/-! ## Closing a group -/

/-- **Closing a group that reached a conflict** marks its candidate covered. -/
theorem Good.closeGroup (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) (hc : candOf B ≠ 0)
    (hcf : cf ≠ 0#32) :
    Good xs [2#32, t, c, S, cf, sid, u, n] (wr B (covAddr (candOf B - 1)) (tagOf B)) := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have st : StepOk [2#32, t, c, S, cf, sid, u, n] B := hG.step rfl
  obtain ⟨hk, hlk, htc⟩ := st.cand hc
  have hka : covAddr (candOf B - 1) + 4 ≤ memSize := by
    simp only [covAddr, covBase, maxId, memSize] at *; omega
  have hr : RatSame B (wr B (covAddr (candOf B - 1)) (tagOf B)) :=
    RatSame.of_wr _ hs (by simp only [covAddr]; omega)
      (by simp only [covAddr, covBase, arenaBase, maxId] at *; omega)
  have hcm : c.toNat ≤ memSize := Nat.le_trans hct htm
  have hdb := hr.sameDb hG.entries hcm
  obtain ⟨hbuf, -, hres⟩ := hr.view (G := [2#32, t, c, S, cf, sid, u, n]) hG.entries hcm hbc
  have hcand : candOf (wr B (covAddr (candOf B - 1)) (tagOf B)) = candOf B := by
    show (wd (wr B (covAddr (candOf B - 1)) (tagOf B)) candAddr).toNat = candOf B
    rw [wd_wr_of _ hs hka (Or.inl (by simp only [covAddr, covBase, candAddr, maxId] at *; omega))]
    rfl
  have htag : tagOf (wr B (covAddr (candOf B - 1)) (tagOf B)) = tagOf B := by
    show wd (wr B (covAddr (candOf B - 1)) (tagOf B)) tagAddr = tagOf B
    rw [wd_wr_of _ hs hka (Or.inl (by simp only [covAddr, covBase, tagAddr, maxId] at *; omega))]
    rfl
  have hcov : ∀ id < maxId, covOf (wr B (covAddr (candOf B - 1)) (tagOf B)) id =
      if id = candOf B - 1 then tagOf B else covOf B id := by
    intro id hid
    unfold covOf
    by_cases he : id = candOf B - 1
    · simp only [he, ite_true]; exact wd_wr_self _ hs hka
    · simp only [he, ite_false]
      exact wd_wr_of _ hs hka (by simp only [covAddr] at *; omega)
  have htgt : targetOf [2#32, t, c, S, cf, sid, u, n] (wr B (covAddr (candOf B - 1)) (tagOf B)) =
      targetOf [2#32, t, c, S, cf, sid, u, n] B := by
    have hc' : candOf (wr B (covAddr (candOf B - 1)) (tagOf B)) ≠ 0 := by rw [hcand]; exact hc
    rw [targetOf_cand hc, targetOf_cand hc', hcand, hres _ hk]
  have hm : ∀ τ, Models τ (wr B (covAddr (candOf B - 1)) (tagOf B)) ↔ Models τ B :=
    fun τ => hr.models hG.entries hcm
  have hval : Same B (wr B (covAddr (candOf B - 1)) (tagOf B)) 4 startBase :=
    hr.lo.mono (Nat.zero_le _) (by simp only [startBase, covBase]; omega)
  have hstep : StepOk [2#32, t, c, S, cf, sid, u, n] (wr B (covAddr (candOf B - 1)) (tagOf B)) := by
    refine ⟨st.id_lt, fun w hw => st.valid w (hbuf ▸ hw), fun h0 => ?_, fun h0 τ hτ => ?_,
      fun τ hτ hf => ?_, fun id hid h => ?_⟩
    · rw [hcand] at h0 ⊢
      exact ⟨hk, by rw [(hdb _ hk).1]; exact hlk, htc⟩
    · rw [htgt]; exact st.confl h0 τ ((hm τ).1 hτ)
    · rw [htgt] at hf; exact hval.agrees (st.agrees τ ((hm τ).1 hτ) hf)
    · show entryLen _ id ≠ 0 ∧ t ≠ c ∧ ∀ τ, Models τ _ → Clause.eval τ (resolventOf _ _ id) = true
      rw [hcov id hid, htag] at h
      by_cases he : id = candOf B - 1
      · refine ⟨by rw [(hdb id hid).1, he]; exact hlk, htc, fun τ hτ => ?_⟩
        rw [hres id hid, he, ← targetOf_cand hc]
        exact st.confl hcf τ ((hm τ).1 hτ)
      · simp only [he, ite_false] at h
        obtain ⟨h1, h2, h3⟩ := st.cov id hid h
        exact ⟨by rw [(hdb id hid).1]; exact h1, h2, fun τ hτ => by
          rw [hres id hid]; exact h3 τ ((hm τ).1 hτ)⟩
  refine ⟨size_wr_of _ hs hka, hG.mode_le, hbc, hct, htm, hcd, htd, hSm, hval.stale hG.stale,
    by rw [htag]; exact hG.tag_le, fun id hid => ?_, hr.entries hG.entries hcm, fun hF => ?_,
    hG.unsat, fun h => absurd (show (2#32 : BitVec 32) = 0#32 from h) (by decide),
    fun _ => hstep⟩
  · rw [hcov id hid, htag]
    split
    · exact le_rfl
    · exact hG.cov_le id hid
  · obtain ⟨τ, hτ⟩ := hG.sat hF
    exact ⟨τ, (hm τ).2 hτ⟩

/-! ## The assignments of a group -/

/-- The assignments of a group so far, from the memory `B₀` at its start: only literal values
change, they stay at most `2S + 1`, and every model of the database making the literals of `L`
false agrees with them. -/
structure AsgOk (B₀ B' : ByteArray) (S : BitVec 32) (L : List (BitVec 32)) : Prop where
  hi : HiSame B₀ B'
  stale : ∀ x, ValidLit x → (wd B' (litAddr x)).toNat ≤ 2 * S.toNat + 1
  agrees : ∀ τ, Models τ B₀ → (∀ w ∈ L, Lit.eval τ w.toInt = false) → Agrees τ B' S

/-- A fresh stamp: nothing is assigned. -/
theorem AsgOk.start (hs : B.size = memSize) (hS : S.toNat < maxStamp)
    (hst : ∀ x, ValidLit x → (wd B (litAddr x)).toNat ≤ 2 * S.toNat + 1) :
    AsgOk B B (S + 1#32) [] := by
  have hS1 : (S + 1#32).toNat = S.toNat + 1 := by simp only [maxStamp] at *; bv_omega
  refine ⟨HiSame.refl hs, fun x hx => by have := hst x hx; omega, fun τ _ _ y hy => ?_⟩
  have h := hst y hy
  constructor <;> intro e <;> rw [e] at h <;> (simp only [maxStamp] at *; bv_omega)

/-- Assigning `x` false. -/
theorem AsgOk.assign {B₀ : ByteArray} {L : List (BitVec 32)} {x : BitVec 32}
    (h : AsgOk B₀ B S L) (hS : S.toNat ≤ maxStamp) (hx : ValidLit x) :
    AsgOk B₀ (wr (wr B (litAddr x) (S * 2#32 + 0#32)) (negAddr x) (S * 2#32 + 1#32)) S
      (L ++ [x]) := by
  have hs : B.size = memSize := h.hi.size'
  refine ⟨h.hi.trans (HiSame.assign hs hx), stale_assign hs hx h.stale
    (by simp only [maxStamp] at hS; show (S * 2#32 + 0#32).toNat ≤ 2 * S.toNat + 1; bv_omega)
    (by simp only [maxStamp] at hS; show (S * 2#32 + 1#32).toNat ≤ 2 * S.toNat + 1; bv_omega),
    fun τ hτ hL => ?_⟩
  have hxf : Lit.eval τ x.toInt = false := hL x (List.mem_append_right _ (List.mem_singleton_self _))
  have ha := h.agrees τ hτ fun w hw => hL w (List.mem_append_left _ hw)
  have hne : S * 2#32 + 0#32 ≠ S * 2#32 + 1#32 := by rw [BitVec.add_zero]; exact stamp_ne S
  exact ha.assign hs hx (fun _ => hxf) (fun e => absurd e hne)
    (fun e => absurd e.symm (stamp_ne S)) (fun _ => hxf)

/-! ## Starting a group -/

/-- A word other than `-p` of a clause containing it is in the resolvent part. -/
theorem mem_resPart {p w : BitVec 32} {id : Nat} (hp : ValidLit p)
    (hm : w ∈ entryWords B id) (hne : w ≠ -p) : w.toInt ∈ resPart B p id := by
  refine List.mem_filter.2 ⟨List.mem_map_of_mem hm, ?_⟩
  have : w.toInt ≠ -p.toInt := fun h => hne (BitVec.toInt_inj.1 (by rw [h, hp.toInt_neg]))
  simpa using this

/-- The pivot is a literal of the step's clause. -/
theorem pivot_mem {G : List (BitVec 32)} (htc : gv G gTop ≠ gv G gCstart)
    (hct : (gv G gCstart).toNat ≤ (gv G gTop).toNat) (hcd : 4 ∣ (gv G gCstart).toNat)
    (htd : 4 ∣ (gv G gTop).toNat) : pivotOf G B ∈ bufWords G B := by
  have hn : 0 < ((gv G gTop).toNat - (gv G gCstart).toNat) / 4 := by
    have : (gv G gTop).toNat ≠ (gv G gCstart).toNat := fun h => htc (BitVec.eq_of_toNat_eq h)
    omega
  unfold bufWords
  rw [mem_words]
  exact ⟨0, hn, by simp [pivotOf]⟩

/-- **The group of candidate `j`**, once the step's clause and the literals of clause `j` other
than `-p` are assigned false. -/
theorem Good.ratGroup {j : BitVec 32} (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B)
    (hj : j.toNat < maxId) (hlen : entryLen B j.toNat ≠ 0) (htc : t ≠ c)
    (ha : AsgOk (wr B candAddr (j + 1#32)) B' (S + 1#32)
      (bufWords [2#32, t, c, S, cf, sid, u, n] B ++ (entryWords B j.toNat).filter
        (· != -(pivotOf [2#32, t, c, S, cf, sid, u, n] B)))) (hS : S.toNat < maxStamp) :
    Good xs [2#32, t, c, S + 1#32, 0#32, sid, u, n] B' := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have st : StepOk [2#32, t, c, S, cf, sid, u, n] B := hG.step rfl
  have hcm : c.toNat ≤ memSize := Nat.le_trans hct htm
  have hS1 : (S + 1#32).toNat = S.toNat + 1 := by simp only [maxStamp] at *; bv_omega
  have hca : candAddr + 4 ≤ memSize := by decide
  have hr : RatSame B (wr B candAddr (j + 1#32)) :=
    RatSame.of_wr _ hs (by decide) (by decide)
  have hent₂ := hr.entries hG.entries hcm
  have hdb := (hr.sameDb hG.entries hcm)
  obtain ⟨hbuf₂, hpiv₂, hres₂⟩ := hr.view (G := [2#32, t, c, S, cf, sid, u, n]) hG.entries hcm hbc
  have hbase : startBase ≤ c.toNat := by simp only [arenaBase, startBase] at *; omega
  obtain ⟨hbuf, hcand, htag, hcov, -, hres⟩ := ha.hi.step (G := [2#32, t, c, S + 1#32, 0#32, sid, u, n])
    hent₂ hbase fun _ => by
      unfold candOf; rw [wd_wr_self _ hs hca]
      simp only [maxId] at *; bv_omega
  have hcand' : candOf B' = j.toNat + 1 := by
    rw [hcand]; unfold candOf; rw [wd_wr_self _ hs hca]
    simp only [maxId] at *; bv_omega
  have htag' : tagOf B' = tagOf B := by
    rw [htag]; unfold tagOf
    rw [wd_wr_of _ hs hca (Or.inl (by decide))]
  have hcov' : ∀ id < maxId, covOf B' id = covOf B id := by
    intro id hid; rw [hcov]; unfold covOf
    rw [wd_wr_of _ hs hca (Or.inr (by simp only [covBase, candAddr, maxId] at *; omega))]
  have hm : ∀ τ, Models τ B' ↔ Models τ B := fun τ =>
    (ha.hi.models hent₂).trans (hr.models hG.entries hcm)
  have hl : ∀ id < maxId, entryLen B' id = entryLen B id := fun id hid =>
    ((ha.hi.sameDb hent₂) id hid).1.trans (hdb id hid).1
  have hres' : ∀ id < maxId, resolventOf [2#32, t, c, S + 1#32, 0#32, sid, u, n] B' id =
      resolventOf [2#32, t, c, S, cf, sid, u, n] B id := fun id hid =>
    (hres id hid).trans (hres₂ id hid)
  have hbuf' : bufWords [2#32, t, c, S + 1#32, 0#32, sid, u, n] B' =
      bufWords [2#32, t, c, S, cf, sid, u, n] B := hbuf.trans hbuf₂
  have htgt : targetOf [2#32, t, c, S + 1#32, 0#32, sid, u, n] B' =
      resolventOf [2#32, t, c, S, cf, sid, u, n] B j.toNat := by
    rw [targetOf_cand (by rw [hcand']; omega), hcand', Nat.add_sub_cancel, hres' _ hj]
  have hpv : ValidLit (pivotOf [2#32, t, c, S, cf, sid, u, n] B) :=
    st.valid _ (pivot_mem (B := B) (G := [2#32, t, c, S, cf, sid, u, n]) htc hct hcd htd)
  have hstep : StepOk [2#32, t, c, S + 1#32, 0#32, sid, u, n] B' := by
    refine ⟨st.id_lt, hbuf' ▸ st.valid, fun _ => ?_, fun h0 => absurd rfl h0,
      fun τ hτ hf => ?_, fun id hid h => ?_⟩
    · rw [hcand', Nat.add_sub_cancel]
      exact ⟨hj, by rw [hl _ hj]; exact hlen, htc⟩
    · show Agrees τ B' (S + 1#32)
      rw [htgt] at hf
      have hf' : Clause.eval τ (toClause (bufWords [2#32, t, c, S, cf, sid, u, n] B)) = false ∧
          Clause.eval τ (resPart B (pivotOf [2#32, t, c, S, cf, sid, u, n] B) j.toNat) = false := by
        simpa [resolventOf] using hf
      refine ha.agrees τ ((hr.models hG.entries hcm).2 ((hm τ).1 hτ)) fun w hw => ?_
      rcases List.mem_append.1 hw with hw | hw
      · exact (Clause.eval_eq_false_iff _ _).1 hf'.1 _ (List.mem_map_of_mem hw)
      · obtain ⟨hwm, hwp⟩ := List.mem_filter.1 hw
        exact (Clause.eval_eq_false_iff _ _).1 hf'.2 _
          (mem_resPart hpv hwm (by simpa using hwp))
    · rw [hcov' id hid, htag'] at h
      obtain ⟨h1, h2, h3⟩ := st.cov id hid h
      exact ⟨by rw [hl id hid]; exact h1, h2, fun τ hτ => by
        rw [hres' id hid]; exact h3 τ ((hm τ).1 hτ)⟩
  refine ⟨ha.hi.size', hG.mode_le, hbc, hct, htm, hcd, htd,
    (show (S + 1#32).toNat ≤ maxStamp by simp only [maxStamp] at *; omega), ha.stale,
    ?_, fun id hid => by rw [hcov' id hid, htag']; exact hG.cov_le id hid,
    ha.hi.entries hent₂, fun hF => ?_, hG.unsat,
    fun h => absurd (show (2#32 : BitVec 32) = 0#32 from h) (by decide), fun _ => hstep⟩
  · rw [htag']
    have := hG.tag_le
    show (tagOf B).toNat ≤ (S + 1#32).toNat
    simp only [gv, List.getD_cons_succ, List.getD_cons_zero] at this
    omega
  · obtain ⟨τ, hτ⟩ := hG.sat hF
    exact ⟨τ, (hm τ).2 hτ⟩

/-! ## The end of a RAT step -/

/-- **Storing a RAT clause**: when every stored clause containing `-p` that is not covered in
this step has been scanned without finding `-p`, storing the step's clause keeps the database
satisfiable. -/
theorem Good.ratCommit (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) (htc : t ≠ c)
    (hscan : ∀ id < maxId, entryLen B id ≠ 0 → covOf B id ≠ tagOf B →
      ∀ w ∈ entryWords B id, w ≠ 0#32 - pivotOf [2#32, t, c, S, cf, sid, u, n] B) :
    Good xs [1#32, t, t, S, cf, sid, u, n] (recordB B sid c t) := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have st : StepOk [2#32, t, c, S, cf, sid, u, n] B := hG.step rfl
  have hpm := pivot_mem (B := B) (G := [2#32, t, c, S, cf, sid, u, n]) htc hct hcd htd
  have hpv : ValidLit (pivotOf [2#32, t, c, S, cf, sid, u, n] B) := st.valid _ hpm
  refine hG.commit fun τ hτ => ?_
  have hp : (pivotOf [2#32, t, c, S, cf, sid, u, n] B).toInt ∈
      toClause (bufWords [2#32, t, c, S, cf, sid, u, n] B) := List.mem_map_of_mem hpm
  have hrat : ∀ D ∈ dbOf B, -(pivotOf [2#32, t, c, S, cf, sid, u, n] B).toInt ∈ D →
      (dbOf B).Implies (toClause (bufWords [2#32, t, c, S, cf, sid, u, n] B) ++
        D.filter (· != -(pivotOf [2#32, t, c, S, cf, sid, u, n] B).toInt)) := by
    intro D hD hn
    obtain ⟨id, hid, hl, rfl⟩ := mem_dbOf.1 hD
    obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hn
    have hwv : ValidLit w := (hG.entries id hid hl).valid w hw
    have hwp : w = 0#32 - pivotOf [2#32, t, c, S, cf, sid, u, n] B := by
      rw [BitVec.zero_sub]
      exact BitVec.toInt_inj.1 (by rw [hwe, hpv.toInt_neg])
    have hcov : covOf B id = tagOf B := by
      by_contra hne
      exact hscan id hid hl hne w hw hwp
    exact fun τ hτ => (st.cov id hid hcov).2.2 τ hτ
  obtain ⟨τ', hτ'⟩ := CNF.sat_cons_of_rat (G := dbOf B) hp hrat hτ
  simp only [CNF.eval, List.all_cons, Bool.and_eq_true] at hτ'
  exact ⟨τ', hτ'.2, hτ'.1⟩

end Silmaril.Wasm.Examples.LRAT
