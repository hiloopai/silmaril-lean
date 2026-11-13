module

public import Silmaril.Proofs.Wasm.Examples.LRAT.GoodBase

@[expose] public section

/-!
# The invariant across a RUP hint

`step_hint(h)` scans clause `h` (stored, so true in every model of the database) and counts its
literals that are not assigned false. The two effects keep `Good`:

* `Good.hintConfl`: every literal of the clause is assigned false: every model of the database
  that falsifies the target (the step's clause, or a RAT resolvent) would falsify clause `h`, so
  there is none, and the database implies the target (the conflict flag is set);
* `Good.hintUnit`: all literals but `l` are assigned false: such a model must make `l` true,
  so assigning `l` true (and `-l` false) keeps the agreement (`Good.hiSame`: writes to the
  literal values only).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Logic.SAT

variable {xs : List Int} {t c S cf sid u n : BitVec 32} {B : ByteArray}

/-- **A step after writes to the literal values only**, given the bound on the values and
the new agreement. -/
theorem Good.hiSame {G : List (BitVec 32)} {B' : ByteArray} (hG : Good xs G B)
    (hm : gv G gMode = 2#32) (h : HiSame B B')
    (hst : ∀ x, ValidLit x → (wd B' (litAddr x)).toNat ≤ 2 * (gv G gStamp).toNat + 1)
    (hag : ∀ τ, Models τ B → Clause.eval τ (targetOf G B) = false → Agrees τ B' (gv G gStamp)) :
    Good xs G B' := by
  have st : StepOk G B := hG.step hm
  have hbase : startBase ≤ (gv G gCstart).toNat := by
    have := hG.base_le; simp only [arenaBase, startBase] at *; omega
  obtain ⟨-, -, htag, hcov, -⟩ := h.step hG.entries hbase fun hc => (st.cand hc).1
  refine ⟨h.size', hG.mode_le, hG.base_le, hG.cstart_le, hG.top_le, hG.cstart_dvd, hG.top_dvd,
    hG.stamp_le, hst, htag ▸ hG.tag_le, fun id hid => by rw [hcov, htag]; exact hG.cov_le id hid,
    h.entries hG.entries, fun hF => ?_, hG.unsat, fun h0 => absurd (h0.symm.trans hm) (by decide),
    fun _ => st.hiSame h hG.entries hbase hag⟩
  obtain ⟨τ, hτ⟩ := hG.sat hF
  exact ⟨τ, (h.models hG.entries).2 hτ⟩

/-- A model of the database falsifying the target makes the unit literal true. -/
theorem hint_unit_true {G : List (BitVec 32)} {τ : Assignment} {id : Nat}
    {l : BitVec 32} (st : StepOk G B) (he : EntryOk B c.toNat id) (hid : id < maxId)
    (hlen : entryLen B id ≠ 0) (hτ : Models τ B)
    (hf : Clause.eval τ (targetOf G B) = false)
    (hrest : ∀ w ∈ entryWords B id, w ≠ l → wd B (litAddr w) = gv G gStamp * 2#32) :
    Lit.eval τ l.toInt = true := by
  have ha := st.agrees τ hτ hf
  have hc : (entryClause B id).eval τ = true := hτ.entry hid hlen
  rw [entryClause, Clause.eval_eq_true_iff] at hc
  obtain ⟨_, hw', hlt⟩ := hc
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
  by_cases hwl : w = l
  · rw [← hwl]; exact hlt
  · rw [(ha w (he.valid w hw)).1 (hrest w hw hwl)] at hlt
    exact absurd hlt Bool.false_ne_true

/-- All literals of a stored clause are false: conflict. -/
theorem Good.hintConfl {id : Nat} (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B)
    (hid : id < maxId) (hlen : entryLen B id ≠ 0)
    (hall : ∀ w ∈ entryWords B id, wd B (litAddr w) = S * 2#32) :
    Good xs [2#32, t, c, S, 1#32, sid, u, n] B := by
  have st := hG.step rfl
  have he := hG.entries id hid hlen
  have hconfl : ∀ τ, Models τ B → Clause.eval τ (targetOf [2#32, t, c, S, 1#32, sid, u, n] B) =
      true := by
    intro τ hτ
    by_contra hf
    have hf' : Clause.eval τ (targetOf [2#32, t, c, S, cf, sid, u, n] B) = false :=
      Bool.eq_false_iff.2 hf
    have ha := st.agrees τ hτ hf'
    have hc : (entryClause B id).eval τ = true := hτ.entry hid hlen
    rw [entryClause, Clause.eval_eq_true_iff] at hc
    obtain ⟨_, hw', hlt⟩ := hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    rw [(ha w (he.valid w hw)).1 (hall w hw)] at hlt
    exact absurd hlt Bool.false_ne_true
  exact ⟨hG.size, hG.mode_le, hG.base_le, hG.cstart_le, hG.top_le, hG.cstart_dvd, hG.top_dvd,
    hG.stamp_le, hG.stale, hG.tag_le, hG.cov_le, hG.entries, hG.sat, hG.unsat,
    fun h => absurd (show (2#32 : BitVec 32) = 0#32 from h) (by decide),
    fun _ => ⟨st.id_lt, st.valid, st.cand, fun _ => hconfl, st.agrees, st.cov⟩⟩

/-- All literals of a stored clause but `l` are false: `l` becomes true. -/
theorem Good.hintUnit {id : Nat} {l : BitVec 32} (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B)
    (hid : id < maxId) (hlen : entryLen B id ≠ 0) (hl : l ∈ entryWords B id)
    (hrest : ∀ w ∈ entryWords B id, w ≠ l → wd B (litAddr w) = S * 2#32) :
    Good xs [2#32, t, c, S, cf, sid, u, n]
      (wr (wr B (litAddr l) (S * 2#32 + 1#32)) (negAddr l) (S * 2#32)) := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have st : StepOk [2#32, t, c, S, cf, sid, u, n] B := hG.step rfl
  have he : EntryOk B c.toNat id := hG.entries id hid hlen
  have hlv : ValidLit l := he.valid l hl
  have hstale : ∀ x, ValidLit x → (wd (wr (wr B (litAddr l) (S * 2#32 + 1#32)) (negAddr l)
      (S * 2#32)) (litAddr x)).toNat ≤ 2 * S.toNat + 1 :=
    stale_assign hs hlv hG.stale
      (by simp only [maxStamp] at hSm; show (S * 2#32 + 1#32).toNat ≤ 2 * S.toNat + 1; bv_omega)
      (by simp only [maxStamp] at hSm; show (S * 2#32).toNat ≤ 2 * S.toNat + 1; bv_omega)
  refine hG.hiSame rfl (HiSame.assign hs hlv) hstale fun τ hτ hf => ?_
  have hlt : Lit.eval τ l.toInt = true := hint_unit_true st he hid hlen hτ hf hrest
  exact (st.agrees τ hτ hf).assign hs hlv (fun e => absurd e.symm (stamp_ne S))
    (fun _ => hlt) (fun _ => hlt) (fun e => absurd e (stamp_ne S))

end Silmaril.Wasm.Examples.LRAT
