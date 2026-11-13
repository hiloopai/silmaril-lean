module

public import Silmaril.Proofs.Wasm.Examples.LRAT.RatLoop

@[expose] public section

/-!
# `rat_begin`, every run

`ratBegin_hwp`: from a store whose view satisfies `Good xs`, every run of the body of
`rat_begin(j)` falls through in a store whose view satisfies `Good xs`. A valid call (in a step,
`j` a stored id, the step's clause not empty, a stamp left) closes the previous group
(`Good.closeGroup` when it reached a conflict), starts the group of `j` with a fresh stamp, and
runs the assignment loop twice (`asg_loop`: the step's clause, then clause `j` without `-p`);
`Good.ratGroup` gives the invariant. Any other call changes nothing. Every profile and host
relation.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Logic.SAT

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}
variable {s : Store H} {xs : List Int} {m t c S cf sid u n : BitVec 32} {B : ByteArray}

/-- The two assignment loops of `rat_begin` and the code between them. -/
def ratLoops : List Instr :=
  [.block .empty [.loop .empty assignLoopBody],
    c32 startBase, lget 6, c32 4, imul, iadd, iload, lget 1, imul, lset 2,
    lget 2, c32 lenBase, lget 6, c32 4, imul, iadd, iload, lget 1, imul, iadd, lset 3,
    c32 0, gget gCstart, lget 1, imul, iload, isub, lset 5,
    .block .empty [.loop .empty assignLoopBody]]

/-- The words of the step's clause without `0` are the step's clause. -/
theorem filter_ne_zero {ws : List (BitVec 32)} (h : ∀ w ∈ ws, ValidLit w) :
    ws.filter (· != 0#32) = ws :=
  List.filter_eq_self.2 fun w hw => by simpa using (h w hw).1

set_option maxHeartbeats 4000000 in
/-- **The loops of a valid `rat_begin(j)`**, from the memory `B₁` after the previous group was
closed. -/
theorem ratBegin_loops (hX : MiOk X) {B₀ B₁ : ByteArray} {G₀ : List (BitVec 32)} {j l7 : BitVec 32}
    (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B₁)
    (hcl : ∀ xs, Good xs G₀ B₀ → Good xs [2#32, t, c, S, cf, sid, u, n] B₁)
    (hS : Shape X s [2#32, t, c, S + 1#32, 0#32, sid, u, n] (wr B₁ 20480 (j + 1#32)))
    (hj : j.toNat < 1024) (hln : entryLen B₁ j.toNat ≠ 0) (htc : t ≠ c)
    (hSt : S.toNat < maxStamp) :
    HWP P host s (fr X.mi [j, 1#32, c, t, 0#32, 0#32, j, l7])
      (vals ([] : List Val).reverse ++ expression ratLoops ++ []) (stepPost X G₀ B₀ []) := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have st : StepOk [2#32, t, c, S, cf, sid, u, n] B₁ := hG.step rfl
  have hcm : c.toNat ≤ memSize := Nat.le_trans hct htm
  have hr : RatSame B₁ (wr B₁ 20480 (j + 1#32)) := RatSame.of_wr _ hs (by decide) (by decide)
  have hS1 : (S + 1#32).toNat = S.toNat + 1 := by simp only [maxStamp] at *; bv_omega
  have hSm1 : (S + 1#32).toNat ≤ maxStamp := by simp only [maxStamp] at *; omega
  have hct' : c.toNat < t.toNat := by
    have : c.toNat ≠ t.toNat := fun h => htc (BitVec.eq_of_toNat_eq h).symm
    omega
  -- the first loop: the step's clause
  have hbuf₂ : words (wr B₁ 20480 (j + 1#32)) c.toNat ((t.toNat - c.toNat) / 4) =
      bufWords [2#32, t, c, S, cf, sid, u, n] B₁ :=
    hr.bufWords (G := [2#32, t, c, S, cf, sid, u, n]) hbc
  have hctx₁ : AsgCtx (wr B₁ 20480 (j + 1#32)) c t ((t.toNat - c.toNat) / 4) := by
    refine ⟨by omega, by omega, Or.inr (by simp only [arenaBase, startBase] at *; omega),
      fun k hk => st.valid _ ?_⟩
    rw [← hbuf₂, mem_words]
    exact ⟨k, hk, rfl⟩
  have ha₀ : AsgOk (wr B₁ 20480 (j + 1#32)) (wr B₁ 20480 (j + 1#32)) (S + 1#32) [] :=
    AsgOk.start hr.size' hSt fun x hx => by
      rw [hr.lo _ (by have := hx.addr.1; omega)
        (by have := hx.addr.2; simp only [startBase, covBase] at *; omega)]
      exact hG.stale x hx
  simp only [ratLoops, expression, List.map_cons, List.map_nil, List.append_nil]
  refine asg_loop hX hS hSm1 hctx₁ ha₀ fun s₁ B₂ x₁ hS₁ ha₁ => ?_
  -- between the loops: the second loop's bounds and `skip = -p`
  have he := hG.entries _ hj hln
  have hsame : ∀ a, arenaBase ≤ a → wd B₂ a = wd B₁ a ∨ a < startBase := fun a ha =>
    Or.inl ((ha₁.hi.wd (by simp only [arenaBase, startBase] at *; omega)).trans (hr.wd_hi ha))
  have hst : wd B₂ (startBase + 4 * j.toNat) = wd B₁ (startBase + 4 * j.toNat) :=
    (ha₁.hi.wd (by omega)).trans (hr.lo _ (by omega) (by simp only [startBase, covBase] at *; omega))
  have hlen : wd B₂ (lenBase + 4 * j.toNat) = wd B₁ (lenBase + 4 * j.toNat) :=
    (ha₁.hi.wd (by simp only [lenBase, startBase]; omega)).trans
      (hr.lo _ (by omega) (by simp only [lenBase, covBase] at *; omega))
  have hpiv : wd B₂ c.toNat = wd B₁ c.toNat := by
    rcases hsame c.toNat hbc with h | h
    · exact h
    · simp only [arenaBase, startBase] at *; omega
  have ea : (BitVec.ofNat 32 startBase + j * 4#32).toNat = startBase + 4 * j.toNat := by
    simp only [startBase]; bv_omega
  have eb : (BitVec.ofNat 32 lenBase + j * 4#32).toNat = lenBase + 4 * j.toNat := by
    simp only [lenBase]; bv_omega
  have hc4 : c.toNat + 4 ≤ 65536 := by
    have := hcd; have := htd; simp only [memSize] at *; omega
  have hend : (wd B₁ (startBase + 4 * j.toNat) + wd B₁ (lenBase + 4 * j.toNat)).toNat =
      (wd B₁ (startBase + 4 * j.toNat)).toNat + 4 * ((wd B₁ (lenBase + 4 * j.toNat)).toNat / 4) := by
    have h1 : entryStart B₁ j.toNat + entryLen B₁ j.toNat ≤ c.toNat := he.end_le
    have h2 := he.dvd
    simp only [entryStart, entryLen, memSize] at h1 h2 hcm
    bv_omega
  wrun [ea, eb, hst, hlen, hpiv, BitVec.mul_one]
  have hw₂ : words (wr B₁ 20480 (j + 1#32)) (wd B₁ (startBase + 4 * j.toNat)).toNat
      ((wd B₁ (lenBase + 4 * j.toNat)).toNat / 4) = entryWords B₁ j.toNat := by
    unfold LRAT.words
    exact List.map_congr_left fun k _ => hr.wd_hi (by have := he.base_le; unfold entryStart at this; omega)
  have hctx₂ : AsgCtx (wr B₁ 20480 (j + 1#32)) (wd B₁ (startBase + 4 * j.toNat))
      (wd B₁ (startBase + 4 * j.toNat) + wd B₁ (lenBase + 4 * j.toNat))
      ((wd B₁ (lenBase + 4 * j.toNat)).toNat / 4) := by
    refine ⟨hend, ?_, Or.inr ?_, fun k hk => he.valid _ ?_⟩
    · have h1 : entryStart B₁ j.toNat + entryLen B₁ j.toNat ≤ c.toNat := he.end_le
      have h2 := he.dvd
      simp only [entryStart, entryLen] at h1 h2; omega
    · have := he.base_le; simp only [entryStart, arenaBase, startBase] at *; omega
    · rw [← hw₂, mem_words]; exact ⟨k, hk, rfl⟩
  refine asg_loop hX (by assumption) hSm1 hctx₂ ha₁ fun s₂ B₃ x₂ hS₂ ha₂ => ?_
  refine w_end (stepPost_of hS₂ fun xs hG₀ => ?_)
  rw [List.append_nil]
  refine (hcl xs hG₀).ratGroup hj hln htc ?_ hSt
  rw [List.nil_append, hbuf₂, filter_ne_zero st.valid, hw₂, BitVec.zero_sub] at ha₂
  exact ha₂

set_option linter.unusedTactic false in
/-- An assignment loop with `p = e` does nothing. -/
theorem asg_skip {G : List (BitVec 32)} (hS : Shape X s G B) {a0 a1 p x skip a6 a7 : BitVec 32}
    {rest : List Admin} {Q : Post H}
    (hk : HWP P host s (fr X.mi [a0, a1, p, p, x, skip, a6, a7]) (vals ([] : List Val).reverse ++ rest)
      Q) :
    HWP P host s (fr X.mi [a0, a1, p, p, x, skip, a6, a7])
      (vals ([] : List Val).reverse ++ .plain (.block .empty [.loop .empty assignLoopBody]) :: rest)
      Q := by
  have _ := hS
  refine w_while (Inv := fun s' f' => s' = s ∧ f' = fr X.mi [a0, a1, p, p, x, skip, a6, a7])
    ⟨rfl, rfl⟩ ?_
  rintro s' f' ⟨rfl, rfl⟩
  rw [assignLoopBody_eq]
  simp only [expression, List.map_cons, List.cons_append, List.nil_append]
  wstep; try wnorm
  wstep; try wnorm
  wstep; try wnorm [le_refl]
  refine w_brIf (fun _ => w_br (whilePost_exit hk)) (fun hc => absurd hc (by decide))

set_option maxHeartbeats 4000000 in
/-- The loops of an invalid `rat_begin`: both are empty and nothing changes. -/
theorem ratBegin_skip (hX : MiOk X) {G : List (BitVec 32)} (hS : Shape X s G B) {j jm : BitVec 32}
    (hjm : jm.toNat < 1024) :
    HWP P host s (fr X.mi [j, 0#32, 0#32, 0#32, 0#32, 0#32, jm, 0#32])
      (vals ([] : List Val).reverse ++ expression ratLoops ++ []) (stepPost X G B []) := by
  simp only [ratLoops, expression, List.map_cons, List.map_nil, List.append_nil]
  refine asg_skip hS ?_
  wrun [BitVec.mul_zero, BitVec.zero_add]
  refine asg_skip (by assumption) ?_
  exact w_end (stepPost_same (by assumption))

/-- The code of `rat_begin(j)` from the view `G`, `B`. -/
abbrev RatBeginHwp (P : Profile) (host : HostSemantics H) (X : Fix H) (s : Store H)
    (G : List (BitVec 32)) (B : ByteArray) (j : BitVec 32) : Prop :=
  HWP P host s (fr X.mi [j, 0, 0, 0, 0, 0, 0, 0])
    (vals ([] : List Val).reverse ++ expression ratBeginBody ++ []) (stepPost X G B [])

/-- Unfold the body of `rat_begin` up to its loops. -/
macro "ratBegin_unfold" : tactic => `(tactic| (
  simp only [RatBeginHwp]
  rw [show ratBeginBody = (ratBeginBody.take 56) ++ ratLoops from rfl]
  simp only [List.take, ratBeginBody, closeCode, expression, List.map_append,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_assoc]))

set_option maxHeartbeats 4000000 in
/-- A valid `rat_begin(j)` after a group with a conflict: close it, then start `j`. -/
theorem ratBegin_close (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) {j : BitVec 32} (hj : j.toNat < 1024)
    (hln : ¬ wd B (lenBase + 4 * j.toNat) = 0#32) (htc : ¬ t = c) (hSt : S.toNat < 536870912)
    (hc : ¬ wd B 20480 = 0#32) (hcf : ¬ cf = 0#32) :
    RatBeginHwp P host X s [2#32, t, c, S, cf, sid, u, n] B j := by
  have eb : (BitVec.ofNat 32 lenBase + j * 4#32).toNat = lenBase + 4 * j.toNat := by
    simp only [lenBase]; bv_omega
  have hc0 : candOf B ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa [candOf] using h))
  obtain ⟨hk, -, -⟩ := (hG.step rfl).cand hc0
  have hcw : candOf B = (wd B 20480).toNat := rfl
  have hw1 : 1 ≤ (wd B 20480).toNat := by omega
  have hw2 : (wd B 20480).toNat ≤ 1024 := by simp only [maxId] at hk; omega
  have hca : (BitVec.ofNat 32 covBase + (wd B 20480 - 1#32) * 4#32).toNat =
      covAddr (candOf B - 1) := by
    unfold candOf; simp only [covAddr, covBase, candAddr]; bv_omega
  ratBegin_unfold
  wrun [eb, hj, hln, htc, hSt, hc, hcf, BitVec.mul_one]
  have e20 : (20480#32 : BitVec 32).toNat = 20480 := rfl
  simp only [hca, e20] at *
  have hG₁ := hG.closeGroup hc0 (by simpa using hcf)
  have hln₁ : entryLen (wr B (covAddr (candOf B - 1)) (tagOf B)) j.toNat ≠ 0 := by
    have hka : covAddr (candOf B - 1) + 4 ≤ memSize := by
      simp only [covAddr, covBase, maxId, memSize] at *; omega
    unfold entryLen
    rw [wd_wr_of _ hG.size hka (Or.inr (by simp only [covAddr, covBase, lenBase, maxId] at *; omega))]
    exact fun h => hln (BitVec.eq_of_toNat_eq h)
  exact ratBegin_loops hX hG₁ (fun _ hG' => hG'.closeGroup hc0 (by simpa using hcf))
    (by assumption) hj hln₁ htc hSt

theorem entryLen_ne {j : BitVec 32} (hln : ¬ wd B (lenBase + 4 * j.toNat) = 0#32) :
    entryLen B j.toNat ≠ 0 :=
  fun h => hln (BitVec.eq_of_toNat_eq h)

set_option maxHeartbeats 4000000 in
/-- A valid `rat_begin(j)` with no group to close. -/
theorem ratBegin_open (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) {j : BitVec 32} (hj : j.toNat < 1024)
    (hln : ¬ wd B (lenBase + 4 * j.toNat) = 0#32) (htc : ¬ t = c) (hSt : S.toNat < 536870912)
    (hcl : wd B 20480 = 0#32 ∨ cf = 0#32) :
    RatBeginHwp P host X s [2#32, t, c, S, cf, sid, u, n] B j := by
  have eb : (BitVec.ofNat 32 lenBase + j * 4#32).toNat = lenBase + 4 * j.toNat := by
    simp only [lenBase]; bv_omega
  have e20 : (20480#32 : BitVec 32).toNat = 20480 := rfl
  ratBegin_unfold
  rcases hcl with hc | hcf
  · wrun [eb, hj, hln, htc, hSt, hc, BitVec.mul_one]
    simp only [e20] at *
    exact ratBegin_loops hX hG (fun _ h => h) (by assumption) hj (entryLen_ne hln) htc hSt
  · subst hcf
    wrun [eb, hj, hln, htc, hSt, BitVec.mul_one]
    simp only [e20] at *
    exact ratBegin_loops hX hG (fun _ h => h) (by assumption) hj (entryLen_ne hln) htc hSt

set_option maxHeartbeats 4000000 in
/-- `rat_begin(j)` outside a step, or with `j` out of range: nothing changes. -/
theorem ratBegin_idle (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    {j : BitVec 32} (h : ¬ (m = 2#32 ∧ j.toNat < 1024)) :
    RatBeginHwp P host X s [m, t, c, S, cf, sid, u, n] B j := by
  ratBegin_unfold
  by_cases hm : m = 2#32
  · subst hm
    have hj : ¬ j.toNat < 1024 := fun hj => h ⟨rfl, hj⟩
    have hj' := eq_false hj
    wrun [hj', BitVec.mul_zero, BitVec.zero_mul, BitVec.add_zero, BitVec.zero_add]
    exact ratBegin_skip hX (by assumption) (by decide)
  · wrun [hm, BitVec.mul_zero, BitVec.zero_mul, BitVec.add_zero, BitVec.zero_add]
    exact ratBegin_skip hX (by assumption) (by decide)

set_option maxHeartbeats 4000000 in
/-- A `rat_begin(j)` in a step that fails one of its other checks: nothing changes. -/
theorem ratBegin_fail (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    {j : BitVec 32} (hj : j.toNat < 1024)
    (h : ¬ (¬ wd B (lenBase + 4 * j.toNat) = 0#32 ∧ ¬ t = c ∧ S.toNat < 536870912)) :
    RatBeginHwp P host X s [2#32, t, c, S, cf, sid, u, n] B j := by
  have eb : (BitVec.ofNat 32 lenBase + j * 4#32).toNat = lenBase + 4 * j.toNat := by
    simp only [lenBase]; bv_omega
  ratBegin_unfold
  by_cases hln : wd B (lenBase + 4 * j.toNat) = 0#32
  · wrun [eb, hj, hln, BitVec.mul_one, BitVec.mul_zero, BitVec.zero_mul, BitVec.add_zero,
      BitVec.zero_add]
    exact ratBegin_skip hX (by assumption) hj
  by_cases htc : t = c
  · subst htc
    wrun [eb, hj, hln, BitVec.mul_one, BitVec.mul_zero, BitVec.zero_mul, BitVec.add_zero,
      BitVec.zero_add]
    exact ratBegin_skip hX (by assumption) hj
  have hSt : ¬ S.toNat < 536870912 := fun hS' => h ⟨hln, htc, hS'⟩
  have hSt' := eq_false hSt
  wrun [eb, hj, hln, htc, hSt', BitVec.mul_one, BitVec.mul_zero, BitVec.zero_mul, BitVec.add_zero,
    BitVec.zero_add]
  exact ratBegin_skip hX (by assumption) hj

/-- **`rat_begin(j)`, every run.** -/
theorem ratBegin_hwp (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [m, t, c, S, cf, sid, u, n] B) (j : BitVec 32) :
    RatBeginHwp P host X s [m, t, c, S, cf, sid, u, n] B j := by
  by_cases hmj : m = 2#32 ∧ j.toNat < 1024
  · obtain ⟨rfl, hj⟩ := hmj
    by_cases hv : ¬ wd B (lenBase + 4 * j.toNat) = 0#32 ∧ ¬ t = c ∧ S.toNat < 536870912
    · obtain ⟨hln, htc, hSt⟩ := hv
      by_cases hcl : ¬ wd B 20480 = 0#32 ∧ ¬ cf = 0#32
      · exact ratBegin_close hX hS hG hj hln htc hSt hcl.1 hcl.2
      · exact ratBegin_open hX hS hG hj hln htc hSt (by tauto)
    · exact ratBegin_fail hX hS hj hv
  · exact ratBegin_idle hX hS hmj

end Silmaril.Wasm.Examples.LRAT
