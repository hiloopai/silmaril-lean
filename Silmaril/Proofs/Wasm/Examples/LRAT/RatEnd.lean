module

public import Silmaril.Proofs.Wasm.Examples.LRAT.RatBegin

@[expose] public section

/-!
# `rat_end`, every run

`ratEnd_hwp`: from a store whose view satisfies `Good xs`, every run of the body of `rat_end()`
falls through in a store whose view satisfies `Good xs`. A valid call (in a step, the step's
clause not empty) closes the last group (`Good.closeGroup`), scans every stored clause not
covered in this step for `-p` (the outer loop over ids, `outer_loop`, around `scan_loop`) and
stores the step's clause if none contains it (`Good.ratCommit`), then leaves the step
(`Good.abort` otherwise). Any other call changes nothing. Every profile and host relation.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Logic.SAT

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}
variable {s : Store H} {xs : List Int} {m t c S cf sid u n : BitVec 32} {B : ByteArray}
variable {rest : List Admin} {Q : Post H}

/-- Clause `id` is stored and not covered in this step: the scan looks at it. -/
def Uncov (B : ByteArray) (id : Nat) : Prop := entryLen B id ≠ 0 ∧ covOf B id ≠ tagOf B

/-- What the scan establishes for the ids below `i`: with `bad = 0`, no clause it looks at
contains `skip`. -/
def ScanDone (B : ByteArray) (skip bad : BitVec 32) (i : Nat) : Prop :=
  bad = 0#32 → ∀ id < i, Uncov B id → ∀ w ∈ entryWords B id, w ≠ skip

/-- One iteration of the outer loop after its exit test. -/
def outerStep : List Instr :=
  [c32 lenBase, lget 1, c32 4, imul, iadd, iload, c32 0, ine,
    c32 covBase, lget 1, c32 4, imul, iadd, iload, c32 tagAddr, iload, ine, iand, lset 8,
    c32 startBase, lget 1, c32 4, imul, iadd, iload, lget 8, imul, lset 3,
    lget 3, c32 lenBase, lget 1, c32 4, imul, iadd, iload, lget 8, imul, iadd, lset 4,
    .block .empty [.loop .empty scanInnerBody],
    lget 1, c32 1, iadd, lset 1, .br ⟨0⟩]

theorem scanOuterBody_eq : scanOuterBody = [lget 1, lget 2, igeu, .brIf ⟨1⟩] ++ outerStep := rfl

/-- The invariant of the outer loop. -/
def OuterInv (X : Fix H) (G : List (BitVec 32)) (B : ByteArray) (skip l7 : BitVec 32) :
    Store H → Frame → Prop := fun s' f' =>
  Shape X s' G B ∧ ∃ (i p e bad u8 x : BitVec 32),
    f' = fr X.mi [1#32, i, 1024#32, p, e, skip, bad, l7, u8, x] ∧ i.toNat ≤ 1024 ∧
    ScanDone B skip bad i.toNat

variable {G : List (BitVec 32)} {skip l7 : BitVec 32}

/-- The end of one id: the scan of clause `i` extends `ScanDone` to `i + 1`. -/
theorem ScanDone.succ {i : Nat} {bad bad' : BitVec 32} (h : ScanDone B skip bad i)
    (hi : bad' = 0#32 → bad = 0#32 ∧ (Uncov B i → ∀ w ∈ entryWords B i, w ≠ skip)) :
    ScanDone B skip bad' (i + 1) := by
  intro h0 id hid hu
  rcases Nat.lt_succ_iff_lt_or_eq.1 hid with hid | rfl
  · exact h (hi h0).1 id hid hu
  · exact (hi h0).2 hu

/-- The words of a stored clause, as the scan computes them. -/
theorem EntryOk.span {cs id : Nat} (he : EntryOk B cs id) (hcs : cs ≤ memSize) :
    (wd B (startBase + 4 * id) + wd B (lenBase + 4 * id)).toNat =
      (wd B (startBase + 4 * id)).toNat + 4 * ((wd B (lenBase + 4 * id)).toNat / 4) ∧
    (wd B (startBase + 4 * id)).toNat + 4 * ((wd B (lenBase + 4 * id)).toNat / 4) ≤ memSize := by
  have h1 := he.end_le
  have h2 := he.dvd
  simp only [entryStart, entryLen, memSize] at h1 h2 hcs
  constructor
  · bv_omega
  · simp only [memSize]; omega

set_option maxHeartbeats 4000000 in
/-- **One iteration of the outer loop**: clause `i` is scanned if it is uncovered. -/
theorem outer_iter (hX : MiOk X) (hS : Shape X s G B)
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B memSize id)
    {i p e bad u8 x : BitVec 32} (hi : i.toNat < 1024) (hd : ScanDone B skip bad i.toNat) :
    HWP P host s (fr X.mi [1#32, i, 1024#32, p, e, skip, bad, l7, u8, x])
      (vals ([] : List Val).reverse ++ expression outerStep)
      (whilePost P host (OuterInv X G B skip l7) rest Q) := by
  have ea : (BitVec.ofNat 32 startBase + i * 4#32).toNat = startBase + 4 * i.toNat := by
    simp only [startBase]; bv_omega
  have eb : (BitVec.ofNat 32 lenBase + i * 4#32).toNat = lenBase + 4 * i.toNat := by
    simp only [lenBase]; bv_omega
  have ec : (BitVec.ofNat 32 covBase + i * 4#32).toNat = covBase + 4 * i.toNat := by
    simp only [covBase]; bv_omega
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  have hcont : ∀ (bad' : BitVec 32) (s' : Store H) (p' e' u8' x' : BitVec 32), Shape X s' G B →
      (bad' = 0#32 → bad = 0#32 ∧ (Uncov B i.toNat → ∀ w ∈ entryWords B i.toNat, w ≠ skip)) →
      HWP P host s' (fr X.mi [1#32, i, 1024#32, p', e', skip, bad', l7, u8', x'])
        (vals ([] : List Val).reverse ++ expression [lget 1, c32 1, iadd, lset 1, .br ⟨0⟩])
        (whilePost P host (OuterInv X G B skip l7) rest Q) := by
    intro bad' s' p' e' u8' x' hS' hb
    simp only [expression, List.map_cons, List.map_nil]
    wrun
    exact w_br (whilePost_cont ⟨hS', i + 1#32, p', e', bad', u8', x', rfl, by omega,
      hi1 ▸ hd.succ hb⟩)
  simp only [outerStep, expression, List.map_cons, List.map_nil]
  by_cases hl : wd B (lenBase + 4 * i.toNat) = 0#32
  · wrun [ea, eb, ec, hl, BitVec.mul_zero, BitVec.zero_add]
    refine scan_loop (N := 0) hX (by assumption) rfl (by simp) fun s' bad' x' hS' hb => ?_
    have hl0 : entryLen B i.toNat = 0 := by unfold entryLen; rw [hl]; rfl
    exact hcont bad' s' _ _ _ x' hS' fun h0 => ⟨(hb h0).1, fun hu => absurd hl0 hu.1⟩
  by_cases hcv : wd B (covBase + 4 * i.toNat) = wd B tagAddr
  · wrun [ea, eb, ec, hl, hcv, BitVec.mul_zero, BitVec.zero_add]
    refine scan_loop (N := 0) hX (by assumption) rfl (by simp) fun s' bad' x' hS' hb => ?_
    exact hcont bad' s' _ _ _ x' hS' fun h0 => ⟨(hb h0).1, fun hu => absurd hcv hu.2⟩
  · obtain ⟨hend, hb⟩ := (hent _ (by simp only [maxId]; omega)
      (fun h => hl (BitVec.eq_of_toNat_eq h))).span le_rfl
    wrun [ea, eb, ec, hl, hcv, BitVec.mul_one]
    refine scan_loop hX (by assumption) hend hb fun s' bad' x' hS' hsc => ?_
    refine hcont bad' s' _ _ _ x' hS' fun h0 => ⟨(hsc h0).1, fun _ w hw => ?_⟩
    obtain ⟨k, hk, rfl⟩ := mem_words.1 hw
    exact (hsc h0).2 k hk

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- **The outer loop of the scan**, over the ids `0 … 1023`. -/
theorem outer_loop (hX : MiOk X) (hS : Shape X s G B)
    (hent : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B memSize id) {p e u8 x : BitVec 32}
    (hk : ∀ s' (p' e' bad' u8' x' : BitVec 32), Shape X s' G B → ScanDone B skip bad' 1024 →
      HWP P host s' (fr X.mi [1#32, 1024#32, 1024#32, p', e', skip, bad', l7, u8', x'])
        (vals ([] : List Val).reverse ++ rest) Q) :
    HWP P host s (fr X.mi [1#32, 0#32, 1024#32, p, e, skip, 0#32, l7, u8, x])
      (vals ([] : List Val).reverse ++ .plain (.block .empty [.loop .empty scanOuterBody]) :: rest)
      Q := by
  refine w_while (Inv := OuterInv X G B skip l7)
    ⟨hS, 0#32, p, e, 0#32, u8, x, rfl, by decide, fun _ _ h => absurd h (by simp)⟩ ?_
  rintro s' f' ⟨hS', i, p', e', bad, u8', x', rfl, hi, hd⟩
  rw [scanOuterBody_eq]
  simp only [expression, List.map_cons, List.cons_append, List.nil_append]
  wstep; try wnorm
  wstep; try wnorm
  wstep; try wnorm
  refine w_brIf (fun hx => ?_) (fun hx => ?_)
  · have hi' : i = 1024#32 := BitVec.eq_of_toNat_eq (by have := b32_ne_zero.1 hx; simp at *; omega)
    subst hi'
    exact w_br (whilePost_exit (hk s' p' e' bad u8' x' hS' hd))
  · have hi' : i.toNat < 1024 := by have := b32_eq_zero.1 hx; simp at *; omega
    exact outer_iter hX hS' hent hi' hd

set_option linter.unusedTactic false in
/-- An outer loop with `i = e₀` does nothing. -/
theorem outer_skip (hS : Shape X s G B) {a0 i a3 a4 a5 a6 a7 a8 a9 : BitVec 32}
    (hk : HWP P host s (fr X.mi [a0, i, i, a3, a4, a5, a6, a7, a8, a9])
      (vals ([] : List Val).reverse ++ rest) Q) :
    HWP P host s (fr X.mi [a0, i, i, a3, a4, a5, a6, a7, a8, a9])
      (vals ([] : List Val).reverse ++ .plain (.block .empty [.loop .empty scanOuterBody]) :: rest)
      Q := by
  have _ := hS
  refine w_while (Inv := fun s' f' => s' = s ∧ f' = fr X.mi [a0, i, i, a3, a4, a5, a6, a7, a8, a9])
    ⟨rfl, rfl⟩ ?_
  rintro s' f' ⟨rfl, rfl⟩
  rw [scanOuterBody_eq]
  simp only [expression, List.map_cons, List.cons_append, List.nil_append]
  wstep; try wnorm
  wstep; try wnorm
  wstep; try wnorm [le_refl]
  refine w_brIf (fun _ => w_br (whilePost_exit hk)) (fun hc => absurd hc (by decide))

/-- The scan of `rat_end` and the code after it. -/
def ratEndRest : List Instr :=
  [.block .empty [.loop .empty scanOuterBody],
    lget 0, lget 6, ieqz, iand, ifThen [c32 startBase, gget gStepId, c32 4, imul, iadd,
      gget gCstart, istore, c32 lenBase, gget gStepId, c32 4, imul, iadd, gget gTop, gget gCstart,
      isub, istore, gget gTop, gset gCstart],
    lget 0, ifThen [gget gCstart, gset gTop, c32 1, gset gMode]]

theorem ratEndBody_eq : ratEndBody = ratEndBody.take 32 ++ ratEndRest := rfl

set_option maxHeartbeats 4000000 in
/-- **The scan and the end of a valid `rat_end`**, from the memory `B₁` after the last group was
closed. -/
theorem ratEnd_scan (hX : MiOk X) {B₀ B₁ : ByteArray} {G₀ : List (BitVec 32)}
    (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B₁)
    (hcl : ∀ xs, Good xs G₀ B₀ → Good xs [2#32, t, c, S, cf, sid, u, n] B₁)
    (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B₁) (htc : t ≠ c) {l7 : BitVec 32} :
    HWP P host s (fr X.mi [1#32, 0#32, 1024#32, 0#32, 0#32, 0#32 - wd B₁ c.toNat, 0#32, l7, 0#32,
      0#32]) (vals ([] : List Val).reverse ++ expression ratEndRest ++ []) (stepPost X G₀ B₀ []) := by
  obtain ⟨hs, hbc, hct, htm, hcd, htd, hSm⟩ := hG.facts
  have hsid : sid.toNat < 1024 := (hG.step rfl).id_lt
  have hent : ∀ id < maxId, entryLen B₁ id ≠ 0 → EntryOk B₁ memSize id := fun id hid hl =>
    (hG.entries id hid hl).weaken (Nat.le_trans hct htm)
  simp only [ratEndRest, expression, List.map_cons, List.map_nil, List.append_nil]
  have ha : (BitVec.ofNat 32 startBase + sid * 4#32).toNat = startBase + 4 * sid.toNat := by
    simp only [startBase]; bv_omega
  have hb : (BitVec.ofNat 32 lenBase + sid * 4#32).toNat = lenBase + 4 * sid.toNat := by
    simp only [lenBase]; bv_omega
  refine outer_loop hX hS hent fun s' p' e' bad' u8' x' hS' hd => ?_
  by_cases hbad : bad' = 0#32
  · subst hbad
    wrun
    simp only [ha, hb] at *
    exact w_end (stepPost_of (by assumption) fun xs hG₀ => by
      rw [List.append_nil]
      exact (hcl xs hG₀).ratCommit htc fun id hid hl hc w hw => hd rfl id hid ⟨hl, hc⟩ w hw)
  · wrun [hbad]
    exact w_end (stepPost_of (by assumption) fun xs hG₀ => by
      rw [List.append_nil]; exact (hcl xs hG₀).abort)

/-- The code of `rat_end` from the view `G`, `B`. -/
abbrev RatEndHwp (P : Profile) (host : HostSemantics H) (X : Fix H) (s : Store H)
    (G : List (BitVec 32)) (B : ByteArray) : Prop :=
  HWP P host s (fr X.mi [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    (vals ([] : List Val).reverse ++ expression ratEndBody ++ []) (stepPost X G B [])

/-- Unfold the body of `rat_end` up to its scan. -/
macro "ratEnd_unfold" : tactic => `(tactic| (
  simp only [RatEndHwp]
  rw [ratEndBody_eq]
  simp only [List.take, ratEndBody, closeCode, expression, List.map_append,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_assoc]))

set_option maxHeartbeats 4000000 in
/-- A valid `rat_end` after a group with a conflict: close it, then scan. -/
theorem ratEnd_close (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) (htc : ¬ t = c) (hc : ¬ wd B 20480 = 0#32)
    (hcf : ¬ cf = 0#32) : RatEndHwp P host X s [2#32, t, c, S, cf, sid, u, n] B := by
  have hc0 : candOf B ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa [candOf] using h))
  obtain ⟨hk, -, -⟩ := (hG.step rfl).cand hc0
  have hcw : candOf B = (wd B 20480).toNat := rfl
  have hw1 : 1 ≤ (wd B 20480).toNat := by omega
  have hw2 : (wd B 20480).toNat ≤ 1024 := by simp only [maxId] at hk; omega
  have hca : (BitVec.ofNat 32 covBase + (wd B 20480 - 1#32) * 4#32).toNat =
      covAddr (candOf B - 1) := by
    unfold candOf; simp only [covAddr, covBase, candAddr]; bv_omega
  have hc4 : c.toNat + 4 ≤ 65536 := by
    obtain ⟨-, -, hct, htm, hcd, htd, -⟩ := hG.facts
    have : c.toNat ≠ t.toNat := fun h => htc (BitVec.eq_of_toNat_eq h).symm
    simp only [memSize] at *; omega
  have hcf' : cf ≠ 0#32 := hcf
  ratEnd_unfold
  wrun [htc, hc, hcf, BitVec.mul_one]
  simp only [hca] at *
  exact ratEnd_scan hX (hG.closeGroup hc0 hcf') (fun _ hG' => hG'.closeGroup hc0 hcf')
    (by assumption) htc

set_option maxHeartbeats 4000000 in
/-- A valid `rat_end` with no group to close. -/
theorem ratEnd_open (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) (htc : ¬ t = c)
    (hcl : wd B 20480 = 0#32 ∨ cf = 0#32) : RatEndHwp P host X s [2#32, t, c, S, cf, sid, u, n] B := by
  have hc4 : c.toNat + 4 ≤ 65536 := by
    obtain ⟨-, -, hct, htm, hcd, htd, -⟩ := hG.facts
    have : c.toNat ≠ t.toNat := fun h => htc (BitVec.eq_of_toNat_eq h).symm
    simp only [memSize] at *; omega
  ratEnd_unfold
  rcases hcl with hc | hcf
  · wrun [htc, hc, BitVec.mul_one]
    exact ratEnd_scan hX hG (fun _ h => h) (by assumption) htc
  · subst hcf
    wrun [htc, BitVec.mul_one]
    exact ratEnd_scan hX hG (fun _ h => h) (by assumption) htc

set_option maxHeartbeats 4000000 in
/-- `rat_end` outside a step or with an empty clause: nothing changes. -/
theorem ratEnd_idle (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hv : ¬ (m = 2#32 ∧ ¬ t = c)) : RatEndHwp P host X s [m, t, c, S, cf, sid, u, n] B := by
  ratEnd_unfold
  by_cases hm : m = 2#32
  · subst hm
    have htc : t = c := by tauto
    subst htc
    wrun [BitVec.mul_zero, BitVec.zero_mul]
    refine outer_skip (by assumption) ?_
    wrun
    exact w_end (stepPost_same (by assumption))
  · wrun [hm, BitVec.mul_zero, BitVec.zero_mul]
    refine outer_skip (by assumption) ?_
    wrun
    exact w_end (stepPost_same (by assumption))

/-- **`rat_end`, every run.** -/
theorem ratEnd_hwp (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [m, t, c, S, cf, sid, u, n] B) :
    RatEndHwp P host X s [m, t, c, S, cf, sid, u, n] B := by
  by_cases hv : m = 2#32 ∧ ¬ t = c
  · obtain ⟨rfl, htc⟩ := hv
    by_cases hcl : ¬ wd B 20480 = 0#32 ∧ ¬ cf = 0#32
    · exact ratEnd_close hX hS hG htc hcl.1 hcl.2
    · exact ratEnd_open hX hS hG htc (by tauto)
  · exact ratEnd_idle hX hS hv

end Silmaril.Wasm.Examples.LRAT
