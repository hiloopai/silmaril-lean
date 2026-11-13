module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Steps
public import Silmaril.Proofs.Wasm.Examples.LRAT.Loop
public import Silmaril.Proofs.Wasm.Examples.LRAT.GoodHint

@[expose] public section

/-!
# `step_hint`, every run

`stepHint_hwp`: from a store whose view satisfies `Good xs`, every run of the body of
`step_hint(h)` falls through in a store whose view satisfies `Good xs`. The scan is a while loop
(`w_while`) with the invariant `ScanOk`: after `k` words of clause `h`, the count `cnt` and the
last literal `last` summarise which of them are not assigned false. Every profile and host
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

/-- The scan summary after the first `k` words from byte `p₀`: `cnt` (at most `k`) counts the
literals not assigned false; with `cnt = 0` all are false, with `cnt = 1` all but `last` are. -/
def ScanOk (B : ByteArray) (p₀ : Nat) (S : BitVec 32) (k : Nat) (cnt last : BitVec 32) : Prop :=
  cnt.toNat ≤ k ∧
  (cnt = 0#32 → ∀ j < k, wd B (litAddr (wd B (p₀ + 4 * j))) = S * 2#32) ∧
  (cnt = 1#32 → (∃ j < k, wd B (p₀ + 4 * j) = last) ∧
    ∀ j < k, wd B (p₀ + 4 * j) ≠ last → wd B (litAddr (wd B (p₀ + 4 * j))) = S * 2#32)

theorem ScanOk.zero {p₀ : Nat} : ScanOk B p₀ S 0 0#32 0#32 :=
  ⟨by simp, fun _ j hj => absurd hj (Nat.not_lt_zero j), fun h => absurd h (by decide)⟩

/-- A literal assigned false: the count and the last literal stay. -/
theorem ScanOk.step_false {p₀ k : Nat} {cnt last x : BitVec 32} (h : ScanOk B p₀ S k cnt last)
    (hx : wd B (p₀ + 4 * k) = x) (hf : wd B (litAddr x) = S * 2#32) :
    ScanOk B p₀ S (k + 1) cnt last := by
  obtain ⟨hle, h0, h1⟩ := h
  refine ⟨by omega, fun hc j hj => ?_, fun hc => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h0 hc j hj
    · rw [hx]; exact hf
  · obtain ⟨⟨j, hj, hjl⟩, hr⟩ := h1 hc
    refine ⟨⟨j, by omega, hjl⟩, fun j' hj' hne => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
    · exact hr j' hj' hne
    · rw [hx]; exact hf

/-- A literal not assigned false: it is counted and remembered. -/
theorem ScanOk.step_true {p₀ k : Nat} {cnt last x : BitVec 32} (h : ScanOk B p₀ S k cnt last)
    (hk : k < 2 ^ 30) (hx : wd B (p₀ + 4 * k) = x) :
    ScanOk B p₀ S (k + 1) (cnt + 1#32) x := by
  obtain ⟨hle, h0, -⟩ := h
  have hlt : cnt.toNat < 2 ^ 31 := by omega
  have hc1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by bv_omega
  refine ⟨by omega, fun hc => absurd hc (by intro h'; rw [h'] at hc1; simp at hc1), fun hc => ?_⟩
  have hc0 : cnt = 0#32 := by
    have : (cnt + 1#32).toNat = 1 := by rw [hc]; rfl
    apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨⟨k, by omega, hx⟩, fun j hj hne => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact h0 hc0 j hj
  · exact absurd hx hne

/-- **One word of the scan**, in the form the code computes it. -/
theorem ScanOk.step {p₀ k : Nat} {cnt last x : BitVec 32} (h : ScanOk B p₀ S k cnt last)
    (hk : k < 2 ^ 30) (hx : wd B (p₀ + 4 * k) = x) :
    ScanOk B p₀ S (k + 1) (cnt + b32 (¬ wd B (litAddr x) = S * 2#32))
      (last + b32 (¬ wd B (litAddr x) = S * 2#32) * (x - last)) := by
  by_cases hf : wd B (litAddr x) = S * 2#32
  · have e : b32 (¬ wd B (litAddr x) = S * 2#32) = 0#32 := b32_neg (not_not.2 hf)
    rw [e, BitVec.add_zero, BitVec.zero_mul, BitVec.add_zero]
    exact h.step_false hx hf
  · have e : b32 (¬ wd B (litAddr x) = S * 2#32) = 1#32 := b32_pos hf
    rw [e, BitVec.one_mul, show last + (x - last) = x by bv_omega]
    exact h.step_true hk hx

/-- The updates after the scan: a conflict, or a unit literal made true. -/
def hintPost : List Instr :=
  [lget 1, lget 4, ieqz, iand, ifThen [c32 1, gset gConfl]] ++
  [lget 1, lget 4, c32 1, ieq, iand, ifThen (assignCode 5 1)]

/-- One iteration of the scan after its exit test. -/
def hintStep : List Instr :=
  [lget 2, iload, lset 6] ++ valAddrCode 6 ++ [iload] ++ stamp2Code ++ [ine, lset 7,
    lget 4, lget 7, iadd, lset 4,
    lget 5, lget 7, lget 6, lget 5, isub, imul, iadd, lset 5,
    lget 2, c32 4, iadd, lset 2, .br ⟨0⟩]

theorem hintLoopBody_eq : hintLoopBody = [lget 2, lget 3, igeu, .brIf ⟨1⟩] ++ hintStep := rfl

/-- The updates after the scan, from the frame `L`. -/
abbrev HintPostHwp (P : Profile) (host : HostSemantics H) (X : Fix H) (s : Store H)
    (L G : List (BitVec 32)) (B : ByteArray) : Prop :=
  HWP P host s (fr X.mi L) (vals ([] : List Val).reverse ++ expression hintPost ++ [])
    (stepPost X G B [])

/-- Unfold the updates after the scan. -/
macro "hintPost_unfold" : tactic => `(tactic| simp only [HintPostHwp, hintPost, assignCode,
  valAddrCode, negAddrCode, stamp2Code, expression, List.cons_append, List.nil_append,
  List.map_cons, List.map_nil, List.append_nil])

set_option maxHeartbeats 1000000 in
/-- Two or more literals not false: nothing changes. -/
theorem hint_none {G : List (BitVec 32)} (hS : Shape X s G B) {h p e cnt last x nf : BitVec 32}
    (hc0 : ¬ cnt = 0#32) (hc1 : ¬ cnt = 1#32) :
    HintPostHwp P host X s [h, 1#32, p, e, cnt, last, x, nf, h] G B := by
  hintPost_unfold
  wrun [hc0, hc1]
  exact w_end (stepPost_same hS)

set_option maxHeartbeats 1000000 in
/-- Every literal false: conflict. -/
theorem hint_confl (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    {h p e last x nf : BitVec 32} (hh : h.toNat < 1024) (hlen : entryLen B h.toNat ≠ 0)
    (hall : ∀ w ∈ entryWords B h.toNat, wd B (litAddr w) = S * 2#32) :
    HintPostHwp P host X s [h, 1#32, p, e, 0#32, last, x, nf, h] [2#32, t, c, S, cf, sid, u, n] B := by
  hintPost_unfold
  wrun
  exact w_end (stepPost_of (by assumption) fun _ hG => by
    rw [List.append_nil]; exact hG.hintConfl hh hlen hall)

set_option maxHeartbeats 1000000 in
/-- Every literal but `last` false: `last` becomes true. -/
theorem hint_unit (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    {h p e last x nf : BitVec 32} (hh : h.toNat < 1024) (hlen : entryLen B h.toNat ≠ 0)
    (hlm : last ∈ entryWords B h.toNat) (hlv : ValidLit last)
    (hrest : ∀ w ∈ entryWords B h.toNat, w ≠ last → wd B (litAddr w) = S * 2#32) :
    HintPostHwp P host X s [h, 1#32, p, e, 1#32, last, x, nf, h] [2#32, t, c, S, cf, sid, u, n] B := by
  hintPost_unfold
  have hla : (BitVec.ofNat 32 valBase + last * 4#32).toNat + 4 ≤ startBase := hlv.addr.2
  have hna : (BitVec.ofNat 32 valBase - last * 4#32).toNat + 4 ≤ startBase := by
    have := hlv.neg.addr.2
    rw [← negAddr_eq] at this
    exact this
  wrun
  have e1 : (BitVec.ofNat 32 valBase + last * 4#32).toNat = litAddr last := rfl
  have e2 : (BitVec.ofNat 32 valBase - last * 4#32).toNat = negAddr last := rfl
  have e3 : S * 2#32 + BitVec.ofNat 32 (1 - 1) = S * 2#32 := BitVec.add_zero _
  simp only [e1, e2, e3] at *
  exact w_end (stepPost_of (by assumption) fun _ hG => by
    rw [List.append_nil]; exact hG.hintUnit hh hlen hlm hrest)

/-- The scan invariant: the view is unchanged, and after `k` words the frame holds the position
`p`, the end `st + ln`, and a summary `ScanOk` of the words read. -/
def ScanInv (X : Fix H) (G : List (BitVec 32)) (B : ByteArray) (h st ln S : BitVec 32) :
    Store H → Frame → Prop := fun s' f' =>
  Shape X s' G B ∧ ∃ (k : Nat) (p cnt last x nf : BitVec 32),
    f' = fr X.mi [h, 1#32, p, st + ln, cnt, last, x, nf, h] ∧ p.toNat = st.toNat + 4 * k ∧
    4 * k ≤ ln.toNat ∧ ScanOk B st.toNat S k cnt last

/-- The words of the clause being scanned are literals in range, and the scan stays in memory. -/
structure ScanCtx (B : ByteArray) (h st ln : BitVec 32) : Prop where
  words : entryWords B h.toNat = words B st.toNat (ln.toNat / 4)
  valid : ∀ w ∈ entryWords B h.toNat, ValidLit w
  dvd : 4 ∣ ln.toNat
  bound : st.toNat + ln.toNat ≤ memSize
  sum : (st + ln).toNat = st.toNat + ln.toNat

variable {h st ln : BitVec 32}

set_option maxHeartbeats 1000000 in
/-- **One iteration of the scan** keeps the invariant. -/
theorem hint_iter (hX : MiOk X) (hc : ScanCtx B h st ln) {s' : Store H}
    (hS' : Shape X s' [2#32, t, c, S, cf, sid, u, n] B) {k : Nat}
    {p cnt last x nf : BitVec 32} (hp : p.toNat = st.toNat + 4 * k) (hsc : ScanOk B st.toNat S k cnt last)
    (hlt : p.toNat + 4 ≤ st.toNat + ln.toNat) {rest : List Admin} {Q : Post H} :
    HWP P host s' (fr X.mi [h, 1#32, p, st + ln, cnt, last, x, nf, h])
      (vals ([] : List Val).reverse ++ expression hintStep)
      (whilePost P host (ScanInv X [2#32, t, c, S, cf, sid, u, n] B h st ln S) rest Q) := by
  have hkn : k < ln.toNat / 4 := by have := hc.dvd; omega
  have hpb : p.toNat + 4 ≤ memSize := by have := hc.bound; simp only [memSize] at *; omega
  have hxm : wd B p.toNat ∈ entryWords B h.toNat := by
    rw [hc.words, mem_words]; exact ⟨k, hkn, by rw [hp]⟩
  have hvb : (BitVec.ofNat 32 valBase + wd B p.toNat * 4#32).toNat + 4 ≤ startBase :=
    (hc.valid _ hxm).addr.2
  simp only [hintStep, valAddrCode, stamp2Code, expression, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil]
  wrun
  refine w_br (whilePost_cont ⟨by assumption, k + 1, p + 4#32, _, _, _, _, rfl, ?_, by omega,
    hsc.step (by omega) (by rw [hp])⟩)
  simp only [memSize] at hpb
  rw [BitVec.toNat_add_of_lt (by simp; omega), hp]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

set_option maxHeartbeats 1000000 in
/-- **The end of the scan**: dispatch on the count. -/
theorem hint_exit (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    (hc : ScanCtx B h st ln) (hh : h.toNat < 1024) (hlen : entryLen B h.toNat ≠ 0)
    {p cnt last x nf : BitVec 32} (hsc : ScanOk B st.toNat S (ln.toNat / 4) cnt last) :
    HintPostHwp P host X s [h, 1#32, p, st + ln, cnt, last, x, nf, h] [2#32, t, c, S, cf, sid, u, n] B := by
  by_cases hc0 : cnt = 0#32
  · subst hc0
    refine hint_confl hX hS hh hlen fun w hw => ?_
    rw [hc.words, mem_words] at hw
    obtain ⟨j, hj, rfl⟩ := hw
    exact hsc.2.1 rfl j hj
  · by_cases hc1 : cnt = 1#32
    · subst hc1
      obtain ⟨⟨j, hj, hjl⟩, hrest⟩ := hsc.2.2 rfl
      have hlm : last ∈ entryWords B h.toNat := by rw [hc.words, mem_words]; exact ⟨j, hj, hjl⟩
      refine hint_unit hX hS hh hlen hlm (hc.valid last hlm) fun w hw hne => ?_
      rw [hc.words, mem_words] at hw
      obtain ⟨j', hj', rfl⟩ := hw
      exact hrest j' hj' hne
    · exact hint_none hS hc0 hc1

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- `step_hint(h)` with a valid hint: the scan of clause `h`. -/
theorem stepHint_valid (hX : MiOk X) (hS : Shape X s [2#32, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [2#32, t, c, S, cf, sid, u, n] B) (h : BitVec 32) (hh : h.toNat < 1024)
    (hln : ¬ wd B (BitVec.ofNat 32 lenBase + h * 4#32).toNat = 0#32) :
    HWP P host s (fr X.mi [h, 0, 0, 0, 0, 0, 0, 0, 0])
      (vals ([] : List Val).reverse ++ expression stepHintBody ++ [])
      (stepPost X [2#32, t, c, S, cf, sid, u, n] B []) := by
  simp only [stepHintBody, hintLoopBody_eq, expression, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.append_nil]
  have ea : (BitVec.ofNat 32 startBase + h * 4#32).toNat = startBase + 4 * h.toNat := by
    simp only [startBase]; bv_omega
  have eb : (BitVec.ofNat 32 lenBase + h * 4#32).toNat = lenBase + 4 * h.toNat := by
    simp only [lenBase]; bv_omega
  have hlen : entryLen B h.toNat ≠ 0 := fun h0 =>
    hln (BitVec.eq_of_toNat_eq (by simpa [entryLen, eb] using h0))
  have he := hG.entries h.toNat hh hlen
  have hc : ScanCtx B h (wd B (startBase + 4 * h.toNat)) (wd B (lenBase + 4 * h.toNat)) := by
    have hb2 : entryStart B h.toNat + entryLen B h.toNat ≤ c.toNat := he.end_le
    have hcl : c.toNat ≤ memSize := le_trans hG.cstart_le hG.top_le
    refine ⟨rfl, he.valid, he.dvd, by simp only [entryStart, entryLen] at hb2; omega, ?_⟩
    simp only [entryStart, entryLen, memSize] at hb2 hcl ⊢; bv_omega
  have hln' : ¬ wd B (lenBase + 4 * h.toNat) = 0#32 := eb ▸ hln
  wrun [hh, hln', BitVec.mul_one, ea, eb]
  refine w_while (Inv := ScanInv X _ B h _ _ S) ⟨hS, 0, _, 0#32, 0#32, 0#32, 0#32, rfl, by simp,
    by simp, ScanOk.zero⟩ ?_
  rintro s' f' ⟨hS', k, p, cnt, last, x, nf, rfl, hp, hk, hsc⟩
  simp only [expression, List.map_cons]
  wstep; try wnorm
  wstep; try wnorm
  wstep
  refine w_brIf (fun hx => ?_) (fun hx => ?_)
  · have hkn : k = (wd B (lenBase + 4 * h.toNat)).toNat / 4 := by
      have := b32_ne_zero.1 hx; have := hc.sum; have := hc.dvd; omega
    subst hkn
    exact w_br (whilePost_exit (hint_exit hX hS' hc hh hlen hsc))
  · have hlt : p.toNat + 4 ≤ (wd B (startBase + 4 * h.toNat)).toNat +
        (wd B (lenBase + 4 * h.toNat)).toNat := by
      have := b32_eq_zero.1 hx; have := hc.sum; have := hc.dvd; omega
    exact hint_iter hX hc hS' hp hsc hlt

/-- The code after the prefix of `step_hint`: the scan and the two updates. -/
def hintRest : List Instr :=
  [.block .empty [.loop .empty hintLoopBody]] ++
  [lget 1, lget 4, ieqz, iand, ifThen [c32 1, gset gConfl]] ++
  [lget 1, lget 4, c32 1, ieq, iand, ifThen (assignCode 5 1)]

set_option linter.unusedTactic false in
/-- An invalid hint: the scan is empty and nothing changes. -/
theorem hint_skip {G : List (BitVec 32)} (hS : Shape X s G B) (h l8 : BitVec 32) :
    HWP P host s (fr X.mi [h, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, l8])
      (vals ([] : List Val).reverse ++ expression hintRest ++ []) (stepPost X G B []) := by
  simp only [hintRest, hintLoopBody, assignCode, valAddrCode, negAddrCode, stamp2Code,
    expression, List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_nil]
  refine w_while (Inv := fun s' f' => Shape X s' G B ∧
    f' = fr X.mi [h, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, l8]) ⟨hS, rfl⟩ ?_
  rintro s' f' ⟨hS', rfl⟩
  simp only [expression, List.map_cons, List.map_nil]
  wstep; try wnorm
  wstep; try wnorm
  wstep; try wnorm [le_refl]
  refine w_brIf (fun _ => ?_) (fun hc => absurd hc (by decide))
  refine w_br (whilePost_exit ?_)
  wrun
  exact w_end (stepPost_same hS')

set_option maxHeartbeats 4000000 in
/-- **`step_hint`, every run.** -/
theorem stepHint_hwp (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hG : Good xs [m, t, c, S, cf, sid, u, n] B) (h : BitVec 32) :
    HWP P host s (fr X.mi [h, 0, 0, 0, 0, 0, 0, 0, 0])
      (vals ([] : List Val).reverse ++ expression stepHintBody ++ [])
      (stepPost X [m, t, c, S, cf, sid, u, n] B []) := by
  by_cases hm : m = 2#32
  · subst hm
    by_cases hh : h.toNat < 1024
    · by_cases hln : wd B (BitVec.ofNat 32 lenBase + h * 4#32).toNat = 0#32
      · simp only [stepHintBody, List.append_assoc, expression, List.cons_append,
          List.nil_append, List.map_cons, List.map_nil]
        wrun [hh, hln, BitVec.mul_one, BitVec.mul_zero, BitVec.zero_add]
        exact hint_skip hS h h
      · exact stepHint_valid hX hS hG h hh hln
    · have hh' := eq_false hh
      simp only [stepHintBody, List.append_assoc, expression, List.cons_append,
        List.nil_append, List.map_cons, List.map_nil]
      wrun [hh', BitVec.mul_zero, BitVec.zero_mul, BitVec.add_zero, BitVec.zero_add]
      exact hint_skip hS h 0#32
  · simp only [stepHintBody, List.append_assoc, expression, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil]
    wrun [hm, BitVec.mul_zero, BitVec.zero_mul, BitVec.add_zero, BitVec.zero_add]
    exact hint_skip hS h 0#32

end Silmaril.Wasm.Examples.LRAT
