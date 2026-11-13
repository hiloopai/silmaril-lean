module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Hint
public import Silmaril.Proofs.Wasm.Examples.LRAT.GoodRat

@[expose] public section

/-!
# The loops of the RAT exports, every run

* `asg_loop`: the assignment loop of `rat_begin` (`assignLoopBody`) over the words `[p₀, e)`:
  every word other than `skip` is assigned false, with the invariant `AsgOk`;
* `scan_loop`: the inner scan of `rat_end` (`scanInnerBody`) over `[p₀, e)`: `bad` stays `0` only
  if no word is `skip`; the memory is unchanged.

Both are `w_while` loops whose exit continues with the code after them. Every profile and host
relation.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Logic.SAT

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}
variable {s : Store H} {m t c S cf sid u n : BitVec 32} {B B₀ : ByteArray}
variable {rest : List Admin} {Q : Post H}

/-! ## The assignment loop -/

/-- One iteration of the assignment loop after its exit test. -/
def asgStep : List Instr :=
  [lget 2, iload, lset 4, lget 4, lget 5, ine, ifThen (assignCode 4 0),
    lget 2, c32 4, iadd, lset 2, .br ⟨0⟩]

theorem assignLoopBody_eq : assignLoopBody = [lget 2, lget 3, igeu, .brIf ⟨1⟩] ++ asgStep := rfl

/-- The invariant of the assignment loop: after `k` words from `p₀`, the frame holds `p₀ + 4k`
and the assignments are those of the non-`skip` words read. -/
def AsgInv (X : Fix H) (G : List (BitVec 32)) (B₀ : ByteArray) (S : BitVec 32)
    (L₀ : List (BitVec 32)) (a0 a1 a6 a7 p₀ e skip : BitVec 32) : Store H → Frame → Prop :=
  fun s' f' => ∃ (k : Nat) (B' : ByteArray) (p x : BitVec 32), Shape X s' G B' ∧
    f' = fr X.mi [a0, a1, p, e, x, skip, a6, a7] ∧ p.toNat = p₀.toNat + 4 * k ∧
    p.toNat ≤ e.toNat ∧ AsgOk B₀ B' S (L₀ ++ (words B₀ p₀.toNat k).filter (· != skip))

/-- The words of the loop are literals in range and lie above the tables (unless there are
none). -/
structure AsgCtx (B₀ : ByteArray) (p₀ e : BitVec 32) (N : Nat) : Prop where
  e_eq : e.toNat = p₀.toNat + 4 * N
  bound : p₀.toNat + 4 * N ≤ memSize
  base : N = 0 ∨ startBase ≤ p₀.toNat
  valid : ∀ k < N, ValidLit (wd B₀ (p₀.toNat + 4 * k))

variable {G : List (BitVec 32)} {L₀ : List (BitVec 32)} {a0 a1 a6 a7 p₀ e skip : BitVec 32}
  {N : Nat}

theorem words_filter_succ (B : ByteArray) (p k : Nat) (skip : BitVec 32) :
    (words B p (k + 1)).filter (· != skip) = (words B p k).filter (· != skip) ++
      (if wd B (p + 4 * k) = skip then [] else [wd B (p + 4 * k)]) := by
  rw [words_succ, List.filter_append]
  by_cases h : wd B (p + 4 * k) = skip
  · simp [h]
  · simp [h]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **One iteration of the assignment loop.** -/
theorem asg_iter (hX : MiOk X) (hc : AsgCtx B₀ p₀ e N) {s' : Store H} {B' : ByteArray}
    (hS' : Shape X s' [m, t, c, S, cf, sid, u, n] B') (hSm : S.toNat ≤ maxStamp) {k : Nat}
    {p x : BitVec 32} (hp : p.toNat = p₀.toNat + 4 * k) (hk : k < N)
    (ha : AsgOk B₀ B' S (L₀ ++ (words B₀ p₀.toNat k).filter (· != skip))) :
    HWP P host s' (fr X.mi [a0, a1, p, e, x, skip, a6, a7])
      (vals ([] : List Val).reverse ++ expression asgStep)
      (whilePost P host (AsgInv X [m, t, c, S, cf, sid, u, n] B₀ S L₀ a0 a1 a6 a7 p₀ e skip)
        rest Q) := by
  have hbase : startBase ≤ p₀.toNat := hc.base.resolve_left (by omega)
  have hpb : p.toNat + 4 ≤ memSize := by have := hc.bound; omega
  have hpe : p.toNat + 4 ≤ e.toNat := by have := hc.e_eq; omega
  have hw : wd B' p.toNat = wd B₀ (p₀.toNat + 4 * k) := by
    rw [hp]; exact ha.hi.wd (by omega)
  have hv : ValidLit (wd B' p.toNat) := hw ▸ hc.valid k hk
  have hla : (BitVec.ofNat 32 valBase + wd B' p.toNat * 4#32).toNat + 4 ≤ startBase := hv.addr.2
  have hna : (BitVec.ofNat 32 valBase - wd B' p.toNat * 4#32).toNat + 4 ≤ startBase := by
    have := hv.neg.addr.2
    rw [← negAddr_eq] at this
    exact this
  have hp4 : (p + 4#32).toNat = p₀.toNat + 4 * (k + 1) := by
    simp only [memSize] at hpb; rw [BitVec.toNat_add_of_lt (by simp; omega), hp]; simp; omega
  simp only [asgStep, assignCode, valAddrCode, negAddrCode, stamp2Code, expression,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil]
  have e1 : (BitVec.ofNat 32 valBase + wd B' p.toNat * 4#32).toNat = litAddr (wd B' p.toNat) :=
    rfl
  have e2 : (BitVec.ofNat 32 valBase - wd B' p.toNat * 4#32).toNat = negAddr (wd B' p.toNat) :=
    rfl
  have e4 : BitVec.ofNat 32 (1 - 0) = 1#32 := rfl
  by_cases hx : wd B' p.toNat = skip
  · wrun [hx]
    refine w_br (whilePost_cont ⟨k + 1, B', p + 4#32, _, by assumption, rfl, hp4, by omega, ?_⟩)
    rw [words_filter_succ, ← hw]
    simp only [hx, ite_true, List.append_nil]
    exact ha
  · wrun [hx]
    simp only [e1, e2, e4] at *
    refine w_br (whilePost_cont ⟨k + 1, _, p + 4#32, _, by assumption, rfl, hp4, by omega, ?_⟩)
    rw [words_filter_succ, ← hw]
    simp only [hx, ite_false, ← List.append_assoc]
    exact ha.assign hSm hv

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- **The assignment loop**: from `AsgOk B₀ B S L₀`, it ends with `p = e` in a memory `B'` with
`AsgOk B₀ B' S (L₀ ++ non-skip words)`. -/
theorem asg_loop (hX : MiOk X) (hS : Shape X s [m, t, c, S, cf, sid, u, n] B)
    (hSm : S.toNat ≤ maxStamp) (hc : AsgCtx B₀ p₀ e N) (ha : AsgOk B₀ B S L₀) {x : BitVec 32}
    (hk : ∀ s' B' x', Shape X s' [m, t, c, S, cf, sid, u, n] B' →
      AsgOk B₀ B' S (L₀ ++ (words B₀ p₀.toNat N).filter (· != skip)) →
      HWP P host s' (fr X.mi [a0, a1, e, e, x', skip, a6, a7]) (vals ([] : List Val).reverse ++ rest)
        Q) :
    HWP P host s (fr X.mi [a0, a1, p₀, e, x, skip, a6, a7])
      (vals ([] : List Val).reverse ++ .plain (.block .empty [.loop .empty assignLoopBody]) :: rest)
      Q := by
  refine w_while (Inv := AsgInv X [m, t, c, S, cf, sid, u, n] B₀ S L₀ a0 a1 a6 a7 p₀ e skip)
    ⟨0, B, p₀, x, hS, rfl, by simp, by have := hc.e_eq; omega, by
      rw [words_zero, List.filter_nil, List.append_nil]; exact ha⟩ ?_
  rintro s' f' ⟨k, B', p, x', hS', rfl, hp, hpe, ha'⟩
  rw [assignLoopBody_eq]
  simp only [expression, List.map_cons, List.cons_append, List.nil_append]
  wstep; try wnorm
  wstep; try wnorm
  wstep
  refine w_brIf (fun hx => ?_) (fun hx => ?_)
  · have hkN : k = N := by
      have := b32_ne_zero.1 hx; have := hc.e_eq; omega
    subst hkN
    have hpe' : p = e := BitVec.eq_of_toNat_eq (by have := hc.e_eq; omega)
    subst hpe'
    exact w_br (whilePost_exit (hk s' B' x' hS' ha'))
  · have hkN : k < N := by
      have := b32_eq_zero.1 hx; have := hc.e_eq; omega
    exact asg_iter hX hc hS' hSm hp hkN ha'

/-! ## The scan loop -/

/-- One iteration of the scan after its exit test. -/
def scanStep : List Instr :=
  [lget 3, iload, lset 9, lget 9, lget 5, ieq, ifThen [c32 1, lset 6],
    lget 3, c32 4, iadd, lset 3, .br ⟨0⟩]

theorem scanInnerBody_eq : scanInnerBody = [lget 3, lget 4, igeu, .brIf ⟨1⟩] ++ scanStep := rfl

/-- The invariant of the scan: after `k` words from `p₀`, `bad` is still `0` only if it was `0`
and none of them is `skip`. -/
def ScanInv' (X : Fix H) (G : List (BitVec 32)) (B : ByteArray)
    (a0 a1 a2 a7 a8 p₀ e skip bad : BitVec 32) : Store H → Frame → Prop :=
  fun s' f' => Shape X s' G B ∧ ∃ (k : Nat) (p bad' x : BitVec 32),
    f' = fr X.mi [a0, a1, a2, p, e, skip, bad', a7, a8, x] ∧ p.toNat = p₀.toNat + 4 * k ∧
    p.toNat ≤ e.toNat ∧ (bad' = 0#32 → bad = 0#32 ∧ ∀ j < k, wd B (p₀.toNat + 4 * j) ≠ skip)

variable {a2 a8 bad : BitVec 32}

set_option maxHeartbeats 4000000 in
/-- **One iteration of the scan.** -/
theorem scan_iter (hX : MiOk X) (he : e.toNat = p₀.toNat + 4 * N)
    (hb : p₀.toNat + 4 * N ≤ memSize) {s' : Store H} (hS' : Shape X s' G B) {k : Nat}
    {p bad' x : BitVec 32} (hp : p.toNat = p₀.toNat + 4 * k) (hk : k < N)
    (hinv : bad' = 0#32 → bad = 0#32 ∧ ∀ j < k, wd B (p₀.toNat + 4 * j) ≠ skip) :
    HWP P host s' (fr X.mi [a0, a1, a2, p, e, skip, bad', a7, a8, x])
      (vals ([] : List Val).reverse ++ expression scanStep)
      (whilePost P host (ScanInv' X G B a0 a1 a2 a7 a8 p₀ e skip bad) rest Q) := by
  have hpb : p.toNat + 4 ≤ memSize := by omega
  have hp4 : (p + 4#32).toNat = p₀.toNat + 4 * (k + 1) := by
    simp only [memSize] at hpb; rw [BitVec.toNat_add_of_lt (by simp; omega), hp]; simp; omega
  simp only [scanStep, expression, List.map_cons, List.map_nil]
  by_cases hx : wd B p.toNat = skip
  · wrun [hx]
    refine w_br (whilePost_cont ⟨by assumption, k + 1, p + 4#32, 1#32, _, rfl, hp4, by omega,
      fun h => absurd h (by decide)⟩)
  · wrun [hx]
    refine w_br (whilePost_cont ⟨by assumption, k + 1, p + 4#32, bad', _, rfl, hp4, by omega,
      fun h0 => ⟨(hinv h0).1, fun j hj => ?_⟩⟩)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact (hinv h0).2 j hj
    · rw [← hp]; exact hx

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- **The scan loop**: it ends with `p = e`, the memory unchanged, and `bad = 0` only if it was
`0` and no word of `[p₀, p₀ + 4N)` is `skip`. -/
theorem scan_loop (hX : MiOk X) (hS : Shape X s G B) (he : e.toNat = p₀.toNat + 4 * N)
    (hb : p₀.toNat + 4 * N ≤ memSize) {x : BitVec 32}
    (hk : ∀ s' bad' x', Shape X s' G B →
      (bad' = 0#32 → bad = 0#32 ∧ ∀ j < N, wd B (p₀.toNat + 4 * j) ≠ skip) →
      HWP P host s' (fr X.mi [a0, a1, a2, e, e, skip, bad', a7, a8, x'])
        (vals ([] : List Val).reverse ++ rest) Q) :
    HWP P host s (fr X.mi [a0, a1, a2, p₀, e, skip, bad, a7, a8, x])
      (vals ([] : List Val).reverse ++ .plain (.block .empty [.loop .empty scanInnerBody]) :: rest)
      Q := by
  refine w_while (Inv := ScanInv' X G B a0 a1 a2 a7 a8 p₀ e skip bad)
    ⟨hS, 0, p₀, bad, x, rfl, by simp, by omega, fun h => ⟨h, fun _ hj => absurd hj (by omega)⟩⟩ ?_
  rintro s' f' ⟨hS', k, p, bad', x', rfl, hp, hpe, hinv⟩
  rw [scanInnerBody_eq]
  simp only [expression, List.map_cons, List.cons_append, List.nil_append]
  wstep; try wnorm
  wstep; try wnorm
  wstep
  refine w_brIf (fun hx => ?_) (fun hx => ?_)
  · have hkN : k = N := by
      have := b32_ne_zero.1 hx; omega
    subst hkN
    have hpe' : p = e := BitVec.eq_of_toNat_eq (by omega)
    subst hpe'
    exact w_br (whilePost_exit (hk s' bad' x' hS' hinv))
  · have hkN : k < N := by
      have := b32_eq_zero.1 hx; omega
    exact scan_iter hX he hb hS' hp hkN hinv

end Silmaril.Wasm.Examples.LRAT
