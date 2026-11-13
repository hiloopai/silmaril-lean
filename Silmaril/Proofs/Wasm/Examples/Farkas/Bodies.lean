module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Inv

@[expose] public section

/-!
# The Farkas checker: every-run specifications of the bodies

At every profile and for every host relation (`HWP`, partial correctness):

* `row_hwp`, `entry_hwp`: the bodies end normally with no results, in the store holding
  `rowM m y b`, resp. `entryM m j a` (symbolic execution, `Common.Wp.exec_eq`);
* `check_hwp`: the body ends normally with the single result `checkRes m nz`, in the store
  holding `checkEnd B`, for some `B` and `nz` with `ScanDone m.mem B nz` (the scan loop by
  `HWP.loop` with the invariant `LoopInv`, inside `HWP.block`).

No body traps, throws or branches out.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP Wp labelPost seqPost loopPost)
open Silmaril.Wasm.Examples.Common (Wp.exec_eq)

variable {P : Profile} {host : HostSemantics Nat} {s₀ : Store Nat} {m : Mach}

theorem row_hwp (y b : BitVec 64) {Q : Post Nat}
    (hQ : ∀ f', Q (withMach s₀ (rowM m y b)) f' (.normal [])) :
    HWP P host (withMach s₀ m) (Frame.forCall farkasMI [.i64 y, .i64 b] [.i64]) (expression rowBody) Q := by
  rw [frame_row]
  have h := Wp.exec_eq (m := .part) (P := P) (host := host) (vs := []) (rest := []) (Q := Q)
    (exec_row (s₀ := s₀) (m := m) y b) (by simpa using Wp.of_vals (m := .part) (hQ _))
  simpa using h

theorem entry_hwp (hB : m.mem.size = 65536) (j : BitVec 32) (a : BitVec 64) {Q : Post Nat}
    (hQ : ∀ f', Q (withMach s₀ (entryM m j a)) f' (.normal [])) :
    HWP P host (withMach s₀ m) (Frame.forCall farkasMI [.i32 j, .i64 a] [.i32, .i64])
      (expression entryBody) Q := by
  rw [frame_entry]
  have h := Wp.exec_eq (m := .part) (P := P) (host := host) (vs := []) (rest := []) (Q := Q)
    (exec_entry (s₀ := s₀) hB j a) (by simpa using Wp.of_vals (m := .part) (hQ _))
  simpa using h

/-! ## The scan loop of `check` -/

/-- The invariant of the scan loop: slots below `i` are zero, the others unchanged, and `nz = 0`
only if the slots below `i` were zero. -/
structure LoopInv (B₀ : ByteArray) (i nz : BitVec 32) (B : ByteArray) : Prop where
  le : i.toNat ≤ nVars
  size : B.size = 65536
  done : ∀ k < i.toNat, slot B k = 0
  rest : ∀ k, i.toNat ≤ k → k < nVars → slot B k = slot B₀ k
  nz_zero : nz = 0 → ∀ k < i.toNat, slot B₀ k = 0
  nz_of : (∀ k < i.toNat, slot B₀ k = 0) → nz = 0

theorem LoopInv.init (hB : m.mem.size = 65536) : LoopInv m.mem 0 0 m.mem :=
  ⟨by decide, hB, fun _ hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ => rfl,
    fun _ _ hk => absurd hk (Nat.not_lt_zero _), fun _ => rfl⟩

theorem LoopInv.step {B₀ B : ByteArray} {i nz : BitVec 32} (h : LoopInv B₀ i nz B)
    (hi : i.toNat < nVars) :
    LoopInv B₀ (i + 1) (scanNz B i nz) (setSlot B i.toNat 0) := by
  have hi' : i.toNat < 8192 := hi
  have hsucc : (i + 1).toNat = i.toNat + 1 := by
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1]
    omega
  have hslot : ∀ k, slot (setSlot B i.toNat 0) k = if i.toNat = k then 0 else slot B k := by
    intro k
    by_cases hk : i.toNat = k
    · simp only [hk, ↓reduceIte]
      rw [← hk, slot_setSlot_same h.size hi]
    · simp only [hk, ↓reduceIte]
      rw [slot_setSlot_ne h.size hi hk]
  refine ⟨by rw [hsucc]; exact hi, size_setSlot h.size hi 0, fun k hk => ?_, fun k hk hkn => ?_,
    fun hnz k hk => ?_, fun hall => ?_⟩
  · rw [hslot k]
    split
    · rfl
    · exact h.done k (by omega)
  · have hne : i.toNat ≠ k := by omega
    rw [hslot k]
    simp only [hne, ↓reduceIte]
    exact h.rest k (by omega) hkn
  · have hz := or_eq_zero.1 hnz
    by_cases hk' : k = i.toNat
    · rw [hk', ← h.rest i.toNat le_rfl hi]
      exact ne_eq_zero.1 hz.2
    · exact h.nz_zero hz.1 k (by omega)
  · have hlow : ∀ k < i.toNat, slot B₀ k = 0 := fun k hk => hall k (by omega)
    have hcur : slot B i.toNat = 0 := (h.rest i.toNat le_rfl hi).trans (hall i.toNat (by omega))
    exact or_eq_zero.2 ⟨h.nz_of hlow, ne_eq_zero.2 hcur⟩

theorem LoopInv.exit {B₀ B : ByteArray} {i nz : BitVec 32} (h : LoopInv B₀ i nz B)
    (hi : ¬ i.toNat < nVars) : ScanDone B₀ B nz := by
  have hiN : i.toNat = nVars := le_antisymm h.le (Nat.not_lt.1 hi)
  exact ⟨h.size, fun k hk => h.done k (hiN ▸ hk), fun hnz k hk => h.nz_zero hnz k (hiN ▸ hk),
    fun hall => h.nz_of fun k hk => hall k (hiN ▸ hk)⟩

/-- The loop invariant as a predicate on configurations. -/
def LInv (s₀ : Store Nat) (m : Mach) (s : Store Nat) (f : Frame) (vs : List Val) : Prop :=
  vs = [] ∧ ∃ i nz B, s = withMach s₀ { m with mem := B } ∧ f = scanFrame i nz ∧ LoopInv m.mem i nz B

theorem geU_ne_zero {i : BitVec 32} (h : intRelOp .i32 (.ge .unsigned) i (BitVec.ofNat 32 nVars) ≠ 0) :
    ¬ i.toNat < nVars := fun hi => h (geU_eq_zero.2 hi)

/-- After the loop: the tail of `check`. -/
theorem tail_hwp {Q : Post Nat} {i nz : BitVec 32} {B : ByteArray}
    (hQ : ∀ f', Q (withMach s₀ (checkEnd B)) f' (.normal [Val.i32 (checkRes m nz)])) :
    HWP P host (withMach s₀ { m with mem := B }) (scanFrame i nz) (vals [] ++ expression checkTail) Q := by
  have h := Wp.exec_eq (m := .part) (P := P) (host := host) (vs := []) (rest := []) (Q := Q)
    (exec_tail (s₀ := s₀) (m := { m with mem := B }) i nz)
    (by simpa using Wp.of_vals (m := .part) (hQ _))
  simpa using h

/-- One round of the scan loop. -/
theorem loop_hwp {Q : Post Nat}
    (hQ : ∀ B nz f', ScanDone m.mem B nz →
      Q (withMach s₀ (checkEnd B)) f' (.normal [Val.i32 (checkRes m nz)]))
    (s : Store Nat) (f : Frame) (vs : List Val) (hI : LInv s₀ m s f vs) :
    HWP P host s f (vals vs ++ expression loopBody)
      (loopPost 0 [] (LInv s₀ m) (labelPost P host 0 [] [] (seqPost P host (expression checkTail) Q))) := by
  obtain ⟨rfl, i, nz, B, rfl, rfl, hL⟩ := hI
  rw [loopBody_eq, expression, List.map_append, List.map_cons, ← expression, ← expression,
    ← List.append_assoc]
  refine Wp.exec_eq (m := .part) (vs := []) (exec_test _ i nz) ?_
  refine Silmaril.Wasm.Logic.Hoare.HWP.brIf (us := []) (fun hc => ?_) (fun hc => ?_)
  · -- `i ≥ nVars`: leave the block and run the tail
    have hd : ScanDone m.mem B nz := hL.exit (geU_ne_zero hc)
    refine Silmaril.Wasm.Logic.Hoare.Wp.br (m := .part) ⟨[], [], rfl, rfl, ?_⟩
    exact Silmaril.Wasm.Logic.Hoare.HWP.of_vals (vs := []) (tail_hwp (hQ B nz · hd))
  · -- `i < nVars`: scan slot `i` and go round
    have hi : i.toNat < nVars := geU_eq_zero.1 hc
    rw [expression, List.map_append, ← expression, ← List.append_assoc]
    refine Wp.exec_eq (m := .part) (vs := []) (exec_scan (m := { m with mem := B }) hL.size hi) ?_
    exact Silmaril.Wasm.Logic.Hoare.Wp.br (m := .part)
      ⟨[], [], rfl, rfl, rfl, i + 1, scanNz B i nz, setSlot B i.toNat 0, rfl, rfl, hL.step hi⟩

/-- **The body of `check`.** -/
theorem check_hwp (hB : m.mem.size = 65536) {Q : Post Nat}
    (hQ : ∀ B nz f', ScanDone m.mem B nz →
      Q (withMach s₀ (checkEnd B)) f' (.normal [Val.i32 (checkRes m nz)])) :
    HWP P host (withMach s₀ m) (Frame.forCall farkasMI [] [.i32, .i32]) (expression checkBody) Q := by
  rw [frame_check, checkBody_eq]
  have hloop := Silmaril.Wasm.Logic.Hoare.HWP.loop (P := P) (host := host) (us := []) (Inv := LInv s₀ m)
    (bt := .empty) (body := loopBody) (t₁ := []) (t₂ := [])
    (Q := labelPost P host 0 [] [] (seqPost P host (expression checkTail) Q))
    (fun _ _ _ _ => rfl) (fun _ _ _ h => h.1 ▸ rfl) (loop_hwp hQ)
    (s := withMach s₀ m) (f := scanFrame 0 0) (vs := []) ⟨rfl, 0, 0, m.mem, rfl, rfl, LoopInv.init hB⟩
  have hblock := Silmaril.Wasm.Logic.Hoare.HWP.block (P := P) (host := host) (us := []) (vs := [])
    (bt := .empty) (body := [.loop .empty loopBody]) (rest := expression checkTail) (Q := Q)
    (t₁ := []) (t₂ := []) rfl rfl (by simpa [expression] using hloop)
  simpa [expression] using hblock

end Silmaril.Wasm.Examples.Farkas
