module

public import Silmaril.Wasm.Dataflow.Liveness.Defs
public import Silmaril.Wasm.Dataflow.Structured.Thms

/-!
# Live locals of structured Wasm code: theorems

* `LiveSet.le_kill_sup`, `LiveSet.single_le_kill`, `LiveSet.kill_eq_of_mem_false`: the
  algebra of `kill`;
* `liveAdminSeq_expression`, `liveAdminSeq_vals`: administrative liveness on source code
  and on values;
* `FrameRel.setLocal`, `FrameRel.setLocal_dead`: transfer soundness of a kept and of a
  removed `local.set`;
* `liveSeq_loop_safe`: the loop-head live set covers the back edge.

The source's `FrameRel.setLocal_dead` took a hypothesis `x < f.locals.length` that it did
not use; the port drops it.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

namespace LiveSet

theorem mem_iff (x : ℕ) (L : LiveSet) : L.mem x = true ↔ single x ≤ L := by
  induction L using WithTop.recTopCoe with
  | top => exact iff_of_true rfl le_top
  | coe s =>
    change decide (x ∈ s) = true ↔ ((({x} : Finset ℕ)) : LiveSet) ≤ (s : LiveSet)
    rw [WithTop.coe_le_coe, decide_eq_true_iff]
    exact Finset.singleton_subset_iff.symm

/-- Killing is sound: whatever was live after the kill or is `x` was live before. -/
theorem le_kill_sup (x : ℕ) (L : LiveSet) : L ≤ kill x L ⊔ single x := by
  induction L using WithTop.recTopCoe with
  | top => exact (show (⊤ : LiveSet) ≤ ⊤ ⊔ single x from le_sup_left)
  | coe s =>
    change ((s : Finset ℕ) : LiveSet) ≤
      ((s.erase x : Finset ℕ) : LiveSet) ⊔ ((({x} : Finset ℕ)) : LiveSet)
    rw [← WithTop.coe_sup, WithTop.coe_le_coe]
    intro y hy
    rw [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    by_cases h : y = x
    · exact .inr h
    · exact .inl ⟨h, hy⟩

theorem kill_le (x : ℕ) (L : LiveSet) : kill x L ≤ L := by
  induction L using WithTop.recTopCoe with
  | top => exact le_top
  | coe s =>
    change ((s.erase x : Finset ℕ) : LiveSet) ≤ ((s : Finset ℕ) : LiveSet)
    rw [WithTop.coe_le_coe]
    exact Finset.erase_subset x s

/-- A local other than `x` that is live is live after killing `x`. -/
theorem single_le_kill {x y : ℕ} {L : LiveSet} (hxy : y ≠ x) (h : single y ≤ L) :
    single y ≤ kill x L := by
  induction L using WithTop.recTopCoe with
  | top => exact le_top
  | coe s =>
    change ((({y} : Finset ℕ)) : LiveSet) ≤ ((s : Finset ℕ) : LiveSet) at h
    change ((({y} : Finset ℕ)) : LiveSet) ≤ ((s.erase x : Finset ℕ) : LiveSet)
    rw [WithTop.coe_le_coe] at h ⊢
    exact Finset.singleton_subset_iff.mpr
      (Finset.mem_erase.mpr ⟨hxy, Finset.singleton_subset_iff.mp h⟩)

theorem kill_eq_of_mem_false {x : ℕ} {L : LiveSet} (h : L.mem x = false) : kill x L = L := by
  induction L using WithTop.recTopCoe with
  | top => exact absurd h (by simp [mem])
  | coe s =>
    change decide (x ∈ s) = false at h
    change ((s.erase x : Finset ℕ) : LiveSet) = (s : LiveSet)
    rw [Finset.erase_eq_of_notMem (of_decide_eq_false h)]

end LiveSet

theorem liveAdminSeq_append (env : List LiveSet) (out : LiveSet) (as bs : List Admin) :
    liveAdminSeq env out (as ++ bs) = liveAdminSeq env (liveAdminSeq env out bs) as := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

/-- On source code, administrative liveness is `liveSeq`. -/
theorem liveAdminSeq_expression (env : List LiveSet) (out : LiveSet) (e : List Instr) :
    liveAdminSeq env out (expression e) = liveSeq env out e := by
  induction e with
  | nil => simp [expression]
  | cons i e ih =>
      simp only [expression, List.map_cons, liveAdminSeq_cons] at ih ⊢
      rw [ih]
      simp [liveAdmin]

/-- Values do not change liveness. -/
theorem liveAdminSeq_vals (env : List LiveSet) (out : LiveSet) (vs : List Val) :
    liveAdminSeq env out (vals vs) = out := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih =>
      simp only [vals, List.map_cons, liveAdminSeq_cons] at ih ⊢
      rw [ih]
      rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;>
        simp [Val.toAdmin, liveAdmin, Backward.instr, liveness, liveTransfer]

theorem liveAdmin_toAdmin (env : List LiveSet) (out : LiveSet) (v : Val) :
    liveAdmin env out v.toAdmin = out := by
  simpa only [vals, List.map_cons, List.map_nil, liveAdminSeq_cons, liveAdminSeq_nil] using
    liveAdminSeq_vals env out [v]

/-! ## Meaning of live sets -/

theorem FrameRel.refl (L : LiveSet) (f : Frame) : FrameRel L f f :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem FrameRel.mono {L L' : LiveSet} {f f' : Frame} (h : FrameRel L f f') (hL : L' ≤ L) :
    FrameRel L' f f' :=
  ⟨h.module, h.length, fun x hx => h.agree x (hx.trans hL)⟩

/-- Related by `⊤` means equal. -/
theorem FrameRel.top_iff {f f' : Frame} : FrameRel ⊤ f f' ↔ f = f' := by
  constructor
  · intro h
    rcases f with ⟨l, m⟩
    rcases f' with ⟨l', m'⟩
    have hl : l = l' := List.ext_getElem? fun x => h.agree x le_top
    have hm : m = m' := h.module
    subst hl hm
    rfl
  · rintro rfl
    exact FrameRel.refl _ _

/-- A live local reads the same in related frames. -/
theorem FrameRel.local?_eq {L : LiveSet} {f f' : Frame} (h : FrameRel L f f') {x : LocalIdx}
    (hx : LiveSet.single x.toNat ≤ L) : f.local? x = f'.local? x :=
  h.agree x.toNat hx

/-- Transfer soundness of `local.set x` when `x` is written in both frames. -/
theorem FrameRel.setLocal {L : LiveSet} {f f' : Frame} {x : LocalIdx} (v : Val)
    (h : FrameRel (LiveSet.kill x.toNat L) f f') :
    FrameRel L (f.setLocal x v) (f'.setLocal x v) := by
  refine ⟨h.module, by simp [Frame.setLocal, h.length], ?_⟩
  intro y hy
  simp only [Frame.setLocal, List.getElem?_set]
  by_cases hyx : x.toNat = y
  · simp [hyx, h.length]
  · simp only [hyx, ↓reduceIte]
    exact h.agree y (LiveSet.single_le_kill (Ne.symm hyx) hy)

/-- Transfer soundness of a dead `local.set x`, performed in the first frame only. -/
theorem FrameRel.setLocal_dead {L : LiveSet} {f f' : Frame} {x : LocalIdx} (v : Val)
    (hdead : L.mem x.toNat = false) (h : FrameRel L f f') :
    FrameRel L (f.setLocal x v) f' := by
  refine ⟨h.module, by simp [Frame.setLocal, h.length], ?_⟩
  intro y hy
  simp only [Frame.setLocal, List.getElem?_set]
  by_cases hyx : x.toNat = y
  · subst hyx
    rw [← LiveSet.mem_iff, hdead] at hy
    exact absurd hy Bool.false_ne_true
  · simp only [hyx, ↓reduceIte]
    exact h.agree y hy

/-! ## Safety of the solution -/

/-- The loop-head live set covers the live set of the loop body entered with that
label (the back edge, notes p. 8 "safe"). -/
theorem liveSeq_loop_safe (env : List LiveSet) (out : LiveSet) (bt : BlockType)
    (body : List Instr) :
    liveSeq (liveInstr env out (.loop bt body) :: env) out body ≤
      liveInstr env out (.loop bt body) :=
  liveness.instr_loop_safe env out bt body

end Silmaril.Wasm.Dataflow
