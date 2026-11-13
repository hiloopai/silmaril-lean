module

public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Heap

/-!
# Proofs: one-step rules for read-modify-writes and atomic loads

* `safe_rmw_at`: a read-modify-write at a cell that, for every invariant heap, is mapped in the
  thread's heap or the invariant's, and whose effect can be re-split into a new owned heap and a
  new invariant heap;
* `safe_load_at`: an atomic (non-`na`) load from a cell of the thread's heap or the invariant's,
  which keeps every cell where it is.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-- Write cell `a`. -/
def setH (H : Heap) (a v : Nat) : Heap := fun x => if x = a then some v else H x

theorem updH_rmw {m : Mode} {a sz o n : Nat} (H : Heap) :
    (Lab.rmw m a sz o n).updH H = setH H a n := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [Lab.updH, Lab.wval, setH]
  · have : a ≠ x := Ne.symm hx
    simp [Lab.updH, Lab.wval, setH, this, hx]

theorem touches_rmw {m : Mode} {a sz o n x : Nat} : Lab.Touches (.rmw m a sz o n) x ↔ x = a := by
  by_cases h : a = x <;> simp [Lab.Touches, Lab.reads, Lab.wval, h]

theorem touches_rd {m : Mode} {fl : Flav} {a sz v x : Nat} :
    Lab.Touches (.rd m fl a sz v) x ↔ x = a := by
  simp [Lab.Touches, Lab.reads, Lab.wval]

/-- **A read-modify-write at a known cell.** For every invariant heap `hI` disjoint from the
thread's heap, the cell is mapped in `h ∪ hI`, and for every old value it may hold, the write's
result re-splits into a new owned heap satisfying the postcondition and a new invariant heap. -/
theorem safe_rmw_at {I : HProp} {Q : Regs → HProp} {d : Reg} {m : Mode} {sz : Nat} {op : RmwOp}
    {a arg : Expr} {rs : Regs} {h : Heap} {c : Nat} (hc : (a.eval rs).toNat = c)
    (H : ∀ hI, I hI → Heap.Disjoint h hI → (Heap.union h hI c).isSome ∧
      ∀ old, Heap.union h hI c = some old →
        ∃ h' hI', Heap.Disjoint h' hI' ∧
          Heap.union h' hI' = setH (Heap.union h hI) c (op.result rs sz old (arg.eval rs)) ∧
          I hI' ∧ Q (rs.set d (BitVec.ofNat 64 old)) h') :
    Csl.Safe I Q (.rmw d m sz op a arg) rs h := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' st => by cases st) ?_
  intro lab s' rs' st
  cases st with
  | rmw hv =>
    rename_i old
    refine ⟨rfl, rfl, (fun e => by cases e), fun _ hI hIi hd => ?_⟩
    obtain ⟨hsome, hstep⟩ := H hI hIi hd
    refine ⟨fun x hx => ?_, (fun e => by cases e), fun hok => ?_⟩
    · rw [touches_rmw, hc] at hx; subst hx; exact hsome
    · have hold : Heap.union h hI c = some old := by
        have := hok (c, old) (by simp [Lab.reads, hc])
        exact this
      obtain ⟨h', hI', d', e', i', q'⟩ := hstep old hold
      refine ⟨h', hI', d', ?_, i', q', fun e => by cases e⟩
      rw [e', updH_rmw, hc]

/-- **An atomic load at a known cell.** For every invariant heap, the cell is mapped in
`h ∪ hI`, and whatever value it holds there satisfies the postcondition on the same heap. -/
theorem safe_load_at {I : HProp} {Q : Regs → HProp} {d : Reg} {m : Mode} {sz : Nat} {fl : Flav}
    {a : Expr} {rs : Regs} {h : Heap} {c : Nat} (hm : m ≠ .na) (hc : (a.eval rs).toNat = c)
    (H : ∀ hI, I hI → Heap.Disjoint h hI → (Heap.union h hI c).isSome ∧
      ∀ v, Heap.union h hI c = some v → Q (rs.set d (BitVec.ofNat 64 v)) h) :
    Csl.Safe I Q (.load d m sz fl a) rs h := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' st => by cases st) ?_
  intro lab s' rs' st
  cases st with
  | load hv =>
    rename_i v
    have hna' : (Lab.rd m fl (a.eval rs).toNat sz v).na = false := by
      cases m <;> simp_all [Lab.na]
    refine ⟨rfl, rfl, (fun e => by rw [hna'] at e; cases e), fun _ hI hIi hd => ?_⟩
    obtain ⟨hsome, hq⟩ := H hI hIi hd
    refine ⟨fun x hx => ?_, fun _ x hx => by simp [Lab.wval] at hx, fun hok => ?_⟩
    · rw [touches_rd, hc] at hx; subst hx; exact hsome
    · have hv' : Heap.union h hI c = some v := by
        have := hok ((a.eval rs).toNat, v) (by simp [Lab.reads])
        rw [hc] at this; exact this
      refine ⟨h, hI, hd, ?_, hIi, hq v hv', fun _ _ x => x⟩
      funext x; simp [Lab.updH, Lab.wval]

end Silmaril.Proofs.X86.Concurrency.Cir.Rc
