module

public import Silmaril.Process.Mt.Csl.Defs

/-!
# A non-vacuity example: a mutex-protected counter

Any number of threads run the same code on a memory of naturals (`Nat → Nat`): cell `lk` is a
lock word, cell `ctr` a counter.

| pc | kind | action |
|---|---|---|
| 0 | atomic (`lock`) | if `[lk] = 0` then `[lk] := 1` (blocks otherwise) |
| 1 | plain | `[ctr] := [ctr] + 1` (footprint `ctr`) |
| 2 | atomic (`unlock`) | `[lk] := 0` (a fault unless `[lk] = 1`) |
| 3 | finished | |

The lock invariant `inv`: unlocked and owning the counter (`unlocked v`), or locked (`locked`).
Lock moves the counter cell from the invariant to the thread, unlock moves it back (`own`).
`Example/Thms` proves the threads safe, hence (by `Csl.adequacy`) no fault and no race in any
reachable configuration: in particular **mutual exclusion** (`excl`), as two threads at pc 1
would race on `ctr`.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Csl.Example

/-- The lock word. -/
def lk : Nat := 0
/-- The counter. -/
def ctr : Nat := 1

/-- Memories: every cell holds a natural. -/
def store : Store (Nat → Nat) Nat Nat := ⟨fun m a => some (m a)⟩

/-- Write one cell. -/
def wr (m : Nat → Nat) (a v : Nat) : Nat → Nat := fun x => if x = a then v else m x

/-- The threads. -/
def thr : TIsa store where
  St := Nat
  step _ s m s' m' := s = 1 ∧ s' = 2 ∧ m' = wr m ctr (m ctr + 1)
  fault _ _ _ := False
  fp _ s _ a := s = 1 ∧ a = ctr
  atom _ s m s' m' := (s = 0 ∧ m lk = 0 ∧ s' = 1 ∧ m' = wr m lk 1) ∨
    (s = 2 ∧ s' = 3 ∧ m' = wr m lk 0)
  afault _ s m := s = 2 ∧ m lk ≠ 1
  spawn _ _ _ _ _ _ _ := False
  done s := s = 3

/-- The lock free, the counter at `v`. -/
def unlocked (v : Nat) : Heap Nat Nat := fun a => if a = lk then some 0 else if a = ctr then some v else none
/-- The lock held. -/
def locked : Heap Nat Nat := fun a => if a = lk then some 1 else none
/-- The counter at `v`. -/
def counter (v : Nat) : Heap Nat Nat := fun a => if a = ctr then some v else none

/-- The lock invariant. -/
def inv : HProp Nat Nat := fun h => (∃ v, h = unlocked v) ∨ h = locked

/-- What a thread owns: nothing outside the critical section, the counter inside. -/
def own (_t : Nat) (s : Nat) (h : Heap Nat Nat) : Prop :=
  ((s = 0 ∨ s = 3) ∧ h = Heap.empty) ∨ ((s = 1 ∨ s = 2) ∧ ∃ v, h = counter v)

/-- The postcondition: a finished thread owns nothing. -/
def post (_t : Nat) (_s : Nat) (h : Heap Nat Nat) : Prop := h = Heap.empty

/-- The start: threads `0 … n-1` at pc 0, the lock free, the counter at `v`. -/
def start (n v : Nat) : Cfg thr :=
  ⟨fun t => if t < n then some (0 : Nat) else none, fun a => if a = ctr then v else 0⟩

end Silmaril.Process.Mt.Csl.Example
