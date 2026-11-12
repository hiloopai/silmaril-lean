module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Raw.Wasm.Component.Reference

@[expose] public section

/-!
# Proof (unrefined): a REF copy completes itself with progress `0` only when its buffer is empty

`ref_own_progress_pos`, stated and explained in `Silmaril.Wasm.Component.Async.RefZero.Thms`: a
case analysis of `Silmaril.Wasm.Component.Runtime.copyCore` (REF `End.copy`, L956-979).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.RefZero

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Component.Engine (CoreEngine)

variable {E : CoreEngine}

/-- The end posted by the copying end in case 3 records progress `buf.progress + n` with
`n = min buf.remain ob.remain`. -/
theorem advance_progress_pos {buf ob : BufferDesc E} (h : 0 < buf.remain ∧ 0 < ob.remain) :
    0 < (buf.advance (min buf.remain ob.remain)).progress := by
  rw [BufferDesc.progress_advance]
  have : 0 < min buf.remain ob.remain := Nat.lt_min.2 h
  omega

/-- **In REF, a copy never completes itself with progress `0` unless its buffer is empty**: if
`copyCore` changes the pending event of the copying end, then the buffer was empty or the
recorded progress is positive. -/
theorem ref_own_progress_pos {s s' : CStore E} {e : EndId} {x z : End E} {buf : BufferDesc E}
    {isRead : Bool} {a : CopyAction E} (h : copyCore e buf isRead s = .ok (s', a))
    (hx : s.end? e = some x) (hz : s'.end? e = some z) :
    z.common.pending = x.common.pending ∨ buf.remain = 0 ∨
      ∃ p, 0 < p ∧ z.common.pending = some (x.pendingFor e p) := by
  unfold copyCore at h
  rw [hx] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  split at h
  · cases h
    left
    rw [end?_setEnd_self hx] at hz
    cases hz; rfl
  next o ho =>
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    next y hy =>
      have hne : e ≠ o := fun h' => by simp_all
      split at h
      · cases h
        left
        rw [end?_setEnd_self hx] at hz
        cases hz; rfl
      next ob hob =>
        split at h
        next hpos =>
          split at h
          · exact absurd h (by simp)
          cases h
          right; right
          refine ⟨(buf.advance (min buf.remain ob.remain)).progress, advance_progress_pos hpos, ?_⟩
          rw [end?_setEnd_ne _ _ hne, end?_setEnd_self hx] at hz
          cases hz; rfl
        next hpos =>
          split at h
          · cases h
            left
            rw [end?_setEnd_ne _ _ hne, end?_setEnd_self hx] at hz
            cases hz; rfl
          next h4 =>
            cases h
            right; left
            omega

/-- **In REF, a copy completes its parked peer with progress `0` only when the peer's buffer is
empty**: if `copyCore` changes the pending event of the peer `o`, whose parked buffer is `ob`
with no progress yet, then `ob` was empty or the recorded progress is positive. -/
theorem ref_peer_progress_pos {s s' : CStore E} {e o : EndId} {x y z : End E}
    {buf ob : BufferDesc E} {isRead : Bool} {a : CopyAction E}
    (h : copyCore e buf isRead s = .ok (s', a)) (hx : s.end? e = some x) (ho : x.other = some o)
    (hy : s.end? o = some y) (hb : y.buffer = some ob) (hz : s'.end? o = some z) :
    z.common.pending = y.common.pending ∨ ob.remain = 0 ∨
      ∃ p, 0 < p ∧ z.common.pending = some (y.pendingFor o p) := by
  unfold copyCore at h
  rw [hx] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  rw [ho] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  next hne =>
    rw [hy] at h
    dsimp only at h
    rw [hb] at h
    dsimp only at h
    have hne' : o ≠ e := hne
    split at h
    next hpos =>
      split at h
      · exact absurd h (by simp)
      cases h
      right; right
      refine ⟨(ob.advance (min buf.remain ob.remain)).progress, ?_, ?_⟩
      · rw [BufferDesc.progress_advance]
        have : 0 < min buf.remain ob.remain := Nat.lt_min.2 hpos
        omega
      · rw [end?_setEnd_self (by rw [end?_setEnd_ne _ _ hne']; exact hy)] at hz
        cases hz; rfl
    next hpos =>
      split at h
      next h4 =>
        cases h
        right; left
        rcases h4 with h4 | ⟨-, h4⟩
        · omega
        · exact h4
      next =>
        cases h
        left
        rw [end?_setEnd_ne _ _ hne', hy] at hz
        cases hz; rfl

end Silmaril.Wasm.Component.Async.RefZero
