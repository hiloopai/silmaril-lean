module

public import Silmaril.X86.Str9K.Defs

/-!
# `Str9K`: lifting runs of the machines below

`Str9K.extendsStr9Fs` (and the other lenses of `Str9K.Defs`) turn a run of a lower machine on the
view of a `Str9K` state into a `Str9K` run. Here the lens for `Str9Fs` is unfolded: a `Str9Fs` run
from `x.s.x.m` is a `Str9K` run from `x` to a state whose `MState` is the end of the run, with the
XMM file, the ghost (`tsc`, `cetOff`), the kernel and the answer stream unchanged (`fs_lift`).
`fs_lift_ex` is the form for existential run statements.
-/

@[expose] public section

namespace Silmaril.X86.Str9K

open Silmaril.X86 (MState)
open Silmaril.Machine.Execution (Reaches)

/-- **A `Str9Fs` run of the `MState` of `x` is a `Str9K` run of `x`**: the end state has that
`MState`; the XMM file, `tsc`, `cetOff`, the kernel and the answers are those of `x`. -/
theorem fs_lift {x : KState} {m' : MState} (h : Reaches Str9Fs.step x.s.x.m m') :
    ∃ y : KState, Reaches isa.step x y ∧ y.s.x.m = m' ∧ y.s.x.xmm = x.s.x.xmm ∧
      y.s.tsc = x.s.tsc ∧ y.s.cetOff = x.s.cetOff ∧ y.k = x.k ∧ y.ans = x.ans :=
  ⟨_, extendsStr9Fs.reaches h, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fs_lift` for a run given as an existential with a property of the end `MState`. -/
theorem fs_lift_ex {x : KState} {P : MState → Prop}
    (h : ∃ m', Reaches Str9Fs.step x.s.x.m m' ∧ P m') :
    ∃ y : KState, Reaches isa.step x y ∧ P y.s.x.m ∧ y.s.x.xmm = x.s.x.xmm ∧
      y.s.tsc = x.s.tsc ∧ y.s.cetOff = x.s.cetOff ∧ y.k = x.k ∧ y.ans = x.ans := by
  obtain ⟨m', hr, hp⟩ := h
  obtain ⟨y, hy, rfl, h1, h2, h3, h4, h5⟩ := fs_lift hr
  exact ⟨y, hy, hp, h1, h2, h3, h4, h5⟩

end Silmaril.X86.Str9K
