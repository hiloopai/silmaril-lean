module

public import Silmaril.X86.Str9L.Defs
public import Silmaril.X86.Str9X.Thms

/-!
# `Str9L`: the conservative extension of `Str9X`, the lane law

* `str9x_none`, `step_of_str9x`: where `Str9X` claims no bytes it has no step, so **every
  `Str9X` step is a step** with MXCSR kept.
* `step_of_fetch_lane`: a lane form decoded at the fetch window.
-/

@[expose] public section

namespace Silmaril.X86.Str9L

open Silmaril.X86 (State Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Features (Extension FeatureSet)
open Silmaril.Process (Memory)

/-- Where no decoder of `Str9X` claims the bytes, `Str9X` has no step. -/
theorem str9x_none {x : Str9X.XState} (h : lowerClaims x = false) : Str9X.step x = none := by
  simp only [lowerClaims, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Str9X.step, h1, Bool.false_eq_true, ite_false, h2]

/-- **Every `Str9X` step is a step**, with MXCSR kept. -/
theorem step_of_str9x {F : FeatureSet} {exts : List Extension} {s : LState} {x' : Str9X.XState}
    (h : Str9X.step s.x = some x') : step F exts s = some ⟨x', s.mxcsr⟩ := by
  cases hc : lowerClaims s.x
  · rw [str9x_none hc] at h; cases h
  · simp [step, hc, h]

/-- **The law of a lane form** at the fetch window: where `Str9X` claims nothing, the first
lane that decodes the window runs on the lane view. -/
theorem step_of_fetch_lane {F : FeatureSet} {exts : List Extension} {s : LState} {e : Extension}
    {i : e.Syntax} {n : Nat} {m : Silmaril.X86.Features.MState} (hc : lowerClaims s.x = false)
    (hd : Silmaril.X86.Features.extDecode exts
      (fetchWindow s.memory maxInstrLength s.core.rip.toNat) = some ⟨e, i, n⟩)
    (hp : s.memory.Permitted .execute s.core.rip.toNat n)
    (hx : Silmaril.X86.Features.extStep F e i n ⟨view s, s.memory⟩ = .retired m) :
    step F exts s = some (back s m.state m.memory) := by
  simp only [step, hc, Bool.false_eq_true, ite_false, hd, hp, ite_true, execLane, hx]

end Silmaril.X86.Str9L
