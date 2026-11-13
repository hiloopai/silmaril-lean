module

public import Silmaril.Wasm.Jco.Styles.Realloc.Defs
public import Silmaril.Wasm.Jco.Basic.Thms

/-!
# `realloc` with a nonzero old pointer: the shim computes the emulation

* `reallocShimX_zero`: with old pointer 0 the shim is `alloc(size, align)`, the `reallocShim` of
  `wrap`, whatever `alloc` returns.
* **`reallocShimX_run`**: when `alloc` returns one `i32`, the shim computes `reallocEmu` on every
  `i32` argument list (`reallocShimX_ne` for a nonzero old pointer).
* `reallocEmu_zero`: the emulation with old pointer 0 is `alloc(size, align)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst)

theorem execX_cons (i : XInstr) (is : List XInstr) (f : Frame) :
    execX M (i :: is) f = (i.step M f >>= fun f' => execX M is f') := by
  simp [execX]

theorem reallocShimX_zero (alloc : String) (os al ns : BitVec 32) :
    (reallocShimX alloc).run M [Flat.i32 0, Flat.i32 os, Flat.i32 al, Flat.i32 ns] =
      M.call alloc [Flat.i32 ns, Flat.i32 al] := by
  simp [XFn.run, reallocShimX, execX_cons, XInstr.step, AInstr.step, RM.bind_assoc, execX, asI32?]

theorem reallocShimX_ne (alloc : String) {old : BitVec 32} (h : old ≠ 0) (os al ns : BitVec 32)
    (hA : RM.Returns (M.call alloc [Flat.i32 ns, Flat.i32 al]) fun r => ∃ p, r = [Flat.i32 p]) :
    (reallocShimX alloc).run M [Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns] =
      reallocEmu M alloc old os al ns := by
  have hb : (old == 0) = false := by simpa using h
  simp only [reallocEmu, hb, Bool.false_eq_true, ↓reduceIte]
  simp [XFn.run, reallocShimX, execX_cons, XInstr.step, AInstr.step, RM.bind_assoc, execX, asI32?]
  split
  · next hc => exact absurd (by simpa using hc) h
  rw [RM.bind_assoc]
  refine RM.bind_congr_returns hA ?_
  rintro r ⟨p, rfl⟩
  simp only [single32?, copyBytes, RM.ofOption_some, RM.pure_bind, RM.bind_assoc]
  by_cases hle : ns.toNat ≤ os.toNat
  · simp [hle, RM.bind_assoc]
  · simp [hle, Nat.min_eq_left (by omega : os.toNat ≤ ns.toNat), RM.bind_assoc]

theorem reallocEmu_zero (alloc : String) (os al ns : BitVec 32) :
    reallocEmu M alloc 0 os al ns = M.call alloc [Flat.i32 ns, Flat.i32 al] := by
  simp [reallocEmu]

/-- **The shim computes the emulated `realloc`** on `i32` arguments, when `alloc` returns one
`i32`. -/
theorem reallocShimX_run (alloc : String) (old os al ns : BitVec 32)
    (hA : RM.Returns (M.call alloc [Flat.i32 ns, Flat.i32 al]) fun r => ∃ p, r = [Flat.i32 p]) :
    (reallocShimX alloc).run M [Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns] =
      reallocEmuF M alloc [Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns] := by
  show _ = reallocEmu M alloc old os al ns
  by_cases h : old = 0
  · rw [h, reallocShimX_zero, reallocEmu_zero]
  · exact reallocShimX_ne M alloc h os al ns hA

end Silmaril.Wasm.Jco
