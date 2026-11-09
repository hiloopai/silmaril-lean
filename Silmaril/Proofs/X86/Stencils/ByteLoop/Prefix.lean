module

public import Silmaril.X86.Stencils.ByteLoop.Defs

/-!
# The written-prefix invariant of byte loops

One-byte loads and stores as explicit memories (`storeN_one`, `loadN_one`), and the algebra
of `Prefix`: it starts empty, grows by one `set1` at its end, is a `WritesWithin` of its
range, and leaves the permissions, the code image and every interval apart from the
destination untouched.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Stencils.ByteLoop

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.Stencils.ByteLoop

theorem checkSpan_one {mem : Memory} {acc : Silmaril.Process.Access} {a : Nat}
    (ha : a < addressLimit) (hp : mem.permits acc a = true) : mem.checkSpan acc a 1 = true := by
  rw [Memory.checkSpan_iff]
  refine ⟨ha, by omega, fun o ho => ?_⟩
  rw [show o = 0 by omega, Nat.add_zero]; exact hp

/-- A one-byte store that is permitted. -/
theorem storeN_one {mem : Memory} {w v : Word} (hp : mem.permits .write w.toNat = true) :
    storeN mem w 1 v = some (set1 mem w.toNat (v.setWidth 8)) := by
  have ha : w.toNat < addressLimit := by simpa [addressLimit] using w.isLt
  simp only [storeN, Memory.writeBytes, Silmaril.X86.Ext.length_leBytes, checkSpan_one ha hp,
    ite_true, set1, Option.some.injEq]
  congr 1

/-- A one-byte load that is permitted and backed. -/
theorem loadN_one {mem : Memory} {w : Word} {b : Byte} (hp : mem.permits .read w.toNat = true)
    (hb : mem.bytes.get? w.toNat = some b) :
    loadN mem w 1 = some (BitVec.ofNat 64 b.toNat) := by
  have ha : w.toNat < addressLimit := by simpa [addressLimit] using w.isLt
  simp only [Std.ExtHashMap.get?_eq_getElem?] at hb
  simp [loadN, Memory.readBytes, Memory.readWith, checkSpan_one ha hp, Memory.readBacking, hb,
    Silmaril.X86.Ext.leValue]

theorem prefix_init (m0 : Memory) (d : Nat) (val : Nat → Option Byte) : Prefix m0 m0 d 0 val :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

theorem prefix_set1 {m0 mem : Memory} {d i : Nat} {val : Nat → Option Byte} {b : Byte}
    (h : Prefix m0 mem d i val) (hv : val i = some b) :
    Prefix m0 (Silmaril.X86.Stencils.ByteLoop.set1 mem (d + i) b) d (i + 1) val := by
  refine ⟨h.regions, fun j hj => ?_, fun a ha => ?_⟩
  · have e := h.inside
    simp only [Silmaril.X86.Stencils.ByteLoop.set1, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.getElem?_insert] at e ⊢
    by_cases e' : j = i
    · subst e'; simp [hv]
    · have : (d + i == d + j) = false := by simp; omega
      simp only [this, Bool.false_eq_true, ite_false]
      exact e j (by omega)
  · have e := h.outside
    simp only [Silmaril.X86.Stencils.ByteLoop.set1, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.getElem?_insert] at e ⊢
    have : (d + i == a) = false := by simp; omega
    simp only [this, Bool.false_eq_true, ite_false]
    exact e a (by omega)

theorem prefix_writesWithin {m0 mem : Memory} {d i : Nat} {val : Nat → Option Byte}
    (h : Prefix m0 mem d i val) {n : Nat} (hi : i ≤ n) :
    m0.WritesWithin mem (fun a => d ≤ a ∧ a < d + n) :=
  ⟨h.regions, fun a ha => h.outside a (by omega)⟩

theorem prefix_permits {m0 mem : Memory} {d i : Nat} {val : Nat → Option Byte}
    (h : Prefix m0 mem d i val) (acc : Silmaril.Process.Access) (a : Nat) :
    mem.permits acc a = m0.permits acc a := by
  unfold Memory.permits; rw [h.regions]

theorem prefix_loaded {m0 mem : Memory} {d i n : Nat} {val : Nat → Option Byte}
    (h : Prefix m0 mem d i val) (hi : i ≤ n) {base : Word} {code : List Byte}
    (hap : Apart d n base.toNat code.length) (hl : Loaded m0 base code) : Loaded mem base code := by
  unfold Loaded
  rw [(prefix_writesWithin h hi).fetchBytes (fun o ho hin => by unfold Apart at hap; omega)]
  exact hl

theorem prefix_readBytes {m0 mem : Memory} {d i n : Nat} {val : Nat → Option Byte}
    (h : Prefix m0 mem d i val) (hi : i ≤ n) {a k : Nat} (hap : Apart d n a k) :
    mem.readBytes a k = m0.readBytes a k :=
  (prefix_writesWithin h hi).readBytes (fun o ho hin => by unfold Apart at hap; omega)

end Silmaril.Proofs.X86.Stencils.ByteLoop
