module

public import Silmaril.X86.Ext.Store

/-! # Memory facts for segment VCs

Byte-wise loads (what a byte-copy loop's invariant naturally says) and span reads (what a
callee contract such as `Sha256O2.SysVEntry` asks for) are interchangeable:
`readBytes_of_loads`. -/

@[expose] public section

namespace Silmaril.X86.SegVC

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext

/-- One byte read through `loadN … 1`. -/
theorem readBytes_one_of_loadN {m : Memory} {a : Word} {b : Byte}
    (h : loadN m a 1 = some (BitVec.ofNat 64 b.toNat)) : m.readBytes a.toNat 1 = some [b] := by
  unfold loadN at h
  cases hr : m.readBytes a.toNat 1 with
  | none => rw [hr] at h; cases h
  | some bs =>
    rw [hr] at h
    have hlen : bs.length = 1 := Memory.readWith_length hr
    match bs, hlen with
    | [b'], _ =>
      simp only [Option.map_some, Option.some.injEq, leValue, Nat.mul_zero, Nat.add_zero] at h
      have : b'.toNat = b.toNat := by
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        have h1 := b'.isLt; have h2 := b.isLt
        omega
      rw [BitVec.toNat_inj.mp this]

/-- **Byte-wise loads give a span read.** -/
theorem readBytes_of_loads {m : Memory} {a : Word} :
    ∀ {bs : List Byte}, a.toNat + bs.length < 2 ^ 64 →
      (∀ j (hj : j < bs.length), loadN m (a + BitVec.ofNat 64 j) 1 =
        some (BitVec.ofNat 64 bs[j].toNat)) →
      m.readBytes a.toNat bs.length = some bs
  | [], fit, _ => by
    simp [Memory.readBytes, Memory.readWith, Memory.checkSpan, Memory.readBacking,
      Silmaril.Process.addressLimit] at fit ⊢
    omega
  | b :: rest, fit, h => by
    have h0 := h 0 (by simp)
    simp only [BitVec.add_zero, List.getElem_cons_zero] at h0
    have h0 : loadN m a 1 = some (BitVec.ofNat 64 b.toNat) := by simpa using h0
    have first := readBytes_one_of_loadN h0
    have hfit : (a + 1#64).toNat = a.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; simp at fit; omega
    have rest' : m.readBytes (a + 1#64).toNat rest.length = some rest := by
      apply readBytes_of_loads (by simp at fit; omega)
      intro j hj
      have := h (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [← this]
      congr 1
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hfit] at rest'
    have := Memory.readBytes_append first rest'
    simpa [Nat.add_comm] using this

end Silmaril.X86.SegVC
