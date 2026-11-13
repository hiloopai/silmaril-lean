module

public import Silmaril.X86.Flow.Defs
import Silmaril.X86.Ext.SymExec

/-! Proofs for `Silmaril.X86.Flow`: with a stable decoder, the instruction read at an address is
unique (`at_unique`). -/

@[expose] public section

namespace Silmaril.Proofs.X86.Flow

open Silmaril.X86 (Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Flow

/-- A fetch of `l ≤ n` bytes is the prefix of a fetch of `n`. -/
theorem fetch_prefix {m : Memory} {a n l : Nat} {s : List Byte} (h : m.fetchBytes a n = some s)
    (hl : l ≤ n) : m.fetchBytes a l = some (s.take l) := by
  rcases Nat.eq_zero_or_pos l with rfl | hpos
  · have hp := Memory.readWith_permitted h
    simp only [Memory.Permitted, Memory.checkSpan_iff] at hp
    have h1 : m.checkSpan .execute a 0 = true := by
      rw [Memory.checkSpan_iff]; exact ⟨hp.1, by omega, fun o ho => absurd ho (Nat.not_lt_zero _)⟩
    simp [Memory.fetchBytes, Memory.readWith, h1, Memory.readBacking]
  · have := Memory.readWith_sub_range (address := a) (offset := 0) (len := l) h (by omega) (by omega)
    simpa [Memory.fetchBytes] using this

/-- **The instruction at an address is unique**: what a stable decoder reads from a fetch of
`n` bytes is what it reads from any fetch of exactly the instruction's length. -/
theorem at_unique {D : FlowDec} (hD : D.Stable) {m : Memory} {a n l l' : Nat} {s w : List Byte}
    {i i' : D.Instr} (hs : m.fetchBytes a n = some s) (hds : D.decode s = some (i', l'))
    (hw : m.fetchBytes a l = some w) (hdw : D.decode w = some (i, l)) : i = i' ∧ l = l' := by
  obtain ⟨hl's, hs'⟩ := hD s i' l' hds
  obtain ⟨_, hw'⟩ := hD w i l hdw
  have hsn : s.length = n := Memory.readWith_length hs
  have hwl : w.length = l := Memory.readWith_length hw
  by_cases hle : l ≤ l'
  · -- `w` is a prefix of `s`
    have hwt : w = s.take l := by
      have := fetch_prefix hs (by omega : l ≤ n); rw [hw] at this; exact Option.some.inj this
    have e1 := hw' ((s.take l').drop l)
    have e2 := hs' []
    rw [List.append_nil] at e2
    have : w.take l ++ (s.take l').drop l = s.take l' := by
      have h3 : (s.take l').take l = s.take l := by rw [List.take_take, Nat.min_eq_left hle]
      rw [hwt, List.take_take, Nat.min_self, ← h3, List.take_append_drop]
    rw [this, e2] at e1
    simp only [Option.some.injEq, Prod.mk.injEq] at e1
    exact ⟨e1.1.symm, e1.2.symm⟩
  · -- `s`'s instruction is a prefix of `w`
    exfalso
    have h1 : m.fetchBytes a l' = some (s.take l') := fetch_prefix hs (by omega)
    have h2 : m.fetchBytes a l' = some (w.take l') := fetch_prefix hw (by omega)
    rw [h1] at h2
    have hst : s.take l' = w.take l' := Option.some.inj h2
    have e := hs' (w.drop l')
    rw [hst, List.take_append_drop] at e
    rw [hdw] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    omega

end Silmaril.Proofs.X86.Flow
