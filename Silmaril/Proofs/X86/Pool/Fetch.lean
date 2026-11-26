module

public import Silmaril.X86.Pool.Defs

/-!
# Proofs: fetches of `Ext` forms depend only on their own bytes

`FetchStable` (in `Pool/Defs.lean`) asks that a fetch be the same on every memory with the
same mapping list and the same fetched bytes. `openFetch_stable`: for `openEv`, every fetch of
an `Ext` form (`.base`) is stable. This uses `Ext.fetch_eq_decoded_iff` (silmaril): an `Ext`
fetch succeeds exactly when its own bytes, read as one executable span, decode alone.

Fetches of `Ext8` new forms, and of `Open9`/`Atomic9` forms, are not covered: they first need
`Ext.fetch` to fail on the whole fifteen-byte window, which depends on bytes after the
instruction.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Pool

open Silmaril.X86 (State)
open Silmaril.Process (Memory)
open Silmaril.X86.Pool
open Silmaril.X86.MemEvent (Agree openFetch)

/-- Two memories with the same mapping list permit the same accesses. -/
theorem permitted_congr {m m' : Memory} (hr : m.regions = m'.regions)
    {acc : Silmaril.Process.Access} {a n : Nat} (h : m.Permitted acc a n) :
    m'.Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan, Memory.permits] at h ⊢
  rwa [← hr]

/-- A checked read depends only on the mapping list and the bytes read. -/
theorem readWith_congr {m m' : Memory} {acc : Silmaril.Process.Access} {a n : Nat}
    {bs : List Silmaril.X86.Byte} (hag : Agree (fun x => a ≤ x ∧ x < a + n) m m')
    (h : m.readWith acc a n = some bs) : m'.readWith acc a n = some bs := by
  have hlen := Memory.readWith_length h
  subst hlen
  refine Memory.readWith_eq _ _ _ _ (permitted_congr hag.1 (Memory.readWith_permitted h))
    (fun j hj => ?_)
  rw [← Memory.readWith_get h j hj]
  have := hag.2 (a + j) ⟨by omega, by omega⟩
  simpa [Std.ExtHashMap.get?_eq_getElem?] using this.symm

/-- **An `Ext` fetch of `openEv` is stable**: on every memory with the same mapping list and
the same bytes of the instruction, `openFetch` decodes the same instruction. -/
theorem openFetch_stable {mem : Memory} {pc : Nat} {i : Silmaril.X86.Ext.Instr} {k : Nat}
    (h : openFetch mem pc = some (.base i, k)) : FetchStable openEv mem pc (.base i) k := by
  have hx : ∃ n, Silmaril.X86.Ext.fetch mem pc = .decoded i n ∧ k = i.length := by
    cases hE : Silmaril.X86.Ext.fetch mem pc with
    | decoded j n =>
      have h8 := Silmaril.X86.Ext8.fetch_of_ne_undecodable (memory := mem) (address := pc)
        (by rw [hE]; simp)
      simp only [openFetch, h8, hE, Option.some.injEq, Prod.mk.injEq,
        Silmaril.X86.Ext8.Instr.base.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨n, rfl, rfl⟩
    | truncated =>
      have h8 := Silmaril.X86.Ext8.fetch_of_ne_undecodable (memory := mem) (address := pc)
        (by rw [hE]; simp)
      simp [openFetch, h8, hE] at h
    | undecodable =>
      exfalso
      have hne : ∀ j n, Silmaril.X86.Ext8.fetch mem pc ≠ .inl (.decoded j n) := by
        intro j n e
        unfold Silmaril.X86.Ext8.fetch at e
        rw [hE] at e
        simp only at e
        split at e
        · split at e <;> simp at e
        · simp at e
      unfold openFetch at h
      split at h
      · rename_i j n e
        exact hne j n e
      · simp at h
      · simp at h
  obtain ⟨n, hf, rfl⟩ := hx
  have hn := Silmaril.X86.Ext.fetch_length hf
  subst hn
  obtain ⟨bs, hb, hd⟩ := Silmaril.X86.Ext.fetch_eq_decoded_iff.mp hf
  intro mem' hag
  have hx' : Silmaril.X86.Ext.fetch mem' pc = .decoded i i.length :=
    Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr ⟨bs, readWith_congr hag hb, hd⟩
  have h8 := Silmaril.X86.Ext8.fetch_of_ne_undecodable (memory := mem') (address := pc)
    (by rw [hx']; simp)
  change openFetch mem' pc = some (.base i, i.length)
  simp only [openFetch, h8, hx']

end Silmaril.Proofs.X86.Pool
