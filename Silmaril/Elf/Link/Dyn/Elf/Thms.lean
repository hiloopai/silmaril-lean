module

public import Silmaril.Elf.Link.Dyn.Elf.Defs

/-! # Reading programs: soundness of sparse reads

PROVED (standard axioms):

* `Rd.run_mono`: a reading program that succeeds against an oracle succeeds with the same
  result against every oracle that agrees wherever the first one answers;
* `Chunk.read_of`, `sparseRead_of`: a chunk of a file answers as the file does
  (`blobRead`), so **a reading program that succeeds on a sparse view of a file
  (`ChunksOf b cs`) succeeds with the same result on the file** (`run_sparse`);
* `Rd.run_bind`, `Rd.run_pure`, `Rd.run_read_some`, `Rd.run_read_none`: equations of `run`.
-/

@[expose] public section

namespace Silmaril.Elf.Link.DynElf

open Silmaril.X86.Link (Blob)

namespace Rd

theorem run_pure {α : Type} (r : Nat → Nat → Option Nat) (a : α) : (Rd.pure a).run r = some a :=
  rfl

theorem run_fail {α : Type} (r : Nat → Nat → Option Nat) : (Rd.fail : Rd α).run r = none := rfl

theorem run_read_some {α : Type} {r : Nat → Nat → Option Nat} {o w v : Nat} (k : Nat → Rd α)
    (h : r o w = some v) : (Rd.read o w k).run r = (k v).run r := by
  simp only [run, h]

theorem run_read_none {α : Type} {r : Nat → Nat → Option Nat} {o w : Nat} (k : Nat → Rd α)
    (h : r o w = none) : (Rd.read o w k).run r = none := by
  simp only [run, h]

/-- **Monotonicity in the oracle.** -/
theorem run_mono {α : Type} {r r' : Nat → Nat → Option Nat}
    (h : ∀ o w v, r o w = some v → r' o w = some v) :
    ∀ (p : Rd α) (a : α), p.run r = some a → p.run r' = some a := by
  intro p
  induction p with
  | pure a => intro b hb; exact hb
  | fail => intro b hb; cases hb
  | read o w k ih =>
    intro b hb
    cases e : r o w with
    | none => rw [run_read_none k e] at hb; cases hb
    | some v =>
      rw [run_read_some k e] at hb
      rw [run_read_some k (h o w v e)]
      exact ih v b hb

theorem run_bind {α β : Type} (r : Nat → Nat → Option Nat) (p : Rd α) (f : α → Rd β) :
    (p.bind f).run r = (p.run r).bind fun a => (f a).run r := by
  induction p with
  | pure a => rfl
  | fail => rfl
  | read o w k ih =>
    show (Rd.read o w fun v => (k v).bind f).run r = _
    cases e : r o w with
    | none => rw [run_read_none _ e, run_read_none _ e]; rfl
    | some v => rw [run_read_some _ e, run_read_some _ e]; exact ih v

end Rd

/-! ## Chunks are reads of the file -/

theorem shiftRight_mod_of_mod {x y k L s m : Nat}
    (h : x % 2 ^ L = (y >>> k) % 2 ^ L) (hs : s + m ≤ L) :
    (x >>> s) % 2 ^ m = (y >>> (k + s)) % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < m
  · simp only [hi, decide_true, Bool.true_and]
    have hx := congrArg (fun z => z.testBit (s + i)) h
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight] at hx
    have : s + i < L := by omega
    simp only [this, decide_true, Bool.true_and] at hx
    rw [hx, Nat.add_assoc]
  · simp [hi]

/-- A chunk answers as the file. -/
theorem Chunk.read_of {b : Blob} {c : Chunk} (hc : c.Of b) {o w v : Nat}
    (h : c.read o w = some v) : blobRead b o w = some v := by
  unfold Chunk.read at h
  split at h
  · rename_i hin
    cases h
    unfold blobRead Blob.readLEN
    have hle : o + w ≤ b.len := by have := hc.1; omega
    simp only [show (w = 0 ∨ o + w ≤ b.len) from Or.inr hle, ↓reduceIte]
    congr 1
    have e := shiftRight_mod_of_mod (s := 8 * (o - c.off)) (m := 8 * w) hc.2 (by omega)
    rw [e]
    congr 2
    omega
  · cases h

theorem sparseRead_of {b : Blob} {cs : List Chunk} (hc : ChunksOf b cs) {o w v : Nat}
    (h : sparseRead cs o w = some v) : blobRead b o w = some v := by
  induction cs with
  | nil => cases h
  | cons c cs ih =>
    unfold sparseRead at h
    cases e : c.read o w with
    | some v' =>
      rw [e] at h; cases h
      exact Chunk.read_of (hc c (List.mem_cons_self ..)) e
    | none =>
      rw [e] at h
      exact ih (fun c' hm => hc c' (List.mem_cons_of_mem _ hm)) h

/-- **A reading program that succeeds on a sparse view of a file succeeds with the same
result on the file.** -/
theorem run_sparse {α : Type} {b : Blob} {cs : List Chunk} (hc : ChunksOf b cs) {p : Rd α}
    {a : α} (h : p.run (sparseRead cs) = some a) : p.run (blobRead b) = some a :=
  Rd.run_mono (fun _ _ _ => sparseRead_of hc) p a h

/-- The whole file as one chunk. -/
def wholeChunk (b : Blob) : Chunk := ⟨0, b.len, b.n⟩

theorem wholeChunk_of (b : Blob) : (wholeChunk b).Of b := by
  simp [wholeChunk, Chunk.Of]

end Silmaril.Elf.Link.DynElf
