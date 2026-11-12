module

public import Silmaril.Elf.Link.Dyn.Pages.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Thms

/-! # Pages of an included file are chunks of it

`pages_of`: for every chunk size `c` and chunk list, every page lies in the file
`⟨chunksVal c len cs, chunksLen c len cs⟩` (silmaril's value of an `include_bytes` file) and
holds its bytes. Proved with the standard axioms. -/

@[expose] public section

namespace Silmaril.Elf.Link.DynElf

open Silmaril.X86.Link (Blob)
open Silmaril.Project.Shapes (chunksVal chunksLen)

private theorem pow256 (m : Nat) : (256 : Nat) ^ m = 2 ^ (8 * m) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

private theorem shift_tail (X R k s : Nat) (hX : X < 2 ^ k) :
    (X + 2 ^ k * R) >>> (k + s) = R >>> s := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hX, Nat.zero_add]

/-- **Every page of an included file is part of it.** -/
theorem pages_of (c : Nat) : ∀ (len : Nat) (cs : List Nat),
    ChunksOf ⟨chunksVal c len cs, chunksLen c len cs⟩ (pages c len cs)
  | _, [] => by intro ch h; simp [pages] at h
  | len, x :: cs => by
    intro ch hch
    simp only [pages, List.mem_cons] at hch
    simp only [chunksVal, chunksLen, pow256]
    have hX : x % 2 ^ (8 * min c len) < 2 ^ (8 * min c len) := Nat.mod_lt _ (Nat.two_pow_pos _)
    rcases hch with rfl | hch
    · refine ⟨by simp, ?_⟩
      simp only [Nat.mul_zero, Nat.shiftRight_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
    · split at hch
      · simp at hch
      · rename_i hlen
        obtain ⟨ch0, h0, rfl⟩ := List.mem_map.mp hch
        obtain ⟨h1, h2⟩ := pages_of c (len - c) cs ch0 h0
        have hm : min c len = c := by omega
        rw [hm] at hX ⊢
        refine ⟨by simp only at h1 ⊢; omega, ?_⟩
        simp only
        rw [show 8 * (ch0.off + c) = 8 * c + 8 * ch0.off by omega, shift_tail _ _ _ _ hX]
        exact h2

/-- The pages from `off`, relative to `off`, are part of the file. -/
theorem pagesFrom_of (c : Nat) : ∀ (off len : Nat) (cs : List Nat) (ch : Chunk),
    ch ∈ pagesFrom c off len cs → off ≤ ch.off ∧
      (Chunk.mk (ch.off - off) ch.len ch.n).Of ⟨chunksVal c len cs, chunksLen c len cs⟩
  | _, _, [] => by intro ch h; simp [pagesFrom] at h
  | off, len, x :: cs => by
    intro ch hch
    simp only [pagesFrom, List.mem_cons] at hch
    simp only [chunksVal, chunksLen, pow256]
    have hX : x % 2 ^ (8 * min c len) < 2 ^ (8 * min c len) := Nat.mod_lt _ (Nat.two_pow_pos _)
    rcases hch with rfl | hch
    · refine ⟨le_rfl, by simp, ?_⟩
      simp only [Nat.sub_self, Nat.mul_zero, Nat.shiftRight_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
    · split at hch
      · simp at hch
      · rename_i hlen
        obtain ⟨hle, h1, h2⟩ := pagesFrom_of c (off + c) (len - c) cs ch hch
        have hm : min c len = c := by omega
        rw [hm] at hX ⊢
        refine ⟨by omega, by simp only at h1 ⊢; omega, ?_⟩
        simp only at h2 ⊢
        rw [show 8 * (ch.off - off) = 8 * c + 8 * (ch.off - (off + c)) by omega,
          shift_tail _ _ _ _ hX]
        exact h2

/-- **Every page from offset `0` is part of the file.** -/
theorem pagesFrom_zero_of (c len : Nat) (cs : List Nat) :
    ChunksOf ⟨chunksVal c len cs, chunksLen c len cs⟩ (pagesFrom c 0 len cs) := by
  intro ch h
  have := (pagesFrom_of c 0 len cs ch h).2
  simpa using this

/-- Two adjacent reads of the file make one. -/
theorem blobRead_split {b : Blob} {o a w lo hi : Nat} (haw : a < w)
    (h1 : blobRead b o a = some lo) (h2 : blobRead b (o + a) (w - a) = some hi) :
    blobRead b o w = some (lo + 2 ^ (8 * a) * hi) := by
  unfold blobRead Blob.readLEN at *
  split at h1
  · split at h2
    · rename_i c1 c2
      cases h1; cases h2
      have hle : o + w ≤ b.len := by omega
      simp only [show (w = 0 ∨ o + w ≤ b.len) from Or.inr hle, ↓reduceIte, Option.some.injEq]
      rw [show 8 * w = 8 * a + 8 * (w - a) by omega, Nat.pow_add, Nat.mod_mul,
        Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow (m := b.n) (n := 8 * (o + a)),
        Nat.div_div_eq_div_mul, ← Nat.pow_add, show 8 * o + 8 * a = 8 * (o + a) by omega]
    · cases h2
  · cases h1

/-- **The page reader answers as the file.** -/
theorem pageRead_of {b : Blob} {c : Nat} {pg : List Chunk} (hc : ChunksOf b pg) {o w v : Nat}
    (h : pageRead c pg o w = some v) : blobRead b o w = some v := by
  unfold pageRead at h
  split at h
  · rename_i ch hch
    have hm := hc ch (List.mem_of_getElem? hch)
    split at h
    · rename_i v' hv; cases h; exact Chunk.read_of hm hv
    · dsimp only at h
      split at h
      · rename_i haw
        split at h
        · rename_i lo ch' hlo hch'
          have hm' := hc ch' (List.mem_of_getElem? hch')
          cases hhi : ch'.read (o + (ch.off + ch.len - o)) (w - (ch.off + ch.len - o)) with
          | none => rw [hhi] at h; cases h
          | some hi =>
            rw [hhi] at h; cases h
            exact blobRead_split haw.2 (Chunk.read_of hm hlo) (Chunk.read_of hm' hhi)
        · cases h
      · cases h
  · cases h

/-- **A reading program that succeeds on the pages succeeds on the file.** -/
theorem run_pages {α : Type} {b : Blob} {c : Nat} {pg : List Chunk} (hc : ChunksOf b pg)
    {p : Rd α} {a : α} (h : p.run (pageRead c pg) = some a) : p.run (blobRead b) = some a :=
  Rd.run_mono (fun _ _ _ => pageRead_of hc) p a h
