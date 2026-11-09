module

public import Silmaril.X86.Ladder.Pinned.Defs
public import Silmaril.X86.Link.Blob.Thms

/-! # Pinned ladder executables: soundness of the checks

`check_sound`: `check exe perms addr code = true` gives `LoadedAt exe perms addr code`, by
`Link.Blob.parse_bytesOf` (the fast reader `parseN` is the public `ELFImage.parse` on the
blob's bytes). `checkAll_sound`: the same for each triple of a `checkAll`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.Pinned

open Silmaril.Process.LPS
open Silmaril.X86.Link
open Silmaril.X86.Ladder.Pinned

theorem check_sound {exe : Blob} {perms : String} {addr : Nat} {code : List (BitVec 8)}
    (h : check exe perms addr code = true) : LoadedAt exe perms addr code := by
  unfold check at h
  split at h
  · rename_i records hparse
    obtain ⟨seg, mem, hseg⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hseg
    refine ⟨records, ?_, seg, mem, hseg.1, hseg.2⟩
    rw [Blob.bytes, Blob.parse_bytesOf]
    exact hparse
  · cases h

theorem checkAll_sound {exe : Blob} {slices : List (String × Nat × List (BitVec 8))}
    (h : checkAll exe slices = true) {perms : String} {addr : Nat} {code : List (BitVec 8)}
    (mem : (perms, addr, code) ∈ slices) : LoadedAt exe perms addr code := by
  apply check_sound
  unfold checkAll at h
  unfold check
  split at h
  · exact (List.all_eq_true.mp h) _ mem
  · cases h

end Silmaril.Proofs.X86.Ladder.Pinned
