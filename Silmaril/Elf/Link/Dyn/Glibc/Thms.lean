module

public import Silmaril.Elf.Link.Dyn.Glibc.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Thms

/-! # glibc 2.39: the lookup facts, kernel-checked on the sparse chunks

PROVED (standard axioms), for **every** file `F` agreeing with the chunks:

* `libc_info`, `ld_info`: what the loader reads from each object's headers;
* `libc_lookup`, `ld_lookup`: every entry of `libcFacts`/`ldFacts` is what ld.so's lookup
  (`Elf.lookupDef`) finds in that object.

Each fact is one `decide +kernel` over the chunks (`run_sparse`); no theorem unfolds the
2 MB file. These are the facts every executable linked against this glibc reuses.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Glibc

open Silmaril.Elf.Link.DynElf.Elf
open Silmaril.X86.Link (Blob)

/-- The whole table on the sparse view (one kernel evaluation). -/
def factsHold (cs : List Chunk) (d : DynInfo) (T : List (Ref × Bool × Option Def)) : Bool :=
  T.all fun e => (lookupDef d e.1 e.2.1).run (sparseRead cs) == some e.2.2

theorem facts_of {cs : List Chunk} {d : DynInfo} {T : List (Ref × Bool × Option Def)}
    (h : factsHold cs d T = true) {F : Blob} (hF : ChunksOf F cs) :
    ∀ e ∈ T, (lookupDef d e.1 e.2.1).run (blobRead F) = some e.2.2 := by
  intro e he
  have := List.all_eq_true.mp h e he
  exact run_sparse hF (by simpa using this)

theorem libc_info_sparse : dynInfo.run (sparseRead libcChunks) = some libcInfo := by
  decide +kernel

theorem ld_info_sparse : dynInfo.run (sparseRead ldChunks) = some ldInfo := by
  decide +kernel

theorem libc_facts_sparse : factsHold libcChunks libcInfo libcFacts = true := by
  decide +kernel

theorem ld_facts_sparse : factsHold ldChunks ldInfo ldFacts = true := by
  decide +kernel

theorem libc_info {F : Blob} (hF : ChunksOf F libcChunks) :
    dynInfo.run (blobRead F) = some libcInfo := run_sparse hF libc_info_sparse

theorem ld_info {F : Blob} (hF : ChunksOf F ldChunks) :
    dynInfo.run (blobRead F) = some ldInfo := run_sparse hF ld_info_sparse

theorem libc_lookup {F : Blob} (hF : ChunksOf F libcChunks) :
    ∀ e ∈ libcFacts, (lookupDef libcInfo e.1 e.2.1).run (blobRead F) = some e.2.2 :=
  facts_of libc_facts_sparse hF

theorem ld_lookup {F : Blob} (hF : ChunksOf F ldChunks) :
    ∀ e ∈ ldFacts, (lookupDef ldInfo e.1 e.2.1).run (blobRead F) = some e.2.2 :=
  facts_of ld_facts_sparse hF

theorem libc_lookup' {F : Blob} (hF : ChunksOf F libcChunks) {r : Ref} {p : Bool}
    {x : Option Def} (h : (r, p, x) ∈ libcFacts) :
    (lookupDef libcInfo r p).run (blobRead F) = some x :=
  by have h' := libc_lookup hF (r, p, x) h; dsimp only at h'; exact h'

theorem ld_lookup' {F : Blob} (hF : ChunksOf F ldChunks) {r : Ref} {p : Bool}
    {x : Option Def} (h : (r, p, x) ∈ ldFacts) :
    (lookupDef ldInfo r p).run (blobRead F) = some x :=
  by have h' := ld_lookup hF (r, p, x) h; dsimp only at h'; exact h'

end Silmaril.Elf.Link.Dyn.Glibc
