module

public import Silmaril.Elf.Decode.Defs
import Silmaril.Proofs.Elf.Decode

/-! # Three-valued decoding: agreement with the parse, and stability under fuller views

* `decode_whole_ok_iff`: on a whole file, `decode` answers `ok A` exactly when `Parses F A`;
* `decode_whole_final`: a whole file is never `incomplete`;
* `not_parses_of_decode`: an `unsupported` or `invalid` answer on a whole file means no parse;
* `runD_refines`, `decode_refines`: a final answer (not `incomplete`) does not change on a fuller
  view; `prefixOf_refines`, `windows_refines`: the partial views are refined by the whole file.

Proofs: `Silmaril.Proofs.Elf.Decode` (standard axioms only).
-/

@[expose] public section

namespace Silmaril.Elf.Decode

open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.X86.Link (Blob)

/-- A run on a whole file is the run of the two-valued oracle. -/
theorem runD_whole {α : Type} (F : Blob) (p : Rd α) :
    (runD (whole F) p).toOption = p.run (blobRead F) :=
  Proofs.Elf.Decode.runD_whole F p

/-- **On a whole file, `decode` is the parse.** -/
theorem decode_whole_ok_iff (F : Blob) (A : File) : decode (whole F) = .ok A ↔ Parses F A :=
  Proofs.Elf.Decode.decode_whole_ok_iff F A

/-- A whole file is never `incomplete`. -/
theorem decode_whole_final (F : Blob) : (decode (whole F)).Final :=
  Proofs.Elf.Decode.decode_whole_final F

/-- An answer other than `ok` on a whole file means the file has no parse. -/
theorem not_parses_of_decode {F : Blob} (h : ∀ A, decode (whole F) ≠ .ok A) (A : File) :
    ¬ Parses F A := fun hp => h A ((decode_whole_ok_iff F A).mpr hp)

/-- A reading program never answers `unsupported`: only `decode`'s identification does. -/
theorem runD_ne_unsupported {α : Type} (r : ASrc) (p : Rd α) (u : Unsupported) :
    runD r p ≠ .unsupported u :=
  Proofs.Elf.Decode.runD_ne_unsupported r p u

/-- **A final answer is stable**: a fuller view gives the same answer. -/
theorem runD_refines {α : Type} {v w : ASrc} (h : Refines v w) (p : Rd α)
    (hf : (runD v p).Final) : runD w p = runD v p :=
  Proofs.Elf.Decode.runD_refines h p hf

/-- **A final `decode` answer is stable** (an `unsupported` or `invalid` verdict on a partial view
is the verdict on the whole file). -/
theorem decode_refines {v w : ASrc} (h : Refines v w) (hf : (decode v).Final) :
    decode w = decode v :=
  Proofs.Elf.Decode.decode_refines h hf

theorem prefixOf_refines (F : Blob) (k : Nat) : Refines (prefixOf F k) (whole F) :=
  Proofs.Elf.Decode.prefixOf_refines F k

theorem windows_refines (F : Blob) (ws : List Span) :
    Refines (windows ws (blobRead F)) (whole F) :=
  Proofs.Elf.Decode.windows_refines F ws

/-- A final answer on a prefix is the answer on the whole file. -/
theorem decode_prefix {F : Blob} {k : Nat} (hf : (decode (prefixOf F k)).Final) :
    decode (whole F) = decode (prefixOf F k) :=
  decode_refines (prefixOf_refines F k) hf

end Silmaril.Elf.Decode
