module

public import Silmaril.Process.CLI.Cover.Defs
public import Silmaril.Process.CLI.Loaded.Thms
import Silmaril.Proofs.Process.CLI.Cover

/-!
# Placed segments covered by a `CLI.Image`: facts

PROVED (standard axioms); the proofs are in `Silmaril/Proofs/Process/CLI/Cover.lean`.

* `valueLE_inj`: on byte lists of one length, `valueLE` is injective;
* `Covers.codeIn`, `Covers.dataIn`: an image that covers a segment holds each of its code
  ranges (`CodeIn`) and each of its data ranges (`DataIn`);
* `CodeIn.fetch`, `DataIn.read`: in a loaded image (`Image.Loaded`), held code fetches back
  and held data reads back.

A pinned image then needs one `decide +kernel` (`Covers`, or `CodeIn` directly) per call.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.X86.Link.Blob (valueLE)

/-- On byte lists of one length, `valueLE` is injective. -/
theorem valueLE_inj {xs ys : List Byte} (hl : xs.length = ys.length)
    (h : valueLE xs = valueLE ys) : xs = ys :=
  Silmaril.Proofs.Process.CLI.Cover.valueLE_inj hl h

/-- **A covered code range is held code.** -/
theorem Covers.codeIn {img : Image} {seg : Seg} {a : Nat} {code : List Byte}
    (h : Covers img seg) (hr : ⟨a, code.length, true, valueLE code⟩ ∈ seg.ranges) :
    CodeIn img a code :=
  Silmaril.Proofs.Process.CLI.Cover.Covers.codeIn h hr

/-- **A covered data range is held data.** -/
theorem Covers.dataIn {img : Image} {seg : Seg} {a : Nat} {bytes : List Byte}
    (h : Covers img seg) (hr : ⟨a, bytes.length, false, valueLE bytes⟩ ∈ seg.ranges) :
    DataIn img a bytes :=
  Silmaril.Proofs.Process.CLI.Cover.Covers.dataIn h hr

/-- **Held code fetches back from a loaded image.** -/
theorem CodeIn.fetch {img : Image} {a : Nat} {code : List Byte} {mem : Memory}
    (h : CodeIn img a code) (hl : img.Loaded mem) (pos : 0 < code.length) :
    mem.fetchBytes a code.length = some code :=
  Silmaril.Proofs.Process.CLI.Cover.CodeIn.fetch h hl pos

/-- **Held data reads back from a loaded image.** -/
theorem DataIn.read {img : Image} {a : Nat} {bytes : List Byte} {mem : Memory}
    (h : DataIn img a bytes) (hl : img.Loaded mem) (pos : 0 < bytes.length) :
    mem.readBytes a bytes.length = some bytes :=
  Silmaril.Proofs.Process.CLI.Cover.DataIn.read h hl pos

end Silmaril.Process.CLI
