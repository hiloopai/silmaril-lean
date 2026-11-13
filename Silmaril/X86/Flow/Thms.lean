module

public import Silmaril.X86.Flow.X64.Defs
import Silmaril.Proofs.X86.Flow.Unique
import Silmaril.Proofs.X86.Flow.X64

/-!
# Flow decoders: uniqueness of the instruction at an address, and the `X64` decoder

* `at_unique`: for a stable decoder, the instruction read from a fetch of `n` bytes at `a` is the
  one read from a fetch of exactly its length (what a machine step reads, `Flow.At`).
* `X64.stable`: `X64.dec` is stable (by construction: it returns the shortest prefix its reader
  consumes entirely).

Open: the flow law of each machine for `X64.dec` (`Task.flowLaw_str9`).
-/

@[expose] public section

namespace Silmaril.X86.Flow

open Silmaril.X86 (Byte)
open Silmaril.Process (Memory)

/-- **The instruction at an address is unique.** -/
theorem at_unique {D : FlowDec} (hD : D.Stable) {m : Memory} {a n l l' : Nat} {s w : List Byte}
    {i i' : D.Instr} (hs : m.fetchBytes a n = some s) (hds : D.decode s = some (i', l'))
    (hw : m.fetchBytes a l = some w) (hdw : D.decode w = some (i, l)) : i = i' ∧ l = l' :=
  Silmaril.Proofs.X86.Flow.at_unique hD hs hds hw hdw

/-- **`X64.dec` reads a prefix.** -/
theorem X64.stable : X64.dec.Stable := Silmaril.Proofs.X86.Flow.X64.stable

/-! ## Spot checks of the decoder -/

example : X64.decode [0x48, 0x89, 0xC7] = some (⟨.seq, .keep⟩, 3) := by decide
example : X64.decode [0x48, 0x89, 0xF8] = some (⟨.seq, .clobber⟩, 3) := by decide
example : X64.decode [0xB8, 0x3C, 0, 0, 0, 0x0F, 0x05] = some (⟨.seq, .set 60⟩, 5) := by decide
example : X64.decode [0x0F, 0x05] = some (⟨.syscall, .clobber⟩, 2) := by decide
example : X64.decode [0xF3, 0x0F, 0x1E, 0xFA] = some (⟨.seq, .keep⟩, 4) := by decide
example : X64.decode [0xFF, 0x25, 0x10, 0, 0, 0] = some (⟨.jmpInd (.ripMem 16), .keep⟩, 6) := by decide
example : X64.decode [0xE8, 0xFB, 0xFF, 0xFF, 0xFF] = some (⟨.call (-5), .keep⟩, 5) := by decide
example : X64.decode [0xC5, 0xFD, 0x74, 0x0F] = some (⟨.seq, .clobber⟩, 4) := by decide
example : X64.decode [0x62, 0xB1, 0x7D, 0x48, 0x74, 0x0F] = some (⟨.seq, .clobber⟩, 6) := by decide

end Silmaril.X86.Flow
