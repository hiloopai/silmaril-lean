module

public import Silmaril.Raw.X86.Str9FsXN

/-!
# `Str9FsXN`: the conservative extension, the listing laws, the machine

* `step_of_str9fsx`: every `Str9FsX` step is a step, so `extendsStr9FsX :
  Str9FsX.isa.Extends isa` (identity lens on `Sse9.XState`) and, by composition,
  `extendsSse9`, `extendsStr9Fs`, `extendsStr9`, `extendsOpen9`, `extendsOpen`: every run and
  contract of the machines below lifts unchanged.
* Listing laws: `step_of_fetch_narrow`, `step_of_listed_narrow` (a `Narrow9` form),
  `step_of_listed` (`isa`: `Str9FsX`'s integer instructions and the `Narrow9` forms) and
  `step_of_listed_sse`.

The proofs are in `Silmaril.Raw.X86.Str9FsXN` (valid, not yet in Isar style), re-exported
here. The vectors below are kernel-checked; `Str9FsXN/Vectors.lean` compares the machine with
hardware.
-/

@[expose] public section

namespace Silmaril.X86.Str9FsXN

/-- The six encodings of the gzip API binaries that `Str9FsX` rejects and `Narrow9` reads are
listed `Narrow9` forms of their own length: `shr ax, 0xf`, `shr bp, 7`, `shr r12w, 7`,
`shr word [rax+0x1730], 8`, `shr word [rdi+0x1730], 8`, `sbb cl, 0xff`. -/
example : [[0x66, 0xC1, 0xE8, 0x0F], [0x66, 0xC1, 0xED, 0x07], [0x66, 0x41, 0xC1, 0xEC, 0x07],
    [0x66, 0xC1, 0xA8, 0x30, 0x17, 0x00, 0x00, 0x08],
    [0x66, 0xC1, 0xAF, 0x30, 0x17, 0x00, 0x00, 0x08], [0x80, 0xD9, 0xFF]].all
    (fun (e : List Silmaril.X86.Byte) => match decode e with
      | some (.narrow _, n) => n == e.length
      | _ => false) = true := by decide

/-- `Str9FsX` forms stay `Str9FsX`'s: `rep stosd` (`F3 AB`), `shr eax, 7` (`C1 E8 07`, an `Ext`
form), `shr al, 1` (`D0 E8`, an `Ext8` form), `add ax, 1` (`66 83 C0 01`, an `Ext9` form). -/
example : [[0xF3, 0xAB], [0xC1, 0xE8, 0x07], [0xD0, 0xE8], [0x66, 0x83, 0xC0, 0x01]].all
    (fun (e : List Silmaril.X86.Byte) => match decode e with
      | some (.base _, n) => n == e.length
      | _ => false) = true := by decide

end Silmaril.X86.Str9FsXN
