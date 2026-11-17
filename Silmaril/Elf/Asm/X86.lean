module

public import Silmaril.Elf.Asm.Defs
public import Silmaril.X86.Ext.Encoding
public import Silmaril.X86.Open.Defs
public import Silmaril.X86.Open9.Defs

/-! # x86-64 instruction models for `Silmaril.Elf.Asm`

Three existing decoders of this repository, as `Isa`s for `EM_X86_64`. None is new and none
is complete for x86-64: each decodes the instructions its machine model executes, and returns
`none` on anything else, which `decodes` reports as `false` (never as a guess).

| model | decoder | used by |
|---|---|---|
| `x86Ext` | `Silmaril.X86.Ext.decode` (the base forms, canonical encodings only) | `Silmaril.Elf.Staged.x86Ok` (`elf.tiles.x86`) |
| `x86Open` | `Silmaril.X86.Open.decode` (`Ext8`: the base forms and the `Ext8` forms) | the `Open` machine's listings |
| `x86Open9` | `Silmaril.X86.Open9.decode` (`Open` first, then the `Ext9` forms) | the `Open9` machine's listings |

Each knows the targets of the base forms' `jmp`, `jcc` and `call` (8- and 32-bit displacements);
the extension forms have no direct targets. A decoder is not a machine semantics: that a model
decodes a function says nothing about what it computes, and a contract proved on a machine says
nothing about these decoders (the machines fetch through their own decoders, which these are
taken from, but no theorem here relates fetching to `decodes`). Renderings are `Repr` output (`shortRepr`).
-/

@[expose] public section

namespace Silmaril.Elf.Asm

open Silmaril.X86.Ext (Instr)

/-- The target of a relative branch: `pc + len + rel` (sign-extended), when nonnegative. -/
def relTarget (pc len : Nat) (rel : Int) : Option Nat :=
  let t := (pc : Int) + len + rel
  if 0 ≤ t then some t.toNat else none

/-- `Repr` output on one line, without the `Silmaril.X86.` prefixes. -/
def shortRepr {α : Type} [Repr α] (a : α) : String :=
  (((((repr a).pretty 1000).replace "Silmaril.X86.Ext9.Instr." "").replace "Silmaril.X86.Ext8.Instr." "").replace
    "Silmaril.X86.Ext.Instr." "").replace "Silmaril.X86." ""

/-- Direct branch and call targets of `Silmaril.X86.Ext` instructions. -/
def extTarget : Instr → Nat → Nat → Option Nat
  | .jmp rel, pc, n => relTarget pc n rel.toInt
  | .jmp8 rel, pc, n => relTarget pc n rel.toInt
  | .jcc _ rel, pc, n => relTarget pc n rel.toInt
  | .jcc8 _ rel, pc, n => relTarget pc n rel.toInt
  | .call rel, pc, n => relTarget pc n rel.toInt
  | _, _, _ => none

/-- **`Silmaril.X86.Ext.decode`**: the base forms. -/
def x86Ext : Isa where
  name := "x86-64/Silmaril.X86.Ext.decode"
  machine := EM_X86_64
  Instr := Instr
  decEq := inferInstance
  decode := Silmaril.X86.Ext.decode
  target := extTarget
  render i := shortRepr i

/-- **`Silmaril.X86.Open.decode`**, the listing decoder of the `Open` machine. -/
def x86Open : Isa where
  name := "x86-64/Silmaril.X86.Open.decode"
  machine := EM_X86_64
  Instr := Silmaril.X86.Ext8.Instr
  decEq := inferInstance
  decode := Silmaril.X86.Open.decode
  target
    | .base i, pc, n => extTarget i pc n
    | .new _, _, _ => none
  render i := shortRepr i

/-- **`Silmaril.X86.Open9.decode`**, the listing decoder of the `Open9` machine. -/
def x86Open9 : Isa where
  name := "x86-64/Silmaril.X86.Open9.decode"
  machine := EM_X86_64
  Instr := Silmaril.X86.Ext9.Instr
  decEq := inferInstance
  decode := Silmaril.X86.Open9.decode
  target
    | .ext8 (.base i), pc, n => extTarget i pc n
    | _, _, _ => none
  render i := shortRepr i

end Silmaril.Elf.Asm
