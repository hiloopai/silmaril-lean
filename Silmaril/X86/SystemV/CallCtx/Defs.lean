module

public import Silmaril.Process.CLI.Loaded.Defs
public import Silmaril.X86.Stencils.ByteLoop.Defs

/-!
# The call context of a function in a pinned image

A function contract over a whole executable leaves its call environment abstract: where the
function is, what the caller has set up, and what the call may write besides its outputs.
`Ctx` packages that environment, and a problem fixes it from the pinned image:

* `Ctx.ok entry m`: the call environment at a call of the unit at `entry`;
* `Ctx.scratch m a`: the bytes the call may write besides its outputs.

`AtCall X entry m`: `m` is at `entry`, in context `X`.

The standard contexts:

* `unitCtx img unit frame`: the entry is `unit` and the image is loaded
  (`Silmaril.Process.CLI.Image.Loaded`); the call may write the `frame` bytes below the entry
  stack pointer (`stackBelow`);
* `leafCtx img unit frame Own`: a leaf function that does not allocate. Besides `unitCtx`,
  the `frame` bytes below `rsp` are readable, writable and outside the image (`StackOk`), and
  no byte the caller passes (`Own m`, the argument regions) is in the stack frame, the
  return-address slot (`retSlot`) or the image (`InImage`): `SepLeaf`.

Writable segments (`.data`, `.bss`) are left unconstrained by `Image.Loaded`: the program may
have changed them before the call.
-/

@[expose] public section

namespace Silmaril.X86.SystemV.CallCtx

open Silmaril.X86 (MState Word)
open Silmaril.Process.CLI (Image)
open Silmaril.X86.Stencils.ByteLoop (Readable Writable Apart)

/-- The call environment of a unit. -/
structure Ctx where
  /-- The call environment at a call of the unit at `entry`. -/
  ok : Word → MState → Prop
  /-- Bytes the call may write besides its outputs. -/
  scratch : MState → Nat → Prop

/-- The stack area of `k` bytes below the entry stack pointer: the usual `Ctx.scratch` of a
leaf function. -/
def stackBelow (k : Nat) (m : MState) (a : Nat) : Prop :=
  (m.core.read .rsp).toNat - k ≤ a ∧ a < (m.core.read .rsp).toNat

/-- The common entry: at `entry`, in context `X`. -/
def AtCall (X : Ctx) (entry : Word) (m : MState) : Prop := m.core.rip = entry ∧ X.ok entry m

/-- The `frame` bytes below `rsp` are readable and writable, and the frame and the
return-address slot are outside every image segment. -/
def StackOk (img : Image) (frame : Nat) (m : MState) : Prop :=
  let sp := (m.core.read .rsp).toNat
  frame ≤ sp ∧ Readable m.memory (sp - frame) frame ∧ Writable m.memory (sp - frame) frame ∧
    ∀ seg ∈ img.segments, Apart (sp - frame) (frame + 8) seg.vaddr seg.memSize

/-- `a` is in some segment of the image (its memory extent). -/
def InImage (img : Image) (a : Nat) : Prop :=
  ∃ seg ∈ img.segments, seg.vaddr ≤ a ∧ a < seg.vaddr + seg.memSize

/-- `a` is in the return-address slot `[rsp, rsp + 8)` of `m`. -/
def retSlot (m : MState) (a : Nat) : Prop :=
  (m.core.read .rsp).toNat ≤ a ∧ a < (m.core.read .rsp).toNat + 8

/-- The argument regions `Own m` are apart from the stack frame, the return-address slot and
the image. -/
def SepLeaf (img : Image) (frame : Nat) (Own : MState → Nat → Prop) (m : MState) : Prop :=
  ∀ a, Own m a → ¬ (stackBelow frame m a ∨ retSlot m a ∨ InImage img a)

/-- **The call context of the unit at `unit` in `img`**: the entry is `unit`, the image is
loaded, and the call may write `frame` bytes below the entry stack pointer. -/
def unitCtx (img : Image) (unit : Word) (frame : Nat) : Ctx where
  ok entry m := entry = unit ∧ img.Loaded m.memory
  scratch := stackBelow frame

/-- **The call context of a non-allocating leaf unit** at `unit` in `img`, with a `frame`-byte
stack frame and argument regions `Own`. -/
def leafCtx (img : Image) (unit : Word) (frame : Nat) (Own : MState → Nat → Prop) : Ctx where
  ok entry m := entry = unit ∧ img.Loaded m.memory ∧ StackOk img frame m ∧
    SepLeaf img frame Own m
  scratch := stackBelow frame

end Silmaril.X86.SystemV.CallCtx
