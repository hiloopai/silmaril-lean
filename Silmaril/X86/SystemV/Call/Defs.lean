module

public import Silmaril.X86.EntryState
public import Silmaril.X86.FnContract.Defs
public import Silmaril.X86.SystemV.CallCtx.Defs

/-!
# A concrete System V call into a pinned image

Refutations and nonvacuity witnesses of a function problem over a pinned executable need an
explicit machine state at a call of the function: the entry address in `rip`, the image loaded
(`Silmaril.Process.CLI.Image.Loaded`), a readable and writable stack frame below `rsp` apart
from the image, and a System V return address at `[rsp]`. This module builds one with
silmaril's `EntryState` builder.

* `Frame`: the stack: `size` zero bytes from `base`, then the return address `ret`, so that the
  entry stack pointer is `Frame.sp = base + size`;
* `placements F img`, `memory F img`: the stack page (read and write) and every segment of
  `img` backed by its contents with its own permissions;
* `callCore F entry args`, `callState F img entry args`: `rip = entry`, `rsp = F.sp`, the
  integer arguments `args` in `rdi, rsi, rdx, rcx, r8, r9` (missing ones zero), every other
  register zero and every flag undefined;
* `Layout F img`: the geometry the facts need: the placements are well formed
  (`EntryState.WF`), every segment is nonempty and lies above the return-address slot, the
  stack pointer is `8 mod 16`, and address `0` is below the frame. `Layout.check` decides it
  (`Layout.of_check`), and the tactic `sysv_layout` proves a `Layout` by one kernel evaluation.

What a `Layout` gives (`Silmaril/X86/SystemV/Call/Thms.lean`): the image is loaded
(`Layout.loaded`), every core whose `rsp` is `F.sp` is a System V entry returning to `F.ret`
(`Layout.abi`, `Layout.retOf`), meets the leaf call context with a `F.size`-byte frame
(`Layout.stackOk`, `Layout.atCall`), finds every address below the frame unmapped
(`Layout.unmapped_below`, `Layout.read_null`), and writes inside the stack keep the image
loaded (`Layout.stack_write_same`).
-/

@[expose] public section

namespace Silmaril.X86.SystemV.Call

open Silmaril.X86 (MState State Word Byte Reg)
open Silmaril.Process (Memory Region addressLimit)
open Silmaril.Process.CLI (Image Segment)
open Silmaril.X86.EntryState (Placement)

/-- The stack of a call: `size` bytes of frame from `base`, then the return address. -/
structure Frame where
  /-- The lowest address of the stack. -/
  base : Nat
  /-- The frame bytes below the entry stack pointer. -/
  size : Nat
  /-- The return address at `[rsp]`. -/
  ret : Word := 0

namespace Frame

/-- The entry stack pointer: the return-address slot, just above the frame. -/
def sp (F : Frame) : Nat := F.base + F.size

/-- The stack's bytes: the zeroed frame, then the return address. -/
def bytes (F : Frame) : List Byte :=
  List.replicate F.size 0 ++ Silmaril.Machine.LittleEndian.encodeWords [F.ret]

/-- The stack region: the frame and the return-address slot, readable and writable. -/
def region (F : Frame) : Region := ⟨F.base, F.size + 8, ⟨true, true, false⟩⟩

/-- The stack placement. -/
def placement (F : Frame) : Placement := ⟨F.region, some F.bytes⟩

end Frame

/-- The placements: the stack, then every segment of the image backed by its contents. -/
def placements (F : Frame) (img : Image) : List Placement :=
  F.placement :: img.segments.map fun s => ⟨s.region, some s.contents⟩

/-- The memory at the call. -/
def memory (F : Frame) (img : Image) : Memory := Silmaril.X86.EntryState.memory (placements F img)

/-- The integer argument registers of System V, in order. -/
def argRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- The core at the call: `rip = entry`, `rsp = F.sp`, the integer arguments `args` in
`argRegs` (missing ones zero), every other register zero and every flag undefined. -/
def callCore (F : Frame) (entry : Word) (args : List Word) : State where
  regs
    | .rsp => BitVec.ofNat 64 F.sp
    | .rdi => args.getD 0 0
    | .rsi => args.getD 1 0
    | .rdx => args.getD 2 0
    | .rcx => args.getD 3 0
    | .r8 => args.getD 4 0
    | .r9 => args.getD 5 0
    | _ => 0
  rip := entry
  flags := Silmaril.X86.EntryState.unknownFlags
  fsBase := 0

/-- **The machine state at a call of `entry`** with the integer arguments `args`. -/
def callState (F : Frame) (img : Image) (entry : Word) (args : List Word) : MState :=
  ⟨callCore F entry args, memory F img⟩

/-- **The geometry of a call**: the placements are well formed, every segment is nonempty and
lies above the return-address slot, the stack pointer is `8 mod 16`, and the frame does not
start at address `0`. -/
structure Layout (F : Frame) (img : Image) : Prop where
  wf : Silmaril.X86.EntryState.WF (placements F img)
  positive : ∀ s ∈ img.segments, 0 < s.memSize
  above : ∀ s ∈ img.segments, F.sp + 8 ≤ s.vaddr
  aligned : F.sp % 16 = 8
  base_pos : 0 < F.base

/-- The decision procedure for `Layout` (`Layout.of_check`). It never forms a segment's zero
fill: a segment's contents span its memory size exactly when its file bytes fit. -/
def Layout.check (F : Frame) (img : Image) : Bool :=
  decide (0 < F.base) && decide (F.sp % 16 = 8) && decide (F.base + (F.size + 8) ≤ addressLimit)
    && img.segments.all (fun s => decide (s.fileBytes.length ≤ s.memSize) && decide (0 < s.memSize)
      && decide (F.sp + 8 ≤ s.vaddr) && decide (s.vaddr + s.memSize ≤ addressLimit))
    && decide ((F.region :: img.segments.map Segment.region).Pairwise Region.Disjoint)

end Silmaril.X86.SystemV.Call
