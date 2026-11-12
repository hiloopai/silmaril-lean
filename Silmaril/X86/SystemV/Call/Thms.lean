module

public import Silmaril.X86.SystemV.Call.Defs
public import Silmaril.Process.CLI.Loaded.Thms
import Silmaril.Proofs.X86.SystemV.Call

/-!
# A concrete System V call into a pinned image: facts

PROVED (standard axioms); the longer proofs are in `Silmaril/Proofs/X86/SystemV/Call.lean`.

* `Layout.of_check`, and the tactic `sysv_layout`: a `Layout` from one kernel evaluation of
  `Layout.check`;
* `Layout.loaded`: the image is loaded in the call memory;
* `Layout.retOf`, `Layout.abi`: every core with `rsp = F.sp` is a System V entry returning to
  `F.ret`;
* `Layout.stackOk`, `Layout.atCall`: such a core at `entry` meets the leaf call context
  `leafCtx img entry F.size Own` when no argument byte is owned;
* `Layout.unmapped_below`, `Layout.read_null`: every address below the frame is unmapped, and
  a read at address `0` fails;
* `Layout.stack_write_same`: writes inside the stack keep the image loaded;
* `callCore_*`, `Layout.callCore_rsp_toNat`, `Layout.callState_abi`, `Layout.callState_atCall`:
  the same for `callState`.

These give a nonvacuity witness of a leaf function problem: `callState F img entry args` is a
live System V entry in the leaf context, and the argument-specific precondition is the only
part a problem has to supply.
-/

@[expose] public section

namespace Silmaril.X86.SystemV.Call

open Silmaril.X86 (MState State Word Byte Reg)
open Silmaril.Process (Memory Region Access)
open Silmaril.Process.CLI (Image Segment)
open Silmaril.X86.SystemV.CallCtx

variable {F : Frame} {img : Image}

/-- **A `Layout` from one evaluation of `Layout.check`.** -/
theorem Layout.of_check (h : Layout.check F img = true) : Layout F img :=
  Silmaril.Proofs.X86.SystemV.Call.of_check h

/-- **The image is loaded in the call memory.** -/
theorem Layout.loaded (h : Layout F img) : img.Loaded (memory F img) :=
  Silmaril.Proofs.X86.SystemV.Call.loaded h

/-- The return address reads back from `[F.sp]`. -/
theorem Layout.ret_read (h : Layout F img) :
    (memory F img).readBytes F.sp 8 = some (Silmaril.Machine.LittleEndian.encodeWords [F.ret]) :=
  Silmaril.Proofs.X86.SystemV.Call.ret_read h

/-- The return address of a core with `rsp = F.sp` is `F.ret`. -/
theorem Layout.retOf (h : Layout F img) {core : State} (hsp : (core.read .rsp).toNat = F.sp) :
    Silmaril.X86.FnContract.retOf core (memory F img) = F.ret :=
  Silmaril.Proofs.X86.SystemV.Call.retOf h hsp

/-- **A core with `rsp = F.sp` is a System V entry.** -/
theorem Layout.abi (h : Layout F img) {core : State} (hsp : (core.read .rsp).toNat = F.sp) :
    Silmaril.X86.FnContract.AbiEntry core (memory F img) :=
  Silmaril.Proofs.X86.SystemV.Call.abi h hsp

/-- The frame below a core with `rsp = F.sp` is readable, writable and apart from the image. -/
theorem Layout.stackOk (h : Layout F img) {core : State} (hsp : (core.read .rsp).toNat = F.sp) :
    StackOk img F.size ⟨core, memory F img⟩ :=
  Silmaril.Proofs.X86.SystemV.Call.stackOk h hsp

/-- **A call meets the leaf call context** when no byte is an argument byte. -/
theorem Layout.atCall (h : Layout F img) {core : State} {entry : Word}
    {Own : MState → Nat → Prop} (hrip : core.rip = entry) (hsp : (core.read .rsp).toNat = F.sp)
    (noOwn : ∀ a, ¬ Own ⟨core, memory F img⟩ a) :
    AtCall (leafCtx img entry F.size Own) entry ⟨core, memory F img⟩ :=
  ⟨hrip, rfl, h.loaded, h.stackOk hsp, fun a ha => (noOwn a ha).elim⟩

/-- **Every address below the frame is unmapped.** -/
theorem Layout.unmapped_below (h : Layout F img) {a : Nat} (ha : a < F.base) (access : Access) :
    (memory F img).permits access a = false :=
  Silmaril.Proofs.X86.SystemV.Call.unmapped_below h ha access

/-- **A read at address `0` fails.** -/
theorem Layout.read_null (h : Layout F img) {n : Nat} (hn : 0 < n) :
    (memory F img).readBytes 0 n = none :=
  Silmaril.Proofs.X86.SystemV.Call.read_null h hn

/-- **Writes inside the stack keep the image loaded.** -/
theorem Layout.stack_write_same (h : Layout F img) {mem : Memory}
    (hw : Memory.WritesWithin (memory F img) mem F.region.Contains) : img.Loaded mem :=
  Silmaril.Proofs.X86.SystemV.Call.stack_write_same h hw

/-! ## The call core -/

@[simp] theorem callCore_rip (F : Frame) (entry : Word) (args : List Word) :
    (callCore F entry args).rip = entry := rfl

@[simp] theorem callCore_rsp (F : Frame) (entry : Word) (args : List Word) :
    (callCore F entry args).read .rsp = BitVec.ofNat 64 F.sp := rfl

@[simp] theorem callCore_rdi (F : Frame) (entry : Word) (args : List Word) :
    (callCore F entry args).read .rdi = args.getD 0 0 := rfl

@[simp] theorem callCore_rsi (F : Frame) (entry : Word) (args : List Word) :
    (callCore F entry args).read .rsi = args.getD 1 0 := rfl

@[simp] theorem callCore_rdx (F : Frame) (entry : Word) (args : List Word) :
    (callCore F entry args).read .rdx = args.getD 2 0 := rfl

@[simp] theorem callCore_rcx (F : Frame) (entry : Word) (args : List Word) :
    (callCore F entry args).read .rcx = args.getD 3 0 := rfl

@[simp] theorem callCore_r8 (F : Frame) (entry : Word) (args : List Word) :
    (callCore F entry args).read .r8 = args.getD 4 0 := rfl

@[simp] theorem callCore_r9 (F : Frame) (entry : Word) (args : List Word) :
    (callCore F entry args).read .r9 = args.getD 5 0 := rfl

@[simp] theorem callState_core (F : Frame) (img : Image) (entry : Word) (args : List Word) :
    (callState F img entry args).core = callCore F entry args := rfl

@[simp] theorem callState_memory (F : Frame) (img : Image) (entry : Word) (args : List Word) :
    (callState F img entry args).memory = memory F img := rfl

/-- The call core's stack pointer is `F.sp` (no wrap, by the layout). -/
theorem Layout.callCore_rsp_toNat (h : Layout F img) (entry : Word) (args : List Word) :
    ((callCore F entry args).read .rsp).toNat = F.sp :=
  Silmaril.Proofs.X86.SystemV.Call.callCore_rsp_toNat h entry args

/-- **The call state is a System V entry** returning to `F.ret`. -/
theorem Layout.callState_abi (h : Layout F img) (entry : Word) (args : List Word) :
    Silmaril.X86.FnContract.AbiEntry (callState F img entry args).core
      (callState F img entry args).memory :=
  h.abi (h.callCore_rsp_toNat entry args)

/-- **The call state meets the leaf call context** when no byte is an argument byte. -/
theorem Layout.callState_atCall (h : Layout F img) {entry : Word} {args : List Word}
    {Own : MState → Nat → Prop} (noOwn : ∀ a, ¬ Own (callState F img entry args) a) :
    AtCall (leafCtx img entry F.size Own) entry (callState F img entry args) :=
  h.atCall rfl (h.callCore_rsp_toNat entry args) noOwn

/-- `sysv_layout` proves `Layout F img` for concrete `F` and `img` by one kernel evaluation
of `Layout.check`. -/
macro "sysv_layout" : tactic =>
  `(tactic| (set_option maxRecDepth 100000 in exact Layout.of_check (by decide +kernel)))

end Silmaril.X86.SystemV.Call
