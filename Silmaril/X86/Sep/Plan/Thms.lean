module

public import Silmaril.X86.Sep.Plan.Defs
public import Silmaril.X86.Sep.BI.Thms
import Silmaril.Proofs.X86.Sep.Plan
/-!
# Placement assertions: agreement with the ABI model

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/Machine/X86/Sep/Plan.lean`).

**Against `Ffi`.** On the projection `ffiXState s` of an `Ffi.State` (integer machine, low
128 bits of vector registers 0-15) and with `Ffi` bytes read as `Sep` bytes (`toSepBytes`):
* `chunksPt_iff_chunksAt`: `XHolds (chunksPt bs cs)` iff every chunk is `modelled` and
  `Ffi.ChunksAt s bs cs`; `chunkPt_iff_chunksAt` for one chunk;
* `argPt_reg`, `argPt_reg_iff`: a register argument is its chunks;
* `argPt_stack`: a stack argument is `↑ₓ(bytesPt (sp + 8 + off) bytes)`, and
  `argPt_stack_storedAt`: it gives `Ffi.StoredAt` at `rsp + 8 + off` (the address
  `Ffi.ArgumentAt` reads), for non-empty objects.

**BI.** `xsep_eq_bi_sep`, `xemp_eq_bi_emp`: `xsep`/`xemp` are K3's generic `BI.sep`/`BI.emp`
at the product separation algebra `XFrag = Frag × XMap`, so `xsprop_laws : Laws (ops XFrag)`.

**Examples** (in the proof module, namespace `Silmaril.Proofs.X86.Sep.Plan.Examples`):
`plan_pair`, `plan_big`, `plan_mix`, `plan_vec2`, `plan_fmt7` are `Abi.plan` results decided by
`decide`, and `pair_argsPt`, `big_argsPt`, `mix_argsPt`, `vec2_argsPt`, `fmt7_argsPt` unfold the
placement assertions of those plans.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Plan

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Xmm
open Silmaril.Machine.SystemV.Abi (Chunk Argument)
open Silmaril.Machine.SystemV.Abi.Ffi (ChunksAt StoredAt)

theorem toSepBytes_bytesOfNat {w : Nat} (v : BitVec w) (off n : Nat) :
    toSepBytes (Silmaril.Machine.SystemV.Abi.Ffi.bytesOfNat v.toNat off n) = byteSlice v off n :=
  Silmaril.Proofs.X86.Sep.Plan.toSepBytes_bytesOfNat v off n

theorem byteSlice_setWidth {w m : Nat} (v : BitVec w) {off n : Nat} (h : 8 * (off + n) ≤ m) :
    byteSlice (v.setWidth m) off n = byteSlice v off n :=
  Silmaril.Proofs.X86.Sep.Plan.byteSlice_setWidth v h

theorem toSepBytes_inj {a b : Silmaril.Cerberus.NativeTypes.Bytes} :
    toSepBytes a = toSepBytes b ↔ a = b :=
  Silmaril.Proofs.X86.Sep.Plan.toSepBytes_inj

/-- **Register chunks agree with `Ffi.ChunksAt`** on the `Ffi.State` projection. -/
theorem chunksPt_iff_chunksAt (s : Silmaril.Machine.SystemV.Abi.Ffi.State)
    (bs : Silmaril.Cerberus.NativeTypes.Bytes) (cs : List Chunk) :
    XHolds (chunksPt (toSepBytes bs) cs) (ffiXState s) ↔
      (∀ c ∈ cs, modelled c = true) ∧ ChunksAt s bs cs :=
  Silmaril.Proofs.X86.Sep.Plan.chunksPt_iff_chunksAt s bs cs

/-- One chunk. -/
theorem chunkPt_iff_chunksAt (s : Silmaril.Machine.SystemV.Abi.Ffi.State)
    (bs : Silmaril.Cerberus.NativeTypes.Bytes) (c : Chunk) :
    XHolds (chunkPt (toSepBytes bs) c) (ffiXState s) ↔ modelled c = true ∧ ChunksAt s bs [c] :=
  Silmaril.Proofs.X86.Sep.Plan.chunkPt_iff_chunksAt s bs c

/-- A stack argument is its object bytes at `[sp + 8 + stackOffset]`. -/
theorem argPt_stack {fr : Frame} {a : Argument} {off : Nat} (h : a.stackOffset = some off)
    (bytes : List Byte) :
    argPt fr a bytes = ↑ₓ(bytesPt (fr.sp.toNat + 8 + off) bytes) :=
  Silmaril.Proofs.X86.Sep.Plan.argPt_stack h bytes

/-- A register argument is its chunks. -/
theorem argPt_reg {fr : Frame} {a : Argument} (h : a.stackOffset = none) (bytes : List Byte) :
    argPt fr a bytes = chunksPt bytes a.chunks :=
  Silmaril.Proofs.X86.Sep.Plan.argPt_reg h bytes

theorem argPt_reg_iff (s : Silmaril.Machine.SystemV.Abi.Ffi.State) (fr : Frame) {a : Argument}
    (h : a.stackOffset = none) (bs : Silmaril.Cerberus.NativeTypes.Bytes) :
    XHolds (argPt fr a (toSepBytes bs)) (ffiXState s) ↔
      (∀ c ∈ a.chunks, modelled c = true) ∧ ChunksAt s bs a.chunks :=
  Silmaril.Proofs.X86.Sep.Plan.argPt_reg_iff s fr h bs

/-- A stack argument is `Ffi.StoredAt` where `Ffi.ArgumentAt` reads it. -/
theorem argPt_stack_storedAt (s : Silmaril.Machine.SystemV.Abi.Ffi.State) {fr : Frame}
    {a : Argument} {off : Nat} (h : a.stackOffset = some off)
    (hsp : fr.sp = s.machine.core.read .rsp) {bs : Silmaril.Cerberus.NativeTypes.Bytes}
    (hne : bs ≠ []) (hh : XHolds (argPt fr a (toSepBytes bs)) (ffiXState s)) :
    StoredAt s ((s.machine.core.read .rsp).toNat + 8 + off) bs :=
  Silmaril.Proofs.X86.Sep.Plan.argPt_stack_storedAt s h hsp hne hh

/-- `xsep` is K3's generic separating conjunction at `XFrag`. -/
theorem xsep_eq_bi_sep : xsep = Silmaril.X86.Sep.BI.sep (α := XFrag) :=
  Silmaril.Proofs.X86.Sep.Plan.xsep_eq_bi_sep

theorem xemp_eq_bi_emp : xemp = Silmaril.X86.Sep.BI.emp (α := XFrag) :=
  Silmaril.Proofs.X86.Sep.Plan.xemp_eq_bi_emp

/-- `XSProp` (as predicates over the product algebra `XFrag`) satisfies the BI laws. -/
theorem xsprop_laws : Silmaril.X86.Sep.BI.Laws (Silmaril.X86.Sep.BI.ops XFrag) :=
  Silmaril.X86.Sep.BI.laws

end Silmaril.X86.Sep.Plan
