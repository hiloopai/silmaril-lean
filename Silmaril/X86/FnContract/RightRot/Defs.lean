module

public import Silmaril.X86.FnContract.SystemV.Thms
public import Silmaril.X86.Decompile.RightRot.Defs
/-!
# `right_rot` as a generic System V function contract

The `clang -O0` `right_rot` decompilation certificate (`Silmaril.X86.Decompile.RightRot`,
imported under `Silmaril/Raw`) as a `FnContract Open.isa` (`contract`, via `ofDecompiled`), and
the integer C signature, result and domain of its first concrete System V `Realizes`
certificate (`FnContract/RightRot/Thms.lean`).

`Silmaril.Machine.SystemV.Realizes` takes a write footprint that depends on the C arguments only,
not on the call. `right_rot` writes sixteen bytes below its entry stack pointer, so the
`Realizes` statement is a family indexed by that stack pointer `sp0`, which `domain` fixes.
-/

@[expose] public section

namespace Silmaril.X86.FnContract.RightRot

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Decompile.RightRot

/-- The sixteen bytes below the entry stack pointer: the saved `rbp` and eight red-zone
bytes. -/
def footprint (m : MState) (a : Nat) : Prop :=
  (m.core.read .rsp).toNat - 16 ≤ a ∧ a < (m.core.read .rsp).toNat - 16 + 16

/-- The certificate's postcondition gives the ABI return discipline and the footprint. -/
theorem post_abi (e x : Word) (m fin : MState) (_ : Entry e x m)
    (h : Post (rightRotSpec (args m).1 (args m).2) m fin) :
    fin.core.read .rsp = m.core.read .rsp + 8#64 ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, fin.core.read r = m.core.read r) ∧
      m.memory.WritesWithin fin.memory (footprint m) :=
  ⟨h.2.1, h.2.2.1, (Silmaril.Process.Memory.writesOnly_iff_writesWithin _ _ _ _).mp h.2.2.2⟩

/-- **`right_rot` as a generic contract on the open machine.** -/
def contract : FnContract Open.isa :=
  FnContract.ofDecompiled decompiled footprint post_abi

/-- `right_rot(uint32_t value, unsigned int count) → uint32_t`. -/
def signature : Silmaril.C.Api.Signature := ⟨[.uint32, .uint32], some .uint32⟩

/-- The C result. -/
def result : Silmaril.C.Api.Arguments signature.arguments →
    Silmaril.C.Api.ReturnValue signature.result
  | .cons value (.cons count .nil) => rightRotSpec value count.toNat

/-- The count argument. -/
def count : Silmaril.C.Api.Arguments signature.arguments → BitVec 32
  | .cons _ (.cons count .nil) => count

/-- The writes of a call entered with stack pointer `sp0`. -/
def writes (sp0 : Word) (_ : Silmaril.C.Api.Arguments signature.arguments) :
    Silmaril.Machine.SystemV.Footprint :=
  fun a => sp0.toNat - 16 ≤ a ∧ a < sp0.toNat - 16 + 16

/-- The domain beyond the ABI: the code loaded at the entry, the frame mapped, apart from the
code and not wrapping, the entry stack pointer `sp0`, and the C source's `0 < count < 32`. -/
structure Domain (sp0 : Word) (arguments : Silmaril.C.Api.Arguments signature.arguments)
    (call : Silmaril.Machine.SystemV.Call) : Prop where
  image : Silmaril.X86.Decompile.Image code call.entry call.initial.memory
  frameWrite : call.initial.memory.Permitted .write
    ((call.initial.core.read .rsp).toNat - 16) 16
  frameRead : call.initial.memory.Permitted .read
    ((call.initial.core.read .rsp).toNat - 16) 16
  spLow : 16 ≤ (call.initial.core.read .rsp).toNat
  apart : call.entry.toNat + 37 ≤ (call.initial.core.read .rsp).toNat - 16 ∨
    (call.initial.core.read .rsp).toNat ≤ call.entry.toNat
  sp : call.initial.core.read .rsp = sp0
  countPos : 0 < (count arguments).toNat
  countLt : (count arguments).toNat < 32

end Silmaril.X86.FnContract.RightRot
