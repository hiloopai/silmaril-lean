module

public import Silmaril.X86.FnContract.SystemV.Defs
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Open9.Thms
import Silmaril.Proofs.X86.FnContract.SystemV.Adapter
/-!
# Function contracts: the System V and decompilation bridges

Split out of `FnContract.Thms` so that the contract core does not import the
the ABI model System V ABI model and its Cerberus closure. Names are unchanged:

* `total_of_decompiled`, `ofDecompiled`: a `Decompile.Decompiled` certificate as a contract on
  the open machine;
* `toRealizes`: a contract on the open machine is an integer System V
  `Silmaril.Machine.SystemV.Realizes` certificate whose execution relation is an open run;
* `toFfiRealizes`: the same for the typed FFI contract `Silmaril.Machine.SystemV.Abi.Ffi.Realizes`
  of the ABI model, with execution relation `Open.ffiExecute`;
* `toRealizes9`: `toRealizes` on the `Ext9` open machine `Open9.isa` (moved from `Open9.Thms`).

The ABI compatibility obligations (`entry`, `value`, `footprint` of `toRealizes`) are explicit
hypotheses, as in `Silmaril.Machine.Decompile.realizes_of_decompiled`.
-/

@[expose] public section

namespace Silmaril.X86.FnContract

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.X86.SegVC (Isa Call)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

theorem total_of_decompiled {α β : Type} {code : List Byte}
    {Pre : Word → Word → MState → Prop} {args : MState → α} {f : α → β}
    {Post : β → MState → MState → Prop}
    (cert : Silmaril.X86.Decompile.Decompiled code Pre args f Post)
    (footprint : MState → Nat → Prop)
    (abi : ∀ e x m fin, Pre e x m → Post (f (args m)) m fin →
      fin.core.read .rsp = m.core.read .rsp + 8#64 ∧
      (∀ r ∈ sysv64.calleeSaved, fin.core.read r = m.core.read r) ∧
      m.memory.WritesWithin fin.memory (footprint m)) :
    (decompiledSpec Pre args f Post footprint).Total Open.isa :=
  Silmaril.Proofs.X86.FnContract.total_of_decompiled cert footprint abi

/-- **A decompilation certificate as a contract.** The certificate's postcondition must imply
the ABI return discipline and the write footprint (`abi`). -/
def ofDecompiled {α β : Type} {code : List Byte}
    {Pre : Word → Word → MState → Prop} {args : MState → α} {f : α → β}
    {Post : β → MState → MState → Prop}
    (cert : Silmaril.X86.Decompile.Decompiled code Pre args f Post)
    (footprint : MState → Nat → Prop)
    (abi : ∀ e x m fin, Pre e x m → Post (f (args m)) m fin →
      fin.core.read .rsp = m.core.read .rsp + 8#64 ∧
      (∀ r ∈ sysv64.calleeSaved, fin.core.read r = m.core.read r) ∧
      m.memory.WritesWithin fin.memory (footprint m)) :
    FnContract Open.isa :=
  ⟨decompiledSpec Pre args f Post footprint, total_of_decompiled cert footprint abi⟩

/-- **A contract on the open machine is an integer System V `Realizes` certificate.** The
three ABI compatibility obligations are hypotheses. -/
theorem toRealizes (C : FnContract Open.isa) (signature : Silmaril.C.Api.Signature)
    (result : Silmaril.C.Api.Arguments signature.arguments →
      Silmaril.C.Api.ReturnValue signature.result)
    (writes : Silmaril.C.Api.Arguments signature.arguments → Silmaril.Machine.SystemV.Footprint)
    (domain : Silmaril.C.Api.Arguments signature.arguments → Silmaril.Machine.SystemV.Call → Prop)
    (entry : ∀ arguments call, Silmaril.C.Api.SysV.Entry signature arguments call →
      domain arguments call → C.entry call.initial)
    (value : ∀ arguments call final, Silmaril.C.Api.SysV.Entry signature arguments call →
      domain arguments call → C.post call.initial final →
        Silmaril.C.Api.SysV.ResultAt final signature.result (result arguments))
    (footprint : ∀ arguments call a, Silmaril.C.Api.SysV.Entry signature arguments call →
      domain arguments call → C.footprint call.initial a → writes arguments a) :
    Silmaril.Machine.SystemV.Realizes signature result writes domain
      (fun call final => Reaches Open.step call.initial final) :=
  Silmaril.Proofs.X86.FnContract.toRealizes C signature result writes domain entry value
    footprint

open Silmaril.Machine.SystemV.Abi in
/-- **A contract on the open machine is a typed FFI `Realizes` certificate** (`Silmaril.Machine.SystemV.Abi`), with
the extended state carried unchanged (`Open.ffiExecute`). The stack alignment of the call plan
must be a multiple of 16. -/
theorem toFfiRealizes (C : FnContract Open.isa) (signature : Ffi.Signature)
    (result : Ffi.Values signature.arguments → Ffi.ResultValue signature.result)
    (writes : Ffi.Values signature.arguments → Ffi.Footprint)
    (unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop)
    (domain : Ffi.Values signature.arguments → Ffi.Call → Prop)
    (stackAlign : 16 ∣ signature.callPlan.stackAlign)
    (entry : ∀ arguments call, Ffi.Entry signature arguments call (unaliased arguments) →
      domain arguments call → C.entry call.initial.machine)
    (value : ∀ arguments call (final : MState),
      Ffi.Entry signature arguments call (unaliased arguments) → domain arguments call →
      C.post call.initial.machine final →
        Ffi.ResultAt signature call { call.initial with machine := final } (result arguments))
    (footprint : ∀ arguments call a, Ffi.Entry signature arguments call (unaliased arguments) →
      domain arguments call → C.footprint call.initial.machine a → writes arguments a) :
    Ffi.Realizes signature result writes unaliased domain Open.ffiExecute :=
  Silmaril.Proofs.X86.FnContract.toFfiRealizes C signature result writes unaliased domain
    stackAlign entry value footprint

open Silmaril.Machine.Execution (Reaches) in
/-- **A contract on `Open9` is an integer System V `Realizes` certificate** (as
`FnContract.toRealizes`, with `Open9` runs). The three ABI obligations are hypotheses. -/
theorem toRealizes9 (C : FnContract Open9.isa) (signature : Silmaril.C.Api.Signature)
    (result : Silmaril.C.Api.Arguments signature.arguments →
      Silmaril.C.Api.ReturnValue signature.result)
    (writes : Silmaril.C.Api.Arguments signature.arguments → Silmaril.Machine.SystemV.Footprint)
    (domain : Silmaril.C.Api.Arguments signature.arguments → Silmaril.Machine.SystemV.Call → Prop)
    (entry : ∀ arguments call, Silmaril.C.Api.SysV.Entry signature arguments call →
      domain arguments call → C.entry call.initial)
    (value : ∀ arguments call final, Silmaril.C.Api.SysV.Entry signature arguments call →
      domain arguments call → C.post call.initial final →
        Silmaril.C.Api.SysV.ResultAt final signature.result (result arguments))
    (footprint : ∀ arguments call a, Silmaril.C.Api.SysV.Entry signature arguments call →
      domain arguments call → C.footprint call.initial a → writes arguments a) :
    Silmaril.Machine.SystemV.Realizes signature result writes domain
      (fun call final => Reaches Open9.step call.initial final) := by
  intro arguments call admitted inDomain
  have hret := retOf_of_readBytes admitted.returnAddress
  obtain ⟨t, hr, res⟩ := C.total call.initial trivial
    ⟨admitted.alignment, by rw [hret]; exact admitted.returnAddress⟩
    (entry arguments call admitted inDomain)
  refine ⟨t, hr, ⟨⟨?_, res.abi.stack, res.abi.calleeSaved⟩, ?_, ?_⟩⟩
  · have := res.abi.pc
    simp only at this
    rw [this, hret]
  · exact value arguments call t admitted inDomain res.post
  · exact res.frame.mono (fun a ha => footprint arguments call a admitted inDomain ha)

end Silmaril.X86.FnContract
