module

public import Silmaril.X86.FnContract.SystemV.Defs
public import Silmaril.Proofs.X86.FnContract.Open
/-!
# Function contracts as System V `Realizes` certificates

Proofs behind `FnContract.toRealizes` (the integer `Silmaril.Machine.SystemV.Realizes`) and
`FnContract.toFfiRealizes` (the typed `Silmaril.Machine.SystemV.Abi.Ffi.Realizes` of the ABI model),
both on the open machine, and `total_of_decompiled` (a `Decompile.Decompiled` certificate as
a total spec).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.FnContract

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86
open Silmaril.X86.FnContract

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
      (fun call final => Reaches Open.step call.initial final) := by
  intro arguments call admitted inDomain
  have hret := retOf_of_readBytes admitted.returnAddress
  obtain ⟨t, hr, res⟩ := C.total call.initial trivial
    (abiEntry_of admitted.alignment admitted.returnAddress) (entry arguments call admitted inDomain)
  refine ⟨t, hr, ⟨⟨?_, res.abi.stack, res.abi.calleeSaved⟩, ?_, ?_⟩⟩
  · have := res.abi.pc
    simp only at this
    rw [this, hret]
  · exact value arguments call t admitted inDomain res.post
  · exact res.frame.mono (fun a ha => footprint arguments call a admitted inDomain ha)

open Silmaril.Machine.SystemV.Abi in
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
    Ffi.Realizes signature result writes unaliased domain Open.ffiExecute := by
  intro arguments call admitted inDomain
  have hret := retOf_of_readBytes admitted.returnAddress
  have aligned : (call.initial.machine.core.read .rsp).toNat % 16 = 8 := by
    have h0 := Nat.dvd_of_mod_eq_zero admitted.alignment
    have h16 := Nat.dvd_trans stackAlign h0
    omega
  obtain ⟨t, hr, res⟩ := C.total call.initial.machine trivial
    (abiEntry_of aligned admitted.returnAddress) (entry arguments call admitted inDomain)
  refine ⟨{ call.initial with machine := t }, ⟨hr, rfl⟩, ⟨?_, ?_, ?_⟩⟩
  · refine ⟨?_, res.abi.stack, res.abi.calleeSaved, admitted.direction, admitted.x87Mode,
      rfl, rfl, rfl⟩
    have := res.abi.pc
    simp only at this
    simp only
    rw [this, hret]
  · exact value arguments call t admitted inDomain res.post
  · exact res.frame.mono (fun a ha => footprint arguments call a admitted inDomain ha)

theorem total_of_decompiled {α β : Type} {code : List Byte}
    {Pre : Word → Word → MState → Prop} {args : MState → α} {f : α → β}
    {Post : β → MState → MState → Prop} (cert : Silmaril.X86.Decompile.Decompiled code Pre args f Post)
    (footprint : MState → Nat → Prop)
    (abi : ∀ e x m fin, Pre e x m → Post (f (args m)) m fin →
      fin.core.read .rsp = m.core.read .rsp + 8#64 ∧
      (∀ r ∈ sysv64.calleeSaved, fin.core.read r = m.core.read r) ∧
      m.memory.WritesWithin fin.memory (footprint m)) :
    (decompiledSpec Pre args f Post footprint).Total Open.isa :=
  total_of_ext_returns _ fun m _ ⟨e, he⟩ => by
    obtain ⟨fin, hret, hpost⟩ := cert.cert e _ m he
    obtain ⟨h1, h2, h3⟩ := abi e _ m fin he hpost
    exact ⟨fin, hret, h1, h2, h3, hpost⟩

end Silmaril.Proofs.X86.FnContract
