module

public import Silmaril.Machine.Abi.LibMini.Defs
public import Silmaril.Machine.Abi.OpenMachine.Thms
public import Silmaril.Machine.Abi.CallFootprint.Thms
public import Silmaril.X86.Ladder.LibMini.Thms
/-!
# libmini against the System V comorphism: proofs

* `strlen_sysv_sat`, `memcpy_sysv_sat`: track A's strict (first-return) stencil contracts
  `strlen_strict`, `memcpy_strict` give the institution sentences
  `Contracts.Sat callModel (within ((sysv o).translate p c) room)` through the generic
  `OpenMachine.sat_of_strict`;
* `strlen_ffiRealizes`, `strlen_ffiRealizesCall`: `strlen` as the ABI model's typed certificate,
  per length and as one call-dependent `FfiRealizesCall` with result `cstrLen`;
* `memcpy_ffiRealizesCall`: `memcpy` as a typed `FfiRealizesCall` with the call-dependent
  footprint `[rdi, rdi + rdx)` (through `CallFootprint.toFfiRealizesCall`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.LibMini

open Silmaril.X86 (MState Word)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Stencils.ByteLoop
open Silmaril.X86.Ladder.LibMini
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options)
open Silmaril.Machine.Abi.OpenMachine
open Silmaril.Machine.Abi.LibMini

/-- `strlen`'s stencil contract as a total WP3 contract on the open machine. -/
def strlenFn (entry : Word) : FnContract Open.isa := ⟨scanContract strlenCode entry, strlen_total entry⟩

/-- `memcpy`'s stencil contract as a total WP3 contract on the open machine. -/
def memcpyFn (entry : Word) : FnContract Open.isa := ⟨copyContract memcpyCode entry, memcpy_total entry⟩

theorem strlen_sysv_sat (o : Options) (entry : Word) (k : Nat) :
    Contracts.Sat callModel
      (within ((sysv o).translate strlenProto (strlenC k)) (StrlenRoom entry k)) := by
  refine sat_of_strict (strlen_strict entry) (fun _ _ _ _ roomy => ⟨roomy.1, roomy.2.1⟩) ?_
  intro a s t _ _ roomy hpost
  have hrax : t.core.read .rax = BitVec.ofNat 64 k := hpost.1 k roomy.2.2
  refine ⟨⟨BitVec.ofNat 64 k, (resultAt_word64 _ .uint64 (.inl rfl) _ _ _ _).2 hrax⟩,
    fun r at_ => ?_⟩
  have := (resultAt_word64 _ .uint64 (.inl rfl) _ _ _ _).1 at_
  exact congrArg some (this.symm.trans hrax)

theorem memcpy_args {o : Options} {d src n : BitVec 64} {s : Ffi.State}
    (entry : (sysv o).Entry memcpyProto (.cons d (.cons src (.cons n .nil))) s) :
    s.machine.core.read .rdi = d := by
  obtain ⟨exit, e⟩ := entry
  obtain ⟨⟨-, b0, e0, c0⟩, -⟩ := e.argumentsAt
  subst e0
  exact (chunk64_iff _ .rdi _).1 c0

theorem memcpy_sysv_sat (o : Options) (entry : Word) :
    Contracts.Sat callModel
      (within ((sysv o).translate memcpyProto memcpyC) (MemcpyRoom entry)) := by
  refine sat_of_strict (memcpy_strict entry) (fun _ _ _ _ roomy => roomy) ?_
  intro a s t e _ _ hpost
  match a, e with
  | .cons d (.cons src (.cons n .nil)), e =>
    have hrax : t.core.read .rax = d := hpost.1.trans (memcpy_args e)
    refine ⟨⟨d, (resultAt_word64 _ .pointer (.inr (.inr rfl)) _ _ _ _).2 hrax⟩,
      fun r at_ => ?_⟩
    have := (resultAt_word64 _ .pointer (.inr (.inr rfl)) _ _ _ _).1 at_
    exact congrArg some (this.symm.trans hrax)

theorem strlen_ffiRealizes (profile : Profile) (entry : Word) (k : Nat) :
    Ffi.Realizes (strlenProto.ffi profile (SystemV.plan_intPlan profile))
      (fun _ => BitVec.ofNat 64 k) (fun _ _ => False) (fun _ _ _ => True)
      (strlenDomain entry k) Open.ffiExecute := by
  refine FnContract.toFfiRealizes (strlenFn entry) _ _ _ _ _ (Nat.dvd_refl 16) ?_ ?_ ?_
  · intro _ call e d
    exact ⟨e.pc.trans d.2.1, d.1, k, d.2.2⟩
  · intro v call final _ d hpost
    exact ⟨_, rfl, (chunk64_iff _ .rax _).2 (hpost.1 k d.2.2)⟩
  · intro _ _ _ _ _ h
    exact h

theorem strlen_ffiRealizesCall (profile : Profile) (entry : Word) :
    CallFootprint.FfiRealizesCall (strlenProto.ffi profile (SystemV.plan_intPlan profile))
      (fun _ call => BitVec.ofNat 64
        (CallFootprint.cstrLen call.initial.machine.memory (arg0 call.initial.machine)))
      (fun _ _ _ => False) (fun _ _ _ => True)
      (fun a call => strlenDomain entry
        (CallFootprint.cstrLen call.initial.machine.memory (arg0 call.initial.machine)) a call)
      Open.ffiExecute :=
  CallFootprint.FfiRealizesCall.of_family
    (signature := strlenProto.ffi profile (SystemV.plan_intPlan profile))
    (result := fun k _ => (BitVec.ofNat 64 k : BitVec 64))
    (writes := fun _ _ _ => False) (domain := fun k => strlenDomain entry k)
    (fun _ call => CallFootprint.cstrLen call.initial.machine.memory (arg0 call.initial.machine))
    (strlen_ffiRealizes profile entry)

theorem memcpy_ffi_args {profile : Profile} {planned : SystemV.Planned profile}
    {v : Ffi.Values (memcpyProto.ffi profile planned).arguments} {call : Ffi.Call}
    {u : Nat → Nat → Prop} (e : Ffi.Entry (memcpyProto.ffi profile planned) v call u) :
    call.initial.machine.core.read .rdi = v.1 := by
  obtain ⟨⟨-, b0, e0, c0⟩, -⟩ := e.argumentsAt
  subst e0
  exact (chunk64_iff _ .rdi _).1 c0

theorem memcpy_ffiRealizesCall (profile : Profile) (entry : Word) :
    CallFootprint.FfiRealizesCall (memcpyProto.ffi profile (SystemV.plan_intPlan profile))
      (fun v _ => v.1)
      (fun _ call a => arg0 call.initial.machine ≤ a ∧
        a < arg0 call.initial.machine + arg2 call.initial.machine)
      (fun _ _ _ => True) (memcpyDomain entry) Open.ffiExecute := by
  refine CallFootprint.toFfiRealizesCall (memcpyFn entry)
    (memcpyProto.ffi profile (SystemV.plan_intPlan profile)) (fun v => v.1) _ _
    (Nat.dvd_refl 16) (fun _ _ _ d => d.2) ?_
  intro v call final e _ hpost
  exact ⟨_, rfl, (chunk64_iff _ .rax _).2 (hpost.1.trans (memcpy_ffi_args e))⟩

end Silmaril.Proofs.Machine.Abi.LibMini
