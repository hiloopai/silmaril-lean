module

public import Silmaril.Machine.Abi.Thms
public import Silmaril.Machine.Abi.SystemV.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Thms
import Silmaril.Proofs.Machine.Abi.SystemV.Basic
import Silmaril.Proofs.Machine.Abi.SystemV.Entry
/-! # The System V comorphism on the INTEGER/pointer fragment

* `plan_intPlan`: the ABI model's planner returns the closed-form `intPlan` on every
  fragment prototype under every vector profile (registers RDI…R9, then 8-byte
  stack slots; result in RAX; 16-byte stack alignment).
* `entry_inhabited`: every argument tuple has an `Ffi.Entry` state.
* `sysv`: the convention, and `sysv.coHom` its institution comorphism.
* `sysv_sat`: the satisfaction condition, i.e. System V correctness of a machine
  call relation is C-level correctness of its read-back.
* `sysv_agree`: profiles (SSE/AVX/AVX-512, red zone) agree on this fragment, so
  cross-profile calls need no thunk (`Convention.Agree.direct_correct`). For the
  red zone this holds only because value-level sentences carry no frame or
  footprint conjunct; it is not evidence that red-zone and no-red-zone code may
  be linked.
* `resultAt_lowBits`: the result read-back ignores RAX bits above the object
  width (the ABI model's `locationBytes_gp_eq_of_lowBits`).
-/

@[expose] public section
namespace Silmaril.Machine.Abi.SystemV

open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Logic.Institution.Bridges

/-- the ABI model's planner on the fragment, for every profile. -/
theorem plan_intPlan (profile : Profile) : Planned profile :=
  Silmaril.Proofs.Machine.Abi.SystemV.plan_intPlan profile

/-- Every C argument tuple of the fragment is placed by some machine entry state. -/
theorem entry_inhabited (profile : Profile) (p : Proto) (a : Arguments p.signature.arguments) :
    ∃ s, p.Entry profile (plan_intPlan profile) a s :=
  Silmaril.Proofs.Machine.Abi.SystemV.entry_inhabited profile _ p a

/-- The System V AMD64 convention on the INTEGER/pointer fragment. -/
def sysv (options : Options := {}) : Convention vocab Ffi.State CallSite :=
  convention options (plan_intPlan options.profile) (entry_inhabited options.profile)

/-- The System V institution comorphism from C interfaces to machine interfaces. -/
abbrev sysvCoHom (options : Options := {}) :=
  (sysv options).coHom

/-- The descriptor of a prototype is the ABI model's successful plan. -/
theorem sysv_desc (options : Options) (p : Proto) :
    (sysv options).desc p = ⟨options.tag, .ok (intPlan p.objects p.resultObject)⟩ := by
  simp only [sysv, convention, plan_intPlan options.profile p]

/-- The satisfaction condition of the System V comorphism. -/
theorem sysv_sat (options : Options) (p : Proto) (model : Contracts.Model Ffi.State Ffi.State)
    (c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))) :
    Contracts.Sat model ((sysv options).translate p c) ↔
      Contracts.Sat ((sysv options).reduce p model) c :=
  (sysv options).sat_translate p model c

/-- Argument placement does not depend on the vector profile. -/
theorem entry_profile (first second : Profile) (p : Proto) (a : Arguments p.signature.arguments)
    (s : Ffi.State) :
    p.Entry first (plan_intPlan first) a s → p.Entry second (plan_intPlan second) a s :=
  fun ⟨exit, h⟩ => ⟨exit, ⟨h.pc, h.argumentsAt, h.alignment, h.stackNoWrap, h.returnAddress,
    h.sret, h.direction, h.x87Mode, h.variadicAL⟩⟩

/-- On this fragment every System V profile places and observes identically.
The red-zone flag agrees trivially: it has no semantic effect until sentences
carry footprints. -/
theorem sysv_agree (first second : Options) (p : Proto) :
    (sysv first).Agree (sysv second) p :=
  ⟨fun a s => ⟨entry_profile _ _ p a s, entry_profile _ _ p a s⟩, fun _ _ _ => Iff.rfl⟩

/-- A callee verified under one profile meets every other profile's contract. -/
theorem sysv_cross_profile {first second : Options} {p : Proto}
    {model : Contracts.Model Ffi.State Ffi.State}
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))}
    (callee : Contracts.Sat model ((sysv second).translate p c)) :
    Contracts.Sat model ((sysv first).translate p c) :=
  ((sysv_agree first second p).sat_iff model c).2 callee

/-- The result read-back depends only on the low object-width bits of RAX. -/
theorem resultAt_lowBits (options : Options) (p : Proto) (k : Scalar)
    (hk : p.signature.result = some k) (s first second : Ffi.State) (r : vocab.Ret p)
    (low : (first.machine.core.read .rax).setWidth (8 * (Kind.object k).size) =
      (second.machine.core.read .rax).setWidth (8 * (Kind.object k).size)) :
    (sysv options).ResultAt p s first r ↔ (sysv options).ResultAt p s second r := by
  obtain ⟨⟨args, res⟩, arity⟩ := p
  cases hk
  have same := Ffi.locationBytes_gp_eq_of_lowBits first second .rax
    (Kind.object k).size low
  show (∃ bytes, (Kind.spec k).representation.encodes r bytes ∧
      Ffi.ChunksAt first bytes [⟨0, (Kind.object k).size, .gp .rax⟩]) ↔
    (∃ bytes, (Kind.spec k).representation.encodes r bytes ∧
      Ffi.ChunksAt second bytes [⟨0, (Kind.object k).size, .gp .rax⟩])
  simp only [Ffi.ChunksAt, List.mem_singleton, forall_eq, same]

end Silmaril.Machine.Abi.SystemV
