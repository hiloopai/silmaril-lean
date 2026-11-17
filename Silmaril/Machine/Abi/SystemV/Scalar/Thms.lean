module

public import Silmaril.Machine.Abi.SystemV.Scalar.Defs
public import Silmaril.Machine.Abi.Thms
import Silmaril.Proofs.Machine.Abi.SystemV.Scalar.Plan
import Silmaril.Proofs.Machine.Abi.SystemV.Scalar.Entry
import Silmaril.Proofs.Machine.Abi.SystemV.Scalar.Result

/-!
# The System V comorphism on the scalar fragment

* `plan_scalarPlan`: the ABI model's planner returns the closed form `scalarPlan` on every
  fragment prototype under every vector profile: INTEGER arguments in RDI…R9 and SSE
  arguments in XMM0–XMM7, counted separately, the rest in 8-byte stack slots in argument
  order; an INTEGER result in RAX, an SSE result in XMM0;
* `entry_inhabited`: every argument tuple has an `Ffi.Entry` state;
* `sysv`: the convention, and `sysv_sat` its satisfaction condition;
* `resultAt_some`, `resultAt_none`: a result is the object representation of the value in
  the low bytes of RAX or XMM0 (`Ffi.locationBytes`); a `void` function returns nothing.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.SystemV.Scalar

open Silmaril.Machine.SystemV.Abi
open Silmaril.Logic.Institution.Bridges

/-- The ABI model's planner on the fragment, for every profile. -/
theorem plan_scalarPlan (profile : Profile) : Planned profile :=
  Silmaril.Proofs.Machine.Abi.SystemV.Scalar.plan_scalarPlan profile

/-- Every C argument tuple of the fragment is placed by some machine entry state. -/
theorem entry_inhabited (profile : Profile) (p : Proto) (a : vocab.Args p) :
    ∃ s, p.Entry profile (plan_scalarPlan profile) a s :=
  Silmaril.Proofs.Machine.Abi.SystemV.Scalar.entry_inhabited profile _ p a

/-- The System V AMD64 convention on the scalar fragment. -/
def sysv (options : Options := {}) : Convention vocab Ffi.State CallSite :=
  convention options (plan_scalarPlan options.profile) (entry_inhabited options.profile)

/-- The descriptor of a prototype is the ABI model's successful plan. -/
theorem sysv_desc (options : Options) (p : Proto) :
    (sysv options).desc p = ⟨options.tag, .ok (scalarPlan p.args p.result)⟩ := by
  simp only [sysv, convention, plan_scalarPlan options.profile p]

/-- The satisfaction condition of the scalar System V comorphism. -/
theorem sysv_sat (options : Options) (p : Proto) (model : Contracts.Model Ffi.State Ffi.State)
    (c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))) :
    Contracts.Sat model ((sysv options).translate p c) ↔
      Contracts.Sat ((sysv options).reduce p model) c :=
  (sysv options).sat_translate p model c

/-- A scalar result: the value's bytes in the low bytes of RAX (INTEGER) or XMM0 (SSE). -/
theorem resultAt_some (options : Options) (args : List Kind) (k : Kind)
    (h : args.length ≤ maxArity) (s s' : Ffi.State) (r : k.Value) :
    (sysv options).ResultAt ⟨args, some k, h⟩ s s' r ↔
      Ffi.locationBytes s' (if k.sse then .vector 0 0 else .gp .rax) k.bytes =
        some (k.encode r) :=
  Silmaril.Proofs.Machine.Abi.SystemV.Scalar.resultAt_some options.profile
    (plan_scalarPlan _) args k h s s' r

theorem resultAt_none (options : Options) (args : List Kind) (h : args.length ≤ maxArity)
    (s s' : Ffi.State) (r : PUnit) : (sysv options).ResultAt ⟨args, none, h⟩ s s' r :=
  Silmaril.Proofs.Machine.Abi.SystemV.Scalar.resultAt_none options.profile
    (plan_scalarPlan _) args h s s' r

end Silmaril.Machine.Abi.SystemV.Scalar
