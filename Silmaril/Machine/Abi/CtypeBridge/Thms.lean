module

public import Silmaril.Machine.Abi.CtypeBridge.Defs
import Silmaril.Proofs.Machine.Abi.CtypeBridge
/-! # `Scalar ↔ Ctype`: classification and the convention's descriptor

* `objectOfCtype_toCtype`: the ABI model's `objectOfCtype` classifies the C type of
  every fragment scalar as `Abi.SystemV.Kind.object`, for every tag table (scalars never
  look up tags; their alignments are 4 or 8, so the power-of-two field check
  does not apply to them).
* `toCtype_injective`.
* `forall₂_toCtype`: the per-argument classification relation, in the shape of
  the native correspondence's `Correspondence.Parameters` (without its `Retained` conjunct, which is
  `True` on these non-enum types and lives in the Compiler region).
* `ctypePlan_proto`: the `Ctype`-keyed planner on `Proto.ctypes` is
  `Abi.SystemV.Proto.plan`.
* `proto_plan_eq_callPlan`: `Proto.plan` returns the `callPlan` of the typed
  FFI signature `sigOf` that the convention uses.
* `convention_desc_of_ctypes`: the descriptor of `Abi.SystemV.sysv` (and of
  every `convention` instance) is the `Ctype` planner's output on the Cerberus
  prototype.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.CtypeBridge

open Silmaril.C.Api (Scalar)
open Silmaril.Cerberus (Ctype)
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi (Object Profile CallPlan objectOfCtype)
open Silmaril.Machine.Abi.SystemV (Options intPlan sysv)

/-- The classification of a fragment scalar's C type, for every tag table. -/
theorem objectOfCtype_toCtype (tags : Tags) (k : Scalar) :
    objectOfCtype tags (Scalar.toCtype k) = .ok (Abi.SystemV.Kind.object k) :=
  Silmaril.Proofs.Machine.Abi.CtypeBridge.objectOfCtype_toCtype tags k

theorem toCtype_injective : Function.Injective Scalar.toCtype :=
  Silmaril.Proofs.Machine.Abi.CtypeBridge.toCtype_injective

theorem mapM_toCtype (tags : Tags) (ks : List Scalar) :
    (ks.map Scalar.toCtype).mapM (objectOfCtype tags) = .ok (ks.map Abi.SystemV.Kind.object) :=
  Silmaril.Proofs.Machine.Abi.CtypeBridge.mapM_toCtype tags ks

theorem optionMapM_toCtype (tags : Tags) (r : Option Scalar) :
    (r.map Scalar.toCtype).mapM (objectOfCtype tags) = .ok (r.map Abi.SystemV.Kind.object) :=
  Silmaril.Proofs.Machine.Abi.CtypeBridge.optionMapM_toCtype tags r

/-- Argument-wise: each Cerberus argument type classifies as the object of the
corresponding the ABI model object specification. -/
theorem forall₂_toCtype (tags : Tags) (ks : List Scalar) :
    List.Forall₂ (fun type spec => objectOfCtype tags type =
        .ok (spec : Silmaril.Machine.SystemV.Abi.Ffi.ObjectSpec).object)
      (ks.map Scalar.toCtype) (ks.map Abi.SystemV.Kind.spec) := by
  induction ks with
  | nil => exact .nil
  | cons k ks ih => exact .cons (objectOfCtype_toCtype tags k) ih

/-- The `Ctype` planner on a fragment prototype's Cerberus types is the ABI model's
planner on its objects. -/
theorem ctypePlan_proto (profile : Profile) (tags : Tags) (p : Abi.SystemV.Proto) :
    ctypePlan profile tags (Proto.ctypes p) (Proto.resultCtype p) = p.plan profile :=
  Silmaril.Proofs.Machine.Abi.CtypeBridge.ctypePlan_proto profile tags p

/-- `Proto.plan` is the `callPlan` of the typed FFI signature `sigOf p`. -/
theorem proto_plan_eq_callPlan (profile : Profile) (p : Abi.SystemV.Proto) :
    p.plan profile = .ok (sigOf profile p).callPlan :=
  Abi.SystemV.plan_intPlan profile p

/-- The `Ctype` planner returns the FFI signature's `callPlan`. -/
theorem ctypePlan_eq_callPlan (profile : Profile) (tags : Tags) (p : Abi.SystemV.Proto) :
    ctypePlan profile tags (Proto.ctypes p) (Proto.resultCtype p) =
      .ok (sigOf profile p).callPlan := by
  rw [ctypePlan_proto, proto_plan_eq_callPlan]

theorem sigOf_objects (profile : Profile) (p : Abi.SystemV.Proto) :
    (sigOf profile p).arguments.map (·.object) = p.objects := by
  simp [sigOf, Abi.SystemV.Proto.ffi, Abi.SystemV.Proto.objects, Abi.SystemV.Kind.spec]

theorem sigOf_resultObject (profile : Profile) (p : Abi.SystemV.Proto) :
    (sigOf profile p).result.map (·.object) = p.resultObject := by
  cases h : p.signature.result <;>
    simp [sigOf, Abi.SystemV.Proto.ffi, Abi.SystemV.Proto.resultObject, Abi.SystemV.Kind.spec, h]

/-- Any instance of `Abi.SystemV.convention` describes a prototype by the
`Ctype` planner on its Cerberus types, for every tag table. -/
theorem convention_desc_of_ctypes (options : Options) (planned : Abi.SystemV.Planned options.profile)
    (inhabited : ∀ (p : Abi.SystemV.Proto) (a : Silmaril.C.Api.Arguments p.signature.arguments),
      ∃ s, p.Entry options.profile planned a s) (tags : Tags) (p : Abi.SystemV.Proto) :
    (Abi.SystemV.convention options planned inhabited).desc p =
      ⟨options.tag, ctypePlan options.profile tags (Proto.ctypes p) (Proto.resultCtype p)⟩ := by
  rw [ctypePlan_proto]; rfl

/-- `sysv`'s descriptor is the `Ctype` planner's output, which succeeds with the
FFI signature's `callPlan`. -/
theorem sysv_desc_of_ctypes (options : Options) (tags : Tags) (p : Abi.SystemV.Proto) :
    (sysv options).desc p =
      ⟨options.tag, ctypePlan options.profile tags (Proto.ctypes p) (Proto.resultCtype p)⟩ :=
  convention_desc_of_ctypes options _ _ tags p

/-! ## Per-constructor checks by `decide` (empty tag table) -/

example : (objectOfCtype ∅ (Scalar.toCtype .int32)).toOption = some (Abi.SystemV.Kind.object .int32) := by
  decide
example : (objectOfCtype ∅ (Scalar.toCtype .uint32)).toOption = some (Abi.SystemV.Kind.object .uint32) := by
  decide
example : (objectOfCtype ∅ (Scalar.toCtype .int64)).toOption = some (Abi.SystemV.Kind.object .int64) := by
  decide
example : (objectOfCtype ∅ (Scalar.toCtype .uint64)).toOption = some (Abi.SystemV.Kind.object .uint64) := by
  decide
example : (objectOfCtype ∅ (Scalar.toCtype .pointer)).toOption =
    some (Abi.SystemV.Kind.object .pointer) := by
  decide

/-- `int add(int, int)`: the `Ctype` planner puts the arguments in RDI and RSI
and the result in RAX, as the closed form `intPlan` says. -/
example : (ctypePlan {} ∅ [Scalar.toCtype .int32, Scalar.toCtype .int32]
    (some (Scalar.toCtype .int32))).toOption =
    some (intPlan [Abi.SystemV.Kind.object .int32, Abi.SystemV.Kind.object .int32] (some (Abi.SystemV.Kind.object .int32))) := by
  decide

end Silmaril.Machine.Abi.CtypeBridge
