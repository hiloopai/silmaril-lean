module

public import Silmaril.Machine.Abi.CtypeBridge.Defs
/-!
# Scalar ↔ Ctype: classification and planning proofs

Proofs for `Silmaril.Machine.Abi.CtypeBridge.Thms`; nothing else imports this
module.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.CtypeBridge

open Silmaril.C.Api (Scalar)
open Silmaril.Cerberus (Ctype)
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi (Object Profile CallPlan objectOfCtype)
open Silmaril.Machine.Abi.CtypeBridge

/-- The classification of a fragment scalar's C type, for every tag table. -/
theorem objectOfCtype_toCtype (tags : Tags) (k : Scalar) :
    objectOfCtype tags (Scalar.toCtype k) = .ok (Silmaril.Machine.Abi.SystemV.Kind.object k) := by
  cases k <;> rfl

theorem toCtype_injective : Function.Injective Scalar.toCtype := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [Scalar.toCtype, integerCtype] at h)

theorem mapM_toCtype (tags : Tags) (ks : List Scalar) :
    (ks.map Scalar.toCtype).mapM (objectOfCtype tags) =
      .ok (ks.map Silmaril.Machine.Abi.SystemV.Kind.object) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [List.map_cons, List.mapM_cons, objectOfCtype_toCtype, ih]
    rfl

theorem optionMapM_toCtype (tags : Tags) (r : Option Scalar) :
    (r.map Scalar.toCtype).mapM (objectOfCtype tags) =
      .ok (r.map Silmaril.Machine.Abi.SystemV.Kind.object) := by
  cases r with
  | none => rfl
  | some k => rw [Option.map_some, Option.mapM_some, objectOfCtype_toCtype]; rfl

theorem ctypePlan_proto (profile : Profile) (tags : Tags) (p : Silmaril.Machine.Abi.SystemV.Proto) :
    ctypePlan profile tags (Proto.ctypes p) (Proto.resultCtype p) = p.plan profile := by
  simp only [ctypePlan, Proto.ctypes, Proto.resultCtype, mapM_toCtype, optionMapM_toCtype,
    List.length_map, Silmaril.Machine.Abi.SystemV.Proto.plan,
    Silmaril.Machine.Abi.SystemV.Proto.objects, Silmaril.Machine.Abi.SystemV.Proto.resultObject]
  rfl

end Silmaril.Proofs.Machine.Abi.CtypeBridge
