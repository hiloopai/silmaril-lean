module

public import Silmaril.Compiler.Native.Abi.Defs
public import Silmaril.Compiler.Native.Types.Defs
public import Silmaril.Compiler.Native.Emit.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Defs
/-! Type-retention boundary for comparing native ABI lowering with the
independent Cerberus classifier. Scalar enums currently lose their registry
before code-type classification; aggregates retain their original whole type. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Abi.Correspondence
open Silmaril.Cerberus

/-- This is a syntax/metadata condition, not successful classification. -/
def RetainedInteger : IntegerType → Prop
  | .enum _ => False
  | _ => True

/-- Only top-level scalar enum metadata is excluded. Enum fields inside an
aggregate remain available to the independent recursive layout classifier. -/
def Retained : Ctype → Prop
  | .mk _ (.basic (.integer integer)) => RetainedInteger integer
  | _ => True

open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi

/-- Independent source classifications align the retained parameter list with
an arbitrary typed FFI signature. No native classification or plan is assumed. -/
def Parameters (tags : Tags) (types : List Ctype) (specs : List Ffi.ObjectSpec) : Prop :=
  List.Forall₂ (fun type spec => Retained type ∧ objectOfCtype tags type = .ok spec.object)
    types specs

/-- Void has no object. Every value result retains its actual source C type
and an independently classified FFI object, before native type conversion. -/
inductive ResultClassification (tags : Tags) :
    Silmaril.Compile.C.CType → Option Ffi.ObjectSpec → Prop where
  | void : ResultClassification tags .void none
  | object (type : Ctype) (spec : Ffi.ObjectSpec)
      (retained : Retained type) (classified : objectOfCtype tags type = .ok spec.object) :
      ResultClassification tags (Types.ofCtype type) (some spec)

end Silmaril.Compiler.Native.Abi.Correspondence
