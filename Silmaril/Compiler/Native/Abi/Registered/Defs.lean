module

public import Silmaril.Compiler.Native.Abi.Defs
public import Silmaril.Compiler.Native.Types.Registered.Defs
public import Silmaril.Compiler.Native.Emit.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Defs
/-! Source classifications for the actual registry-preserving native path.
No scalar enum restriction is needed: conversions retain the independently
registered width and signedness. This interface compares plans, not execution. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Abi.Registered
open Silmaril.Cerberus

open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi

/-- Independent source classifications align the parameter list with
an arbitrary typed FFI signature. No native classification or plan is assumed. -/
def Parameters (tags : Tags) (types : List Ctype) (specs : List Ffi.ObjectSpec) : Prop :=
  List.Forall₂ (fun type spec => objectOfCtype tags type = .ok spec.object)
    types specs

/-- Void has no object. Every value result uses its actual source C type
and an independently classified FFI object, before native type conversion. -/
inductive ResultClassification (tags : Tags) :
    Silmaril.Compile.C.CType → Option Ffi.ObjectSpec → Prop where
  | void : ResultClassification tags .void none
  | object (type : Ctype) (spec : Ffi.ObjectSpec)
      (classified : objectOfCtype tags type = .ok spec.object) :
      ResultClassification tags (Types.Registered.ofCtype tags type) (some spec)

end Silmaril.Compiler.Native.Abi.Registered
