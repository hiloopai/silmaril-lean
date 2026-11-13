module

public import Silmaril.Compiler.Native.Abi.Registered.Defs
public import Silmaril.Compiler.Native.Types.Registered.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Abi.Registered
open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi

/-- The actual native argument-classification traversal agrees with all
independently classified objects, preserving their order and count. -/
theorem argument_objects (tags : Tags) (types : List Ctype) (specs : List Ffi.ObjectSpec)
    (matched : Parameters tags types specs) :
    (types.map (Types.Registered.ofCtype tags)).mapM (Abi.objectOfCodeType tags) = .ok (specs.map (·.object)) := by
  induction matched with
  | nil => rfl
  | @cons type spec types specs matched rest ih =>
    simp only [List.map_cons, List.mapM_cons, Types.Registered.classify tags type spec.object matched, ih]
    rfl

private theorem resultObject_some (tags : Tags) (code : Silmaril.Compile.C.CType) (object : Object)
    (nonvoid : code ≠ .void) (classified : Abi.objectOfCodeType tags code = .ok object) :
    Emit.resultObject tags code = .ok (some object) := by
  cases code <;> first
    | exact False.elim (nonvoid rfl)
    | simp only [Emit.resultObject, Planning.resultObject, classified]; rfl

/-- Native result lowering preserves the independently classified result,
including aggregate, x87 and indirect-memory objects; void is kept distinct. -/
theorem result_object (tags : Tags) (code : Silmaril.Compile.C.CType)
    (result : Option Ffi.ObjectSpec) (matched : ResultClassification tags code result) :
    Emit.resultObject tags code = .ok (result.map (·.object)) := by
  cases matched with
  | void => rfl
  | object type spec classified =>
    have converted : Abi.objectOfCodeType tags (Types.Registered.ofCtype tags type) = .ok spec.object :=
      Types.Registered.classify tags type spec.object classified
    have nonvoid : Types.Registered.ofCtype tags type ≠ .void := by
      intro same
      rw [same] at converted
      cases converted
    exact resultObject_some tags (Types.Registered.ofCtype tags type) spec.object nonvoid converted

/-- The actual call planner agrees with an independent typed FFI plan for
arbitrary registered arguments and results, including variadic named counts. -/
theorem call_plan (info : Silmaril.Compiler.Native.CallInfo) (signature : Ffi.Signature)
    (types : List Ctype) (arguments : Parameters info.tags types signature.arguments)
    (storedArguments : info.arguments = types.map (Types.Registered.ofCtype info.tags))
    (result : ResultClassification info.tags info.result signature.result)
    (profile : signature.profile = {}) (named : signature.namedCount = info.namedCount)
    (variadic : signature.variadic = info.variadic) :
    Emit.callPlan info = .ok signature.callPlan := by
  have independentlyPlanned : plan {} (signature.arguments.map (·.object))
      (signature.result.map (·.object)) info.namedCount info.variadic = .ok signature.callPlan := by
    simpa only [profile, named, variadic] using signature.planned
  simp only [Emit.callPlan, Planning.callPlan, storedArguments,
    argument_objects info.tags types signature.arguments arguments,
    result_object info.tags info.result signature.result result, Bind.bind, Except.bind]
  exact independentlyPlanned

/-- The actual function-entry/result planner agrees with the same independent
FFI contract. All declaration parameters are named, even for a variadic function. -/
theorem function_plan (info : Silmaril.Compiler.Native.FunctionInfo) (signature : Ffi.Signature)
    (arguments : Parameters info.tags info.signature.params signature.arguments)
    (result : ResultClassification info.tags info.signature.ret signature.result)
    (profile : signature.profile = {})
    (named : signature.namedCount = info.signature.params.length)
    (variadic : signature.variadic = info.signature.variadic) :
    Emit.functionPlan info = .ok signature.callPlan := by
  have classified : info.signature.params.mapM
      (fun type => Abi.objectOfCodeType info.tags (Types.Registered.ofCtype info.tags type)) =
      .ok (signature.arguments.map (·.object)) := by
    simpa only [List.mapM_map, Function.comp_def] using
      argument_objects info.tags info.signature.params signature.arguments arguments
  have lengths : info.signature.params.length = signature.arguments.length := arguments.length_eq
  have independentlyPlanned : plan {} (signature.arguments.map (·.object))
      (signature.result.map (·.object)) (signature.arguments.map (·.object)).length
      info.signature.variadic = .ok signature.callPlan := by
    simpa only [profile, named, variadic, List.length_map, lengths] using signature.planned
  simp only [Emit.functionPlan, Planning.functionPlan, classified,
    result_object info.tags info.signature.ret signature.result result, Bind.bind, Except.bind]
  exact independentlyPlanned

end Silmaril.Compiler.Native.Abi.Registered
