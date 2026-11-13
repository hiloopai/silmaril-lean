module

public import Silmaril.Compiler.Native.Abi.Correspondence.Defs
public import Silmaril.Compiler.Native.Abi.Registered.Thms
public import Silmaril.Machine.SystemV.Abi.Ctypes.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Abi.Correspondence
open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi

private theorem integer_tags (tags : Tags) (integer : IntegerType)
    (retained : RetainedInteger integer) : integerObject tags integer = integerObject ∅ integer := by
  cases integer <;> first | rfl | exact False.elim retained

private theorem converted_integer (tags : Tags) (annotations : List Annot)
    (integer : IntegerType) (object : Object) (supported : annotationsSupported annotations = true)
    (retained : RetainedInteger integer)
    (classified : objectOfCtype tags (.mk annotations (.basic (.integer integer))) = .ok object)
    (source : integerObject tags integer = .ok object) :
    Abi.objectOfCodeType tags (Types.ofCtype (.mk annotations (.basic (.integer integer)))) = .ok object := by
  have empty : integerObject ∅ integer = .ok object :=
    (integer_tags tags integer retained).symm.trans source
  have nonenum : ∀ tag, integer ≠ .enum tag := by
    cases integer <;> simp_all [RetainedInteger]
  obtain ⟨bytes, same, width⟩ := integerObject_ordinary_shape tags integer object nonenum source
  subst object
  rcases width with rfl | rfl | rfl | rfl | rfl
  all_goals cases integer <;>
    simp_all [RetainedInteger, Types.ofCtype, Types.integerType,
      Abi.objectOfCodeType, Object.integer, integerObject, pure, Except.pure]

/-- Successful independent classification survives the actual native code-type
conversion whenever its scalar enum metadata is retained. -/
theorem classify (tags : Tags) (type : Ctype) (object : Object)
    (retained : Retained type) (classified : objectOfCtype tags type = .ok object) :
    Abi.objectOfCodeType tags (Types.ofCtype type) = .ok object := by
  obtain ⟨annotations, node⟩ := type
  have supported : annotationsSupported annotations = true :=
    objectOfCtype_annotations_supported tags annotations node object classified
  cases node with
  | basic basic =>
    show Abi.objectOfCodeType tags (Types.ofCtype (.mk annotations (.basic basic))) = .ok object
    cases basic with
    | integer integer =>
      have source : integerObject tags integer = .ok object :=
        objectOfCtype_integer tags annotations integer object supported classified
      exact converted_integer tags annotations integer object supported retained classified source
    | floating format =>
      show Abi.objectOfCodeType tags (Types.ofCtype (.mk annotations (.basic (.floating format)))) = .ok object
      cases format with
      | realFloating format =>
        cases format <;>
          simpa [Types.ofCtype, Silmaril.Compile.C.ofCtype, Silmaril.Compile.C.ofFloatingType,
            Abi.objectOfCodeType, objectOfCtype, layoutOfCtype, layoutOfCtypeWithFuel,
            scalarObject, supported, Except.map] using classified
  | pointer qualifiers pointee | byte =>
    simpa [Types.ofCtype, Silmaril.Compile.C.ofCtype, Abi.objectOfCodeType,
      objectOfCtype, layoutOfCtype, layoutOfCtypeWithFuel, scalarObject, supported, Except.map]
      using classified
  | array element length | struct tag | union tag =>
    simpa [Types.ofCtype, Silmaril.Compile.C.ofCtype, Abi.objectOfCodeType, supported]
      using classified
  | void | function result parameters variadic | functionNoParams result | atomic underlying =>
    simp [objectOfCtype, layoutOfCtype, layoutOfCtypeWithFuel, supported, Except.map] at classified


/-- The actual native argument-classification traversal agrees with all
independently classified objects, preserving their order and count. -/
theorem argument_objects (tags : Tags) (types : List Ctype) (specs : List Ffi.ObjectSpec)
    (matched : Parameters tags types specs) :
    (types.map Types.ofCtype).mapM (Abi.objectOfCodeType tags) = .ok (specs.map (·.object)) := by
  induction matched with
  | nil => rfl
  | @cons type spec types specs matched rest ih =>
    simp only [List.map_cons, List.mapM_cons, classify tags type spec.object matched.1 matched.2, ih]
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
  | object type spec retained classified =>
    have converted : Abi.objectOfCodeType tags (Types.ofCtype type) = .ok spec.object :=
      classify tags type spec.object retained classified
    have nonvoid : Types.ofCtype type ≠ .void := by
      intro same
      rw [same] at converted
      cases converted
    exact resultObject_some tags (Types.ofCtype type) spec.object nonvoid converted

/-- The actual call planner agrees with an independent typed FFI plan for
arbitrary retained arguments and results, including variadic named counts. -/
theorem call_plan (info : Silmaril.Compiler.Native.CallInfo) (signature : Ffi.Signature)
    (types : List Ctype) (arguments : Parameters info.tags types signature.arguments)
    (storedArguments : info.arguments = types.map Types.ofCtype)
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
  have registered : Registered.Parameters info.tags info.signature.params signature.arguments := by
    apply List.Forall₂.imp ?_ arguments
    intro type spec matched
    exact matched.2
  have classified : info.signature.params.mapM
      (fun type => Abi.objectOfCodeType info.tags (Types.Registered.ofCtype info.tags type)) =
      .ok (signature.arguments.map (·.object)) := by
    simpa only [List.mapM_map, Function.comp_def] using
      Registered.argument_objects info.tags info.signature.params signature.arguments registered
  have lengths : info.signature.params.length = signature.arguments.length := arguments.length_eq
  have independentlyPlanned : plan {} (signature.arguments.map (·.object))
      (signature.result.map (·.object)) (signature.arguments.map (·.object)).length
      info.signature.variadic = .ok signature.callPlan := by
    simpa only [profile, named, variadic, List.length_map, lengths] using signature.planned
  simp only [Emit.functionPlan, Planning.functionPlan, classified,
    result_object info.tags info.signature.ret signature.result result, Bind.bind, Except.bind]
  exact independentlyPlanned

end Silmaril.Compiler.Native.Abi.Correspondence
