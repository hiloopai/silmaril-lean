module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ViewFolding.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.BlockSemantics.Thms
public import Mathlib.Data.List.GetD

/-! Actual restore and optimize success paths discharge flattening acceptance.
The real function caller supplies the freshBase input bound, separately from
view acceptance; the actual restore register map is then globally injective.
No successful source execution or generic semantic simulation is assumed. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission
open Silmaril.Compile Silmaril.Machine
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.RTL (Opcode CallOracle packValues)

private theorem if_none_inv {α : Type} {condition : Bool} {result : Option α} {value : α}
    (accepted : (if condition then none else result) = some value) :
    condition = false ∧ result = some value := by
  cases condition with
  | false => exact ⟨rfl, accepted⟩
  | true => cases accepted

private theorem ret_match_inv {α : Type} {term : Silmaril.Machine.RTL.SSA.Term Nat}
    {result : List Nat → Option α} {value : α}
    (accepted : (match term with | .ret values => result values | _ => none) = some value) :
    ∃ values, term = .ret values ∧ result values = some value := by
  cases term with
  | ret values => exact ⟨values, rfl, accepted⟩
  | jump | cond | trap => cases accepted

private theorem singleton_of_length_lookup {α : Type} {values : List α} {value : α}
    (length : values.length = 1) (found : values[0]? = some value) : values = [value] := by
  cases values with
  | nil => cases found
  | cons head tail =>
    have empty : tail = [] := List.length_eq_zero_iff.mp (by simpa using length)
    have same : head = value := Option.some.inj found
    simp only [empty, same]

/-- Every successful actual restore exposes the exact function, checked block,
reverse-adapted instruction list and mutable-boundary commits it returns. -/
theorem restore_witness {base : Nat} {source candidate : Mir.Block} {view : View} {region : Old.Region}
    (accepted : restore base source view region = some candidate) :
    ∃ function block values instructions,
      Silmaril.Machine.RTL.SSA.ofLambdaSSA? [] region view.annotation view.inputs.length view.outputs.length = some function ∧
      function.entry = 0 ∧ function.blocks = [block] ∧
      block.params = List.range view.inputs.length ∧ block.term = .ret values ∧
      values.length = view.outputs.length ∧
      block.ops.mapM (newOp (register base view.inputs)) = some instructions ∧
      candidate = ⟨(instructions ++ (view.outputs.zip values).map
        (fun (original, result) => Mir.Instr.op (.move original (register base view.inputs result)))).toArray,
          source.term⟩ := by
  unfold restore at accepted
  dsimp only at accepted
  obtain ⟨function, flattened, checkedShape⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨shape, checkedLookup⟩ := if_none_inv checkedShape
  obtain ⟨block, found, checkedParameters⟩ := Option.bind_eq_some_iff.mp checkedLookup
  obtain ⟨parameters, checkedTerm⟩ := if_none_inv checkedParameters
  obtain ⟨values, term, checkedWidth⟩ := ret_match_inv checkedTerm
  obtain ⟨width, checkedConversion⟩ := if_none_inv checkedWidth
  obtain ⟨instructions, converted, same⟩ := Option.bind_eq_some_iff.mp checkedConversion
  have validShape : function.entry = 0 ∧ function.blocks.length = 1 := by simpa using shape
  have validParameters : block.params = List.range view.inputs.length := by simpa using parameters
  have validWidth : values.length = view.outputs.length := by simpa using width
  have singleton : function.blocks = [block] := singleton_of_length_lookup validShape.2 found
  exact ⟨function, block, values, instructions, flattened, validShape.1, singleton,
    validParameters, term, validWidth, converted, (Option.some.inj same).symm⟩

/-- Successful actual restore supplies the existing actual flatten-acceptance
predicate; it is not an independent semantic-success assumption. -/
theorem restore_compiles {base : Nat} {source candidate : Mir.Block} {view : View} {region : Old.Region}
    (accepted : restore base source view region = some candidate) :
    Silmaril.Machine.RTL.SSA.Compiles [] region view.annotation view.inputs.length view.outputs.length := by
  obtain ⟨function, _, _, _, flattened, _⟩ := restore_witness accepted
  simp only [Silmaril.Machine.RTL.SSA.Compiles, flattened, Option.isSome_some]

theorem foldl_max_initial (registers : List Nat) (initial : Nat) :
    initial ≤ registers.foldl Nat.max initial := by
  induction registers generalizing initial with
  | nil => exact Nat.le_refl initial
  | cons head rest ih => exact (Nat.le_max_left initial head).trans (ih (max initial head))

theorem member_le_foldl_max {registers : List Nat} {register : Nat} (member : register ∈ registers)
    (initial : Nat) : register ≤ registers.foldl Nat.max initial := by
  induction registers generalizing initial with
  | nil => cases member
  | cons head rest ih =>
    obtain rfl | member := List.mem_cons.mp member
    · exact (Nat.le_max_right initial register).trans (foldl_max_initial rest (max initial register))
    · exact ih member (max initial head)

/-- The actual per-function freshBase exceeds every register in every actual
member block's source operands and terminator. -/
theorem freshBase_input {function : Mir.Func} {block : Mir.Block} (member : block ∈ function.blocks.toList)
    {base : Nat} {input : Nat} (used : input ∈ (enter base block).inputs) : input < freshBase function := by
  have source : input ∈ block.instrs.toList.flatMap uses ++ Mir.DeadCode.termUses block.term := by
    change input ∈ (block.instrs.toList.flatMap uses ++ Mir.DeadCode.termUses block.term).dedup at used
    exact List.mem_dedup.mp used
  have included : input ∈ function.params ++ function.blocks.toList.flatMap (fun block =>
      Mir.DeadCode.termUses block.term ++ block.instrs.toList.flatMap (fun instruction => uses instruction ++ defs instruction)) := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨block, member, ?_⟩
    obtain operand | term := List.mem_append.mp source
    · apply List.mem_append_right
      obtain ⟨instruction, inBlock, read⟩ := List.mem_flatMap.mp operand
      exact List.mem_flatMap.mpr ⟨instruction, inBlock, List.mem_append_left _ read⟩
    · exact List.mem_append_left _ term
  exact Nat.lt_succ_of_le (member_le_foldl_max included 0)

/-- View acceptance checks unique input names. This gives no arbitrary-base
bound; the next theorem derives the real caller's bound separately. -/
theorem view_inputs_nodup {base : Nat} {source : Mir.Block} {result : View}
    (accepted : view base source = some result) : result.inputs.Nodup := by
  obtain ⟨_, unique, _, inputs, _⟩ := BlockSemantics.view_function accepted
  have names : ((enter base source).inputs ++ (enter base source).body.instrs.toList.flatMap defs).Nodup :=
    of_decide_eq_true unique
  rw [inputs]
  exact List.nodup_append.mp names |>.1

theorem view_inputs_below_freshBase {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (accepted : view (freshBase function) block = some result) :
    ∀ input ∈ result.inputs, input < freshBase function := by
  obtain ⟨_, _, _, inputs, _⟩ := BlockSemantics.view_function accepted
  intro input used
  exact freshBase_input member (inputs ▸ used)

theorem register_input {base : Nat} {inputs : List Nat} {index : Nat} (bound : index < inputs.length) :
    register base inputs index = inputs[index] := by
  simp only [register, bound, ↓reduceIte, List.getD_eq_getElem inputs 0 bound]

theorem register_fresh {base : Nat} {inputs : List Nat} {index : Nat} (bound : inputs.length ≤ index) :
    register base inputs index = base + (index - inputs.length) := by
  simp only [register, Nat.not_lt.mpr bound, ↓reduceIte]

/-- The exact register map used by restore is globally injective under unique
inputs and a separate real freshness bound, including disjoint input/fresh cases. -/
theorem register_injective {base : Nat} {inputs : List Nat} (unique : inputs.Nodup)
    (bounded : ∀ input ∈ inputs, input < base) : Function.Injective (register base inputs) := by
  intro first second equal
  by_cases firstInput : first < inputs.length
  · show first = second
    have firstValue : register base inputs first < base := by
      rw [register_input firstInput]
      exact bounded _ (List.getElem_mem _)
    by_cases secondInput : second < inputs.length
    · have values : inputs[first] = inputs[second] := by
        simpa only [register_input firstInput, register_input secondInput] using equal
      exact unique.getElem_inj_iff.mp values
    · have secondFresh : base ≤ register base inputs second := by
        rw [register_fresh (by omega)]
        omega
      omega
  · show first = second
    by_cases secondInput : second < inputs.length
    · have secondValue : register base inputs second < base := by
        rw [register_input secondInput]
        exact bounded _ (List.getElem_mem _)
      have firstFresh : base ≤ register base inputs first := by
        rw [register_fresh (by omega)]
        omega
      omega
    · have firstBound : inputs.length ≤ first := Nat.le_of_not_gt firstInput
      have secondBound : inputs.length ≤ second := Nat.le_of_not_gt secondInput
      have freshEqual : base + (first - inputs.length) = base + (second - inputs.length) := by
        simpa only [register_fresh firstBound, register_fresh secondBound] using equal
      omega

/-- Actual function/block membership and successful actual view construction
supply every input/fresh disjointness premise of restore's actual register map. -/
theorem view_register_injective {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (accepted : view (freshBase function) block = some result) :
    Function.Injective (register (freshBase function) result.inputs) :=
  register_injective (view_inputs_nodup accepted) (view_inputs_below_freshBase member accepted)

/-- Successful actual optimization exposes the very view, fold count, restore
and independent validation checks on its real selected path. -/
theorem optimize_witness {base : Nat} {source candidate : Mir.Block} {count : Nat}
    (accepted : optimize? base source = some (candidate, count)) :
    ∃ result, view base source = some result ∧
      restore base source result (foldRegion [.unknown] result.region).1 = some candidate ∧
      count = (foldRegion [.unknown] result.region).2 ∧ 0 < count ∧
      Validation.check base source candidate = true ∧
      Silmaril.Machine.RTL.SSA.Compiles [] (foldRegion [.unknown] result.region).1
        result.annotation result.inputs.length result.outputs.length := by
  unfold optimize? at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨result, viewed, checked⟩ := Option.bind_eq_some_iff.mp accepted
    split at checked
    · cases checked
    · rename_i nonzero
      obtain ⟨actual, restored, validated⟩ := Option.bind_eq_some_iff.mp checked
      split at validated
      · rename_i valid
        obtain ⟨same, counted⟩ := Prod.mk.inj (Option.some.inj validated)
        have restoredCandidate : restore base source result (foldRegion [.unknown] result.region).1 = some candidate :=
          same ▸ restored
        exact ⟨result, viewed, restoredCandidate, counted.symm, by omega,
          same ▸ valid, restore_compiles restoredCandidate⟩
      · cases validated

/-- The existing fold/flatten observation theorem needs no separately assumed
Compiles predicate once the actual restore for that folded view has succeeded. -/
theorem restored_view_eval_iff (oracle : CallOracle)
    (signatures : Silmaril.Machine.RTL.SSA.CallOracle.MatchesSigs oracle [])
    {base : Nat} {source candidate : Mir.Block} {result : View}
    (accepted : view base source = some result)
    (restored : restore base source result (foldRegion [.unknown] result.region).1 = some candidate)
    {frame : Silmaril.Machine.RTL.Frame Nat} {args : List Lir.Word}
    (arguments : frame.readAll (Silmaril.Machine.RTL.SSA.freshRegs 0 result.inputs.length) = some args)
    {env : Semantics.Env Lir.Word} (input : env 0 = packValues args)
    {before : Silmaril.Machine.Lir.Memory} {label : Nat} {value : Value Lir.Word}
    {after : Silmaril.Machine.Lir.Memory} :
    Semantics.Region.Eval (Opcode.step oracle) env result.region before label value after ↔
      (label = 0 ∧ ∃ values, value = packValues values ∧
        Silmaril.Machine.RTL.SSA.Func.Exec oracle
          (Silmaril.Machine.RTL.SSA.ofLambdaSSA [] (foldRegion [.unknown] result.region).1
            result.annotation result.inputs.length result.outputs.length)
          0 frame before (.returned values after)) ∨
      (label = 1 ∧ value = .unit ∧
        Silmaril.Machine.RTL.SSA.Func.Exec oracle
          (Silmaril.Machine.RTL.SSA.ofLambdaSSA [] (foldRegion [.unknown] result.region).1
            result.annotation result.inputs.length result.outputs.length)
          0 frame before (.trapped after)) :=
  ViewFolding.view_flattened_eval_iff oracle signatures accepted (restore_compiles restored) arguments input

/-- The function returned by the actual partial flattener and accepted by
restore is exactly a singleton with the checked return, not the fallback trap. -/
theorem restored_function_singleton {base : Nat} {source candidate : Mir.Block} {result : View}
    {region : Old.Region} (accepted : restore base source result region = some candidate) :
    ∃ (block : Silmaril.Machine.RTL.SSA.Block Nat) (values : List Nat) (instructions : List Mir.Instr),
      Silmaril.Machine.RTL.SSA.ofLambdaSSA [] region result.annotation result.inputs.length result.outputs.length =
        ViewTyping.singleFunction (List.range result.inputs.length) block.ops values ∧
      block.params = List.range result.inputs.length ∧ block.term = .ret values ∧
      values.length = result.outputs.length ∧
      block.ops.mapM (newOp (register base result.inputs)) = some instructions ∧
      candidate = ⟨(instructions ++ (result.outputs.zip values).map
        (fun (original, output) => Mir.Instr.op (.move original (register base result.inputs output)))).toArray,
          source.term⟩ := by
  obtain ⟨function, block, values, instructions, flattened, entry, singleton, parameters,
    term, width, converted, emitted⟩ := restore_witness accepted
  have signature : function.sig = ⟨result.inputs.length, result.outputs.length⟩ :=
    Silmaril.Machine.RTL.SSA.ofLambdaSSA?_sig flattened
  have actualFunction : Silmaril.Machine.RTL.SSA.ofLambdaSSA [] region result.annotation
      result.inputs.length result.outputs.length = function := by
    simp only [Silmaril.Machine.RTL.SSA.ofLambdaSSA, flattened, Option.getD_some]
  have exactSingleton : function = ViewTyping.singleFunction (List.range result.inputs.length) block.ops values := by
    cases function with
    | mk sig start blocks =>
      simp only at signature entry singleton
      rw [signature, entry, singleton]
      cases block with
      | mk params operations terminator =>
        simp only at parameters term
        rw [parameters, term]
        simp only [ViewTyping.singleFunction, List.length_range, width]
  exact ⟨block, values, instructions, actualFunction.trans exactSingleton,
    parameters, term, width, converted, emitted⟩

end Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission
