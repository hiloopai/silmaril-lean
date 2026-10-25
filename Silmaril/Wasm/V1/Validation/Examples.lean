module

public import Silmaril.Wasm.V1.Validation.Modules
public import Silmaril.Wasm.V1.Validation.Inversion
public import Silmaril.Wasm.ModuleBuilder

/-! # Examples at the WebAssembly 1.0 validation boundary -/

@[expose] public section

namespace Silmaril.Wasm.V1.Validation.Examples

def idx0 {kind : IndexKind} : Idx kind := ⟨0⟩
def idx1 {kind : IndexKind} : Idx kind := ⟨1⟩

def addType : FuncType := ⟨[.i32, .i32], [.i32]⟩

def addBody : Expr := [.localGet idx0, .localGet idx1, .intBinOp .i32 .add]

/-- Parameters precede declared locals, and the second get preserves the first operand. -/
theorem addBody_typed (C : Context) :
    ExprType (functionContext C addType []) addBody [] [.i32] := by
  refine .cons (.localGet idx0 rfl) ?_
  refine .cons (.frame [.i32] (.localGet idx1 rfl)) ?_
  exact .singleton (.intBinOp .i32 .add)

/-- A loop branch targets the loop's empty input stack, even for a result-producing loop. -/
theorem looping_result_typed (C : Context) :
    InstrType C (.loop (some .i64) [.br idx0]) [] [.i64] := by
  apply InstrType.loop
  exact .singleton (.br idx0 rfl [] [.i64])

/-- The branch exits the block with its i32 result. -/
theorem block_result_typed (C : Context) :
    InstrType C (.block (some .i32) [.intConst .i32 7, .br idx0]) [] [.i32] := by
  apply InstrType.block
  exact .cons (.intConst .i32 7) (.singleton (.br idx0 rfl [] [.i32]))

/-- Both unreachable stacks are unconstrained by the current control context. -/
theorem unreachable_polymorphic (C : Context) :
    ExprType C [.unreachable, .intBinOp .i64 .add] [.f32] [.i64] :=
  .cons (.unreachable _ _) (.singleton (.intBinOp .i64 .add))

def addModule : Module := Scalar.Module.ofFunction addType [] addBody (some "add")

/-- A complete module proof, including type resolution and its exported function. -/
theorem addModule_valid : ModuleValid addModule where
  types := by simp [addModule, Scalar.Module.ofFunction, FuncTypeValid, addType]
  imports := by simp [addModule, Scalar.Module.ofFunction]
  functions := by
    intro f hf
    simp only [addModule, Scalar.Module.ofFunction, List.mem_singleton] at hf
    subst f
    exact ⟨addType, rfl, Nat.le_refl 1, addBody_typed _⟩
  tables := by simp [addModule, Scalar.Module.ofFunction]
  memories := by simp [addModule, Scalar.Module.ofFunction]
  globals := by simp [addModule, Scalar.Module.ofFunction]
  elements := by simp [addModule, Scalar.Module.ofFunction]
  data := by simp [addModule, Scalar.Module.ofFunction]
  start := by simp [StartValid, addModule, Scalar.Module.ofFunction]
  exports := by
    intro e he
    simp [addModule, Scalar.Module.ofFunction] at he
    subst e
    exact ⟨.func addType, rfl⟩
  uniqueExports := by simp [addModule, Scalar.Module.ofFunction]
  singleTable := by decide
  singleMemory := by decide

/-- Having two declared memories is invalid even when each separate limit is valid. -/
theorem two_memories_invalid :
    ¬ ModuleValid { memories := [⟨⟨0, none⟩⟩, ⟨⟨0, none⟩⟩] } := by
  intro h
  exact Nat.not_succ_le_self 1 h.singleMemory

/-- The one-result restriction applies to unused type-section entries as well. -/
theorem two_results_invalid :
    ¬ ModuleValid { types := [⟨[], [.i32, .i64]⟩] } := by
  intro h
  have ht := h.types ⟨[], [.i32, .i64]⟩ (by simp)
  exact Nat.not_succ_le_self 1 ht

/-- A mutable global can be imported but cannot be used as a constant initializer. -/
theorem mutable_import_valid :
    ImportValid [] ⟨"env", "counter", .global ⟨.var, .i32⟩⟩ :=
  ⟨.global ⟨.var, .i32⟩, rfl, trivial⟩

theorem mutable_global_not_constant :
    ¬ ConstantInstr { globals := [⟨.var, .i32⟩] } (.globalGet idx0) := by
  intro h
  cases h with
  | globalGet _ hget => cases hget

/-- Packed integer accesses must actually narrow the accessed scalar. -/
theorem full_width_is_not_packed : ¬ IntAccess .i32 (some .i32) ⟨0, 0⟩ := by
  simp [IntAccess, Aligned, PackSize.width, IntType.width]

/-- A one-byte access cannot request two-byte alignment. -/
theorem over_aligned_packed_invalid : ¬ IntAccess .i64 (some .i8) ⟨1, 0⟩ := by
  simp [IntAccess, Aligned, PackSize.width, IntType.width]

/-- Memory limits count 64 KiB pages and cannot exceed 65536 pages. -/
theorem oversized_memory_invalid : ¬ MemoryTypeValid ⟨⟨65537, none⟩⟩ := by
  simp [MemoryTypeValid, LimitsValid]

/-- Framing never removes the requirement for a declared memory. -/
theorem load_without_memory_invalid (a b : ResultType) :
    ¬ InstrType {} (.intLoad .i64 (some (.i16, .signed)) ⟨1, 3⟩) a b := by
  intro h
  exact h.intLoad_access.1 rfl

theorem immutable_global_write_invalid (a b : ResultType) :
    ¬ InstrType { globals := [⟨.const, .i32⟩] } (.globalSet idx0) a b := by
  intro h
  obtain ⟨t, ht⟩ := h.globalSet_lookup
  cases ht

/-- Duplicate names are forbidden independently of the validity of the export index. -/
theorem duplicate_exports_invalid (e : Export) :
    ¬ ModuleValid { exports := [e, e] } := by
  intro h
  simpa using h.uniqueExports

def initializedModule : Module where
  imports := [⟨"env", "base", .global ⟨.const, .i32⟩⟩]
  globals := [⟨⟨.const, .i32⟩, [.globalGet idx0]⟩]
  memories := [⟨⟨1, none⟩⟩]
  data := [⟨idx0, [.globalGet idx1], ⟨#[42]⟩⟩]

/-- Global initialization reads the import, while the segment offset reads the definition. -/
theorem initializedModule_valid : ModuleValid initializedModule where
  types := by simp [initializedModule]
  imports := by
    intro i hi
    simp only [initializedModule, List.mem_singleton] at hi
    subst i
    exact ⟨.global ⟨.const, .i32⟩, rfl, trivial⟩
  functions := by simp [initializedModule]
  tables := by simp [initializedModule]
  memories := by simp [initializedModule, MemoryTypeValid, LimitsValid]
  globals := by
    intro g hg
    simp only [initializedModule, List.mem_singleton] at hg
    subst g
    exact ⟨.singleton (.globalGet idx0 rfl), by
      intro i hi
      simp only [Global.init, List.mem_singleton] at hi
      subst i
      exact .globalGet idx0 rfl⟩
  elements := by simp [initializedModule]
  data := by
    intro d hd
    simp only [initializedModule, List.mem_singleton] at hd
    subst d
    refine ⟨⟨_, rfl⟩, .singleton (.globalGet idx1 (gt := ⟨.const, .i32⟩) rfl), ?_⟩
    intro i hi
    simp only [Data.offset, List.mem_singleton] at hi
    subst i
    exact .globalGet idx1 (t := .i32) rfl
  start := by simp [StartValid, initializedModule]
  exports := by simp [initializedModule]
  uniqueExports := by simp [initializedModule]
  singleTable := by decide
  singleMemory := by decide

end Silmaril.Wasm.V1.Validation.Examples
