module

public import Silmaril.Wasm.V1.Types

@[expose] public section

/-! # Lime1 types

Lime1 retains Wasm1's numeric value types and 32-bit linear memory. Multivalue
adds indexed block signatures; it does not add reference or vector value types.
The profile is pinned to the [official Lime1 definition](https://github.com/WebAssembly/tool-conventions/blob/83e5d715d0c18aee51e2d5ae9434f22d67b6e905/Lime.md).
-/

namespace Silmaril.Wasm.Lime1

abbrev ValType := V1.ValType
abbrev ResultType := V1.ResultType
abbrev Limits := V1.Limits
abbrev FuncType := V1.FuncType
abbrev TableType := V1.TableType
abbrev MemoryType := V1.MemoryType
abbrev GlobalType := V1.GlobalType
abbrev ExternType := V1.ExternType
abbrev MemArg := V1.MemArg
abbrev PackSize := V1.PackSize

/-- The sign-extension sizes are the three scalar packed sizes. Operand-width
restrictions remain separate, just as for packed loads and stores. -/
inductive IntUnOp where
  | clz | ctz | popcnt
  | extend (size : PackSize)
  deriving DecidableEq, Repr

abbrev ConvertOp := Wasm.ConvertOp

/-- Indexed block signatures support both parameters and multiple results. -/
inductive BlockType where
  | empty
  | value (type : ValType)
  | typeIdx (index : TypeIdx)
  deriving DecidableEq, Repr

def BlockType.toCore : BlockType → Wasm.BlockType
  | .empty => .empty
  | .value t => .value (.num t)
  | .typeIdx i => .typeIdx i

theorem BlockType.toCore_injective : Function.Injective toCore := by
  intro a b h
  cases a <;> cases b <;> simp_all [toCore]

/-- Source revision of the stable profile definition. -/
def sourceRevision : String := "83e5d715d0c18aee51e2d5ae9434f22d67b6e905"

end Silmaril.Wasm.Lime1

namespace Silmaril.Wasm.V1

def BlockType.toLime : BlockType → Lime1.BlockType
  | none => .empty
  | some t => .value t

theorem BlockType.toLime_injective : Function.Injective toLime := by
  intro a b h
  cases a <;> cases b <;> simp_all [toLime]

end Silmaril.Wasm.V1
