module

public import Silmaril.Wasm.Validation.TypeOk

@[expose] public section

/-! # Typing family: table instructions (§2.3 "Table instructions")

Spec rules (all present): `Instr_ok/table.get`, `table.set`, `table.size`,
`table.grow`, `table.fill`, `table.copy`, `table.init`, `elem.drop`.
Operands of address type `at` are `at.valType` (table64).
-/

namespace Silmaril.Wasm.Validation

inductive TableInstrOk (C : Context) : Instr → InstrType → Prop where
  /-- `Instr_ok/table.get`. -/
  | tableGet {x : TableIdx} {a : AddrType} {l : Limits} {rt : CRefType}
      (h : C.tables[x.toNat]? = some ⟨a, l, rt⟩) :
      TableInstrOk C (.tableGet x) (.plain [a.valType] [.refv rt])
  /-- `Instr_ok/table.set`. -/
  | tableSet {x : TableIdx} {a : AddrType} {l : Limits} {rt : CRefType}
      (h : C.tables[x.toNat]? = some ⟨a, l, rt⟩) :
      TableInstrOk C (.tableSet x) (.plain [a.valType, .refv rt] [])
  /-- `Instr_ok/table.size`. -/
  | tableSize {x : TableIdx} {a : AddrType} {l : Limits} {rt : CRefType}
      (h : C.tables[x.toNat]? = some ⟨a, l, rt⟩) :
      TableInstrOk C (.tableSize x) (.plain [] [a.valType])
  /-- `Instr_ok/table.grow`. -/
  | tableGrow {x : TableIdx} {a : AddrType} {l : Limits} {rt : CRefType}
      (h : C.tables[x.toNat]? = some ⟨a, l, rt⟩) :
      TableInstrOk C (.tableGrow x) (.plain [.refv rt, a.valType] [a.valType])
  /-- `Instr_ok/table.fill`. -/
  | tableFill {x : TableIdx} {a : AddrType} {l : Limits} {rt : CRefType}
      (h : C.tables[x.toNat]? = some ⟨a, l, rt⟩) :
      TableInstrOk C (.tableFill x) (.plain [a.valType, .refv rt, a.valType] [])
  /-- `Instr_ok/table.copy`. -/
  | tableCopy {x₁ x₂ : TableIdx} {a₁ a₂ : AddrType} {l₁ l₂ : Limits} {rt₁ rt₂ : CRefType}
      (h₁ : C.tables[x₁.toNat]? = some ⟨a₁, l₁, rt₁⟩)
      (h₂ : C.tables[x₂.toNat]? = some ⟨a₂, l₂, rt₂⟩)
      (hs : Sub C.toTypeCtx rt₂ rt₁) :
      TableInstrOk C (.tableCopy x₁ x₂)
        (.plain [a₁.valType, a₂.valType, (AddrType.min a₁ a₂).valType] [])
  /-- `Instr_ok/table.init`. -/
  | tableInit {x : TableIdx} {y : ElemIdx} {a : AddrType} {l : Limits} {rt₁ rt₂ : CRefType}
      (h : C.tables[x.toNat]? = some ⟨a, l, rt₁⟩) (he : C.elems[y.toNat]? = some rt₂)
      (hs : Sub C.toTypeCtx rt₂ rt₁) :
      TableInstrOk C (.tableInit x y) (.plain [a.valType, .i32, .i32] [])
  /-- `Instr_ok/elem.drop`. -/
  | elemDrop {y : ElemIdx} {rt : CRefType} (he : C.elems[y.toNat]? = some rt) :
      TableInstrOk C (.elemDrop y) (.plain [] [])

end Silmaril.Wasm.Validation
