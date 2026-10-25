module

public import Silmaril.Wasm.Execution.Core.Store
public import Silmaril.Wasm.Numerics.Profile

@[expose] public section

/-! # Reduction family: table and element-segment instructions

Spec rules (all 18 present): `table.get-oob`, `table.get-val`, `table.set-oob`,
`table.set-val`, `table.size`, `table.grow-succeed`, `table.grow-fail`,
`table.fill-oob`, `table.fill-zero`, `table.fill-succ`, `table.copy-oob`,
`table.copy-zero`, `table.copy-le`, `table.copy-gt`, `table.init-oob`,
`table.init-zero`, `table.init-succ`, `elem.drop`.

Operands of address type are `CONST at i` (`aconst`), so table64 is covered. The
spec's `-fail` rule for `table.grow` has no premise; the profile's grow policy
restricts it (`Profile.spec` allows it unconditionally).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics

/-- `CONST at i`. -/
abbrev aconst (a : AddrType) (i : BitVec a.intType.width) : Admin := .plain (.intConst a.intType i)

variable {H : Type}

inductive TableStep (P : Profile) : Config H → Config H → Prop where
  /-- `Step_read/table.get-oob`. -/
  | getOob {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType} {i : BitVec a.intType.width}
      {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
      (h : ti.refs.length ≤ i.toNat) :
      TableStep P ⟨s, f, [aconst a i, .plain (.tableGet x)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/table.get-val`. -/
  | getVal {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType} {i : BitVec a.intType.width}
      {ta : Nat} {ti : TableInst} {r : Ref} (ht : s.table? f x = some (ta, ti))
      (h : ti.refs[i.toNat]? = some r) :
      TableStep P ⟨s, f, [aconst a i, .plain (.tableGet x)]⟩ ⟨s, f, [.ref r]⟩
  /-- `Step/table.set-oob`. -/
  | setOob {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType} {i : BitVec a.intType.width}
      {r : Ref} {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
      (h : ti.refs.length ≤ i.toNat) :
      TableStep P ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step/table.set-val`. -/
  | setVal {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType} {i : BitVec a.intType.width}
      {r : Ref} {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti))
      (h : i.toNat < ti.refs.length) :
      TableStep P ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x)]⟩
        ⟨s.setTable ta { ti with refs := ti.refs.set i.toNat r }, f, []⟩
  /-- `Step_read/table.size`. -/
  | size {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
      (ht : s.table? f x = some (ta, ti)) :
      TableStep P ⟨s, f, [.plain (.tableSize x)]⟩
        ⟨s, f, [aconst ti.type.address (BitVec.ofNat _ ti.refs.length)]⟩
  /-- `Step/table.grow-succeed`. -/
  | growSucceed {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
      {n : BitVec a.intType.width} {r : Ref} {ta : Nat} {ti ti' : TableInst}
      (ht : s.table? f x = some (ta, ti)) (hg : ti.grow? n.toNat r = some ti')
      (hp : P.growMaySucceed .table ta ti.refs.length n.toNat) :
      TableStep P ⟨s, f, [.ref r, aconst a n, .plain (.tableGrow x)]⟩
        ⟨s.setTable ta ti', f, [aconst a (BitVec.ofNat _ ti.refs.length)]⟩
  /-- `Step/table.grow-fail` (result `-1`). -/
  | growFail {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
      {n : BitVec a.intType.width} {r : Ref} {ta : Nat} {ti : TableInst}
      (ht : s.table? f x = some (ta, ti))
      (hp : P.growMayFail .table ta ti.refs.length n.toNat ∨ ti.grow? n.toNat r = none) :
      TableStep P ⟨s, f, [.ref r, aconst a n, .plain (.tableGrow x)]⟩
        ⟨s, f, [aconst a (BitVec.allOnes _)]⟩
  /-- `Step_read/table.fill-oob`. -/
  | fillOob {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
      {i n : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
      (ht : s.table? f x = some (ta, ti)) (h : ti.refs.length < i.toNat + n.toNat) :
      TableStep P ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.tableFill x)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/table.fill-zero`. -/
  | fillZero {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
      {i : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
      (ht : s.table? f x = some (ta, ti)) (h : i.toNat ≤ ti.refs.length) :
      TableStep P ⟨s, f, [aconst a i, v.toAdmin, aconst a 0, .plain (.tableFill x)]⟩ ⟨s, f, []⟩
  /-- `Step_read/table.fill-succ`. -/
  | fillSucc {s : Store H} {f : Frame} {x : TableIdx} {a : AddrType}
      {i n : BitVec a.intType.width} {v : Val} {ta : Nat} {ti : TableInst}
      (ht : s.table? f x = some (ta, ti)) (h : i.toNat + n.toNat ≤ ti.refs.length)
      (hn : n ≠ 0) :
      TableStep P ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.tableFill x)]⟩
        ⟨s, f, [aconst a i, v.toAdmin, .plain (.tableSet x),
          aconst a (i + 1), v.toAdmin, aconst a (n - 1), .plain (.tableFill x)]⟩
  /-- `Step_read/table.copy-oob`. -/
  | copyOob {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
      {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
      {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
      (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
      (h : ti₁.refs.length < i₁.toNat + n.toNat ∨ ti₂.refs.length < i₂.toNat + n.toNat) :
      TableStep P ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/table.copy-zero`. -/
  | copyZero {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
      {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width}
      {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
      (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
      (h : i₁.toNat ≤ ti₁.refs.length ∧ i₂.toNat ≤ ti₂.refs.length) :
      TableStep P ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' 0, .plain (.tableCopy x₁ x₂)]⟩
        ⟨s, f, []⟩
  /-- `Step_read/table.copy-le`. -/
  | copyLe {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
      {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
      {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
      (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
      (h : i₁.toNat + n.toNat ≤ ti₁.refs.length ∧ i₂.toNat + n.toNat ≤ ti₂.refs.length)
      (hn : n ≠ 0) (hle : i₁.toNat ≤ i₂.toNat) :
      TableStep P ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩
        ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, .plain (.tableGet x₂), .plain (.tableSet x₁),
          aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1), .plain (.tableCopy x₁ x₂)]⟩
  /-- `Step_read/table.copy-gt`. -/
  | copyGt {s : Store H} {f : Frame} {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType}
      {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
      {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}
      (h₁ : s.table? f x₁ = some (ta₁, ti₁)) (h₂ : s.table? f x₂ = some (ta₂, ti₂))
      (h : i₁.toNat + n.toNat ≤ ti₁.refs.length ∧ i₂.toNat + n.toNat ≤ ti₂.refs.length)
      (hn : n ≠ 0) (hgt : i₂.toNat < i₁.toNat) :
      TableStep P ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.tableCopy x₁ x₂)]⟩
        ⟨s, f, [aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1), aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1),
          .plain (.tableGet x₂), .plain (.tableSet x₁),
          aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1), .plain (.tableCopy x₁ x₂)]⟩
  /-- `Step_read/table.init-oob`. -/
  | initOob {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
      {i : BitVec a.intType.width} {j n : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
      (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
      (h : ti.refs.length < i.toNat + n.toNat ∨ ei.refs.length < j.toNat + n.toNat) :
      TableStep P ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/table.init-zero`. -/
  | initZero {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
      {i : BitVec a.intType.width} {j : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
      (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
      (h : i.toNat ≤ ti.refs.length ∧ j.toNat ≤ ei.refs.length) :
      TableStep P ⟨s, f, [aconst a i, constI32 j, constI32 0, .plain (.tableInit x y)]⟩ ⟨s, f, []⟩
  /-- `Step_read/table.init-succ`. -/
  | initSucc {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
      {i : BitVec a.intType.width} {j n : BitVec 32} {ta ea : Nat} {ti : TableInst} {ei : ElemInst}
      {r : Ref}
      (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
      (h : i.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length)
      (hn : n ≠ 0) (hr : ei.refs[j.toNat]? = some r) :
      TableStep P ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩
        ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x),
          aconst a (i + 1), constI32 (j + 1), constI32 (n - 1), .plain (.tableInit x y)]⟩
  /-- `Step/elem.drop`. -/
  | elemDrop {s : Store H} {f : Frame} {y : ElemIdx} {ea : Nat} {ei : ElemInst}
      (he : s.elem? f y = some (ea, ei)) :
      TableStep P ⟨s, f, [.plain (.elemDrop y)]⟩ ⟨s.setElem ea [], f, []⟩

end Silmaril.Wasm.Execution.Core
