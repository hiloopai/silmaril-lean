module

public import Silmaril.Cerberus.Ctype.Defs

/-! # Cerberus memory-interface types

The types Core needs from Cerberus's `frontend/model/mem_common.lem`,
`frontend/model/mem.lem`, `frontend/model/ail/ailSyntax.lem` (the operators
only), `frontend/concurrency/cmm_csem.lem` (`memory_order` only) and
`frontend/concurrency/linux.lem` (`linux_memory_order` only) at commit
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`.

`mem.lem` declares its value types abstractly and binds them to whichever OCaml
memory model (`Impl_mem`: concrete, symbolic, CHERI, …) Cerberus is built with.
The port makes that choice a parameter: `MemoryModel` bundles the abstract types,
and every Core type that mentions one takes a `MemoryModel`.
-/

@[expose] public section

namespace Silmaril.Cerberus

/-- Arithmetic operators (STD §6.5.5–6.5.12). -/
inductive ArithmeticOperator where
  | mul | div | mod
  | add | sub
  | shl | shr
  | band
  | bxor
  | bor
  deriving DecidableEq, Repr

/-- Unary operators. -/
inductive UnaryOperator where
  | plus
  | minus
  | bnot
  | address
  | indirection
  | postfixIncr
  | postfixDecr
  deriving DecidableEq, Repr

/-- Binary operators, also used for compound assignments. -/
inductive BinaryOperator where
  | arithmetic : ArithmeticOperator → BinaryOperator
  | comma
  | and
  | or
  | lt
  | gt
  | le
  | ge
  | eq
  | ne
  deriving DecidableEq, Repr

/-- C11 memory orders; `na` is non-atomic. -/
inductive MemoryOrder where
  | na
  | seqCst
  | relaxed
  | release
  | acquire
  | consume
  | acqRel
  deriving DecidableEq, Repr

/-- Linux-kernel memory-model orders. -/
inductive LinuxMemoryOrder where
  | once
  | acquire
  | release
  | rmb
  | wmb
  | mb
  | rbDep
  | rcuLock
  | rcuUnlock
  | syncRcu
  deriving DecidableEq, Repr

/-- Thread identifiers. -/
abbrev ThreadId := Nat

/-- Constraints over memory-model values, used by `PexprNode.constrained`. -/
inductive MemConstraint (a : Type) where
  | empty
  | eq : a → a → MemConstraint a
  | le : a → a → MemConstraint a
  | lt : a → a → MemConstraint a
  | inDevice : a → MemConstraint a
  | or : MemConstraint a → MemConstraint a → MemConstraint a
  | conj : List (MemConstraint a) → MemConstraint a
  | not : MemConstraint a → MemConstraint a
  deriving Repr

/-- The C operator a CHERI capability derivation stands for. -/
inductive DeriveCapOp where
  | unary : UnaryOperator → DeriveCapOp
  | binary : BinaryOperator → DeriveCapOp
  deriving DecidableEq, Repr

/-- Memory operations that do not touch the memory state. The `Bool` of
`deriveCap` is whether the operation is signed. -/
inductive PureMemOp where
  | deriveCap : DeriveCapOp → Bool → PureMemOp
  | capAssignValue
  | ptrTIntValue
  | byteFromInt
  | intFromByte
  deriving DecidableEq, Repr

/-- Memory operations that read or change the memory state. -/
inductive MemOp (sym : Type) where
  | ptrEq
  | ptrNe
  | ptrLt
  | ptrGt
  | ptrLe
  | ptrGe
  | ptrdiff
  | intFromPtr
  | ptrFromInt
  | ptrValidForDeref
  | ptrWellAligned
  | ptrArrayShift
  | ptrMemberShift : sym → Identifier → MemOp sym
  | memcpy
  | memcmp
  | realloc
  | vaStart
  | vaCopy
  | vaArg
  | vaEnd
  | copyAllocId
  | cheriIntrinsic : String → (Ctype × List Ctype) → MemOp sym
  deriving Repr

/-- The abstract types of Lem's `Mem` interface that Core mentions, supplied by a
memory model. `Footprint` is what a memory action returns so that two actions can
be checked for overlap. -/
structure MemoryModel where
  PointerValue : Type
  IntegerValue : Type
  FloatingValue : Type
  MemValue : Type
  Footprint : Type
  [decEqPointerValue : DecidableEq PointerValue]
  [decEqIntegerValue : DecidableEq IntegerValue]
  [decEqFloatingValue : DecidableEq FloatingValue]
  [decEqMemValue : DecidableEq MemValue]
  [decEqFootprint : DecidableEq Footprint]
  [reprPointerValue : Repr PointerValue]
  [reprIntegerValue : Repr IntegerValue]
  [reprFloatingValue : Repr FloatingValue]
  [reprMemValue : Repr MemValue]
  [reprFootprint : Repr Footprint]

attribute [instance] MemoryModel.decEqPointerValue MemoryModel.decEqIntegerValue
  MemoryModel.decEqFloatingValue MemoryModel.decEqMemValue MemoryModel.decEqFootprint
  MemoryModel.reprPointerValue MemoryModel.reprIntegerValue MemoryModel.reprFloatingValue
  MemoryModel.reprMemValue MemoryModel.reprFootprint

/-- Constraints over integer values. -/
abbrev IvConstraint (M : MemoryModel) := MemConstraint M.IntegerValue

end Silmaril.Cerberus
