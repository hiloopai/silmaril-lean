module

/-! # Cerberus implementation-defined constants

The `implementation_constant` type of Cerberus's
`frontend/model/implementation.lem` at commit
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. These name the implementation-defined
parameters of ISO C Annex J.3 that Core refers to through `PexprNode.impl` and
`Name.impl`; the implementation record that gives them values is not ported.
Lem's equality and ordering on these constants are structural.
-/

@[expose] public section

namespace Silmaril.Cerberus

/-- Implementation-defined constants and builtin functions. -/
inductive ImplementationConstant where
  | environmentStartupName
  | environmentStartupType
  | charactersBitsInByte
  | charactersExecutionCharacterSetValues
  | charactersTodo1
  | charactersTodo2
  | charactersPlainCharIsSigned
  | charactersTodo3
  | charactersTodo4
  | charactersTodo5
  | charactersTodo6
  | charactersTodo7
  | charactersTodo8
  | charactersTodo9
  | charactersTodo10
  | integerEncode
  | integerDecode
  | integerConvNonrepresentableSignedInteger
  | sizeof
  | alignof
  | shrSignedNegative
  | bitwiseComplement
  | plainBitfieldSign
  | bitfieldOtherTypes
  | atomicBitfieldPermitted
  | ctypeMin
  | ctypeMax
  | builtinFunction : String → ImplementationConstant
  deriving DecidableEq, Repr

end Silmaril.Cerberus
