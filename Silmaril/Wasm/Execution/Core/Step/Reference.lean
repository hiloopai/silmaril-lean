module

public import Silmaril.Wasm.Execution.Core.Values

@[expose] public section

/-! # Reduction family: reference, i31 and extern instructions

Spec rules (all 20 present): `Step_read/ref.null`, `Step_read/ref.func`,
`Step_pure/ref.i31`, `ref.is_null-true/false`, `ref.as_non_null-null/addr`,
`ref.eq-null/true/false`, `Step_read/ref.test-true/false`,
`Step_read/ref.cast-succeed/fail`, `Step_pure/i31.get-null/num`,
`extern.convert_any-null/addr`, `any.convert_extern-null/addr`.

Casts consult `RefOk` (§4.1) against the reference type instantiated in the
current module (`$inst_reftype(f.MODULE, rt)`).
-/

namespace Silmaril.Wasm.Execution.Core

variable {H : Type}

inductive RefStep : Config H → Config H → Prop where
  /-- `Step_read/ref.null`. -/
  | refNull {s : Store H} {f : Frame} (ht : HeapType) :
      RefStep ⟨s, f, [.plain (.refNull ht)]⟩ ⟨s, f, [.ref .null]⟩
  /-- `Step_read/ref.func`. -/
  | refFunc {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} (h : f.module.funcs[x.toNat]? = some a) :
      RefStep ⟨s, f, [.plain (.refFunc x)]⟩ ⟨s, f, [.ref (.func a)]⟩
  /-- `Step_pure/ref.i31` (`$wrap__(32, 31, i)`). -/
  | refI31 {s : Store H} {f : Frame} (i : BitVec 32) :
      RefStep ⟨s, f, [constI32 i, .plain .refI31]⟩ ⟨s, f, [.ref (.i31 (i.setWidth 31))]⟩
  /-- `Step_pure/ref.is_null-true`. -/
  | isNullTrue {s : Store H} {f : Frame} :
      RefStep ⟨s, f, [.ref .null, .plain .refIsNull]⟩ ⟨s, f, [constI32 1]⟩
  /-- `Step_pure/ref.is_null-false`. -/
  | isNullFalse {s : Store H} {f : Frame} {r : Ref} (h : r ≠ .null) :
      RefStep ⟨s, f, [.ref r, .plain .refIsNull]⟩ ⟨s, f, [constI32 0]⟩
  /-- `Step_pure/ref.as_non_null-null`. -/
  | asNonNullNull {s : Store H} {f : Frame} :
      RefStep ⟨s, f, [.ref .null, .plain .refAsNonNull]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_pure/ref.as_non_null-addr`. -/
  | asNonNullAddr {s : Store H} {f : Frame} {r : Ref} (h : r ≠ .null) :
      RefStep ⟨s, f, [.ref r, .plain .refAsNonNull]⟩ ⟨s, f, [.ref r]⟩
  /-- `Step_pure/ref.eq-null`. -/
  | eqNull {s : Store H} {f : Frame} :
      RefStep ⟨s, f, [.ref .null, .ref .null, .plain .refEq]⟩ ⟨s, f, [constI32 1]⟩
  /-- `Step_pure/ref.eq-true`. -/
  | eqTrue {s : Store H} {f : Frame} {r : Ref} (h : r ≠ .null) :
      RefStep ⟨s, f, [.ref r, .ref r, .plain .refEq]⟩ ⟨s, f, [constI32 1]⟩
  /-- `Step_pure/ref.eq-false`. -/
  | eqFalse {s : Store H} {f : Frame} {r₁ r₂ : Ref} (h : r₁ ≠ r₂) :
      RefStep ⟨s, f, [.ref r₁, .ref r₂, .plain .refEq]⟩ ⟨s, f, [constI32 0]⟩
  /-- `Step_read/ref.test-true`. -/
  | testTrue {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
      (h : RefOk s r (f.module.instRef rt)) :
      RefStep ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 1]⟩
  /-- `Step_read/ref.test-false`. -/
  | testFalse {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt)) :
      RefStep ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 0]⟩
  /-- `Step_read/ref.cast-succeed`. -/
  | castSucceed {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
      (h : RefOk s r (f.module.instRef rt)) :
      RefStep ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩
  /-- `Step_read/ref.cast-fail`. -/
  | castFail {s : Store H} {f : Frame} {r : Ref} {rt : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt)) :
      RefStep ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_pure/i31.get-null`. -/
  | i31GetNull {s : Store H} {f : Frame} (sx : Signedness) :
      RefStep ⟨s, f, [.ref .null, .plain (.i31Get sx)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_pure/i31.get-num` (`$extend__(31, 32, sx, i)`). -/
  | i31GetNum {s : Store H} {f : Frame} (sx : Signedness) (i : BitVec 31) :
      RefStep ⟨s, f, [.ref (.i31 i), .plain (.i31Get sx)]⟩
        ⟨s, f, [constI32 (match sx with | .signed => i.signExtend 32 | .unsigned => i.setWidth 32)]⟩
  /-- `Step_pure/extern.convert_any-null`. -/
  | externConvertNull {s : Store H} {f : Frame} :
      RefStep ⟨s, f, [.ref .null, .plain .externConvertAny]⟩ ⟨s, f, [.ref .null]⟩
  /-- `Step_pure/extern.convert_any-addr`. -/
  | externConvertAddr {s : Store H} {f : Frame} {r : Ref} (h : r ≠ .null) :
      RefStep ⟨s, f, [.ref r, .plain .externConvertAny]⟩ ⟨s, f, [.ref (.extern r)]⟩
  /-- `Step_pure/any.convert_extern-null`. -/
  | anyConvertNull {s : Store H} {f : Frame} :
      RefStep ⟨s, f, [.ref .null, .plain .anyConvertExtern]⟩ ⟨s, f, [.ref .null]⟩
  /-- `Step_pure/any.convert_extern-addr`. -/
  | anyConvertAddr {s : Store H} {f : Frame} (r : Ref) :
      RefStep ⟨s, f, [.ref (.extern r), .plain .anyConvertExtern]⟩ ⟨s, f, [.ref r]⟩

end Silmaril.Wasm.Execution.Core
