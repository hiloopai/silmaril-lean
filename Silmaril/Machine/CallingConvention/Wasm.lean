module

public import Silmaril.Machine.CallingConvention

/-!
# The Wasm-specific half of a calling convention

`Silmaril.Machine.CallingConvention` (from #887) records the **integer** part of
a procedure-call ABI: argument and result registers, callee-saved registers,
stack alignment, red zone, shadow space, and where the return address lives.
It deliberately stops there, because the three things a WebAssembly backend
additionally needs all require a notion of value type:

* **sub-word integers.** A Wasm `i32` occupies a 32-bit register slot inside a
  64-bit argument or result register. An ABI says how the other 32 bits are
  filled: System V AMD64 leaves the high half of a 32-bit result undefined
  and the compiler writes zeros (`IntExt.zero`), whereas RISC-V LP64 *requires*
  that a 32-bit value be held sign-extended into the 64-bit register
  (`IntExt.sign`). This is exactly the `ResultExt` that
  `Silmaril/Wasm/Compile/EndToEnd.lean` currently carries as a free parameter
  of `retWord`, with no ABI to pin it down. Here it becomes two `cc` fields,
  `argExt` and `retExt`.
* **floats and vectors.** `f32`, `f64` and `v128` travel in a different
  register bank from the integers: `xmm0…xmm7` under System V, `fa0…fa7`
  under RISC-V LP64D. The bank has its own type, so `FloatConvention` is
  parametric in a second register type `FReg` and `WasmConvention` pairs the
  two. Neither the x86-64 nor the RV64 machine model in this repository has
  floating-point registers yet, so no backend reads these fields; they are
  recorded because the ABI *is* this data, and because a later float backend
  must not have to reshape the record.
* **multi-value returns.** Wasm 1.1 functions may return several values. An
  ABI either has enough result registers (`MultiValue.registersOnly`, which
  caps the arity at `intRetRegs.length`) or passes a pointer to a
  caller-allocated result area in a hidden leading argument
  (`MultiValue.sretPointer`, the C `sret` convention). `ResultsFit` is the
  resulting arity side-condition.

## Why a separate structure and a separate file

`WasmConvention` **extends** `CallingConvention`; it does not replace or edit
it. `(wcc : WasmConvention Reg FReg).toCallingConvention` is the #887 record,
field for field, and every #887 field name projects through. Keeping the
addition in its own file means `Silmaril/Machine/CallingConvention.lean` is
byte-identical to #887's and the two pull requests cannot conflict there.

Nothing here mentions WebAssembly's syntax or `Silmaril.Wasm`: the fields are
stated over register types and `Nat`, so this module stays at the
`Silmaril.Machine` layer and adds no dependency. The bridge to
`Wasm.Compile.ResultExt` is a one-line function in the Wasm layer
(`Silmaril.Wasm.Compile.Implements`).

## Scope

As in #887, a convention is a *description*, not a claim about a binary.
`WasmWellFormed` adds the three nodup conditions the float bank needs and the
`sretPointer` slot-size condition; like `WellFormed` it is shallow enough to be
checked by `decide`.
-/

@[expose] public section

namespace Silmaril.Machine

universe u v

/-- How a value narrower than a register is widened to fill it. `zero` writes
zeros into the high bits (System V AMD64 for a 32-bit result); `sign` replicates
the sign bit (RISC-V LP64, which *requires* 32-bit values to be held
sign-extended in their 64-bit registers). -/
inductive IntExt where
  /-- Fill the high bits with zeros. -/
  | zero
  /-- Replicate the sign bit into the high bits. -/
  | sign
  deriving DecidableEq, Repr

/-- How results beyond the register result class are returned. -/
inductive MultiValue where
  /-- Only as many results as there are result registers; a higher arity is
  outside the convention. -/
  | registersOnly
  /-- Results that do not fit in registers are written to a caller-allocated
  area whose address arrives in a hidden leading pointer argument, each result
  occupying `slotSize` bytes. This is the C `sret` convention. -/
  | sretPointer (slotSize : Nat)
  deriving DecidableEq, Repr

/-- The floating-point and vector register bank of an ABI. Separate from
`CallingConvention` because it is indexed by a different register type. -/
structure FloatConvention (FReg : Type v) where
  /-- Floating-point and vector arguments, in order. -/
  floatArgRegs : List FReg
  /-- Floating-point and vector results, in order. -/
  floatRetRegs : List FReg
  /-- Floating-point registers the callee must restore before returning.
  Empty for both System V AMD64 and RISC-V LP64's *argument* registers; RISC-V
  `fs0…fs11` are callee-saved and are listed for `lp64d`. -/
  calleeSavedFloat : List FReg

namespace FloatConvention

variable {FReg : Type v} (fc : FloatConvention FReg)

/-- How many floating-point arguments go in registers. -/
def maxFloatArgs : Nat := fc.floatArgRegs.length

/-- The register holding floating-point argument `i`, if it is passed in one. -/
def floatArgReg? (i : Nat) : Option FReg := fc.floatArgRegs[i]?

/-- The register holding floating-point result `i`, if there is one. -/
def floatRetReg? (i : Nat) : Option FReg := fc.floatRetRegs[i]?

/-- The float bank's lists are sets. -/
structure WellFormed : Prop where
  /-- No register carries two different floating-point arguments. -/
  argRegs_nodup : fc.floatArgRegs.Nodup
  /-- No register carries two different floating-point results. -/
  retRegs_nodup : fc.floatRetRegs.Nodup
  /-- The callee-saved float list is a set. -/
  calleeSaved_nodup : fc.calleeSavedFloat.Nodup

end FloatConvention

/-- A `CallingConvention` together with everything a WebAssembly backend needs
on top of it: the float bank, the sub-word extension rules, and the
multi-value return rule. `toCallingConvention` is the #887 record unchanged. -/
structure WasmConvention (Reg : Type u) (FReg : Type v) extends CallingConvention Reg where
  /-- The floating-point and vector register bank. -/
  float : FloatConvention FReg
  /-- How an incoming 32-bit integer argument fills its 64-bit register. -/
  argExt : IntExt
  /-- How an outgoing 32-bit integer result fills its 64-bit register. This is
  the `ResultExt` of `Silmaril/Wasm/Compile/EndToEnd.lean`, here fixed by the
  ABI rather than left free. -/
  retExt : IntExt
  /-- How results beyond `intRetRegs` are returned. -/
  multiValue : MultiValue

namespace WasmConvention

variable {Reg : Type u} {FReg : Type v} (wcc : WasmConvention Reg FReg)

/-- How many integer results fit in registers. -/
def maxIntRets : Nat := wcc.intRetRegs.length

/-- A function returning `n` integer results is within the convention: either
they all fit in result registers, or the convention has an indirect result
area. -/
def ResultsFit (n : Nat) : Prop :=
  n ≤ wcc.maxIntRets ∨ wcc.multiValue ≠ .registersOnly

/-- A function taking `n` integer arguments is within the convention: either
they all fit in argument registers, or the convention passes the rest on the
stack, which it does exactly when it has a nonzero stack argument slot. -/
def ArgsFit (n : Nat) : Prop :=
  n ≤ wcc.maxIntArgs ∨ 0 < wcc.stackArgSlot

/-- Every convention accommodates a single integer result, the Wasm 1.0 case,
provided it has a result register at all. -/
theorem resultsFit_one (h : 0 < wcc.maxIntRets) : wcc.ResultsFit 1 := .inl h

/-- Nothing returned always fits. -/
theorem resultsFit_zero : wcc.ResultsFit 0 := .inl (Nat.zero_le _)

/-- The integer half is well formed, the float bank is well formed, and an
indirect result area has a positive slot size. -/
structure WasmWellFormed : Prop where
  /-- The #887 conditions on the integer half. -/
  base : wcc.toCallingConvention.WellFormed
  /-- The float bank's lists are sets. -/
  float : wcc.float.WellFormed
  /-- A result area with zero-sized slots would alias every result. -/
  sret_pos : ∀ n, wcc.multiValue = .sretPointer n → 0 < n

end WasmConvention

end Silmaril.Machine
