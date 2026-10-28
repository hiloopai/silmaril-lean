module

public import Silmaril.Machine.CallingConvention.Wasm
public import Silmaril.X86.Basic

/-!
# System V AMD64 as a `Machine.CallingConvention`

`sysv64` is the integer part of the System V AMD64 psABI, as data:

* integer arguments in `rdi, rsi, rdx, rcx, r8, r9`, in that order;
* integer results in `rax`, then `rdx`;
* callee-saved `rbx, rbp, r12, r13, r14, r15` (and `rsp`, whose discipline is
  `linkSize = 8` rather than `calleeSaved`);
* `rsp ≡ 0 (mod 16)` immediately **before** a `call`, hence
  `rsp ≡ 8 (mod 16)` **at function entry**, because the call pushed eight
  bytes of return address;
* a 128-byte red zone below `rsp` that a leaf function may use without
  adjusting `rsp`;
* no shadow space (that is Win64);
* the return address at `[rsp]` on entry, consumed by `ret`, so `rsp` at the
  `ret` is the entry `rsp` and `rsp` *after* the `ret` is entry `rsp + 8`.

`sysv64_wellFormed` checks these against `CallingConvention.WellFormed` by
`decide`; in particular it checks that `rsp` is in neither the argument list
nor the callee-saved list, and that `linkSize % stackAlign = entryResidue`,
i.e. that `8 ≡ 8 (mod 16)` is the entry residue the call produces.

## Provenance

`sysv64`, `sysv64_wellFormed` and the lemmas about them originate in PR #887
(`x86/sha256-contract`, #882 Track 2b) and are reproduced here **verbatim**, so
that whichever of #887 and #879 merges second sees identical content. The
`sysv64Wasm` section at the end is #879's additive extension: it reuses
`sysv64` as its integer half and adds only the fields
`Silmaril.Machine.WasmConvention` introduces.

## Why this lives here and not in `Silmaril/Machine/`

`Silmaril/Machine/CallingConvention.lean` mentions no instruction set: its
register type is a parameter. Putting `sysv64` there would make every
`Silmaril.Machine` module transitively depend on `Silmaril.X86.Basic`, and
would have to be undone as soon as `aapcs64` and `lp64` arrive. Per-ISA
instances therefore live under the ISA. #882 asked for the structure and the
instance together; this is the same content, split along the dependency.

## Scope

This is a description of an ABI, not a claim about any binary. Nothing here
says that a particular `.text` image honours `sysv64`; that is a theorem about
a program (#704), and `Silmaril/Crypto/X86/Sha256O0.lean` states the first one.

Varargs (`al` = number of vector registers used), struct passing by `MEMORY`
class, `x87` argument and return classes, and the 16-byte alignment of
`__m128` arguments are **out of scope**: the `CallingConvention` record covers
the `INTEGER` class only. `sysv64Wasm` adds the `SSE` class in the shape the
Wasm backend would need it (`xmm0…xmm7` for arguments, `xmm0`, `xmm1` for
results, none callee-saved), together with the `i32` extension rule and the
multi-value rule. The x86-64 machine model in this repository has no
floating-point registers, so `Xmm` below is ABI data only: no instruction
semantics mention it, and the Wasm backend rejects `f32`/`f64` long before any
register allocation.
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.Machine (CallingConvention ReturnAddress FloatConvention IntExt MultiValue
  WasmConvention)

/-- The System V AMD64 integer calling convention. -/
def sysv64 : CallingConvention Reg where
  intArgRegs := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
  intRetRegs := [.rax, .rdx]
  calleeSaved := [.rbx, .rbp, .r12, .r13, .r14, .r15]
  stackPointer := .rsp
  stackAlign := 16
  entryResidue := 8
  redZone := 128
  shadowSpace := 0
  stackArgSlot := 8
  returnAddress := .onStack 0
  linkSize := 8

theorem sysv64_wellFormed : sysv64.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

@[simp] theorem sysv64_maxIntArgs : sysv64.maxIntArgs = 6 := rfl

@[simp] theorem sysv64_redZone : sysv64.redZone = 128 := rfl

@[simp] theorem sysv64_linkSize : sysv64.linkSize = 8 := rfl

/-- At entry, `rsp ≡ 8 (mod 16)`. -/
theorem sysv64_entryAligned_iff (sp : Nat) : sysv64.EntryAligned sp ↔ sp % 16 = 8 :=
  Iff.rfl

/-- A 16-byte-aligned stack pointer at the call site becomes an entry stack
pointer congruent to 8, after the call has pushed the return address. -/
theorem sysv64_entryAligned_of_callAligned {sp : Nat} (h : sysv64.CallAligned sp)
    (hle : 8 ≤ sp) : sysv64.EntryAligned (sp - 8) := by
  have hsp : sp % 16 = 0 := h
  show (sp - 8) % 16 = 8
  omega

theorem sysv64_calleeSaved :
    sysv64.calleeSaved = [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] := rfl

/-- `rsp` is not among the registers `Preserved` talks about; the stack
discipline is stated separately. -/
theorem sysv64_rsp_not_calleeSaved : Reg.rsp ∉ sysv64.calleeSaved := by decide

/-- The six registers a System V callee must give back. -/
theorem sysv64_mem_calleeSaved (r : Reg) :
    r ∈ sysv64.calleeSaved ↔
      r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 := by
  cases r <;> decide

/-! ## The Wasm extension (#879)

`sysv64Wasm` is `sysv64` with the three fields a WebAssembly backend needs on
top of the `INTEGER` class. Its integer half is `sysv64` itself
(`sysv64Wasm_toCallingConvention`), so nothing stated about `sysv64` has to be
restated.
-/

/-- The System V AMD64 SSE registers, as ABI data. The x86-64 machine model in
this repository has no floating-point state, so these name argument and result
locations without any instruction referring to them. -/
inductive Xmm where
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  deriving DecidableEq, Repr

/-- The System V AMD64 `SSE` class: the first eight floating-point and vector
arguments in `xmm0…xmm7`, results in `xmm0` and `xmm1`, and none of the
sixteen callee-saved. -/
def sysv64Float : FloatConvention Xmm where
  floatArgRegs := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]
  floatRetRegs := [.xmm0, .xmm1]
  calleeSavedFloat := []

/-- System V AMD64 as a WebAssembly calling convention: `sysv64` for the
integers, `sysv64Float` for the floats, `i32` values **zero**-extended into
their 64-bit registers (System V leaves the high half of a 32-bit result
unspecified and the psABI's own compilers write zeros, which is what
`Wasm.Compile.ResultExt.zero` does), and a second result register `rdx`, so a
two-result Wasm function needs no indirect result area. Results beyond two go
through an `sret` pointer with eight-byte slots. -/
def sysv64Wasm : WasmConvention Reg Xmm where
  toCallingConvention := sysv64
  float := sysv64Float
  argExt := .zero
  retExt := .zero
  multiValue := .sretPointer 8

/-- The integer half of `sysv64Wasm` is exactly #887's `sysv64`. -/
@[simp] theorem sysv64Wasm_toCallingConvention :
    sysv64Wasm.toCallingConvention = sysv64 := rfl

theorem sysv64Wasm_wellFormed : sysv64Wasm.WasmWellFormed where
  base := sysv64_wellFormed
  float := by refine ⟨?_, ?_, ?_⟩ <;> decide
  sret_pos := by rintro n ⟨rfl⟩; decide

/-- System V returns an `i32` zero-extended, matching
`Wasm.Compile.ResultExt.zero`. -/
@[simp] theorem sysv64Wasm_retExt : sysv64Wasm.retExt = IntExt.zero := rfl

/-- System V places no requirement on the high half of a 32-bit *argument*
either, so the backend may zero it. -/
@[simp] theorem sysv64Wasm_argExt : sysv64Wasm.argExt = IntExt.zero := rfl

@[simp] theorem sysv64Wasm_maxIntArgs : sysv64Wasm.maxIntArgs = 6 := rfl

@[simp] theorem sysv64Wasm_maxIntRets : sysv64Wasm.maxIntRets = 2 := rfl

/-- Six integer arguments fit in registers, and more fit on the stack. -/
theorem sysv64Wasm_argsFit (n : Nat) : sysv64Wasm.ArgsFit n := .inr (by decide)

/-- Every Wasm result arity is within the convention: up to two in registers,
the rest through the indirect result area. -/
theorem sysv64Wasm_resultsFit (n : Nat) : sysv64Wasm.ResultsFit n :=
  .inr (by decide)

/-- Eight floating-point arguments in registers. -/
@[simp] theorem sysv64Wasm_maxFloatArgs : sysv64Wasm.float.maxFloatArgs = 8 := rfl

end Silmaril.X86
