module

public import Silmaril.X86.AbiFunction.Defs
public import Silmaril.X86.FnContract.SystemV.Thms
meta import Silmaril.X86.AbiFunction.Defs
/-!
# `AbiFunction`: placement and the System V judgements

* `placedIn_bytes`: a placed body assembles, and the region holds its bytes at the offset.
* `SysV.toFnContract`: the register-level judgement as a total `FnContract` on the open
  machine (so it composes with the segment VC generator through `FnContract.toCall`).
* `SysV.toRealizes`: the register-level judgement gives the C-level one
  (`FnContract.toRealizes`), given that the postcondition puts the C result in `rax` and the
  footprint is inside the C-level `writes`.
-/

@[expose] public section

namespace Silmaril.X86.AbiFunction

open Silmaril.X86 (MState Byte)

/-- A placed body assembles, and the region holds its bytes at the function's offset. -/
theorem placedIn_bytes {Abi : Type} {f : AbiFunction Abi} {σ : String → Option Nat}
    {p : Placement} (h : f.placedIn σ p = true) :
    ∃ bs, f.bytesAt p.addr σ = some bs ∧ (p.code.drop p.off).take bs.length = bs := by
  unfold placedIn at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  split at h
  · rename_i bs hb
    exact ⟨bs, hb, by simpa using h⟩
  · cases h

namespace SysV

variable {f : AbiFunction Link.Abi.Conv} {σ : String → Option Nat} {p : Placement}
  {footprint : MState → Nat → Prop} {post : MState → MState → Prop}

/-- The judgement as a total System V `FnContract` on the open machine. -/
def toFnContract (h : SysV f σ p footprint post) : FnContract Open.isa :=
  ⟨spec p footprint post, h.total⟩

/-- **Register level to C level.** A System V contract whose postcondition puts the C result
in `rax` and whose footprint lies inside `writes` realizes the C function. -/
theorem toRealizes (h : SysV f σ p footprint post)
    (result : Silmaril.C.Api.Arguments f.sig.arguments →
      Silmaril.C.Api.ReturnValue f.sig.result)
    (writes : Silmaril.C.Api.Arguments f.sig.arguments → Silmaril.Machine.SystemV.Footprint)
    (value : ∀ arguments call final, Silmaril.C.Api.SysV.Entry f.sig arguments call →
      domain p arguments call → post call.initial final →
        Silmaril.C.Api.SysV.ResultAt final f.sig.result (result arguments))
    (fp : ∀ arguments call a, Silmaril.C.Api.SysV.Entry f.sig arguments call →
      domain p arguments call → footprint call.initial a → writes arguments a) :
    SysVRealizes f σ p result writes where
  abi := h.abi
  placed := h.placed
  realizes := FnContract.toRealizes h.toFnContract f.sig result writes (domain p)
    (fun _ _ he hd => ⟨hd.1, he.pc.trans hd.2⟩) value fp

end SysV

/-! ## Assembler regression checks against GNU as

One-line listings and the bytes GNU as 2.42 (`as --64`) assembles them to, for the `Ext9`
forms of `encodeNew` (`adc`/`sbb`, `imul $imm`, `test $imm`, `rep ret` as `.byte 0xf3,0xc3`),
one-operand `mul`, `cmpb $imm, m8` and perlasm's `a+b` displacements and immediates. A corpus
of 460 such lines (every register, SIB and `rbp`/`r13`/`rsp`/`r12` base, imm8/imm32
boundaries) agreed except for `adc`/`sbb $imm32` into `eax`/`rax`, where GNU as uses the
accumulator form `15 id`/`1D id` that `Ext9` does not decode; those are rejected. `test $imm`
into `eax`/`rax` is GNU's accumulator form `A9 id` (`Ext`'s `testA`). Raw `.byte` lines are
accepted only when `Open9.decode` reads them as whole instructions that re-encode to the same
bytes. Compiled evaluation (`#guard`), not proof. -/

/-- The bytes of a one-line listing at address 0, if it parses and assembles. -/
def lineBytes (l : String) : Option (List Nat) :=
  match ofGccS Silmaril.X86.Link.Abi.Conv.sysv64 ⟨[], none⟩ "f"
      ("f:\n\t" ++ l ++ "\n.size f,.-f\n") with
  | .ok f => (f.bytesAt 0 noSymbols).map (·.map BitVec.toNat)
  | .error _ => none

#guard lineBytes "adcq %r15,%rbp" == some [0x4c, 0x11, 0xfd]
#guard lineBytes "adcq 8(%rsi,%rcx,8),%r9" == some [0x4c, 0x13, 0x4c, 0xce, 0x08]
#guard lineBytes "adcq $0,%r12" == some [0x49, 0x83, 0xd4, 0x00]
#guard lineBytes "adcl $-129,%r12d" == some [0x41, 0x81, 0xd4, 0x7f, 0xff, 0xff, 0xff]
#guard lineBytes "sbbq %r15,%rbp" == some [0x4c, 0x19, 0xfd]
#guard lineBytes "sbbl (%rbp),%r9d" == some [0x44, 0x1b, 0x4d, 0x00]
#guard lineBytes "sbbq $0x1000,8(%rsp)" == some [0x48, 0x81, 0x5c, 0x24, 0x08, 0x00, 0x10, 0x00, 0x00]
#guard lineBytes "imulq $19,8(%rsi),%rbx" == some [0x48, 0x6b, 0x5e, 0x08, 0x13]
#guard lineBytes "imulq $121666,(%r13),%rcx" == some [0x49, 0x69, 0x4d, 0x00, 0x42, 0xdb, 0x01, 0x00]
#guard lineBytes "imull $-1,8(%rsi),%ebx" == some [0x6b, 0x5e, 0x08, 0xff]
#guard lineBytes "mulq 16(%r12)" == some [0x49, 0xf7, 0x64, 0x24, 0x10]
#guard lineBytes "mull %r10d" == some [0x41, 0xf7, 0xe2]
#guard lineBytes "adcl $127,%eax" == some [0x83, 0xd0, 0x7f]
#guard lineBytes "sbbq $1,%r12" == some [0x49, 0x83, 0xdc, 0x01]
#guard lineBytes "adcq $0x1000,%rax" == none
#guard lineBytes "sbbl $128,%eax" == none
#guard lineBytes "testl $536870912,%r11d" == some [0x41, 0xf7, 0xc3, 0x00, 0x00, 0x00, 0x20]
#guard lineBytes "testl $512,%r10d" == some [0x41, 0xf7, 0xc2, 0x00, 0x02, 0x00, 0x00]
#guard lineBytes "testq $-2,(%rdi)" == some [0x48, 0xf7, 0x07, 0xfe, 0xff, 0xff, 0xff]
#guard lineBytes "testl $1,%eax" == some [0xa9, 0x01, 0x00, 0x00, 0x00]
#guard lineBytes "testq $256,%rax" == some [0x48, 0xa9, 0x00, 0x01, 0x00, 0x00]
#guard lineBytes "testl $7,8(%rsp,%rcx,4)" == some [0xf7, 0x44, 0x8c, 0x08, 0x07, 0x00, 0x00, 0x00]
#guard lineBytes "cmpb $0,3(%rbp)" == some [0x80, 0x7d, 0x03, 0x00]
#guard lineBytes "cmpb $-1,(%r12)" == some [0x41, 0x80, 0x3c, 0x24, 0xff]
#guard lineBytes "movq %rdi,64+0(%rsp)" == some [0x48, 0x89, 0x7c, 0x24, 0x40]
#guard lineBytes "subq $64+32,%rsp" == some [0x48, 0x83, 0xec, 0x60]
#guard lineBytes "movq -48(%rsi),%r15" == some [0x4c, 0x8b, 0x7e, 0xd0]
#guard lineBytes "leaq (%rsi),%rsp" == some [0x48, 0x8d, 0x26]
#guard lineBytes ".byte 0xf3,0xc3" == some [0xf3, 0xc3]
#guard lineBytes ".byte 0xf3" == none
#guard lineBytes ".byte 0xf3,0x48,0xc3" == none
#guard lineBytes ".word 0xc3" == none

end Silmaril.X86.AbiFunction
