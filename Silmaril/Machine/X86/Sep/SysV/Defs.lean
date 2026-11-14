module

public import Silmaril.Machine.X86.Sep.Spec.Defs
public import Silmaril.X86.CallingConvention

/-!
# System V function specifications in separation logic

`FnSpec` is the **shared interface** for function contracts: ELF verification proves
functions against it, and the verified linker states translation-unit imports and
exports with it. It is kept small on purpose; everything ABI-specific is in the fixed
template `SysVPre`/`SysVPost`, not in the record.

A spec has

* `Arg`: the logical arguments (ghost variables), shared by pre- and postcondition;
* `args x`: the integer argument values, passed in `rdi, rsi, rdx, rcx, r8, r9` in order
  (at most six are used; stack-passed arguments are not modelled yet);
* `stack`: the **stack budget**, the number of bytes below the entry `rsp` the function may
  use — its frame, the part of the 128-byte red zone it touches, and everything its callees
  need, including the eight bytes each `call` pushes;
* `pre x`, `post x v`: the user pre- and postcondition (buffers, …); `v` is the final `rax`.

**The template** (DESIGN §3). At entry, the function owns `rip ↦ entry`, `rsp ↦ sp`, the
nine caller-saved registers (`SysVRegs`: the arguments in the argument registers, the rest
with unknown values), the flags, the return-address slot `wordPt sp ret` and the budget
`blockAny (sp - stack) stack`. It returns with `rip ↦ ret`, `rsp ↦ sp + 8`, `rax ↦ v`, the
other caller-saved registers and the flags unknown (`SysVRet`), and the budget plus the
return slot as unknown bytes. **Callee-saved registers (`rbx, rbp, r12–r15`) are not in the
template**, so the caller's frame carries them across the call unchanged
(`calleeSaved_by_frame`). Neither is anything else the caller owns.

`FnSpec.SatWith A C entry S`: the code `C` at `entry` meets `S` for every entry stack pointer
satisfying `A` that leaves room for the budget. `FnSpec.Sat` takes `A` = the System V entry
alignment `rsp ≡ 8 (mod 16)`. Code that is only ever called from non-conforming call sites
can be specified with a weaker `A` (`fun _ => True`).

`FnSpec.Sub S T` (`S ⊑ T`): every function meeting `S` meets `T` (`FnSpec.SatWith.mono`).
-/

@[expose] public section

namespace Silmaril.Machine.X86.Sep

open Silmaril.X86 (MState Word Reg)

/-- The System V integer argument registers, in order. -/
def argRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- The caller-saved registers that are not argument registers. -/
def scratchRegs : List Reg := [.rax, .r10, .r11]

/-- The callee-saved registers (`sysv64.calleeSaved`). -/
def calleeSavedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The caller-saved registers other than `rax`, owned with unknown values after a call. -/
def clobberedRegs : List Reg := [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- Registers holding the given values in order; registers past the values are owned with
unknown values. -/
def regsWith : List Reg → List Word → SProp
  | [], _ => emp
  | r :: rs, v :: vs => regPt r v ∗ regsWith rs vs
  | r :: rs, [] => regAny r ∗ regsWith rs []

/-- Owned registers with unknown values. -/
def regsAny (rs : List Reg) : SProp := regsWith rs []

/-- The caller-saved registers at entry: the arguments, then unknown values. -/
def SysVRegs (args : List Word) : SProp := regsWith argRegs args ∗ regsAny scratchRegs

/-- The caller-saved registers at return: `rax ↦ v` and the rest unknown. -/
def SysVRet (v : Word) : SProp := regPt .rax v ∗ regsAny clobberedRegs

/-- **A System V function specification** (see the module documentation). -/
structure FnSpec where
  /-- Logical arguments. -/
  Arg : Type
  /-- Integer argument values (`rdi, rsi, rdx, rcx, r8, r9`). -/
  args : Arg → List Word
  /-- Stack budget below the entry `rsp`, including red zone use and callees. -/
  stack : Nat
  /-- User precondition. -/
  pre : Arg → SProp
  /-- User postcondition, given the final `rax`. -/
  post : Arg → Word → SProp

namespace FnSpec

/-- The ABI part of the precondition: `rip`, `rsp`, the caller-saved registers, the flags,
the return-address slot and the stack budget. -/
def SysVEntry (S : FnSpec) (x : S.Arg) (entry sp ret : Word) : SProp :=
  ripPt entry ∗ regPt .rsp sp ∗ SysVRegs (S.args x) ∗ flagsAny ∗ wordPt sp.toNat ret ∗
    blockAny (sp.toNat - S.stack) S.stack

/-- The ABI part of the postcondition, with final `rax = v`. -/
def SysVExit (S : FnSpec) (sp ret v : Word) : SProp :=
  ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ SysVRet v ∗ flagsAny ∗
    blockAny (sp.toNat - S.stack) (S.stack + 8)

/-- **The System V precondition template.** -/
def SysVPre (S : FnSpec) (x : S.Arg) (entry sp ret : Word) : SProp :=
  S.SysVEntry x entry sp ret ∗ S.pre x

/-- **The System V postcondition template.** -/
def SysVPost (S : FnSpec) (x : S.Arg) (sp ret : Word) : SProp :=
  sexists fun v => S.SysVExit sp ret v ∗ S.post x v

/-- The System V entry alignment, `rsp ≡ 8 (mod 16)`. -/
def EntryAligned (sp : Word) : Prop := sp.toNat % 16 = 8

/-- The code `C`, entered at `entry`, meets `S` from every entry stack pointer satisfying `A`
that leaves room for the budget. -/
def SatWith (A : Word → Prop) (C : SProp) (entry : Word) (S : FnSpec) : Prop :=
  ∀ (x : S.Arg) (sp ret : Word), A sp → S.stack ≤ sp.toNat →
    SPEC C (S.SysVPre x entry sp ret) (S.SysVPost x sp ret)

/-- **The code `C` at `entry` meets `S` under the System V ABI.** -/
def Sat (C : SProp) (entry : Word) (S : FnSpec) : Prop := SatWith EntryAligned C entry S

/-- `S ⊑ T`: a function meeting `S` meets `T`. Each `T` call is an `S` call with the same
argument registers, `T`'s precondition splits into `S`'s and a frame `R`, and `S`'s
postcondition with `R` gives `T`'s; `T` may grant a larger stack budget. -/
structure Sub (S T : FnSpec) : Prop where
  stack : S.stack ≤ T.stack
  arg : ∀ y : T.Arg, ∃ x : S.Arg, S.args x = T.args y ∧
    ∃ R : SProp, (T.pre y ⊢ₛ S.pre x ∗ R) ∧ ∀ v, (S.post x v ∗ R ⊢ₛ T.post y v)

end FnSpec

end Silmaril.Machine.X86.Sep
