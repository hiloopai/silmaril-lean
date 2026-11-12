module

public import Silmaril.X86.Sep.Plan.Defs
public import Silmaril.X86.Sep.SysV.Defs
/-!
# `CSpec`: the System V author spec with frames, plans and XMM registers

`FnSpec` (`Sep/SysV`) is the integer author spec: at most
six word arguments in `rdi … r9`, one word result in `rax`, a constant stack budget, no XMM
registers. `CSpec` is the author spec for code that needs more (structs by value, varargs,
floating point, `Arg`-dependent stack budgets). It is stated over `XSProp` (`Sep/Xmm`, CP-9)
and its argument and result placement is the data of a `CallPlan`, usually computed by
`Silmaril.Machine.SystemV.Abi.plan` (`Silmaril.Machine.SystemV.Abi`), through the placement assertions of `Sep/Plan`
(CP-10a). There is **no classification of our own**.

* `CallShape`: a plan, the object bytes of each actual argument, and the hidden result pointer
  (`sret`, for an `indirect` result).
* `CSpec`: logical arguments `Arg`, a shape per argument, an `Arg`-dependent stack budget, and
  a pre- and postcondition that see the entry `Frame` (entry `rsp` and return address); the
  postcondition also sees the result object bytes (`[]` for `void`).
* **The template.** At entry (`EntryOf`) the callee owns `rip`, `rsp`, the flags, the return
  slot, the stack budget below `rsp`, and `ArgsIn`: the argument placement (`argsPt`), the
  hidden result pointer (`sretPt`), `al` for variadic calls (`alPt`), and **every other
  caller-saved register with an unknown value**: the GP registers of `callerSavedGp` not used
  by the plan (`unusedGp`), and the XMM registers 0-15 not used by the plan (`unusedX`). At
  exit (`ExitOf`) it owns `rip ↦ ret`, `rsp ↦ sp + 8`, the flags, the budget plus the return
  slot as unknown bytes, and `RetOut`: the result placement (`retPt`), the stack-argument
  areas as unknown bytes (the callee may clobber them), and every other caller-saved GP and
  XMM register with an unknown value. Callee-saved registers are not in the template; the
  caller's frame carries them, as for `FnSpec`.
* `CSpec.SatN M n C entry S` (step-indexed, partial correctness on any XMM machine `M`)
  and `CSpec.Sat` (every index): the code `C` at `entry` meets `S` from every aligned entry
  frame that leaves room for the budget.
* `CSpec.Sub S T`: every `T` call is an `S` call with the same shape and no larger budget,
  `T`'s precondition splits into `S`'s and a frame, and `S`'s postcondition with the frame
  gives `T`'s.
* `CSpec.ofPlan`: the shape computed by `Abi.plan` from object layouts. Its precondition
  records that planning succeeded and that each argument's bytes have the object's size.
* `FnSpec.toC`: the integer embedding (`intShape`: word arguments in the first
  `min 6 (args.length)` argument registers, a word result in `rax`).
* `XProgress`: a triple on an XMM machine that takes at least one step (used by the call
  rules to pay for the step index).

Theorems (`ccall_rule`, `cicall_rule`, `sat_toC_of_sat`, …) are in `Sep/CSpec/Thms.lean`.

Name hygiene: no declaration here is named after the ABI convention type, and
no `open` of the compiler's category namespace.
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (Reg XReg Word Byte)
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Sse9 (XState)
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.Machine.SystemV.Abi (Chunk Argument CallPlan Object Profile)

/-- **The data of one call**: the plan, the object bytes of each actual argument (in order),
and the hidden result pointer (exactly when the plan's result is `indirect`). -/
structure CallShape where
  plan : CallPlan
  bytes : List (List Byte)
  sret : Option Word

/-- **A System V function specification with plans, frames and XMM registers.** -/
structure CSpec where
  /-- Logical arguments (ghost variables). -/
  Arg : Type
  /-- The call shape of each call. -/
  shape : Arg → CallShape
  /-- Stack budget below the entry `rsp` (frame, red-zone use and callees). -/
  stack : Arg → Nat
  /-- User precondition, given the entry frame. -/
  pre : Arg → Frame → XSProp
  /-- User postcondition, given the entry frame and the result object bytes. -/
  post : Arg → Frame → List Byte → XSProp

/-- **Progress on an XMM machine**: a total triple that takes at least one step. -/
def XProgress (M : Silmaril.X86.SegVC.Isa XState) (P R : XSProp) : Prop :=
  ∀ (F : XSProp) (x : XState), (P ∗ₓ F) (toXFrag x) →
    ∃ k x', run M.step (k + 1) x = some x' ∧ (R ∗ₓ F) (toXFrag x')

namespace CSpec

/-! ## Registers of the template -/

/-- The caller-saved GP registers: the six argument registers, then `rax, r10, r11`. -/
def callerSavedGp : List Reg := argRegs ++ scratchRegs

/-- The XMM registers 0-15 (all caller-saved). -/
def allXRegs : List XReg := (List.range 16).map xregOfIdx

/-- Owned XMM registers with unknown values. -/
def xmmsAny : List XReg → XSProp
  | [] => xemp
  | r :: rs => xmmAny r ∗ₓ xmmsAny rs

/-- The chunks of the register-passed arguments. -/
def regChunks (p : CallPlan) : List Chunk :=
  p.arguments.flatMap fun a => match a.stackOffset with
    | none => a.chunks
    | some _ => []

/-- GP registers the entry placement owns: argument chunks, `rdi` for an indirect result,
`rax` for a variadic call. -/
def usedGp (p : CallPlan) : List Reg :=
  gpRegs (regChunks p) ++
    (match p.result with
      | .indirect .. => [.rdi]
      | _ => []) ++
    (match p.variadicAL with
      | some _ => [.rax]
      | none => [])

/-- XMM registers the entry placement owns. -/
def usedX (p : CallPlan) : List XReg := xRegs (regChunks p)

/-- Caller-saved GP registers not used at entry. -/
def unusedGp (p : CallPlan) : List Reg := callerSavedGp.filter fun r => decide (r ∉ usedGp p)

/-- XMM registers not used at entry. -/
def unusedX (p : CallPlan) : List XReg := allXRegs.filter fun r => decide (r ∉ usedX p)

/-- GP registers the result placement owns. -/
def resultGp : Silmaril.Machine.SystemV.Abi.Return → List Reg
  | .void => []
  | .direct cs => gpRegs cs
  | .indirect .. => [.rax]

/-- XMM registers the result placement owns. -/
def resultX : Silmaril.Machine.SystemV.Abi.Return → List XReg
  | .direct cs => xRegs cs
  | _ => []

/-- Caller-saved GP registers not used by the result. -/
def otherGp (p : CallPlan) : List Reg :=
  callerSavedGp.filter fun r => decide (r ∉ resultGp p.result)

/-- XMM registers not used by the result. -/
def otherX (p : CallPlan) : List XReg := allXRegs.filter fun r => decide (r ∉ resultX p.result)

/-- The stack-argument areas as unknown bytes (what the caller gets back). -/
def stackArgsAnyL (fr : Frame) : List Argument → List (List Byte) → XSProp
  | a :: as, b :: bs =>
      (match a.stackOffset with
        | none => xemp
        | some off => ↑ₓ(blockAny (fr.sp.toNat + 8 + off) b.length)) ∗ₓ stackArgsAnyL fr as bs
  | _, _ => xemp

/-! ## The template -/

/-- **The argument registers, stack arguments and other caller-saved registers at entry.** -/
def ArgsIn (sh : CallShape) (fr : Frame) : XSProp :=
  argsPt fr sh.plan sh.bytes ∗ₓ sretPt sh.plan.result sh.sret ∗ₓ alPt sh.plan ∗ₓ
    ↑ₓ(regsAny (unusedGp sh.plan)) ∗ₓ xmmsAny (unusedX sh.plan)

/-- **The result, stack-argument areas and other caller-saved registers at exit.** -/
def RetOut (sh : CallShape) (fr : Frame) (rb : List Byte) : XSProp :=
  retPt sh.plan.result sh.sret rb ∗ₓ stackArgsAnyL fr sh.plan.arguments sh.bytes ∗ₓ
    ↑ₓ(regsAny (otherGp sh.plan)) ∗ₓ xmmsAny (otherX sh.plan)

/-- The control part at entry: `rip`, `rsp`, flags, return slot and stack budget. -/
def CtlIn (stack : Nat) (entry : Word) (fr : Frame) : SProp :=
  ripPt entry ∗ regPt .rsp fr.sp ∗ flagsAny ∗ wordPt fr.sp.toNat fr.ret ∗
    blockAny (fr.sp.toNat - stack) stack

/-- The control part at exit: `rip ↦ ret`, `rsp ↦ sp + 8`, flags, budget and return slot. -/
def CtlOut (stack : Nat) (fr : Frame) : SProp :=
  ripPt fr.ret ∗ regPt .rsp (fr.sp + 8#64) ∗ flagsAny ∗
    blockAny (fr.sp.toNat - stack) (stack + 8)

/-- The entry template of a shape and budget. -/
def EntryOf (sh : CallShape) (stack : Nat) (entry : Word) (fr : Frame) : XSProp :=
  ↑ₓ(CtlIn stack entry fr) ∗ₓ ArgsIn sh fr

/-- The exit template of a shape and budget, with result bytes `rb`. -/
def ExitOf (sh : CallShape) (stack : Nat) (fr : Frame) (rb : List Byte) : XSProp :=
  ↑ₓ(CtlOut stack fr) ∗ₓ RetOut sh fr rb

/-- The entry template of `S`. -/
def Entry (S : CSpec) (x : S.Arg) (entry : Word) (fr : Frame) : XSProp :=
  EntryOf (S.shape x) (S.stack x) entry fr

/-- The exit template of `S`. -/
def Exit (S : CSpec) (x : S.Arg) (fr : Frame) (rb : List Byte) : XSProp :=
  ExitOf (S.shape x) (S.stack x) fr rb

/-- **The precondition**: template and user precondition. -/
def Pre (S : CSpec) (x : S.Arg) (entry : Word) (fr : Frame) : XSProp :=
  S.Entry x entry fr ∗ₓ S.pre x fr

/-- **The postcondition**: for some result bytes, template and user postcondition. -/
def Post (S : CSpec) (x : S.Arg) (fr : Frame) : XSProp :=
  xsexists fun rb => S.Exit x fr rb ∗ₓ S.post x fr rb

/-! ## Satisfaction and refinement -/

/-- **The code `C` at `entry` meets `S` for `n` steps** on the XMM machine `step`, from every
System V-aligned entry frame with room for the budget. -/
def SatN (M : Silmaril.X86.SegVC.Isa XState) (n : Nat) (C : XSProp) (entry : Word) (S : CSpec) :
    Prop :=
  ∀ (x : S.Arg) (fr : Frame), FnSpec.EntryAligned fr.sp → S.stack x ≤ fr.sp.toNat →
    XSTriple M n (C ∗ₓ S.Pre x entry fr) (C ∗ₓ S.Post x fr)

/-- **The code `C` at `entry` meets `S`** (at every step index). -/
def Sat (M : Silmaril.X86.SegVC.Isa XState) (C : XSProp) (entry : Word) (S : CSpec) : Prop :=
  ∀ n, SatN M n C entry S

/-- `S ⊑ T`: a function meeting `S` meets `T`. Each `T` call is an `S` call with the same
shape and no larger budget; per frame, `T`'s precondition splits into `S`'s and a frame `R`,
and `S`'s postcondition with `R` gives `T`'s. -/
structure Sub (S T : CSpec) : Prop where
  arg : ∀ y : T.Arg, ∃ x : S.Arg, S.shape x = T.shape y ∧ S.stack x ≤ T.stack y ∧
    ∀ fr : Frame, ∃ R : XSProp, (T.pre y fr ⊢ₓ (S.pre x fr ∗ₓ R)) ∧
      ∀ rb, ((S.post x fr rb ∗ₓ R) ⊢ₓ T.post y fr rb)

/-! ## Specs from `Abi.plan` -/

/-- The plan used when planning fails (with `ofPlan`'s precondition then `False`). -/
def failPlan : CallPlan := ⟨[], .void, 0, 16, 0, 0, none⟩

/-- The planned call, or `failPlan`. -/
def planOr : Except String CallPlan → CallPlan
  | .ok p => p
  | .error _ => failPlan

/-- **A `CSpec` from object layouts**, planned by `Silmaril.Machine.SystemV.Abi.plan`
(`named` named arguments; `variadic` for `...` prototypes). The precondition adds that
planning succeeded and that every argument's bytes have its object's size. -/
def ofPlan (profile : Profile) (Arg : Type) (objs : Arg → List Object)
    (res : Arg → Option Object) (named : Nat) (variadic : Bool)
    (bytes : Arg → List (List Byte)) (sret : Arg → Option Word) (stack : Arg → Nat)
    (pre : Arg → Frame → XSProp) (post : Arg → Frame → List Byte → XSProp) : CSpec where
  Arg := Arg
  shape x :=
    ⟨planOr (Silmaril.Machine.SystemV.Abi.plan profile (objs x) (res x) named variadic),
      bytes x, sret x⟩
  stack := stack
  pre x fr :=
    ⌜(Silmaril.Machine.SystemV.Abi.plan profile (objs x) (res x) named variadic).toOption.isSome
        = true ∧
      List.Forall₂ (fun (b : List Byte) (o : Object) => b.length = o.size) (bytes x) (objs x)⌝ₓ
      ∗ₓ pre x fr
  post := post

/-! ## The integer fragment -/

/-- The layout of a 64-bit INTEGER object. -/
def int64Object : Object := ⟨8, 8, [.integer]⟩

/-- A word argument in register `r`. -/
def intArgument (r : Reg) : Argument := ⟨int64Object, [⟨0, 8, .gp r⟩], none⟩

/-- The eight little-endian bytes of a word. -/
def wordBytes (w : Word) : List Byte := byteSlice w 0 8

/-- The plan of a call with word arguments `args` (the first six, in `rdi … r9`) and a word
result in `rax`. -/
def intPlan (args : List Word) : CallPlan :=
  ⟨(argRegs.zip args).map (fun p => intArgument p.1), .direct [⟨0, 8, .gp .rax⟩], 0, 16,
    (argRegs.zip args).length, 0, none⟩

/-- The shape of a call with word arguments `args`. -/
def intShape (args : List Word) : CallShape :=
  ⟨intPlan args, (argRegs.zip args).map (fun p => wordBytes p.2), none⟩

end CSpec

/-- **The integer embedding**: an `FnSpec` as a `CSpec` (same budget, word arguments and a
word result; the user assertions do not mention XMM registers). -/
def FnSpec.toC (S : FnSpec) : CSpec where
  Arg := S.Arg
  shape x := CSpec.intShape (S.args x)
  stack _ := S.stack
  pre x _ := ↑ₓ(S.pre x)
  post x _ rb := xsexists fun v => ⌜rb = CSpec.wordBytes v⌝ₓ ∗ₓ ↑ₓ(S.post x v)

end Silmaril.X86.Sep
