module

public import Silmaril.X86.Sse9.Defs
public import Silmaril.X86.Open9.Thms
import Silmaril.Proofs.X86.Sse9.Basic

/-!
# `Sse9`: what is proved

All statements are proved with the standard axioms (proofs in
`Silmaril/Proofs/X86/Sse9/Basic.lean`).

**Conservative extension.**
* `step_of_open9`: every `Open9` step is an `Sse9` step with the XMM file unchanged, whatever
  it holds. `run_of_open9`, `reaches_of_open9`: so is every `Open9` run.
* `step_cases`: every `Sse9` step is such a step, or (when `Open9` has no step) an SSE form
  fetched at the program counter.
* `extendsOpen9 : Open9.isa.Extends isa`: the extension along the lens `x ↦ x.m` (the XMM
  file is the frame), and `extendsOpen` from `Open.isa` by `Isa.Extends.trans`. So every
  generic transfer along `Isa.Extends` applies (`FnContract.lift`, `Spec.Strict.lift`,
  `Sep.Triple.lift`, …).
* `FnContract.toSse9`: **every `FnContract Open9.isa` is a contract of the XMM machine**, with
  the same precondition, footprint and postcondition, and the XMM file as a frame (stronger
  than `FnContract.lift extendsOpen9`, which does not mention the XMM file). So every callee
  proved on `Open`/`Open9` is usable from a caller that uses SSE moves.

**The SSE laws.**
* `isa`: the machine as a `SegVC.Isa XState` over the `Ext9` instructions (law:
  `Open9.step_of_listed` and `step_of_open9`).
* `step_of_listed_sse`, `step_of_fetch_sse`: a listed SSE form (`decodeL`) at the program
  counter of a loaded image that executes is one step.
* `exec_pxor_self`, `exec_xorps_self`: the zeroing idiom writes `0`.
* `decodeL_*`: example encodings gcc emits decode to the intended forms (`decide`), and
  `F2`, FS-prefixed and truncated SSE bytes are rejected.

What is **not** claimed: the SSE semantics is a handwritten model of the SDM, tested against
the host CPU outside this repository, not proved to match hardware. No block certificate kind
has SSE blocks; a function using these forms is certified only by stepping it with
`step_of_listed_sse`.
-/

@[expose] public section

namespace Silmaril.X86.Sse9

open Silmaril.X86 (State MState Word Byte XReg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)

/-! ## Conservative extension -/

/-- **Every `Open9` step is a step, with the XMM file unchanged.** -/
theorem step_of_open9 {x : XState} {m' : MState} (h : Open9.step x.m = some m') :
    step x = some ⟨m', x.xmm⟩ :=
  Silmaril.Proofs.X86.Sse9.step_of_open9 h

/-- **Every step is an `Open9` step with the XMM file unchanged, or an SSE step.** -/
theorem step_cases {x y : XState} (h : step x = some y) :
    (Open9.step x.m = some y.m ∧ y.xmm = x.xmm) ∨
      (Open9.step x.m = none ∧ ∃ i n, fetchSse x.m.memory x.m.core.rip.toNat = some (some (i, n)) ∧
        (exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 n)).toOption =
          some y) :=
  Silmaril.Proofs.X86.Sse9.step_cases h

/-- `Open9` runs are runs, with the XMM file unchanged. -/
theorem run_of_open9 (xs : XFile) (k : Nat) {a b : MState} (h : run Open9.step k a = some b) :
    run step k ⟨a, xs⟩ = some ⟨b, xs⟩ :=
  Silmaril.Proofs.X86.Sse9.run_of_open9 xs k h

theorem reaches_of_open9 (xs : XFile) {a b : MState} (h : Reaches Open9.step a b) :
    Reaches step ⟨a, xs⟩ ⟨b, xs⟩ :=
  Silmaril.Proofs.X86.Sse9.reaches_of_open9 xs h

/-! ## The SSE laws -/

/-- **The fetch form of the SSE law.** -/
theorem step_of_fetch_sse {x : XState} {l : Nat} {w : List Byte} {i : Instr} {c : State}
    {xs : XFile} {mem : Memory} (fetched : x.m.memory.fetchBytes x.m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) = .ok c xs mem) :
    step x = some ⟨⟨c, mem⟩, xs⟩ :=
  Silmaril.Proofs.X86.Sse9.step_of_fetch_sse fetched hdec hx

/-- **The SSE listing law.** -/
theorem step_of_listed_sse {x : XState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {xs : XFile} {mem : Memory} (hl : Loaded x.m.memory base code)
    (hrip : x.m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) = .ok c xs mem) :
    step x = some ⟨⟨c, mem⟩, xs⟩ :=
  Silmaril.Proofs.X86.Sse9.step_of_listed_sse hl hrip hfit hdec hx

/-- **The XMM machine as a segment-VC instance** over the `Ext9` instructions. -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa XState where
  Instr := Ext9.Instr
  instDecEq := inferInstance
  decode := Open9.decode
  exec := Ext9.exec
  core := fun x => x.m.core
  mem := fun x => x.m.memory
  upd := fun x c m => ⟨⟨c, m⟩, x.xmm⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ => step_of_open9 (Open9.step_of_listed hl hrip hfit hdec hx)

@[simp] theorem isa_step : isa.step = step := rfl

/-- **`Sse9` extends `Open9`**, along the lens `x ↦ x.m`: the XMM file is the frame. -/
@[reducible] def extendsOpen9 : Open9.isa.Extends isa where
  view x := x.m
  put x m := ⟨m, x.xmm⟩
  view_put _ _ := rfl
  put_put _ _ _ := rfl
  put_view _ := rfl
  core _ := rfl
  mem _ := rfl
  upd _ _ _ := rfl
  live _ _ := trivial
  step h := step_of_open9 h

/-- `Sse9` extends the open machine over `Ext8`. -/
@[reducible] def extendsOpen : Open.isa.Extends isa := Open9.extendsOpen.trans extendsOpen9

/-- `pxor %xmm, %xmm` zeroes the register (the zeroing idiom). -/
theorem exec_pxor_self (d : XReg) (s : State) (x : XFile) (mem : Memory) (next : Word) :
    exec (.pxor d (.reg d)) s x mem next =
      .ok { s with rip := next } (Silmaril.Machine.RegisterFile.write x d 0) mem := by
  simp [exec, binop, misaligned, readX]

/-- `xorps %xmm, %xmm` zeroes the register. -/
theorem exec_xorps_self (d : XReg) (s : State) (x : XFile) (mem : Memory) (next : Word) :
    exec (.xorps d (.reg d)) s x mem next =
      .ok { s with rip := next } (Silmaril.Machine.RegisterFile.write x d 0) mem := by
  simp [exec, binop, misaligned, readX]

/-! ## Decoder regressions (example encodings) -/

/-- `movups %xmm0, 0x84(%rbx)` (`0F 11 83 84000000`). -/
theorem decodeL_movups_store :
    decodeL [0x0F, 0x11, 0x83, 0x84, 0x00, 0x00, 0x00] =
      some (.store .ups (.mem (Silmaril.X86.Ext.Mem.ofReg .rbx none 0x84)) .xmm0, 7) := by
  decide

/-- `movdqu (%rsi), %xmm0` (`F3 0F 6F 06`). -/
theorem decodeL_movdqu_load :
    decodeL [0xF3, 0x0F, 0x6F, 0x06] =
      some (.load .dqu .xmm0 (.mem (Silmaril.X86.Ext.Mem.ofReg .rsi none 0)), 4) := by
  decide

/-- `movq %rdx, %xmm0` (`66 48 0F 6E C2`). -/
theorem decodeL_movq_to_xmm :
    decodeL [0x66, 0x48, 0x0F, 0x6E, 0xC2] = some (.movToX .q .xmm0 (.reg .rdx), 5) := by
  decide

/-- `pxor %xmm0, %xmm0` (`66 0F EF C0`). -/
theorem decodeL_pxor :
    decodeL [0x66, 0x0F, 0xEF, 0xC0] = some (.pxor .xmm0 (.reg .xmm0), 4) := by decide

/-- `punpcklqdq %xmm1, %xmm0` (`66 0F 6C C1`). -/
theorem decodeL_punpcklqdq :
    decodeL [0x66, 0x0F, 0x6C, 0xC1] = some (.punpcklqdq .xmm0 (.reg .xmm1), 4) := by decide

/-- `movsd (%rdi), %xmm2` (`F2 0F 10 17`) is not in the subset. -/
theorem decodeL_movsd_none : decodeL [0xF2, 0x0F, 0x10, 0x17] = none := by decide

/-- The FS override is refused: `movups %fs:(%rax), %xmm0` (`64 0F 10 00`). -/
theorem decodeL_fs_none : decodeL [0x64, 0x0F, 0x10, 0x00] = none := by decide

/-- A truncated form is not a listing: `0F 11`. -/
theorem decodeL_truncated_none : decodeL [0x0F, 0x11] = none := by decide

end Silmaril.X86.Sse9

namespace Silmaril.X86.FnContract

open Silmaril.X86.Sse9 (XState)

/-- A spec over `MState`, read on the `Open9` part of an `XState`, with the XMM file as a
frame. -/
def Spec.toSse9 (S : Spec Silmaril.X86.MState) : Spec XState where
  entry x := S.entry x.m
  footprint x := S.footprint x.m
  post x y := S.post x.m y.m ∧ y.xmm = x.xmm

/-- **Every `Open9` contract is a contract of the XMM machine**, with the XMM registers
unchanged. -/
def toSse9 (C : FnContract Open9.isa) : FnContract Sse9.isa where
  toSpec := C.toSpec.toSse9
  total x _ ha he := by
    obtain ⟨t, hr, res⟩ := C.total x.m trivial ha he
    exact ⟨⟨t, x.xmm⟩, Sse9.reaches_of_open9 x.xmm hr,
      ⟨rfl, res.abi, res.frame, res.post, rfl⟩⟩

end Silmaril.X86.FnContract
