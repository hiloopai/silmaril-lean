module

public import Silmaril.X86.Ext.SymExec

/-!
# Control-flow kinds of decoded instructions, and the flow law of a machine

A **flow decoder** (`FlowDec`) is a decoder of x86-64 instructions together with a syntactic
classification of every instruction it reads (`Kind`): where control may go after it, and what
it does to `rax` (the number of a direct `syscall` is read off `rax`). The **flow law**
(`FlowLaw M D`) is the one per-machine obligation that ties the classification to a semantics:
every step of the machine `M` from an instruction that `D` reads lands where the kind says, and
respects the `rax` transfer.

Nothing here is specific to one decoder. `Silmaril.X86.Flow.X64` is a length decoder of the
x86-64 encoding with its classification (the decoder of the worked examples); the decoders of
the `Str9` tower are other instances. The flow law of a tower machine for a decoder is a
per-machine theorem (`Thms`: the open goals).

## Choices

* `syscall`, `int 0x80`/`sysenter` (`sysOther`) and the traps (`ud2`, `hlt`, `int3`) admit **no
  user step**: system calls are the kernel arm of the process (`Silmaril.Elf.Effects.Step.sys`),
  and a trap on hardware raises a signal.
* An indirect branch through `disp(%rip)` (the GOT form of a PLT stub) lands on the 8 bytes read
  at `next + disp`; through a register, on the register. Other memory forms are unconstrained:
  their targets are a certificate's business (`Cfg.Why`).
* `other` (far transfers, `iret`, `xbegin`, `sysret`, …) admits anything; the CFG checker
  rejects it in a block.
* `Stable`: a decoder's answer depends only on the bytes of the instruction. It makes the
  instruction at an address unique (`Thms.at_unique`), so the step of a machine and the
  block of a certificate read the same instruction.
-/

@[expose] public section

namespace Silmaril.X86.Flow

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (loadN)

/-- The operand of an indirect branch. -/
inductive Opnd where
  /-- `jmp *%r` / `call *%r`. -/
  | reg (r : Reg)
  /-- `jmp *disp(%rip)`: the slot at `next + disp` (the GOT form of a PLT stub or `-fno-plt`). -/
  | ripMem (disp : Int)
  /-- `jmp *disp(base, index, scale)` and other memory forms. -/
  | mem
  deriving DecidableEq, Repr

/-- **The control-flow kind** of an instruction. Displacements are relative to the address of
the next instruction, as the machine computes them (wrapping at `2^64`). -/
inductive Kind where
  /-- Retires to the next instruction. -/
  | seq
  /-- A `rep` string form: one element per step, `rip` stays or moves to the next instruction. -/
  | rep
  /-- A conditional branch (also `loop`, `jrcxz`): the next instruction or `next + rel`. -/
  | jcc (rel : Int)
  | jmp (rel : Int)
  | jmpInd (op : Opnd)
  | call (rel : Int)
  | callInd (op : Opnd)
  /-- `syscall` (`0F 05`): a direct system call. -/
  | syscall
  /-- `int 0x80`, `int n`, `sysenter`: a system-call path through another table; never a known
  number. -/
  | sysOther
  | ret
  /-- `ud2`, `hlt`, `int3`, `int1`: no retiring step (on hardware: a signal). -/
  | trap
  /-- Any other transfer (far forms, `iret`, `xbegin`, `sysret`, …): rejected in a block. -/
  | other
  deriving DecidableEq, Repr

/-- What an instruction does to `rax` (a whitelist: everything not listed is `clobber`). -/
inductive RaxT where
  | keep
  | set (n : Nat)
  | clobber
  deriving DecidableEq, Repr

/-- **A flow decoder**: a decoder (bytes to an instruction and its length) and its
classification. -/
structure FlowDec where
  Instr : Type
  [deq : DecidableEq Instr]
  decode : List Byte → Option (Instr × Nat)
  kind : Instr → Kind
  rax : Instr → RaxT

attribute [instance] FlowDec.deq

/-- **The decoder reads a prefix**: an instruction read from a slice lies inside it, and its first
`l` bytes followed by anything read the same instruction. -/
def FlowDec.Stable (D : FlowDec) : Prop :=
  ∀ (w : List Byte) i l, D.decode w = some (i, l) →
    l ≤ w.length ∧ ∀ x, D.decode (w.take l ++ x) = some (i, l)

/-- A machine seen through its core and memory: a step relation (a functional machine embeds as
`fun s t => step s = some t`). System calls and library code are not user steps: they are the
kernel and library arms of the process (`Silmaril.Elf.Effects.World`). -/
structure UMach (σ : Type) where
  step : σ → σ → Prop
  core : σ → State
  mem : σ → Memory

/-- The address after an instruction of length `l` at `s.rip`. -/
def next (s : State) (l : Nat) : Word := s.rip + BitVec.ofNat 64 l

/-- `next + rel`, as the machine computes it. -/
def rel (s : State) (l : Nat) (r : Int) : Word := next s l + BitVec.ofInt 64 r

/-- The return address `next` is pushed: `rsp` decreases by 8 and the 8 bytes there are `next`. -/
def Pushed (s : State) (l : Nat) (t : State) (m : Memory) : Prop :=
  t.read .rsp = s.read .rsp - 8#64 ∧ loadN m (t.read .rsp) 8 = some (next s l)

/-- Where an indirect branch through `op` may go from `s` (memory `m`, length `l`). -/
def Opnd.Lands (op : Opnd) (s : State) (m : Memory) (l : Nat) (dst : Word) : Prop :=
  match op with
  | .reg r => dst = s.read r
  | .ripMem d => loadN m (next s l + BitVec.ofInt 64 d) 8 = some dst
  | .mem => True

/-- **Where a step from an instruction of kind `k` and length `l` may go** (`s`, `m`: before;
`t`, `m'`: after). `syscall`, `sysOther` and `trap` admit no user step. -/
def Admits : Kind → State → Memory → Nat → State → Memory → Prop
  | .seq, s, _, l, t, _ => t.rip = next s l
  | .rep, s, _, l, t, _ => t.rip = s.rip ∨ t.rip = next s l
  | .jcc r, s, _, l, t, _ => t.rip = next s l ∨ t.rip = rel s l r
  | .jmp r, s, _, l, t, _ => t.rip = rel s l r
  | .jmpInd op, s, m, l, t, _ => op.Lands s m l t.rip
  | .call r, s, _, l, t, m' => t.rip = rel s l r ∧ Pushed s l t m'
  | .callInd op, s, m, l, t, m' => op.Lands s m l t.rip ∧ Pushed s l t m'
  | .ret, s, m, _, t, _ => loadN m (s.read .rsp) 8 = some t.rip ∧ t.read .rsp = s.read .rsp + 8#64
  | .syscall, _, _, _, _, _ => False
  | .sysOther, _, _, _, _, _ => False
  | .trap, _, _, _, _, _ => False
  | .other, _, _, _, _, _ => True

/-- What a step does to `rax`. -/
def RaxOk : RaxT → State → State → Prop
  | .keep, s, t => t.read .rax = s.read .rax
  | .set n, _, t => t.read .rax = BitVec.ofNat 64 n
  | .clobber, _, _ => True

/-- **`D` reads `i` of length `l` at `rip`**: the `l` bytes fetched there decode to `i`. -/
def At {σ : Type} (M : UMach σ) (D : FlowDec) (s : σ) (i : D.Instr) (l : Nat) : Prop :=
  ∃ w, (M.mem s).fetchBytes (M.core s).rip.toNat l = some w ∧ D.decode w = some (i, l)

/-- **The flow law of `M` for `D`.** From a state where `D` reads `i` of length `l` at `rip`,
every step of `M` is admitted by `D.kind i` and respects `D.rax i`. One theorem per machine and
decoder. -/
def FlowLaw {σ : Type} (M : UMach σ) (D : FlowDec) : Prop :=
  ∀ s t (i : D.Instr) (l : Nat), At M D s i l → M.step s t →
    Admits (D.kind i) (M.core s) (M.mem s) l (M.core t) (M.mem t) ∧ RaxOk (D.rax i) (M.core s) (M.core t)

end Silmaril.X86.Flow
