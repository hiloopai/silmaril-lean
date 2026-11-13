module

public import Silmaril.X86.Ext.SymExec

/-!
# Control-flow kinds of decoded instructions, and the flow law of a machine

DESIGN SKELETON (effects design, `/tmp/elfwork/effects/DESIGN.md`): the signatures are the
proposal; nothing here is proved yet.

A **flow decoder** (`FlowDec`) is a machine's listing decoder together with a syntactic
classification of every instruction it reads (`Kind`): where control may go after it, and what
it does to `rax` (for the number of a direct `syscall`). The **flow law** (`FlowLaw M D`) is the
one per-machine obligation that ties the classification to the semantics: every step of `M` from
an instruction that `D` reads in loaded code lands where the kind says.
-/

@[expose] public section

namespace Silmaril.X86.Flow

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN)

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
  | jcc (rel : Int)
  | jmp (rel : Int)
  | jmpInd (op : Opnd)
  | call (rel : Int)
  | callInd (op : Opnd)
  /-- `syscall` (`0F 05`): a direct system call. -/
  | syscall
  /-- `int 0x80`, `sysenter`, `int n`: a system-call path with another table; never a known
  number. -/
  | sysOther
  | ret
  /-- `ud2`, `hlt`, `int3`: no retiring step (on hardware: a signal that ends the process). -/
  | trap
  /-- Any other transfer (`iret`, far forms, `xbegin`, `loop`, `jrcxz`, ...): the checker rejects
  it in reachable code. -/
  | other
  deriving DecidableEq, Repr

/-- What an instruction does to `rax` (a whitelist: everything not listed is `clobber`). -/
inductive RaxT where
  | keep
  | set (n : Nat)
  | clobber
  deriving DecidableEq, Repr

/-- **A flow decoder**: a listing decoder and its classification. -/
structure FlowDec where
  Instr : Type
  [deq : DecidableEq Instr]
  decode : List Byte → Option (Instr × Nat)
  kind : Instr → Kind
  rax : Instr → RaxT

attribute [instance] FlowDec.deq

/-- A machine seen through its core and memory: a step relation (a functional machine embeds as
`fun s t => step s = some t`; a process machine with a kernel arm is a `UMach` whose `syscall`
steps are not user steps). -/
structure UMach (σ : Type) where
  step : σ → σ → Prop
  core : σ → State
  mem : σ → Memory
  live : σ → Prop := fun _ => True

/-- The address after an instruction of length `l` at `s.rip`. -/
def next (s : State) (l : Nat) : Word := s.rip + BitVec.ofNat 64 l

/-- `next + rel`, as the machine computes it. -/
def rel (s : State) (l : Nat) (r : Int) : Word := next s l + BitVec.ofInt 64 r

/-- The return address `next` is pushed: `rsp` decreases by 8 and the 8 bytes there are `next`. -/
def Pushed (s : State) (l : Nat) (t : State) (m : Memory) : Prop :=
  t.read .rsp = s.read .rsp - 8#64 ∧ loadN m (t.read .rsp) 8 = some (next s l)

/-- **Where a step from an instruction of kind `k` and length `l` may go.** Indirect targets are
not constrained here (their resolution is a certificate's business, `Cfg.Why`), but a
`callInd` still pushes. `syscall`, `sysOther`, `trap` and `other` admit no user step: the
system-call arms belong to the process layer (`Elf.Effects.Gen`). -/
def Admits : Kind → State → Memory → Nat → State → Memory → Prop
  | .seq, s, _, l, t, _ => t.rip = next s l
  | .rep, s, _, l, t, _ => t.rip = s.rip ∨ t.rip = next s l
  | .jcc r, s, _, l, t, _ => t.rip = next s l ∨ t.rip = rel s l r
  | .jmp r, s, _, l, t, _ => t.rip = rel s l r
  | .jmpInd _, _, _, _, _, _ => True
  | .call r, s, _, l, t, m' => t.rip = rel s l r ∧ Pushed s l t m'
  | .callInd _, s, _, l, t, m' => Pushed s l t m'
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

/-- **The flow law of `M` for `D`.** From a live state whose `rip` is offset `o` of code loaded at
`base`, where `D` reads `i` of length `l`, every step of `M` is admitted by `D.kind i` and
respects `D.rax i`. Proved once per machine, layer by layer up the `Str9` tower (see the
design: a layer that adds only `seq`/`rep` forms keeps the law). -/
def FlowLaw {σ : Type} (M : UMach σ) (D : FlowDec) : Prop :=
  ∀ s t (base : Word) (code : List Byte) (o l : Nat) (i : D.Instr),
    M.live s → Loaded (M.mem s) base code → (M.core s).rip = base + BitVec.ofNat 64 o →
    o + l ≤ code.length → D.decode ((code.drop o).take l) = some (i, l) →
    M.step s t →
    Admits (D.kind i) (M.core s) (M.mem s) l (M.core t) (M.mem t) ∧ RaxOk (D.rax i) (M.core s) (M.core t)

end Silmaril.X86.Flow
