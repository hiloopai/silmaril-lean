module

public import Silmaril.X86.Flow.Defs

/-!
# Control-flow graphs of x86 code: certificates and their checker

A **CFG certificate** for code reached from an entry address is a list of basic blocks (`Block`:
its start address, **its own bytes**, and a typed terminator `Term`). `Graph.sub D` (the looser
`cfg_sub`) decodes every block with the flow decoder `D` and checks that every interior
instruction falls through, that the last one agrees with the terminator (targets computed modulo
`2^64`, as the machine computes them), and that the graph is **closed**: the entry and every
intraprocedural successor start a block. `Graph.exact D` (`cfg_is`) adds that the blocks are in
address order and disjoint, that a fall-through goes only into a leader (blocks are maximal) and
that every block is reachable from the entry, so the certificate is *the* CFG.

Blocks carry their bytes so that a certificate holds no instruction terms and the checker is a
closed `decide` goal; that the bytes are the file's is a separate fact per block (`CodeAt`, in the
`Elf` region).

**Direct system calls.** `sys nr ret` must have `nr` equal to the `rax` constant that the block's
own instructions establish before the `syscall` (`raxStep`, a forward run of `D.rax` from
*unknown* at the block start). Otherwise `nr = none`, which the call graph reads as an unknown
system call (`Node.sysAny`).

The meaning of acceptance is the soundness theorem of `Silmaril.Elf.Effects`: under the flow law
of the machine, every reachable `rip` of the image is an instruction of a block, and every
transfer out of a block is one of its terminator's edges. External targets are a type parameter
`ε` (in the `Elf` region: an import by versioned name), so this layer does not depend on the ELF
API.
-/

@[expose] public section

namespace Silmaril.X86.Cfg

open Silmaril.X86 (Byte)
open Silmaril.X86.Flow (FlowDec Kind Opnd RaxT)

/-- An address as the machine computes it: modulo `2^64`. -/
def wrap (x : Int) : Nat := (x % (2 ^ 64 : Int)).toNat

/-- The target of a transfer. -/
inductive Target (ε : Type) where
  /-- A block of this graph (an intraprocedural edge). -/
  | blk (a : Nat)
  /-- The entry of a function (a call, or a tail jump). -/
  | fn (a : Nat)
  /-- An external function (an import), reached through a GOT slot. -/
  | ext (e : ε)
  deriving DecidableEq, Repr

/-- Why an indirect transfer goes only to its listed targets. -/
inductive Why where
  /-- Through the GOT slot at `slot` (`jmp *disp(%rip)`): the slot's relocation names the target
  and the slot is read-only after relocation (RELRO with `BIND_NOW`), or written only by the
  lazy resolver. Checked against the ELF (`Elf.Effects.GotOk`). -/
  | got (slot : Nat)
  /-- A bounded jump table: `n` entries of `width` bytes at `table` in read-only data, the index
  bounded by a `cmp`/`ja` guard in the same block. Checked by `JumpTable.check` (design). -/
  | table (tbl n width : Nat)
  /-- An assumption, carried as a hypothesis of the soundness theorem (`Hyps.ind`). -/
  | assumed
  /-- Not resolved: the targets are unknown (`Node.unresolved` in the call graph). -/
  | flagged
  deriving DecidableEq, Repr

/-- **A block terminator.** -/
inductive Term (ε : Type) where
  /-- The block ends at a leader; `next` is the next instruction. -/
  | fall (next : Nat)
  | jcc (taken next : Nat)
  | jmp (t : Target ε)
  /-- `none`: flagged (unknown targets). -/
  | jmpInd (ts : Option (List (Target ε))) (why : Why)
  /-- `ret = none`: the callee does not return (checked: `Hyps.noret`). -/
  | call (t : Target ε) (ret : Option Nat)
  | callInd (ts : Option (List (Target ε))) (why : Why) (ret : Option Nat)
  /-- A direct `syscall`; `nr = none`: the number is not determined (`Node.sysAny`). -/
  | sys (nr : Option Nat) (ret : Nat)
  /-- `int 0x80`, `sysenter`: always an unknown system call; `ret` is the next instruction. -/
  | sysOther (ret : Nat)
  | ret
  | trap
  deriving DecidableEq, Repr

/-- **A basic block**: its start, its bytes (the last instruction is the terminator's, except
for `fall`), and its terminator. -/
structure Block (ε : Type) where
  start : Nat
  bytes : List Byte
  term : Term ε
  deriving DecidableEq, Repr

/-- The address after the block. -/
def Block.stop {ε : Type} (b : Block ε) : Nat := b.start + b.bytes.length

/-- **A CFG certificate** of the code reached from `entry`. -/
structure Graph (ε : Type) where
  entry : Nat
  blocks : List (Block ε)
  deriving DecidableEq, Repr

variable {ε : Type}

/-- `rax` after one instruction, from `v` (`none`: unknown). -/
def raxStep (D : FlowDec) (v : Option Nat) (i : D.Instr) : Option Nat :=
  match D.rax i with
  | .keep => v
  | .set n => some n
  | .clobber => none

/-- The targets an indirect transfer lists. -/
def Term.listed : Term ε → Option (List (Target ε))
  | .jmpInd ts _ | .callInd ts _ _ => ts
  | _ => none

/-- The return-to address of a call. -/
def Term.retTo : Term ε → Option Nat
  | .call _ r | .callInd _ _ r => r
  | _ => none

/-- A call target is a function or an import, never a block. -/
def Target.callable : Target ε → Bool
  | .blk _ => false
  | _ => true

/-- **The terminator agrees with the last instruction** (kind `k`, ending at `stop`), and a
`syscall` number with the block's `rax` (`v`). -/
def termOk (t : Term ε) (k : Kind) (stop : Nat) (v : Option Nat) : Bool :=
  let tgt (r : Int) : Nat := wrap (stop + r)
  let retOk (r : Option Nat) : Bool := r == none || r == some stop
  match t, k with
  | .fall n, .seq | .fall n, .rep => n == stop
  | .jcc a n, .jcc r => a == tgt r && n == stop
  | .jmp (.blk a), .jmp r | .jmp (.fn a), .jmp r => a == tgt r
  | .jmpInd _ (.got s), .jmpInd (.ripMem d) => s == tgt d
  | .jmpInd _ (.table ..), .jmpInd _ | .jmpInd _ .assumed, .jmpInd _ => true
  | .jmpInd none .flagged, .jmpInd _ => true
  | .call (.fn a) r, .call d => a == tgt d && retOk r
  | .callInd ts (.got s) r, .callInd (.ripMem d) =>
    s == tgt d && retOk r && (ts.getD []).all Target.callable
  | .callInd ts .assumed r, .callInd _ => retOk r && (ts.getD []).all Target.callable
  | .callInd none .flagged r, .callInd _ => retOk r
  | .sys n r, .syscall => r == stop && n == v && (n.getD 0 < 2 ^ 64)
  | .sysOther r, .sysOther => r == stop
  | .ret, .ret | .trap, .trap => true
  | _, _ => false

/-- **Decode a block**, from offset `o` of the block at `start` (`s`: the bytes from `o` on, `v`:
the `rax` constant at `o`). Each instruction has a positive length inside the block; an interior
instruction is `seq` or `rep`; a `rep` keeps `rax`; the last one agrees with `t`. -/
def walk (D : FlowDec) (t : Term ε) (start : Nat) : Nat → Nat → Option Nat → List Byte → Bool
  | 0, _, _, _ => false
  | fuel + 1, o, v, s =>
    match D.decode s with
    | none => false
    | some (i, l) =>
      decide (0 < l) && decide (l ≤ s.length) && (D.kind i != .rep || D.rax i == .keep) &&
        (if l = s.length then termOk t (D.kind i) (start + o + l) v
         else (D.kind i == .seq || D.kind i == .rep) && walk D t start fuel (o + l) (raxStep D v i) (s.drop l))

/-- One block decodes and is well formed. -/
def Block.ok (D : FlowDec) (b : Block ε) : Bool := walk D b.term b.start b.bytes.length 0 none b.bytes

/-- The intraprocedural successors of a terminator. -/
def Term.succs : Term ε → List Nat
  | .fall n => [n]
  | .jcc a n => [a, n]
  | .jmp (.blk a) => [a]
  | .jmpInd (some ts) _ => ts.filterMap fun | .blk a => some a | _ => none
  | .call _ (some r) | .callInd _ _ (some r) | .sys _ r | .sysOther r => [r]
  | _ => []

/-- `a` starts a block. -/
def Graph.isStart (G : Graph ε) (a : Nat) : Bool := G.blocks.any (·.start == a)

/-- **Closed**: the entry and every successor start a block. -/
def Graph.closed (G : Graph ε) : Bool :=
  G.isStart G.entry && G.blocks.all fun b => b.term.succs.all G.isStart

/-- **`cfg_sub`**: every block decodes and is well formed, and the graph is closed. -/
def Graph.sub (D : FlowDec) (G : Graph ε) : Bool := G.blocks.all (Block.ok D) && G.closed

/-- Blocks reachable from the entry in at most `k` intraprocedural edges. -/
def Graph.reach (G : Graph ε) : Nat → List Nat
  | 0 => [G.entry]
  | k + 1 =>
    let r := G.reach k
    r ++ (G.blocks.filter (fun b => r.contains b.start)).flatMap fun b =>
      b.term.succs.filter fun a => !r.contains a

/-- The leaders: the entry and every successor of a terminator other than `fall`. -/
def Graph.leaders (G : Graph ε) : List Nat :=
  G.entry :: G.blocks.flatMap fun b => match b.term with
    | .fall _ => []
    | t => t.succs

/-- **`cfg_is`**: `cfg_sub`, the blocks in address order and disjoint, a `fall` only into a
leader, and every block reachable from the entry. -/
def Graph.exact (D : FlowDec) (G : Graph ε) : Bool :=
  G.sub D &&
    (G.blocks.zip G.blocks.tail).all (fun p => decide (p.1.stop ≤ p.2.start)) &&
    G.blocks.all (fun b => match b.term with
      | .fall n => G.leaders.contains n
      | _ => true) &&
    G.blocks.all fun b => (G.reach G.blocks.length).contains b.start

end Silmaril.X86.Cfg
