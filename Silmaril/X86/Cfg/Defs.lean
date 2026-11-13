module

public import Silmaril.X86.Flow.Defs

/-!
# Control-flow graphs of x86 code: certificates and their checker

DESIGN SKELETON (effects design, `/tmp/elfwork/effects/DESIGN.md`).

A **CFG certificate** for code reached from an entry address is a list of basic blocks (`Block`:
start address, decoded instructions with their lengths, a typed terminator `Term`). `Graph.sub`
(the looser `cfg_sub`) checks that every block decodes, by the flow decoder `D`, from the code
windows `img`, that every interior instruction falls through, that each terminator agrees with
its last instruction, and that the graph is **closed** under intraprocedural successors.
`Graph.exact` (`cfg_is`) adds: the blocks are disjoint and maximal and every block is reachable
from the entry, so the certificate is *the* CFG.

The meaning of acceptance is the soundness theorem of the design (`Elf.Effects`): under the flow
law of the machine, from the entry every reachable `rip` is an instruction of some block until
the code leaves through a `call`, an external target, a `ret` or a `syscall` edge.

External targets are a type parameter `ε` (in the `Elf` region: `Silmaril.Elf.Ref`, an import
by versioned name), so this layer does not depend on the ELF API.
-/

@[expose] public section

namespace Silmaril.X86.Cfg

open Silmaril.X86 (Byte)
open Silmaril.X86.Flow (FlowDec Kind Opnd RaxT)

/-- Code windows: `(vaddr, bytes)`, each a `CodeAt` fact of the file (`Elf.Effects.Faithful`). -/
abbrev Image := List (Nat × List Byte)

/-- The `l` bytes at `a`, from the first window holding all of them. -/
def Image.window (img : Image) (a l : Nat) : Option (List Byte) :=
  img.findSome? fun w => if w.1 ≤ a ∧ a + l ≤ w.1 + w.2.length then some ((w.2.drop (a - w.1)).take l) else none

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

/-- **A basic block**: its start, its instructions with their lengths (the last one is the
terminator's instruction, except for `fall`), and its terminator. -/
structure Block (D : FlowDec) (ε : Type) where
  start : Nat
  body : List (D.Instr × Nat)
  term : Term ε

/-- The address after the block. -/
def Block.stop {D : FlowDec} {ε : Type} (b : Block D ε) : Nat := b.start + (b.body.map (·.2)).sum

/-- **A CFG certificate** of the code reached from `entry`; `raxIn` annotates block starts with a
constant `rax` (validated on every incoming edge). -/
structure Graph (D : FlowDec) (ε : Type) where
  entry : Nat
  blocks : List (Block D ε)
  raxIn : List (Nat × Nat) := []

variable {D : FlowDec} {ε : Type}

/-- The instructions of a block decode at their addresses. -/
def decodes (img : Image) : Nat → List (D.Instr × Nat) → Bool
  | _, [] => true
  | a, (i, l) :: rest =>
    decide (0 < l) && (match img.window a l with
      | some w => decide (D.decode w = some (i, l))
      | none => false) && decodes img (a + l) rest

/-- `rax` after running the transfers of `is` from `v`. -/
def raxRun : Option Nat → List (D.Instr × Nat) → Option Nat
  | v, [] => v
  | v, (i, _) :: rest =>
    raxRun (match D.rax i with
      | .keep => v
      | .set n => some n
      | .clobber => none) rest

/-- The annotated `rax` at a block start. -/
def Graph.raxAt (G : Graph D ε) (a : Nat) : Option Nat := (G.raxIn.find? (·.1 = a)).map (·.2)

/-- The terminator agrees with the last instruction (`k`, at `last`, length `l`, block end
`stop`), and the `syscall` number with the block's `rax` (`v`). -/
def termOk (t : Term ε) (k : Kind) (stop : Nat) (v : Option Nat) : Bool :=
  let tgt (r : Int) : Nat := wrap (stop + r)
  match t, k with
  | .fall n, .seq | .fall n, .rep => n = stop
  | .jcc a n, .jcc r => a = tgt r && n = stop
  | .jmp (.blk a), .jmp r | .jmp (.fn a), .jmp r => a = tgt r
  | .jmpInd _ (.got s), .jmpInd (.ripMem d) => s = tgt d
  | .jmpInd _ (.table ..), .jmpInd _ | .jmpInd _ .assumed, .jmpInd _ => true
  | .jmpInd none .flagged, .jmpInd _ => true
  | .call (.fn a) r, .call d => a = tgt d && (r = none || r = some stop)
  | .callInd _ (.got s) r, .callInd (.ripMem d) => s = tgt d && (r = none || r = some stop)
  | .callInd _ .assumed r, .callInd _ => r = none || r = some stop
  | .callInd none .flagged r, .callInd _ => r = none || r = some stop
  | .sys n r, .syscall => r = stop && n == v
  | .sysOther r, .sysOther => r = stop
  | .ret, .ret | .trap, .trap => true
  | _, _ => false

/-- Interior instructions fall through (`seq` or `rep`). -/
def interiorOk (is : List (D.Instr × Nat)) : Bool :=
  is.dropLast.all fun (i, _) => D.kind i = .seq || D.kind i = .rep

/-- One block is well formed. -/
def Block.ok (G : Graph D ε) (img : Image) (b : Block D ε) : Bool :=
  !b.body.isEmpty && decodes img b.start b.body && interiorOk b.body &&
    (match b.body.getLast? with
      | some (i, _) =>
        termOk b.term (D.kind i) b.stop (raxRun (G.raxAt b.start) b.body.dropLast)
      | none => false)

/-- The intraprocedural successors of a terminator, with whether `rax` survives the edge. -/
def Term.succs : Term ε → List (Nat × Bool)
  | .fall n => [(n, true)]
  | .jcc a n => [(a, true), (n, true)]
  | .jmp (.blk a) => [(a, true)]
  | .jmpInd (some ts) _ => ts.filterMap fun | .blk a => some (a, true) | _ => none
  | .call _ (some r) | .callInd _ _ (some r) | .sys _ r | .sysOther r => [(r, false)]
  | _ => []

/-- `a` starts a block. -/
def Graph.isStart (G : Graph D ε) (a : Nat) : Bool := G.blocks.any (·.start = a)

/-- **Closed**: the entry and every successor start a block, and every `rax` annotation holds on
every incoming edge (the entry's `rax` is unknown). -/
def Graph.closed (G : Graph D ε) : Bool :=
  G.isStart G.entry && G.raxAt G.entry = none &&
    G.blocks.all fun b => b.term.succs.all fun (a, keep) =>
      G.isStart a && (match G.raxAt a with
        | none => true
        | some n => keep && raxRun (G.raxAt b.start) b.body == some n)

/-- **`cfg_sub`**: every block decodes and is well formed, and the graph is closed. -/
def Graph.sub (G : Graph D ε) (img : Image) : Bool := G.blocks.all (Block.ok G img) && G.closed

/-- Blocks reachable from the entry in at most `k` intraprocedural edges. -/
def Graph.reach (G : Graph D ε) : Nat → List Nat
  | 0 => [G.entry]
  | k + 1 =>
    let r := G.reach k
    r ++ (G.blocks.filter (fun b => r.contains b.start)).flatMap fun b =>
      (b.term.succs.map (·.1)).filter fun a => !r.contains a

/-- The leaders: the entry and every successor of a terminator other than `fall`. -/
def Graph.leaders (G : Graph D ε) : List Nat :=
  G.entry :: G.blocks.flatMap fun b => match b.term with
    | .fall _ => []
    | t => t.succs.map (·.1)

/-- **`cfg_is`**: `cfg_sub`, the blocks pairwise disjoint and in address order, a `fall` only into
a leader, and every block reachable from the entry. -/
def Graph.exact (G : Graph D ε) (img : Image) : Bool :=
  G.sub img &&
    (G.blocks.zip G.blocks.tail).all (fun p => decide (p.1.stop ≤ p.2.start)) &&
    G.blocks.all (fun b => match b.term with
      | .fall n => G.leaders.contains n
      | _ => true) &&
    G.blocks.all fun b => (G.reach G.blocks.length).contains b.start

end Silmaril.X86.Cfg
