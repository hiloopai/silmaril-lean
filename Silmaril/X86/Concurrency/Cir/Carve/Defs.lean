module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs

/-!
# Carving a CIR thread into sequential and concurrent regions (prototype)

After translation validation (`Cir.Tv`, `Cir.TvCfg`) a thread is a list of CIR statements, one
cut per x86 instruction. This module splits such a list **automatically** into

* **sequential regions** (`Region.seq ops`): maximal runs of statements that touch only cells
  the thread owns. These are the candidates for `local(B)` blocks, where a sequential contract
  (`FnContract`, Bir, X86Loose) replaces the code;
* **concurrent statements** (`Region.conc s`): everything else.

## The ownership test

Ownership is decided syntactically from the program (`privCells`): a cell `(a, sz)` that
thread `i` accesses at a literal address is **private** to `i` when every other thread's body
`Stmt.avoids` it (every access of that thread is at a literal address disjoint from the cell;
a computed address makes the cell shared, conservatively).

A statement is **local** (`Stmt.isLocalIn`) when it is an `assign`, a plain write-back load or
store of a private cell at a literal address, a `local` block over private cells, or a
structured statement whose parts are local. Read-modify-writes, fences, futex calls, `spawn`
and `join` are never local, even on a private cell: they are the synchronisation points, and
summarising them away would weaken every verdict (sound, but useless).

## The link to `Task.cirLocalize`

`footOk P i pre ops post B` is the Boolean form of the syntactic hypotheses of
`Tv.Task.cirLocalize` for the region `ops` of thread `i` with context `pre`/`post` and block
`B` (it also checks that the footprint lies below the ghost bytes).
`Carve.localize_of_footOk` (in `Thms`) turns a passing check and a contract into the refinement
(under XL it also asks that the statements after the region use write-back stores); it is
unconditional, as `Tv.Task.cirLocalize` is proved. `Region.foot` is the default footprint of a
region (cells read and
written, registers written). The checks here are decided per program; nothing in this module
is trusted.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Carve

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (uniq)

/-! ## Cells -/

/-- The cells a statement accesses at literal addresses (computed addresses are skipped). -/
def Stmt.litCells : Stmt → List (Nat × Nat)
  | .load _ _ sz _ (.lit a) | .store _ sz _ (.lit a) _ | .rmw _ _ sz _ (.lit a) _ => [(a, sz)]
  | .futexWait _ (.lit a) _ => [(a, 4)]
  | .local b => b.ins ++ b.outs
  | .seq s t | .ite _ s t => Stmt.litCells s ++ Stmt.litCells t
  | .loop _ _ b => Stmt.litCells b
  | _ => []

/-- The cells a statement reads (loads, and the inputs of blocks) at literal addresses. -/
def Stmt.readCells : Stmt → List (Nat × Nat)
  | .load _ _ sz _ (.lit a) => [(a, sz)]
  | .local b => b.ins
  | .seq s t | .ite _ s t => Stmt.readCells s ++ Stmt.readCells t
  | .loop _ _ b => Stmt.readCells b
  | _ => []

/-- The cells a statement writes (stores, and the outputs of blocks) at literal addresses. -/
def Stmt.writeCells : Stmt → List (Nat × Nat)
  | .store _ sz _ (.lit a) _ => [(a, sz)]
  | .local b => b.outs
  | .seq s t | .ite _ s t => Stmt.writeCells s ++ Stmt.writeCells t
  | .loop _ _ b => Stmt.writeCells b
  | _ => []

/-- The cells of thread `i` that no other thread touches (`Stmt.avoids`). -/
def privCells (P : Prog) (i : Nat) (ops : List Stmt) : List (Nat × Nat) :=
  uniq ((ops.flatMap Stmt.litCells).filter fun c =>
    (List.range P.threads.length).all fun j =>
      j == i || (P.threads[j]?.all fun th => th.body.avoids [c]))

/-! ## Local statements and regions -/

/-- **A local statement**: it touches only private cells, by plain write-back accesses at
literal addresses, and is not a synchronisation point. -/
def Stmt.isLocalIn (priv : List (Nat × Nat)) : Stmt → Bool
  | .skip | .assign .. => true
  | .load _ _ sz fl (.lit a) => fl == .wb && priv.contains (a, sz)
  | .store _ sz fl (.lit a) _ => fl == .wb && priv.contains (a, sz)
  | .local b => (b.ins ++ b.outs).all priv.contains
  | .seq s t | .ite _ s t => Stmt.isLocalIn priv s && Stmt.isLocalIn priv t
  | .loop _ _ b => Stmt.isLocalIn priv b
  | _ => false

/-- A region of a carved thread. -/
inductive Region where
  /-- A maximal run of local statements: a candidate `local(B)`. -/
  | seq (ops : List Stmt)
  /-- A statement that stays in the concurrency layer. -/
  | conc (s : Stmt)

/-- The statements of a region. -/
def Region.stmts : Region → List Stmt
  | .seq ops => ops
  | .conc s => [s]

/-- Is the region sequential. -/
def Region.isSeq : Region → Bool
  | .seq _ => true
  | .conc _ => false

/-- Put a local statement in front: it joins a following sequential region. -/
def pushSeq (s : Stmt) : List Region → List Region
  | .seq ops :: rs => .seq (s :: ops) :: rs
  | rs => .seq [s] :: rs

/-- **Carve** a statement list into maximal local runs and concurrent statements. -/
def carve (priv : List (Nat × Nat)) : List Stmt → List Region
  | [] => []
  | s :: l => if Stmt.isLocalIn priv s then pushSeq s (carve priv l) else .conc s :: carve priv l

/-- Carve thread `i` of `P`, whose body is `chain ops`, with its own private cells. -/
def carveThread (P : Prog) (i : Nat) (ops : List Stmt) : List Region :=
  carve (privCells P i ops) ops

/-! ## Footprints and the localisation check -/

/-- The default footprint of a sequential region: cells read, cells written, registers
written. -/
def Region.foot (ops : List Stmt) : List (Nat × Nat) × List (Nat × Nat) × List Reg :=
  (uniq (ops.flatMap Stmt.readCells), uniq (ops.flatMap Stmt.writeCells),
    uniq (ops.flatMap Stmt.writes))

/-- **The syntactic hypotheses of `Task.cirLocalize`**, as one Boolean, for the region `ops`
of thread `i` between `pre` and `post`, summarised by `B` (only `B`'s footprint is read). -/
def footOk (P : Prog) (i : Nat) (pre ops post : List Stmt) (B : Block) : Bool :=
  let cs := B.ins ++ B.outs
  B.cellsOk &&
    (ops.all fun s => s.onCells cs && s.storesWithin B.outs && s.threadFree && s.futexFree) &&
    (cs.all fun c => P.locs.any fun l => decide (l.addr ≤ c.1 ∧ c.1 + c.2 ≤ l.addr + l.size)) &&
    (cs.all fun c => decide (c.1 + c.2 ≤ ctlAddr 0)) &&
    ((pre ++ post).all (Stmt.avoids cs)) &&
    ((List.range P.threads.length).all fun j =>
      j == i || (P.threads[j]?.all fun th => th.body.avoids cs)) &&
    (ops.all fun s => s.writes.all B.rout.contains)

/-- A block with a given footprint and contract. -/
def blockOf (name : String) (ins outs : List (Nat × Nat)) (rin rout : List Reg)
    (spec : List Nat → List Nat → Prop) (dec : ∀ a b, Decidable (spec a b)) : Block :=
  ⟨name, ins, outs, rin, rout, spec, dec⟩

/-- The footprint block of a region with the trivial contract (for the syntactic check only). -/
def footBlock (ops : List Stmt) : Block :=
  let f := Region.foot ops
  blockOf "foot" f.1 f.2.1 [] f.2.2 (fun _ _ => True) fun _ _ => inferInstance

/-- The regions of a carved list with the statements before and after each. -/
def withContext : List Region → List (List Stmt × Region × List Stmt)
  | [] => []
  | r :: rs =>
    (([] : List Stmt), r, rs.flatMap Region.stmts) ::
      (withContext rs).map fun p => (r.stmts ++ p.1, p.2.1, p.2.2)

/-! ## Statistics (for the IR study) -/

/-- Per thread: statements, statements in sequential regions, sequential regions, and
sequential regions that pass `footOk` with their default footprint. -/
def stats (P : Prog) (i : Nat) (ops : List Stmt) : Nat × Nat × Nat × Nat :=
  let rs := carveThread P i ops
  let seqs := (withContext rs).filter fun p => p.2.1.isSeq
  (ops.length, (rs.filter Region.isSeq).foldl (fun n r => n + r.stmts.length) 0, seqs.length,
    (seqs.filter fun p => footOk P i p.1 p.2.1.stmts p.2.2 (footBlock p.2.1.stmts)).length)

/-! ## An example: store buffering with result slots -/

namespace Ex

/-- `x`, `y` (shared) and the result slots `r0`, `r1` (written by one thread each). -/
abbrev x : Nat := 0x10000
abbrev y : Nat := 0x10040
abbrev r0 : Nat := 0x10080
abbrev r1 : Nat := 0x100c0

/-- Thread `i` of `SB` as compiled C: store one flag, load the other, store the result. -/
def ops (a b r : Nat) : List Stmt :=
  [.store .rlx 4 .wb (.lit a) (.lit 1), .load .rax .rlx 4 .wb (.lit b),
    .store .na 4 .wb (.lit r) (.reg .rax)]

/-- The program. -/
def prog : Prog :=
  ⟨[⟨"x", x, 4, 0⟩, ⟨"y", y, 4, 0⟩, ⟨"r0", r0, 4, 0⟩, ⟨"r1", r1, 4, 0⟩],
    [⟨chain (ops x y r0), false⟩, ⟨chain (ops y x r1), false⟩]⟩

end Ex

end Silmaril.X86.Concurrency.Cir.Carve
