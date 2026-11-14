module

public import Silmaril.X86.Concurrency.Cir.Defs

/-!
# Fork-join CIR (`Fj`): disjoint jobs in parallel, then a combine

A **fork-join program** is the smallest shape of data-parallel code: a main thread spawns `N`
workers, each worker runs **one** sequential job, the main thread
joins them all and runs a combine job. Every job
is a CIR `local(B)` block, so its only meaning is its sequential summary.

`Fj` is a tiny IR *on top of* CIR, not a new semantics. `Par.prog` lowers it to an ordinary
CIR `Prog` (judged by SC/TSO/XL), and `Par.seqMem` is its sequential meaning: run the
jobs one after another on one flat memory, then the combine. The theorem (`Par.behav_mem`, in
`...Cir.Fj.Thms`) is that under every model `M ⊑ XL`, every behaviour of the parallel program
ends with the sequential memory on the data bytes, provided the footprints are disjoint
(`Par.Ok`): no job writes a byte another job reads or writes. The proof is done **once**, for
every fork-join program; an instance (parallel hashing, `Cir.ParHash`) only checks `Par.okB`
and never unfolds the memory model.

* `Job`: a functional sequential job over cells (`ins` read, `outs` written, `fn` the output
  values as a function of the input values). `Job.block` is its CIR block; its contract is
  `outs = fn ins`.
* `Par`: locations, the worker jobs and the combine job. `Par.prog`: thread `0` is
  `spawn 1; …; spawn N; join 1; …; join N; local comb`, thread `k + 1` is `local (jobs[k])`.
* `Par.seqMem`: the jobs, then the combine, replayed on the initial memory.
* `Par.Ok`: the footprint conditions, and `Par.okB`, a decision procedure for them.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Fj

open Silmaril.X86.MemoryModel.Litmus (Loc initByte)

/-! ## Jobs -/

/-- A **job**: sequential code summarised by a function from the values of its input cells
(in order) to the values of its output cells (in order). -/
structure Job where
  name : String
  ins : List (Nat × Nat)
  outs : List (Nat × Nat)
  fn : List Nat → List Nat

/-- The CIR block of a job: no registers, contract `outs = fn ins`. -/
def Job.block (j : Job) : Block where
  name := j.name
  ins := j.ins
  outs := j.outs
  rin := []
  rout := []
  spec a b := b = j.fn a
  dec _ _ := inferInstance

/-- Byte `y` lies in cell `c = (addr, size)`. -/
def Cell.has (c : Nat × Nat) (y : Nat) : Prop := c.1 ≤ y ∧ y < c.1 + c.2

/-- Two cells share no byte. -/
def Cell.disjB (c d : Nat × Nat) : Bool := decide (c.1 + c.2 ≤ d.1) || decide (d.1 + d.2 ≤ c.1)

/-- The value of a cell in a flat memory (unmapped bytes read as `0`). -/
def cellVal (m : Mem) (c : Nat × Nat) : Nat := (m.val c.1 c.2).getD 0

/-- Write cells with values, in order (as `Lab.replay` of a block). -/
def putAll (m : Mem) (l : List (Nat × Nat × Nat)) : Mem :=
  l.foldl (fun m c => m.put c.1 c.2.1 c.2.2) m

/-- **Run a job sequentially**: read its input cells, write `fn` of them. -/
def Job.run (j : Job) (m : Mem) : Mem := putAll m (cellVals j.outs (j.fn (j.ins.map (cellVal m))))

/-! ## Fork-join programs -/

/-- A fork-join program: locations, `N` worker jobs and a combine job. -/
structure Par where
  locs : List Loc
  jobs : List Job
  comb : Job

/-- Sequence statements (`s₁; …; sₙ; skip`). -/
def seqs : List Stmt → Stmt
  | [] => .skip
  | s :: l => .seq s (seqs l)

/-- The main thread: spawn every worker, join every worker, run the combine job. -/
def Par.main (F : Par) : Stmt :=
  .seq (seqs ((List.range F.jobs.length).map fun k => .spawn (k + 1)))
    (.seq (seqs ((List.range F.jobs.length).map fun k => .join (k + 1))) (.local F.comb.block))

/-- **The CIR program**: thread `0` is the main thread, thread `k + 1` runs `jobs[k]`. -/
def Par.prog (F : Par) : Prog :=
  ⟨F.locs, ⟨F.main, false⟩ :: F.jobs.map fun j => ⟨.local j.block, true⟩⟩

/-- The initial memory. -/
def Par.init (F : Par) : Mem := initByte F.locs

/-- The memory after the worker jobs, run sequentially in order. -/
def Par.jobsMem (F : Par) : Mem := F.jobs.foldl (fun m j => j.run m) F.init

/-- **The sequential meaning**: the worker jobs in order, then the combine. -/
def Par.seqMem (F : Par) : Mem := F.comb.run F.jobsMem

/-! ## Footprint conditions -/

/-- The data region: below every ghost control byte. -/
def dataTop : Nat := ctlAddr 0

/-- **Disjoint footprints.**
* every cell and every location lies in the data region (below the control bytes);
* no job writes a byte that some worker reads (`insFree`), so worker inputs are initial;
* two different output cells (of one job or of two jobs, combine included) share no byte;
* the combine's inputs and outputs share no byte. -/
structure Par.Ok (F : Par) : Prop where
  locsLow : ∀ l ∈ F.locs, l.addr + l.size ≤ dataTop
  jobsLow : ∀ j ∈ F.jobs, ∀ c ∈ j.ins ++ j.outs, c.1 + c.2 ≤ dataTop
  combLow : ∀ c ∈ F.comb.ins ++ F.comb.outs, c.1 + c.2 ≤ dataTop
  insFree : ∀ j ∈ F.jobs, ∀ c ∈ j.ins, ∀ k ∈ F.jobs ++ [F.comb], ∀ d ∈ k.outs, Cell.disjB c d
  outsDisj : ((F.jobs ++ [F.comb]).flatMap Job.outs).Pairwise fun c d => Cell.disjB c d
  combDisj : ∀ c ∈ F.comb.ins, ∀ d ∈ F.comb.outs, Cell.disjB c d

/-- `Par.Ok` as a Boolean (`Par.ok_of_okB`). -/
def Par.okB (F : Par) : Bool :=
  F.locs.all (fun l => decide (l.addr + l.size ≤ dataTop)) &&
  F.jobs.all (fun j => (j.ins ++ j.outs).all fun c => decide (c.1 + c.2 ≤ dataTop)) &&
  (F.comb.ins ++ F.comb.outs).all (fun c => decide (c.1 + c.2 ≤ dataTop)) &&
  F.jobs.all (fun j => j.ins.all fun c => (F.jobs ++ [F.comb]).all fun k =>
    k.outs.all fun d => Cell.disjB c d) &&
  pairwiseB Cell.disjB ((F.jobs ++ [F.comb]).flatMap Job.outs) &&
  F.comb.ins.all (fun c => F.comb.outs.all fun d => Cell.disjB c d)
where
  /-- `List.Pairwise` as a Boolean. -/
  pairwiseB (r : Nat × Nat → Nat × Nat → Bool) : List (Nat × Nat) → Bool
    | [] => true
    | c :: l => l.all (r c) && pairwiseB r l

end Silmaril.X86.Concurrency.Cir.Fj
