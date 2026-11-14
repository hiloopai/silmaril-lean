module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs

/-!
# A finite-state explorer for CIR's native machines, and a TSO-robustness checker

The CIR-native machines
(`Csl.ScStep`, the SC interleaving, and `Csl.OStep .tso`, x86-TSO store buffers) run closed CIR
programs. For a program with bounded loops, no `local` blocks and finitely many cells, the
reachable configurations are finite. This module enumerates them:

* `tsucc`: the small steps of one thread (`Csl.TStep`), with each read answered by a given view
  of memory (so the machines' read choice is made here);
* `scSucc`, `tsoSucc`: one step of the SC machine and of the TSO machine on a concrete
  configuration `CSt` (thread statements and register lists, cell list, store buffers);
* silent steps are run eagerly (`tauNF`, `ftsoSucc`, `fscSucc`), and visited sets are hashed
  binary trees (`HTree`); `explore` is a depth-first search with a fuel bound.

Two checks use them. Their soundness theorems are in `Robust/Thms.lean`.

* **Final-state checking on TSO** (`tsoCheck`): a set of configurations is **closed** under the
  fused TSO successors and contains the normalised start, and a Boolean property holds of every
  finished, drained element. Then the property holds of every finished, drained TSO-reachable
  configuration (`tsoCheck_sound`). The set is computed by `explore`, but soundness rests only on
  the closure check, so the search is untrusted.
* **TSO robustness** (`robustB`): every finished, drained configuration of the closed TSO set
  has the same thread states and memory as a finished configuration found by exploring the SC
  machine. Then every TSO final state is an SC final state (`robustB_sound`). On the SC side every
  explored configuration is reachable by construction (`explore` only adds successors).

The checks are **state** checks of one closed program instance: one choice of threads, initial
values and loop bounds. They are exact for that instance (no abstraction), and say nothing about
other instances.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap Ent TStep view newest)
open Silmaril.X86.Concurrency.Cir.TvCfg (sbeq)

/-! ## Concrete registers and memory -/

/-- The value of register `r` in a list of the sixteen register values (in register-number
order, `Tv.allRegs`). -/
def rget (l : List Word) (r : Reg) : Word := l.getD r.toBitVec.toNat 0

/-- The register list of a register file. -/
def rlist (rs : Regs) : List Word := Tv.allRegs.map rs

/-- A memory as a list of `(cell, value)`. -/
def memOf (l : List (Nat × Nat)) : Heap := fun a => (l.find? (·.1 == a)).map (·.2)

/-- Set a cell (in place if present, else in front). -/
def setC (l : List (Nat × Nat)) (a v : Nat) : List (Nat × Nat) :=
  if l.any (·.1 == a) then l.map fun p => if p.1 == a then (a, v) else p else (a, v) :: l

/-- The cells a label reads or writes (no `local` blocks). -/
def labCells : Lab → List Nat
  | .rd _ _ a _ _ | .wr _ _ a _ _ | .rmw _ a _ _ _ | .fwait a _ _ _
  | .fblock a _ => [a]
  | _ => []

/-- A label's writes, on a cell list (no `local` blocks). -/
def updL (l : List (Nat × Nat)) : Lab → List (Nat × Nat)
  | .wr _ _ a _ v => setC l a v
  | .rmw _ a _ _ n => setC l a n
  | _ => l

/-- Flush a buffer entry into a cell list. -/
def applyE (l : List (Nat × Nat)) : Ent → List (Nat × Nat)
  | .st a v _ => setC l a v
  | .bar => l

/-- No `local` blocks. -/
def noBlk : Stmt → Bool
  | .local _ => false
  | .seq s t | .ite _ s t => noBlk s && noBlk t
  | .loop _ _ b => noBlk b
  | _ => true

/-! ## Thread steps -/

/-- **The small steps of a thread** (`Csl.TStep`) whose reads return the values of `vw`.
A futex wait or wake also lists every value `< 2 ^ 8` of its ghost waiter-queue byte: `TStep`
leaves that byte free, and it changes neither the statement, the registers nor the memory. -/
def tsucc (vw : Heap) : Stmt → Regs → List (Option Lab × Stmt × Regs)
  | .skip, _ => []
  | .assign d e, rs => [(none, .skip, rs.set d (e.eval rs))]
  | .load d m sz fl a, rs =>
    match vw (a.eval rs).toNat with
    | some v =>
      if v < 2 ^ (8 * sz) then
        [(some (.rd m fl (a.eval rs).toNat sz v), .skip, rs.set d (BitVec.ofNat 64 v))]
      else []
    | none => []
  | .store m sz fl a v, rs =>
    [(some (.wr m fl (a.eval rs).toNat sz ((v.eval rs).toNat % 2 ^ (8 * sz))), .skip, rs)]
  | .rmw d m sz op a arg, rs =>
    match vw (a.eval rs).toNat with
    | some old =>
      if old < 2 ^ (8 * sz) then
        [(some (.rmw m (a.eval rs).toNat sz old (op.result rs sz old (arg.eval rs))), .skip,
          rs.set d (BitVec.ofNat 64 old))]
      else []
    | none => []
  | .fence k, rs => [(some (.fence k), .skip, rs)]
  | .futexWait d a v, rs =>
    match vw (a.eval rs).toNat with
    | some seen =>
      if seen < 2 ^ 32 then
        (List.range (2 ^ 8)).map fun r =>
          (some (.fwait (a.eval rs).toNat ((v.eval rs).toNat % 2 ^ 32) seen r), .skip,
            rs.set d (BitVec.ofNat 64 (if seen = (v.eval rs).toNat % 2 ^ 32 then 0 else eagain)))
      else []
    | none => []
  | .futexWake a n, rs =>
    (List.range (2 ^ 8)).map fun q =>
      (some (.fwake (a.eval rs).toNat (n.eval rs).toNat q), .skip, rs)
  | .spawn t, rs => [(some (.spawn t), .skip, rs)]
  | .join t, rs => [(some (.join t), .skip, rs)]
  | .local _, _ => []
  | .seq s t, rs =>
    (match s with | .skip => [(none, t, rs)] | _ => []) ++
      (tsucc vw s rs).map fun p => (p.1, .seq p.2.1 t, p.2.2)
  | .ite c s t, rs => [(none, if truthy (c.eval rs) then s else t, rs)]
  | .loop n c b, rs =>
    if truthy (c.eval rs) then
      match n with
      | 0 => []
      | k + 1 => [(none, .seq b (.loop k c b), rs)]
    else [(none, .skip, rs)]

/-! ## Concrete configurations -/

/-- A concrete configuration: per thread its statement and register list, the cells, and per
thread its store buffer (oldest first). -/
structure CSt where
  ts : List (Stmt × List Word)
  mem : List (Nat × Nat)
  buf : List (List Ent)

/-- Equality of concrete configurations (`false` on `local` blocks). -/
def CSt.beq (c d : CSt) : Bool :=
  c.ts.length == d.ts.length &&
    (c.ts.zip d.ts).all (fun p => sbeq p.1.1 p.2.1 && p.1.2 == p.2.2) &&
    c.mem == d.mem && c.buf == d.buf

/-- The thread state of thread `t`. -/
def CSt.th (c : CSt) (t : Nat) : Stmt × Regs :=
  match c.ts[t]? with
  | some p => (p.1, rget p.2)
  | none => (.skip, Regs.zero)

/-- **The SC configuration** a concrete configuration stands for. -/
def CSt.cfg (c : CSt) : Csl.Cfg := ⟨c.th, memOf c.mem⟩

/-- **The buffered configuration** a concrete configuration stands for. -/
def CSt.ocfg (c : CSt) : Csl.OCfg := ⟨c.th, memOf c.mem, fun t => c.buf.getD t []⟩

/-- Replace thread `t`'s state. -/
def CSt.setTh (c : CSt) (t : Nat) (s : Stmt) (rs : Regs) : CSt :=
  { c with ts := c.ts.set t (s, rlist rs) }

/-- Every cell a label touches is mapped. -/
def mappedB (mem : List (Nat × Nat)) (l : Lab) : Bool :=
  (labCells l).all fun a => (memOf mem a).isSome

/-! ## Machine steps -/

/-- **One SC step** of thread `t`. -/
def scStepT (c : CSt) (t : Nat) : List CSt :=
  (tsucc (memOf c.mem) (c.th t).1 (c.th t).2).filterMap fun p =>
    match p.1 with
    | none => some (c.setTh t p.2.1 p.2.2)
    | some l =>
      if l.isMem && mappedB c.mem l then some { c.setTh t p.2.1 p.2.2 with mem := updL c.mem l }
      else none

/-- **The SC successors** of a configuration of `N` threads. -/
def scSucc (N : Nat) (c : CSt) : List CSt := (List.range N).flatMap (scStepT c)

/-- Thread `t`'s buffer. -/
def CSt.bufT (c : CSt) (t : Nat) : List Ent := c.buf.getD t []

/-- **One TSO step** of thread `t` (a thread step or a flush of its oldest entry). -/
def tsoStepT (c : CSt) (t : Nat) : List CSt :=
  ((tsucc (view (memOf c.mem) (c.bufT t)) (c.th t).1 (c.th t).2).filterMap fun p =>
    match p.1 with
    | none => some (c.setTh t p.2.1 p.2.2)
    | some l =>
      if l.isMem && mappedB c.mem l then
        if l.drains then
          if c.bufT t = [] then some { c.setTh t p.2.1 p.2.2 with mem := updL c.mem l } else none
        else some { c.setTh t p.2.1 p.2.2 with buf := c.buf.set t (c.bufT t ++ l.ents) }
      else none) ++
  match c.bufT t with
  | e :: post => [{ c with mem := applyE c.mem e, buf := c.buf.set t post }]
  | [] => []

/-- **The TSO successors** of a configuration of `N` threads. -/
def tsoSucc (N : Nat) (c : CSt) : List CSt := (List.range N).flatMap (tsoStepT c)

/-! ## Silent steps

A thread's silent steps (`assign`, branches, loop tests, `seq` bookkeeping) touch only its own
statement and registers, and are deterministic. The explorer therefore runs them eagerly: it
stores only configurations in which no thread has a silent step (`CSt.normalB`), and after a
thread's visible step it runs that thread's silent steps to the end (`tauNF`). `Robust/Thms`
proves that this loses no finished configuration. -/

/-- Thread `t` has no silent step. -/
def CSt.normalT (c : CSt) (t : Nat) : Bool :=
  (tsucc (memOf c.mem) (c.th t).1 (c.th t).2).all fun p => p.1.isSome

/-- No thread of `N` has a silent step. -/
def CSt.normalB (N : Nat) (c : CSt) : Bool := (List.range N).all c.normalT

/-- Run thread `t`'s silent steps (at most `fuel`). -/
def tauNF (t : Nat) : Nat → CSt → CSt
  | 0, c => c
  | f + 1, c =>
    match tsucc (memOf c.mem) (c.th t).1 (c.th t).2 with
    | [(none, s', rs')] => tauNF t f (c.setTh t s' rs')
    | _ => c

/-- Run every thread's silent steps. -/
def normAll (N fuel : Nat) (c : CSt) : CSt := (List.range N).foldl (fun c t => tauNF t fuel c) c

/-- The fuel for one thread's silent steps. -/
def tauFuel : Nat := 10000

/-- **The fused TSO successors**: a visible step or flush of a thread, then its silent steps. -/
def ftsoSucc (N : Nat) (c : CSt) : List CSt :=
  (List.range N).flatMap fun t => (tsoStepT c t).map (tauNF t tauFuel)

/-- **The fused SC successors**. -/
def fscSucc (N : Nat) (c : CSt) : List CSt :=
  (List.range N).flatMap fun t => (scStepT c t).map (tauNF t tauFuel)

/-! ## Hashed sets of configurations -/

/-- Mix a number into a hash. -/
def mix (h x : Nat) : Nat := (h * 1000003 + x) % 4611686018427387847

/-- The number of nodes and the loop bounds of a statement (a cheap fingerprint). -/
def stmtFp : Stmt → Nat
  | .seq s t => mix (mix 1 (stmtFp s)) (stmtFp t)
  | .ite _ s t => mix (mix 2 (stmtFp s)) (stmtFp t)
  | .loop n _ b => mix (mix 3 n) (stmtFp b)
  | .skip => 4
  | .assign .. => 5
  | .load .. => 6
  | .store .. => 7
  | .rmw .. => 8
  | _ => 9

/-- The fingerprint of a buffer entry. -/
def entFp : Ent → Nat
  | .st a v w => mix (mix (if w then 2 else 1) a) v
  | .bar => 3

/-- **The hash of a configuration** (only for speed: membership always compares fully). -/
def CSt.hash (c : CSt) : Nat :=
  let h := c.ts.foldl (fun h p => p.2.foldl (fun h w => mix h w.toNat) (mix h (stmtFp p.1))) 7
  let h := c.mem.foldl (fun h p => mix (mix h p.1) p.2) h
  c.buf.foldl (fun h b => b.foldl (fun h e => mix h (entFp e)) (mix h 11)) h

/-- A binary search tree of configurations keyed by hash. -/
inductive HTree where
  | leaf
  | node (l : HTree) (k : Nat) (vs : List CSt) (r : HTree)

/-- The configurations stored under key `k`. -/
def HTree.find (k : Nat) : HTree → List CSt
  | .leaf => []
  | .node l k' vs r => if k < k' then l.find k else if k' < k then r.find k else vs

/-- Insert `c` under key `k`. -/
def HTree.ins (k : Nat) (c : CSt) : HTree → HTree
  | .leaf => .node .leaf k [c] .leaf
  | .node l k' vs r =>
    if k < k' then .node (l.ins k c) k' vs r else if k' < k then .node l k' vs (r.ins k c)
    else .node l k' (c :: vs) r

/-- `c` is in the tree (up to `CSt.beq`). -/
def HTree.memB (T : HTree) (c : CSt) : Bool := (T.find c.hash).any (CSt.beq c)

/-- The elements of a tree. -/
def HTree.elems : HTree → List CSt
  | .leaf => []
  | .node l _ vs r => l.elems ++ vs ++ r.elems

/-- The tree of a list. -/
def HTree.ofList (l : List CSt) : HTree := l.foldl (fun T c => T.ins c.hash c) .leaf

/-! ## Exploration -/

/-- Depth-first exploration: the visited configurations when the stack is empty or the fuel runs
out. The tree `T` holds the visited configurations, for deduplication. -/
def explore (succ : CSt → List CSt) : Nat → List CSt → HTree → List CSt → List CSt
  | 0, _, _, vis => vis
  | _ + 1, [], _, vis => vis
  | f + 1, x :: st, T, vis =>
    let r := (succ x).foldl (fun (acc : List CSt × HTree) y =>
      if acc.2.memB y then acc else (y :: acc.1, acc.2.ins y.hash y)) ([], T)
    explore succ f (r.1 ++ st) r.2 (r.1 ++ vis)

/-- Every thread has finished (`N` threads). -/
def CSt.doneB (N : Nat) (c : CSt) : Bool := (List.range N).all fun t => sbeq (c.th t).1 .skip

/-- Every buffer is empty. -/
def CSt.drainedB (c : CSt) : Bool := c.buf.all List.isEmpty

/-- The configuration is well shaped for `N` threads, with no `local` blocks. -/
def CSt.okB (N : Nat) (c : CSt) : Bool :=
  c.ts.length == N && c.buf.length == N && c.ts.all fun p => noBlk p.1 && p.2.length == 16

/-- `S` is **closed** under the fused TSO successors of `N` threads (up to `CSt.beq`, looked up
in the tree of `S`), and every element is well shaped and has no silent step. -/
def closedB (N : Nat) (S : List CSt) : Bool :=
  let T := HTree.ofList S
  S.all fun c => c.okB N && c.normalB N && (ftsoSucc N c).all T.memB

/-- The fused TSO configurations explored from `c0`. -/
def tsoStates (N fuel : Nat) (c0 : CSt) : List CSt :=
  let c := normAll N tauFuel c0
  explore (ftsoSucc N) fuel [c] (HTree.leaf.ins c.hash c) [c]

/-- The fused SC configurations explored from `c0`. -/
def scStates (N fuel : Nat) (c0 : CSt) : List CSt :=
  let c := normAll N tauFuel c0
  explore (fscSucc N) fuel [c] (HTree.leaf.ins c.hash c) [c]

/-- **Final-state check on TSO**: the explored set is closed, contains the normalised start, and
`P` holds of each of its finished, drained elements. -/
def tsoCheck (N fuel : Nat) (c0 : CSt) (P : CSt → Bool) : Bool :=
  let S := tsoStates N fuel c0
  closedB N S && (HTree.ofList S).memB (normAll N tauFuel c0) && c0.buf.all List.isEmpty &&
    S.all fun c => !(c.doneB N && c.drainedB) || P c

/-- `S` is closed under the fused SC successors, every element well shaped, without silent
steps and with empty buffers. -/
def closedScB (N : Nat) (S : List CSt) : Bool :=
  let T := HTree.ofList S
  S.all fun c => c.okB N && c.normalB N && c.drainedB && (fscSucc N c).all T.memB

/-- **The SC final-state check**: the explored set is closed and contains the normalised start,
and `P` holds of its finished elements. -/
def scCheck (N fuel : Nat) (c0 : CSt) (P : CSt → Bool) : Bool :=
  let S := scStates N fuel c0
  closedScB N S && (HTree.ofList S).memB (normAll N tauFuel c0) && c0.buf.all List.isEmpty &&
    S.all fun c => !c.doneB N || P c

/-- Same thread states and memory. -/
def CSt.sameFinal (c d : CSt) : Bool :=
  c.ts.length == d.ts.length &&
    (c.ts.zip d.ts).all (fun p => sbeq p.1.1 p.2.1 && p.1.2 == p.2.2) && c.mem == d.mem

/-- **The TSO-robustness check** of a closed program instance of `N` threads: every finished,
drained TSO configuration has the threads and memory of a finished SC configuration. -/
def robustB (N fuelT fuelS : Nat) (c0 : CSt) : Bool :=
  let S := tsoStates N fuelT c0
  let F := (scStates N fuelS c0).filter (CSt.doneB N)
  closedB N S && (HTree.ofList S).memB (normAll N tauFuel c0) && c0.buf.all List.isEmpty &&
    S.all fun c => !(c.doneB N && c.drainedB) || F.any (CSt.sameFinal c)

/-- The finished, drained TSO configurations with no finished SC configuration of the same
threads and memory among those explored (the witnesses of non-robustness). -/
def violations (N fuelT fuelS : Nat) (c0 : CSt) : List CSt :=
  let S := tsoStates N fuelT c0
  let F := (scStates N fuelS c0).filter (CSt.doneB N)
  S.filter fun c => c.doneB N && c.drainedB && !F.any (CSt.sameFinal c)

/-- A start configuration: the threads with their registers, the cells, empty buffers. -/
def start (ts : List (Stmt × Regs)) (mem : List (Nat × Nat)) : CSt :=
  ⟨ts.map fun p => (p.1, rlist p.2), mem, ts.map fun _ => []⟩

end Silmaril.X86.Concurrency.Cir.Robust
