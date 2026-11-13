module

public import Silmaril.Machine.CBackend.RTL.SSA.Defs
public import Silmaril.Foundations.ForwardSim
public import Silmaril.Machine.CBackend.Lift.Diff.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-!
# Rung 4: SSA construction, checked by erasure

An agent proposes an `RTL.SSA.Func` and claims it is the SSA form of a given
`RTL.Func`. The check is that the proposal is well formed **and** that it
*erases* to the function it claims to come from. `erase` is SSA destruction:
block arguments become moves and the blocks are flattened into the numbered
nodes RTL uses. So the checker does not have to trust an SSA construction
algorithm; it recomputes the inverse, which is syntactic, and compares.

## The layout

`erase` lays each block out in order: its ops, one node each, then its
terminator's expansion.

| terminator | nodes emitted |
| --- | --- |
| `jump t as` | one `move` per argument, then `jump` to `t`'s first node |
| `cond c t₁ a₁ t₂ a₂` | a `cond` to two chunks, each the moves of its edge then a `jump` |
| `ret vs` | one `ret` |
| `trap` | one `trap` |

The moves of each edge sit in the *predecessor*'s region, one chunk per
successor. There is therefore no critical-edge problem: two edges out of one
`cond` never share a move sequence, so nothing has to be split.

## The parallel-move problem, and what this rung does about it

A transfer `jump t as` writes `t`'s parameters simultaneously. Emitting
`params[0] := as[0]; params[1] := as[1]; …` sequentially is **wrong** when a
parameter already written is read as a later argument — the swap `L(a, b): …
jump L(b, a)`, which is perfectly legal SSA, becomes `a := b; b := a` and loses
`a`. The two standard repairs are to route every move through a scratch
register, and to sequentialize the parallel move properly (Rideau, Serpette and
Leroy's algorithm), which also needs one scratch register.

**Neither is available here.** `erase` must land in `RTL.Func R` for the same
`R` the proposal uses, because the function it is compared against is over `R`;
there is no fresh-name supply for an arbitrary register type, and inventing one
would change the type of the result and so change what the checker could
compare. Rather than emit a wrong `erase`, this rung restricts `erase`'s domain
and makes the restriction a checker condition with its own rejection:
`sequentialMoves` holds of a transfer when no parameter is written before it is
read, which is exactly — not merely sufficiently — the condition under which the
moves in the given order implement the simultaneous write. A proposal that
violates it is rejected as `SsaReject.parallelMove`, naming both blocks, and the
repair is to split the edge through an intermediate block.

The condition can only fail on a transfer to a block that dominates the
transferring block, because a parameter of `t` is in scope at the jump only
then; in practice that means a back edge into a loop header whose parameters are
permuted. `RTL.Examples.ssaFactorial` is not such a program and is accepted.

Routing through a scratch register, with the register type widened to `R ⊕ Nat`
and the comparison widened to match, is the follow-up that lifts the
restriction.

## What acceptance buys

`erase_behaves` is the deliverable: the proposal and the function it erases to
have the same behaviours, started on the same function, arguments and memory.
It is a real simulation — one SSA step becomes one or more RTL steps — and it is
the substantial content of this rung.
-/

@[expose] public section

namespace Silmaril.Machine.Lift

open Silmaril.Machine.Lir (Word Memory)

variable {R : Type}

/-! ## Erasure

Every list-building function here is defined by structural recursion threading
the node the next instruction occupies. That is not cosmetic: the layout lemmas
below (`opsCode_drop`, `movesCode_drop`, `codeFrom_drop`) are what the
simulation runs on, and each is one induction on the list being laid out. A
definition by `zipIdx` and `map` computes the same list and makes those lemmas
an exercise in index arithmetic instead. -/

/-- An SSA operation as an RTL instruction continuing at `succ`. -/
def instrOfOp (succ : Nat) : RTL.SSA.Op R → RTL.Instr R
  | .const d v => .const d v succ
  | .move d s => .move d s succ
  | .unary op d s => .unary op d s succ
  | .binary op d a b => .binary op d a b succ
  | .load w e d base off => .load w e d base off succ
  | .store w base off src => .store w base off src succ
  | .call f args results => .call f args results succ

/-- A block's straight-line operations, one node each from `base`, each
continuing at the next. -/
def opsCode (base : Nat) : List (RTL.SSA.Op R) → List (RTL.Instr R)
  | [] => []
  | o :: rest => instrOfOp (base + 1) o :: opsCode (base + 1) rest

/-- A block's operations occupy one node each. -/
@[simp] theorem opsCode_length (base : Nat) (os : List (RTL.SSA.Op R)) :
    (opsCode base os).length = os.length := by
  induction os generalizing base with
  | nil => rfl
  | cons o rest ih => simp [opsCode, ih]

/-- Dropping `i` operations from a laid-out block is laying out the rest from
`i` nodes further on. -/
theorem opsCode_drop (base : Nat) : ∀ (os : List (RTL.SSA.Op R)) (i : Nat),
    (opsCode base os).drop i = opsCode (base + i) (os.drop i)
  | os, 0 => by simp
  | [], _ + 1 => by simp [opsCode]
  | o :: rest, i + 1 => by
    have hb : base + 1 + i = base + (i + 1) := by omega
    rw [opsCode, List.drop_succ_cons, opsCode_drop (base + 1) rest i, List.drop_succ_cons, hb]

/-- The moves of a transfer, one node each from `base`, each continuing at the
next. -/
def movesCode (base : Nat) : List (R × R) → List (RTL.Instr R)
  | [] => []
  | (d, src) :: rest => RTL.Instr.move d src (base + 1) :: movesCode (base + 1) rest

/-- A transfer's moves occupy one node each. -/
@[simp] theorem movesCode_length (base : Nat) (ms : List (R × R)) :
    (movesCode base ms).length = ms.length := by
  induction ms generalizing base with
  | nil => rfl
  | cons m rest ih => simp [movesCode, ih]

/-- The parameters of a block, and `[]` for a label that names none. -/
def paramsOf (fn : RTL.SSA.Func R) (l : RTL.SSA.Label) : List R :=
  (fn.block? l).elim [] RTL.SSA.Block.params

/-- The moves one transfer performs, as destination-source pairs. `ArgsMatch`
makes the two lists the same length; zipping keeps `erase` total when it does
not hold, and a proposal for which it does not is rejected. -/
def transferPairs (fn : RTL.SSA.Func R) (t : RTL.SSA.Label) (as : List R) : List (R × R) :=
  List.zipWith Prod.mk (paramsOf fn t) as

/-- The number of nodes a terminator expands to. -/
def termSize (fn : RTL.SSA.Func R) : RTL.SSA.Term R → Nat
  | .jump t as => (transferPairs fn t as).length + 1
  | .cond _ t₁ a₁ t₂ a₂ =>
    1 + ((transferPairs fn t₁ a₁).length + 1) + ((transferPairs fn t₂ a₂).length + 1)
  | .ret _ => 1
  | .trap => 1

/-- The number of nodes a block expands to. -/
def blockSize (fn : RTL.SSA.Func R) (b : RTL.SSA.Block R) : Nat :=
  b.ops.length + termSize fn b.term

/-- The node counts of the blocks, in order. -/
def blockSizes (fn : RTL.SSA.Func R) : List Nat := fn.blocks.map (blockSize fn)

/-- The first node of a block. A label past the last block starts at the node
count of the whole function, which is out of range, so a transfer to a block
that does not exist is stuck in the erased function exactly as it is in the
SSA one. -/
def startOf (fn : RTL.SSA.Func R) (l : RTL.SSA.Label) : Nat :=
  ((blockSizes fn).take l).sum

/-- The moves of one transfer laid out from `base`, followed by the jump to the
target's first node. -/
def transferCode (fn : RTL.SSA.Func R) (base : Nat) (t : RTL.SSA.Label) (as : List R) :
    List (RTL.Instr R) :=
  movesCode base (transferPairs fn t as) ++ [RTL.Instr.jump (startOf fn t)]

/-- A transfer occupies one node per move and one for the jump. -/
@[simp] theorem transferCode_length (fn : RTL.SSA.Func R) (base : Nat)
    (t : RTL.SSA.Label) (as : List R) :
    (transferCode fn base t as).length = (transferPairs fn t as).length + 1 := by
  simp [transferCode]

/-- A terminator's expansion, laid out from `base`. -/
def termCode (fn : RTL.SSA.Func R) (base : Nat) : RTL.SSA.Term R → List (RTL.Instr R)
  | .jump t as => transferCode fn base t as
  | .cond c t₁ a₁ t₂ a₂ =>
    RTL.Instr.cond c (base + 1) (base + 1 + (transferPairs fn t₁ a₁).length + 1) ::
      (transferCode fn (base + 1) t₁ a₁ ++
        transferCode fn (base + 1 + (transferPairs fn t₁ a₁).length + 1) t₂ a₂)
  | .ret vs => [RTL.Instr.ret vs]
  | .trap => [RTL.Instr.trap]

/-- A terminator occupies the nodes `termSize` counts. -/
@[simp] theorem termCode_length (fn : RTL.SSA.Func R) (base : Nat) (t : RTL.SSA.Term R) :
    (termCode fn base t).length = termSize fn t := by
  cases t <;> (simp [termCode, termSize]; try omega)

/-- A block's expansion, laid out from `base`. -/
def blockCode (fn : RTL.SSA.Func R) (base : Nat) (b : RTL.SSA.Block R) :
    List (RTL.Instr R) :=
  opsCode base b.ops ++ termCode fn (base + b.ops.length) b.term

/-- A block occupies the nodes `blockSize` counts. -/
@[simp] theorem blockCode_length (fn : RTL.SSA.Func R) (base : Nat)
    (b : RTL.SSA.Block R) : (blockCode fn base b).length = blockSize fn b := by
  simp [blockCode, blockSize]

/-- Blocks laid out one after another from `base`. -/
def codeFrom (fn : RTL.SSA.Func R) (base : Nat) : List (RTL.SSA.Block R) →
    List (RTL.Instr R)
  | [] => []
  | b :: rest => blockCode fn base b ++ codeFrom fn (base + blockSize fn b) rest

/-- **Erase block arguments to moves and flatten blocks to nodes.** -/
def erase (fn : RTL.SSA.Func R) : RTL.Func R where
  sig := fn.sig
  params := paramsOf fn fn.entry
  entry := startOf fn fn.entry
  code := codeFrom fn 0 fn.blocks

/-- Erasure of a whole program, function by function. -/
def eraseProg (p : RTL.SSA.Prog R) : RTL.Prog R := ⟨p.funcs.map erase⟩

/-! ## The layout of the erased code -/

/-- The nodes a prefix of the blocks occupies. -/
theorem sum_take_blockSizes (fn : RTL.SSA.Func R) (i : Nat) :
    ((fn.blocks.take i).map (blockSize fn)).sum = startOf fn i := by
  rw [startOf, blockSizes, List.map_take]

/-- Blocks laid out one after another occupy the sum of their node counts. -/
@[simp] theorem codeFrom_length (fn : RTL.SSA.Func R) (base : Nat) :
    ∀ bs : List (RTL.SSA.Block R), (codeFrom fn base bs).length = (bs.map (blockSize fn)).sum
  | [] => rfl
  | b :: rest => by
    rw [codeFrom, List.length_append, blockCode_length, codeFrom_length fn _ rest]
    simp

/-- Dropping the nodes of the first `i` blocks leaves the rest laid out from
where they start. -/
theorem codeFrom_drop (fn : RTL.SSA.Func R) : ∀ (bs : List (RTL.SSA.Block R)) (base i : Nat),
    (codeFrom fn base bs).drop (((bs.take i).map (blockSize fn)).sum) =
      codeFrom fn (base + ((bs.take i).map (blockSize fn)).sum) (bs.drop i)
  | _, base, 0 => by simp
  | [], base, _ + 1 => by simp [codeFrom]
  | b :: rest, base, i + 1 => by
    have hb : (blockCode fn base b).length = blockSize fn b := blockCode_length fn base b
    have hsplit : blockSize fn b + ((rest.take i).map (blockSize fn)).sum
        = (blockCode fn base b).length + ((rest.take i).map (blockSize fn)).sum := by rw [hb]
    have hassoc : base + blockSize fn b + ((rest.take i).map (blockSize fn)).sum
        = base + (blockSize fn b + ((rest.take i).map (blockSize fn)).sum) := by omega
    rw [List.take_succ_cons, List.map_cons, List.sum_cons, List.drop_succ_cons, codeFrom,
      hsplit, ← List.drop_drop, List.drop_left,
      codeFrom_drop fn rest (base + blockSize fn b) i, hassoc, hb]

/-- **The code of an erased function, read from the start of one block.** This
is the lemma the simulation runs on: the nodes from a block's first are that
block's expansion followed by everything after it. -/
theorem erase_code_drop (fn : RTL.SSA.Func R) {l : Nat} (h : l < fn.blocks.length) :
    (erase fn).code.drop (startOf fn l) =
      blockCode fn (startOf fn l) fn.blocks[l] ++
        codeFrom fn (startOf fn l + blockSize fn fn.blocks[l]) (fn.blocks.drop (l + 1)) := by
  rw [erase]
  simp only
  rw [← sum_take_blockSizes, codeFrom_drop fn fn.blocks 0 l, Nat.zero_add,
    List.drop_eq_getElem_cons h, codeFrom, sum_take_blockSizes]

/-- The node count of an erased function. -/
theorem erase_code_length (fn : RTL.SSA.Func R) :
    (erase fn).code.length = startOf fn fn.blocks.length := by
  rw [erase]
  simp only
  rw [codeFrom_length, ← sum_take_blockSizes, List.take_length]

/-- A label past the last block starts past the last node, so a transfer to a
block that does not exist is stuck in the erased function. -/
theorem erase_code_length_le (fn : RTL.SSA.Func R) {l : Nat} (h : fn.blocks.length ≤ l) :
    (erase fn).code.length ≤ startOf fn l := by
  have hlen : (blockSizes fn).length = fn.blocks.length := by simp [blockSizes]
  rw [erase_code_length, startOf, startOf, List.take_of_length_le (by omega),
    List.take_of_length_le (by omega)]

/-! ## The sequentializable transfers -/

/-- The sequential moves `ps[0] := as[0]; ps[1] := as[1]; …` implement the
simultaneous assignment `ps := as` exactly when no parameter is written before
it is read as a later argument. This is the condition, not merely a sufficient
one: if `ps[i]` occurs among `as[i+1…]` then the move to `ps[i]` changes what
the later read sees, and if it does not then no move changes any later read. -/
def sequentialMoves [DecidableEq R] : List R → List R → Bool
  | [], _ => true
  | _, [] => true
  | p :: ps, _ :: as => !(as.contains p) && sequentialMoves ps as

/-- Every transfer of the function is sequentializable in the order its
argument list gives. -/
def SequentialTransfers [DecidableEq R] (fn : RTL.SSA.Func R) : Prop :=
  ∀ b ∈ fn.blocks, ∀ ta ∈ b.term.args, sequentialMoves (paramsOf fn ta.1) ta.2 = true

instance [DecidableEq R] (fn : RTL.SSA.Func R) : Decidable (SequentialTransfers fn) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _))

/-- The first transfer whose moves the given order would compute wrongly, as
the labels of its source and target blocks. -/
def firstNonSequential [DecidableEq R] (fn : RTL.SSA.Func R) :
    Option (RTL.SSA.Label × RTL.SSA.Label) :=
  (List.range fn.blocks.length).findSome? fun l =>
    match fn.block? l with
    | none => none
    | some b => b.term.args.findSome? fun ta =>
        if sequentialMoves (paramsOf fn ta.1) ta.2 then none else some (l, ta.1)

/-! ## Rejection -/

/-- Why an SSA proposal was rejected. -/
inductive SsaReject where
  /-- The entry block is missing, its parameter count disagrees with the
  signature, a terminator names a block that does not exist, or a `ret` returns
  the wrong number of values. -/
  | signature
  /-- Some register is assigned twice: the proposal is not in SSA form. -/
  | notSingleAssignment
  /-- Some use is not reached by a definition that dominates it. -/
  | useNotDominated
  /-- Some terminator's argument list does not have the length of its target's
  parameter list. -/
  | argsMismatch
  /-- The transfer from `source` to `target` writes a parameter that a later
  argument of the same transfer reads, so the moves `erase` emits would compute
  the wrong simultaneous assignment. Split the edge. -/
  | parallelMove (source target : RTL.SSA.Label)
  /-- The proposal is well formed, but its signature, parameters or entry node
  differ from the recovered function's. -/
  | shapeMismatch
  /-- The proposal is well formed, but erasing it gives a different instruction
  at this node. -/
  | erasureMismatch (node : RTL.Node)
  /-- The proposal and the recovered program have different numbers of
  functions. -/
  | functionCount (proposed recovered : Nat)
  /-- This function of the proposal was rejected. -/
  | inFunction (func : RTL.FuncId) (reason : SsaReject)
  deriving DecidableEq, Repr

/-! ## The checker -/

/-- **Check a proposed SSA function**: that it is well formed, that every
transfer is sequentializable in the order given, and that erasing it reproduces
the recovered function exactly. -/
def checkSsa [DecidableEq R] (target : RTL.Func R) (spec : RTL.SSA.Func R) :
    Except SsaReject Unit :=
  if ¬ spec.WellFormedSig then .error .signature
  else if ¬ spec.SingleAssignment then .error .notSingleAssignment
  else if ¬ spec.UsesDominated then .error .useNotDominated
  else if ¬ spec.ArgsMatch then .error .argsMismatch
  else
    match firstNonSequential spec with
    | some (l, t) => .error (.parallelMove l t)
    | none =>
      if (erase spec).sig ≠ target.sig ∨ (erase spec).params ≠ target.params ∨
          (erase spec).entry ≠ target.entry then
        .error .shapeMismatch
      else
        match firstDiff 0 (erase spec).code target.code with
        | some n => .error (.erasureMismatch n)
        | none => .ok ()

/-- Check a proposed SSA program, function by function. -/
def checkSsaProg [DecidableEq R] (target : RTL.Prog R) (spec : RTL.SSA.Prog R) :
    Except SsaReject Unit :=
  if spec.funcs.length ≠ target.funcs.length then
    .error (.functionCount spec.funcs.length target.funcs.length)
  else
    match (List.range spec.funcs.length).findSome? fun i =>
        match target.funcs[i]?, spec.funcs[i]? with
        | some t, some sp =>
          match checkSsa t sp with
          | .error e => some (SsaReject.inFunction i e)
          | .ok () => none
        | _, _ => none with
    | some e => .error e
    | none => .ok ()

/-! ## Inverting the checker

`checkSsa_inv` is the single inversion; the statements after it read one
conjunct of it back. -/

/-- Two RTL functions agreeing field by field are equal. -/
private theorem func_eq {a b : RTL.Func R} (hs : a.sig = b.sig) (hp : a.params = b.params)
    (he : a.entry = b.entry) (hc : a.code = b.code) : a = b := by
  cases a; cases b; simp_all

/-- Everything a successful `checkSsa` established, in one statement. -/
theorem checkSsa_inv [DecidableEq R] {target : RTL.Func R} {spec : RTL.SSA.Func R}
    (h : checkSsa target spec = .ok ()) :
    spec.WellFormed ∧ firstNonSequential spec = none ∧ erase spec = target := by
  rw [checkSsa] at h
  split at h
  case isTrue => exact absurd h (by simp)
  rename_i h1
  split at h
  case isTrue => exact absurd h (by simp)
  rename_i h2
  split at h
  case isTrue => exact absurd h (by simp)
  rename_i h3
  split at h
  case isTrue => exact absurd h (by simp)
  rename_i h4
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hseq
  split at h
  case isTrue => exact absurd h (by simp)
  rename_i hshape
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hdiff
  simp only [not_or, ne_eq, not_not] at hshape
  exact ⟨⟨not_not.mp h1, not_not.mp h2, not_not.mp h3, not_not.mp h4⟩, hseq,
    func_eq hshape.1 hshape.2.1 hshape.2.2 (eq_of_firstDiff_none 0 _ _ hdiff)⟩

/-- Acceptance establishes well-formedness. -/
theorem checkSsa_wellFormed [DecidableEq R] {target : RTL.Func R} {spec : RTL.SSA.Func R}
    (h : checkSsa target spec = .ok ()) : spec.WellFormed := (checkSsa_inv h).1

/-- Acceptance establishes that every transfer is sequentializable. -/
theorem checkSsa_sequential [DecidableEq R] {target : RTL.Func R} {spec : RTL.SSA.Func R}
    (h : checkSsa target spec = .ok ()) : SequentialTransfers spec := by
  intro b hb ta hta
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hb
  have hblk : spec.block? l = some spec.blocks[l] := List.getElem?_eq_getElem hl
  have hnone := List.findSome?_eq_none_iff.mp (checkSsa_inv h).2.1 l (List.mem_range.mpr hl)
  rw [hblk] at hnone
  have := List.findSome?_eq_none_iff.mp hnone ta hta
  split at this
  · assumption
  · exact absurd this (by simp)

/-- Acceptance establishes that the proposal erases to the recovered
function. -/
theorem checkSsa_erase_eq [DecidableEq R] {target : RTL.Func R} {spec : RTL.SSA.Func R}
    (h : checkSsa target spec = .ok ()) : erase spec = target := (checkSsa_inv h).2.2

/-- Everything a successful `checkSsaProg` established. -/
theorem checkSsaProg_inv [DecidableEq R] {target : RTL.Prog R} {spec : RTL.SSA.Prog R}
    (h : checkSsaProg target spec = .ok ()) :
    spec.funcs.length = target.funcs.length ∧
      ∀ i (hi : i < spec.funcs.length) (hi' : i < target.funcs.length),
        checkSsa target.funcs[i] spec.funcs[i] = .ok () := by
  rw [checkSsaProg] at h
  split at h
  case isTrue => exact absurd h (by simp)
  rename_i hlen
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hall
  have hlen' : spec.funcs.length = target.funcs.length := not_not.mp hlen
  refine ⟨hlen', fun i hi hi' => ?_⟩
  have := List.findSome?_eq_none_iff.mp hall i (List.mem_range.mpr hi)
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at this
  simp only at this
  split at this
  · exact absurd this (by simp)
  · rename_i heq
    simpa using heq

/-- Acceptance of a program establishes that it erases to the recovered
program. -/
theorem checkSsaProg_erase_eq [DecidableEq R] {target : RTL.Prog R} {spec : RTL.SSA.Prog R}
    (h : checkSsaProg target spec = .ok ()) : eraseProg spec = target := by
  obtain ⟨hlen, hall⟩ := checkSsaProg_inv h
  refine congrArg RTL.Prog.mk (List.ext_getElem (by simpa using hlen) fun i hi hi' => ?_)
  rw [List.getElem_map]
  exact checkSsa_erase_eq (hall i (by simpa using hi) (by simpa using hi'))

/-- Acceptance of a program establishes that every function is well formed. -/
theorem checkSsaProg_wellFormed [DecidableEq R] {target : RTL.Prog R} {spec : RTL.SSA.Prog R}
    (h : checkSsaProg target spec = .ok ()) : spec.WellFormed := by
  obtain ⟨hlen, hall⟩ := checkSsaProg_inv h
  intro fn hfn
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfn
  exact checkSsa_wellFormed (hall i hi (by omega))

/-- Acceptance of a program establishes that every transfer of every function
is sequentializable. -/
theorem checkSsaProg_sequential [DecidableEq R] {target : RTL.Prog R} {spec : RTL.SSA.Prog R}
    (h : checkSsaProg target spec = .ok ()) :
    ∀ fn ∈ spec.funcs, SequentialTransfers fn := by
  obtain ⟨hlen, hall⟩ := checkSsaProg_inv h
  intro fn hfn
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfn
  exact checkSsa_sequential (hall i hi (by omega))

/-! ## The erased state

The simulation relation is a *function*: an SSA state determines the RTL state
it corresponds to, because erasure changes no value and no memory — only the
program point, from a block label and an index into that block's operations to
the node the pair was laid out at. -/

/-- The node a program point maps to. -/
def nodeOf (p : RTL.SSA.Prog R) (pt : RTL.SSA.Point) : Nat :=
  match p.func? pt.func with
  | some fn => startOf fn pt.label + pt.index
  | none => 0

/-- A program point of the erased program. -/
def erasePoint (p : RTL.SSA.Prog R) (pt : RTL.SSA.Point) : RTL.Point :=
  ⟨pt.func, nodeOf p pt⟩

/-- A suspended caller of the erased program. -/
def eraseAct (p : RTL.SSA.Prog R) (a : RTL.SSA.Activation R) : RTL.Activation R :=
  ⟨erasePoint p a.point, a.frame⟩

/-- An SSA machine state as an RTL machine state. -/
def eraseState (p : RTL.SSA.Prog R) (s : RTL.SSA.State R) : RTL.State R :=
  ⟨erasePoint p s.point, s.frame, s.stack.map (eraseAct p), s.mem⟩

/-- Erasure keeps the function table, function by function. -/
@[simp] theorem eraseProg_func? (p : RTL.SSA.Prog R) (f : RTL.FuncId) :
    (eraseProg p).func? f = (p.func? f).map erase := by
  simp [eraseProg, RTL.Prog.func?, RTL.SSA.Prog.func?, List.getElem?_map]

/-! ## Reading the erased code

Every fetch below is `fetch_of_drop` applied to a `drop` of the erased code. The
`drop`s compose: `erase_code_drop` opens a block, and dropping further inside it
stays inside it. -/

/-- An instruction at a node, from a `drop` of the code that exposes it. -/
theorem fetch_of_drop {q : RTL.Prog R} {f : RTL.FuncId} {fn : RTL.Func R} {n : Nat}
    (hf : q.func? f = some fn) {x : RTL.Instr R} {rest : List (RTL.Instr R)}
    (h : fn.code.drop n = x :: rest) : q.fetch ⟨f, n⟩ = some x := by
  have : fn.code[n]? = some x := by
    have := congrArg (fun l => l[0]?) h
    simpa [List.getElem?_drop] using this
  simp [RTL.Prog.fetch, RTL.Prog.instr?, hf, RTL.Func.instr?, this]

/-- An instruction at a node, from the head of a `drop` of the code. -/
theorem fetch_of_head? {q : RTL.Prog R} {f : RTL.FuncId} {fn : RTL.Func R} {n : Nat}
    (hf : q.func? f = some fn) {x : RTL.Instr R}
    (h : (fn.code.drop n).head? = some x) : q.fetch ⟨f, n⟩ = some x := by
  have : fn.code[n]? = some x := by simpa [List.getElem?_drop] using h
  simp [RTL.Prog.fetch, RTL.Prog.instr?, hf, RTL.Func.instr?, this]

/-- No instruction at a node past the end of the code. -/
theorem fetch_of_le {q : RTL.Prog R} {f : RTL.FuncId} {fn : RTL.Func R} {n : Nat}
    (hf : q.func? f = some fn) (h : fn.code.length ≤ n) : q.fetch ⟨f, n⟩ = none := by
  simp [RTL.Prog.fetch, RTL.Prog.instr?, hf, RTL.Func.instr?, List.getElem?_eq_none h]

/-- The code of an erased function, read from inside one block. -/
theorem erase_drop_in_block {fn : RTL.SSA.Func R} {l : Nat} {b : RTL.SSA.Block R}
    (hb : fn.block? l = some b) (m : Nat) :
    ∃ rest, (erase fn).code.drop (startOf fn l + m) =
      (blockCode fn (startOf fn l) b).drop m ++ rest := by
  have hl : l < fn.blocks.length := by
    by_contra hc
    rw [RTL.SSA.Func.block?, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hb
    exact absurd hb (by simp)
  have hbl : fn.blocks[l] = b := by
    rw [RTL.SSA.Func.block?, List.getElem?_eq_getElem hl] at hb
    exact Option.some.inj hb
  rw [← List.drop_drop, erase_code_drop fn hl, hbl, List.drop_append]
  exact ⟨_, rfl⟩

/-- An operation of a block, at the node it was laid out at. -/
theorem opsCode_drop_at {base : Nat} (os : List (RTL.SSA.Op R)) (i : Nat) (h : i < os.length) :
    (opsCode base os).drop i =
      instrOfOp (base + i + 1) os[i] :: opsCode (base + i + 1) (os.drop (i + 1)) := by
  rw [opsCode_drop base os i, List.drop_eq_getElem_cons h, opsCode]

/-- A move of a transfer, at the node it was laid out at. -/
theorem movesCode_drop (base : Nat) : ∀ (ms : List (R × R)) (i : Nat),
    (movesCode base ms).drop i = movesCode (base + i) (ms.drop i)
  | ms, 0 => by simp
  | [], _ + 1 => by simp [movesCode]
  | (d, src) :: rest, i + 1 => by
    have hb : base + 1 + i = base + (i + 1) := by omega
    rw [movesCode, List.drop_succ_cons, movesCode_drop (base + 1) rest i, List.drop_succ_cons, hb]

/-! ## Sequential moves

The one place where the erasure is not a renaming: a transfer writes its
target's parameters simultaneously and the erased code writes them one at a
time. `applyMoves` is what the erased code computes and `Frame.writeAll` is what
the transfer means; `applyMoves_eq_writeAll` is that they agree exactly when
`sequentialMoves` holds. -/

/-- The frame after performing a list of moves in order, reading each source
after the earlier destinations have been written. -/
def applyMoves [DecidableEq R] (fr : RTL.Frame R) : List (R × R) → Option (RTL.Frame R)
  | [] => some fr
  | (d, src) :: rest => (fr.get src).bind fun x => applyMoves (fr.set d x) rest

/-- Reading a list of registers, one at a time. -/
theorem readAll_cons [DecidableEq R] (fr : RTL.Frame R) (a : R) (as : List R) :
    fr.readAll (a :: as) = (fr.get a).bind fun v => (fr.readAll as).map (v :: ·) := by
  simp [RTL.Frame.readAll, List.mapM_cons]
  cases fr.get a <;> simp
  cases List.mapM fr.get as <;> simp

/-- Writing a register no later read mentions changes no later read. -/
theorem readAll_set_of_not_mem [DecidableEq R] (fr : RTL.Frame R) {r : R} (w : Word)
    {as : List R} (h : r ∉ as) : (fr.set r w).readAll as = fr.readAll as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have hne : a ≠ r := by rintro rfl; exact h List.mem_cons_self
    have hget : (fr.set r w).get a = fr.get a := by simp [hne]
    rw [readAll_cons, readAll_cons, hget, ih (fun hm => h (List.mem_cons_of_mem a hm))]

/-- **The sequential moves compute the simultaneous write.** The hypothesis is
`sequentialMoves`, and it is used exactly once per move: the destination just
written must not be read by any later move. -/
theorem applyMoves_eq_writeAll [DecidableEq R] : ∀ (ps as : List R) (vals : List Word)
    (fr : RTL.Frame R), sequentialMoves ps as = true → ps.length = as.length →
    fr.readAll as = some vals → applyMoves fr (List.zipWith Prod.mk ps as) = fr.writeAll ps vals
  | [], [], vals, fr, _, _, hread => by
    have hv : vals = [] := by
      have he : fr.readAll ([] : List R) = some [] := rfl
      rw [he] at hread
      exact (Option.some.inj hread).symm
    subst hv
    simp [applyMoves, RTL.Frame.writeAll]
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen
  | p :: ps, a :: as, vals, fr, hseq, hlen, hread => by
    rw [readAll_cons] at hread
    cases hget : fr.get a with
    | none => rw [hget] at hread; simp at hread
    | some v =>
      rw [hget] at hread
      cases hrest : fr.readAll as with
      | none => rw [hrest] at hread; simp at hread
      | some vs =>
        rw [hrest] at hread
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hread
        subst hread
        simp only [sequentialMoves, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, List.elem_eq_mem] at hseq
        rw [List.zipWith_cons_cons, applyMoves, hget, Option.bind_some, RTL.Frame.writeAll]
        refine applyMoves_eq_writeAll ps as vs (fr.set p v) hseq.2 (by simpa using hlen) ?_
        rw [readAll_set_of_not_mem fr v hseq.1, hrest]

/-- **The erased code performs the moves.** -/
theorem steps_movesCode {q : RTL.Prog R} [DecidableEq R] {f : RTL.FuncId} {fn : RTL.Func R}
    (hf : q.func? f = some fn) : ∀ (ms : List (R × R)) (base : Nat) (fr fr' : RTL.Frame R)
      (stack : List (RTL.Activation R)) (mem : Memory),
      (∃ rest, fn.code.drop base = movesCode base ms ++ rest) →
      applyMoves fr ms = some fr' →
      RTL.Steps q ⟨⟨f, base⟩, fr, stack, mem⟩ ⟨⟨f, base + ms.length⟩, fr', stack, mem⟩
  | [], base, fr, fr', stack, mem, _, happ => by
    simp only [applyMoves, Option.some.injEq] at happ
    subst happ
    simpa using Relation.ReflTransGen.refl
  | (d, src) :: rest, base, fr, fr', stack, mem, ⟨tail, hcode⟩, happ => by
    simp only [applyMoves] at happ
    cases hget : fr.get src with
    | none => rw [hget] at happ; simp at happ
    | some x =>
      rw [hget, Option.bind_some] at happ
      have hfetch : q.fetch ⟨f, base⟩ = some (RTL.Instr.move d src (base + 1)) :=
        fetch_of_drop hf (by rw [hcode, movesCode, List.cons_append])
      have hstep : RTL.Step q ⟨⟨f, base⟩, fr, stack, mem⟩
          ⟨⟨f, base + 1⟩, fr.set d x, stack, mem⟩ := by
        show RTL.step q _ = _
        simp [RTL.step, hfetch, hget, RTL.Point.at]
      have hcode' : ∃ tl, fn.code.drop (base + 1) = movesCode (base + 1) rest ++ tl := by
        refine ⟨tail, ?_⟩
        have hsplit : fn.code.drop (base + 1) = (fn.code.drop base).drop 1 := by
          rw [List.drop_drop]
        rw [hsplit, hcode, movesCode, List.cons_append]
        simp
      have htail := steps_movesCode hf rest (base + 1) (fr.set d x) fr' stack mem hcode' happ
      have harith : base + 1 + rest.length = base + ((d, src) :: rest).length := by
        simp only [List.length_cons]; omega
      rw [harith] at htail
      exact Relation.ReflTransGen.head hstep htail

/-- **A move whose source was never written gets stuck**, after performing the
moves before it. -/
theorem steps_movesCode_stuck {q : RTL.Prog R} [DecidableEq R] {f : RTL.FuncId}
    {fn : RTL.Func R} (hf : q.func? f = some fn) :
    ∀ (ms : List (R × R)) (base : Nat) (fr : RTL.Frame R)
      (stack : List (RTL.Activation R)) (mem : Memory),
      (∃ rest, fn.code.drop base = movesCode base ms ++ rest) → applyMoves fr ms = none →
      ∃ t, RTL.Steps q ⟨⟨f, base⟩, fr, stack, mem⟩ t ∧ RTL.step q t = .stuck
  | [], _, _, _, _, _, happ => by simp [applyMoves] at happ
  | (d, src) :: rest, base, fr, stack, mem, ⟨tail, hcode⟩, happ => by
    have hfetch : q.fetch ⟨f, base⟩ = some (RTL.Instr.move d src (base + 1)) :=
      fetch_of_drop hf (by rw [hcode, movesCode, List.cons_append])
    simp only [applyMoves] at happ
    cases hget : fr.get src with
    | none =>
      refine ⟨⟨⟨f, base⟩, fr, stack, mem⟩, .refl, ?_⟩
      simp [RTL.step, hfetch, hget]
    | some x =>
      rw [hget, Option.bind_some] at happ
      have hstep : RTL.Step q ⟨⟨f, base⟩, fr, stack, mem⟩
          ⟨⟨f, base + 1⟩, fr.set d x, stack, mem⟩ := by
        show RTL.step q _ = _
        simp [RTL.step, hfetch, hget, RTL.Point.at]
      have hcode' : ∃ tl, fn.code.drop (base + 1) = movesCode (base + 1) rest ++ tl := by
        refine ⟨tail, ?_⟩
        have hsplit : fn.code.drop (base + 1) = (fn.code.drop base).drop 1 := by
          rw [List.drop_drop]
        rw [hsplit, hcode, movesCode, List.cons_append]
        simp
      obtain ⟨t, ht, hst⟩ := steps_movesCode_stuck hf rest (base + 1) (fr.set d x) stack mem
        hcode' happ
      exact ⟨t, Relation.ReflTransGen.head hstep ht, hst⟩

/-! ## What a fetch of each program finds -/

/-- The function, block and operation behind a successful SSA fetch of an
operation. -/
theorem ssa_fetch_op {p : RTL.SSA.Prog R} {pt : RTL.SSA.Point} {o : RTL.SSA.Op R}
    (h : p.fetch pt = some (.op o)) :
    ∃ fn b, p.func? pt.func = some fn ∧ fn.block? pt.label = some b ∧
      ∃ hi : pt.index < b.ops.length, b.ops[pt.index] = o := by
  rw [RTL.SSA.Prog.fetch, RTL.SSA.Prog.block?] at h
  cases hfn : p.func? pt.func with
  | none => simp only [hfn] at h; simp at h
  | some fn =>
    simp only [hfn, Option.bind_some] at h
    cases hb : fn.block? pt.label with
    | none => simp only [hb] at h; simp at h
    | some b =>
      simp only [hb, Option.bind_some] at h
      cases ho : b.ops[pt.index]? with
      | none => simp only [ho] at h; split at h <;> simp at h
      | some o' =>
        simp only [ho] at h
        obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp ho
        refine ⟨fn, b, rfl, hb, hlt, ?_⟩
        simp only [Option.some.injEq, RTL.SSA.Code.op.injEq] at h
        exact hget.trans h

/-- The function and block behind a successful SSA fetch of a terminator. -/
theorem ssa_fetch_term {p : RTL.SSA.Prog R} {pt : RTL.SSA.Point} {t : RTL.SSA.Term R}
    (h : p.fetch pt = some (.term t)) :
    ∃ fn b, p.func? pt.func = some fn ∧ fn.block? pt.label = some b ∧
      pt.index = b.ops.length ∧ b.term = t := by
  rw [RTL.SSA.Prog.fetch, RTL.SSA.Prog.block?] at h
  cases hfn : p.func? pt.func with
  | none => simp only [hfn] at h; simp at h
  | some fn =>
    simp only [hfn, Option.bind_some] at h
    cases hb : fn.block? pt.label with
    | none => simp only [hb] at h; simp at h
    | some b =>
      simp only [hb, Option.bind_some] at h
      cases ho : b.ops[pt.index]? with
      | none =>
        simp only [ho] at h
        by_cases hidx : pt.index = b.ops.length
        · simp only [hidx, reduceIte, Option.some.injEq, RTL.SSA.Code.term.injEq] at h
          exact ⟨fn, b, rfl, hb, hidx, h⟩
        · simp only [hidx, reduceIte] at h
          simp at h
      | some o => simp only [ho] at h; simp at h

/-- The erased instruction at the node an SSA operation was laid out at. -/
theorem erase_fetch_op {p : RTL.SSA.Prog R} {f : RTL.FuncId} {fn : RTL.SSA.Func R}
    {l : Nat} {b : RTL.SSA.Block R} {i : Nat} (hf : p.func? f = some fn)
    (hb : fn.block? l = some b) (hi : i < b.ops.length) :
    (eraseProg p).fetch ⟨f, startOf fn l + i⟩ =
      some (instrOfOp (startOf fn l + i + 1) b.ops[i]) := by
  obtain ⟨rest, hd⟩ := erase_drop_in_block hb i
  have hzero : i - (opsCode (startOf fn l) b.ops).length = 0 := by
    rw [opsCode_length]; omega
  refine fetch_of_head? (fn := erase fn) (by simp [hf]) ?_
  rw [hd, blockCode, List.drop_append, hzero, opsCode_drop_at b.ops i hi]
  simp

/-- The erased code from the node a block's terminator was laid out at. -/
theorem erase_drop_term {fn : RTL.SSA.Func R} {l : Nat} {b : RTL.SSA.Block R}
    (hb : fn.block? l = some b) (k : Nat) :
    ∃ rest, (erase fn).code.drop (startOf fn l + b.ops.length + k) =
      (termCode fn (startOf fn l + b.ops.length) b.term).drop k ++ rest := by
  obtain ⟨rest, hd⟩ := erase_drop_in_block hb (b.ops.length + k)
  refine ⟨rest, ?_⟩
  rw [show startOf fn l + b.ops.length + k = startOf fn l + (b.ops.length + k) from by omega, hd,
    blockCode, List.drop_append, opsCode_length,
    show b.ops.length + k - b.ops.length = k from by omega,
    List.drop_of_length_le (by rw [opsCode_length]; omega), List.nil_append]

/-! ## Entering a function -/

/-- The entry block of a well-formed function exists and its parameters are the
erased function's. -/
theorem erase_entry_block {p : RTL.SSA.Prog R} [DecidableEq R] (hwf : p.WellFormed)
    {f : RTL.FuncId} {fn : RTL.SSA.Func R} (hf : p.func? f = some fn) :
    ∃ b, fn.block? fn.entry = some b ∧ (erase fn).params = b.params := by
  have hmem : fn ∈ p.funcs := by
    rw [RTL.SSA.Prog.func?] at hf
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hf
    exact heq ▸ List.getElem_mem hlt
  have hsig := (hwf fn hmem).sig
  obtain ⟨hlt, -, -⟩ := hsig
  have hb : fn.block? fn.entry = some fn.blocks[fn.entry] :=
    List.getElem?_eq_getElem hlt
  exact ⟨_, hb, by simp [erase, paramsOf, hb]⟩

/-- **Entering a function is the same in both programs.** -/
theorem erase_enter {p : RTL.SSA.Prog R} [DecidableEq R] (hwf : p.WellFormed)
    {g : RTL.FuncId} {vals : List Word} {pt : RTL.SSA.Point} {fr : RTL.Frame R}
    (h : p.enter g vals = some (pt, fr)) :
    (eraseProg p).enter g vals = some (erasePoint p pt, fr) := by
  rw [RTL.SSA.Prog.enter] at h
  cases hf : p.func? g with
  | none => rw [hf] at h; simp at h
  | some fn =>
    rw [hf] at h
    simp only [Option.bind_some] at h
    obtain ⟨b, hb, hpar⟩ := erase_entry_block hwf hf
    rw [hb] at h
    simp only [Option.bind_some] at h
    cases hw : RTL.Frame.empty.writeAll b.params vals with
    | none => rw [hw] at h; simp at h
    | some fr' =>
      rw [hw] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hpt, hfr⟩ := h
      subst hfr
      rw [RTL.Prog.enter, eraseProg_func?, hf, Option.map_some, Option.bind_some, hpar, hw,
        Option.map_some]
      congr 1
      rw [← hpt]
      simp [erasePoint, nodeOf, hf, erase]

/-- **Failing to enter a function is the same in both programs.** -/
theorem erase_enter_none {p : RTL.SSA.Prog R} [DecidableEq R] (hwf : p.WellFormed)
    {g : RTL.FuncId} {vals : List Word} (h : p.enter g vals = none) :
    (eraseProg p).enter g vals = none := by
  rw [RTL.SSA.Prog.enter] at h
  cases hf : p.func? g with
  | none => rw [RTL.Prog.enter, eraseProg_func?, hf]; rfl
  | some fn =>
    rw [hf] at h
    simp only [Option.bind_some] at h
    obtain ⟨b, hb, hpar⟩ := erase_entry_block hwf hf
    rw [hb] at h
    simp only [Option.bind_some, Option.map_eq_none_iff] at h
    rw [RTL.Prog.enter, eraseProg_func?, hf, Option.map_some, Option.bind_some, hpar, h]
    rfl

/-! ## One operation -/

/-- **An erased operation does what the operation did.** The two `exec`
definitions agree constructor by constructor; `call` is excluded because it is
not straight-line and `RTL.SSA.Op.exec` returns `none` on it. -/
theorem step_instrOfOp {q : RTL.Prog R} [DecidableEq R] {t : RTL.State R} {o : RTL.SSA.Op R}
    {n : Nat} (hf : q.fetch t.point = some (instrOfOp n o))
    (hne : ∀ g args results, o ≠ .call g args results) :
    RTL.step q t =
      (match o.exec t.frame t.mem with
        | some (fr, m) => .running { t with point := t.point.at n, frame := fr, mem := m }
        | none => .stuck) := by
  cases o with
  | const d v => simp [RTL.step, hf, instrOfOp, RTL.SSA.Op.exec]
  | move d src =>
    simp only [RTL.step, hf, instrOfOp, RTL.SSA.Op.exec]
    cases t.frame.get src <;> simp
  | unary op d src =>
    simp only [RTL.step, hf, instrOfOp, RTL.SSA.Op.exec]
    cases t.frame.get src <;> simp
  | binary op d a b =>
    simp only [RTL.step, hf, instrOfOp, RTL.SSA.Op.exec]
    cases t.frame.get a <;> cases t.frame.get b <;> simp
    rename_i x y
    cases op.eval x y <;> simp
  | load w e d base off =>
    simp only [RTL.step, hf, instrOfOp, RTL.SSA.Op.exec]
    cases t.frame.get base <;> simp
    rename_i addr
    cases t.mem.load w e (addr.toNat + off) <;> simp
  | store w base off src =>
    simp only [RTL.step, hf, instrOfOp, RTL.SSA.Op.exec]
    cases t.frame.get base <;> cases t.frame.get src <;> simp
    rename_i addr x
    cases t.mem.store w (addr.toNat + off) x <;> simp
  | call g args results => exact absurd rfl (hne g args results)

/-! ## The moves, once more, as a single `bind` -/

/-- **The sequential moves compute the simultaneous write, failures
included.** -/
theorem applyMoves_eq_bind [DecidableEq R] : ∀ (ps as : List R) (fr : RTL.Frame R),
    sequentialMoves ps as = true → ps.length = as.length →
    applyMoves fr (List.zipWith Prod.mk ps as) = (fr.readAll as).bind (fr.writeAll ps)
  | [], [], fr, _, _ => by
    have he : fr.readAll ([] : List R) = some [] := rfl
    simp [applyMoves, he, RTL.Frame.writeAll]
  | [], _ :: _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, hlen => by simp at hlen
  | p :: ps, a :: as, fr, hseq, hlen => by
    simp only [sequentialMoves, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, List.elem_eq_mem] at hseq
    rw [List.zipWith_cons_cons, applyMoves, readAll_cons]
    cases hget : fr.get a with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      rw [applyMoves_eq_bind ps as (fr.set p v) hseq.2 (by simpa using hlen),
        readAll_set_of_not_mem fr v hseq.1]
      cases hrest : fr.readAll as with
      | none => simp
      | some vs => simp [RTL.Frame.writeAll]

/-- `ArgsMatch` in the form the simulation uses: the target of a transfer has
as many parameters as the transfer supplies arguments. -/
theorem paramsOf_length_eq {fn : RTL.SSA.Func R} (h : fn.ArgsMatch) {b : RTL.SSA.Block R}
    (hb : b ∈ fn.blocks) {t : RTL.SSA.Label} {as : List R} (hta : (t, as) ∈ b.term.args) :
    (paramsOf fn t).length = as.length := by
  rw [RTL.SSA.Func.ArgsMatch, RTL.SSA.Func.argsMatch, List.all_eq_true] at h
  have hb' := h b (by simpa using hb)
  rw [List.all_eq_true] at hb'
  have hta' := hb' (t, as) (by simpa using hta)
  simp only at hta'
  cases hbt : fn.block? t with
  | none => rw [hbt] at hta'; simp at hta'
  | some bt =>
    rw [hbt] at hta'
    simp only [beq_iff_eq] at hta'
    simp [paramsOf, hbt, hta']

/-- The second arm of an erased `cond`: everything after the branch and the
first edge's chunk. -/
theorem termCode_cond_drop_right (fn : RTL.SSA.Func R) (base : Nat) (c : R)
    (t₁ t₂ : RTL.SSA.Label) (a₁ a₂ : List R) :
    (termCode fn base (.cond c t₁ a₁ t₂ a₂)).drop (1 + (transferPairs fn t₁ a₁).length + 1) =
      transferCode fn (base + 1 + (transferPairs fn t₁ a₁).length + 1) t₂ a₂ := by
  have hlen : 1 + (transferPairs fn t₁ a₁).length + 1
      = (transferCode fn (base + 1) t₁ a₁).length + 1 := by
    rw [transferCode_length]; omega
  rw [termCode, hlen, List.drop_succ_cons, List.drop_left]

/-- The first arm of an erased `cond`: everything after the branch. -/
theorem termCode_cond_drop_left (fn : RTL.SSA.Func R) (base : Nat) (c : R)
    (t₁ t₂ : RTL.SSA.Label) (a₁ a₂ : List R) :
    (termCode fn base (.cond c t₁ a₁ t₂ a₂)).drop 1 =
      transferCode fn (base + 1) t₁ a₁ ++
        transferCode fn (base + 1 + (transferPairs fn t₁ a₁).length + 1) t₂ a₂ := by
  simp [termCode]

/-! ## The reachability invariant

Erasure is faithful at the program points the machine can actually be at, and
only there. An index past a block's operations fetches nothing in the SSA
program — it is stuck — but lands inside the terminator's expansion in the
erased one, where there is a move to execute. Such a point is never reached:
transfers and calls land at index `0`, and an operation advances to at most the
terminator. `StateOk` is that fact, and it is carried by the simulation relation
rather than assumed. -/

/-- A program point at which the machine can be. -/
def PointOk (p : RTL.SSA.Prog R) (pt : RTL.SSA.Point) : Prop :=
  ∀ fn, p.func? pt.func = some fn → ∀ b, fn.block? pt.label = some b → pt.index ≤ b.ops.length

/-- The machine is at a point it can be at, and every suspended caller is
suspended at a `call`. -/
def StateOk [DecidableEq R] (p : RTL.SSA.Prog R) (s : RTL.SSA.State R) : Prop :=
  PointOk p s.point ∧
    ∀ a ∈ s.stack, ∃ g args results, p.fetch a.point = some (.op (.call g args results))

/-- The erased instruction a suspended caller is suspended at, and where it
resumes. -/
theorem erase_fetch_act {p : RTL.SSA.Prog R} {pt : RTL.SSA.Point} {g : RTL.FuncId}
    {cargs cres : List R} (h : p.fetch pt = some (.op (.call g cargs cres))) :
    (eraseProg p).fetch (erasePoint p pt) =
        some (.call g cargs cres (nodeOf p pt + 1)) ∧
      nodeOf p pt.next = nodeOf p pt + 1 ∧
      ∃ fn b, p.func? pt.func = some fn ∧ fn.block? pt.label = some b ∧
        pt.index < b.ops.length := by
  obtain ⟨fn, b, hfn, hb, hi, hops⟩ := ssa_fetch_op h
  have hnode : nodeOf p pt = startOf fn pt.label + pt.index := by simp [nodeOf, hfn]
  have hnext : nodeOf p pt.next = startOf fn pt.label + pt.index + 1 := by
    simp only [nodeOf, hfn, RTL.SSA.Point.next]
    omega
  refine ⟨?_, ?_, fn, b, hfn, hb, hi⟩
  · have := erase_fetch_op hfn hb hi
    rw [hops] at this
    rw [erasePoint, hnode, hnext] at *
    simpa [instrOfOp] using this
  · rw [hnext, hnode]

/-- Entering a function lands at the first operation of its entry block. -/
theorem enter_index {p : RTL.SSA.Prog R} [DecidableEq R] {g : RTL.FuncId} {vals : List Word}
    {pt : RTL.SSA.Point} {fr : RTL.Frame R} (h : p.enter g vals = some (pt, fr)) :
    pt.index = 0 := by
  rw [RTL.SSA.Prog.enter] at h
  cases hf : p.func? g with
  | none => simp only [hf] at h; simp at h
  | some fn =>
    simp only [hf, Option.bind_some] at h
    cases hb : fn.block? fn.entry with
    | none => simp only [hb] at h; simp at h
    | some b =>
      simp only [hb, Option.bind_some] at h
      cases hw : RTL.Frame.empty.writeAll b.params vals with
      | none => simp only [hw] at h; simp at h
      | some fr' =>
        simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]

/-! ## One transfer

`steps_transfer` is the jump and the `cond` arms of the simulation at once: from
the first node of an edge's move chunk, the erased code performs the moves and
jumps to the target's first node. -/

/-- **The erased code performs one transfer.** -/
theorem steps_transfer {p : RTL.SSA.Prog R} [DecidableEq R] {f : RTL.FuncId}
    {fn : RTL.SSA.Func R} (hfn : p.func? f = some fn) {t : RTL.SSA.Label} {as : List R}
    {cbase : Nat} (hcode : ∃ rest, (erase fn).code.drop cbase = transferCode fn cbase t as ++ rest)
    (hseq : sequentialMoves (paramsOf fn t) as = true)
    (hlen : (paramsOf fn t).length = as.length) {fr fr' : RTL.Frame R} {vals : List Word}
    (hv : fr.readAll as = some vals) (hw : fr.writeAll (paramsOf fn t) vals = some fr')
    (stack : List (RTL.Activation R)) (mem : Memory) :
    Relation.TransGen (RTL.Step (eraseProg p)) ⟨⟨f, cbase⟩, fr, stack, mem⟩
      ⟨⟨f, startOf fn t⟩, fr', stack, mem⟩ := by
  obtain ⟨rest, hd⟩ := hcode
  have hq : (eraseProg p).func? f = some (erase fn) := by simp [hfn]
  have happ : applyMoves fr (transferPairs fn t as) = some fr' := by
    rw [transferPairs, applyMoves_eq_bind _ _ fr hseq hlen, hv, Option.bind_some, hw]
  have hmoves := steps_movesCode (q := eraseProg p) hq (transferPairs fn t as) cbase fr fr'
    stack mem ⟨_, by rw [hd, transferCode, List.append_assoc]⟩ happ
  have hjump : (eraseProg p).fetch ⟨f, cbase + (transferPairs fn t as).length⟩ =
      some (RTL.Instr.jump (startOf fn t)) := by
    refine fetch_of_head? hq ?_
    rw [← List.drop_drop, hd, transferCode, List.append_assoc, List.drop_append,
      List.drop_of_length_le (by simp), movesCode_length]
    simp
  refine Relation.TransGen.tail' hmoves ?_
  show RTL.step (eraseProg p) _ = _
  simp [RTL.step, hjump, RTL.Point.at]

/-! ## The simulation -/

/-- **One SSA step is one or more steps of the erased program**, and the
reachability invariant is preserved. This is the simulation the rung rests on.
-/
theorem erase_sim [DecidableEq R] {p : RTL.SSA.Prog R} (hwf : p.WellFormed)
    (hsq : ∀ fn ∈ p.funcs, SequentialTransfers fn) {s s' : RTL.SSA.State R}
    (hok : StateOk p s) (h : RTL.SSA.Step p s s') :
    StateOk p s' ∧
      Relation.TransGen (RTL.Step (eraseProg p)) (eraseState p s) (eraseState p s') := by
  have htr := RTL.SSA.Transition.of_step h (by simp)
  cases htr with
  | @op o fr m hf he =>
    obtain ⟨fn, b, hfn, hb, hi, hops⟩ := ssa_fetch_op hf
    have hnode : nodeOf p s.point = startOf fn s.point.label + s.point.index := by
      simp [nodeOf, hfn]
    have hnext : nodeOf p s.point.next = startOf fn s.point.label + s.point.index + 1 := by
      simp only [nodeOf, hfn, RTL.SSA.Point.next]
      omega
    have hne : ∀ g args results, o ≠ RTL.SSA.Op.call g args results := by
      rintro g args results rfl
      simp [RTL.SSA.Op.exec] at he
    have hfetch : (eraseProg p).fetch (eraseState p s).point =
        some (instrOfOp (nodeOf p s.point + 1) o) := by
      have := erase_fetch_op hfn hb hi
      rw [hops] at this
      simpa [eraseState, erasePoint, hnode] using this
    refine ⟨⟨fun fn' hfn' b' hb' => ?_, hok.2⟩, Relation.TransGen.single ?_⟩
    · simp only [RTL.SSA.Point.next] at hfn' hb'
      rw [hfn] at hfn'
      obtain rfl := Option.some.inj hfn'
      rw [hb] at hb'
      obtain rfl := Option.some.inj hb'
      show s.point.index + 1 ≤ b.ops.length
      omega
    · show RTL.step (eraseProg p) _ = _
      rw [step_instrOfOp hfetch hne]
      show (match RTL.SSA.Op.exec o s.frame s.mem with
        | some (fr, m) => _ | none => _) = _
      rw [he]
      simp [eraseState, erasePoint, RTL.Point.at, hnext, hnode]
  | @call g args results vals ptc frc hf ha he =>
    obtain ⟨hfetch, hnext, fn, b, hfn, hb, hi⟩ := erase_fetch_act hf
    refine ⟨⟨?_, ?_⟩, Relation.TransGen.single ?_⟩
    · intro fn' hfn' b' hb'
      rw [enter_index he]
      omega
    · intro a hamem
      rcases List.mem_cons.mp hamem with rfl | hamem
      · exact ⟨g, args, results, hf⟩
      · exact hok.2 a hamem
    · show RTL.step (eraseProg p) _ = _
      have hfr : (eraseState p s).frame = s.frame := rfl
      simp only [RTL.step, show (eraseState p s).point = erasePoint p s.point from rfl, hfetch,
        hfr, ha, erase_enter hwf he]
      simp [eraseState, eraseAct]
  | @jump t as vals bt frt hf hv hbt hw =>
    obtain ⟨fn, blk, hfn, hblk, hidx, hterm⟩ := ssa_fetch_term hf
    have hbtfn : fn.block? t = some bt := by
      rw [RTL.SSA.Prog.block?, hfn] at hbt
      simpa using hbt
    have hpar : paramsOf fn t = bt.params := by simp [paramsOf, hbtfn]
    have hmem : blk ∈ fn.blocks := by
      rw [RTL.SSA.Func.block?] at hblk
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hblk
      exact heq ▸ List.getElem_mem hlt
    have hfnmem : fn ∈ p.funcs := by
      rw [RTL.SSA.Prog.func?] at hfn
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hfn
      exact heq ▸ List.getElem_mem hlt
    have hta : (t, as) ∈ blk.term.args := by rw [hterm]; simp [RTL.SSA.Term.args]
    have hseq : sequentialMoves (paramsOf fn t) as = true :=
      hsq fn hfnmem blk hmem (t, as) hta
    have hlen : (paramsOf fn t).length = as.length :=
      paramsOf_length_eq (hwf fn hfnmem).argsMatch hmem hta
    have hnode : nodeOf p s.point = startOf fn s.point.label + blk.ops.length := by
      simp [nodeOf, hfn, hidx]
    obtain ⟨rest, hd⟩ := erase_drop_term hblk 0
    rw [hterm] at hd
    refine ⟨⟨fun fn' hfn' b' hb' => by simp, hok.2⟩, ?_⟩
    have := steps_transfer (p := p) hfn (t := t) (as := as)
      (cbase := startOf fn s.point.label + blk.ops.length)
      ⟨rest, by simpa [termCode] using hd⟩ hseq hlen hv (by rw [hpar]; exact hw)
      ((eraseState p s).stack) s.mem
    simpa [eraseState, erasePoint, nodeOf, hfn, hidx] using this
  | @cond c t₁ t₂ a₁ a₂ x vals bt frt hf hc hv hbt hw =>
    obtain ⟨fn, blk, hfn, hblk, hidx, hterm⟩ := ssa_fetch_term hf
    have hfnmem : fn ∈ p.funcs := by
      rw [RTL.SSA.Prog.func?] at hfn
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hfn
      exact heq ▸ List.getElem_mem hlt
    have hmem : blk ∈ fn.blocks := by
      rw [RTL.SSA.Func.block?] at hblk
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hblk
      exact heq ▸ List.getElem_mem hlt
    have hnode : nodeOf p s.point = startOf fn s.point.label + blk.ops.length := by
      simp [nodeOf, hfn, hidx]
    have hq : (eraseProg p).func? s.point.func = some (erase fn) := by simp [hfn]
    have hfetch : (eraseProg p).fetch (eraseState p s).point =
        some (RTL.Instr.cond c (startOf fn s.point.label + blk.ops.length + 1)
          (startOf fn s.point.label + blk.ops.length + 1 +
            (transferPairs fn t₁ a₁).length + 1)) := by
      refine fetch_of_head? hq ?_
      obtain ⟨rest, hd⟩ := erase_drop_term hblk 0
      rw [hterm] at hd
      show ((erase fn).code.drop (nodeOf p s.point)).head? = _
      rw [hnode, show startOf fn s.point.label + blk.ops.length
        = startOf fn s.point.label + blk.ops.length + 0 from rfl, hd]
      simp [termCode]
    -- one argument, applied to whichever edge the branch takes
    have key : ∀ (tt : RTL.SSA.Label) (aa : List R) (cb : Nat), (tt, aa) ∈ blk.term.args →
        s.frame.readAll aa = some vals → fn.block? tt = some bt →
        (∃ rest, (erase fn).code.drop cb = transferCode fn cb tt aa ++ rest) →
        RTL.Step (eraseProg p) (eraseState p s)
          ⟨⟨s.point.func, cb⟩, s.frame, (eraseState p s).stack, s.mem⟩ →
        Relation.TransGen (RTL.Step (eraseProg p)) (eraseState p s)
          ⟨⟨s.point.func, startOf fn tt⟩, frt, (eraseState p s).stack, s.mem⟩ := by
      intro tt aa cb hta hvv hbb hchunk hstep
      have hpar : paramsOf fn tt = bt.params := by rw [paramsOf, hbb]; rfl
      exact Relation.TransGen.head hstep
        (steps_transfer (p := p) hfn hchunk (hsq fn hfnmem blk hmem (tt, aa) hta)
          (paramsOf_length_eq (hwf fn hfnmem).argsMatch hmem hta) hvv (by rw [hpar]; exact hw)
          ((eraseState p s).stack) s.mem)
    refine ⟨⟨fun fn' hfn' b' hb' => by simp, hok.2⟩, ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp only [reduceIte] at hv hbt ⊢
      have hbb : fn.block? t₂ = some bt := by
        rw [RTL.SSA.Prog.block?, hfn] at hbt
        simpa using hbt
      have hchunk : ∃ rest, (erase fn).code.drop
          (startOf fn s.point.label + blk.ops.length + 1 +
            (transferPairs fn t₁ a₁).length + 1) =
          transferCode fn (startOf fn s.point.label + blk.ops.length + 1 +
            (transferPairs fn t₁ a₁).length + 1) t₂ a₂ ++ rest := by
        obtain ⟨rest, hd⟩ := erase_drop_term hblk (1 + (transferPairs fn t₁ a₁).length + 1)
        rw [hterm] at hd
        refine ⟨rest, ?_⟩
        have harith : startOf fn s.point.label + blk.ops.length + 1 +
            (transferPairs fn t₁ a₁).length + 1
          = startOf fn s.point.label + blk.ops.length +
            (1 + (transferPairs fn t₁ a₁).length + 1) := by omega
        rw [harith, hd, termCode_cond_drop_right, harith]
      have := key t₂ a₂ _ (by rw [hterm]; simp [RTL.SSA.Term.args]) hv hbb hchunk (by
        show RTL.step (eraseProg p) _ = _
        simp only [RTL.step, hfetch, show (eraseState p s).frame = s.frame from rfl, hc]
        rfl)
      simpa [eraseState, erasePoint, nodeOf, hfn] using this
    · simp only [hx, reduceIte] at hv hbt ⊢
      have hbb : fn.block? t₁ = some bt := by
        rw [RTL.SSA.Prog.block?, hfn] at hbt
        simpa using hbt
      have hchunk : ∃ rest, (erase fn).code.drop
          (startOf fn s.point.label + blk.ops.length + 1) =
          transferCode fn (startOf fn s.point.label + blk.ops.length + 1) t₁ a₁ ++ rest := by
        obtain ⟨rest, hd⟩ := erase_drop_term hblk 1
        rw [hterm] at hd
        exact ⟨_, by rw [hd, termCode_cond_drop_left, List.append_assoc]⟩
      have := key t₁ a₁ _ (by rw [hterm]; simp [RTL.SSA.Term.args]) hv hbb hchunk (by
        show RTL.step (eraseProg p) _ = _
        simp only [RTL.step, hfetch, show (eraseState p s).frame = s.frame from rfl, hc, hx]
        rfl)
      simpa [eraseState, erasePoint, nodeOf, hfn] using this
  | @ret regs vals a restStack g cargs cres frr hf hv hs ha hw =>
    obtain ⟨fn, blk, hfn, hblk, hidx, hterm⟩ := ssa_fetch_term hf
    obtain ⟨hfetcha, hnexta, fna, ba, hfna, hba, hia⟩ := erase_fetch_act ha
    have hnode : nodeOf p s.point = startOf fn s.point.label + blk.ops.length := by
      simp [nodeOf, hfn, hidx]
    have hfetch : (eraseProg p).fetch (eraseState p s).point = some (RTL.Instr.ret regs) := by
      refine fetch_of_head? (fn := erase fn) (by simp [hfn]) ?_
      obtain ⟨rest, hd⟩ := erase_drop_term hblk 0
      rw [hterm] at hd
      show ((erase fn).code.drop (nodeOf p s.point)).head? = _
      rw [hnode, show startOf fn s.point.label + blk.ops.length
        = startOf fn s.point.label + blk.ops.length + 0 from rfl, hd]
      simp [termCode]
    refine ⟨⟨?_, ?_⟩, Relation.TransGen.single ?_⟩
    · intro fn' hfn' b' hb'
      rw [RTL.SSA.Point.next] at hfn' hb' ⊢
      simp only at hfn' hb' ⊢
      rw [hfna] at hfn'
      obtain rfl := Option.some.inj hfn'
      rw [hba] at hb'
      obtain rfl := Option.some.inj hb'
      omega
    · intro act hact
      refine hok.2 act ?_
      rw [hs]
      exact List.mem_cons_of_mem a hact
    · show RTL.step (eraseProg p) _ = _
      have hstack : (eraseState p s).stack = eraseAct p a :: restStack.map (eraseAct p) := by
        simp [eraseState, hs]
      simp only [RTL.step, hfetch, show (eraseState p s).frame = s.frame from rfl, hv, hstack,
        show (eraseAct p a).point = erasePoint p a.point from rfl, hfetcha,
        show (eraseAct p a).frame = a.frame from rfl, hw]
      simp [eraseState, erasePoint, RTL.Point.at, hnexta]

/-! ## Stopping, and getting stuck

The simulation covers running steps. A whole behaviour also needs the three ways
a run stops: returning, trapping and getting stuck. The first two are one step
each; the third is the only place the reachability invariant is consumed. -/

/-- Reading a list of registers yields as many values as registers. -/
theorem readAll_length [DecidableEq R] {fr : RTL.Frame R} : ∀ {as : List R} {vals : List Word},
    fr.readAll as = some vals → vals.length = as.length
  | [], vals, h => by
    have he : fr.readAll ([] : List R) = some [] := rfl
    rw [he] at h
    simp [← Option.some.inj h]
  | a :: as, vals, h => by
    rw [readAll_cons] at h
    cases hg : fr.get a with
    | none => rw [hg] at h; simp at h
    | some v =>
      rw [hg] at h
      cases hr : fr.readAll as with
      | none => rw [hr] at h; simp at h
      | some vs =>
        rw [hr] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h, List.length_cons, List.length_cons, readAll_length hr]

/-- Writing as many values as registers always succeeds. -/
theorem writeAll_isSome [DecidableEq R] : ∀ (ps : List R) (vals : List Word) (fr : RTL.Frame R),
    ps.length = vals.length → (fr.writeAll ps vals).isSome
  | [], [], fr, _ => by simp [RTL.Frame.writeAll]
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen
  | p :: ps, v :: vs, fr, hlen => by
    rw [RTL.Frame.writeAll]
    exact writeAll_isSome ps vs (fr.set p v) (by simpa using hlen)

/-- An SSA step at an operation other than a call. -/
theorem ssa_step_op [DecidableEq R] {p : RTL.SSA.Prog R} {s : RTL.SSA.State R}
    {o : RTL.SSA.Op R} (hf : p.fetch s.point = some (.op o))
    (hne : ∀ g args results, o ≠ .call g args results) :
    RTL.SSA.step p s =
      (match o.exec s.frame s.mem with
        | some (fr, m) => .running { s with point := s.point.next, frame := fr, mem := m }
        | none => .stuck) := by
  cases o with
  | call g args results => exact absurd rfl (hne g args results)
  | _ => simp only [RTL.SSA.step, hf]; rfl

/-- Everything a terminator fetch gives the erased program. -/
theorem erase_fetch_term {p : RTL.SSA.Prog R} {pt : RTL.SSA.Point} {t : RTL.SSA.Term R}
    (h : p.fetch pt = some (.term t)) :
    ∃ fn blk, p.func? pt.func = some fn ∧ fn.block? pt.label = some blk ∧ blk.term = t ∧
      nodeOf p pt = startOf fn pt.label + blk.ops.length ∧
      ∃ rest, (erase fn).code.drop (nodeOf p pt) = termCode fn (nodeOf p pt) t ++ rest := by
  obtain ⟨fn, blk, hfn, hblk, hidx, hterm⟩ := ssa_fetch_term h
  have hnode : nodeOf p pt = startOf fn pt.label + blk.ops.length := by simp [nodeOf, hfn, hidx]
  obtain ⟨rest, hd⟩ := erase_drop_term hblk 0
  rw [hterm] at hd
  exact ⟨fn, blk, hfn, hblk, hterm, hnode, rest, by rw [hnode]; simpa using hd⟩

/-- **A returning SSA step returns in the erased program too.** -/
theorem erase_returned [DecidableEq R] {p : RTL.SSA.Prog R} {s : RTL.SSA.State R}
    {vs : List Word} {m : Memory} (h : RTL.SSA.step p s = .returned vs m) :
    RTL.step (eraseProg p) (eraseState p s) = .returned vs m := by
  have htr := RTL.SSA.Transition.of_step h (by simp)
  cases htr with
  | @halt regs vals hf hv hst =>
    obtain ⟨fn, blk, hfn, hblk, hterm, hnode, rest, hd⟩ := erase_fetch_term hf
    have hfetch : (eraseProg p).fetch (erasePoint p s.point) = some (RTL.Instr.ret regs) := by
      refine fetch_of_head? (fn := erase fn) (by simp [hfn]) ?_
      show ((erase fn).code.drop (nodeOf p s.point)).head? = _
      rw [hd]
      simp [termCode]
    show RTL.step (eraseProg p) _ = _
    simp [RTL.step, hfetch, hv, hst, eraseState]

/-- **A trapping SSA step traps in the erased program too.** -/
theorem erase_trapped [DecidableEq R] {p : RTL.SSA.Prog R} {s : RTL.SSA.State R}
    {m : Memory} (h : RTL.SSA.step p s = .trapped m) :
    RTL.step (eraseProg p) (eraseState p s) = .trapped m := by
  have htr := RTL.SSA.Transition.of_step h (by simp)
  cases htr with
  | trap hf =>
    obtain ⟨fn, blk, hfn, hblk, hterm, hnode, rest, hd⟩ := erase_fetch_term hf
    have hfetch : (eraseProg p).fetch (erasePoint p s.point) = some RTL.Instr.trap := by
      refine fetch_of_head? (fn := erase fn) (by simp [hfn]) ?_
      show ((erase fn).code.drop (nodeOf p s.point)).head? = _
      rw [hd]
      simp [termCode]
    show RTL.step (eraseProg p) _ = _
    simp [RTL.step, hfetch, eraseState]

/-- A transfer to a block that does not exist jumps past the last node. -/
theorem steps_transfer_bad_target [DecidableEq R] {p : RTL.SSA.Prog R} {f : RTL.FuncId}
    {fn : RTL.SSA.Func R} (hfn : p.func? f = some fn) {tt : RTL.SSA.Label} {aa : List R}
    {cb : Nat} (hchunk : ∃ rest, (erase fn).code.drop cb = transferCode fn cb tt aa ++ rest)
    (hnone : fn.block? tt = none) {fr : RTL.Frame R} (stack : List (RTL.Activation R))
    (mem : Memory) :
    ∃ t, RTL.Steps (eraseProg p) ⟨⟨f, cb⟩, fr, stack, mem⟩ t ∧
      RTL.step (eraseProg p) t = .stuck := by
  have hq : (eraseProg p).func? f = some (erase fn) := by simp [hfn]
  have hpar : paramsOf fn tt = [] := by simp [paramsOf, hnone]
  have hpairs : transferPairs fn tt aa = [] := by simp [transferPairs, hpar]
  obtain ⟨rest, hd⟩ := hchunk
  have hjump : (eraseProg p).fetch ⟨f, cb⟩ = some (RTL.Instr.jump (startOf fn tt)) := by
    refine fetch_of_head? hq ?_
    rw [hd, transferCode, hpairs]
    simp [movesCode]
  have hstep : RTL.Step (eraseProg p) ⟨⟨f, cb⟩, fr, stack, mem⟩
      ⟨⟨f, startOf fn tt⟩, fr, stack, mem⟩ := by
    show RTL.step (eraseProg p) _ = _
    simp [RTL.step, hjump, RTL.Point.at]
  have hlt : fn.blocks.length ≤ tt := by
    by_contra hc
    rw [RTL.SSA.Func.block?, List.getElem?_eq_getElem (Nat.lt_of_not_le hc)] at hnone
    exact absurd hnone (by simp)
  refine ⟨⟨⟨f, startOf fn tt⟩, fr, stack, mem⟩, Relation.ReflTransGen.single hstep, ?_⟩
  simp [RTL.step, fetch_of_le hq (erase_code_length_le fn hlt)]

/-- **A stuck transfer is stuck in the erased program too**, after performing
whichever moves it can. -/
theorem erase_stuck_transfer [DecidableEq R] {p : RTL.SSA.Prog R} {f : RTL.FuncId}
    {fn : RTL.SSA.Func R} (hfn : p.func? f = some fn) {tt : RTL.SSA.Label} {aa : List R}
    {cb : Nat} (hchunk : ∃ rest, (erase fn).code.drop cb = transferCode fn cb tt aa ++ rest)
    (hseq : sequentialMoves (paramsOf fn tt) aa = true)
    (hlen : (paramsOf fn tt).length = aa.length) {fr : RTL.Frame R}
    (stack : List (RTL.Activation R)) (mem : Memory)
    (hstuck : (fr.readAll aa).bind
      (fun vals => (fn.block? tt).bind fun bt => fr.writeAll bt.params vals) = none) :
    ∃ t, RTL.Steps (eraseProg p) ⟨⟨f, cb⟩, fr, stack, mem⟩ t ∧
      RTL.step (eraseProg p) t = .stuck := by
  have hq : (eraseProg p).func? f = some (erase fn) := by simp [hfn]
  obtain ⟨rest, hd⟩ := hchunk
  have hmoves : ∃ tl, (erase fn).code.drop cb = movesCode cb (transferPairs fn tt aa) ++ tl :=
    ⟨_, by rw [hd, transferCode, List.append_assoc]⟩
  cases hr : fr.readAll aa with
  | none =>
    refine steps_movesCode_stuck hq (transferPairs fn tt aa) cb fr stack mem hmoves ?_
    rw [transferPairs, applyMoves_eq_bind _ _ fr hseq hlen, hr]
    rfl
  | some vals =>
    cases hb : fn.block? tt with
    | none => exact steps_transfer_bad_target hfn ⟨rest, hd⟩ hb stack mem
    | some bt =>
      exfalso
      rw [hr, hb] at hstuck
      simp only [Option.bind_some] at hstuck
      have hpar : paramsOf fn tt = bt.params := by rw [paramsOf, hb]; rfl
      have hplen : bt.params.length = vals.length := by
        rw [← hpar, hlen, ← readAll_length hr]
      have := writeAll_isSome bt.params vals fr hplen
      rw [hstuck] at this
      simp at this

/-- **A stuck SSA step is stuck in the erased program too.** This is the one
place the reachability invariant is used: at a point past a block's operations
the SSA program is stuck and the erased one is not, and `StateOk` says no such
point is reached. -/
theorem erase_stuck [DecidableEq R] {p : RTL.SSA.Prog R} (hwf : p.WellFormed)
    (hsq : ∀ fn ∈ p.funcs, SequentialTransfers fn) {s : RTL.SSA.State R}
    (hok : StateOk p s) (h : RTL.SSA.step p s = .stuck) :
    ∃ t, RTL.Steps (eraseProg p) (eraseState p s) t ∧
      RTL.step (eraseProg p) t = .stuck := by
  cases hf : p.fetch s.point with
  | none =>
    refine ⟨eraseState p s, .refl, ?_⟩
    cases hfn : p.func? s.point.func with
    | none =>
      show RTL.step (eraseProg p) _ = _
      simp [RTL.step, RTL.Prog.fetch, RTL.Prog.instr?, eraseState, erasePoint, hfn]
    | some fn =>
      cases hb : fn.block? s.point.label with
      | none =>
        have hlt : fn.blocks.length ≤ s.point.label := by
          by_contra hc
          rw [RTL.SSA.Func.block?, List.getElem?_eq_getElem (Nat.lt_of_not_le hc)] at hb
          exact absurd hb (by simp)
        have hle : (erase fn).code.length ≤ nodeOf p s.point := by
          rw [show nodeOf p s.point = startOf fn s.point.label + s.point.index from by
            simp [nodeOf, hfn]]
          exact le_trans (erase_code_length_le fn hlt) (Nat.le_add_right _ _)
        show RTL.step (eraseProg p) _ = _
        simp [RTL.step,
          fetch_of_le (q := eraseProg p) (f := s.point.func) (fn := erase fn) (by simp [hfn]) hle,
          eraseState, erasePoint]
      | some b =>
        exfalso
        have hidx := hok.1 fn hfn b hb
        rw [RTL.SSA.Prog.fetch, RTL.SSA.Prog.block?, hfn, Option.bind_some, hb,
          Option.bind_some] at hf
        cases ho : b.ops[s.point.index]? with
        | some o => rw [ho] at hf; simp at hf
        | none =>
          rw [ho] at hf
          have : s.point.index = b.ops.length := by
            have := List.getElem?_eq_none_iff.mp ho
            omega
          simp only [this, reduceIte] at hf
          simp at hf
  | some cd =>
    cases cd with
    | op o =>
      obtain ⟨fn, b, hfn, hb, hi, hops⟩ := ssa_fetch_op hf
      have hnode : nodeOf p s.point = startOf fn s.point.label + s.point.index := by
        simp [nodeOf, hfn]
      have hfetch : (eraseProg p).fetch (eraseState p s).point =
          some (instrOfOp (nodeOf p s.point + 1) o) := by
        have := erase_fetch_op hfn hb hi
        rw [hops] at this
        simpa [eraseState, erasePoint, hnode] using this
      by_cases hcall : ∃ g args results, o = RTL.SSA.Op.call g args results
      · obtain ⟨g, args, results, rfl⟩ := hcall
        refine ⟨eraseState p s, .refl, ?_⟩
        simp only [RTL.SSA.step, hf] at h
        show RTL.step (eraseProg p) _ = _
        simp only [RTL.step, hfetch, instrOfOp,
          show (eraseState p s).frame = s.frame from rfl]
        cases ha : s.frame.readAll args with
        | none => simp
        | some vals =>
          simp only [ha] at h
          cases he : p.enter g vals with
          | none => simp [erase_enter_none hwf he]
          | some r => rw [he] at h; obtain ⟨pt, fr⟩ := r; simp at h
      · push Not at hcall
        have hne : ∀ g args results, o ≠ RTL.SSA.Op.call g args results := by
          intro g args results he
          exact absurd he (by simpa using hcall g args results)
        rw [ssa_step_op hf hne] at h
        refine ⟨eraseState p s, .refl, ?_⟩
        cases he : RTL.SSA.Op.exec o s.frame s.mem with
        | some r => rw [he] at h; obtain ⟨fr, m⟩ := r; simp at h
        | none =>
          show RTL.step (eraseProg p) _ = _
          rw [step_instrOfOp hfetch hne]
          simp [show (eraseState p s).frame = s.frame from rfl,
            show (eraseState p s).mem = s.mem from rfl, he]
    | term t =>
      obtain ⟨fn, blk, hfn, hblk, hterm, hnode, rest, hd⟩ := erase_fetch_term hf
      have hq : (eraseProg p).func? s.point.func = some (erase fn) := by simp [hfn]
      have hfnmem : fn ∈ p.funcs := by
        rw [RTL.SSA.Prog.func?] at hfn
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hfn
        exact heq ▸ List.getElem_mem hlt
      have hmem : blk ∈ fn.blocks := by
        rw [RTL.SSA.Func.block?] at hblk
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hblk
        exact heq ▸ List.getElem_mem hlt
      have hpt : (eraseState p s).point = ⟨s.point.func, nodeOf p s.point⟩ := rfl
      cases t with
      | jump tt aa =>
        simp only [RTL.SSA.step, hf, RTL.SSA.transfer] at h
        have hta : (tt, aa) ∈ blk.term.args := by rw [hterm]; simp [RTL.SSA.Term.args]
        have hchunk : ∃ r, (erase fn).code.drop (nodeOf p s.point) =
            transferCode fn (nodeOf p s.point) tt aa ++ r := ⟨rest, by rw [hd]; rfl⟩
        refine erase_stuck_transfer hfn hchunk (hsq fn hfnmem blk hmem (tt, aa) hta)
          (paramsOf_length_eq (hwf fn hfnmem).argsMatch hmem hta) _ _ ?_
        cases hr : s.frame.readAll aa with
        | none => rfl
        | some vals =>
          simp only [hr] at h
          simp only [Option.bind_some]
          cases hbb : fn.block? tt with
          | none => rfl
          | some bt =>
            simp only [RTL.SSA.Prog.block?, hfn, Option.bind_some, hbb] at h
            simp only [Option.bind_some]
            cases hw : s.frame.writeAll bt.params vals with
            | none => rfl
            | some fr => simp only [hw] at h; simp at h
      | cond c t₁ a₁ t₂ a₂ =>
        simp only [RTL.SSA.step, hf] at h
        have hfetch : (eraseProg p).fetch ⟨s.point.func, nodeOf p s.point⟩ =
            some (RTL.Instr.cond c (nodeOf p s.point + 1)
              (nodeOf p s.point + 1 + (transferPairs fn t₁ a₁).length + 1)) := by
          refine fetch_of_head? hq ?_
          show ((erase fn).code.drop (nodeOf p s.point)).head? = _
          rw [hd]
          simp [termCode]
        cases hc : s.frame.get c with
        | none =>
          refine ⟨eraseState p s, .refl, ?_⟩
          show RTL.step (eraseProg p) (eraseState p s) = .stuck
          simp [RTL.step, eraseState, erasePoint, hfetch, hc]
        | some x =>
          simp only [hc, RTL.SSA.transfer] at h
          -- the badness of the taken edge, read off the stuck transfer
          have bad : ∀ (tt : RTL.SSA.Label) (aa : List R),
              (match s.frame.readAll aa with
                | none => RTL.SSA.Result.stuck
                | some vals =>
                  match p.block? s.point.func tt with
                  | none => RTL.SSA.Result.stuck
                  | some b =>
                    match s.frame.writeAll b.params vals with
                    | some fr => .running ⟨⟨s.point.func, tt, 0⟩, fr, s.stack, s.mem⟩
                    | none => .stuck) = RTL.SSA.Result.stuck →
              (s.frame.readAll aa).bind (fun vals =>
                (fn.block? tt).bind fun bt => s.frame.writeAll bt.params vals) = none := by
            intro tt aa hst
            cases hr : s.frame.readAll aa with
            | none => rfl
            | some vals =>
              simp only [hr] at hst
              simp only [Option.bind_some]
              cases hbb : fn.block? tt with
              | none => rfl
              | some bt =>
                simp only [RTL.SSA.Prog.block?, hfn, Option.bind_some, hbb] at hst
                simp only [Option.bind_some]
                cases hw : s.frame.writeAll bt.params vals with
                | none => rfl
                | some fr => simp only [hw] at hst; simp at hst
          have key : ∀ (tt : RTL.SSA.Label) (aa : List R) (cb : Nat),
              (tt, aa) ∈ blk.term.args →
              (∃ r, (erase fn).code.drop cb = transferCode fn cb tt aa ++ r) →
              RTL.Step (eraseProg p) (eraseState p s)
                ⟨⟨s.point.func, cb⟩, s.frame, (eraseState p s).stack, s.mem⟩ →
              (s.frame.readAll aa).bind (fun vals =>
                (fn.block? tt).bind fun bt => s.frame.writeAll bt.params vals) = none →
              ∃ u, RTL.Steps (eraseProg p) (eraseState p s) u ∧
                RTL.step (eraseProg p) u = .stuck := by
            intro tt aa cb hta hchunk hst hbad
            obtain ⟨u, hu, hsu⟩ := erase_stuck_transfer hfn hchunk
              (hsq fn hfnmem blk hmem (tt, aa) hta)
              (paramsOf_length_eq (hwf fn hfnmem).argsMatch hmem hta)
              ((eraseState p s).stack) s.mem hbad
            exact ⟨u, Relation.ReflTransGen.head hst hu, hsu⟩
          by_cases hx : x = 0
          · subst hx
            simp only [reduceIte] at h
            refine key t₂ a₂ (nodeOf p s.point + 1 + (transferPairs fn t₁ a₁).length + 1)
              (by rw [hterm]; simp [RTL.SSA.Term.args]) ?_ ?_ (bad t₂ a₂ h)
            · obtain ⟨r, hdd⟩ := erase_drop_term hblk (1 + (transferPairs fn t₁ a₁).length + 1)
              rw [hterm] at hdd
              refine ⟨r, ?_⟩
              have harith : nodeOf p s.point + 1 + (transferPairs fn t₁ a₁).length + 1
                  = startOf fn s.point.label + blk.ops.length +
                    (1 + (transferPairs fn t₁ a₁).length + 1) := by rw [hnode]; omega
              have harith2 : startOf fn s.point.label + blk.ops.length + 1 +
                  (transferPairs fn t₁ a₁).length + 1
                = startOf fn s.point.label + blk.ops.length +
                  (1 + (transferPairs fn t₁ a₁).length + 1) := by omega
              rw [harith, hdd, termCode_cond_drop_right, harith2]
            · show RTL.step (eraseProg p) _ = _
              simp [RTL.step, eraseState, hfetch, hc, RTL.Point.at, erasePoint]
          · simp only [hx, reduceIte] at h
            refine key t₁ a₁ (nodeOf p s.point + 1)
              (by rw [hterm]; simp [RTL.SSA.Term.args]) ?_ ?_ (bad t₁ a₁ h)
            · obtain ⟨r, hdd⟩ := erase_drop_term hblk 1
              rw [hterm] at hdd
              have harith : nodeOf p s.point + 1
                  = startOf fn s.point.label + blk.ops.length + 1 := by rw [hnode]
              rw [harith, hdd, termCode_cond_drop_left, List.append_assoc]
              exact ⟨_, rfl⟩
            · show RTL.step (eraseProg p) _ = _
              simp [RTL.step, eraseState, hfetch, hc, RTL.Point.at, erasePoint]
              exact fun hz => absurd hz hx
      | ret regs =>
        simp only [RTL.SSA.step, hf] at h
        have hfetch : (eraseProg p).fetch ⟨s.point.func, nodeOf p s.point⟩ =
            some (RTL.Instr.ret regs) := by
          refine fetch_of_head? hq ?_
          show ((erase fn).code.drop (nodeOf p s.point)).head? = _
          rw [hd]
          simp [termCode]
        refine ⟨eraseState p s, .refl, ?_⟩
        show RTL.step (eraseProg p) (eraseState p s) = .stuck
        cases hv : s.frame.readAll regs with
        | none => simp [RTL.step, eraseState, erasePoint, hfetch, hv]
        | some vals =>
          simp only [hv] at h
          cases hst : s.stack with
          | nil => simp only [hst] at h; simp at h
          | cons a restStack =>
            simp only [hst] at h
            obtain ⟨g, cargs, cres, hacall⟩ := hok.2 a (by rw [hst]; exact List.mem_cons_self)
            obtain ⟨hfa, hna, -⟩ := erase_fetch_act hacall
            have hfa' : (eraseProg p).fetch ⟨a.point.func, nodeOf p a.point⟩ =
                some (.call g cargs cres (nodeOf p a.point + 1)) := hfa
            simp only [hacall] at h
            cases hw : a.frame.writeAll cres vals with
            | none =>
              simp [RTL.step, eraseState, erasePoint, hfetch, hv, hst, eraseAct, hfa', hw]
            | some fr => simp only [hw] at h; simp at h
      | trap => simp only [RTL.SSA.step, hf] at h; simp at h

/-! ## Soundness -/

/-- An SSA behaviour as an RTL behaviour: the same four constructors, in two
namespaces. `docs/CompCertLessons.md` §0 records that the repository has about
ten structurally identical `Behavior` inductives with transport functions
between them, and that a generic simulation kit is where they all
belong; this is one more, added rather than refactored on purpose. -/
def behaviorOfSsa : RTL.SSA.Behavior → RTL.Behavior
  | .returned vs m => .returned vs m
  | .trapped m => .trapped m
  | .stuck => .stuck
  | .diverges => .diverges

/-- Transporting a behaviour loses nothing, which is what turns the forward
direction plus determinism into the `iff`. -/
theorem behaviorOfSsa_injective : Function.Injective behaviorOfSsa := by
  intro a b h
  cases a <;> cases b <;> simp_all [behaviorOfSsa]

/-- **The start states of the two programs correspond**, and the start state
satisfies the reachability invariant: it is at the first operation of its entry
block with an empty stack. -/
theorem erase_start [DecidableEq R] {p : RTL.SSA.Prog R} (hwf : p.WellFormed)
    {f : RTL.FuncId} {args : List Word} {mem : Memory} {s : RTL.SSA.State R}
    (h : p.start f args mem = some s) :
    (eraseProg p).start f args mem = some (eraseState p s) ∧ StateOk p s := by
  rw [RTL.SSA.Prog.start] at h
  cases he : p.enter f args with
  | none => simp only [he] at h; simp at h
  | some r =>
    obtain ⟨pt, fr⟩ := r
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨?_, ⟨fun fn' hfn' b' hb' => ?_, fun a ha => absurd ha (by simp)⟩⟩
    · rw [RTL.Prog.start, erase_enter hwf he]
      rfl
    · rw [enter_index he]
      omega

/-- **Erasure preserves and reflects behaviour.** A well-formed SSA program all
of whose transfers are sequentializable has exactly the behaviours of the RTL
program it erases to, started on the same function, arguments and memory — all
four of them, stuck included, with no side condition on the source. This is the
theorem the rung exists for. -/
theorem erase_behaves [DecidableEq R] {p : RTL.SSA.Prog R} (hwf : p.WellFormed)
    (hseq : ∀ fn ∈ p.funcs, SequentialTransfers fn) {f : RTL.FuncId} {args : List Word}
    {mem : Memory} {s : RTL.SSA.State R} (hs : p.start f args mem = some s) :
    ∃ t, (eraseProg p).start f args mem = some t ∧
      ∀ b : RTL.SSA.Behavior,
        (RTL.SSA.Behaves p s b ↔ RTL.Behaves (eraseProg p) t (behaviorOfSsa b)) := by
  obtain ⟨hstart, hok⟩ := erase_start hwf hs
  refine ⟨eraseState p s, hstart, ?_⟩
  have sim : Silmaril.LockstepSim (RTL.SSA.Step p) (RTL.Step (eraseProg p))
      (fun u t => StateOk p u ∧ t = eraseState p u) := by
    constructor
    rintro u u' t hst ⟨hok', rfl⟩
    obtain ⟨hok'', htr⟩ := erase_sim hwf hseq hok' hst
    exact ⟨eraseState p u', htr, hok'', rfl⟩
  have fwd : ∀ b : RTL.SSA.Behavior, RTL.SSA.Behaves p s b →
      RTL.Behaves (eraseProg p) (eraseState p s) (behaviorOfSsa b) := by
    intro b hb
    cases b with
    | returned vs m =>
      obtain ⟨u, hu, hfin⟩ := hb
      obtain ⟨t, ht, -, rfl⟩ := sim.steps hu ⟨hok, rfl⟩
      exact ⟨eraseState p u, ht, erase_returned hfin⟩
    | trapped m =>
      obtain ⟨u, hu, hfin⟩ := hb
      obtain ⟨t, ht, -, rfl⟩ := sim.steps hu ⟨hok, rfl⟩
      exact ⟨eraseState p u, ht, erase_trapped hfin⟩
    | stuck =>
      obtain ⟨u, hu, hfin⟩ := hb
      obtain ⟨t, ht, hok', rfl⟩ := sim.steps hu ⟨hok, rfl⟩
      obtain ⟨t', ht', hst'⟩ := erase_stuck hwf hseq hok' hfin
      exact ⟨t', ht.trans ht', hst'⟩
    | diverges => exact sim.diverges hb ⟨hok, rfl⟩
  obtain ⟨b₀, hb₀⟩ := RTL.SSA.Behaves.exists p s
  intro b
  refine ⟨fwd b, fun hb => ?_⟩
  exact behaviorOfSsa_injective (RTL.Behaves.unique hb (fwd b₀ hb₀)) ▸ hb₀

/-- **An accepted SSA form has the same behaviours as the RTL function it
erases to.** -/
theorem checkSsa_sound [DecidableEq R] {target : RTL.Prog R} {spec : RTL.SSA.Prog R}
    (hok : checkSsaProg target spec = .ok ()) {f : RTL.FuncId} {args : List Word}
    {mem : Memory} {s : RTL.SSA.State R} (hs : spec.start f args mem = some s) :
    ∃ t, target.start f args mem = some t ∧
      ∀ b : RTL.SSA.Behavior,
        (RTL.SSA.Behaves spec s b ↔ RTL.Behaves target t (behaviorOfSsa b)) := by
  obtain ⟨t, ht, hiff⟩ := erase_behaves (checkSsaProg_wellFormed hok)
    (checkSsaProg_sequential hok) hs
  rw [checkSsaProg_erase_eq hok] at ht hiff
  exact ⟨t, ht, hiff⟩

end Silmaril.Machine.Lift
