module

public import Silmaril.Raw.Machine.RTL.Behaviour
public import Silmaril.Raw.Machine.RTL.Machine.Graph.Dominance
public import Mathlib.Data.List.Nodup

/-!
# RTL.SSA: the SSA-form subset, with block arguments

`RTL.SSA` is RTL in static single assignment form. Two things change relative to
`RTL`:

* the program is **block-structured** again — a function is a list of blocks,
  each a list of straight-line `Op`s ending in a `Term` — because SSA is a
  property of a basic-block graph, not of individual instructions;
* a block **takes arguments**, and every jump carries the arguments of its
  target. Block arguments are the φ-nodes: instead of a φ at the head of a block
  naming one source register per predecessor, each predecessor supplies its own
  value at the edge. This is MLIR's and Swift SIL's presentation. It avoids the
  parallel-copy semantics of φ-nodes entirely: an edge is one simultaneous write
  of the target's parameters.

A function's entry parameters are the parameters of its entry block; there is no
separate `entryParams` field, so there is nothing to keep consistent. The entry
block may therefore be the target of a back edge, as in a loop whose header is
the entry.

Values, operators, memory and the undefined-behaviour convention are `Lir`'s and
`RTL`'s, unchanged.

## Well-formedness

`Func.WellFormed` bundles, all decidable:

* `WellFormedSig` — the entry block exists, its parameter count is the
  signature's, every terminator target exists, and every `ret` returns the
  declared number of values;
* `SingleAssignment` — no register is defined twice, counting block parameters
  and op destinations across the whole function;
* `UsesDominated` — every use of a register is either a parameter of the using
  block, the destination of an earlier op of the using block, or a definition of
  a block that strictly dominates the using block;
* `ArgsMatch` — every jump's argument list has the length of its target's
  parameter list.

Dominance is not defined here. `Func.digraph` presents a function as a
`Machine.Graph.Digraph` and `Func.Dominates` is that graph's dominance, so the
fixpoint, its decidability and its agreement with the path definition are proved
once in `Machine/Graph/Dominance.lean`.

**The theorem these definitions exist for** is `reachable_uses_isSome`: in a
well-formed program, every state reachable from a whole-program start reads only
registers that have been written. A well-formed SSA function never gets stuck on
an unwritten register.

The statement is deliberately "every use is written" and not "`step` is never
stuck", because the latter is **false**: a well-formed SSA function may divide
by zero, and division by zero is stuck by design, exactly as in `Lir`. That is
the sharpest way to say what well-formedness buys. It rules out the stuck states
that are an artefact of the *representation* — reading a register that no
dominating definition wrote — and leaves untouched the stuck states that are
genuine source-level undefined behaviour of the operators themselves (division,
remainder, out-of-bounds memory).

It is also worth recording which conjuncts of `WellFormed` do the work.
`UsesDominated` is the only one the theorem consumes: `Invariant.start` and
`Invariant.step` hold for *every* program, well-formed or not, because a
transition that has already succeeded carries the writes it performed.
`SingleAssignment` earns its place elsewhere — it is what makes the value at a
use unambiguous, which is what a later optimisation or a translation out of SSA
will need — not by ruling out stuckness. `ArgsMatch` likewise is what makes the
checker reject programs whose transfers would get stuck, rather than something
the invariant needs once a transfer has gone through.

Not provided: a lowering from `RTL` to `RTL.SSA` or back, φ-node elimination,
dominance-frontier-based SSA construction, or any optimisation.
-/

@[expose] public section

namespace Silmaril.Machine.RTL.SSA

open Silmaril.Machine.Lir (Word Memory)
open Relation

/-- Labels index a function's block list. -/
abbrev Label := Nat

/-! ## Syntax -/

/-- Straight-line operations: RTL instructions without their successor. -/
inductive Op (R : Type) where
  | const (dest : R) (value : Lir.Word)
  | move (dest source : R)
  | unary (op : Lir.Unop) (dest source : R)
  | binary (op : Lir.Binop) (dest first second : R)
  | load (width : Lir.Width) (ext : Lir.Ext) (dest base : R) (offset : Nat)
  | store (width : Lir.Width) (base : R) (offset : Nat) (source : R)
  | call (callee : FuncId) (args : List R) (results : List R)
  deriving DecidableEq, Repr

/-- Terminators. Every jump carries the arguments of its target block; there
are no φ-nodes. -/
inductive Term (R : Type) where
  | jump (target : Label) (args : List R)
  | cond (c : R) (ifNonzero : Label) (argsNonzero : List R)
         (ifZero : Label) (argsZero : List R)
  | ret (values : List R)
  | trap
  deriving DecidableEq, Repr

/-- A block takes arguments; they are the φ-nodes. -/
structure Block (R : Type) where
  params : List R
  ops : List (Op R)
  term : Term R
  deriving DecidableEq, Repr

/-- A function: a signature, an entry label and its blocks. The entry block's
parameters are the function's parameters. -/
structure Func (R : Type) where
  sig : Signature
  entry : Label
  blocks : List (Block R)
  deriving DecidableEq, Repr

/-- A program is a function table indexed by `FuncId`. -/
structure Prog (R : Type) where
  funcs : List (Func R)
  deriving DecidableEq, Repr

namespace Op

variable {R : Type}

/-- The registers an operation reads. -/
def uses : Op R → List R
  | .const _ _ => []
  | .move _ s | .unary _ _ s => [s]
  | .binary _ _ a b => [a, b]
  | .load _ _ _ base _ => [base]
  | .store _ base _ src => [base, src]
  | .call _ args _ => args

/-- The registers an operation writes. -/
def defs : Op R → List R
  | .const d _ | .move d _ | .unary _ d _ | .binary _ d _ _ | .load _ _ d _ _ => [d]
  | .store .. => []
  | .call _ _ results => results

/-- Execute a non-call operation. `none` is undefined behaviour; a `call` is
not straight-line and is never executed here. -/
def exec [DecidableEq R] : Op R → Frame R → Memory → Option (Frame R × Memory)
  | .const d v, fr, m => some (fr.set d v, m)
  | .move d s, fr, m => (fr.get s).map fun x => (fr.set d x, m)
  | .unary op d s, fr, m => (fr.get s).map fun x => (fr.set d (op.eval x), m)
  | .binary op d a b, fr, m =>
      (fr.get a).bind fun x => (fr.get b).bind fun y =>
        (op.eval x y).map fun z => (fr.set d z, m)
  | .load w e d base off, fr, m =>
      (fr.get base).bind fun a => (m.load w e (a.toNat + off)).map fun z => (fr.set d z, m)
  | .store w base off src, fr, m =>
      (fr.get base).bind fun a => (fr.get src).bind fun x =>
        (m.store w (a.toNat + off) x).map fun m' => (fr, m')
  | .call .., _, _ => none

end Op

namespace Term

variable {R : Type}

/-- The labels a terminator may transfer to. -/
def successors : Term R → List Label
  | .jump t _ => [t]
  | .cond _ t₁ _ t₂ _ => [t₁, t₂]
  | .ret _ | .trap => []

/-- The targets of a terminator with the arguments supplied to each. -/
def args : Term R → List (Label × List R)
  | .jump t as => [(t, as)]
  | .cond _ t₁ a₁ t₂ a₂ => [(t₁, a₁), (t₂, a₂)]
  | .ret _ | .trap => []

/-- The registers a terminator reads: its condition and all block arguments,
or the returned values. -/
def uses : Term R → List R
  | .jump _ as => as
  | .cond c _ a₁ _ a₂ => c :: (a₁ ++ a₂)
  | .ret values => values
  | .trap => []

/-- `t` fits a function with `results` return values and `n` blocks. -/
def okIn (results n : Nat) (t : Term R) : Bool :=
  t.successors.all (fun l => decide (l < n)) &&
    (match t with
     | .ret values => values.length == results
     | _ => true)

end Term

/-- The registers a block defines: its parameters and its ops' destinations. -/
def Block.defs {R : Type} (b : Block R) : List R := b.params ++ b.ops.flatMap Op.defs

namespace Func

variable {R : Type}

/-- The block with the given label. -/
def block? (fn : Func R) (l : Label) : Option (Block R) := fn.blocks[l]?

/-- The successors of a block; a missing block has none. -/
def succ (fn : Func R) (l : Label) : List Label :=
  match fn.block? l with
  | some b => b.term.successors
  | none => []

/-- The registers defined by a block; a missing block defines none. -/
def defsOf (fn : Func R) (l : Label) : List R :=
  match fn.block? l with
  | some b => b.defs
  | none => []

/-- The control-flow graph of a function, as a `Machine.Graph.Digraph`. All
graph notions below are this graph's. -/
def digraph (fn : Func R) : Graph.Digraph where
  size := fn.blocks.length
  succ := fn.succ
  entry := fn.entry

/-- A control-flow edge. -/
def Edge (fn : Func R) (a b : Label) : Prop := fn.digraph.Edge a b

instance (fn : Func R) (a b : Label) : Decidable (fn.Edge a b) :=
  inferInstanceAs (Decidable (Graph.Digraph.Edge _ _ _))

/-- The edge list of the control-flow graph. -/
def Edges (fn : Func R) : List (Label × Label) :=
  (List.range fn.blocks.length).flatMap fun a => (fn.digraph.step a).map fun b => (a, b)

/-- A block is reachable when some path leads to it from the entry. -/
def Reachable (fn : Func R) (l : Label) : Prop := fn.digraph.Reachable l

instance (fn : Func R) (l : Label) : Decidable (fn.Reachable l) :=
  inferInstanceAs (Decidable (Graph.Digraph.Reachable _ _))

/-- `a` dominates `b` when every path from the entry to `b` passes through `a`;
`Machine.Graph.Dominance` proves the fixpoint computing this agrees with the
path definition. -/
def Dominates (fn : Func R) (a b : Label) : Prop := fn.digraph.Dominates a b

instance (fn : Func R) (a b : Label) : Decidable (fn.Dominates a b) :=
  inferInstanceAs (Decidable (Graph.Digraph.Dominates _ _ _))

/-! ### Well-formedness -/

/-- The entry block exists with the signature's parameter count, every
terminator target exists, and every `ret` returns the declared number of
values. -/
def WellFormedSig (fn : Func R) : Prop :=
  fn.entry < fn.blocks.length ∧
    (match fn.block? fn.entry with
     | some b => b.params.length == fn.sig.params
     | none => false) = true ∧
    fn.blocks.all (fun b => b.term.okIn fn.sig.results fn.blocks.length) = true

instance (fn : Func R) : Decidable fn.WellFormedSig := inferInstanceAs (Decidable (_ ∧ _))

/-- Every register defined by the function, with multiplicity. -/
def allDefs (fn : Func R) : List R := fn.blocks.flatMap Block.defs

/-- No register is defined twice, counting block parameters and op
destinations across the whole function. -/
def SingleAssignment (fn : Func R) : Prop := fn.allDefs.Nodup

instance [DecidableEq R] (fn : Func R) : Decidable fn.SingleAssignment :=
  inferInstanceAs (Decidable (List.Nodup _))

/-- `r` may be used at op index `j` of block `l`: it is a parameter of `l`, the
destination of an op of `l` before `j`, or a definition of a block that strictly
dominates `l`. -/
def okUse [DecidableEq R] (fn : Func R) (l : Label) (j : Nat) (r : R) : Bool :=
  (match fn.block? l with
   | none => false
   | some b =>
     decide (r ∈ b.params) || (b.ops.take j).any fun o => decide (r ∈ o.defs)) ||
  (List.range fn.blocks.length).any fun a =>
    decide (a ≠ l) && decide (fn.Dominates a l) && decide (r ∈ fn.defsOf a)

/-- Every use is dominated by its definition, and inside a block the defining
op precedes the using op. -/
def usesDominated [DecidableEq R] (fn : Func R) : Bool :=
  (List.range fn.blocks.length).all fun l =>
    match fn.block? l with
    | none => true
    | some b =>
      ((List.range b.ops.length).all fun j =>
        match b.ops[j]? with
        | some o => o.uses.all (fn.okUse l j)
        | none => true) &&
      b.term.uses.all (fn.okUse l b.ops.length)

/-- Every use is dominated by its definition. -/
def UsesDominated [DecidableEq R] (fn : Func R) : Prop := fn.usesDominated = true

instance [DecidableEq R] (fn : Func R) : Decidable fn.UsesDominated :=
  inferInstanceAs (Decidable (_ = _))

/-- Every jump's argument list has the length of its target's parameter list. -/
def argsMatch (fn : Func R) : Bool :=
  fn.blocks.all fun b =>
    b.term.args.all fun ta =>
      match fn.block? ta.1 with
      | some tb => tb.params.length == ta.2.length
      | none => false

/-- Every jump's arguments match its target's parameters. -/
def ArgsMatch (fn : Func R) : Prop := fn.argsMatch = true

instance (fn : Func R) : Decidable fn.ArgsMatch := inferInstanceAs (Decidable (_ = _))

/-- A well-formed SSA function. -/
structure WellFormed [DecidableEq R] (fn : Func R) : Prop where
  sig : fn.WellFormedSig
  singleAssignment : fn.SingleAssignment
  usesDominated : fn.UsesDominated
  argsMatch : fn.ArgsMatch

instance [DecidableEq R] (fn : Func R) : Decidable fn.WellFormed :=
  decidable_of_iff (fn.WellFormedSig ∧ fn.SingleAssignment ∧ fn.UsesDominated ∧ fn.ArgsMatch)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
     fun h => ⟨h.sig, h.singleAssignment, h.usesDominated, h.argsMatch⟩⟩

end Func

/-! ## Semantics

The shape is `RTL/Semantics.lean`'s, with a program point carrying an index into
the current block's op list, as in `Lir`. Frames are `RTL.Frame`: SSA does not
change the register model. -/

variable {R : Type}

/-- A program point: the `index`-th op of block `label` of `func`, or its
terminator when `index` is the number of ops. -/
structure Point where
  func : FuncId
  label : Label
  index : Nat
  deriving DecidableEq, Repr

/-- The point of the next op of the same block. -/
def Point.next (pt : Point) : Point := { pt with index := pt.index + 1 }

@[simp] theorem Point.next_func (pt : Point) : pt.next.func = pt.func := rfl
@[simp] theorem Point.next_label (pt : Point) : pt.next.label = pt.label := rfl
@[simp] theorem Point.next_index (pt : Point) : pt.next.index = pt.index + 1 := rfl

/-- The fetched code at a point. -/
inductive Code (R : Type) where
  | op (o : Op R)
  | term (t : Term R)
  deriving DecidableEq, Repr

namespace Prog

/-- The function with the given identifier. -/
def func? (p : Prog R) (f : FuncId) : Option (Func R) := p.funcs[f]?

/-- The block with the given label of the given function. -/
def block? (p : Prog R) (f : FuncId) (l : Label) : Option (Block R) :=
  (p.func? f).bind fun fn => fn.block? l

/-- The code at a point: an op, or the block's terminator one past the last op. -/
def fetch (p : Prog R) (pt : Point) : Option (Code R) :=
  (p.block? pt.func pt.label).bind fun b =>
    match b.ops[pt.index]? with
    | some o => some (.op o)
    | none => if pt.index = b.ops.length then some (.term b.term) else none

end Prog

/-- A suspended caller: the point of its `call` op and its frame. -/
structure Activation (R : Type) where
  point : Point
  frame : Frame R

/-- A machine state. -/
structure State (R : Type) where
  point : Point
  frame : Frame R
  stack : List (Activation R)
  mem : Memory

/-- The result of one step. -/
inductive Result (R : Type) where
  | running (s : State R)
  | returned (values : List Word) (mem : Memory)
  | trapped (mem : Memory)
  | stuck

/-- Returned values of a result, for executable checks. -/
def Result.returnedValues? : Result R → Option (List Word)
  | .returned vs _ => some vs
  | _ => none

/-- Whether a result is a trap, for executable checks. -/
def Result.isTrapped : Result R → Bool
  | .trapped _ => true
  | _ => false

variable [DecidableEq R]

namespace Prog

/-- The entry point and fresh frame of a call: the callee's entry block's
parameters bound to the arguments. -/
def enter (p : Prog R) (f : FuncId) (vals : List Word) : Option (Point × Frame R) :=
  (p.func? f).bind fun fn =>
    (fn.block? fn.entry).bind fun b =>
      (Frame.empty.writeAll b.params vals).map fun fr => (⟨f, fn.entry, 0⟩, fr)

/-- The initial state of a whole-program run of `f` on `args`. -/
def start (p : Prog R) (f : FuncId) (args : List Word) (mem : Memory) : Option (State R) :=
  (p.enter f args).map fun (pt, fr) => ⟨pt, fr, [], mem⟩

end Prog

/-- Transfer control to `target`, binding its parameters to the values of
`args` in the current frame. -/
def transfer (p : Prog R) (s : State R) (target : Label) (args : List R) : Result R :=
  match s.frame.readAll args with
  | none => .stuck
  | some vals =>
    match p.block? s.point.func target with
    | none => .stuck
    | some b =>
      match s.frame.writeAll b.params vals with
      | some fr => .running ⟨⟨s.point.func, target, 0⟩, fr, s.stack, s.mem⟩
      | none => .stuck

/-- One step of the machine, as a total function. -/
def step (p : Prog R) (s : State R) : Result R :=
  match p.fetch s.point with
  | none => .stuck
  | some (.op (.call f args _)) =>
    match s.frame.readAll args with
    | none => .stuck
    | some vals =>
      match p.enter f vals with
      | none => .stuck
      | some (pt, fr) => .running ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩
  | some (.op o) =>
    match o.exec s.frame s.mem with
    | some (fr, m) => .running { s with point := s.point.next, frame := fr, mem := m }
    | none => .stuck
  | some (.term (.jump t as)) => transfer p s t as
  | some (.term (.cond c t₁ a₁ t₂ a₂)) =>
    match s.frame.get c with
    | none => .stuck
    | some x => transfer p s (if x = 0 then t₂ else t₁) (if x = 0 then a₂ else a₁)
  | some (.term (.ret regs)) =>
    match s.frame.readAll regs with
    | none => .stuck
    | some vals =>
      match s.stack with
      | [] => .returned vals s.mem
      | a :: rest =>
        match p.fetch a.point with
        | some (.op (.call _ _ results)) =>
          match a.frame.writeAll results vals with
          | some fr => .running ⟨a.point.next, fr, rest, s.mem⟩
          | none => .stuck
        | _ => .stuck
  | some (.term .trap) => .trapped s.mem

/-- At an op other than a call, `step` is the op's effect on the frame and
memory. The `call` arm of `step` overlaps the general arm, so this is the shape
every other arm actually has. -/
private theorem step_op_of_ne_call {p : Prog R} {s : State R} {o : Op R}
    (hf : p.fetch s.point = some (.op o))
    (hne : ∀ f args results, o ≠ .call f args results) :
    step p s =
      (match o.exec s.frame s.mem with
       | some (fr, m) => .running { s with point := s.point.next, frame := fr, mem := m }
       | none => .stuck) := by
  cases o with
  | call f args results => exact absurd rfl (hne f args results)
  | _ => simp [step, hf]

/-- The non-stuck results of `step`, one constructor per kind. -/
inductive Transition (p : Prog R) : State R → Result R → Prop
  | op {s : State R} {o : Op R} {fr : Frame R} {m : Memory} :
      p.fetch s.point = some (.op o) → o.exec s.frame s.mem = some (fr, m) →
      Transition p s (.running { s with point := s.point.next, frame := fr, mem := m })
  | call {s : State R} {f : FuncId} {args results : List R} {vals : List Word}
      {pt : Point} {fr : Frame R} :
      p.fetch s.point = some (.op (.call f args results)) → s.frame.readAll args = some vals →
      p.enter f vals = some (pt, fr) →
      Transition p s (.running ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩)
  | jump {s : State R} {t : Label} {as : List R} {vals : List Word} {b : Block R} {fr : Frame R} :
      p.fetch s.point = some (.term (.jump t as)) → s.frame.readAll as = some vals →
      p.block? s.point.func t = some b → s.frame.writeAll b.params vals = some fr →
      Transition p s (.running ⟨⟨s.point.func, t, 0⟩, fr, s.stack, s.mem⟩)
  | cond {s : State R} {c : R} {t₁ t₂ : Label} {a₁ a₂ : List R} {x : Word} {vals : List Word}
      {b : Block R} {fr : Frame R} :
      p.fetch s.point = some (.term (.cond c t₁ a₁ t₂ a₂)) → s.frame.get c = some x →
      s.frame.readAll (if x = 0 then a₂ else a₁) = some vals →
      p.block? s.point.func (if x = 0 then t₂ else t₁) = some b →
      s.frame.writeAll b.params vals = some fr →
      Transition p s
        (.running ⟨⟨s.point.func, if x = 0 then t₂ else t₁, 0⟩, fr, s.stack, s.mem⟩)
  | ret {s : State R} {regs : List R} {vals : List Word} {a : Activation R}
      {rest : List (Activation R)} {f : FuncId} {args results : List R} {fr : Frame R} :
      p.fetch s.point = some (.term (.ret regs)) → s.frame.readAll regs = some vals →
      s.stack = a :: rest → p.fetch a.point = some (.op (.call f args results)) →
      a.frame.writeAll results vals = some fr →
      Transition p s (.running ⟨a.point.next, fr, rest, s.mem⟩)
  | halt {s : State R} {regs : List R} {vals : List Word} :
      p.fetch s.point = some (.term (.ret regs)) → s.frame.readAll regs = some vals →
      s.stack = [] → Transition p s (.returned vals s.mem)
  | trap {s : State R} :
      p.fetch s.point = some (.term .trap) → Transition p s (.trapped s.mem)

theorem Transition.step_eq {p : Prog R} {s : State R} {r : Result R}
    (h : Transition p s r) : step p s = r := by
  cases h with
  | op hf he =>
    rename_i o _ _
    have hne : ∀ f args results, o ≠ .call f args results := by
      rintro f args results rfl
      simp [Op.exec] at he
    rw [step_op_of_ne_call hf hne, he]
  | call hf ha he => simp [step, hf, ha, he]
  | jump hf hv hb hw => simp [step, hf, transfer, hv, hb, hw]
  | cond hf hc hv hb hw =>
    rename_i c t₁ t₂ a₁ a₂ x _ _ _
    have hstep : step p s =
        transfer p s (if x = 0 then t₂ else t₁) (if x = 0 then a₂ else a₁) := by
      simp [step, hf, hc]
    rw [hstep, transfer, hv, hb]
    simp [hw]
  | ret hf hv hs ha hw => simp [step, hf, hv, hs, ha, hw]
  | halt hf hv hs => simp [step, hf, hv, hs]
  | trap hf => simp [step, hf]

theorem Transition.of_step {p : Prog R} {s : State R} {r : Result R}
    (h : step p s = r) (hr : r ≠ .stuck) : Transition p s r := by
  subst h
  have key : ∀ {r}, Transition p s r → Transition p s (step p s) := fun t => t.step_eq ▸ t
  cases hf : p.fetch s.point with
  | none => simp [step, hf] at hr
  | some c =>
    cases c with
    | op o =>
      by_cases hcall : ∃ f args results, o = (.call f args results : Op R)
      · obtain ⟨f, args, results, rfl⟩ := hcall
        cases ha : s.frame.readAll args with
        | none => simp [step, hf, ha] at hr
        | some vals =>
          cases he : p.enter f vals with
          | none => simp [step, hf, ha, he] at hr
          | some r' =>
            obtain ⟨pt, fr⟩ := r'
            exact key (.call hf ha he)
      · have hne : ∀ f args results, o ≠ .call f args results := by
          intro f args results heq
          exact hcall ⟨f, args, results, heq⟩
        rw [step_op_of_ne_call hf hne] at hr ⊢
        cases he : o.exec s.frame s.mem with
        | none => simp [he] at hr
        | some r' =>
          obtain ⟨fr, m⟩ := r'
          exact .op hf he
    | term t =>
      cases t with
      | jump tgt as =>
        cases hv : s.frame.readAll as with
        | none => simp [step, hf, transfer, hv] at hr
        | some vals =>
          cases hb : p.block? s.point.func tgt with
          | none => simp [step, hf, transfer, hv, hb] at hr
          | some b =>
            cases hw : s.frame.writeAll b.params vals with
            | none => simp [step, hf, transfer, hv, hb, hw] at hr
            | some fr => exact key (.jump hf hv hb hw)
      | cond c t₁ a₁ t₂ a₂ =>
        cases hc : s.frame.get c with
        | none => simp [step, hf, hc] at hr
        | some x =>
          have hstep : step p s =
              transfer p s (if x = 0 then t₂ else t₁) (if x = 0 then a₂ else a₁) := by
            simp [step, hf, hc]
          rw [hstep] at hr
          simp only [transfer] at hr
          cases hv : s.frame.readAll (if x = 0 then a₂ else a₁) with
          | none => rw [hv] at hr; simp at hr
          | some vals =>
            rw [hv] at hr
            cases hb : p.block? s.point.func (if x = 0 then t₂ else t₁) with
            | none => rw [hb] at hr; simp at hr
            | some b =>
              rw [hb] at hr
              cases hw : s.frame.writeAll b.params vals with
              | none => simp [hw] at hr
              | some fr => exact key (.cond hf hc hv hb hw)
      | ret regs =>
        cases hv : s.frame.readAll regs with
        | none => simp [step, hf, hv] at hr
        | some vals =>
          cases hs : s.stack with
          | nil => exact key (.halt hf hv hs)
          | cons a rest =>
            cases ha : p.fetch a.point with
            | none => simp [step, hf, hv, hs, ha] at hr
            | some c' =>
              cases c' with
              | term t' => simp [step, hf, hv, hs, ha] at hr
              | op o' =>
                cases o' with
                | call f args results =>
                  cases hw : a.frame.writeAll results vals with
                  | none => simp [step, hf, hv, hs, ha, hw] at hr
                  | some fr => exact key (.ret hf hv hs ha hw)
                | _ => simp [step, hf, hv, hs, ha] at hr
      | trap => exact key (.trap hf)

/-! ### Executions and behaviours -/

/-- One running step. -/
def Step (p : Prog R) (s s' : State R) : Prop := step p s = .running s'

/-- Zero or more running steps. -/
abbrev Steps (p : Prog R) : State R → State R → Prop := Relation.ReflTransGen (Step p)

/-- An infinite sequence of running steps. -/
def Diverges (p : Prog R) (s : State R) : Prop := Silmaril.InfiniteTrace (Step p) s

/-- What a whole run of the machine shows. -/
inductive Behavior where
  | returned (values : List Word) (mem : Memory)
  | trapped (mem : Memory)
  | stuck
  | diverges

/-- The final result of `step` corresponding to a finite behaviour. -/
def Behavior.result? : Behavior → Option (Result R)
  | .returned vs m => some (.returned vs m)
  | .trapped m => some (.trapped m)
  | .stuck => some .stuck
  | .diverges => none

/-- `s` shows behaviour `b`. -/
def Behaves (p : Prog R) (s : State R) : Behavior → Prop
  | .returned vs m => ∃ s', Steps p s s' ∧ step p s' = .returned vs m
  | .trapped m => ∃ s', Steps p s s' ∧ step p s' = .trapped m
  | .stuck => ∃ s', Steps p s s' ∧ step p s' = .stuck
  | .diverges => Diverges p s

theorem Step.deterministic {p : Prog R} {s a b : State R} (ha : Step p s a) (hb : Step p s b) :
    a = b := by
  unfold Step at ha hb
  rw [ha] at hb
  cases hb
  rfl

theorem step_rightUnique (p : Prog R) : Relator.RightUnique (Step p) :=
  fun _ _ _ ha hb => Step.deterministic ha hb

/-- Two executions from the same state are prefixes of one another. -/
private theorem Steps.total {p : Prog R} {s a b : State R} (ha : Steps p s a) (hb : Steps p s b) :
    Steps p a b ∨ Steps p b a :=
  Relation.ReflTransGen.total_of_right_unique (step_rightUnique p) ha hb

/-- A state whose step is not running has no successor. -/
private theorem Steps.eq_of_final {p : Prog R} {s t : State R} (h : Steps p s t)
    (final : ∀ s', step p s ≠ .running s') : t = s := by
  cases h.cases_head with
  | inl h => exact h.symm
  | inr h =>
    obtain ⟨c, hc, _⟩ := h
    exact absurd hc (final c)

/-- Divergence is inherited by every reachable state. -/
private theorem Diverges.of_steps {p : Prog R} {s t : State R} (d : Diverges p s)
    (h : Steps p s t) : Diverges p t := by
  induction h with
  | refl => exact d
  | tail _ hstep ih =>
    obtain ⟨b, hb, tail⟩ := ih.unfold
    rw [Step.deterministic hstep hb]
    exact tail

private theorem Diverges.running {p : Prog R} {s : State R} (d : Diverges p s) :
    ∃ s', step p s = .running s' := by
  obtain ⟨b, hb, _⟩ := d.unfold
  exact ⟨b, hb⟩

/-- Prefixing a behaviour with one step. -/
theorem Behaves.head {p : Prog R} {s s' : State R} {b : Behavior}
    (h : Step p s s') (hb : Behaves p s' b) : Behaves p s b := by
  cases b with
  | returned vs m => obtain ⟨t, ht, hf⟩ := hb; exact ⟨t, .head h ht, hf⟩
  | trapped m => obtain ⟨t, ht, hf⟩ := hb; exact ⟨t, .head h ht, hf⟩
  | stuck => obtain ⟨t, ht, hf⟩ := hb; exact ⟨t, .head h ht, hf⟩
  | diverges => exact Silmaril.InfiniteTrace.fold h hb

private theorem final_unique {p : Prog R} {s a b : State R} {ra rb : Result R}
    (ha : Steps p s a) (hb : Steps p s b) (fa : step p a = ra) (fb : step p b = rb)
    (na : ∀ x, ra ≠ .running x) (nb : ∀ x, rb ≠ .running x) : ra = rb := by
  rcases Steps.total ha hb with h | h
  · rw [Steps.eq_of_final h (fun x e => na x (fa ▸ e))] at fb
    rw [← fa, ← fb]
  · rw [Steps.eq_of_final h (fun x e => nb x (fb ▸ e))] at fa
    rw [← fa, ← fb]

private theorem not_diverges_of_final {p : Prog R} {s a : State R} {r : Result R}
    (ha : Steps p s a) (fa : step p a = r) (na : ∀ x, r ≠ .running x) : ¬ Diverges p s := by
  intro d
  obtain ⟨x, hx⟩ := (d.of_steps ha).running
  exact na x (fa ▸ hx)

/-- A finite behaviour, as a final state reached by running steps. -/
private theorem Behaves.final {p : Prog R} {s : State R} {b : Behavior} {r : Result R}
    (hb : b.result? = some r) (h : Behaves p s b) :
    ∃ t, Steps p s t ∧ step p t = r ∧ ∀ x, r ≠ .running x := by
  cases b <;> simp only [Behavior.result?, Option.some.injEq, reduceCtorEq] at hb <;> subst hb <;>
    obtain ⟨t, ht, hf⟩ := h <;> exact ⟨t, ht, hf, by intro x hx; cases hx⟩

omit [DecidableEq R] in
private theorem Behavior.result?_injective {b₁ b₂ : Behavior} {r : Result R}
    (h₁ : b₁.result? = some r) (h₂ : b₂.result? = some r) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;>
    simp only [Behavior.result?, Option.some.injEq, reduceCtorEq] at h₁ h₂ <;> subst h₁ <;> simp_all

omit [DecidableEq R] in
private theorem Behavior.result?_isSome :
    ∀ b : Behavior, b ≠ .diverges → ∃ r : Result R, b.result? = some r
  | .returned _ _, _ => ⟨_, rfl⟩
  | .trapped _, _ => ⟨_, rfl⟩
  | .stuck, _ => ⟨_, rfl⟩
  | .diverges, h => absurd rfl h

/-- **A state has at most one behaviour.** -/
theorem Behaves.unique {p : Prog R} {s : State R} {b₁ b₂ : Behavior}
    (h₁ : Behaves p s b₁) (h₂ : Behaves p s b₂) : b₁ = b₂ := by
  by_cases d₁ : b₁ = .diverges
  · by_cases d₂ : b₂ = .diverges
    · rw [d₁, d₂]
    · obtain ⟨r, hr⟩ := Behavior.result?_isSome (R := R) b₂ d₂
      obtain ⟨t, ht, ft, nt⟩ := Behaves.final hr h₂
      subst d₁
      exact absurd h₁ (not_diverges_of_final ht ft nt)
  · obtain ⟨r, hr⟩ := Behavior.result?_isSome (R := R) b₁ d₁
    obtain ⟨t, ht, ft, nt⟩ := Behaves.final hr h₁
    by_cases d₂ : b₂ = .diverges
    · subst d₂
      exact absurd h₂ (not_diverges_of_final ht ft nt)
    · obtain ⟨r', hr'⟩ := Behavior.result?_isSome (R := R) b₂ d₂
      obtain ⟨t', ht', ft', nt'⟩ := Behaves.final hr' h₂
      have := final_unique ht ht' ft ft' nt nt'
      subst this
      exact Behavior.result?_injective hr hr'

/-- **Every state has a behaviour** (classically). -/
theorem Behaves.exists (p : Prog R) (s : State R) : ∃ b, Behaves p s b := by
  classical
  by_cases fin : ∃ t, Steps p s t ∧ ∀ x, step p t ≠ .running x
  · obtain ⟨t, ht, final⟩ := fin
    cases hr : step p t with
    | running x => exact absurd hr (final x)
    | returned vs m => exact ⟨.returned vs m, t, ht, hr⟩
    | trapped m => exact ⟨.trapped m, t, ht, hr⟩
    | stuck => exact ⟨.stuck, t, ht, hr⟩
  · refine ⟨.diverges, ?_⟩
    apply Silmaril.InfiniteTrace.coinduct (fun t => Steps p s t) ?_ Relation.ReflTransGen.refl
    intro t ht
    have : ∃ x, step p t = .running x := by
      by_contra hno
      exact fin ⟨t, ht, fun x hx => hno ⟨x, hx⟩⟩
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx, ht.tail hx⟩

/-- Run at most `n` steps. -/
def run (p : Prog R) : Nat → State R → Result R
  | 0, s => .running s
  | n + 1, s =>
    match step p s with
    | .running s' => run p n s'
    | r => r

theorem run_final {p : Prog R} {n : Nat} {s : State R} {r : Result R} (h : run p n s = r)
    (hr : ∀ x, r ≠ .running x) : ∃ s', Steps p s s' ∧ step p s' = r := by
  induction n generalizing s with
  | zero => subst h; exact absurd rfl (hr s)
  | succ n ih =>
    unfold run at h
    split at h
    · obtain ⟨t, ht, hf⟩ := ih h
      exact ⟨t, Relation.ReflTransGen.head (by assumption) ht, hf⟩
    · exact ⟨s, .refl, h⟩

theorem run_returned {p : Prog R} {n : Nat} {s : State R} {vs : List Word} {m : Memory}
    (h : run p n s = .returned vs m) : Behaves p s (.returned vs m) :=
  run_final h (by intro x hx; cases hx)

/-- Run a whole program from `start`; `stuck` if the start is undefined. -/
def Prog.runMain (p : Prog R) (fuel : Nat) (f : FuncId) (args : List Word) (mem : Memory) :
    Result R :=
  match p.start f args mem with
  | some s => run p fuel s
  | none => .stuck

/-! ### `RTL.SSA` as a `Machine.Behaviour.Semantics` -/

/-- The outcome a result shows when a run stops there; `.stuck` is undefined
behaviour, as in `RTL`. -/
def outcomeOf : Result R → Option (Silmaril.Machine.Behaviour.Outcome Ret Memory Empty)
  | .returned vs m => some (.returned (vs, m))
  | .trapped m => some (.trapped m)
  | .stuck => some .undefined
  | .running _ => none

/-- `RTL.SSA` as a small-step semantics with behaviours. -/
def sem (p : Prog R) : Silmaril.Machine.Behaviour.Semantics (State R) Ret Memory Empty where
  step := Step p
  final s o := outcomeOf (step p s) = some o

/-- A state is final exactly when its step shows a finite outcome. -/
theorem sem_final_iff {p : Prog R} {s : State R}
    {o : Silmaril.Machine.Behaviour.Outcome Ret Memory Empty} :
    (sem p).final s o ↔ outcomeOf (step p s) = some o := Iff.rfl

/-- **`RTL.SSA` is deterministic.** -/
theorem sem_deterministic (p : Prog R) : (sem p).Deterministic where
  step_unique _ _ _ ha hb := Step.deterministic ha hb
  final_unique _ _ _ h h' := by
    rw [sem_final_iff] at h h'
    rw [h] at h'
    exact Option.some.inj h'
  final_stop s _ h t ht := by
    have hs : step p s = .running t := ht
    rw [sem_final_iff, hs] at h
    simp [outcomeOf] at h

/-- **`RTL.SSA` has progress**, for the same reason as `RTL`: a stuck state
shows `undefined` rather than nothing. -/
theorem sem_progress (p : Prog R) : (sem p).Progress := by
  intro s
  cases h : step p s with
  | running s' => exact .inl ⟨s', h⟩
  | returned vs m => exact .inr ⟨.returned (vs, m), by rw [sem_final_iff, h]; rfl, by simp⟩
  | trapped m => exact .inr ⟨.trapped m, by rw [sem_final_iff, h]; rfl, by simp⟩
  | stuck => exact .inr ⟨.undefined, by rw [sem_final_iff, h]; rfl, by simp⟩

theorem beh_returned_iff {p : Prog R} {s : State R} {vs : List Word} {m : Memory} :
    (sem p).Beh s (.returned (vs, m)) ↔ Behaves p s (.returned vs m) := by
  rw [Silmaril.Machine.Behaviour.Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨t, ht, hf⟩
    rw [sem_final_iff] at hf
    cases hs : step p t with
    | returned vs' m' =>
      rw [hs] at hf
      simp only [outcomeOf, Option.some.injEq, Silmaril.Machine.Behaviour.Outcome.returned.injEq,
        Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨t, ht, hs⟩
    | _ => rw [hs] at hf; simp [outcomeOf] at hf
  · rintro ⟨t, ht, hf⟩
    exact ⟨t, ht, by rw [sem_final_iff, hf]; rfl⟩

theorem beh_trapped_iff {p : Prog R} {s : State R} {m : Memory} :
    (sem p).Beh s (.trapped m) ↔ Behaves p s (.trapped m) := by
  rw [Silmaril.Machine.Behaviour.Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨t, ht, hf⟩
    rw [sem_final_iff] at hf
    cases hs : step p t with
    | trapped m' =>
      rw [hs] at hf
      simp only [outcomeOf, Option.some.injEq, Silmaril.Machine.Behaviour.Outcome.trapped.injEq] at hf
      exact ⟨t, ht, hf ▸ hs⟩
    | _ => rw [hs] at hf; simp [outcomeOf] at hf
  · rintro ⟨t, ht, hf⟩
    exact ⟨t, ht, by rw [sem_final_iff, hf]; rfl⟩

theorem beh_undefined_iff {p : Prog R} {s : State R} :
    (sem p).Beh s .undefined ↔ Behaves p s .stuck := by
  rw [Silmaril.Machine.Behaviour.Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨t, ht, hf⟩
    rw [sem_final_iff] at hf
    cases hs : step p t with
    | stuck => exact ⟨t, ht, hs⟩
    | _ => rw [hs] at hf; simp [outcomeOf] at hf
  · rintro ⟨t, ht, hf⟩
    exact ⟨t, ht, by rw [sem_final_iff, hf]; rfl⟩

theorem beh_diverges_iff {p : Prog R} {s : State R} :
    (sem p).Beh s .diverges ↔ Diverges p s := Iff.rfl

/-- **`Safe` is "does not get stuck".** -/
theorem safe_iff_not_stuck {p : Prog R} {s : State R} :
    (sem p).Safe s ↔ ¬ Behaves p s .stuck := not_congr beh_undefined_iff

/-! ## Well-formedness implies definedness

The invariant: at op index `i` of block `l`, the frame has written every
register that the definitions of the strict dominators of `l`, the parameters of
`l` and the ops of `l` before `i` provide. `UsesDominated` says exactly that
every use is in that set, and the set is inductive along edges because a strict
dominator of a successor dominates its predecessor (`Graph.Digraph.Dominates.of_edge`). -/

namespace Func

variable {R : Type}

/-- The registers a frame is guaranteed to hold at op index `i` of block `l`. -/
def Defined (fn : Func R) (l : Label) (i : Nat) (r : R) : Prop :=
  (∃ a, fn.Dominates a l ∧ a ≠ l ∧ r ∈ fn.defsOf a) ∨
    ∃ b, fn.block? l = some b ∧ (r ∈ b.params ∨ ∃ o ∈ b.ops.take i, r ∈ o.defs)

/-- A frame covers a point when it has written every register guaranteed
there. -/
def Covers (fn : Func R) (fr : Frame R) (l : Label) (i : Nat) : Prop :=
  ∀ r, fn.Defined l i r → (fr.get r).isSome

/-- Later points of a block are guaranteed more. -/
theorem Defined.mono {fn : Func R} {l i j : Nat} {r : R} (hij : i ≤ j)
    (h : fn.Defined l i r) : fn.Defined l j r := by
  rcases h with h | ⟨b, hb, h⟩
  · exact .inl h
  · refine .inr ⟨b, hb, ?_⟩
    rcases h with h | ⟨o, ho, hd⟩
    · exact .inl h
    · refine .inr ⟨o, ?_, hd⟩
      rw [show b.ops.take i = (b.ops.take j).take i by
        rw [List.take_take, Nat.min_eq_left hij]] at ho
      exact List.take_subset _ _ ho

/-- At a block's terminator the point is guaranteed everything the block
defines. -/
theorem defined_of_mem_defsOf {fn : Func R} {l : Label} {b : Block R} {r : R}
    (hb : fn.block? l = some b) (hr : r ∈ fn.defsOf l) : fn.Defined l b.ops.length r := by
  rw [defsOf, hb] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact .inr ⟨b, hb, .inl hr⟩
  · obtain ⟨o, ho, hd⟩ := List.mem_flatMap.mp hr
    exact .inr ⟨b, hb, .inr ⟨o, by rwa [List.take_length], hd⟩⟩

/-- `okUse` decides `Defined`: this is the link between the well-formedness
checker and the invariant. -/
theorem defined_of_okUse [DecidableEq R] {fn : Func R} {l j : Nat} {r : R}
    (h : fn.okUse l j r = true) : fn.Defined l j r := by
  rw [okUse, Bool.or_eq_true] at h
  rcases h with h | h
  · cases hb : fn.block? l with
    | none => rw [hb] at h; simp at h
    | some b =>
      rw [hb, Bool.or_eq_true] at h
      refine .inr ⟨b, hb, ?_⟩
      rcases h with h | h
      · exact .inl (by simpa using h)
      · obtain ⟨o, ho, hd⟩ := List.any_eq_true.mp h
        exact .inr ⟨o, ho, by simpa using hd⟩
  · obtain ⟨a, -, ha⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq] at ha
    exact .inl ⟨a, ha.1.2, ha.1.1, ha.2⟩

/-- A terminator's successor that names an existing block is a control-flow
edge. -/
theorem edge_of_term {fn : Func R} {l t : Label} {b : Block R}
    (hb : fn.block? l = some b) (ht : t ∈ b.term.successors) (hlt : t < fn.blocks.length) :
    fn.Edge l t := by
  simp only [Edge, digraph, Graph.Digraph.Edge, Graph.Digraph.step, List.mem_filter, succ, hb]
  exact ⟨ht, decide_eq_true hlt⟩

end Func

/-! ### Frames, ops and fetching -/

section Helpers

variable {R : Type} [DecidableEq R]

/-- Writing registers never unwrites one. -/
private theorem writeAll_mono {fr fr' : Frame R} {rs : List R} {vs : List Word} {r : R}
    (h : fr.writeAll rs vs = some fr') (hr : (fr.get r).isSome) : (fr'.get r).isSome := by
  induction rs generalizing fr vs with
  | nil => cases vs with
    | nil => cases h; exact hr
    | cons _ _ => simp [Frame.writeAll] at h
  | cons x xs ih => cases vs with
    | nil => simp [Frame.writeAll] at h
    | cons v vs =>
      refine ih (vs := vs) h ?_
      simp only [Frame.get_set]
      split <;> simp [hr]

/-- Every register written by `writeAll` is afterwards defined. -/
private theorem writeAll_isSome {fr fr' : Frame R} {rs : List R} {vs : List Word} {r : R}
    (h : fr.writeAll rs vs = some fr') (hr : r ∈ rs) : (fr'.get r).isSome := by
  induction rs generalizing fr vs with
  | nil => simp at hr
  | cons x xs ih => cases vs with
    | nil => simp [Frame.writeAll] at h
    | cons v vs =>
      have h' : (fr.set x v).writeAll xs vs = some fr' := h
      rcases List.mem_cons.mp hr with rfl | hr
      · refine writeAll_mono h' ?_
        simp [Frame.get_set]
      · exact ih (vs := vs) h' hr

/-- An op writes exactly its destinations: its effect on the frame is a
`writeAll` of `Op.defs`. This is what makes the covering invariant inductive
through straight-line code. -/
private theorem exec_writeAll {o : Op R} {fr fr' : Frame R} {m m' : Memory}
    (h : o.exec fr m = some (fr', m')) : ∃ ws, fr.writeAll o.defs ws = some fr' := by
  cases o with
  | const d v =>
    simp only [Op.exec, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[v], by simp [Op.defs, Frame.writeAll, h.1]⟩
  | move d src =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, -, hx, -⟩ := h
    exact ⟨[x], by simp [Op.defs, Frame.writeAll, hx]⟩
  | unary op d src =>
    simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, -, hx, -⟩ := h
    exact ⟨[op.eval x], by simp [Op.defs, Frame.writeAll, hx]⟩
  | binary op d a b =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, -, y, -, z, -, hz, -⟩ := h
    exact ⟨[z], by simp [Op.defs, Frame.writeAll, hz]⟩
  | load w e d base off =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨a, -, z, -, hz, -⟩ := h
    exact ⟨[z], by simp [Op.defs, Frame.writeAll, hz]⟩
  | store w base off src =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨a, -, x, -, m₂, -, h'⟩ := h
    exact ⟨[], by simp [Op.defs, Frame.writeAll, h'.1]⟩
  | call f args results => simp [Op.exec] at h

end Helpers

section Fetch

variable {R : Type}

/-- Fetching an op names the block and the op's index in it. -/
private theorem fetch_op {p : Prog R} {pt : Point} {o : Op R} (hf : p.fetch pt = some (.op o)) :
    ∃ b, p.block? pt.func pt.label = some b ∧ b.ops[pt.index]? = some o := by
  unfold Prog.fetch at hf
  cases hb : p.block? pt.func pt.label with
  | none => rw [hb] at hf; simp at hf
  | some b =>
    rw [hb] at hf
    simp only [Option.bind_some] at hf
    split at hf
    · rename_i o' heq
      simp only [Option.some.injEq, Code.op.injEq] at hf
      exact ⟨b, rfl, by rw [heq, hf]⟩
    · split at hf <;> simp at hf

/-- Fetching a terminator says the index is one past the last op. -/
private theorem fetch_term {p : Prog R} {pt : Point} {t : Term R}
    (hf : p.fetch pt = some (.term t)) :
    ∃ b, p.block? pt.func pt.label = some b ∧ pt.index = b.ops.length ∧ t = b.term := by
  unfold Prog.fetch at hf
  cases hb : p.block? pt.func pt.label with
  | none => rw [hb] at hf; simp at hf
  | some b =>
    rw [hb] at hf
    simp only [Option.bind_some] at hf
    split at hf
    · simp at hf
    · split at hf
      · rename_i hlen
        simp only [Option.some.injEq, Code.term.injEq] at hf
        exact ⟨b, rfl, hlen, hf.symm⟩
      · simp at hf

end Fetch

namespace Prog

variable {R : Type} [DecidableEq R]

/-- Every function of the program is well-formed. -/
def WellFormed (p : Prog R) : Prop := ∀ fn ∈ p.funcs, fn.WellFormed

instance (p : Prog R) : Decidable p.WellFormed := inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- An activation is sound: its function exists, its block is reachable, and
its frame covers its point. -/
def Ok (p : Prog R) (pt : Point) (fr : Frame R) : Prop :=
  ∃ fn, p.func? pt.func = some fn ∧ fn.Reachable pt.label ∧ fn.Covers fr pt.label pt.index

/-- The invariant of every state of a run of a well-formed program: the current
activation and every suspended one are sound. -/
def Invariant (p : Prog R) (s : State R) : Prop :=
  p.Ok s.point s.frame ∧ ∀ a ∈ s.stack, p.Ok a.point a.frame

/-- The registers read by the code at a point; a missing point reads none. -/
def usesAt (p : Prog R) (pt : Point) : List R :=
  match p.fetch pt with
  | some (.op o) => o.uses
  | some (.term t) => t.uses
  | none => []

omit [DecidableEq R] in
/-- The blocks of a program's function are the function's blocks. -/
private theorem block?_eq {p : Prog R} {f : FuncId} {l : Label} {fn : Func R}
    (hfn : p.func? f = some fn) : p.block? f l = fn.block? l := by
  simp [Prog.block?, hfn]

/-- Entering a function lands on a sound activation: nothing strictly dominates
the entry block, so the entry's parameters are all the entry point is
guaranteed, and `enter` has just written them. -/
theorem Ok_of_enter {p : Prog R} {f : FuncId} {vals : List Word} {pt : Point} {fr : Frame R}
    (h : p.enter f vals = some (pt, fr)) : p.Ok pt fr := by
  simp only [enter, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨fn, hfn, b, hb, fr0, hw, hpt, hfr⟩ := h
  subst hfr
  subst hpt
  refine ⟨fn, hfn, Graph.Digraph.reachable_entry _, ?_⟩
  intro r hr
  rcases hr with ⟨a, hda, hne, -⟩ | ⟨bb, hbb, hcase⟩
  · exact absurd (Graph.Digraph.Dominates.eq_entry hda) hne
  · rw [show fn.block? fn.entry = some b from hb] at hbb
    have : bb = b := (Option.some.inj hbb).symm
    subst this
    rcases hcase with hp | ⟨o, ho, -⟩
    · exact writeAll_isSome hw hp
    · simp at ho

/-- The covering invariant crosses an edge. Both `jump` and `cond` land here:
the target's parameters are written by the transfer, and a strict dominator of
the target either dominates the source block (by `Dominates.of_edge`) or is the
source block itself, whose definitions the frame already covers because the
source is sitting at its terminator. -/
private theorem cover_target {p : Prog R} {s : State R} {fn : Func R} {bcur bt : Block R}
    {t : Label} {vals : List Word} {fr : Frame R}
    (hfn : p.func? s.point.func = some fn) (hreach : fn.Reachable s.point.label)
    (hcov : fn.Covers s.frame s.point.label s.point.index)
    (hstack : ∀ a ∈ s.stack, p.Ok a.point a.frame)
    (hbcur : fn.block? s.point.label = some bcur) (hidx : s.point.index = bcur.ops.length)
    (ht : t ∈ bcur.term.successors) (hb : fn.block? t = some bt)
    (hw : s.frame.writeAll bt.params vals = some fr) :
    p.Invariant ⟨⟨s.point.func, t, 0⟩, fr, s.stack, s.mem⟩ := by
  have hlt : t < fn.blocks.length := (List.getElem?_eq_some_iff.mp hb).1
  have hedge : fn.Edge s.point.label t := Func.edge_of_term hbcur ht hlt
  refine ⟨⟨fn, hfn, hreach.step hedge, ?_⟩, hstack⟩
  intro r hr
  rcases hr with ⟨a, hda, hne, hrd⟩ | ⟨bb, hbb, hcase⟩
  · have hda2 : fn.Dominates a s.point.label := Graph.Digraph.Dominates.of_edge hedge hda hne
    by_cases hal : a = s.point.label
    · subst hal
      refine writeAll_mono hw (hcov r ?_)
      rw [hidx]
      exact Func.defined_of_mem_defsOf hbcur hrd
    · exact writeAll_mono hw (hcov r (.inl ⟨a, hda2, hal, hrd⟩))
  · have : bb = bt := by rw [hb] at hbb; exact (Option.some.inj hbb).symm
    subst this
    rcases hcase with hp | ⟨o, ho, -⟩
    · exact writeAll_isSome hw hp
    · simp at ho

/-- The start state satisfies the invariant. Well-formedness is not used:
nothing strictly dominates the entry block, so the entry's parameters are
everything the entry point is guaranteed. -/
theorem Invariant.start {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory} {s : State R}
    (_hwf : p.WellFormed) (h : p.start f args mem = some s) : p.Invariant s := by
  unfold Prog.start at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨pt, fr⟩, he, rfl⟩ := h
  exact ⟨Ok_of_enter he, by simp⟩

/-- The invariant is preserved by every step. Well-formedness is not used: a
transition that has already succeeded carries the writes it performed, so
`ArgsMatch` and `SingleAssignment` are not needed here. Only
`Invariant.uses_isSome` consumes `WellFormed`, and only through
`UsesDominated`. -/
theorem Invariant.step {p : Prog R} {s s' : State R} (_hwf : p.WellFormed)
    (hi : p.Invariant s) (hs : Step p s s') : p.Invariant s' := by
  obtain ⟨⟨fn, hfn, hreach, hcov⟩, hstack⟩ := hi
  have ht := Transition.of_step hs (by simp)
  cases ht with
  | op hf he =>
    obtain ⟨b, hb, hop⟩ := fetch_op hf
    rw [block?_eq hfn] at hb
    obtain ⟨ws, hws⟩ := exec_writeAll he
    refine ⟨⟨fn, hfn, hreach, ?_⟩, hstack⟩
    show fn.Covers _ s.point.label (s.point.index + 1)
    intro r hr
    rcases hr with hdom | ⟨bb, hbb, hcase⟩
    · exact writeAll_mono hws (hcov r (.inl hdom))
    · have : bb = b := by rw [hb] at hbb; exact (Option.some.inj hbb).symm
      subst this
      rcases hcase with hp | ⟨o2, ho2, hd⟩
      · exact writeAll_mono hws (hcov r (.inr ⟨bb, hbb, .inl hp⟩))
      · rw [List.take_add_one] at ho2
        rcases List.mem_append.mp ho2 with ho2 | ho2
        · exact writeAll_mono hws (hcov r (.inr ⟨bb, hbb, .inr ⟨o2, ho2, hd⟩⟩))
        · rw [hop] at ho2
          simp only [Option.toList_some, List.mem_singleton] at ho2
          subst ho2
          exact writeAll_isSome hws hd
  | call hf ha he =>
    refine ⟨Ok_of_enter he, ?_⟩
    intro a hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨fn, hfn, hreach, hcov⟩
    · exact hstack a hmem
  | jump hf hv hb hw =>
    obtain ⟨bcur, hbcur, hidx, hterm⟩ := fetch_term hf
    rw [block?_eq hfn] at hbcur hb
    exact cover_target hfn hreach hcov hstack hbcur hidx
      (by rw [← hterm]; simp [Term.successors]) hb hw
  | cond hf hc hv hb hw =>
    rename_i c t1 t2 a1 a2 x _ _ _
    obtain ⟨bcur, hbcur, hidx, hterm⟩ := fetch_term hf
    rw [block?_eq hfn] at hbcur hb
    refine cover_target hfn hreach hcov hstack hbcur hidx ?_ hb hw
    rw [← hterm]
    show (if x = 0 then t2 else t1) ∈ [t1, t2]
    split <;> simp
  | ret hf hv hstk ha hwr =>
    rename_i regs vals act rest f args results fr
    have hact : p.Ok act.point act.frame := hstack act (by rw [hstk]; simp)
    obtain ⟨fn2, hfn2, hreach2, hcov2⟩ := hact
    obtain ⟨b, hb, hop⟩ := fetch_op ha
    rw [block?_eq hfn2] at hb
    refine ⟨⟨fn2, hfn2, hreach2, ?_⟩, fun a2 hmem => hstack a2 (by rw [hstk]; simp [hmem])⟩
    show fn2.Covers _ act.point.label (act.point.index + 1)
    intro r hr
    rcases hr with hdom | ⟨bb, hbb, hcase⟩
    · exact writeAll_mono hwr (hcov2 r (.inl hdom))
    · have : bb = b := by rw [hb] at hbb; exact (Option.some.inj hbb).symm
      subst this
      rcases hcase with hp | ⟨o2, ho2, hd⟩
      · exact writeAll_mono hwr (hcov2 r (.inr ⟨bb, hbb, .inl hp⟩))
      · rw [List.take_add_one] at ho2
        rcases List.mem_append.mp ho2 with ho2 | ho2
        · exact writeAll_mono hwr (hcov2 r (.inr ⟨bb, hbb, .inr ⟨o2, ho2, hd⟩⟩))
        · rw [hop] at ho2
          simp only [Option.toList_some, List.mem_singleton] at ho2
          subst ho2
          exact writeAll_isSome hwr (by simpa [Op.defs] using hd)

theorem Invariant.steps {p : Prog R} {s s' : State R} (hwf : p.WellFormed)
    (hi : p.Invariant s) (hs : Steps p s s') : p.Invariant s' := by
  induction hs with
  | refl => exact hi
  | tail _ hstep ih => exact ih.step hwf hstep

/-- Under the invariant every register the current code reads has been
written. -/
theorem Invariant.uses_isSome {p : Prog R} {s : State R} (hwf : p.WellFormed)
    (hi : p.Invariant s) : ∀ r ∈ p.usesAt s.point, (s.frame.get r).isSome := by
  obtain ⟨⟨fn, hfn, -, hcov⟩, -⟩ := hi
  have hfnwf : fn.WellFormed := hwf fn (List.mem_of_getElem? hfn)
  have hud := hfnwf.usesDominated
  rw [Func.UsesDominated, Func.usesDominated, List.all_eq_true] at hud
  intro r hr
  rw [usesAt] at hr
  cases hf : p.fetch s.point with
  | none => rw [hf] at hr; simp at hr
  | some code =>
    rw [hf] at hr
    cases code with
    | op o =>
      obtain ⟨b, hb, hop⟩ := fetch_op hf
      rw [block?_eq hfn] at hb
      have hlt : s.point.label < fn.blocks.length := (List.getElem?_eq_some_iff.mp hb).1
      have h1 := hud s.point.label (List.mem_range.mpr hlt)
      rw [hb] at h1
      simp only [Bool.and_eq_true, List.all_eq_true] at h1
      have hidx : s.point.index < b.ops.length := (List.getElem?_eq_some_iff.mp hop).1
      have h2 := h1.1 s.point.index (List.mem_range.mpr hidx)
      rw [hop, List.all_eq_true] at h2
      exact hcov r (Func.defined_of_okUse (h2 r hr))
    | term t =>
      obtain ⟨b, hb, hidx, hterm⟩ := fetch_term hf
      rw [block?_eq hfn] at hb
      have hlt : s.point.label < fn.blocks.length := (List.getElem?_eq_some_iff.mp hb).1
      have h1 := hud s.point.label (List.mem_range.mpr hlt)
      rw [hb] at h1
      simp only [Bool.and_eq_true, List.all_eq_true] at h1
      subst hterm
      rw [← hidx] at h1
      exact hcov r (Func.defined_of_okUse (h1.2 r hr))

end Prog

/-- **A well-formed SSA program never reads an unwritten register.** Every
state reachable from a whole-program start reads only registers that have been
written, so no execution gets stuck on an unwritten register; the remaining
stuck states are the undefined behaviour of the operators themselves. -/
theorem reachable_uses_isSome {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory}
    {s₀ s : State R} (hwf : p.WellFormed) (hstart : p.start f args mem = some s₀)
    (hreach : Steps p s₀ s) : ∀ r ∈ p.usesAt s.point, (s.frame.get r).isSome :=
  Prog.Invariant.uses_isSome hwf (Prog.Invariant.steps hwf (Prog.Invariant.start hwf hstart) hreach)

end Silmaril.Machine.RTL.SSA
