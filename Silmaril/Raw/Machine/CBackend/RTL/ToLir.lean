module

public import Silmaril.Machine.CBackend.RTL.Semantics.Defs
public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
public import Silmaril.Foundations.ForwardSim

/-!
# Lowering RTL to Lir

**One RTL node becomes one Lir block.** An RTL function is an array of
instructions indexed by node, each naming its successors; a Lir function is a
list of blocks indexed by label, each a list of straight-line operations ending
in a terminator. Taking the node index as the label and the instruction as a
one-block program makes the translation a table:

| RTL instruction | Lir block |
| --- | --- |
| `nop succ` | `⟨[], .jump succ⟩` |
| `const`, `move`, `unary`, `binary`, `load`, `store` | `⟨[.op …], .jump succ⟩` |
| `call callee args results succ` | `⟨[.call callee (args.map .reg) (results.map .reg)], .jump succ⟩` |
| `cond c t f` | `⟨[], .branch c t f⟩` |
| `jump t` | `⟨[], .jump t⟩` |
| `ret vs` | `⟨[], .ret (vs.map .reg)⟩` |
| `trap` | `⟨[], .trap⟩` |

Nothing is translated inside an instruction: RTL reuses `Lir.Unop`, `Lir.Binop`,
`Lir.Width`, `Lir.Ext`, `Lir.Cond`, `Lir.Memory` and `Lir.Word` verbatim, so the
operator arguments are copied. The only change of type is `R ↦ Lir.Loc R`, the
embedding `Loc.reg` of a pseudo-register as a Lir location, at the four call
boundaries (parameters, arguments, results, returned values).

## The matching relation and the shape of the simulation

The relation is a *function*: an RTL state `s` is matched by exactly one Lir
state `toState s`, with point `⟨s.point.func, s.point.node, 0⟩`, the same
register map (the slot map is everywhere unwritten, because RTL has no slots),
the same stack and the same memory.

Each RTL step becomes one or two Lir steps and never zero, so the simulation is
**lock-step**: `Silmaril.LockstepSim`, built by `LockstepSim.ofFun` from
`toState_step`, which is the whole content of this file. The two-step cases are
the ones whose block has an instruction before its terminator: an operation is
one `Lir.Transition.op` followed by the block's `jump`, and a return into a
caller is one `Lir.Transition.ret` — which lands on the *terminator* of the
caller's one-instruction block — followed by that `jump`. `nop`, `cond`, `jump`,
`call`, the program `ret` and `trap` are single steps.

## Which of the two offered constructions this is

The simulation kit of `Silmaril/Machine/Lir/Simulation.lean` goes *from* a Lir
program to a target, so its `CaseSimulation` cannot be instantiated here: the
source is RTL. Of the two mirror images, this file takes the direct one —
case analysis on `RTL.Transition`, which `RTL.Transition.of_step` supplies, so
`RTL.step` is never unfolded either — and feeds the resulting one-step lemma to
the *generic* kit `Silmaril/Foundations/ForwardSim.lean`, which is where
`steps` and `diverges` come from. A bespoke RTL-side
`CaseSimulation`-shaped bundle would add thirteen fields of boilerplate with a
single instantiation and no extra reuse: `LockstepSim` already carries the
abstraction, because the matching relation here is a function and the measure
is constant. The Lir side is never unfolded: every Lir step is produced by a
`Lir.Transition` constructor and `Lir.Transition.step_eq`.

## What is proved

`toLir_start` lowers an initial state, `toLir_behaves` lowers every non-stuck
behaviour, and `toLir_behaves_iff` is the converse, which is what a statement
quantifying over *target* behaviours needs. The converse is not obtained from
`Behaviour.Refines.of_forward`, because that theorem is about
`Machine.Behaviour.Semantics` and Lir is not packaged as one; with both
languages deterministic and total (`RTL.Behaves.unique`/`exists`,
`Lir.Behaves.unique`/`exists`) the argument is two lines anyway.

Stuck RTL states are not covered, and deliberately so: a stuck state is source
undefined behaviour, and `safe_iff_not_stuck` (`RTL/Behaviour.lean`) is the
side condition that excludes it.

`toLirBehavior` transports an `RTL.Behavior` to a `Lir.Behavior`: the two are
distinct inductives with identical constructors, so they do not unify. See its
docstring for the pointer to that kit.
-/

@[expose] public section

namespace Silmaril.Machine.RTL

open Silmaril.Machine.Lir (Word Memory)
open Relation

variable {R : Type}

/-! ## The translation -/

/-- The Lir block of one RTL instruction: its operation, if it has one, followed
by a terminator naming its successors. -/
def toLirInstr : Instr R → Lir.Block R
  | .nop s => ⟨[], .jump s⟩
  | .const d v s => ⟨[.op (.const d v)], .jump s⟩
  | .move d src s => ⟨[.op (.move d src)], .jump s⟩
  | .unary op d src s => ⟨[.op (.unary op d src)], .jump s⟩
  | .binary op d a b s => ⟨[.op (.binary op d a b)], .jump s⟩
  | .load w e d base off s => ⟨[.op (.load w e d base off)], .jump s⟩
  | .store w base off src s => ⟨[.op (.store w base off src)], .jump s⟩
  | .call callee args results s =>
      ⟨[.call callee (args.map .reg) (results.map .reg)], .jump s⟩
  | .cond c t f => ⟨[], .branch c t f⟩
  | .jump t => ⟨[], .jump t⟩
  | .ret vs => ⟨[], .ret (vs.map .reg)⟩
  | .trap => ⟨[], .trap⟩

/-- The Lir function of an RTL function: the parameters as locations, the entry
node as the entry label, and one block per node. -/
def toLirFunc (fn : Func R) : Lir.Func R where
  params := fn.params.map .reg
  entry := fn.entry
  blocks := fn.code.map toLirInstr

/-- The Lir program of an RTL program. -/
def toLir (p : Prog R) : Lir.Prog R := ⟨p.funcs.map toLirFunc⟩

/-! ## The matching relation -/

/-- The Lir point of an RTL point: the first position of the node's block. -/
def toPoint (pt : Point) : Lir.Point := ⟨pt.func, pt.node, 0⟩

/-- The Lir frame of an RTL frame: the same registers, no slots. -/
def toFrame (fr : Frame R) : Lir.Frame R := ⟨fr.regs, fun _ => none⟩

/-- The Lir activation of a suspended RTL caller. -/
def toActivation (a : Activation R) : Lir.Activation R := ⟨toPoint a.point, toFrame a.frame⟩

/-- The Lir state matching an RTL state. -/
def toState (s : State R) : Lir.State R :=
  ⟨toPoint s.point, toFrame s.frame, s.stack.map toActivation, s.mem⟩

/-- The Lir behaviour matching an RTL behaviour. The two `Behavior` types have
the same constructors but are distinct inductives, one per language, so they do
not unify and a transport function is needed. `RTL.Behavior` is the eleventh
such inductive in the repository; the duplication is
known, and the right home for all of them is a
generic simulation kit. Nothing is refactored here. -/
def toLirBehavior : Behavior → Lir.Behavior
  | .returned vs m => .returned vs m
  | .trapped m => .trapped m
  | .stuck => .stuck
  | .diverges => .diverges

theorem toLirBehavior_injective : Function.Injective toLirBehavior := by
  intro a b h
  cases a <;> cases b <;> simp_all [toLirBehavior]

/-! ## Lookup -/

theorem toLir_func? (p : Prog R) (f : FuncId) :
    (toLir p).func? f = (p.func? f).map toLirFunc := by
  simp [toLir, Lir.Prog.func?, Prog.func?, List.getElem?_map]

/-- The block of a node is the translation of the instruction there. -/
theorem toLir_block? (p : Prog R) (f : FuncId) (n : Node) :
    (toLir p).block? f n = (p.instr? f n).map toLirInstr := by
  simp only [Lir.Prog.block?, toLir_func?, Prog.instr?]
  cases p.func? f with
  | none => rfl
  | some fn => simp [toLirFunc, Func.instr?, List.getElem?_map]

/-- The block at every Lir position of a node is the translation of the
instruction there. -/
theorem toLir_block?_point {p : Prog R} {pt : Point} {i : Instr R} (h : p.fetch pt = some i)
    (j : Nat) :
    (toLir p).block? (⟨pt.func, pt.node, j⟩ : Lir.Point).func
      (⟨pt.func, pt.node, j⟩ : Lir.Point).label = some (toLirInstr i) := by
  rw [toLir_block?]
  exact congrArg (Option.map toLirInstr) h

/-- The Lir fetch at the operation position of a one-operation block. -/
theorem toLir_fetch_op {p : Prog R} {pt : Point} {i : Instr R} {o : Lir.Instr R}
    (h : p.fetch pt = some i) (hi : (toLirInstr i).instrs = [o]) :
    (toLir p).fetch ⟨pt.func, pt.node, 0⟩ = some (.instr o) :=
  Lir.Prog.fetch_eq_instr (b := toLirInstr i) (toLir_block?_point h 0) (by rw [hi]; rfl)

/-- The Lir fetch at the terminator of a block with no operation. -/
theorem toLir_fetch_term {p : Prog R} {pt : Point} {i : Instr R}
    (h : p.fetch pt = some i) (hi : (toLirInstr i).instrs = []) :
    (toLir p).fetch ⟨pt.func, pt.node, 0⟩ = some (.term (toLirInstr i).term) :=
  Lir.Prog.fetch_eq_term (toLir_block?_point h 0) (by rw [hi]; rfl)

/-- The Lir fetch at the terminator of a one-operation block, the position a
`Lir.Point.next` lands on. -/
theorem toLir_fetch_term_next {p : Prog R} {pt : Point} {i : Instr R} {o : Lir.Instr R}
    (h : p.fetch pt = some i) (hi : (toLirInstr i).instrs = [o]) :
    (toLir p).fetch ⟨pt.func, pt.node, 1⟩ = some (.term (toLirInstr i).term) :=
  Lir.Prog.fetch_eq_term (toLir_block?_point h 1) (by rw [hi]; rfl)

/-! ## Frames -/

@[simp] theorem toFrame_regs (fr : Frame R) : (toFrame fr).regs = fr.regs := rfl

@[simp] theorem toFrame_read_reg (fr : Frame R) (r : R) :
    (toFrame fr).read (.reg r) = fr.get r := rfl

@[simp] theorem toFrame_get (fr : Frame R) (r : R) : (toFrame fr).get r = fr.get r := rfl

@[simp] theorem toFrame_slots (fr : Frame R) (n : Nat) : (toFrame fr).slots n = none := rfl

@[simp] theorem toFrame_empty : toFrame (Frame.empty : Frame R) = Lir.Frame.empty := rfl

/-- Reading a list of registers agrees with reading their locations. -/
theorem toFrame_readAll (fr : Frame R) (rs : List R) :
    (toFrame fr).readAll (rs.map .reg) = fr.readAll rs := by
  show (rs.map Lir.Loc.reg).mapM (toFrame fr).read = rs.mapM fr.get
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, List.mapM_cons, ih, toFrame_read_reg]

variable [DecidableEq R]

@[simp] theorem toFrame_set (fr : Frame R) (r : R) (w : Word) :
    toFrame (fr.set r w) = (toFrame fr).set r w := rfl

/-- Writing a list of registers agrees with writing their locations. -/
theorem toFrame_writeAll : ∀ (fr : Frame R) (rs : List R) (vals : List Word),
    (toFrame fr).writeAll (rs.map .reg) vals = (fr.writeAll rs vals).map toFrame
  | _, [], [] => rfl
  | _, [], _ :: _ => rfl
  | _, _ :: _, [] => rfl
  | fr, r :: rs, v :: vs => by
    show ((toFrame fr).write (.reg r) v).writeAll (rs.map .reg) vs =
      ((fr.set r v).writeAll rs vs).map toFrame
    rw [show (toFrame fr).write (.reg r) v = toFrame (fr.set r v) from rfl]
    exact toFrame_writeAll (fr.set r v) rs vs

/-- Entering a function agrees. -/
theorem toLir_enter (p : Prog R) (f : FuncId) (vals : List Word) :
    (toLir p).enter f vals = (p.enter f vals).map (fun r => (toPoint r.1, toFrame r.2)) := by
  simp only [Lir.Prog.enter, Prog.enter, toLir_func?]
  cases p.func? f with
  | none => rfl
  | some fn =>
    simp only [Option.map_some, Option.bind_some, toLirFunc]
    rw [show (Lir.Frame.empty : Lir.Frame R) = toFrame Frame.empty from rfl, toFrame_writeAll]
    cases Frame.empty.writeAll fn.params vals <;> rfl

/-! ## The simulation -/

/-- The Lir state reached after the operation of a one-operation block: the
block's terminator position, with the new frame and memory. -/
private def midState (s : State R) (fr : Frame R) (m : Memory) : Lir.State R :=
  ⟨⟨s.point.func, s.point.node, 1⟩, toFrame fr, s.stack.map toActivation, m⟩

/-- **A block with one operation is two Lir steps**: the operation, which lands
on the block's terminator, and then the terminator's `jump`. -/
private theorem step_op_jump {p : Prog R} {s : State R} {i : Instr R} {o : Lir.Op R} {n : Node}
    (hf : p.fetch s.point = some i) (hi : toLirInstr i = ⟨[.op o], .jump n⟩)
    {fr : Frame R} {m : Memory} (hx : o.exec (toFrame s.frame) s.mem = some (toFrame fr, m)) :
    TransGen (Lir.Step (toLir p)) (toState s)
      (toState { s with point := s.point.at n, frame := fr, mem := m }) := by
  have hins : (toLirInstr i).instrs = [Lir.Instr.op o] := by rw [hi]
  have h1 : Lir.Step (toLir p) (toState s) (midState s fr m) :=
    (Lir.Transition.op (p := toLir p) (s := toState s) (toLir_fetch_op hf hins) hx).step_eq
  have hterm : (toLir p).fetch ⟨s.point.func, s.point.node, 1⟩ = some (.term (.jump n)) := by
    have := toLir_fetch_term_next hf hins
    rwa [hi] at this
  have h2 : Lir.Step (toLir p) (midState s fr m)
      (toState { s with point := s.point.at n, frame := fr, mem := m }) :=
    (Lir.Transition.jump (p := toLir p) (s := midState s fr m) (l := n) hterm).step_eq
  exact TransGen.head h1 (TransGen.single h2)

omit [DecidableEq R] in
/-- A block with no operation: the terminator is at the node's first position. -/
private theorem fetch_term_zero {p : Prog R} {s : State R} {i : Instr R}
    (hf : p.fetch s.point = some i) (hi : (toLirInstr i).instrs = []) :
    (toLir p).fetch (toState s).point = some (.term (toLirInstr i).term) :=
  toLir_fetch_term hf hi

/-- **One RTL step is one or two Lir steps.** This is the whole content of the
lowering: `Lir.Transition` supplies every target step and `RTL.Transition`
every source case, so neither `step` function is unfolded. -/
theorem toState_step {p : Prog R} {s s' : State R} (h : Step p s s') :
    TransGen (Lir.Step (toLir p)) (toState s) (toState s') := by
  have tr := Transition.of_step h (by intro e; cases e)
  generalize hres : Result.running s' = r at tr
  cases tr with
  | @nop n hf =>
    cases hres
    have hterm : (toLir p).fetch (toState s).point = some (.term (.jump n)) :=
      fetch_term_zero hf rfl
    exact TransGen.single (Lir.Transition.jump (p := toLir p) (s := toState s) hterm).step_eq
  | @const d v n hf =>
    cases hres
    exact step_op_jump hf rfl rfl
  | @move d src n x hf hx =>
    cases hres
    exact step_op_jump hf rfl (by simp [Lir.Op.exec, hx])
  | @unary op d src n x hf hx =>
    cases hres
    exact step_op_jump hf rfl (by simp [Lir.Op.exec, hx])
  | @binary op d a b n x y z hf hx hy hz =>
    cases hres
    exact step_op_jump hf rfl (by simp [Lir.Op.exec, hx, hy, hz])
  | @load w e d base off n addr z hf hb hl =>
    cases hres
    exact step_op_jump hf rfl (by simp [Lir.Op.exec, hb, hl])
  | @store w base off src n addr x m hf hb hx hm =>
    cases hres
    exact step_op_jump hf rfl (by simp [Lir.Op.exec, hb, hx, hm])
  | @call f args results n vals pt fr hf ha he =>
    cases hres
    have hfetch : (toLir p).fetch (toState s).point =
        some (.instr (.call f (args.map .reg) (results.map .reg))) :=
      toLir_fetch_op hf rfl
    have hargs : (toState s).frame.readAll (args.map .reg) = some vals := by
      show (toFrame s.frame).readAll (args.map .reg) = some vals
      rw [toFrame_readAll]; exact ha
    have henter : (toLir p).enter f vals = some (toPoint pt, toFrame fr) := by
      rw [toLir_enter, he]; rfl
    exact TransGen.single
      (Lir.Transition.call (p := toLir p) (s := toState s) hfetch hargs henter).step_eq
  | @cond c n₁ n₂ x hf hc =>
    cases hres
    have hterm : (toLir p).fetch (toState s).point = some (.term (.branch c n₁ n₂)) :=
      fetch_term_zero hf rfl
    exact TransGen.single
      (Lir.Transition.branch (p := toLir p) (s := toState s) hterm hc).step_eq
  | @jump t hf =>
    cases hres
    have hterm : (toLir p).fetch (toState s).point = some (.term (.jump t)) :=
      fetch_term_zero hf rfl
    exact TransGen.single (Lir.Transition.jump (p := toLir p) (s := toState s) hterm).step_eq
  | @ret regs vals a rest f args results n fr hf hv hst hc hw =>
    cases hres
    have hterm : (toLir p).fetch (toState s).point = some (.term (.ret (regs.map .reg))) :=
      fetch_term_zero hf rfl
    have hvals : (toState s).frame.readAll (regs.map .reg) = some vals := by
      show (toFrame s.frame).readAll (regs.map .reg) = some vals
      rw [toFrame_readAll]; exact hv
    have hstack : (toState s).stack = toActivation a :: rest.map toActivation := by
      show s.stack.map toActivation = _
      rw [hst]; rfl
    have hcall : (toLir p).fetch (toActivation a).point =
        some (.instr (.call f (args.map .reg) (results.map .reg))) :=
      toLir_fetch_op hc rfl
    have hwrite : (toActivation a).frame.writeAll (results.map .reg) vals = some (toFrame fr) := by
      show (toFrame a.frame).writeAll (results.map .reg) vals = _
      rw [toFrame_writeAll, hw]; rfl
    have h1 : Lir.Step (toLir p) (toState s)
        ⟨⟨a.point.func, a.point.node, 1⟩, toFrame fr, rest.map toActivation, s.mem⟩ :=
      (Lir.Transition.ret (p := toLir p) (s := toState s) hterm hvals hstack hcall hwrite).step_eq
    have hterm2 : (toLir p).fetch ⟨a.point.func, a.point.node, 1⟩ = some (.term (.jump n)) :=
      toLir_fetch_term_next hc rfl
    have h2 : Lir.Step (toLir p)
        ⟨⟨a.point.func, a.point.node, 1⟩, toFrame fr, rest.map toActivation, s.mem⟩
        (toState ⟨a.point.at n, fr, rest, s.mem⟩) :=
      (Lir.Transition.jump (p := toLir p)
        (s := ⟨⟨a.point.func, a.point.node, 1⟩, toFrame fr, rest.map toActivation, s.mem⟩)
        (l := n) hterm2).step_eq
    exact TransGen.head h1 (TransGen.single h2)
  | halt => cases hres
  | trap => cases hres

/-- The lowering as a lock-step forward simulation, from which finite runs and
divergence are inherited. -/
theorem simulation (p : Prog R) :
    Silmaril.LockstepSim (Step p) (Lir.Step (toLir p)) (fun s t => t = toState s) :=
  Silmaril.LockstepSim.ofFun toState toState_step

/-! ## Final results -/

/-- A returning RTL state lowers to a returning Lir state, with the same values
and memory. -/
theorem toLir_step_returned {p : Prog R} {s : State R} {vs : List Word} {m : Memory}
    (h : step p s = .returned vs m) : Lir.step (toLir p) (toState s) = .returned vs m := by
  have tr := Transition.of_step h (by intro e; cases e)
  generalize hres : Result.returned vs m = r at tr
  cases tr with
  | @halt regs vals hf hv hst =>
    cases hres
    have hterm : (toLir p).fetch (toState s).point = some (.term (.ret (regs.map .reg))) :=
      fetch_term_zero hf rfl
    have hvals : (toState s).frame.readAll (regs.map .reg) = some vs := by
      show (toFrame s.frame).readAll (regs.map .reg) = some vs
      rw [toFrame_readAll]; exact hv
    have hstack : (toState s).stack = [] := by show s.stack.map toActivation = _; rw [hst]; rfl
    exact (Lir.Transition.halt (p := toLir p) (s := toState s) hterm hvals hstack).step_eq
  | _ => cases hres

/-- A trapping RTL state lowers to a trapping Lir state, with the same memory. -/
theorem toLir_step_trapped {p : Prog R} {s : State R} {m : Memory}
    (h : step p s = .trapped m) : Lir.step (toLir p) (toState s) = .trapped m := by
  have tr := Transition.of_step h (by intro e; cases e)
  generalize hres : Result.trapped m = r at tr
  cases tr with
  | @trap hf =>
    cases hres
    exact (Lir.Transition.trap (p := toLir p) (s := toState s) (fetch_term_zero hf rfl)).step_eq
  | _ => cases hres

/-! ## Whole-program behaviour -/

/-- **The lowered program has every non-stuck behaviour of the source.** -/
theorem toLir_behaves {p : Prog R} {s : State R} {b : Behavior} (hb : Behaves p s b)
    (hns : b ≠ .stuck) : Lir.Behaves (toLir p) (toState s) (toLirBehavior b) := by
  cases b with
  | returned vs m =>
    obtain ⟨t, ht, hf⟩ := hb
    obtain ⟨u, hu, rfl⟩ := (simulation p).steps ht rfl
    exact ⟨toState t, hu, toLir_step_returned hf⟩
  | trapped m =>
    obtain ⟨t, ht, hf⟩ := hb
    obtain ⟨u, hu, rfl⟩ := (simulation p).steps ht rfl
    exact ⟨toState t, hu, toLir_step_trapped hf⟩
  | stuck => exact absurd rfl hns
  | diverges => exact (simulation p).diverges hb rfl

/-- The start state of a whole-program run lowers to the start state of the
lowered program. -/
theorem toLir_start {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory} {s : State R}
    (h : p.start f args mem = some s) : (toLir p).start f args mem = some (toState s) := by
  unfold Lir.Prog.start
  rw [toLir_enter]
  unfold Prog.start at h
  cases he : p.enter f args with
  | none => rw [he] at h; cases h
  | some r =>
    rw [he] at h
    cases h
    rfl

/-- **Semantic preservation of the lowering**, as a statement about whole
program runs: every non-stuck behaviour of a run of `f` is a behaviour of the
lowered program started with the same function, arguments and memory. -/
theorem toLir_start_behaves {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory}
    {s : State R} (h : p.start f args mem = some s) {b : Behavior} (hb : Behaves p s b)
    (hns : b ≠ .stuck) :
    ∃ t, (toLir p).start f args mem = some t ∧ Lir.Behaves (toLir p) t (toLirBehavior b) :=
  ⟨toState s, toLir_start h, toLir_behaves hb hns⟩

/-- **The converse**, from determinism of both languages: at a safe RTL state
the behaviours of the lowered state are exactly the lowered behaviours. This is
the direction a statement quantifying over *target* behaviours needs. -/
theorem toLir_behaves_iff {p : Prog R} {s : State R} (hsafe : ¬ Behaves p s .stuck)
    {b : Behavior} : Lir.Behaves (toLir p) (toState s) (toLirBehavior b) ↔ Behaves p s b := by
  refine ⟨fun h => ?_, fun h => toLir_behaves h (by rintro rfl; exact hsafe h)⟩
  obtain ⟨b', hb'⟩ := Behaves.exists p s
  have hns : b' ≠ .stuck := by rintro rfl; exact hsafe hb'
  obtain rfl : b = b' := toLirBehavior_injective (Lir.Behaves.unique h (toLir_behaves hb' hns))
  exact hb'

end Silmaril.Machine.RTL
