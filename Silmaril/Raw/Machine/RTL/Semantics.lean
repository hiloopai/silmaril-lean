module

public import Silmaril.Raw.Machine.RTL.Syntax
public import Silmaril.Foundations.InfiniteTrace.Deterministic
public import Mathlib.Logic.Relation

/-!
# Small-step semantics of RTL

The design is `Lir`'s, so that a lowering from RTL to Lir is a simulation
between two machines of the same shape. A state is a program point (a function
identifier and a node), the current frame, an explicit stack of suspended caller
activations and the linear memory. `step` is a **total** function into `Result`,
which distinguishes a running successor, a returned whole program (values and
final memory), a trap (with the memory at the trap) and a stuck state.

Frames map pseudo-registers to `Option Word`: every register of a fresh frame is
unwritten, and reading an unwritten register is stuck. RTL has no stack slots,
so a frame is only a register map.

Undefined behaviour follows `Lir` exactly. Division by zero and signed division
overflow, memory accesses outside the linear memory, reads of unwritten
registers, nodes outside the code array, calls to missing functions and argument
or result count mismatches are **stuck**, not traps. The only trap is the `trap`
instruction.

`Transition` gives a constructor-per-instruction view of the non-stuck results
of `step`. `Behaves.unique` and `Behaves.exists` show that every state has
exactly one behaviour among returned, trapped, stuck and diverging. `run` is a
fuel-bounded runner for executable checks.
-/

@[expose] public section

namespace Silmaril.Machine.RTL

open Silmaril.Machine.Lir (Word Memory)

variable {R : Type}

/-- A program point: a node of a function. -/
structure Point where
  func : FuncId
  node : Node
  deriving DecidableEq, Repr

/-- The point at node `n` of the same function. -/
def Point.at (pt : Point) (n : Node) : Point := { pt with node := n }

@[simp] theorem Point.at_func (pt : Point) (n : Node) : (pt.at n).func = pt.func := rfl
@[simp] theorem Point.at_node (pt : Point) (n : Node) : (pt.at n).node = n := rfl

/-! ## Frames -/

/-- The pseudo-registers of one activation. `none` means never written. -/
structure Frame (R : Type) where
  regs : R → Option Word

namespace Frame

/-- The frame of a fresh activation: every register unwritten. -/
def empty : Frame R := ⟨fun _ => none⟩

/-- The value of a register, `none` when it was never written. -/
def get (fr : Frame R) (r : R) : Option Word := fr.regs r

variable [DecidableEq R]

/-- The frame with `r` set to `w`. -/
def set (fr : Frame R) (r : R) (w : Word) : Frame R :=
  ⟨fun r' => if r' = r then some w else fr.regs r'⟩

/-- Read a list of registers; `none` if any is unwritten. -/
def readAll (fr : Frame R) (rs : List R) : Option (List Word) := rs.mapM fr.get

/-- Write values to registers from left to right; `none` on a length mismatch.
A register listed twice receives the later value. -/
def writeAll (fr : Frame R) : List R → List Word → Option (Frame R)
  | [], [] => some fr
  | r :: rs, v :: vs => (fr.set r v).writeAll rs vs
  | _, _ => none

@[simp] theorem get_set (fr : Frame R) (r r' : R) (w : Word) :
    (fr.set r w).get r' = if r' = r then some w else fr.get r' := rfl

@[simp] theorem regs_set (fr : Frame R) (r r' : R) (w : Word) :
    (fr.set r w).regs r' = if r' = r then some w else fr.regs r' := rfl

end Frame

/-! ## States and steps -/

variable [DecidableEq R]

/-- A suspended caller: the point of its `call` instruction and its frame. -/
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

namespace Prog

/-- The entry point and fresh frame of a call; `none` on a missing function or
an argument count mismatch. -/
def enter (p : Prog R) (f : FuncId) (vals : List Word) : Option (Point × Frame R) :=
  (p.func? f).bind fun fn =>
    (Frame.empty.writeAll fn.params vals).map fun fr => (⟨f, fn.entry⟩, fr)

/-- The initial state of a whole-program run of `f` on `args`. -/
def start (p : Prog R) (f : FuncId) (args : List Word) (mem : Memory) : Option (State R) :=
  (p.enter f args).map fun (pt, fr) => ⟨pt, fr, [], mem⟩

/-- The instruction at a state's point. -/
def fetch (p : Prog R) (pt : Point) : Option (Instr R) := p.instr? pt.func pt.node

end Prog

/-- One step of the machine, as a total function. -/
def step (p : Prog R) (s : State R) : Result R :=
  match p.fetch s.point with
  | none => .stuck
  | some (.nop n) => .running { s with point := s.point.at n }
  | some (.const d v n) => .running { s with point := s.point.at n, frame := s.frame.set d v }
  | some (.move d src n) =>
    match s.frame.get src with
    | none => .stuck
    | some x => .running { s with point := s.point.at n, frame := s.frame.set d x }
  | some (.unary op d src n) =>
    match s.frame.get src with
    | none => .stuck
    | some x => .running { s with point := s.point.at n, frame := s.frame.set d (op.eval x) }
  | some (.binary op d a b n) =>
    match s.frame.get a, s.frame.get b with
    | some x, some y =>
      match op.eval x y with
      | some z => .running { s with point := s.point.at n, frame := s.frame.set d z }
      | none => .stuck
    | _, _ => .stuck
  | some (.load w e d base off n) =>
    match s.frame.get base with
    | none => .stuck
    | some addr =>
      match s.mem.load w e (addr.toNat + off) with
      | some z => .running { s with point := s.point.at n, frame := s.frame.set d z }
      | none => .stuck
  | some (.store w base off src n) =>
    match s.frame.get base, s.frame.get src with
    | some addr, some x =>
      match s.mem.store w (addr.toNat + off) x with
      | some m => .running { s with point := s.point.at n, mem := m }
      | none => .stuck
    | _, _ => .stuck
  | some (.call f args _ _) =>
    match s.frame.readAll args with
    | none => .stuck
    | some vals =>
      match p.enter f vals with
      | none => .stuck
      | some (pt, fr) => .running ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩
  | some (.cond c n₁ n₂) =>
    match s.frame.get c with
    | none => .stuck
    | some x => .running { s with point := s.point.at (if x = 0 then n₂ else n₁) }
  | some (.jump t) => .running { s with point := s.point.at t }
  | some (.ret regs) =>
    match s.frame.readAll regs with
    | none => .stuck
    | some vals =>
      match s.stack with
      | [] => .returned vals s.mem
      | a :: rest =>
        match p.fetch a.point with
        | some (.call _ _ results n) =>
          match a.frame.writeAll results vals with
          | some fr => .running ⟨a.point.at n, fr, rest, s.mem⟩
          | none => .stuck
        | _ => .stuck
  | some .trap => .trapped s.mem

/-- The non-stuck results of `step`, one constructor per instruction kind. -/
inductive Transition (p : Prog R) : State R → Result R → Prop
  | nop {s : State R} {n : Node} :
      p.fetch s.point = some (.nop n) →
      Transition p s (.running { s with point := s.point.at n })
  | const {s : State R} {d : R} {v : Word} {n : Node} :
      p.fetch s.point = some (.const d v n) →
      Transition p s (.running { s with point := s.point.at n, frame := s.frame.set d v })
  | move {s : State R} {d src : R} {n : Node} {x : Word} :
      p.fetch s.point = some (.move d src n) → s.frame.get src = some x →
      Transition p s (.running { s with point := s.point.at n, frame := s.frame.set d x })
  | unary {s : State R} {op : Lir.Unop} {d src : R} {n : Node} {x : Word} :
      p.fetch s.point = some (.unary op d src n) → s.frame.get src = some x →
      Transition p s
        (.running { s with point := s.point.at n, frame := s.frame.set d (op.eval x) })
  | binary {s : State R} {op : Lir.Binop} {d a b : R} {n : Node} {x y z : Word} :
      p.fetch s.point = some (.binary op d a b n) → s.frame.get a = some x →
      s.frame.get b = some y → op.eval x y = some z →
      Transition p s (.running { s with point := s.point.at n, frame := s.frame.set d z })
  | load {s : State R} {w : Lir.Width} {e : Lir.Ext} {d base : R} {off : Nat} {n : Node}
      {addr z : Word} :
      p.fetch s.point = some (.load w e d base off n) → s.frame.get base = some addr →
      s.mem.load w e (addr.toNat + off) = some z →
      Transition p s (.running { s with point := s.point.at n, frame := s.frame.set d z })
  | store {s : State R} {w : Lir.Width} {base : R} {off : Nat} {src : R} {n : Node}
      {addr x : Word} {m : Memory} :
      p.fetch s.point = some (.store w base off src n) → s.frame.get base = some addr →
      s.frame.get src = some x → s.mem.store w (addr.toNat + off) x = some m →
      Transition p s (.running { s with point := s.point.at n, mem := m })
  | call {s : State R} {f : FuncId} {args results : List R} {n : Node} {vals : List Word}
      {pt : Point} {fr : Frame R} :
      p.fetch s.point = some (.call f args results n) → s.frame.readAll args = some vals →
      p.enter f vals = some (pt, fr) →
      Transition p s (.running ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩)
  | cond {s : State R} {c : R} {n₁ n₂ : Node} {x : Word} :
      p.fetch s.point = some (.cond c n₁ n₂) → s.frame.get c = some x →
      Transition p s (.running { s with point := s.point.at (if x = 0 then n₂ else n₁) })
  | jump {s : State R} {t : Node} :
      p.fetch s.point = some (.jump t) →
      Transition p s (.running { s with point := s.point.at t })
  | ret {s : State R} {regs : List R} {vals : List Word} {a : Activation R}
      {rest : List (Activation R)} {f : FuncId} {args results : List R} {n : Node} {fr : Frame R} :
      p.fetch s.point = some (.ret regs) → s.frame.readAll regs = some vals →
      s.stack = a :: rest → p.fetch a.point = some (.call f args results n) →
      a.frame.writeAll results vals = some fr →
      Transition p s (.running ⟨a.point.at n, fr, rest, s.mem⟩)
  | halt {s : State R} {regs : List R} {vals : List Word} :
      p.fetch s.point = some (.ret regs) → s.frame.readAll regs = some vals →
      s.stack = [] → Transition p s (.returned vals s.mem)
  | trap {s : State R} :
      p.fetch s.point = some .trap → Transition p s (.trapped s.mem)

theorem Transition.step_eq {p : Prog R} {s : State R} {r : Result R}
    (h : Transition p s r) : step p s = r := by
  cases h with
  | nop hf => simp [step, hf]
  | const hf => simp [step, hf]
  | move hf hx => simp [step, hf, hx]
  | unary hf hx => simp [step, hf, hx]
  | binary hf hx hy hz => simp [step, hf, hx, hy, hz]
  | load hf hb hl => simp [step, hf, hb, hl]
  | store hf hb hx hm => simp [step, hf, hb, hx, hm]
  | call hf ha he => simp [step, hf, ha, he]
  | cond hf hc => simp [step, hf, hc]
  | jump hf => simp [step, hf]
  | ret hf hv hs ha hw => simp [step, hf, hv, hs, ha, hw]
  | halt hf hv hs => simp [step, hf, hv, hs]
  | trap hf => simp [step, hf]

theorem Transition.of_step {p : Prog R} {s : State R} {r : Result R}
    (h : step p s = r) (hr : r ≠ .stuck) : Transition p s r := by
  subst h
  have key : ∀ {r}, Transition p s r → Transition p s (step p s) := fun t => t.step_eq ▸ t
  cases hf : p.fetch s.point with
  | none => simp [step, hf] at hr
  | some i =>
    cases i with
    | nop n => exact key (.nop hf)
    | const d v n => exact key (.const hf)
    | move d src n =>
      cases hx : s.frame.get src with
      | none => simp [step, hf, hx] at hr
      | some x => exact key (.move hf hx)
    | unary op d src n =>
      cases hx : s.frame.get src with
      | none => simp [step, hf, hx] at hr
      | some x => exact key (.unary hf hx)
    | binary op d a b n =>
      cases hx : s.frame.get a with
      | none => simp [step, hf, hx] at hr
      | some x =>
        cases hy : s.frame.get b with
        | none => simp [step, hf, hx, hy] at hr
        | some y =>
          cases hz : op.eval x y with
          | none => simp [step, hf, hx, hy, hz] at hr
          | some z => exact key (.binary hf hx hy hz)
    | load w e d base off n =>
      cases hb : s.frame.get base with
      | none => simp [step, hf, hb] at hr
      | some addr =>
        cases hl : s.mem.load w e (addr.toNat + off) with
        | none => simp [step, hf, hb, hl] at hr
        | some z => exact key (.load hf hb hl)
    | store w base off src n =>
      cases hb : s.frame.get base with
      | none => simp [step, hf, hb] at hr
      | some addr =>
        cases hx : s.frame.get src with
        | none => simp [step, hf, hb, hx] at hr
        | some x =>
          cases hm : s.mem.store w (addr.toNat + off) x with
          | none => simp [step, hf, hb, hx, hm] at hr
          | some m => exact key (.store hf hb hx hm)
    | call f args results n =>
      cases ha : s.frame.readAll args with
      | none => simp [step, hf, ha] at hr
      | some vals =>
        cases hn : p.enter f vals with
        | none => simp [step, hf, ha, hn] at hr
        | some q => obtain ⟨pt, fr⟩ := q; exact key (.call hf ha hn)
    | cond c n₁ n₂ =>
      cases hc : s.frame.get c with
      | none => simp [step, hf, hc] at hr
      | some x => exact key (.cond hf hc)
    | jump t => exact key (.jump hf)
    | ret regs =>
      cases hv : s.frame.readAll regs with
      | none => simp [step, hf, hv] at hr
      | some vals =>
        cases hs : s.stack with
        | nil => exact key (.halt hf hv hs)
        | cons a rest =>
          cases hc : p.fetch a.point with
          | none => simp [step, hf, hv, hs, hc] at hr
          | some i' =>
            cases i' with
            | call g args' results' n' =>
              cases hw : a.frame.writeAll results' vals with
              | none => simp [step, hf, hv, hs, hc, hw] at hr
              | some fr => exact key (.ret hf hv hs hc hw)
            | _ => simp [step, hf, hv, hs, hc] at hr
    | trap => exact key (.trap hf)

/-! ## Executions and behaviours -/

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
theorem Steps.total {p : Prog R} {s a b : State R} (ha : Steps p s a) (hb : Steps p s b) :
    Steps p a b ∨ Steps p b a :=
  Relation.ReflTransGen.total_of_right_unique (step_rightUnique p) ha hb

/-- A state whose step is not running has no successor. -/
theorem Steps.eq_of_final {p : Prog R} {s t : State R} (h : Steps p s t)
    (final : ∀ s', step p s ≠ .running s') : t = s := by
  cases h.cases_head with
  | inl h => exact h.symm
  | inr h =>
    obtain ⟨c, hc, _⟩ := h
    exact absurd hc (final c)

/-- Divergence is inherited by every reachable state. -/
theorem Diverges.of_steps {p : Prog R} {s t : State R} (d : Diverges p s) (h : Steps p s t) :
    Diverges p t := by
  induction h with
  | refl => exact d
  | tail _ hstep ih =>
    obtain ⟨b, hb, tail⟩ := ih.unfold
    rw [Step.deterministic hstep hb]
    exact tail

theorem Diverges.running {p : Prog R} {s : State R} (d : Diverges p s) :
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

/-! ## A fuel-bounded runner -/

/-- Run at most `n` steps. -/
def run (p : Prog R) : Nat → State R → Result R
  | 0, s => .running s
  | n + 1, s =>
    match step p s with
    | .running s' => run p n s'
    | r => r

theorem run_running {p : Prog R} {n : Nat} {s s' : State R} (h : run p n s = .running s') :
    Steps p s s' := by
  induction n generalizing s with
  | zero => cases h; exact .refl
  | succ n ih =>
    unfold run at h
    split at h
    · exact Relation.ReflTransGen.head (by assumption) (ih h)
    · rename_i hne; exact absurd h (hne s')

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

theorem run_trapped {p : Prog R} {n : Nat} {s : State R} {m : Memory}
    (h : run p n s = .trapped m) : Behaves p s (.trapped m) :=
  run_final h (by intro x hx; cases hx)

/-- Run a whole program from `start`; `stuck` if the start is undefined. -/
def Prog.runMain (p : Prog R) (fuel : Nat) (f : FuncId) (args : List Word) (mem : Memory) :
    Result R :=
  match p.start f args mem with
  | some s => run p fuel s
  | none => .stuck

end Silmaril.Machine.RTL
