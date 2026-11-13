module

public import Silmaril.Machine.CBackend.Lir.Syntax.Defs
public import Silmaril.Foundations.InfiniteTrace
public import Mathlib.Logic.Relation
public import Silmaril.Machine.Execution

/-!
# Small-step semantics of Lir

A state is a program point, the current frame, an explicit stack of suspended
caller activations and the linear memory. `step` is a total function into
`Result`, which distinguishes a running successor, a returned whole program
(values and final memory), a trap (with the memory at the trap) and a stuck
state. Stuck states are undefined behaviour of the source; they are not traps.

Frames map registers and slots to `Option Word`: every register and slot of a
fresh frame is unwritten, and reading an unwritten location is stuck. This lets
a backend relate only the locations Lir has defined, without zeroing target
registers or stack memory on function entry.

The file proves that the semantics is deterministic in the strong sense that a
state has exactly one behaviour (`Behaves.unique`) and, classically, at least
one (`Behaves.exists`). `Transition` gives a constructor-per-case view of the
non-stuck results of `step`, used by the simulation toolkit.
-/

@[expose] public section

namespace Silmaril.Machine.Lir

variable {R : Type}

/-- A program point: the `index`-th instruction of block `label` of `func`, or
its terminator when `index` is the number of instructions. -/
structure Point where
  func : FuncId
  label : Label
  index : Nat
  deriving DecidableEq, Repr

def Point.next (pt : Point) : Point := { pt with index := pt.index + 1 }

@[simp] theorem Point.next_func (pt : Point) : pt.next.func = pt.func := rfl
@[simp] theorem Point.next_label (pt : Point) : pt.next.label = pt.label := rfl
@[simp] theorem Point.next_index (pt : Point) : pt.next.index = pt.index + 1 := rfl

/-- The fetched code at a point. -/
inductive Code (R : Type) where
  | instr (i : Instr R)
  | term (t : Term R)
  deriving DecidableEq, Repr

namespace Prog

def fetch (p : Prog R) (pt : Point) : Option (Code R) :=
  (p.block? pt.func pt.label).bind fun b =>
    match b.instrs[pt.index]? with
    | some i => some (.instr i)
    | none => if pt.index = b.instrs.length then some (.term b.term) else none

theorem fetch_eq_instr {p : Prog R} {pt : Point} {b : Block R} (hb : p.block? pt.func pt.label = some b)
    {i : Instr R} (hi : b.instrs[pt.index]? = some i) : p.fetch pt = some (.instr i) := by
  simp [fetch, hb, hi]

theorem fetch_eq_term {p : Prog R} {pt : Point} {b : Block R} (hb : p.block? pt.func pt.label = some b)
    (hi : pt.index = b.instrs.length) : p.fetch pt = some (.term b.term) := by
  simp [fetch, hb, hi]

theorem fetch_eq_some {p : Prog R} {pt : Point} {c : Code R} (h : p.fetch pt = some c) :
    ∃ b, p.block? pt.func pt.label = some b ∧
      ((∃ i, b.instrs[pt.index]? = some i ∧ c = .instr i) ∨
        (pt.index = b.instrs.length ∧ c = .term b.term)) := by
  unfold fetch at h
  cases hb : p.block? pt.func pt.label with
  | none => simp [hb] at h
  | some b =>
    refine ⟨b, rfl, ?_⟩
    simp only [hb, Option.bind_some] at h
    cases hi : b.instrs[pt.index]? with
    | some i => simp only [hi, Option.some.injEq] at h; exact .inl ⟨i, rfl, h.symm⟩
    | none =>
      simp only [hi] at h
      split at h
      · cases h; exact .inr ⟨by assumption, rfl⟩
      · cases h

end Prog

/-! ## Frames -/

/-- The registers and slots of one activation. `none` means never written. -/
structure Frame (R : Type) where
  regs : R → Option Word
  slots : Nat → Option Word

namespace Frame

def empty : Frame R := ⟨fun _ => none, fun _ => none⟩

def get (fr : Frame R) (r : R) : Option Word := fr.regs r

variable [DecidableEq R]

def set (fr : Frame R) (r : R) (w : Word) : Frame R :=
  { fr with regs := fun r' => if r' = r then some w else fr.regs r' }

def setSlot (fr : Frame R) (n : Nat) (w : Word) : Frame R :=
  { fr with slots := fun n' => if n' = n then some w else fr.slots n' }

def read (fr : Frame R) : Loc R → Option Word
  | .reg r => fr.regs r
  | .slot n => fr.slots n

def write (fr : Frame R) : Loc R → Word → Frame R
  | .reg r, w => fr.set r w
  | .slot n, w => fr.setSlot n w

def readAll (fr : Frame R) (locs : List (Loc R)) : Option (List Word) :=
  locs.mapM fr.read

/-- Write values to locations from left to right; `none` on a length mismatch.
A location listed twice receives the later value. -/
def writeAll (fr : Frame R) : List (Loc R) → List Word → Option (Frame R)
  | [], [] => some fr
  | l :: ls, v :: vs => (fr.write l v).writeAll ls vs
  | _, _ => none

@[simp] theorem get_set (fr : Frame R) (r r' : R) (w : Word) :
    (fr.set r w).get r' = if r' = r then some w else fr.get r' := rfl

@[simp] theorem slots_set (fr : Frame R) (r : R) (w : Word) : (fr.set r w).slots = fr.slots := rfl

omit [DecidableEq R] in
@[simp] theorem regs_setSlot (fr : Frame R) (n : Nat) (w : Word) :
    (fr.setSlot n w).regs = fr.regs := rfl

omit [DecidableEq R] in
@[simp] theorem slots_setSlot (fr : Frame R) (n n' : Nat) (w : Word) :
    (fr.setSlot n w).slots n' = if n' = n then some w else fr.slots n' := rfl

@[simp] theorem regs_set (fr : Frame R) (r r' : R) (w : Word) :
    (fr.set r w).regs r' = if r' = r then some w else fr.regs r' := rfl

end Frame

/-! ## Operations -/

variable [DecidableEq R]

/-- Execute a straight-line operation. `none` is undefined behaviour. -/
def Op.exec : Op R → Frame R → Memory → Option (Frame R × Memory)
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
  | .slotGet d n, fr, m => (fr.slots n).map fun x => (fr.set d x, m)
  | .slotSet n s, fr, m => (fr.get s).map fun x => (fr.setSlot n x, m)

/-- Execute a floating-point instruction `fop op d a b`. `none` is undefined
behaviour (an unwritten operand). -/
def FOp.exec (op : FOp) (d a b : R) (fr : Frame R) : Option (Frame R) :=
  (fr.get a).bind fun x => (fr.get b).map fun y => fr.set d (op.eval x y)

/-! ## States and steps -/

/-- A suspended caller: the point of its `call` instruction and its frame. -/
structure Activation (R : Type) where
  point : Point
  frame : Frame R

structure State (R : Type) where
  point : Point
  frame : Frame R
  stack : List (Activation R)
  mem : Memory

inductive Result (R : Type) where
  | running (s : State R)
  | returned (values : List Word) (mem : Memory)
  | trapped (mem : Memory)
  | stuck

/-- Returned values of a result, for executable checks. -/
def Result.returnedValues? : Result R → Option (List Word)
  | .returned vs _ => some vs
  | _ => none

def Result.isTrapped : Result R → Bool
  | .trapped _ => true
  | _ => false

namespace Prog

/-- The entry point and fresh frame of a call. -/
def enter (p : Prog R) (f : FuncId) (vals : List Word) : Option (Point × Frame R) :=
  (p.func? f).bind fun fn =>
    (Frame.empty.writeAll fn.params vals).map fun fr => (⟨f, fn.entry, 0⟩, fr)

/-- The initial state of a whole-program run of `f` on `args`. -/
def start (p : Prog R) (f : FuncId) (args : List Word) (mem : Memory) : Option (State R) :=
  (p.enter f args).map fun (pt, fr) => ⟨pt, fr, [], mem⟩

end Prog

def step (p : Prog R) (s : State R) : Result R :=
  match p.fetch s.point with
  | none => .stuck
  | some (.instr (.op o)) =>
    match o.exec s.frame s.mem with
    | some (fr, m) => .running { s with point := s.point.next, frame := fr, mem := m }
    | none => .stuck
  | some (.instr (.call f args _)) =>
    match s.frame.readAll args with
    | none => .stuck
    | some vals =>
      match p.enter f vals with
      | none => .stuck
      | some (pt, fr) => .running ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩
  | some (.instr (.fop op d a b)) =>
    match op.exec d a b s.frame with
    | some fr => .running { s with point := s.point.next, frame := fr }
    | none => .stuck
  | some (.term (.jump l)) => .running { s with point := ⟨s.point.func, l, 0⟩ }
  | some (.term (.branch c l₁ l₂)) =>
    match s.frame.get c with
    | none => .stuck
    | some x => .running { s with point := ⟨s.point.func, if x = 0 then l₂ else l₁, 0⟩ }
  | some (.term (.ret locs)) =>
    match s.frame.readAll locs with
    | none => .stuck
    | some vals =>
      match s.stack with
      | [] => .returned vals s.mem
      | a :: rest =>
        match p.fetch a.point with
        | some (.instr (.call _ _ results)) =>
          match a.frame.writeAll results vals with
          | some fr => .running ⟨a.point.next, fr, rest, s.mem⟩
          | none => .stuck
        | _ => .stuck
  | some (.term .trap) => .trapped s.mem

/-- The non-stuck results of `step`, one constructor per case. -/
inductive Transition (p : Prog R) : State R → Result R → Prop
  | op {s : State R} {o : Op R} {fr : Frame R} {m : Memory} :
      p.fetch s.point = some (.instr (.op o)) → o.exec s.frame s.mem = some (fr, m) →
      Transition p s (.running { s with point := s.point.next, frame := fr, mem := m })
  | call {s : State R} {f : FuncId} {args results : List (Loc R)} {vals : List Word}
      {pt : Point} {fr : Frame R} :
      p.fetch s.point = some (.instr (.call f args results)) →
      s.frame.readAll args = some vals → p.enter f vals = some (pt, fr) →
      Transition p s (.running ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩)
  | fop {s : State R} {op : FOp} {d a b : R} {fr : Frame R} :
      p.fetch s.point = some (.instr (.fop op d a b)) → op.exec d a b s.frame = some fr →
      Transition p s (.running { s with point := s.point.next, frame := fr })
  | jump {s : State R} {l : Label} :
      p.fetch s.point = some (.term (.jump l)) →
      Transition p s (.running { s with point := ⟨s.point.func, l, 0⟩ })
  | branch {s : State R} {c : R} {l₁ l₂ : Label} {x : Word} :
      p.fetch s.point = some (.term (.branch c l₁ l₂)) → s.frame.get c = some x →
      Transition p s (.running { s with point := ⟨s.point.func, if x = 0 then l₂ else l₁, 0⟩ })
  | ret {s : State R} {locs : List (Loc R)} {vals : List Word} {a : Activation R}
      {rest : List (Activation R)} {f : FuncId} {args results : List (Loc R)} {fr : Frame R} :
      p.fetch s.point = some (.term (.ret locs)) → s.frame.readAll locs = some vals →
      s.stack = a :: rest → p.fetch a.point = some (.instr (.call f args results)) →
      a.frame.writeAll results vals = some fr →
      Transition p s (.running ⟨a.point.next, fr, rest, s.mem⟩)
  | halt {s : State R} {locs : List (Loc R)} {vals : List Word} :
      p.fetch s.point = some (.term (.ret locs)) → s.frame.readAll locs = some vals →
      s.stack = [] → Transition p s (.returned vals s.mem)
  | trap {s : State R} :
      p.fetch s.point = some (.term .trap) → Transition p s (.trapped s.mem)

theorem Transition.step_eq {p : Prog R} {s : State R} {r : Result R}
    (h : Transition p s r) : step p s = r := by
  cases h with
  | op hf he => simp [step, hf, he]
  | call hf ha he => simp [step, hf, ha, he]
  | fop hf he => simp [step, hf, he]
  | jump hf => simp [step, hf]
  | branch hf hc => simp [step, hf, hc]
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
    rcases c with (o | ⟨f, args, results⟩ | ⟨op, d, a, b⟩) | (l | ⟨c, l₁, l₂⟩ | locs | _)
    · cases he : o.exec s.frame s.mem with
      | none => simp [step, hf, he] at hr
      | some r => obtain ⟨fr, m⟩ := r; exact key (.op hf he)
    · cases ha : s.frame.readAll args with
      | none => simp [step, hf, ha] at hr
      | some vals =>
        cases hn : p.enter f vals with
        | none => simp [step, hf, ha, hn] at hr
        | some r => obtain ⟨pt, fr⟩ := r; exact key (.call hf ha hn)
    · cases he : op.exec d a b s.frame with
      | none => simp [step, hf, he] at hr
      | some fr => exact key (.fop hf he)
    · exact key (.jump hf)
    · cases hc : s.frame.get c with
      | none => simp [step, hf, hc] at hr
      | some x => exact key (.branch hf hc)
    · cases hv : s.frame.readAll locs with
      | none => simp [step, hf, hv] at hr
      | some vals =>
        cases hs : s.stack with
        | nil => exact key (.halt hf hv hs)
        | cons a rest =>
          cases ha : p.fetch a.point with
          | none => simp [step, hf, hv, hs, ha] at hr
          | some c =>
            rcases c with (o | ⟨g, args, results⟩ | _) | t
            · simp [step, hf, hv, hs, ha] at hr
            · cases hw : a.frame.writeAll results vals with
              | none => simp [step, hf, hv, hs, ha, hw] at hr
              | some fr => exact key (.ret hf hv hs ha hw)
            · simp [step, hf, hv, hs, ha] at hr
            · simp [step, hf, hv, hs, ha] at hr
    · exact key (.trap hf)

/-! ## Executions and behaviours -/

/-- One running step. -/
def Step (p : Prog R) (s s' : State R) : Prop := step p s = .running s'

abbrev Steps (p : Prog R) : State R → State R → Prop := Relation.ReflTransGen (Step p)

/-- An infinite sequence of running steps. -/
def Diverges (p : Prog R) (s : State R) : Prop := InfiniteTrace (Step p) s

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
  cases b₁ <;> cases b₂ <;> simp only [Behavior.result?, Option.some.injEq, reduceCtorEq] at h₁ h₂ <;>
    subst h₁ <;> simp_all

omit [DecidableEq R] in
private theorem Behavior.result?_isSome : ∀ b : Behavior, b ≠ .diverges → ∃ r : Result R, b.result? = some r
  | .returned _ _, _ => ⟨_, rfl⟩
  | .trapped _, _ => ⟨_, rfl⟩
  | .stuck, _ => ⟨_, rfl⟩
  | .diverges, h => absurd rfl h

/-- A state has at most one behaviour. -/
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

/-- Every state has a behaviour (classically). -/
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
    apply InfiniteTrace.coinduct (fun t => Steps p s t) ?_ Relation.ReflTransGen.refl
    intro t ht
    have : ∃ x, step p t = .running x := by
      by_contra hno
      exact fin ⟨t, ht, fun x hx => hno ⟨x, hx⟩⟩
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx, ht.tail hx⟩

/-! ## A fuel-bounded runner -/

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

/-! ## Straight-line code

`execOps` runs a list of operations; `steps_execOps` shows that operations laid
out consecutively in a block are executed by consecutive running steps. -/

def execOps : List (Op R) → Frame R → Memory → Option (Frame R × Memory)
  | [], fr, m => some (fr, m)
  | o :: os, fr, m => (o.exec fr m).bind fun r => execOps os r.1 r.2

@[simp] theorem execOps_nil (fr : Frame R) (m : Memory) : execOps [] fr m = some (fr, m) := rfl

theorem execOps_cons (o : Op R) (os : List (Op R)) (fr : Frame R) (m : Memory) :
    execOps (o :: os) fr m = (o.exec fr m).bind fun r => execOps os r.1 r.2 := rfl

theorem execOps_append (xs ys : List (Op R)) (fr : Frame R) (m : Memory) :
    execOps (xs ++ ys) fr m = (execOps xs fr m).bind fun r => execOps ys r.1 r.2 := by
  induction xs generalizing fr m with
  | nil => rfl
  | cons o os ih =>
    simp only [List.cons_append, execOps_cons]
    cases o.exec fr m with
    | none => rfl
    | some r => simp only [Option.bind_some]; exact ih r.1 r.2

/-- One operation at the current point is one running step. -/
theorem step_op_at {p : Prog R} {b : Block R} {s : State R}
    (hb : p.block? s.point.func s.point.label = some b) {o : Op R} {rest : List (Instr R)}
    (hcode : b.instrs.drop s.point.index = .op o :: rest) {fr : Frame R} {m : Memory}
    (hx : o.exec s.frame s.mem = some (fr, m)) :
    Step p s ⟨⟨s.point.func, s.point.label, s.point.index + 1⟩, fr, s.stack, m⟩ := by
  have hi : b.instrs[s.point.index]? = some (.op o) := by
    have := congrArg (fun l => l[0]?) hcode
    simpa [List.getElem?_drop] using this
  have hf := Prog.fetch_eq_instr hb hi
  exact (Transition.op hf hx).step_eq

theorem drop_succ_of_cons {α : Type} {l rest : List α} {i : Nat} {x : α}
    (h : l.drop i = x :: rest) : l.drop (i + 1) = rest := by
  have := congrArg (List.drop 1) h
  simpa [List.drop_drop, Nat.add_comm] using this

theorem steps_execOps {p : Prog R} {b : Block R} :
    ∀ {os : List (Op R)} {s : State R} {rest : List (Instr R)} {fr : Frame R} {m : Memory},
    p.block? s.point.func s.point.label = some b →
    b.instrs.drop s.point.index = os.map .op ++ rest →
    execOps os s.frame s.mem = some (fr, m) →
    Steps p s ⟨⟨s.point.func, s.point.label, s.point.index + os.length⟩, fr, s.stack, m⟩
  | [], s, _, fr, m, _, _, hx => by
    cases hx
    exact .refl
  | o :: os, s, rest, fr, m, hb, hcode, hx => by
    rw [execOps_cons] at hx
    cases h₁ : o.exec s.frame s.mem with
    | none => simp [h₁] at hx
    | some r =>
      obtain ⟨fr₁, m₁⟩ := r
      simp only [h₁, Option.bind_some] at hx
      have st := step_op_at hb (by simpa using hcode) h₁
      have tail := steps_execOps (os := os)
        (s := ⟨⟨s.point.func, s.point.label, s.point.index + 1⟩, fr₁, s.stack, m₁⟩)
        (rest := rest) hb (drop_succ_of_cons (by simpa using hcode)) hx
      have e : s.point.index + 1 + os.length = s.point.index + (o :: os).length := by
        simp; omega
      rw [e] at tail
      exact Relation.ReflTransGen.head st tail

theorem transGen_execOps {p : Prog R} {b : Block R} {o : Op R} {os : List (Op R)} {s : State R}
    {rest : List (Instr R)} {fr : Frame R} {m : Memory}
    (hb : p.block? s.point.func s.point.label = some b)
    (hcode : b.instrs.drop s.point.index = (o :: os).map .op ++ rest)
    (hx : execOps (o :: os) s.frame s.mem = some (fr, m)) :
    Relation.TransGen (Step p) s
      ⟨⟨s.point.func, s.point.label, s.point.index + (o :: os).length⟩, fr, s.stack, m⟩ := by
  rw [execOps_cons] at hx
  cases h₁ : o.exec s.frame s.mem with
  | none => simp [h₁] at hx
  | some r =>
    obtain ⟨fr₁, m₁⟩ := r
    simp only [h₁, Option.bind_some] at hx
    have st := step_op_at hb (by simpa using hcode) h₁
    have tail := steps_execOps (os := os)
      (s := ⟨⟨s.point.func, s.point.label, s.point.index + 1⟩, fr₁, s.stack, m₁⟩)
      (rest := rest) hb (drop_succ_of_cons (by simpa using hcode)) hx
    have e : s.point.index + 1 + os.length = s.point.index + (o :: os).length := by
      simp; omega
    rw [e] at tail
    exact Relation.TransGen.head' st tail

/-! ## Bridge to `Machine.Execution`

Erasing the final results gives a partial deterministic machine in the sense of
`Machine.Execution`; its reachability is exactly `Steps`. -/

def stepOption (p : Prog R) (s : State R) : Option (State R) :=
  match step p s with
  | .running s' => some s'
  | _ => none

theorem stepOption_eq_some {p : Prog R} {s s' : State R} :
    stepOption p s = some s' ↔ Step p s s' := by
  unfold stepOption Step
  split <;> simp_all

theorem steps_iff_reaches {p : Prog R} {s s' : State R} :
    Steps p s s' ↔ Execution.Reaches (stepOption p) s s' := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _ _
    | tail _ hstep ih => exact ih.trans ⟨1, by simp [stepOption_eq_some.mpr hstep]⟩
  · rintro ⟨n, h⟩
    induction n generalizing s with
    | zero => cases h; exact .refl
    | succ n ih =>
      simp only [Execution.run_succ] at h
      cases hs : stepOption p s with
      | none => simp [hs] at h
      | some mid =>
        simp only [hs, Option.bind_some] at h
        exact .head (stepOption_eq_some.mp hs) (ih h)

end Silmaril.Machine.Lir
