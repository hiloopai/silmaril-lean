module

public import Silmaril.Raw.Machine.RTL.SSA
public import Silmaril.Raw.Machine.RTL.Instruction

/-!
# Intra-procedural big-step execution of SSA-form RTL

`RTL.SSA.step` is a small-step machine with an explicit call stack: a `call` op
pushes an activation and the callee's `ret` pops it. A lambda-SSA region has no
call stack, and a lambda-SSA instruction is a single atomic relation. The two
cannot be compared directly, so this file interposes the obvious intermediate:
a **big-step relation for one function**, in which a call is a single step
resolved by a `CallOracle`.

* `Ops.Exec` runs a block's straight-line ops.
* `Func.Exec` runs a function from a block to an exit, which is a `ret` or a
  `trap`. There is no constructor for a nonterminating run, so a function that
  loops forever simply has no derivation, exactly as a lambda-SSA region that
  loops forever has no `Region.Eval` derivation.
* `Func.Diverges` is the greatest fixpoint describing an infinite run, in the
  style of `LambdaSSA.Semantics.Diverges`. A call that itself runs forever is
  described by a separate `DivOracle`, as `Semantics.External.Diverges` does.

`Prog.oracle` is the oracle a whole program induces, and the theorems at the end
relate it back to the small-step machine. That bridge is stated here and proved
once, so that the translation to and from lambda-SSA never has to mention the
call stack.

## Runs of one activation

A big-step derivation describes one activation, and the machine has one global
run, so the bridge has to say *which stretch* of the global run the derivation
describes. That stretch is the window in which the stack the activation started
under has not yet been popped: `StepWithin`, `StepsWithin` and `DivergesWithin`
are the machine's relations restricted to it, and `Prog.Returns` and `Prog.Traps`
are stated with them.

The restriction is not a convenience. Without it the bridge theorems are false,
in both directions and for ordinary programs:

* a run started inside a function may return from it, re-enter the same function
  at the same call site with the same frame, and return a second time with
  different values and a different memory, so "reaches a `ret` with the starting
  stack" does not determine the result;
* a run started inside a function may return from it and then diverge in a
  *caller*, which says nothing about the callee.

Under the empty stack nothing can be popped, so the restriction is vacuous there
(`stepsWithin_nil_iff`, `divergesWithin_nil_iff`) and the whole-program
statements `Func.exec_returned_iff_behaves` and `Func.exec_returned_iff_oracle`
are about `Behaves` and `Prog.oracle` as usual.

## The bridge

`Func.exec_returned_iff_returns`, `Func.exec_trapped_iff_traps` and
`exec_diverges_iff` are proved in both directions, and they are the point of the
file: without them this would be a change of subject rather than a reformulation.
They are the only theorems in the development that mention the call stack.
-/

@[expose] public section

namespace Silmaril.Machine.RTL.SSA

open Silmaril.Machine.Lir (Word Memory)

variable {R : Type} [DecidableEq R]

/-! ## Straight-line code -/

omit [DecidableEq R] in
/-- Running a block's ops, with each call resolved by the oracle in one step.
The `op` constructor never fires on a call, because `Op.exec` is `none` there. -/
inductive Ops.Exec (oracle : CallOracle) :
    List (Op R) → Frame R → Memory → Frame R → Memory → Prop where
  | nil {fr : Frame R} {m : Memory} : Exec oracle [] fr m fr m
  | op {o : Op R} {os : List (Op R)} {fr fr₁ fr₂ : Frame R} {m m₁ m₂ : Memory} :
      o.exec fr m = some (fr₁, m₁) → Exec oracle os fr₁ m₁ fr₂ m₂ →
      Exec oracle (o :: os) fr m fr₂ m₂
  | call {f : FuncId} {args results : List R} {os : List (Op R)}
      {fr fr₁ fr₂ : Frame R} {m m₁ m₂ : Memory} {vals vs : List Word} :
      fr.readAll args = some vals → oracle f vals m vs m₁ →
      fr.writeAll results vs = some fr₁ → Exec oracle os fr₁ m₁ fr₂ m₂ →
      Exec oracle (.call f args results :: os) fr m fr₂ m₂

/-- How a run of one function ends. A run that never ends has no `Func.Exec`
derivation and is described by `Func.Diverges` instead. -/
inductive Exit where
  | returned (values : List Word) (mem : Memory)
  | trapped (mem : Memory)

/-- Big-step execution of one function, from a block and an incoming frame to an
exit. Transfers rebind the target's parameters exactly as `transfer` does. -/
inductive Func.Exec (oracle : CallOracle) (fn : Func R) :
    Label → Frame R → Memory → Exit → Prop where
  | jump {l t : Label} {b bt : Block R} {as : List R} {vals : List Word}
      {fr fr₁ fr₂ : Frame R} {m m₁ : Memory} {out : Exit} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .jump t as →
      fr₁.readAll as = some vals → fn.block? t = some bt →
      fr₁.writeAll bt.params vals = some fr₂ → Exec oracle fn t fr₂ m₁ out →
      Exec oracle fn l fr m out
  | cond {l t₁ t₂ : Label} {c : R} {a₁ a₂ : List R} {b bt : Block R} {x : Word}
      {vals : List Word} {fr fr₁ fr₂ : Frame R} {m m₁ : Memory} {out : Exit} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ →
      b.term = .cond c t₁ a₁ t₂ a₂ → fr₁.get c = some x →
      fr₁.readAll (if x = 0 then a₂ else a₁) = some vals →
      fn.block? (if x = 0 then t₂ else t₁) = some bt →
      fr₁.writeAll bt.params vals = some fr₂ →
      Exec oracle fn (if x = 0 then t₂ else t₁) fr₂ m₁ out → Exec oracle fn l fr m out
  | ret {l : Label} {b : Block R} {regs : List R} {vals : List Word}
      {fr fr₁ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .ret regs →
      fr₁.readAll regs = some vals → Exec oracle fn l fr m (.returned vals m₁)
  | trap {l : Label} {b : Block R} {fr fr₁ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .trap →
      Exec oracle fn l fr m (.trapped m₁)

/-! ## Divergence -/

/-- A point of an unfinished intra-procedural run: a block, its incoming frame
and the memory. -/
structure DivConfig (R : Type) where
  label : Label
  frame : Frame R
  mem : Memory

/-- One unfolding of an infinite run: the ops of the current block finish and a
transfer leads to a configuration that again runs forever, or one of the ops is a
call that itself runs forever. -/
inductive Func.DivStep (oracle : CallOracle) (div : DivOracle) (fn : Func R)
    (continues : DivConfig R → Prop) : DivConfig R → Prop where
  | call {l : Label} {b : Block R} {pre : List (Op R)} {f : FuncId}
      {args results : List R} {post : List (Op R)} {fr fr₁ : Frame R}
      {m m₁ : Memory} {vals : List Word} :
      fn.block? l = some b → b.ops = pre ++ .call f args results :: post →
      Ops.Exec oracle pre fr m fr₁ m₁ → fr₁.readAll args = some vals →
      div f vals m₁ → DivStep oracle div fn continues ⟨l, fr, m⟩
  | jump {l t : Label} {b bt : Block R} {as : List R} {vals : List Word}
      {fr fr₁ fr₂ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .jump t as →
      fr₁.readAll as = some vals → fn.block? t = some bt →
      fr₁.writeAll bt.params vals = some fr₂ → continues ⟨t, fr₂, m₁⟩ →
      DivStep oracle div fn continues ⟨l, fr, m⟩
  | cond {l t₁ t₂ : Label} {c : R} {a₁ a₂ : List R} {b bt : Block R} {x : Word}
      {vals : List Word} {fr fr₁ fr₂ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ →
      b.term = .cond c t₁ a₁ t₂ a₂ → fr₁.get c = some x →
      fr₁.readAll (if x = 0 then a₂ else a₁) = some vals →
      fn.block? (if x = 0 then t₂ else t₁) = some bt →
      fr₁.writeAll bt.params vals = some fr₂ →
      continues ⟨if x = 0 then t₂ else t₁, fr₂, m₁⟩ →
      DivStep oracle div fn continues ⟨l, fr, m⟩

/-- **One unfolding is monotone in the continuation.** This is what makes
`Func.Diverges` a greatest fixpoint rather than merely a definition. -/
theorem Func.DivStep.mono {oracle : CallOracle} {div : DivOracle} {fn : Func R}
    {S T : DivConfig R → Prop} {c : DivConfig R} (h : Func.DivStep oracle div fn S c)
    (hST : ∀ c, S c → T c) : Func.DivStep oracle div fn T c := by
  cases h with
  | call hb hops hpre hargs hdiv => exact .call hb hops hpre hargs hdiv
  | jump hb hops hterm hargs hbt hwrite rest =>
    exact .jump hb hops hterm hargs hbt hwrite (hST _ rest)
  | cond hb hops hterm hget hargs hbt hwrite rest =>
    exact .cond hb hops hterm hget hargs hbt hwrite (hST _ rest)

/-- An infinite intra-procedural run, as a greatest fixpoint witnessed by a
relation closed under unfolding. -/
def Func.Diverges (oracle : CallOracle) (div : DivOracle) (fn : Func R)
    (c : DivConfig R) : Prop :=
  ∃ S : DivConfig R → Prop, S c ∧ ∀ c, S c → Func.DivStep oracle div fn S c

namespace Func.Diverges

variable {oracle : CallOracle} {div : DivOracle} {fn : Func R}

/-- Coinduction: a relation closed under unfolding witnesses divergence. -/
theorem coinduct (S : DivConfig R → Prop)
    (closed : ∀ c, S c → Func.DivStep oracle div fn S c) {c : DivConfig R} (hc : S c) :
    Func.Diverges oracle div fn c := ⟨S, hc, closed⟩

/-- Divergence unfolds one step. -/
theorem unfold {c : DivConfig R} (h : Func.Diverges oracle div fn c) :
    Func.DivStep oracle div fn (Func.Diverges oracle div fn) c := by
  obtain ⟨S, hc, closed⟩ := h
  exact (closed c hc).mono (fun _ hs => ⟨S, hs, closed⟩)

/-- One step of a divergent continuation is divergence. -/
theorem fold {c : DivConfig R}
    (h : Func.DivStep oracle div fn (Func.Diverges oracle div fn) c) :
    Func.Diverges oracle div fn c := by
  refine ⟨fun c' => c' = c ∨ Func.Diverges oracle div fn c', Or.inl rfl, ?_⟩
  intro c' hc'
  rcases hc' with rfl | hd
  · exact h.mono (fun _ hd => Or.inr hd)
  · exact hd.unfold.mono (fun _ hd => Or.inr hd)

/-- Divergence and one unfolding of it are the same thing. -/
theorem iff_divStep {c : DivConfig R} :
    Func.Diverges oracle div fn c ↔ Func.DivStep oracle div fn (Func.Diverges oracle div fn) c :=
  ⟨unfold, fold⟩

end Func.Diverges

/-! ## Fetching inside a known block -/

omit [DecidableEq R] in
/-- A program's blocks are the blocks of its functions. -/
theorem Prog.block?_eq_of_func {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) (l : Label) : p.block? f l = fn.block? l := by
  simp [Prog.block?, hfn]

omit [DecidableEq R] in
/-- The code at an op index of a known block is that op. -/
theorem Prog.fetch_op {p : Prog R} {f : FuncId} {l : Label} {i : Nat} {b : Block R} {o : Op R}
    (hb : p.block? f l = some b) (ho : b.ops[i]? = some o) :
    p.fetch ⟨f, l, i⟩ = some (.op o) := by
  simp [Prog.fetch, hb, ho]

omit [DecidableEq R] in
/-- The code one past the last op of a known block is its terminator. -/
theorem Prog.fetch_term {p : Prog R} {f : FuncId} {l : Label} {b : Block R}
    (hb : p.block? f l = some b) : p.fetch ⟨f, l, b.ops.length⟩ = some (.term b.term) := by
  simp [Prog.fetch, hb]

omit [DecidableEq R] in
/-- There is no code past a block's terminator. -/
theorem Prog.fetch_none {p : Prog R} {f : FuncId} {l : Label} {i : Nat} {b : Block R}
    (hb : p.block? f l = some b) (ho : b.ops[i]? = none) (hi : i ≠ b.ops.length) :
    p.fetch ⟨f, l, i⟩ = none := by
  simp [Prog.fetch, hb, ho, hi]

omit [DecidableEq R] in
/-- Inside a known block, a fetch is one of the block's ops or its terminator. -/
theorem Prog.fetch_cases {p : Prog R} {f : FuncId} {l : Label} {i : Nat} {b : Block R}
    {c : Code R} (hb : p.block? f l = some b) (h : p.fetch ⟨f, l, i⟩ = some c) :
    (∃ o, b.ops[i]? = some o ∧ c = .op o) ∨ (i = b.ops.length ∧ c = .term b.term) := by
  by_cases hopt : ∃ o, b.ops[i]? = some o
  · obtain ⟨o, ho⟩ := hopt
    exact Or.inl ⟨o, ho, (Option.some.inj ((Prog.fetch_op hb ho).symm.trans h)).symm⟩
  · have ho : b.ops[i]? = none := by
      cases hx : b.ops[i]? with
      | none => rfl
      | some o => exact absurd ⟨o, hx⟩ hopt
    by_cases hi : i = b.ops.length
    · subst hi
      exact Or.inr ⟨rfl, (Option.some.inj ((Prog.fetch_term hb).symm.trans h)).symm⟩
    · rw [Prog.fetch_none hb ho hi] at h
      exact absurd h (by simp)

/-- Concatenating two straight-line runs. -/
theorem Ops.Exec.append {oracle : CallOracle} {os₁ os₂ : List (Op R)} {fr fr₁ fr₂ : Frame R}
    {m m₁ m₂ : Memory} (h₁ : Ops.Exec oracle os₁ fr m fr₁ m₁)
    (h₂ : Ops.Exec oracle os₂ fr₁ m₁ fr₂ m₂) : Ops.Exec oracle (os₁ ++ os₂) fr m fr₂ m₂ := by
  induction h₁ with
  | nil => exact h₂
  | op he _ ih => exact .op he (ih h₂)
  | call hr ho hw _ ih => exact .call hr ho hw (ih h₂)

/-- A run finishes with returned values exactly at a `ret` under the empty stack. -/
theorem step_eq_returned_iff {p : Prog R} {s : State R} {vs : List Word} {m : Memory} :
    step p s = .returned vs m ↔
      ∃ regs, p.fetch s.point = some (.term (.ret regs)) ∧ s.frame.readAll regs = some vs ∧
        s.stack = [] ∧ s.mem = m := by
  constructor
  · intro h
    have key : ∀ r : Result R, Transition p s r → r = .returned vs m →
        ∃ regs, p.fetch s.point = some (.term (.ret regs)) ∧ s.frame.readAll regs = some vs ∧
          s.stack = [] ∧ s.mem = m := by
      intro r htr
      cases htr with
      | halt hf hv hstk =>
        intro heq
        rw [Result.returned.injEq] at heq
        exact ⟨_, hf, heq.1 ▸ hv, hstk, heq.2⟩
      | _ => intro heq; exact absurd heq (by simp)
    exact key _ (Transition.of_step h (by simp)) rfl
  · rintro ⟨regs, hf, hv, hstk, rfl⟩
    exact (Transition.halt hf hv hstk).step_eq

/-- A run finishes with a trap exactly at a `trap` terminator. -/
theorem step_eq_trapped_iff {p : Prog R} {s : State R} {m : Memory} :
    step p s = .trapped m ↔ p.fetch s.point = some (.term .trap) ∧ s.mem = m := by
  constructor
  · intro h
    have key : ∀ r : Result R, Transition p s r → r = .trapped m →
        p.fetch s.point = some (.term .trap) ∧ s.mem = m := by
      intro r htr
      cases htr with
      | trap hf => intro heq; exact ⟨hf, (Result.trapped.inj heq)⟩
      | _ => intro heq; exact absurd heq (by simp)
    exact key _ (Transition.of_step h (by simp)) rfl
  · rintro ⟨hf, rfl⟩
    exact (Transition.trap hf).step_eq

/-! ## Runs that stay inside one activation

The small-step machine has one global run; a big-step derivation describes the
run of **one** activation. The two agree only as long as the machine has not
popped the stack the activation started under, because once it has, the states
it visits belong to the caller and not to the function being described. The
relations below are the small-step runs restricted to that window. -/

/-- One running step that does not pop below the stack `k`. The restriction is
what makes a run "a run of the current activation": a `ret` that pops `k` itself
leaves the activation and is excluded. -/
def StepWithin (p : Prog R) (k : List (Activation R)) (s t : State R) : Prop :=
  Step p s t ∧ k <:+ t.stack

/-- Zero or more steps that never pop below `k`. -/
abbrev StepsWithin (p : Prog R) (k : List (Activation R)) : State R → State R → Prop :=
  Relation.ReflTransGen (StepWithin p k)

/-- An infinite run that never pops below `k`: the current activation itself
runs forever, rather than returning into a caller that does. -/
def DivergesWithin (p : Prog R) (k : List (Activation R)) (s : State R) : Prop :=
  Silmaril.InfiniteTrace (StepWithin p k)  s

/-- Under the empty stack nothing can be popped, so the restriction is vacuous. -/
theorem stepWithin_nil_iff {p : Prog R} {s t : State R} : StepWithin p [] s t ↔ Step p s t :=
  ⟨fun h => h.1, fun h => ⟨h, List.nil_suffix⟩⟩

/-- Under the empty stack a restricted run is an ordinary run. -/
theorem stepsWithin_nil_iff {p : Prog R} {s t : State R} :
    StepsWithin p [] s t ↔ Steps p s t := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail hstep.1
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail (stepWithin_nil_iff.mpr hstep)

/-- Under the empty stack an infinite restricted run is an infinite run. -/
theorem divergesWithin_nil_iff {p : Prog R} {s : State R} :
    DivergesWithin p [] s ↔ Diverges p s := by
  constructor
  · exact fun h => h.map id (fun _ _ hs => hs.1)
  · exact fun h => h.map id (fun _ _ hs => stepWithin_nil_iff.mpr hs)

/-- A restricted run is a run. -/
theorem StepsWithin.toSteps {p : Prog R} {k : List (Activation R)} {s t : State R}
    (h : StepsWithin p k s t) : Steps p s t := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail hstep.1

/-- Restricted steps are deterministic, because steps are. -/
theorem StepWithin.deterministic {p : Prog R} {k : List (Activation R)} {s a b : State R}
    (ha : StepWithin p k s a) (hb : StepWithin p k s b) : a = b :=
  Step.deterministic ha.1 hb.1

/-- Two restricted runs from the same state are prefixes of one another. -/
theorem StepsWithin.total {p : Prog R} {k : List (Activation R)} {s a b : State R}
    (ha : StepsWithin p k s a) (hb : StepsWithin p k s b) :
    StepsWithin p k a b ∨ StepsWithin p k b a :=
  Relation.ReflTransGen.total_of_right_unique
    (fun _ _ _ h₁ h₂ => StepWithin.deterministic h₁ h₂) ha hb

/-- An infinite restricted run is inherited by every state it reaches. -/
theorem DivergesWithin.of_stepsWithin {p : Prog R} {k : List (Activation R)} {s t : State R}
    (d : DivergesWithin p k s) (h : StepsWithin p k s t) : DivergesWithin p k t := by
  induction h with
  | refl => exact d
  | tail _ hstep ih =>
    obtain ⟨b, hb, tail⟩ := ih.unfold
    rw [StepWithin.deterministic hstep hb]
    exact tail

/-- A step leaves the stack alone, pushes one activation, or pops one. -/
theorem Step.stack_cases {p : Prog R} {s t : State R} (h : Step p s t) :
    t.stack = s.stack ∨ (∃ a, t.stack = a :: s.stack) ∨ (∃ a, s.stack = a :: t.stack) := by
  have ht : Transition p s (.running t) := Transition.of_step h (by simp)
  cases ht with
  | op _ _ => exact Or.inl rfl
  | call _ _ _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | jump _ _ _ _ => exact Or.inl rfl
  | cond _ _ _ _ _ => exact Or.inl rfl
  | ret _ _ hs _ _ => exact Or.inr (Or.inr ⟨_, hs⟩)

/-- **A step is independent of what lies under the stack.** Pushing a block of
suspended callers under every state of a step leaves it a step. -/
theorem Step.appendStack {p : Prog R} {s t : State R} (h : Step p s t)
    (k : List (Activation R)) :
    Step p { s with stack := s.stack ++ k } { t with stack := t.stack ++ k } := by
  have ht : Transition p s (.running t) := Transition.of_step h (by simp)
  cases ht with
  | op hf he => exact (Transition.op (s := { s with stack := s.stack ++ k }) hf he).step_eq
  | call hf ha he =>
    exact (Transition.call (s := { s with stack := s.stack ++ k }) hf ha he).step_eq
  | jump hf hv hb hw =>
    exact (Transition.jump (s := { s with stack := s.stack ++ k }) hf hv hb hw).step_eq
  | cond hf hc hv hb hw =>
    exact (Transition.cond (s := { s with stack := s.stack ++ k }) hf hc hv hb hw).step_eq
  | ret hf hv hs ha hw =>
    refine (Transition.ret (s := { s with stack := s.stack ++ k }) hf hv ?_ ha hw).step_eq
    show s.stack ++ k = _
    rw [hs]
    rfl

/-- A run is independent of what lies under the stack, and the extended run stays
inside whatever the extension itself lies above. -/
theorem Steps.appendStack {p : Prog R} {s t : State R} (h : Steps p s t)
    {σ k : List (Activation R)} (hk : k <:+ σ) :
    StepsWithin p k { s with stack := s.stack ++ σ } { t with stack := t.stack ++ σ } := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact ih.tail ⟨hstep.appendStack σ, hk.trans (List.suffix_append _ _)⟩

/-- **A step is independent of what lies under the stack**, read backwards:
a step between two states whose stacks both end in `k` is a step between the
states with `k` removed. -/
theorem Step.dropStack {p : Prog R} {s t : State R} {σ τ k : List (Activation R)}
    (h : Step p s t) (hs : s.stack = σ ++ k) (ht : t.stack = τ ++ k) :
    Step p { s with stack := σ } { t with stack := τ } := by
  have htr : Transition p s (.running t) := Transition.of_step h (by simp)
  cases htr with
  | op hf he =>
    rw [show τ = σ from List.append_cancel_right (bs := k) (ht.symm.trans hs)]
    exact (Transition.op (s := { s with stack := σ }) hf he).step_eq
  | call hf ha he =>
    have hτ : τ = ⟨s.point, s.frame⟩ :: σ := by
      refine List.append_cancel_right (bs := k) ?_
      rw [← ht]
      show ⟨s.point, s.frame⟩ :: s.stack = _
      rw [hs]
      rfl
    rw [hτ]
    exact (Transition.call (s := { s with stack := σ }) hf ha he).step_eq
  | jump hf hv hb hw =>
    rw [show τ = σ from List.append_cancel_right (bs := k) (ht.symm.trans hs)]
    exact (Transition.jump (s := { s with stack := σ }) hf hv hb hw).step_eq
  | cond hf hc hv hb hw =>
    rw [show τ = σ from List.append_cancel_right (bs := k) (ht.symm.trans hs)]
    exact (Transition.cond (s := { s with stack := σ }) hf hc hv hb hw).step_eq
  | ret hf hv hstk ha hw =>
    rename_i _ _ a rest _ _ _ _
    have hσ : σ = a :: τ := by
      refine List.append_cancel_right (bs := k) ?_
      rw [← hs, hstk]
      exact congrArg (fun l => a :: l) (show rest = τ ++ k from ht)
    rw [hσ]
    exact (Transition.ret (s := { s with stack := a :: τ }) hf hv rfl ha hw).step_eq

/-! ## The oracle a program induces -/

namespace Prog

/-- The call oracle of a program: a callee relates its arguments and the initial
memory to the values and memory of a run that returns. -/
def oracle (p : Prog R) : CallOracle :=
  fun f args m vs m' => ∃ s, p.start f args m = some s ∧ Behaves p s (.returned vs m')

/-- The divergence oracle of a program: a callee relates its arguments and the
initial memory to the fact that the run never finishes. -/
def divOracle (p : Prog R) : DivOracle :=
  fun f args m => ∃ s, p.start f args m = some s ∧ Diverges p s

/-- A whole-program start state is the callee's entry point under an empty stack. -/
theorem start_eq_some_iff {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory}
    {s : State R} : p.start f args mem = some s ↔
      ∃ pt fr, p.enter f args = some (pt, fr) ∧ s = ⟨pt, fr, [], mem⟩ := by
  constructor
  · intro h
    rw [Prog.start] at h
    cases he : p.enter f args with
    | none => rw [he] at h; exact absurd h (by simp)
    | some pf =>
      obtain ⟨pt, fr⟩ := pf
      rw [he] at h
      exact ⟨pt, fr, rfl, (Option.some.inj h).symm⟩
  · rintro ⟨pt, fr, he, rfl⟩
    rw [Prog.start, he]
    rfl

/-- **A program's call oracle is deterministic**, because the machine is. -/
theorem oracle_deterministic (p : Prog R) : (p.oracle).Deterministic := by
  rintro f args m vs₁ m₁ vs₂ m₂ ⟨s₁, hs₁, hb₁⟩ ⟨s₂, hs₂, hb₂⟩
  rw [hs₁] at hs₂
  obtain rfl := Option.some.inj hs₂
  have := Behaves.unique hb₁ hb₂
  rw [Behavior.returned.injEq] at this
  exact ⟨this.1, this.2⟩

/-- The machine reaches the `ret` of the activation it started in, with the given
values and memory and the stack it began with. This is "the current function
returns", stated without popping the stack, so that it makes sense for a callee
running underneath suspended callers.

The run is a `StepsWithin` and not a bare `Steps`, which matters: a bare `Steps`
would also admit a state reached *after* the activation has already returned and
a caller has called the same function again at the same point with the same
frame, and the second return generally carries different values and a different
memory from the first. Restricting to the window in which `s.stack` has not been
popped is exactly what makes this "the current activation returns". -/
def Returns (p : Prog R) (s : State R) (vs : List Word) (m' : Memory) : Prop :=
  ∃ t regs, StepsWithin p s.stack s t ∧ t.stack = s.stack ∧
    p.fetch t.point = some (.term (.ret regs)) ∧ t.frame.readAll regs = some vs ∧ t.mem = m'

/-- The machine reaches the `trap` of the activation it started in, with the run
restricted to that activation for the reason given for `Prog.Returns`. -/
def Traps (p : Prog R) (s : State R) (m' : Memory) : Prop :=
  ∃ t, StepsWithin p s.stack s t ∧ t.stack = s.stack ∧
    p.fetch t.point = some (.term .trap) ∧ t.mem = m'

end Prog

/-! ## The bridge to the small-step machine

This is the only part of the development that mentions the call stack. The four
theorems at the end of the section are what it exists for; everything before them
is the machinery they need, in the order they need it: a straight-line run as a
machine run, a whole big-step run as a machine run, machine runs counted so that
the converse can recurse on their length, and the two coinductive arguments for
divergence. Once the four theorems are available, the correspondence with
lambda-SSA is a statement about `Func.Exec` and `Func.Diverges` alone. -/

/-- **A straight-line big-step run is a run of the machine.** Each call the
oracle resolves becomes a push, the whole run of the callee and a pop, and none
of those steps pops below the stack the block is running under. The run may be
any contiguous stretch `os` of the block's ops, with `pre` before it and `post`
after. -/
theorem Ops.Exec.stepsWithin {p : Prog R} {os : List (Op R)} {fr fr' : Frame R}
    {m m' : Memory} (h : Ops.Exec p.oracle os fr m fr' m')
    {f : FuncId} {l : Label} {b : Block R} {k : List (Activation R)}
    (hb : p.block? f l = some b) {pre post : List (Op R)} (hops : b.ops = pre ++ os ++ post) :
    StepsWithin p k ⟨⟨f, l, pre.length⟩, fr, k, m⟩ ⟨⟨f, l, (pre ++ os).length⟩, fr', k, m'⟩ := by
  induction h generalizing pre with
  | nil => rw [List.append_nil]
  | @op o os fr₀ fr₁ fr₂ m₀ m₁ m₂ he _ ih =>
    have hop : b.ops[pre.length]? = some o := by rw [hops]; simp
    have hrest := ih (pre := pre ++ [o]) (by rw [hops]; simp)
    rw [show (pre ++ [o]).length = pre.length + 1 from by simp,
      show (pre ++ [o]) ++ os = pre ++ o :: os from by simp] at hrest
    refine .head ⟨?_, List.suffix_refl k⟩ hrest
    exact (Transition.op (s := ⟨⟨f, l, pre.length⟩, fr₀, k, m₀⟩) (Prog.fetch_op hb hop) he).step_eq
  | @call g args results os fr₀ fr₁ fr₂ m₀ m₁ m₂ vals vs hread horacle hwrite _ ih =>
    have hop : b.ops[pre.length]? = some (Op.call g args results) := by rw [hops]; simp
    have hfetch := Prog.fetch_op hb hop
    obtain ⟨s₀, hstart, hbeh⟩ := horacle
    obtain ⟨pt, cfr, henter, rfl⟩ := Prog.start_eq_some_iff.mp hstart
    obtain ⟨u, hu, hufin⟩ := hbeh
    obtain ⟨upt, ufr, ust, umem⟩ := u
    obtain ⟨regs, hrf, hrv, hrs, hrm⟩ := step_eq_returned_iff.mp hufin
    have hrs' : ust = [] := hrs
    have hrm' : umem = m₁ := hrm
    subst hrs'
    subst umem
    have hcall : Step p ⟨⟨f, l, pre.length⟩, fr₀, k, m₀⟩
        ⟨pt, cfr, ⟨⟨f, l, pre.length⟩, fr₀⟩ :: k, m₀⟩ :=
      (Transition.call (s := ⟨⟨f, l, pre.length⟩, fr₀, k, m₀⟩) hfetch hread henter).step_eq
    have hsub : StepsWithin p k ⟨pt, cfr, ⟨⟨f, l, pre.length⟩, fr₀⟩ :: k, m₀⟩
        ⟨upt, ufr, ⟨⟨f, l, pre.length⟩, fr₀⟩ :: k, m₁⟩ :=
      Steps.appendStack hu (σ := ⟨⟨f, l, pre.length⟩, fr₀⟩ :: k) (List.suffix_cons _ _)
    have hpop : Step p ⟨upt, ufr, ⟨⟨f, l, pre.length⟩, fr₀⟩ :: k, m₁⟩
        ⟨⟨f, l, pre.length + 1⟩, fr₁, k, m₁⟩ :=
      (Transition.ret (s := ⟨upt, ufr, ⟨⟨f, l, pre.length⟩, fr₀⟩ :: k, m₁⟩)
        hrf hrv rfl hfetch hwrite).step_eq
    have hrest := ih (pre := pre ++ [Op.call g args results]) (by rw [hops]; simp)
    rw [show (pre ++ [Op.call g args results]).length = pre.length + 1 from by simp,
      show (pre ++ [Op.call g args results]) ++ os = pre ++ Op.call g args results :: os from
        by simp] at hrest
    exact .head ⟨hcall, List.suffix_cons _ _⟩
      (hsub.trans (.head ⟨hpop, List.suffix_refl k⟩ hrest))

/-- A run restricted to a deeper stack is restricted to a shallower one. -/
theorem StepsWithin.mono {p : Prog R} {κ k : List (Activation R)} (hk : k <:+ κ)
    {s t : State R} (h : StepsWithin p κ s t) : StepsWithin p k s t := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail ⟨hstep.1, hk.trans hstep.2⟩

/-- The machine state an activation is in when it finishes: at a `ret` whose
registers read the returned values, or at a `trap`. -/
def Prog.ExitsAt (p : Prog R) (t : State R) : Exit → Prop
  | .returned vs m' =>
    ∃ regs, p.fetch t.point = some (.term (.ret regs)) ∧ t.frame.readAll regs = some vs ∧
      t.mem = m'
  | .trapped m' => p.fetch t.point = some (.term .trap) ∧ t.mem = m'

/-- **A big-step run of a function is a run of the machine.** It stays inside the
activation it started in and stops at the exit the derivation names. -/
theorem Func.Exec.stepsWithin {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) {l : Label} {fr : Frame R} {m : Memory} {out : Exit}
    (h : Func.Exec p.oracle fn l fr m out) (k : List (Activation R)) :
    ∃ t, StepsWithin p k ⟨⟨f, l, 0⟩, fr, k, m⟩ t ∧ t.stack = k ∧ p.ExitsAt t out := by
  induction h with
  | @jump l t b bt as vals fr fr₁ fr₂ m m₁ out hbl hops hterm hargs hbt hwrite _ ih =>
    have hb : p.block? f l = some b := (Prog.block?_eq_of_func hfn l).trans hbl
    have hbt' : p.block? f t = some bt := (Prog.block?_eq_of_func hfn t).trans hbt
    obtain ⟨t', hsteps, hstack, hexit⟩ := ih
    refine ⟨t', (hops.stepsWithin hb (pre := []) (post := []) (by simp)).trans
      (.head ⟨?_, List.suffix_refl k⟩ hsteps), hstack, hexit⟩
    exact (Transition.jump (s := ⟨⟨f, l, b.ops.length⟩, fr₁, k, m₁⟩)
      (hterm ▸ Prog.fetch_term hb) hargs hbt' hwrite).step_eq
  | @cond l t₁ t₂ c a₁ a₂ b bt x vals fr fr₁ fr₂ m m₁ out hbl hops hterm hget hargs hbt
      hwrite _ ih =>
    have hb : p.block? f l = some b := (Prog.block?_eq_of_func hfn l).trans hbl
    have hbt' : p.block? f (if x = 0 then t₂ else t₁) = some bt :=
      (Prog.block?_eq_of_func hfn _).trans hbt
    obtain ⟨t', hsteps, hstack, hexit⟩ := ih
    refine ⟨t', (hops.stepsWithin hb (pre := []) (post := []) (by simp)).trans
      (.head ⟨?_, List.suffix_refl k⟩ hsteps), hstack, hexit⟩
    exact (Transition.cond (s := ⟨⟨f, l, b.ops.length⟩, fr₁, k, m₁⟩)
      (hterm ▸ Prog.fetch_term hb) hget hargs hbt' hwrite).step_eq
  | @ret l b regs vals fr fr₁ m m₁ hbl hops hterm hargs =>
    have hb : p.block? f l = some b := (Prog.block?_eq_of_func hfn l).trans hbl
    exact ⟨⟨⟨f, l, b.ops.length⟩, fr₁, k, m₁⟩,
      hops.stepsWithin hb (pre := []) (post := []) (by simp), rfl,
      regs, hterm ▸ Prog.fetch_term hb, hargs, rfl⟩
  | @trap l b fr fr₁ m m₁ hbl hops hterm =>
    have hb : p.block? f l = some b := (Prog.block?_eq_of_func hfn l).trans hbl
    exact ⟨⟨⟨f, l, b.ops.length⟩, fr₁, k, m₁⟩,
      hops.stepsWithin hb (pre := []) (post := []) (by simp), rfl,
      hterm ▸ Prog.fetch_term hb, rfl⟩

/-- A restricted run of exactly `n` steps. Reconstructing a big-step derivation
from a machine run recurses on the length of the run, not on its structure,
because a call is consumed several steps at a time. -/
inductive StepsNWithin (p : Prog R) (k : List (Activation R)) : Nat → State R → State R → Prop
  | refl {s : State R} : StepsNWithin p k 0 s s
  | head {n : Nat} {s u t : State R} :
      StepWithin p k s u → StepsNWithin p k n u t → StepsNWithin p k (n + 1) s t

/-- A counted run is a run. -/
theorem StepsNWithin.toStepsWithin {p : Prog R} {k : List (Activation R)} {n : Nat}
    {s t : State R} (h : StepsNWithin p k n s t) : StepsWithin p k s t := by
  induction h with
  | refl => exact .refl
  | head hstep _ ih => exact .head hstep ih

/-- Every restricted run has a length. -/
theorem StepsWithin.exists_stepsN {p : Prog R} {k : List (Activation R)} {s t : State R}
    (h : StepsWithin p k s t) : ∃ n, StepsNWithin p k n s t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl⟩
  | head hstep _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .head hstep hn⟩

/-- **A restricted run drops the stack it is restricted to.** Every state it
visits lies above `κ`, so removing `κ` everywhere leaves a run of the machine. -/
theorem StepsWithin.dropStack {p : Prog R} {κ : List (Activation R)} {s t : State R}
    (h : StepsWithin p κ s t) : ∀ {σ τ : List (Activation R)}, s.stack = σ ++ κ →
      t.stack = τ ++ κ → Steps p ⟨s.point, s.frame, σ, s.mem⟩ ⟨t.point, t.frame, τ, t.mem⟩ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro σ τ hσ hτ
    rw [List.append_cancel_right (bs := κ) (hσ.symm.trans hτ)]
  | @head a c hstep _ ih =>
    intro σ τ hσ hτ
    obtain ⟨σ', hσ'⟩ := hstep.2
    exact .head (Step.dropStack hstep.1 hσ hσ'.symm) (ih hσ'.symm hτ)

/-- **A restricted run that returns to its base stack passes through the pop.**
If the run starts above an activation `a` resting on `k` and ends at `k`, it
splits into a run above `a`, the step that pops `a`, and the rest. -/
theorem StepsNWithin.split_pop {p : Prog R} {k : List (Activation R)} {a : Activation R}
    {n : Nat} {s t : State R} (h : StepsNWithin p k n s t) (hs : a :: k <:+ s.stack)
    (ht : t.stack = k) :
    ∃ n₁ n₂ u v, n = n₁ + 1 + n₂ ∧ StepsNWithin p (a :: k) n₁ s u ∧ u.stack = a :: k ∧
      Step p u v ∧ v.stack = k ∧ StepsNWithin p k n₂ v t := by
  induction h with
  | refl =>
    rw [ht] at hs
    exact absurd hs.length_le (by simp)
  | @head n s u t hstep hrest ih =>
    by_cases hcase : a :: k <:+ u.stack
    · obtain ⟨n₁, n₂, w, v, hn, h₁, hw, hstep₂, hv, h₂⟩ := ih hcase ht
      exact ⟨n₁ + 1, n₂, w, v, by omega, .head ⟨hstep.1, hcase⟩ h₁, hw, hstep₂, hv, h₂⟩
    · rcases hstep.1.stack_cases with heq | ⟨c, heq⟩ | ⟨c, heq⟩
      · exact absurd (heq ▸ hs) hcase
      · exact absurd (hs.trans (heq ▸ List.suffix_cons c s.stack)) hcase
      · rcases List.suffix_cons_iff.mp (heq ▸ hs) with hone | hmore
        · refine ⟨0, n, s, u, by omega, .refl, ?_, hstep.1, ?_, hrest⟩
          · rw [heq, (List.cons.inj hone).1, (List.cons.inj hone).2]
          · exact (List.cons.inj hone).2.symm
        · exact absurd hmore hcase

/-- **A step that pops the stack is the `ret` of the activation it pops.** -/
theorem Step.pop_eq {p : Prog R} {s t : State R} {a : Activation R} {rest : List (Activation R)}
    (h : Step p s t) (hs : s.stack = a :: rest) (ht : t.stack = rest) :
    ∃ regs vals g args results fr, p.fetch s.point = some (.term (.ret regs)) ∧
      s.frame.readAll regs = some vals ∧
      p.fetch a.point = some (.op (.call g args results)) ∧
      a.frame.writeAll results vals = some fr ∧ t = ⟨a.point.next, fr, rest, s.mem⟩ := by
  have htr : Transition p s (.running t) := Transition.of_step h (by simp)
  cases htr with
  | op _ _ =>
    have h1 : s.stack = rest := ht
    rw [hs] at h1
    exfalso
    have h2 := congrArg List.length h1
    simp only [List.length_cons] at h2
    omega
  | call _ _ _ =>
    have h1 : (⟨s.point, s.frame⟩ : Activation R) :: s.stack = rest := ht
    rw [hs] at h1
    exfalso
    have h2 := congrArg List.length h1
    simp only [List.length_cons] at h2
    omega
  | jump _ _ _ _ =>
    have h1 : s.stack = rest := ht
    rw [hs] at h1
    exfalso
    have h2 := congrArg List.length h1
    simp only [List.length_cons] at h2
    omega
  | cond _ _ _ _ _ =>
    have h1 : s.stack = rest := ht
    rw [hs] at h1
    exfalso
    have h2 := congrArg List.length h1
    simp only [List.length_cons] at h2
    omega
  | ret hf hv hstk ha hw =>
    rename_i regs vals a₀ rest₀ g args results fr
    obtain ⟨rfl, rfl⟩ : a₀ = a ∧ rest₀ = rest := by
      have := hstk.symm.trans hs
      exact ⟨(List.cons.inj this).1, (List.cons.inj this).2⟩
    exact ⟨regs, vals, g, args, results, fr, hf, hv, ha, hw, rfl⟩

/-- **A machine run of one activation that stops at an exit is a big-step run.**
The derivation is reconstructed from the length of the run: an op is one step, a
call is a push, the whole run of the callee and a pop, and a transfer restarts at
the target block. The last hypothesis carries the ops of the current block that
have already run, so that the recursion may start in the middle of a block. -/
private theorem exec_of_stepsNWithin {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) :
    ∀ (n : Nat) (l : Label) (i : Nat) (b : Block R) (fr : Frame R) (m : Memory)
      (k : List (Activation R)) (t : State R) (out : Exit) (fr₀ : Frame R) (m₀ : Memory),
      fn.block? l = some b → StepsNWithin p k n ⟨⟨f, l, i⟩, fr, k, m⟩ t → t.stack = k →
      p.ExitsAt t out → Ops.Exec p.oracle (b.ops.take i) fr₀ m₀ fr m →
      Func.Exec p.oracle fn l fr₀ m₀ out := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l i b fr m k t out fr₀ m₀ hbl hrun hstack hexit hpre
    have hb : p.block? f l = some b := (Prog.block?_eq_of_func hfn l).trans hbl
    cases n with
    | zero =>
      cases hrun with
      | refl =>
        cases out with
        | returned vs m' =>
          obtain ⟨regs, hf, hv, hm⟩ := hexit
          rcases Prog.fetch_cases hb hf with ⟨o, _, hco⟩ | ⟨hi, hct⟩
          · exact absurd hco (by simp)
          · subst hi
            rw [List.take_length] at hpre
            have hm' : m = m' := hm
            subst hm'
            exact .ret hbl hpre (Code.term.inj hct).symm hv
        | trapped m' =>
          obtain ⟨hf, hm⟩ := hexit
          rcases Prog.fetch_cases hb hf with ⟨o, _, hco⟩ | ⟨hi, hct⟩
          · exact absurd hco (by simp)
          · subst hi
            rw [List.take_length] at hpre
            have hm' : m = m' := hm
            subst hm'
            exact .trap hbl hpre (Code.term.inj hct).symm
    | succ n' =>
      cases hrun with
      | @head _ _ u _ hstep hrest =>
        have htr : Transition p (⟨⟨f, l, i⟩, fr, k, m⟩ : State R) (.running u) :=
          Transition.of_step hstep.1 (by simp)
        cases htr with
        | op hf he =>
          rename_i o fr₁ m₁
          rcases Prog.fetch_cases hb hf with ⟨o', hop, hco⟩ | ⟨_, hct⟩
          · have hop' : b.ops[i]? = some o := by rw [hop, ← Code.op.inj hco]
            have htake : b.ops.take (i + 1) = b.ops.take i ++ [o] := by
              rw [List.take_add_one, hop']
              rfl
            refine ih n' (by omega) l (i + 1) b fr₁ m₁ k t out fr₀ m₀ hbl hrest hstack hexit ?_
            rw [htake]
            exact hpre.append (.op he .nil)
          · exact absurd hct (by simp)
        | call hf ha he =>
          rename_i g args results vals pt cfr
          rcases Prog.fetch_cases hb hf with ⟨o', hop, hco⟩ | ⟨_, hct⟩
          · have hop' : b.ops[i]? = some (Op.call g args results) := by
              rw [hop, ← Code.op.inj hco]
            obtain ⟨n₁, n₂, w, v, hn, hrun₁, hw, hpop, hv, hrun₂⟩ :=
              hrest.split_pop (a := ⟨⟨f, l, i⟩, fr⟩) (List.suffix_refl _) hstack
            obtain ⟨regs', vals', g', args', results', fr', hf2, hv2, ha2, hw2, hveq⟩ :=
              hpop.pop_eq hw hv
            have heq := Op.call.inj (Code.op.inj (Option.some.inj (ha2.symm.trans hf)))
            rw [heq.2.2] at hw2
            have hstart : p.start g vals m = some ⟨pt, cfr, [], m⟩ :=
              Prog.start_eq_some_iff.mpr ⟨pt, cfr, he, rfl⟩
            have hinner : Steps p ⟨pt, cfr, [], m⟩ ⟨w.point, w.frame, [], w.mem⟩ :=
              hrun₁.toStepsWithin.dropStack (σ := []) (τ := []) rfl hw
            have horacle : p.oracle g vals m vals' w.mem :=
              ⟨_, hstart, ⟨w.point, w.frame, [], w.mem⟩, hinner,
                step_eq_returned_iff.mpr ⟨regs', hf2, hv2, rfl, rfl⟩⟩
            have htake : b.ops.take (i + 1) = b.ops.take i ++ [Op.call g args results] := by
              rw [List.take_add_one, hop']
              rfl
            refine ih n₂ (by omega) l (i + 1) b fr' w.mem k t out fr₀ m₀ hbl ?_ hstack hexit ?_
            · rw [hveq] at hrun₂
              exact hrun₂
            · rw [htake]
              exact hpre.append (.call ha horacle hw2 .nil)
          · exact absurd hct (by simp)
        | jump hf hv hbt hw =>
          rename_i tgt as vals bt fr₂
          rcases Prog.fetch_cases hb hf with ⟨o', _, hco⟩ | ⟨hi, hct⟩
          · exact absurd hco (by simp)
          · subst hi
            rw [List.take_length] at hpre
            have hbt' : fn.block? tgt = some bt := (Prog.block?_eq_of_func hfn tgt).symm.trans hbt
            exact .jump hbl hpre (Code.term.inj hct).symm hv hbt' hw
              (ih n' (by omega) tgt 0 bt fr₂ m k t out fr₂ m hbt' hrest hstack hexit .nil)
        | cond hf hc hv hbt hw =>
          rename_i c t₁ t₂ a₁ a₂ x vals bt fr₂
          rcases Prog.fetch_cases hb hf with ⟨o', _, hco⟩ | ⟨hi, hct⟩
          · exact absurd hco (by simp)
          · subst hi
            rw [List.take_length] at hpre
            have hbt' : fn.block? (if x = 0 then t₂ else t₁) = some bt :=
              (Prog.block?_eq_of_func hfn _).symm.trans hbt
            exact .cond hbl hpre (Code.term.inj hct).symm hc hv hbt' hw
              (ih n' (by omega) (if x = 0 then t₂ else t₁) 0 bt fr₂ m k t out fr₂ m hbt' hrest
                hstack hexit .nil)
        | ret hf hv hstk ha hw =>
          rename_i _ _ a₀ rest _ _ _ _
          exfalso
          have h1 : k <:+ rest := hstep.2
          have hk : k = a₀ :: rest := hstk
          rw [hk] at h1
          have h2 := h1.length_le
          simp only [List.length_cons] at h2
          omega

omit [DecidableEq R] in
/-- Fetching succeeds only inside an existing block. -/
theorem Prog.block?_isSome_of_fetch {p : Prog R} {pt : Point} {c : Code R}
    (h : p.fetch pt = some c) : ∃ b, p.block? pt.func pt.label = some b := by
  cases hb : p.block? pt.func pt.label with
  | some b => exact ⟨b, rfl⟩
  | none =>
    rw [Prog.fetch, hb] at h
    exact absurd h (by simp)

/-- A step reads code, so the state it starts from has some. -/
theorem Step.fetch_isSome {p : Prog R} {s t : State R} (h : Step p s t) :
    ∃ c, p.fetch s.point = some c := by
  cases hf : p.fetch s.point with
  | some c => exact ⟨c, rfl⟩
  | none =>
    have h' : step p s = .running t := h
    simp [step, hf] at h'

omit [DecidableEq R] in
/-- An exit state reads code. -/
theorem Prog.ExitsAt.fetch_isSome {p : Prog R} {t : State R} {out : Exit}
    (h : p.ExitsAt t out) : ∃ c, p.fetch t.point = some c := by
  cases out with
  | returned vs m' => obtain ⟨regs, hf, _⟩ := h; exact ⟨_, hf⟩
  | trapped m' => exact ⟨_, h.1⟩

/-- A run that stops at an exit starts inside an existing block. -/
private theorem block?_of_stepsNWithin {p : Prog R} {f : FuncId} {l : Label} {i : Nat}
    {fr : Frame R} {k : List (Activation R)} {m : Memory} {n : Nat} {t : State R} {out : Exit}
    (hrun : StepsNWithin p k n ⟨⟨f, l, i⟩, fr, k, m⟩ t) (hexit : p.ExitsAt t out) :
    ∃ b, p.block? f l = some b := by
  cases hrun with
  | refl =>
    obtain ⟨c, hc⟩ := hexit.fetch_isSome
    exact Prog.block?_isSome_of_fetch hc
  | head hstep _ =>
    obtain ⟨c, hc⟩ := hstep.1.fetch_isSome
    exact Prog.block?_isSome_of_fetch hc

/-- The relation witnessing that a big-step divergent run drives the machine
forever: from `s` the machine either can still reach the start of a divergent
configuration, or already runs forever inside the activation. -/
private def DivWitness (p : Prog R) (fn : Func R) (f : FuncId) (k : List (Activation R))
    (s : State R) : Prop :=
  (∃ c : DivConfig R, Func.Diverges p.oracle p.divOracle fn c ∧
      StepsWithin p k s ⟨⟨f, c.label, 0⟩, c.frame, k, c.mem⟩) ∨ DivergesWithin p k s

/-- Reaching the start of a divergent configuration in at least one step keeps
the witness going. -/
private theorem DivWitness.transfer {p : Prog R} {fn : Func R} {f : FuncId}
    {k : List (Activation R)} {s u : State R} {c : DivConfig R}
    (hrun : StepsWithin p k s u)
    (hstep : StepWithin p k u ⟨⟨f, c.label, 0⟩, c.frame, k, c.mem⟩)
    (hdiv : Func.Diverges p.oracle p.divOracle fn c) :
    ∃ t, StepWithin p k s t ∧ DivWitness p fn f k t := by
  rcases hrun.cases_head with rfl | ⟨w, hw₁, hw₂⟩
  · exact ⟨_, hstep, Or.inl ⟨c, hdiv, .refl⟩⟩
  · exact ⟨w, hw₁, Or.inl ⟨c, hdiv, hw₂.tail hstep⟩⟩

/-- **A big-step divergent run drives the machine forever** without ever leaving
the activation it started in. -/
theorem Func.Diverges.divergesWithin {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) {l : Label} {fr : Frame R} {m : Memory}
    (h : Func.Diverges p.oracle p.divOracle fn ⟨l, fr, m⟩) (k : List (Activation R)) :
    DivergesWithin p k ⟨⟨f, l, 0⟩, fr, k, m⟩ := by
  refine Silmaril.InfiniteTrace.coinduct (DivWitness p fn f k) ?_ (Or.inl ⟨⟨l, fr, m⟩, h, .refl⟩)
  rintro s (⟨c, hc, hreach⟩ | hdiv)
  · rcases hreach.cases_head with rfl | ⟨u, hstep, hrest⟩
    · cases hc.unfold with
      | @call l' b pre g args results post fr' fr₁ m' m₁ vals hbl hopseq hexec hargs hdivo =>
        have hb : p.block? f l' = some b := (Prog.block?_eq_of_func hfn l').trans hbl
        have hops : StepsWithin p k ⟨⟨f, l', 0⟩, fr', k, m'⟩ ⟨⟨f, l', pre.length⟩, fr₁, k, m₁⟩ :=
          hexec.stepsWithin hb (pre := []) (post := Op.call g args results :: post)
            (by simpa using hopseq)
        obtain ⟨s₀, hstart, hinf⟩ := hdivo
        obtain ⟨pt, cfr, henter, rfl⟩ := Prog.start_eq_some_iff.mp hstart
        have hfetch : p.fetch ⟨f, l', pre.length⟩ = some (.op (.call g args results)) :=
          Prog.fetch_op hb (by rw [hopseq]; simp)
        have hcall : Step p ⟨⟨f, l', pre.length⟩, fr₁, k, m₁⟩
            ⟨pt, cfr, ⟨⟨f, l', pre.length⟩, fr₁⟩ :: k, m₁⟩ :=
          (Transition.call (s := ⟨⟨f, l', pre.length⟩, fr₁, k, m₁⟩) hfetch hargs henter).step_eq
        have hinner : DivergesWithin p k ⟨pt, cfr, ⟨⟨f, l', pre.length⟩, fr₁⟩ :: k, m₁⟩ :=
          Silmaril.InfiniteTrace.map (R := Step p) (S := StepWithin p k)
            (fun x => { x with stack := x.stack ++ (⟨⟨f, l', pre.length⟩, fr₁⟩ :: k) })
            (fun _ _ hs => ⟨hs.appendStack _,
              (List.suffix_cons _ _).trans (List.suffix_append _ _)⟩) hinf
        have hall : DivergesWithin p k ⟨⟨f, l', 0⟩, fr', k, m'⟩ :=
          Silmaril.InfiniteTrace.of_steps hops
            (Silmaril.InfiniteTrace.fold ⟨hcall, (List.suffix_cons _ _)⟩ hinner)
        obtain ⟨u, hstep, htail⟩ := hall.unfold
        exact ⟨u, hstep, Or.inr htail⟩
      | @jump l' t' b bt as vals fr' fr₁ fr₂ m' m₁ hbl hexec hterm hargs hbt hwrite hcont =>
        have hb : p.block? f l' = some b := (Prog.block?_eq_of_func hfn l').trans hbl
        have hbt' : p.block? f t' = some bt := (Prog.block?_eq_of_func hfn t').trans hbt
        refine DivWitness.transfer (c := ⟨t', fr₂, m₁⟩)
          (hexec.stepsWithin hb (pre := []) (post := []) (by simp)) ⟨?_, List.suffix_refl k⟩ hcont
        exact (Transition.jump (s := ⟨⟨f, l', b.ops.length⟩, fr₁, k, m₁⟩)
          (hterm ▸ Prog.fetch_term hb) hargs hbt' hwrite).step_eq
      | @cond l' t₁ t₂ c' a₁ a₂ b bt x vals fr' fr₁ fr₂ m' m₁ hbl hexec hterm hget hargs hbt
          hwrite hcont =>
        have hb : p.block? f l' = some b := (Prog.block?_eq_of_func hfn l').trans hbl
        have hbt' : p.block? f (if x = 0 then t₂ else t₁) = some bt :=
          (Prog.block?_eq_of_func hfn _).trans hbt
        refine DivWitness.transfer (c := ⟨if x = 0 then t₂ else t₁, fr₂, m₁⟩)
          (hexec.stepsWithin hb (pre := []) (post := []) (by simp)) ⟨?_, List.suffix_refl k⟩ hcont
        exact (Transition.cond (s := ⟨⟨f, l', b.ops.length⟩, fr₁, k, m₁⟩)
          (hterm ▸ Prog.fetch_term hb) hget hargs hbt' hwrite).step_eq
    · exact ⟨u, hstep, Or.inl ⟨c, hc, hrest⟩⟩
  · obtain ⟨u, hstep, htail⟩ := hdiv.unfold
    exact ⟨u, hstep, Or.inr htail⟩

/-- **Running a block forever either finishes its ops or sticks in a diverging
call.** Started in the middle of a block, an infinite run of the current
activation either completes the remaining ops and goes on running at the
terminator, or reaches a call whose callee never returns. -/
private theorem divergesWithin_ops_cases {p : Prog R} {f : FuncId} {l : Label} {b : Block R}
    {k : List (Activation R)} (hb : p.block? f l = some b) :
    ∀ (os pre : List (Op R)) (fr : Frame R) (m : Memory), b.ops = pre ++ os →
      DivergesWithin p k ⟨⟨f, l, pre.length⟩, fr, k, m⟩ →
      (∃ fr₁ m₁, Ops.Exec p.oracle os fr m fr₁ m₁ ∧
          DivergesWithin p k ⟨⟨f, l, b.ops.length⟩, fr₁, k, m₁⟩) ∨
      (∃ (pre' : List (Op R)) (g : FuncId) (args results : List R) (post : List (Op R))
          (fr₁ : Frame R) (m₁ : Memory) (vals : List Word),
        os = pre' ++ Op.call g args results :: post ∧ Ops.Exec p.oracle pre' fr m fr₁ m₁ ∧
        fr₁.readAll args = some vals ∧ p.divOracle g vals m₁) := by
  intro os
  induction os with
  | nil =>
    intro pre fr m hops hdiv
    rw [List.append_nil] at hops
    exact Or.inl ⟨fr, m, .nil, by rw [hops]; exact hdiv⟩
  | cons o os ih =>
    intro pre fr m hops hdiv
    have hfetch : p.fetch ⟨f, l, pre.length⟩ = some (.op o) :=
      Prog.fetch_op hb (by rw [hops]; simp)
    obtain ⟨u, hstep, htail⟩ := Silmaril.InfiniteTrace.unfold hdiv
    have htr : Transition p (⟨⟨f, l, pre.length⟩, fr, k, m⟩ : State R) (.running u) :=
      Transition.of_step hstep.1 (by simp)
    cases htr with
    | op hf he =>
      rename_i o' fr₁ m₁
      obtain rfl : o' = o := Code.op.inj (Option.some.inj (hf.symm.trans hfetch))
      have hdiv' : DivergesWithin p k ⟨⟨f, l, (pre ++ [o']).length⟩, fr₁, k, m₁⟩ := by
        rw [show (pre ++ [o']).length = pre.length + 1 from by simp]
        exact htail
      rcases ih (pre ++ [o']) fr₁ m₁ (by rw [hops]; simp) hdiv' with
        ⟨fr₂, m₂, hexec, hd⟩ | ⟨pre', g, args, results, post, fr₂, m₂, vals, hoseq, hexec,
          hargs, hdivo⟩
      · exact Or.inl ⟨fr₂, m₂, .op he hexec, hd⟩
      · exact Or.inr ⟨o' :: pre', g, args, results, post, fr₂, m₂, vals, by rw [hoseq]; rfl,
          .op he hexec, hargs, hdivo⟩
    | call hf ha he =>
      rename_i g args results vals pt cfr
      obtain rfl : Op.call g args results = o :=
        Code.op.inj (Option.some.inj (hf.symm.trans hfetch))
      have hstart : p.start g vals m = some ⟨pt, cfr, [], m⟩ :=
        Prog.start_eq_some_iff.mpr ⟨pt, cfr, he, rfl⟩
      by_cases hret : ∃ w, StepsWithin p k ⟨pt, cfr, ⟨⟨f, l, pre.length⟩, fr⟩ :: k, m⟩ w ∧
          w.stack = k
      · obtain ⟨w, hw, hwk⟩ := hret
        obtain ⟨n, hn⟩ := hw.exists_stepsN
        obtain ⟨n₁, n₂, w', v, hn', hrun₁, hw'stack, hpop, hvstack, hrun₂⟩ :=
          hn.split_pop (a := ⟨⟨f, l, pre.length⟩, fr⟩) (List.suffix_refl _) hwk
        obtain ⟨regs', vals', g', args', results', fr', hf2, hv2, ha2, hw2, hveq⟩ :=
          hpop.pop_eq hw'stack hvstack
        have heq := Op.call.inj (Code.op.inj (Option.some.inj (ha2.symm.trans hf)))
        rw [heq.2.2] at hw2
        have hinner : Steps p ⟨pt, cfr, [], m⟩ ⟨w'.point, w'.frame, [], w'.mem⟩ :=
          hrun₁.toStepsWithin.dropStack (σ := []) (τ := []) rfl hw'stack
        have horacle : p.oracle g vals m vals' w'.mem :=
          ⟨_, hstart, ⟨w'.point, w'.frame, [], w'.mem⟩, hinner,
            step_eq_returned_iff.mpr ⟨regs', hf2, hv2, rfl, rfl⟩⟩
        have hvdiv : DivergesWithin p k v :=
          DivergesWithin.of_stepsWithin htail
            ((hrun₁.toStepsWithin.mono (List.suffix_cons _ _)).tail ⟨hpop, by rw [hvstack]⟩)
        rw [hveq] at hvdiv
        have hdiv' : DivergesWithin p k
            ⟨⟨f, l, (pre ++ [Op.call g args results]).length⟩, fr', k, w'.mem⟩ := by
          rw [show (pre ++ [Op.call g args results]).length = pre.length + 1 from by simp]
          exact hvdiv
        rcases ih (pre ++ [Op.call g args results]) fr' w'.mem (by rw [hops]; simp) hdiv' with
          ⟨fr₂, m₂, hexec, hd⟩ | ⟨pre', g₂, args₂, results₂, post, fr₂, m₂, vals₂, hoseq, hexec,
            hargs, hdivo⟩
        · exact Or.inl ⟨fr₂, m₂, .call ha horacle hw2 hexec, hd⟩
        · exact Or.inr ⟨Op.call g args results :: pre', g₂, args₂, results₂, post, fr₂, m₂, vals₂,
            by rw [hoseq]; rfl, .call ha horacle hw2 hexec, hargs, hdivo⟩
      · have hret' : ∀ w, StepsWithin p k ⟨pt, cfr, ⟨⟨f, l, pre.length⟩, fr⟩ :: k, m⟩ w →
            w.stack ≠ k := fun w hw hwk => hret ⟨w, hw, hwk⟩
        have hdeep : DivergesWithin p (⟨⟨f, l, pre.length⟩, fr⟩ :: k)
            ⟨pt, cfr, ⟨⟨f, l, pre.length⟩, fr⟩ :: k, m⟩ := by
          refine Silmaril.InfiniteTrace.coinduct
            (fun x => StepsWithin p k ⟨pt, cfr, ⟨⟨f, l, pre.length⟩, fr⟩ :: k, m⟩ x ∧
              (⟨⟨f, l, pre.length⟩, fr⟩ : Activation R) :: k <:+ x.stack) ?_
            ⟨.refl, List.suffix_refl _⟩
          rintro x ⟨hreach, hsuf⟩
          obtain ⟨y, hy, _⟩ := Silmaril.InfiniteTrace.unfold (DivergesWithin.of_stepsWithin htail hreach)
          have hysuf : (⟨⟨f, l, pre.length⟩, fr⟩ : Activation R) :: k <:+ y.stack := by
            rcases hy.1.stack_cases with heq | ⟨c, heq⟩ | ⟨c, heq⟩
            · rw [heq]; exact hsuf
            · rw [heq]; exact hsuf.trans (List.suffix_cons c x.stack)
            · rcases List.suffix_cons_iff.mp (heq ▸ hsuf) with hone | hmore
              · exact absurd (List.cons.inj hone).2.symm (hret' y (hreach.tail hy))
              · exact hmore
          exact ⟨y, ⟨hy.1, hysuf⟩, hreach.tail hy, hysuf⟩
        have hinf : Diverges p ⟨pt, cfr, [], m⟩ := by
          refine Silmaril.InfiniteTrace.of_map (R := Step p)
            (S := StepWithin p (⟨⟨f, l, pre.length⟩, fr⟩ :: k))
            (fun x => { x with stack := x.stack ++ (⟨⟨f, l, pre.length⟩, fr⟩ :: k) })
            (fun _ => True) ?_ trivial hdeep
          intro x y _ hs
          obtain ⟨σ, hσ⟩ := hs.2
          have hdrop := Step.dropStack (σ := x.stack) (τ := σ)
            (k := ⟨⟨f, l, pre.length⟩, fr⟩ :: k) hs.1 rfl hσ.symm
          exact ⟨⟨y.point, y.frame, σ, y.mem⟩, hdrop, trivial, by rw [hσ]⟩
        exact Or.inr ⟨[], g, args, results, os, fr, m, vals, rfl, .nil, ha, ⟨_, hstart, hinf⟩⟩
    | jump hf _ _ _ => exact absurd (hf.symm.trans hfetch) (by simp)
    | cond hf _ _ _ _ => exact absurd (hf.symm.trans hfetch) (by simp)
    | ret hf _ _ _ _ => exact absurd (hf.symm.trans hfetch) (by simp)

/-- **Big-step return agrees with small-step return.** A function runs from a
block to a `ret` in the big-step relation exactly when the machine, started at
that block under an arbitrary stack, reaches that `ret` with the same stack
without ever popping that stack in between. -/
theorem Func.exec_returned_iff_returns {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) {l : Label} {fr : Frame R} {m m' : Memory}
    {vs : List Word} {stack : List (Activation R)} :
    Func.Exec p.oracle fn l fr m (.returned vs m') ↔
      p.Returns ⟨⟨f, l, 0⟩, fr, stack, m⟩ vs m' := by
  constructor
  · intro h
    obtain ⟨t, hsteps, hstack, regs, hf, hv, hm⟩ := Func.Exec.stepsWithin hfn h stack
    exact ⟨t, regs, hsteps, hstack, hf, hv, hm⟩
  · rintro ⟨t, regs, hsteps, hstack, hf, hv, hm⟩
    obtain ⟨n, hn⟩ := hsteps.exists_stepsN
    have hexit : p.ExitsAt t (.returned vs m') := ⟨regs, hf, hv, hm⟩
    obtain ⟨b, hb⟩ := block?_of_stepsNWithin hn hexit
    have hbl : fn.block? l = some b := (Prog.block?_eq_of_func hfn l).symm.trans hb
    exact exec_of_stepsNWithin hfn n l 0 b fr m stack t (.returned vs m') fr m hbl hn hstack
      hexit .nil

/-- **Big-step trapping agrees with small-step trapping**, in the same sense. -/
theorem Func.exec_trapped_iff_traps {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) {l : Label} {fr : Frame R} {m m' : Memory}
    {stack : List (Activation R)} :
    Func.Exec p.oracle fn l fr m (.trapped m') ↔
      p.Traps ⟨⟨f, l, 0⟩, fr, stack, m⟩ m' := by
  constructor
  · intro h
    obtain ⟨t, hsteps, hstack, hf, hm⟩ := Func.Exec.stepsWithin hfn h stack
    exact ⟨t, hsteps, hstack, hf, hm⟩
  · rintro ⟨t, hsteps, hstack, hf, hm⟩
    obtain ⟨n, hn⟩ := hsteps.exists_stepsN
    have hexit : p.ExitsAt t (.trapped m') := ⟨hf, hm⟩
    obtain ⟨b, hb⟩ := block?_of_stepsNWithin hn hexit
    have hbl : fn.block? l = some b := (Prog.block?_eq_of_func hfn l).symm.trans hb
    exact exec_of_stepsNWithin hfn n l 0 b fr m stack t (.trapped m') fr m hbl hn hstack
      hexit .nil

/-- **Big-step divergence agrees with small-step divergence.** A function runs
forever in the big-step relation exactly when the machine, started at that block
under an arbitrary stack, runs forever without ever popping that stack. The
restriction is necessary and not a convenience: a machine run started inside a
function may well return from it and then diverge in a *caller*, which says
nothing about the callee. -/
theorem exec_diverges_iff {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) {l : Label} {fr : Frame R} {m : Memory}
    {stack : List (Activation R)} :
    Func.Diverges p.oracle p.divOracle fn ⟨l, fr, m⟩ ↔
      DivergesWithin p stack ⟨⟨f, l, 0⟩, fr, stack, m⟩ := by
  constructor
  · intro h
    exact h.divergesWithin hfn stack
  · intro h
    refine Func.Diverges.coinduct
      (fun c => DivergesWithin p stack ⟨⟨f, c.label, 0⟩, c.frame, stack, c.mem⟩) ?_ h
    rintro ⟨l', fr', m'⟩ hd
    obtain ⟨u₀, hstep₀, _⟩ := Silmaril.InfiniteTrace.unfold hd
    obtain ⟨c, hc⟩ := hstep₀.1.fetch_isSome
    obtain ⟨b, hb⟩ := Prog.block?_isSome_of_fetch hc
    have hbl : fn.block? l' = some b := (Prog.block?_eq_of_func hfn l').symm.trans hb
    rcases divergesWithin_ops_cases hb b.ops [] fr' m' (by simp) hd with
      ⟨fr₁, m₁, hexec, hd'⟩ | ⟨pre', g, args, results, post, fr₁, m₁, vals, hoseq, hexec,
        hargs, hdivo⟩
    · obtain ⟨v, hstep, htail⟩ := Silmaril.InfiniteTrace.unfold hd'
      have hfterm : p.fetch ⟨f, l', b.ops.length⟩ = some (.term b.term) := Prog.fetch_term hb
      have htr : Transition p (⟨⟨f, l', b.ops.length⟩, fr₁, stack, m₁⟩ : State R) (.running v) :=
        Transition.of_step hstep.1 (by simp)
      cases htr with
      | op hf _ => exact absurd (hfterm.symm.trans hf) (by simp)
      | call hf _ _ => exact absurd (hfterm.symm.trans hf) (by simp)
      | jump hf hv hbt hw =>
        exact .jump hbl hexec (Code.term.inj (Option.some.inj (hfterm.symm.trans hf))) hv
          ((Prog.block?_eq_of_func hfn _).symm.trans hbt) hw htail
      | cond hf hget hv hbt hw =>
        exact .cond hbl hexec (Code.term.inj (Option.some.inj (hfterm.symm.trans hf))) hget hv
          ((Prog.block?_eq_of_func hfn _).symm.trans hbt) hw htail
      | ret _ _ hstk _ _ =>
        exfalso
        obtain ⟨a₀, rest, hk₁, hk₂⟩ :
            ∃ a₀ rest, stack = a₀ :: rest ∧ stack <:+ rest := ⟨_, _, hstk, hstep.2⟩
        rw [hk₁] at hk₂
        have h₂ := hk₂.length_le
        simp only [List.length_cons] at h₂
        omega
    · exact .call hbl hoseq hexec hargs hdivo

/-- The whole-program specialisation: an outermost run returns exactly when the
entry function's big-step execution returns. Under the empty stack nothing can be
popped, so the restricted run of `Prog.Returns` is an ordinary run and its final
`ret` is `Transition.halt`.

The hypotheses `_hb` and `_hfr`, which say that `fr` is the frame the program's
entry builds for `args`, are not needed for this equivalence; they are what
`Func.exec_returned_iff_oracle` below consumes, and are kept here so that the two
statements have the same hypotheses. -/
theorem Func.exec_returned_iff_behaves {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) {b : Block R} (_hb : fn.block? fn.entry = some b)
    {args vs : List Word} {fr : Frame R} {m m' : Memory}
    (_hfr : Frame.empty.writeAll b.params args = some fr) :
    Func.Exec p.oracle fn fn.entry fr m (.returned vs m') ↔
      Behaves p ⟨⟨f, fn.entry, 0⟩, fr, [], m⟩ (.returned vs m') := by
  rw [Func.exec_returned_iff_returns hfn (stack := [])]
  constructor
  · rintro ⟨t, regs, hsteps, hstack, hf, hv, hm⟩
    exact ⟨t, stepsWithin_nil_iff.mp hsteps, step_eq_returned_iff.mpr ⟨regs, hf, hv, hstack, hm⟩⟩
  · rintro ⟨t, hsteps, hfin⟩
    obtain ⟨regs, hf, hv, hstk, hm⟩ := step_eq_returned_iff.mp hfin
    exact ⟨t, regs, stepsWithin_nil_iff.mpr hsteps, hstk, hf, hv, hm⟩

/-- **A program's call oracle is the big-step execution of its functions.** This
is `Func.exec_returned_iff_behaves` with the start state identified, which is the
form the translation to and from lambda-SSA uses: nothing about the machine, let
alone its call stack, is left in the statement. -/
theorem Func.exec_returned_iff_oracle {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) {b : Block R} (hb : fn.block? fn.entry = some b)
    {args vs : List Word} {fr : Frame R} {m m' : Memory}
    (hfr : Frame.empty.writeAll b.params args = some fr) :
    Func.Exec p.oracle fn fn.entry fr m (.returned vs m') ↔ p.oracle f args m vs m' := by
  have hstart : p.start f args m = some ⟨⟨f, fn.entry, 0⟩, fr, [], m⟩ :=
    Prog.start_eq_some_iff.mpr ⟨⟨f, fn.entry, 0⟩, fr, by simp [Prog.enter, hfn, hb, hfr], rfl⟩
  rw [Func.exec_returned_iff_behaves hfn hb hfr]
  constructor
  · intro h
    exact ⟨_, hstart, h⟩
  · rintro ⟨s, hs, hbeh⟩
    obtain rfl := Option.some.inj (hstart.symm.trans hs)
    exact hbeh

end Silmaril.Machine.RTL.SSA
