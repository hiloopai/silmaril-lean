module

public import Silmaril.Foundations.ForwardSim
public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
public import Silmaril.Semantics.CPort.Foundations.InfiniteTrace.Stutter.Defs

/-!
# Forward simulation from Lir to a target machine

The target is any transition relation `TStep : T → T → Prop`; a deterministic
partial machine `step : T → Option T` is the special case
`fun t t' => step t = some t'`. The backend supplies a state relation `Match`,
a measure on source states, and target predicates `Returned` and `Trapped`
describing what a returned or trapped whole program looks like on the target
(for example: the PC is at a sentinel return address, the return registers hold
the values and the target memory represents the Lir memory).

Obligations (`ForwardSimulation`): every running Lir step from a matched pair is
matched by one or more target steps, or by zero target steps with a strictly
smaller measure (so that the target cannot stutter forever); a returning or
trapping Lir step is matched by finitely many target steps ending in `Returned`
or `Trapped`.

`Match`, `measure` and `running` are exactly the generic `Silmaril.ForwardSim`
of `Foundations/ForwardSim.lean` (`ForwardSimulation.toSim`), from which `steps`
and `diverges` below are inherited.

Conclusions, for whole executions from a matched pair:

* `ForwardSimulation.returns`: a returning Lir execution reaches `Returned`;
* `ForwardSimulation.traps`: a trapping Lir execution reaches `Trapped`;
* `ForwardSimulation.diverges`: a diverging Lir execution has an infinite target
  path.

Nothing is claimed for Lir executions that get stuck: those are undefined
behaviour. Because the relation may be nondeterministic, these theorems say
that *some* target execution matches; for a deterministic target the unique
target execution passes through the matching state.

`CaseSimulation` states the same obligations one Lir transition kind at a time
(operation, call, jump, branch, return to caller, program return, trap), with
the facts established by `step` as hypotheses, so a backend never unfolds
`step`.

`EscapeCaseSimulation p TStep Stop` is the variant for a target that may stop
early at states satisfying `Stop` (a machine that ran out of stack, say): every
obligation may end in a stop state instead. `EscapeCaseSimulation.toCase` is a
`CaseSimulation` for `Stutter TStep Stop`, the target relation extended by
self-loops at stop states, and `EscapeCaseSimulation.returns`, `traps` and
`diverges` project the loops away: each Lir outcome is matched by a `TStep`
execution, or some `TStep` execution reaches a stop state.

`Layout` records the code layout a PC-driven backend relates program
points to; it is data for the backend's `Match` and is not used by the proofs.
-/

@[expose] public section

namespace Silmaril.Machine.Lir

open Relation

variable {R T : Type} [DecidableEq R]

/-- One source step from `s` to `s'` is matched from `t`: by at least one target
step, or by none with a strictly smaller measure. -/
def Progress (TStep : T → T → Prop) (Match : State R → T → Prop) (measure : State R → Nat)
    (s : State R) (t : T) (s' : State R) : Prop :=
  ∃ t', Match s' t' ∧ (TransGen TStep t t' ∨ (t' = t ∧ measure s' < measure s))

structure ForwardSimulation (p : Prog R) (TStep : T → T → Prop) where
  Match : State R → T → Prop
  measure : State R → Nat
  Returned : List Word → Memory → T → Prop
  Trapped : Memory → T → Prop
  running : ∀ s t s', Match s t → Step p s s' → Progress TStep Match measure s t s'
  returned : ∀ s t vs m, Match s t → step p s = .returned vs m →
    ∃ t', ReflTransGen TStep t t' ∧ Returned vs m t'
  trapped : ∀ s t m, Match s t → step p s = .trapped m →
    ∃ t', ReflTransGen TStep t t' ∧ Trapped m t'

namespace ForwardSimulation

variable {p : Prog R} {TStep : T → T → Prop} (sim : ForwardSimulation p TStep)
include sim

/-- The generic forward simulation underlying a Lir one. `Returned`/`Trapped`
are what a Lir simulation adds, because they are about Lir's *final* results,
which the kit deliberately leaves to each development. -/
def toSim : ForwardSim (Step p) TStep sim.Match where
  measure := sim.measure
  step hstep hm := by
    obtain ⟨t', hm', prog⟩ := sim.running _ _ _ hm hstep
    exact ⟨t', prog, hm'⟩

/-- Finite Lir executions are matched by finite target executions. -/
theorem steps {s s' : State R} {t : T} (hm : sim.Match s t) (h : Steps p s s') :
    ∃ t', ReflTransGen TStep t t' ∧ sim.Match s' t' :=
  sim.toSim.steps h hm

theorem returns {s : State R} {t : T} {vs : List Word} {m : Memory} (hm : sim.Match s t)
    (h : Behaves p s (.returned vs m)) : ∃ t', ReflTransGen TStep t t' ∧ sim.Returned vs m t' := by
  obtain ⟨s', hs, hf⟩ := h
  obtain ⟨t₁, h₁, m₁⟩ := sim.steps hm hs
  obtain ⟨t₂, h₂, r⟩ := sim.returned _ _ _ _ m₁ hf
  exact ⟨t₂, h₁.trans h₂, r⟩

theorem traps {s : State R} {t : T} {m : Memory} (hm : sim.Match s t)
    (h : Behaves p s (.trapped m)) : ∃ t', ReflTransGen TStep t t' ∧ sim.Trapped m t' := by
  obtain ⟨s', hs, hf⟩ := h
  obtain ⟨t₁, h₁, m₁⟩ := sim.steps hm hs
  obtain ⟨t₂, h₂, r⟩ := sim.trapped _ _ _ m₁ hf
  exact ⟨t₂, h₁.trans h₂, r⟩

/-- A diverging Lir execution has an infinite target path. The measure bounds
the number of source steps that are matched by no target step; see
`Silmaril.InfiniteTrace.of_sim`. -/
theorem diverges {s : State R} {t : T} (hm : sim.Match s t) (d : Diverges p s) :
    InfiniteTrace TStep t :=
  sim.toSim.diverges d hm

end ForwardSimulation

/-! ## Lir-to-Lir simulations

When the target is itself a Lir program, the matched outcomes are the Lir
outcomes, and every non-stuck behaviour is preserved exactly. -/

/-- The target relation of a Lir program. -/
abbrev LirTarget {P : Type} [DecidableEq P] (q : Prog P) : State P → State P → Prop := Step q

/-- A simulation into Lir whose `Returned` and `Trapped` are the Lir final
results of the target program. -/
def ForwardSimulation.IntoLir {P : Type} [DecidableEq P] {p : Prog R} {q : Prog P}
    (sim : ForwardSimulation p (LirTarget q)) : Prop :=
  (∀ vs m t, sim.Returned vs m t → step q t = .returned vs m) ∧
    (∀ m t, sim.Trapped m t → step q t = .trapped m)

theorem ForwardSimulation.behaves {P : Type} [DecidableEq P] {p : Prog R} {q : Prog P}
    (sim : ForwardSimulation p (LirTarget q)) (lir : sim.IntoLir)
    {s : State R} {t : State P} (hm : sim.Match s t) {b : Behavior}
    (hb : Behaves p s b) (hns : b ≠ .stuck) : Behaves q t b := by
  cases b with
  | returned vs m =>
    obtain ⟨t', h, r⟩ := sim.returns hm hb
    exact ⟨t', h, lir.1 _ _ _ r⟩
  | trapped m =>
    obtain ⟨t', h, r⟩ := sim.traps hm hb
    exact ⟨t', h, lir.2 _ _ r⟩
  | stuck => exact absurd rfl hns
  | diverges => exact sim.diverges hm hb

/-! ## Per-transition obligations -/

structure CaseSimulation (p : Prog R) (TStep : T → T → Prop) where
  Match : State R → T → Prop
  measure : State R → Nat
  Returned : List Word → Memory → T → Prop
  Trapped : Memory → T → Prop
  op : ∀ {s t o fr m}, Match s t → p.fetch s.point = some (.instr (.op o)) →
    o.exec s.frame s.mem = some (fr, m) →
    Progress TStep Match measure s t { s with point := s.point.next, frame := fr, mem := m }
  call : ∀ {s t f args results vals pt fr}, Match s t →
    p.fetch s.point = some (.instr (.call f args results)) →
    s.frame.readAll args = some vals → p.enter f vals = some (pt, fr) →
    Progress TStep Match measure s t ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩
  fop : ∀ {s t op d a b fr}, Match s t → p.fetch s.point = some (.instr (.fop op d a b)) →
    op.exec d a b s.frame = some fr →
    Progress TStep Match measure s t { s with point := s.point.next, frame := fr }
  jump : ∀ {s t l}, Match s t → p.fetch s.point = some (.term (.jump l)) →
    Progress TStep Match measure s t { s with point := ⟨s.point.func, l, 0⟩ }
  branch : ∀ {s t c l₁ l₂ x}, Match s t → p.fetch s.point = some (.term (.branch c l₁ l₂)) →
    s.frame.get c = some x →
    Progress TStep Match measure s t { s with point := ⟨s.point.func, if x = 0 then l₂ else l₁, 0⟩ }
  ret : ∀ {s t locs vals a rest f args results fr}, Match s t →
    p.fetch s.point = some (.term (.ret locs)) → s.frame.readAll locs = some vals →
    s.stack = a :: rest → p.fetch a.point = some (.instr (.call f args results)) →
    a.frame.writeAll results vals = some fr →
    Progress TStep Match measure s t ⟨a.point.next, fr, rest, s.mem⟩
  halt : ∀ {s t locs vals}, Match s t → p.fetch s.point = some (.term (.ret locs)) →
    s.frame.readAll locs = some vals → s.stack = [] →
    ∃ t', ReflTransGen TStep t t' ∧ Returned vals s.mem t'
  trap : ∀ {s t}, Match s t → p.fetch s.point = some (.term .trap) →
    ∃ t', ReflTransGen TStep t t' ∧ Trapped s.mem t'

def CaseSimulation.toForward {p : Prog R} {TStep : T → T → Prop} (sim : CaseSimulation p TStep) :
    ForwardSimulation p TStep where
  Match := sim.Match
  measure := sim.measure
  Returned := sim.Returned
  Trapped := sim.Trapped
  running := by
    intro s t s' hm hs
    have tr := Transition.of_step hs (by intro h; cases h)
    generalize hr : Result.running s' = r at tr
    cases tr with
    | op hf he => cases hr; exact sim.op hm hf he
    | call hf ha he => cases hr; exact sim.call hm hf ha he
    | fop hf he => cases hr; exact sim.fop hm hf he
    | jump hf => cases hr; exact sim.jump hm hf
    | branch hf hc => cases hr; exact sim.branch hm hf hc
    | ret hf hv hst ha hw => cases hr; exact sim.ret hm hf hv hst ha hw
    | halt => cases hr
    | trap => cases hr
  returned := by
    intro s t vs m hm hs
    have tr := Transition.of_step hs (by intro h; cases h)
    generalize hr : Result.returned vs m = r at tr
    cases tr with
    | halt hf hv hst => cases hr; exact sim.halt hm hf hv hst
    | _ => cases hr
  trapped := by
    intro s t m hm hs
    have tr := Transition.of_step hs (by intro h; cases h)
    generalize hr : Result.trapped m = r at tr
    cases tr with
    | trap hf => cases hr; exact sim.trap hm hf
    | _ => cases hr

/-! ## Simulations that may stop early -/

/-- The obligations of `CaseSimulation` for a target that may stop early: each
one may instead end in a state satisfying `Stop`. The target never has to move
out of a stop state; `toCase` supplies the self-loops. -/
structure EscapeCaseSimulation (p : Prog R) (TStep : T → T → Prop) (Stop : T → Prop) where
  Match : State R → T → Prop
  measure : State R → Nat
  Returned : List Word → Memory → T → Prop
  Trapped : Memory → T → Prop
  op : ∀ {s t o fr m}, Match s t → p.fetch s.point = some (.instr (.op o)) →
    o.exec s.frame s.mem = some (fr, m) →
    Progress TStep (fun s t => Match s t ∨ Stop t) measure s t
      { s with point := s.point.next, frame := fr, mem := m }
  call : ∀ {s t f args results vals pt fr}, Match s t →
    p.fetch s.point = some (.instr (.call f args results)) →
    s.frame.readAll args = some vals → p.enter f vals = some (pt, fr) →
    Progress TStep (fun s t => Match s t ∨ Stop t) measure s t
      ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩
  fop : ∀ {s t op d a b fr}, Match s t → p.fetch s.point = some (.instr (.fop op d a b)) →
    op.exec d a b s.frame = some fr →
    Progress TStep (fun s t => Match s t ∨ Stop t) measure s t
      { s with point := s.point.next, frame := fr }
  jump : ∀ {s t l}, Match s t → p.fetch s.point = some (.term (.jump l)) →
    Progress TStep (fun s t => Match s t ∨ Stop t) measure s t
      { s with point := ⟨s.point.func, l, 0⟩ }
  branch : ∀ {s t c l₁ l₂ x}, Match s t → p.fetch s.point = some (.term (.branch c l₁ l₂)) →
    s.frame.get c = some x →
    Progress TStep (fun s t => Match s t ∨ Stop t) measure s t
      { s with point := ⟨s.point.func, if x = 0 then l₂ else l₁, 0⟩ }
  ret : ∀ {s t locs vals a rest f args results fr}, Match s t →
    p.fetch s.point = some (.term (.ret locs)) → s.frame.readAll locs = some vals →
    s.stack = a :: rest → p.fetch a.point = some (.instr (.call f args results)) →
    a.frame.writeAll results vals = some fr →
    Progress TStep (fun s t => Match s t ∨ Stop t) measure s t ⟨a.point.next, fr, rest, s.mem⟩
  halt : ∀ {s t locs vals}, Match s t → p.fetch s.point = some (.term (.ret locs)) →
    s.frame.readAll locs = some vals → s.stack = [] →
    ∃ t', ReflTransGen TStep t t' ∧ (Returned vals s.mem t' ∨ Stop t')
  trap : ∀ {s t}, Match s t → p.fetch s.point = some (.term .trap) →
    ∃ t', ReflTransGen TStep t t' ∧ (Trapped s.mem t' ∨ Stop t')

namespace EscapeCaseSimulation

variable {p : Prog R} {TStep : T → T → Prop} {Stop : T → Prop}

omit [DecidableEq R] in
/-- A step into `Match ∨ Stop` along `TStep` is a step along `Stutter TStep Stop`. -/
theorem progress_lift {Match : State R → T → Prop} {measure : State R → Nat} {s s' : State R}
    {t : T} (h : Progress TStep (fun s t => Match s t ∨ Stop t) measure s t s') :
    Progress (Stutter TStep Stop) (fun s t => Match s t ∨ Stop t) measure s t s' :=
  let ⟨t', hm, hp⟩ := h
  ⟨t', hm, hp.imp_left Stutter.transGen_of⟩

omit [DecidableEq R] in
/-- From a stop state, every source step is matched by the self-loop. -/
theorem progress_stop {Match : State R → T → Prop} {measure : State R → Nat} {s s' : State R}
    {t : T} (h : Stop t) :
    Progress (Stutter TStep Stop) (fun s t => Match s t ∨ Stop t) measure s t s' :=
  ⟨t, .inr h, .inl (.single (Stutter.loop h))⟩

/-- The simulation for the target extended with self-loops at stop states. A
stop state matches every Lir state and every outcome. -/
def toCase (sim : EscapeCaseSimulation p TStep Stop) : CaseSimulation p (Stutter TStep Stop) where
  Match s t := sim.Match s t ∨ Stop t
  measure := sim.measure
  Returned vs m t := sim.Returned vs m t ∨ Stop t
  Trapped m t := sim.Trapped m t ∨ Stop t
  op hm hf he := hm.elim (fun hm => progress_lift (sim.op hm hf he)) progress_stop
  call hm hf ha he := hm.elim (fun hm => progress_lift (sim.call hm hf ha he)) progress_stop
  fop hm hf he := hm.elim (fun hm => progress_lift (sim.fop hm hf he)) progress_stop
  jump hm hf := hm.elim (fun hm => progress_lift (sim.jump hm hf)) progress_stop
  branch hm hf hx := hm.elim (fun hm => progress_lift (sim.branch hm hf hx)) progress_stop
  ret hm hf hv hs ha hw := hm.elim (fun hm => progress_lift (sim.ret hm hf hv hs ha hw)) progress_stop
  halt := by
    intro s t locs vals hm hf hv hs
    rcases hm with hm | h
    · obtain ⟨t', h, r⟩ := sim.halt hm hf hv hs
      exact ⟨t', Stutter.reflTransGen_of h, r⟩
    · exact ⟨t, .refl, .inr h⟩
  trap := by
    intro s t hm hf
    rcases hm with hm | h
    · obtain ⟨t', h, r⟩ := sim.trap hm hf
      exact ⟨t', Stutter.reflTransGen_of h, r⟩
    · exact ⟨t, .refl, .inr h⟩

variable (sim : EscapeCaseSimulation p TStep Stop)
include sim

/-- A returning Lir execution is matched by a target execution that returns
or stops. -/
theorem returns {s : State R} {t : T} (hm : sim.Match s t ∨ Stop t) {vs : List Word} {m : Memory}
    (h : Behaves p s (.returned vs m)) :
    ∃ t', ReflTransGen TStep t t' ∧ (sim.Returned vs m t' ∨ Stop t') :=
  let ⟨t', h, r⟩ := sim.toCase.toForward.returns hm h
  ⟨t', Stutter.reflTransGen_proj h, r⟩

/-- A trapping Lir execution is matched by a target execution that traps or
stops. -/
theorem traps {s : State R} {t : T} (hm : sim.Match s t ∨ Stop t) {m : Memory}
    (h : Behaves p s (.trapped m)) :
    ∃ t', ReflTransGen TStep t t' ∧ (sim.Trapped m t' ∨ Stop t') :=
  let ⟨t', h, r⟩ := sim.toCase.toForward.traps hm h
  ⟨t', Stutter.reflTransGen_proj h, r⟩

/-- A diverging Lir execution is matched by an infinite target execution, or a
target execution reaches a stop state. -/
theorem diverges {s : State R} {t : T} (hm : sim.Match s t ∨ Stop t) (h : Diverges p s) :
    InfiniteTrace TStep t ∨ ∃ t', ReflTransGen TStep t t' ∧ Stop t' :=
  Stutter.infinite (sim.toCase.toForward.diverges hm h)

end EscapeCaseSimulation

/-! ## Code layouts -/

/-- The code layout of a PC-driven target: the address of every program point
and the entry address of every function. A backend's `Match` typically states
`pc t = layout.addr s.point` and relates each suspended activation's
return address to `layout.addr a.point.next`. -/
structure Layout (Addr : Type) where
  addr : Point → Addr
  entry : FuncId → Addr

/-- The entry address of every defined function is the address of its entry
point. -/
def Layout.EntryConsistent {Addr : Type} (layout : Layout Addr) (p : Prog R) : Prop :=
  ∀ f fn, p.func? f = some fn → layout.entry f = layout.addr ⟨f, fn.entry, 0⟩

end Silmaril.Machine.Lir
