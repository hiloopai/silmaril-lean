module

public import Silmaril.X86.FnContract.Defs

/-!
# Relational x86 machines with an explicit stop (`RelIsa`)

A deterministic machine (`SegVC.Isa`) has one successor or none. A *specification* of a
machine is relational: from a state it allows a set of outcomes. This file gives the
relational machines and the two ways of comparing them.

* `Res σ`: the outcome of one step, `ok t` or `stop`. `stop` is a fault, undefined behaviour,
  an unmodelled instruction or getting stuck. Every demonic property forbids it; a loose
  specification that says nothing about a situation allows every outcome, `stop` included.
* `Views σ`: the observation of a machine state through the shared containers
  `Silmaril.X86.State` and `Silmaril.Process.Memory` (the fields of `SegVC.Isa`), plus an
  invariant `live`.
* `ExtFrame V E`: the part `ext : σ → E` of a state beyond core and memory, which `V.upd`
  keeps (an XMM file, for example). `ExtFrame.ofUnit` is the trivial one.
* `RelIsa σ`: a step *relation* `σ → Res σ → Prop` over views, which keeps `live`.
* `Progress A`: every live state has some outcome (`stop` counts).
* `Must A R Q s`: **demonic reachability**. Every run from `s` takes its steps from
  `R`-states, never stops, terminates, and reaches `Q`. Inductive, so termination is built
  in, even with infinite branching.
* `Le C A`: same views, and `C` has fewer behaviours than `A` on live states (same-state
  refinement).
* `Sim C A R`: a forward simulation of `C` by `A` along `R`, matching outcomes (`ResRel`).
* `InfoLe`: the information order on observations (abstract flags less defined).
* `ofIsa I`: a deterministic `SegVC.Isa` as a relational machine (`none` becomes `stop`).
* `RunsInR`: the relational `FnContract.RunsIn`.
* `Spec.ResultV`, `Spec.MustTotalIn`, `Spec.MustTotal` (namespace `FnContract`): the result
  of a System V call read through views, and **demonic total correctness** of a function
  spec on a relational machine.

The theorems are in `RelIsa/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.RelIsa

open Silmaril.X86 (State MState Word Byte Flags)
open Silmaril.Process (Memory)
open Silmaril.X86.SegVC (Isa)

/-- One step's outcome: a successor state, or an explicit stop. -/
inductive Res (σ : Type) where
  | ok (t : σ)
  | stop

/-- The observation of a machine state: the x86 core and the memory containers. The same
fields as `Silmaril.X86.SegVC.Isa`, plus the machine's invariant `live`. -/
structure Views (σ : Type) where
  core : σ → State
  mem : σ → Memory
  upd : σ → State → Memory → σ
  core_upd : ∀ s c m, core (upd s c m) = c
  mem_upd : ∀ s c m, mem (upd s c m) = m
  upd_self : ∀ s, upd s (core s) (mem s) = s
  live : σ → Prop

/-- **An extended-state frame**: the part `ext` of a state beyond core and memory, which
`V.upd` keeps (`upd` replaces only the core and the memory). -/
structure ExtFrame {σ : Type} (V : Views σ) (E : Type) where
  ext : σ → E
  ext_upd : ∀ s c m, ext (V.upd s c m) = ext s

/-- The trivial frame: no extension. -/
def ExtFrame.ofUnit {σ : Type} (V : Views σ) : ExtFrame V Unit where
  ext _ := ()
  ext_upd _ _ _ := rfl

end RelIsa

/-- **A relational machine**: a step relation with an explicit stop, over views. -/
structure RelIsa (σ : Type) extends RelIsa.Views σ where
  step : σ → RelIsa.Res σ → Prop
  live_step : ∀ {s t}, live s → step s (.ok t) → live t

namespace RelIsa

open Silmaril.X86 (State MState Word Byte Flags)
open Silmaril.Process (Memory)
open Silmaril.X86.SegVC (Isa)

variable {σ τ : Type}

/-- Every live state has some outcome (`stop` counts). Asked of concrete machines only. -/
def Progress (A : RelIsa σ) : Prop := ∀ s, A.live s → ∃ r, A.step s r

/-- **Demonic reachability**: every run from `s` steps only from `R`-states, never stops,
terminates, and reaches `Q`. A step case asks that `s` cannot stop and that every successor
satisfies `Must` (`Must.step_iff_outcomes` restates it as "every outcome is an `ok` whose
state satisfies `Must`"). -/
inductive Must (A : RelIsa σ) (R Q : σ → Prop) : σ → Prop
  | done {s : σ} : Q s → Must A R Q s
  | step {s : σ} : R s → ¬ A.step s .stop → (∀ t, A.step s (.ok t) → Must A R Q t) →
      Must A R Q s

/-- **Same-state refinement**: `C` has the views of `A` and fewer behaviours on live
states. -/
structure Le (C A : RelIsa σ) : Prop where
  views : C.toViews = A.toViews
  step : ∀ {s r}, C.live s → C.step s r → A.step s r

/-- Matching outcomes along a state relation. -/
def ResRel (R : τ → σ → Prop) : Res τ → Res σ → Prop
  | .ok c, .ok a => R c a
  | .stop, .stop => True
  | _, _ => False

/-- **Refinement along an abstraction** `R` (concrete `c`, abstract `a`): a forward
simulation of `C` by `A`. -/
structure Sim (C : RelIsa τ) (A : RelIsa σ) (R : τ → σ → Prop) : Prop where
  live : ∀ {c a}, R c a → C.live c → A.live a
  step : ∀ {c a r}, R c a → C.live c → C.step c r → ∃ r', A.step a r' ∧ ResRel R r r'

/-- An abstract flag is less defined than a concrete one: `none`, or equal. -/
def FlagLe (a c : Option Bool) : Prop := a = none ∨ a = c

/-- Per-flag `FlagLe`: the abstract flags `a` are less defined than the concrete `c`. -/
def FlagsLe (a c : Flags) : Prop :=
  FlagLe a.carry c.carry ∧ FlagLe a.parity c.parity ∧ FlagLe a.adjust c.adjust ∧
    FlagLe a.zero c.zero ∧ FlagLe a.sign c.sign ∧ FlagLe a.overflow c.overflow

/-- The information order on observations (concrete `c`, abstract `a`): equal registers,
`rip`, `fsBase` and memory; the abstract flags less defined. -/
def InfoLe (c a : State × Memory) : Prop :=
  c.1.regs = a.1.regs ∧ c.1.rip = a.1.rip ∧ c.1.fsBase = a.1.fsBase ∧ c.2 = a.2 ∧
    FlagsLe a.1.flags c.1.flags

/-- The views of a segment-VC machine. -/
def Views.ofIsa (I : Isa σ) : Views σ :=
  ⟨I.core, I.mem, I.upd, I.core_upd, I.mem_upd, I.upd_self, I.live⟩

/-- A deterministic machine as a relational one: `none` becomes an explicit `stop`. -/
def ofIsa (I : Isa σ) : RelIsa σ where
  toViews := Views.ofIsa I
  step s r := match I.step s with
    | some t => r = .ok t
    | none => r = .stop
  live_step {s t} hl h := by
    simp only [Views.ofIsa] at hl ⊢
    revert h
    cases e : I.step s with
    | some t' => intro h; cases h; exact I.live_step hl e
    | none => intro h; cases h

/-- **Relational runs** whose every step is taken from a state satisfying `P` (the
relational `FnContract.RunsIn`). -/
inductive RunsInR (A : RelIsa σ) (P : σ → Prop) : σ → σ → Prop
  | refl (s : σ) : RunsInR A P s s
  | step {s s' t : σ} : P s → A.step s (.ok s') → RunsInR A P s' t → RunsInR A P s t

/-- The views of the open machine state `MState` (`Open.isa`, `Open9.isa`, `Str9.isa`). -/
def Views.mstate : Views MState where
  core := MState.core
  mem := MState.memory
  upd _ c m := ⟨c, m⟩
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  live _ := True

/-- The open machine state has no extension. -/
def ExtFrame.mstate : ExtFrame Views.mstate Unit := ExtFrame.ofUnit _

end RelIsa

/-! ## Demonic total correctness of a function spec -/

namespace FnContract

open Silmaril.X86.RelIsa (Views)

variable {σ : Type}

/-- What a call of a function with spec `S` guarantees from its entry state `s` to `t`,
read through the views `V` (the fields of `Spec.Result`). -/
structure Spec.ResultV (V : Views σ) (S : Spec σ) (s t : σ) : Prop where
  /-- Only the core and the memory changed. -/
  silent : V.upd s (V.core t) (V.mem t) = t
  abi : AbiReturn (V.core s) (V.mem s) (V.core t)
  frame : (V.mem s).WritesWithin (V.mem t) (S.footprint s)
  post : S.post s t

/-- **The demonic `Spec.TotalIn`**: from every live System V entry `s` of `S`, every run of
`A` takes its steps from states satisfying `R s`, never stops, terminates, and reaches a
result state of `S` (read through the views of `A`). -/
def Spec.MustTotalIn (A : RelIsa σ) (S : Spec σ) (R : σ → σ → Prop) : Prop :=
  ∀ s, A.live s → AbiEntry (A.core s) (A.mem s) → S.entry s →
    RelIsa.Must A (R s) (S.ResultV A.toViews s) s

/-- **The demonic `Spec.Total`**: no run predicate. A run may pass through an earlier
return of the call before it reaches the result. -/
abbrev Spec.MustTotal (A : RelIsa σ) (S : Spec σ) : Prop := S.MustTotalIn A fun _ _ => True

end FnContract

end Silmaril.X86
