module

public import Silmaril.X86.SegVC
public import Silmaril.Machine.X86.FnContract.Defs
public import Silmaril.Machine.X86.Safe.Defs
public import Silmaril.Machine.X86.Sse9.Defs

/-!
# Relational x86 machines with an explicit stop (`RelIsa`)

(an earlier design note §2.1–§2.3, amended by
-2 and AD-15).

* `Res σ`: the outcome of one step, `ok t` or `stop`. `stop` is a fault, undefined
  behaviour, an unmodelled instruction or getting stuck. Every demonic property forbids it;
  a loose spec that leaves a situation unspecified allows every outcome, `stop` included.
* `Views σ`: the observation of a machine state through the shared containers
  `Silmaril.X86.State` and `Silmaril.Process.Memory` (the fields of `SegVC.Isa`), never
  through a particular machine's state type.
* `ExtFrame V E`: an extension `ext : σ → E` that `V.upd` keeps (AD-15). Instances for the
  open `MState` (`E := Unit`) and `Sse9.XState` (the XMM file) here; the one for
  `Silmaril.X86.Features.MState` (`zmm × k × mxcsr × x87`) is in `RelIsa/Features/Defs.lean`,
  so that this core does not import `Silmaril.X86.Features`.
* `RelIsa σ`: a step *relation* `σ → Res σ → Prop` over views, with a `live` invariant.
* `Must A R Q s`: **demonic reachability**. Every run from `s` takes its steps from
  `R`-states, never stops, terminates, and reaches `Q`. Inductive, so termination is built
  in, even with infinite branching.
* `Le C A`: same views, and `C` has fewer behaviours than `A` on live states.
* `Sim C A R`: a forward simulation of `C` by `A` along `R`, matching outcomes (`ResRel`).
* `InfoLe`: the information order on observations (abstract flags less defined).
* `ofIsa I`: a deterministic `SegVC.Isa` as a relational machine (`none` ↦ `stop`).
* `loosen I P`: where `P` holds and `I` takes a step, exactly that step; everywhere else
  every outcome. `RunsInR`: the relational `FnContract.RunsIn`.

The theorems are in `RelIsa/Thms.lean` (proofs under `Silmaril/Proofs/Machine/X86/RelIsa/`).
-/

@[expose] public section

namespace Silmaril.Machine.X86.RelIsa

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

/-- **An extended-state frame** (AD-15): the part `ext` of a state beyond core and memory,
which `V.upd` keeps (`upd` replaces only the core and the memory). -/
structure ExtFrame {σ : Type} (V : Views σ) (E : Type) where
  ext : σ → E
  ext_upd : ∀ s c m, ext (V.upd s c m) = ext s

/-- The trivial frame: no extension. -/
def ExtFrame.ofUnit {σ : Type} (V : Views σ) : ExtFrame V Unit where
  ext _ := ()
  ext_upd _ _ _ := rfl

/-- **A relational machine**: a step relation with an explicit stop, over views. -/
structure _root_.Silmaril.Machine.X86.RelIsa (σ : Type) extends Views σ where
  step : σ → Res σ → Prop
  live_step : ∀ {s t}, live s → step s (.ok t) → live t

variable {σ τ : Type}

/-- Every live state has some outcome (`stop` counts). Required of concrete machines only. -/
def Progress (A : RelIsa σ) : Prop := ∀ s, A.live s → ∃ r, A.step s r

/-- **Demonic reachability**: every run from `s` steps only from `R`-states, never stops,
terminates, and reaches `Q`. A step case asks that `s` cannot stop and that every successor
satisfies `Must` (`Must.step_iff_outcomes` in `Thms` restates it as "every outcome is an `ok` whose
state satisfies `Must`"). -/
inductive Must (A : RelIsa σ) (R Q : σ → Prop) : σ → Prop
  | done {s : σ} : Q s → Must A R Q s
  | step {s : σ} : R s → ¬ A.step s .stop → (∀ t, A.step s (.ok t) → Must A R Q t) →
      Must A R Q s

/-- Same-state refinement: `C` has the views of `A` and fewer behaviours on live states. -/
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

/-- A model flag is less defined than a concrete one: `none`, or equal. -/
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

/-- **Loosening**: where `P` holds and `I` takes a step, exactly that step. Everywhere else
(`I` fails, or `P` fails) every outcome is allowed, `stop` included, subject only to the
machine invariant: a successor of a loose step is `live`. (`live` is part of the views, so
every `C` with `Le C (loosen I P)` keeps it anyway; for `Open.isa`, `Open9.isa` and
`Sse9.isa` it is `True`.) -/
def loosen (I : Isa σ) (P : σ → Prop) : RelIsa σ where
  toViews := Views.ofIsa I
  step s r := (∀ t, P s → I.step s = some t → r = .ok t) ∧ ∀ t, r = .ok t → I.live t
  live_step {_ t} _ h := h.2 t rfl

/-- **Relational runs** whose every step is taken from a state satisfying `P` (the
relational `FnContract.RunsIn`). -/
inductive RunsInR (A : RelIsa σ) (P : σ → Prop) : σ → σ → Prop
  | refl (s : σ) : RunsInR A P s s
  | step {s s' t : σ} : P s → A.step s (.ok s') → RunsInR A P s' t → RunsInR A P s t

/-! ## Views and extension frames of the existing machines -/

/-- The views of the open machine state `MState` (`Open.isa`, `Open9.isa`). -/
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

/-- The views of the XMM machine state `Sse9.XState` (`Sse9.isa`). -/
def Views.xstate : Views Silmaril.Machine.X86.Sse9.XState where
  core x := x.m.core
  mem x := x.m.memory
  upd x c m := ⟨⟨c, m⟩, x.xmm⟩
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  live _ := True

/-- The XMM file is the extension of `Sse9.XState`. -/
def ExtFrame.xstate : ExtFrame Views.xstate Silmaril.Machine.X86.Sse9.XFile where
  ext x := x.xmm
  ext_upd _ _ _ := rfl

end Silmaril.Machine.X86.RelIsa
