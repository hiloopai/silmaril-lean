module

public import Silmaril.Process.CLI.Process
public import Silmaril.Process.CLI.Input

/-! # Statements about CLI programs, and their transfer between models

A `Model` is a point of the model lattice: an instruction-set model with its
ABI, an environment, how the environment starts for an input, and the loader
(how an image and an input give an initial core and memory). A `CliSpec` says
which finite traces and which exits are allowed for an input. Four statement
forms are kept apart, as LPS keeps `strong_universal_T`, `must_exit_with` and
`halts_allowed_T` apart:

* `Agrees`: safety. Every finite run's events satisfy `prefixOk`, and an exit
  satisfies `exitOk`. Says nothing about termination.
* `Covered`: every stop is an exit: no crash and no unmodeled configuration.
* `Halts domain`: no infinite run of completed steps, for inputs in `domain`
  (finite stdin, for a filter). Blocking in a call is allowed.
* `Bounded domain budget perRefusal`: every run takes at most `budget input`
  steps plus `perRefusal` per environment refusal; with `perRefusal = 0` it
  implies `Halts` (`Bounded.halts`), and in a never-refusing environment the
  allowance is void (`Bounded.absolute`).

All four are downward closed in the model order and upward closed in the spec
order (`Agrees.mono`, `Covered.mono`, `Halts.mono`, `Bounded.mono`,
`Agrees.weaken`). This is the "model-agnostic" interface: a proof needs only
the highest model at which it goes through, and is reused at every model below.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall

structure Model where
  isa : Isa
  env : Env
  envInit : ProcInput → Memory → env.State → Prop
  load : Image → ProcInput → isa.Core → Memory → Prop

namespace Model

def Init (M : Model) (image : Image) (input : ProcInput) (x : PState M.isa M.env) : Prop :=
  ∃ m, M.load image input x.core m ∧ M.envInit input m x.env

structure Sim (M N : Model) where
  isa : Isa.Sim M.isa N.isa
  env : Env.Sim M.env N.env
  envInit : ∀ {input m s}, M.envInit input m s → ∃ t, N.envInit input m t ∧ env.rel s t
  load : ∀ {image input c m}, M.load image input c m → ∃ d, N.load image input d m ∧ isa.rel c d

def Le (M N : Model) : Prop := Nonempty (Sim M N)

@[inherit_doc] scoped infix:50 " ≼ " => Le

def Sim.id (M : Model) : Sim M M where
  isa := Isa.Sim.id M.isa
  env := Env.Sim.id M.env
  envInit {_ _ s} init := ⟨s, init, rfl⟩
  load {_ _ c _} load := ⟨c, load, rfl⟩

def Sim.comp {M N P : Model} (first : Sim M N) (second : Sim N P) : Sim M P where
  isa := first.isa.comp second.isa
  env := first.env.comp second.env
  envInit init := by
    obtain ⟨t, init', r₁⟩ := first.envInit init
    obtain ⟨u, init'', r₂⟩ := second.envInit init'
    exact ⟨u, init'', t, r₁, r₂⟩
  load load := by
    obtain ⟨d, load', r₁⟩ := first.load load
    obtain ⟨e, load'', r₂⟩ := second.load load'
    exact ⟨e, load'', d, r₁, r₂⟩

theorem le_refl (M : Model) : M.Le M := ⟨Sim.id M⟩

theorem le_trans {M N P : Model} (h₁ : M.Le N) (h₂ : N.Le P) : M.Le P :=
  let ⟨s₁⟩ := h₁
  let ⟨s₂⟩ := h₂
  ⟨s₁.comp s₂⟩

theorem Sim.init {M N : Model} (sim : Sim M N) {image : Image} {input : ProcInput}
    {x : PState M.isa M.env} (init : M.Init image input x) :
    ∃ y, N.Init image input y ∧ Proc.Related sim.isa sim.env x y := by
  obtain ⟨m, load, envInit⟩ := init
  obtain ⟨d, load', rc⟩ := sim.load load
  obtain ⟨t, envInit', re⟩ := sim.envInit envInit
  exact ⟨⟨d, t⟩, ⟨m, load', envInit'⟩, rc, re⟩

end Model

structure CliSpec where
  prefixOk : ProcInput → List Event → Prop
  exitOk : ProcInput → List Event → Nat → Prop

/-- `S ≤ T`: `S` is the stronger specification. -/
def CliSpec.Le (S T : CliSpec) : Prop :=
  (∀ input events, S.prefixOk input events → T.prefixOk input events) ∧
  (∀ input events status, S.exitOk input events status → T.exitOk input events status)

variable (M : Model) (image : Image)

def Agrees (S : CliSpec) : Prop :=
  ∀ input x, input.Valid → M.Init image input x → ∀ events y, Proc.Runs M.isa M.env x events y →
    S.prefixOk input events ∧
      ∀ status, Proc.Stop M.isa M.env y (.exited status) → S.exitOk input events status

def Covered : Prop :=
  ∀ input x, input.Valid → M.Init image input x → ∀ events y, Proc.Runs M.isa M.env x events y →
    ∀ o, Proc.Stop M.isa M.env y o → ∃ status, o = .exited status

/-- No infinite run on the inputs of `domain` (for a filter: finite stdin; a
filter that reads an infinite stream legitimately runs forever). -/
def Halts (domain : ProcInput → Prop) : Prop :=
  ∀ input x, input.Valid → domain input → M.Init image input x → ¬ Proc.Diverges M.isa M.env x

/-- Runs counting completed steps. -/
inductive Proc.RunsN {I : Isa} {E : Env} : Nat → PState I E → List Event → PState I E → Prop
  | refl (x) : RunsN 0 x [] x
  | cons {n x y z first rest} : Proc.Step I E x first y → RunsN n y rest z →
      RunsN (n + 1) x (first ++ rest) z

/-- Every run on an input of `domain` takes at most `budget input` steps plus
`perRefusal` steps for each refusal by the environment (`CLI.Refused`). With
`perRefusal = 0` this is an absolute budget. The refusal term is what makes a
budget provable under `Env.linux`, where a program that retries `EINTR` can
be refused forever. -/
def Bounded (domain : ProcInput → Prop) (budget : ProcInput → Nat) (perRefusal : Nat) : Prop :=
  ∀ input x, input.Valid → domain input → M.Init image input x → ∀ n events y,
    Proc.RunsN (I := M.isa) (E := M.env) n x events y →
      n ≤ budget input + perRefusal * (events.filter fun e => decide e.IsRefusal).length

variable {M image}

theorem Agrees.weaken {S T : CliSpec} (h : Agrees M image S) (le : S.Le T) : Agrees M image T := by
  intro input x valid init events y run
  obtain ⟨ok, exits⟩ := h input x valid init events y run
  exact ⟨le.1 _ _ ok, fun status stop => le.2 _ _ _ (exits status stop)⟩

theorem Agrees.mono {N : Model} {S : CliSpec} (le : M.Le N) (h : Agrees N image S) :
    Agrees M image S := by
  obtain ⟨sim⟩ := le
  intro input x valid init events y run
  obtain ⟨x', init', related⟩ := sim.init init
  obtain ⟨y', run', related'⟩ := (Proc.refines sim.isa sim.env).runs run related
  obtain ⟨ok, exits⟩ := h input x' valid init' events y' run'
  exact ⟨ok, fun status stop => exits status (Proc.stop_sim sim.isa sim.env related' stop)⟩

theorem Covered.mono {N : Model} (le : M.Le N) (h : Covered N image) : Covered M image := by
  obtain ⟨sim⟩ := le
  intro input x valid init events y run o stop
  obtain ⟨x', init', related⟩ := sim.init init
  obtain ⟨y', run', related'⟩ := (Proc.refines sim.isa sim.env).runs run related
  exact h input x' valid init' events y' run' o (Proc.stop_sim sim.isa sim.env related' stop)

theorem Halts.mono {N : Model} {domain : ProcInput → Prop} (le : M.Le N)
    (h : Halts N image domain) : Halts M image domain := by
  obtain ⟨sim⟩ := le
  intro input x valid inDomain init diverges
  obtain ⟨x', init', related⟩ := sim.init init
  exact h input x' valid inDomain init' (Proc.diverges_sim sim.isa sim.env related diverges)

theorem Proc.RunsN.sim {I J : Isa} {E F : Env} (si : Isa.Sim I J) (se : Env.Sim E F)
    {n : Nat} {x y : PState I E} {x' : PState J F} {events : List Event}
    (run : Proc.RunsN n x events y) (related : Proc.Related si se x x') :
    ∃ y', Proc.RunsN n x' events y' := by
  induction run generalizing x' with
  | refl => exact ⟨x', .refl x'⟩
  | cons step _ ih =>
    obtain ⟨z, step', related'⟩ := Proc.step_sim si se related step
    obtain ⟨y', rest⟩ := ih related'
    exact ⟨y', .cons step' rest⟩

theorem Bounded.mono {N : Model} {domain : ProcInput → Prop} {budget : ProcInput → Nat}
    {perRefusal : Nat} (le : M.Le N) (h : Bounded N image domain budget perRefusal) :
    Bounded M image domain budget perRefusal := by
  obtain ⟨sim⟩ := le
  intro input x valid inDomain init n events y run
  obtain ⟨x', init', related⟩ := sim.init init
  obtain ⟨y', run'⟩ := run.sim sim.isa sim.env related
  exact h input x' valid inDomain init' n events y' run'

/-- An absolute step budget rules out infinite runs. -/
theorem Bounded.halts {domain : ProcInput → Prop} {budget : ProcInput → Nat}
    (h : Bounded M image domain budget 0) : Halts M image domain := by
  intro input x valid inDomain init diverges
  obtain ⟨trace, first, next⟩ := diverges
  have runs : ∀ k j, ∃ events,
      Proc.RunsN (I := M.isa) (E := M.env) k (trace j) events (trace (j + k)) := by
    intro k
    induction k with
    | zero => exact fun j => ⟨[], Proc.RunsN.refl _⟩
    | succ k ih =>
      intro j
      obtain ⟨events, run⟩ := ih (j + 1)
      obtain ⟨first, step⟩ := next j
      rw [show j + 1 + k = j + (k + 1) by omega] at run
      exact ⟨_, .cons step run⟩
  obtain ⟨events, run⟩ := runs (budget input + 1) 0
  rw [first] at run
  have := h input x valid inDomain init _ events _ run
  simp only [Nat.zero_mul, Nat.add_zero] at this
  omega

theorem Proc.RunsN.runs {I : Isa} {E : Env} {n : Nat} {x y : PState I E} {events : List Event}
    (run : Proc.RunsN n x events y) : Proc.Runs I E x events y := by
  induction run with
  | refl => exact .refl _
  | cons step _ ih => exact .cons step ih

/-- In an environment that never refuses, the refusal allowance is void. -/
theorem Bounded.absolute {domain : ProcInput → Prop} {budget : ProcInput → Nat} {perRefusal : Nat}
    (h : Bounded M image domain budget perRefusal)
    (noRefusal : M.env.EventsSatisfy fun e => ¬ e.IsRefusal) :
    Bounded M image domain budget 0 := by
  intro input x valid inDomain init n events y run
  have bound := h input x valid inDomain init n events y run
  have none : (events.filter fun e => decide e.IsRefusal) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e member
    obtain ⟨s, q, r, s', step⟩ := Proc.runs_events_admitted run.runs e member
    simpa using noRefusal s q e r s' step
  rw [none] at bound
  simpa using bound

end Silmaril.Process.CLI
