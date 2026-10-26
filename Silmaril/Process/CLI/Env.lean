module

public import Silmaril.Process.CLI.Observation

/-! # Syscall environments and their refinement order

An `Env` is everything outside the user-mode thread: an abstract state that
contains the process memory, and a relation saying which completed system
calls it admits. It is a structure rather than the concrete
`Process.Syscall.State`, so that a program proof can be stated against any
environment with the laws it uses, and a more faithful Linux model (signals,
files, the LPS-style per-call specifications) can be added later without
touching the proof.

## The order

`E ≼ F` (`Env.Le`) holds when a simulation maps every admitted call of `E` to
one of `F` with the same request, event, reply and memory. A smaller
environment admits fewer behaviours, so every *unary safety* statement about a
program (all finite traces allowed, no unmodeled state, no divergence, a
budget) transfers from `F` down to `E` (`CLI.Spec`). Relational statements
(equivalence of two programs' behaviour sets) do not transfer; LPS makes the
same observation for its `SPURIOUS_CFG` families (`Equivalence.v`,
`run_scfg_sub_traces`).

Reading the order as trust: a proof at `F` is used for real Linux through the
assumption *Linux ≼ F*. The higher `F`, the weaker that assumption. A proof
should therefore be done at the highest environment for which it goes through,
and the points below are the ladder:

  `ideal ≼ reliable ≼ eintrClean ≼ linux`

* `linux`: `Process.Syscall.Step`, with short reads and writes, zero writes and
  any errno. A failed read may consume and clobber its buffer.
* `eintrClean`: as `linux`, except that `EINTR` from `read` consumes nothing
  and leaves memory unchanged. This is what Linux guarantees (a read that has
  transferred data returns the count, not `EINTR`), and is the least a
  program that retries on `EINTR` needs.
* `reliable`: no error returns and no zero-byte writes; short transfers remain.
* `ideal`: reads return as much as is requested and available, writes accept
  everything.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall

/-- An environment: abstract state with a memory lens and the admitted calls. -/
structure Env where
  State : Type
  memory : State → Memory
  withMemory : State → Memory → State
  /-- `some status` once the process has exited. -/
  exited : State → Option Nat
  step : State → Request → Event → Reply → State → Prop

namespace Env

/-- The lens laws the process semantics relies on. -/
structure Lawful (E : Env) : Prop where
  memory_withMemory : ∀ s m, E.memory (E.withMemory s m) = m
  exited_withMemory : ∀ s m, E.exited (E.withMemory s m) = E.exited s
  step_running : ∀ {s q ev r s'}, E.step s q ev r s' → E.exited s = none

/-- A simulation of `E` by `F`: same requests, events, replies, memory and exit. -/
structure Sim (E F : Env) where
  rel : E.State → F.State → Prop
  memory : ∀ {s t}, rel s t → E.memory s = F.memory t
  exited : ∀ {s t}, rel s t → E.exited s = F.exited t
  withMemory : ∀ {s t} (m : Memory), rel s t → rel (E.withMemory s m) (F.withMemory t m)
  step : ∀ {s t q ev r s'}, rel s t → E.step s q ev r s' → ∃ t', F.step t q ev r t' ∧ rel s' t'

/-- `E ≼ F`: every behaviour `E` admits, `F` admits. -/
def Le (E F : Env) : Prop := Nonempty (Sim E F)

@[inherit_doc] scoped infix:50 " ≼ " => Le

def Sim.id (E : Env) : Sim E E where
  rel := Eq
  memory h := by rw [h]
  exited h := by rw [h]
  withMemory m h := by rw [h]
  step {s t q ev r s'} h step := ⟨s', h ▸ step, rfl⟩

def Sim.comp {E F G : Env} (first : Sim E F) (second : Sim F G) : Sim E G where
  rel s u := ∃ t, first.rel s t ∧ second.rel t u
  memory := fun ⟨_, h₁, h₂⟩ => (first.memory h₁).trans (second.memory h₂)
  exited := fun ⟨_, h₁, h₂⟩ => (first.exited h₁).trans (second.exited h₂)
  withMemory m := fun ⟨t, h₁, h₂⟩ => ⟨_, first.withMemory m h₁, second.withMemory m h₂⟩
  step := fun ⟨_, h₁, h₂⟩ step => by
    obtain ⟨t', step', r₁⟩ := first.step h₁ step
    obtain ⟨u', step'', r₂⟩ := second.step h₂ step'
    exact ⟨u', step'', _, r₁, r₂⟩

theorem le_refl (E : Env) : E ≼ E := ⟨Sim.id E⟩

theorem le_trans {E F G : Env} (h₁ : E ≼ F) (h₂ : F ≼ G) : E ≼ G :=
  let ⟨s₁⟩ := h₁
  let ⟨s₂⟩ := h₂
  ⟨s₁.comp s₂⟩

/-- Keep only the admitted calls satisfying `keep`. -/
def restrict (E : Env) (keep : E.State → Request → Event → Reply → E.State → Prop) : Env :=
  { E with step := fun s q ev r s' => E.step s q ev r s' ∧ keep s q ev r s' }

/-- The inclusion of a restriction, as a simulation (the identity relation). -/
def restrictSim (E : Env) (keep : E.State → Request → Event → Reply → E.State → Prop) :
    Sim (E.restrict keep) E where
  rel := Eq
  memory h := by rw [h]; rfl
  exited h := by rw [h]; rfl
  withMemory m h := by rw [h]; rfl
  step {s t q ev r s'} h step := ⟨s', h ▸ step.1, rfl⟩

theorem restrict_le (E : Env) (keep : E.State → Request → Event → Reply → E.State → Prop) :
    E.restrict keep ≼ E :=
  ⟨restrictSim E keep⟩

/-- A stronger filter gives a smaller environment. -/
def restrictMonoSim (E : Env) {keep keep' : E.State → Request → Event → Reply → E.State → Prop}
    (h : ∀ s q ev r s', E.step s q ev r s' → keep s q ev r s' → keep' s q ev r s') :
    Sim (E.restrict keep) (E.restrict keep') where
  rel := Eq
  memory h := by rw [h]; rfl
  exited h := by rw [h]; rfl
  withMemory m h := by rw [h]; rfl
  step {s t q ev r s'} e step := ⟨s', e ▸ ⟨step.1, h _ _ _ _ _ step.1 step.2⟩, rfl⟩

theorem restrict_mono (E : Env) {keep keep' : E.State → Request → Event → Reply → E.State → Prop}
    (h : ∀ s q ev r s', E.step s q ev r s' → keep s q ev r s' → keep' s q ev r s') :
    E.restrict keep ≼ E.restrict keep' :=
  ⟨restrictMonoSim E h⟩

theorem Lawful.restrict {E : Env} (lawful : E.Lawful)
    (keep : E.State → Request → Event → Reply → E.State → Prop) : (E.restrict keep).Lawful where
  memory_withMemory := lawful.memory_withMemory
  exited_withMemory := lawful.exited_withMemory
  step_running step := lawful.step_running step.1

/-- Every request of a running process gets some completed reply: the
environment never blocks forever. A liveness assumption, used only by
statements about progress; it is not inherited by smaller environments. -/
def Answers (E : Env) : Prop :=
  ∀ s q, E.exited s = none → ∃ ev r s', E.step s q ev r s'

/-- Every event an environment admits satisfies `P`. -/
def EventsSatisfy (E : Env) (P : Event → Prop) : Prop :=
  ∀ s q ev r s', E.step s q ev r s' → P ev

theorem EventsSatisfy.mono {E F : Env} {P : Event → Prop} (le : E ≼ F)
    (h : F.EventsSatisfy P) : ∀ s t q ev r s', le.some.rel s t → E.step s q ev r s' → P ev := by
  intro s t q ev r s' related step
  obtain ⟨t', step', _⟩ := le.some.step related step
  exact h _ _ _ _ _ step'

/-! ## The Linux ladder over `Process.Syscall.State` -/

/-- The explicit Linux read/write/exit contract (`Process.Syscall.Step`). -/
def linux : Env where
  State := Syscall.State
  memory := Syscall.State.memory
  withMemory s m := { s with memory := m }
  exited := Syscall.State.exited
  step := Syscall.Step

theorem linux_lawful : linux.Lawful where
  memory_withMemory _ _ := rfl
  exited_withMemory _ _ := rfl
  step_running step := Step.was_running step

/-- The errno of an interrupted call. -/
def eintr : Errno := ⟨4, by decide, by decide⟩

/-- `EINTR` from `read` transfers nothing. -/
def EintrClean (s : Syscall.State) (q : Request) (ev : Event) (_ : Reply)
    (s' : Syscall.State) : Prop :=
  ∀ fd address count, q = .read fd address count → ev = .error q eintr → s' = s

def eintrClean : Env := linux.restrict EintrClean

/-- No error returns and no zero-byte writes. -/
def Reliable (_ : Syscall.State) (_ : Request) (ev : Event) (_ : Reply)
    (_ : Syscall.State) : Prop := ¬ ev.IsRefusal

def reliable : Env := linux.restrict fun s q ev r s' => EintrClean s q ev r s' ∧ Reliable s q ev r s'

/-- Full transfers: a read returns `min count available` bytes (all of them up
to EOF), a write accepts every byte. -/
def Full (s : Syscall.State) (q : Request) (ev : Event) (_ : Reply) (_ : Syscall.State) : Prop :=
  match q, ev with
  | .read fd _ count, .read _ bytes =>
      ∀ descriptor, s.descriptors fd = some descriptor →
        bytes.length = count ∨ descriptor.input.byteAt (descriptor.cursor + bytes.length) = none
  | .write _ _ count, .write _ bytes => bytes.length = count
  | _, _ => True

def ideal : Env :=
  linux.restrict fun s q ev r s' => (EintrClean s q ev r s' ∧ Reliable s q ev r s') ∧ Full s q ev r s'

theorem ideal_le_reliable : ideal ≼ reliable :=
  restrict_mono linux fun _ _ _ _ _ _ h => h.1

theorem reliable_le_eintrClean : reliable ≼ eintrClean :=
  restrict_mono linux fun _ _ _ _ _ _ h => h.1

theorem eintrClean_le_linux : eintrClean ≼ linux := restrict_le linux _

theorem ideal_le_linux : ideal ≼ linux :=
  le_trans ideal_le_reliable (le_trans reliable_le_eintrClean eintrClean_le_linux)

theorem reliable_noRefusal : reliable.EventsSatisfy fun ev => ¬ ev.IsRefusal :=
  fun _ _ _ _ _ step => step.2.2

end Env

end Silmaril.Process.CLI
