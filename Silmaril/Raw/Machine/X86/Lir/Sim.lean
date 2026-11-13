module

public import Silmaril.Machine.X86.Lir.Return.Defs

/-!
# The forward simulation from Lir to the machine

The target relation `Env.TStep` is one retiring machine step (`RStep`), or the
self-loop of a machine stopped at the UD2 of a stack-limit check
(`Env.Overflow`). The loop lets the stack-overflow stop take part in the
simulation of an unbounded Lir stack: a Lir state is matched either by a
machine state of `Env.Body`, or by a machine stopped at a stack-limit check.
Since an overflow state traps, its only `TStep` is the loop, and
`tsteps_rsteps`/`tdiverges` translate `TStep` executions back to executions of
the machine that either follow the Lir execution or stop at the stack limit.

`Env.simulation` is a `Lir.CaseSimulation` with `Returned`
(`Env.Final` after the final RET, or overflow) and `Trapped` (UD2 with the
linear memory represented, or overflow).
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

set_option linter.unusedSectionVars false

namespace Env

variable {P : Type} (E : Env P) [DecidableEq P]

/-- A retiring step, or the loop of a machine stopped at a stack-limit check. -/
def TStep (t t' : MState) : Prop := RStep E.exit t t' ∨ (E.Overflow t ∧ t' = t)

/-- The state relation of the simulation. -/
def Match (s : Lir.State P) (t : MState) : Prop := (∃ B, E.Body s t B) ∨ E.Overflow t

def Returned (vals : List Word) (lm : Lir.Memory) (t : MState) : Prop :=
  (∃ final, Ext.step E.exit t = .returned final ∧ E.Final vals lm final) ∨ E.Overflow t

def Trapped (lm : Lir.Memory) (t : MState) : Prop :=
  (Ext.step E.exit t = .trapped ∧ MemRel E.S lm t.memory) ∨ E.Overflow t

theorem rstep_tstep : RStep E.exit ≤ E.TStep := fun _ _ h => .inl h

theorem overflow_progress {s s' : Lir.State P} {t : MState} (h : E.Overflow t) :
    Lir.Progress E.TStep E.Match (fun _ => 0) s t s' :=
  ⟨t, .inr h, .inl (TransGen.single (.inr ⟨h, rfl⟩))⟩

theorem body_progress {s s' : Lir.State P} {t : MState}
    (h : ∃ t', TransGen (RStep E.exit) t t' ∧ ∃ B', E.Body s' t' B') :
    Lir.Progress E.TStep E.Match (fun _ => 0) s t s' := by
  obtain ⟨t', st, B', hb⟩ := h
  exact ⟨t', .inl ⟨B', hb⟩, .inl (TransGen.mono E.rstep_tstep _ _ st)⟩

/-- The simulation of a compiled program. -/
def simulation (hok : E.Ok) : Lir.CaseSimulation E.p E.TStep where
  Match := E.Match
  measure := fun _ => 0
  Returned := E.Returned
  Trapped := E.Trapped
  op := by
    intro s t o fr m hm hf he
    rcases hm with ⟨B, hm⟩ | hov
    · obtain ⟨t', st, hb⟩ := E.sim_op hok hm hf he
      exact E.body_progress ⟨t', st, B, hb⟩
    · exact E.overflow_progress hov
  call := by
    intro s t f args results vals pt fr hm hf ha he
    rcases hm with ⟨B, hm⟩ | hov
    · obtain ⟨t₁, st₁, hent⟩ := E.sim_callSite hok hm hf ha
      obtain ⟨fn, hfn, hfr, rfl⟩ := E.enter_eq he
      obtain ⟨t₂, st₂, h₂⟩ := E.sim_entry hok hfn hent hfr
      rcases h₂ with hov | hb
      · exact ⟨t₂, .inr hov, .inl (TransGen.mono E.rstep_tstep _ _ (st₁.trans st₂))⟩
      · exact E.body_progress ⟨t₂, st₁.trans st₂, _, hb⟩
    · exact E.overflow_progress hov
  fop := by
    intro s t op d x y fr hm hf he
    rcases hm with ⟨B, hm⟩ | hov
    · exact absurd hf (E.fetch_ne_fop hok)
    · exact E.overflow_progress hov
  jump := by
    intro s t l hm hf
    rcases hm with ⟨B, hm⟩ | hov
    · obtain ⟨t', st, hb⟩ := E.sim_jump hok hm hf
      exact E.body_progress ⟨t', st, B, hb⟩
    · exact E.overflow_progress hov
  branch := by
    intro s t c l₁ l₂ x hm hf hx
    rcases hm with ⟨B, hm⟩ | hov
    · obtain ⟨t', st, hb⟩ := E.sim_branch hok hm hf hx
      exact E.body_progress ⟨t', st, B, hb⟩
    · exact E.overflow_progress hov
  ret := by
    intro s t locs vals a rest f args results fr hm hf hv hst ha hw
    rcases hm with ⟨B, hm⟩ | hov
    · obtain ⟨t', st, hb⟩ := E.sim_ret hok hm hf hv hst ha hw
      exact E.body_progress ⟨t', st, _, hb⟩
    · exact E.overflow_progress hov
  halt := by
    intro s t locs vals hm hf hv hst
    rcases hm with ⟨B, hm⟩ | hov
    · obtain ⟨t', st, fin⟩ := E.sim_halt hok hm hf hv hst
      exact ⟨t', ReflTransGen.mono E.rstep_tstep _ _ st, .inl fin⟩
    · exact ⟨t, .refl, .inr hov⟩
  trap := by
    intro s t hm hf
    rcases hm with ⟨B, hm⟩ | hov
    · exact ⟨t, .refl, .inl ⟨E.sim_trap hok hm hf, hm.mem⟩⟩
    · exact ⟨t, .refl, .inr hov⟩

/-! ## Back to machine executions -/

theorem overflow_not_rstep {t t' : MState} (h : E.Overflow t) : ¬ RStep E.exit t t' := by
  intro hr
  unfold RStep at hr
  rw [h.1] at hr
  cases hr

/-- A finite `TStep` execution is a machine execution: overflow loops do not
move. -/
theorem tsteps_rsteps {t t' : MState} (h : ReflTransGen E.TStep t t') :
    ReflTransGen (RStep E.exit) t t' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with hs | ⟨_, rfl⟩
    · exact ih.tail hs
    · exact ih

/-- An infinite `TStep` execution is an infinite machine execution, or a finite
machine execution that stops at a stack-limit check. -/
theorem tdiverges {t : MState} (h : InfiniteTrace E.TStep t) :
    InfiniteTrace (RStep E.exit) t ∨ ∃ t', ReflTransGen (RStep E.exit) t t' ∧ E.Overflow t' := by
  classical
  by_cases hov : ∃ t', ReflTransGen (RStep E.exit) t t' ∧ E.Overflow t'
  · exact .inr hov
  · left
    refine InfiniteTrace.coinduct (fun x => ReflTransGen (RStep E.exit) t x ∧ InfiniteTrace E.TStep x)
      ?_ ⟨.refl, h⟩
    intro x ⟨hx, hi⟩
    obtain ⟨y, hy, hi'⟩ := hi.unfold
    rcases hy with hy | ⟨hxo, -⟩
    · exact ⟨y, hy, hx.tail hy, hi'⟩
    · exact absurd ⟨x, hx, hxo⟩ hov

end Env

end Silmaril.X86.Backend
