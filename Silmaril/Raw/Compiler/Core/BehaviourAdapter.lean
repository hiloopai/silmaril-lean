module

public import Silmaril.Compiler.Core.Spec.Defs
public import Silmaril.Compiler.C.Sem.BehaviourAdapter.Defs
/-!
# Adapter: core-comp's frozen specification (`Compile.Core.Spec`)

`Spec.lean` is frozen by hash; this file adds to its namespace without
changing its text.

`Spec.Obs` (exit with status and output, abort, trap, fault, divergence,
exhaustion) embeds in the process-level observables of the C semantics
(`C.Sem.ProcessObservable`), with `abort`, `trap` and `fault` as the signals 6,
4 and 11 that ccomp's runtime reports (`Compile.Target.Interp.observe`):

* `Obs.toObservable_injective`: nothing is lost;
* `Obs.toObservable_exit`, `Obs.toObservable_abort`: on exits and aborts the
  embedding agrees with that of the C semantics' `Obs`, so the two
  C-level observation types are one type;
* `coreObservables doc args`: the Core behaviours of a document as a behaviour
  set, with Core undefined behaviour (`CoreUB`) as undefined behaviour at the
  start;
* `allowed_iff`: `Spec.Allowed` is "exhaustion, or allowed by the core closure
  of `coreObservables`". Exhaustion is allowed unconditionally by the frozen
  statement, even when the source has no behaviour; the core's
  `Exhaustion.allowed` asks for a source behaviour, so the two are related by
  the explicit disjunct and not by the exhaustion axis;
* `soundSpec_iff`: the headline `SoundSpec compile` is: every machine
  behaviour other than exhaustion of a compiled, loaded artifact refines the
  Core behaviour set of its source.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Spec

open Silmaril.Machine.Behaviour Silmaril.Cerberus
open Silmaril.X86 (Word Reg)
open Silmaril.X86.Backend (Space)

/-- A specification observation as a process observable. -/
def Obs.toObservable : Obs → C.Sem.ProcessObservable
  | .exit n out => ⟨out, .exited n⟩
  | .abort out => ⟨out, .aborted 6⟩
  | .trap out => ⟨out, .aborted 4⟩
  | .fault out => ⟨out, .aborted 11⟩
  | .diverges => ⟨[], .diverges⟩
  | .exhausted => ⟨[], .exhausted⟩

theorem Obs.toObservable_injective : Function.Injective Obs.toObservable := by
  intro a b h
  cases a <;> cases b <;> simp_all [Obs.toObservable]

theorem Obs.toObservable_exit (n : Nat) (out : List UInt8) :
    (Obs.exit n out).toObservable = C.Sem.Obs.toObservable ⟨out, .status n⟩ := rfl

theorem Obs.toObservable_abort (out : List UInt8) :
    (Obs.abort out).toObservable = C.Sem.Obs.toObservable ⟨out, .signal 6⟩ := rfl

theorem Obs.toObservable_diverges :
    Obs.diverges.toObservable = C.Sem.Obs.toObservable ⟨[], .diverges⟩ := rfl

theorem Obs.toObservable_ne_undefined (o : Obs) (t : List UInt8) :
    o.toObservable ≠ ⟨t, .undefined⟩ := by
  cases o <;> simp [Obs.toObservable]

/-- The Core behaviours of a document run with `args`, as a behaviour set. -/
def coreObservables (doc : Codec.Document) (args : List String) : Set C.Sem.ProcessObservable :=
  Obs.toObservable '' {o | CoreBeh doc args o} ∪ {o | CoreUB doc args ∧ o = ⟨[], .undefined⟩}

/-- **`Spec.Allowed` is the core closure**, apart from unconditional
exhaustion. -/
theorem allowed_iff (doc : Codec.Document) (args : List String) (o : Obs) :
    Allowed doc args o ↔
      o = .exhausted ∨ o.toObservable ∈ Observable.close .forbidden (coreObservables doc args) := by
  constructor
  · rintro (h | h | h)
    · exact .inl h
    · refine .inr ?_
      rw [Observable.close_eq_univ (B := coreObservables doc args) (Or.inr ⟨h, rfl⟩)]
      trivial
    · exact .inr (.inl (.inl ⟨o, h, rfl⟩))
  · rintro (h | h)
    · exact .inl h
    · rcases h with (⟨o', ho', he⟩ | ⟨-, he⟩) | ⟨t, -, (⟨o', -, he⟩ | ⟨hub, -⟩)⟩ | ⟨hx, -⟩
      · exact .inr (.inr (Obs.toObservable_injective he ▸ ho'))
      · cases o <;> simp [Obs.toObservable] at he
      · exact absurd he (Obs.toObservable_ne_undefined o' t)
      · exact .inr (.inl hub)
      · cases hx

/-- The universal statement over machine behaviours, in the core. -/
theorem forall_allowed_iff (doc : Codec.Document) (args : List String) (M : Obs → Prop) :
    (∀ o, M o → Allowed doc args o) ↔
      Observable.Refines .forbidden (Obs.toObservable '' {o | M o ∧ o ≠ .exhausted})
        (coreObservables doc args) := by
  constructor
  · rintro h _ ⟨o, ⟨ho, hne⟩, rfl⟩
    exact ((allowed_iff doc args o).1 (h o ho)).resolve_left hne
  · intro h o ho
    by_cases hne : o = .exhausted
    · exact .inl hne
    · exact (allowed_iff doc args o).2 (.inr (h ⟨o, ⟨ho, hne⟩, rfl⟩))

/-- **The frozen specification as core refinement.** -/
theorem soundSpec_iff (compile : Codec.Document → Option Artifact) :
    SoundSpec compile ↔
      ∀ (doc : Codec.Document) (a : Artifact), compile doc = some a →
        minArgSize ≤ a.argSize ∧
        ∀ (S : Space) (exit : Word) (E0 : Nat), Loaded a S exit E0 →
          ∀ (args : List String), ArgsOk args → ∀ (saved : Reg → Word) (init : X86.State),
            Observable.Refines .forbidden
              (Obs.toObservable '' {o | MachineBeh a S exit E0 saved init args o ∧ o ≠ .exhausted})
              (coreObservables doc args) := by
  simp only [SoundSpec, forall_allowed_iff]

end Silmaril.Compile.Core.Spec
