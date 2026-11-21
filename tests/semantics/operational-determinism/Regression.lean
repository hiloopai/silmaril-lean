module

import Silmaril.Semantics.Operational.Determinism.Fuel.Thms

open Silmaril.Semantics.Operational

private inductive Node where
  | entry | fork | returned | trapped | final
  deriving DecidableEq

private def edge : Node → Node → Prop
  | .entry, .fork | .fork, .returned | .fork, .trapped => True
  | _, _ => False

private def observe (source : Node) (result : Outcome Nat) : Prop :=
  ((source = .returned ∨ source = .final) ∧ result = .returned 7) ∨ (source = .trapped ∧ result = .trap)

private def base : WithUB Node Nat := .ofOpSem ⟨edge, observe⟩
private def admits (source : Node) : Prop := source ≠ .fork
private instance : DecidablePred admits := fun source => inferInstanceAs (Decidable (source ≠ .fork))

private theorem local_iff (source : Node) : base.toOpSem.LocalDetAt source ↔ admits source := by
  constructor
  · intro valid same
    change source = .fork at same
    subst source
    exact Node.noConfusion (valid.1 (left := .returned) (right := .trapped) trivial trivial)
  · intro allowed
    constructor
    · intro first second left right
      change edge source first at left
      change edge source second at right
      cases source <;> cases first <;> cases second <;> simp [admits, edge] at allowed left right ⊢
    · intro first second left right
      change observe source first at left
      change observe source second at right
      cases source <;> simp_all [observe]

instance : DecidablePred base.toOpSem.LocalDetAt := fun source => decidable_of_iff (admits source) (local_iff source).symm

private def choose : Node → Decision Node Nat
  | .entry => .move .fork
  | .fork => .move .returned
  | .returned | .final => .stop (.observed (.returned 7))
  | .trapped => .stop (.observed .trap)

private def selector : Oracle base where
  pick := choose
  valid source := by
    cases source with
    | entry | fork => trivial
    | returned => exact Or.inl ⟨.inl rfl, rfl⟩
    | final => exact Or.inl ⟨.inr rfl, rfl⟩
    | trapped => exact Or.inr ⟨rfl, rfl⟩

private def localSelector : Oracle base.requireLocalDet := selector.guard base.toOpSem.LocalDetAt

example : localSelector.run .entry 0 = .exhausted .entry := rfl
example : localSelector.run .entry 1 = .stop .fork .ub := rfl

example : ¬ base.requireLocalDet.ub .entry := by
  intro bad
  exact bad.elim False.elim (fun fails => fails ((local_iff .entry).mpr (by decide)))

example : (base.requirePrefix base.toOpSem.LocalDetAt).ub .entry :=
  .inr fun accepts => ((local_iff .fork).mp (accepts (Relation.ReflTransGen.single (b := Node.fork)
    (show base.step .entry .fork from trivial)))) rfl

example : base.requireLocalDet.UBReachable .entry := by
  have readback := localSelector.run_sound .entry 1
  change ∃ length, length ≤ 1 ∧ StepsN base.requireLocalDet.step length .entry .fork ∧
    base.requireLocalDet.ub .fork at readback
  obtain ⟨_, _, path, bad⟩ := readback
  exact ⟨.fork, path.reach, bad⟩

private theorem returned : base.toOpSem.May .entry (.returned 7) :=
  ⟨.returned, .tail (.single (show base.step .entry .fork from trivial)) trivial, Or.inl ⟨.inl rfl, rfl⟩⟩

private theorem trap : base.toOpSem.May .entry .trap :=
  ⟨.trapped, .tail (.single (show base.step .entry .fork from trivial)) trivial, Or.inr ⟨rfl, rfl⟩⟩

example : ∃ length, StepsN base.step length .entry .trapped :=
  StepsN.reach_iff_exists.mp (.tail (.single (show base.step .entry .fork from trivial)) trivial)

example : ∃ length target, StepsN base.step length .entry target ∧ base.observe target .trap :=
  (base.toOpSem.may_iff_exists_stepsN .entry .trap).mp trap

example (fuel : Nat) : selector.run .entry fuel ≠ .stop .trapped (.observed .trap) := by
  cases fuel with
  | zero => simp [Oracle.run, selector, choose]
  | succ remaining => cases remaining <;> simp [Oracle.run, selector, choose]

private theorem nonTrap : base.toOpSem.NonTrapDetAt .entry := by
  apply OpSem.nonTrapDetAt_iff.mpr
  intro left right hLeft hRight
  have payload (value : Nat) : base.toOpSem.May .entry (.returned value) → value = 7 := by
    rintro ⟨_, _, witnessed | witnessed⟩
    · cases witnessed.2; rfl
    · cases witnessed.2
  exact (payload left hLeft).trans (payload right hRight).symm

example : ¬ base.toOpSem.ResultDetAt .entry := by
  intro det
  cases OpSem.resultDetAt_iff.mp det returned trap

example : (base.requireViewDet OpSem.returnView).toOpSem.May .entry .trap :=
  (WithUB.enforce_may_iff (fun {_} path => nonTrap.of_reach path)).mpr trap

private def one : WithUB Bool Nat := .ofOpSem {
  step source target := source = false ∧ target = true
  observe source outcome := source = true ∧ outcome = .returned 42 }

private def oneSelector : Oracle one where
  pick
    | false => .move true
    | true => .stop (.observed (.returned 42))
  valid source := by cases source <;> exact ⟨rfl, rfl⟩

private theorem oneTerminal : one.toOpSem.TerminalDiscipline := by
  rintro source outcome ⟨hTrue, _⟩ target ⟨hFalse, _⟩
  cases hTrue.symm.trans hFalse

private theorem oneDet : one.toOpSem.DetFrom false := by
  intro source _
  exact ⟨fun {_ _} l r => l.2.trans r.2.symm, fun {_ _} l r => l.2.trans r.2.symm⟩

private theorem onePath : StepsN one.step 1 false true := .cons ⟨rfl, rfl⟩ (.nil _)

example : oneSelector.run false 0 = .exhausted false := rfl
example : ¬ one.toOpSem.Diverges false := onePath.no_diverges_of_normal oneDet (oneTerminal ⟨rfl, rfl⟩)

example : oneSelector.run false 20 = .stop true (.observed (.returned 42)) :=
  oneSelector.run_complete onePath ⟨rfl, rfl⟩ (by decide) oneDet oneTerminal (WithUB.ofOpSem_safe _ _) (by
    intro state _
    cases state <;> intro invalid <;> cases invalid)

private def unknownSelector : Oracle one := ⟨fun _ => .stop .unknown, fun _ => trivial⟩
example : unknownSelector.run false 20 = .stop false .unknown := rfl

private def protocol : Labelled Bool Bool Nat where
  step source label target := source = false ∧ label.isSome ∧ target = true
  observe := one.observe

example : ¬ protocol.TraceDetAt false := by
  intro det
  have observed (label : Bool) : protocol.Finishes false [label] (.returned 42) :=
    ⟨true, .visible ⟨rfl, rfl, rfl⟩ (.nil _), ⟨rfl, rfl⟩⟩
  cases (det (observed false) (observed true)).1

#print axioms WithUB.enforce_ubReachable_iff
#print axioms WithUB.requirePrefix_safe_iff
#print axioms WithUB.requireViewDet_safe_iff
#print axioms WithUB.permits_join
#print axioms WithUB.meet_permits
#print axioms Oracle.run_sound
#print axioms Oracle.run_complete
#print axioms Oracle.may_iff_run
#print axioms StepsN.reach_iff_exists
#print axioms OpSem.may_iff_exists_stepsN
#print axioms StepsN.no_diverges_of_normal
