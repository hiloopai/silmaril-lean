module

import Silmaril.Machine.Region.Trace.Thms
public import Silmaril.Machine.Vex.X86.MovJump.Thms
public meta import Silmaril.Machine.Vex.X86.MovJump.Defs
public import Silmaril.Machine.Vex.Examples.Defs
public meta import Silmaril.Machine.Vex.Examples.Defs

namespace Silmaril.Machine.Vex.AMD64Scalar.MovJump

open Silmaril.Semantics.Region
open Silmaril.X86 (MState)
open Silmaril.Machine.Region.X86 (system)
open Silmaril.Machine.Vex.Fixtures

@[expose] public def movFixture : Fragment := ⟨0x1000, 0⟩

private theorem fixtureGuard : movFixture.Guard := by
  constructor
  · decide
  · unfold Fragment.support
    decide

private def fixtureState : MState :=
  ⟨⟨fun r => if r = .rdi then 42 else 0, 0x1000, ⟨none, none, none, none, none, none⟩, 0⟩,
    movFixture.code.load⟩

private def fixturePost (_ : Nat) (_ : List Empty) (out : Input) : Prop := out.rax = 42 ∧ out.rip = 0x1005

private theorem fixture_contract (completion : Bool) (ret : Word)
    (loaded : movFixture.code.LoadedIn fixtureState.memory) :
    TotalHoare (system ret) (· = fixtureState) movFixture.support
      (fun label es full => fixturePost label es (project completion full)) (fun _ _ _ => False) :=
  (movFixture.transfer_wp fixtureGuard completion ret fixturePost (admit := (· = fixtureState))
    (fun _ eq => eq ▸ ⟨loaded, (movFixture.entryWP_iff fixtureGuard fixturePost _).mpr ⟨rfl, rfl, rfl⟩⟩)).2

/-- The report's actual MOV/JMP pyvex lift, related to all full first exits
of an inhabited process-memory instance (including either completion of ZF). -/
public theorem fixture_agreement (completion : Bool) (ret : Word) :
    ∃ (initial final : MState) (pair : Pair), validate 0x1000 movBytes movLift = .ok pair ∧
      initial.core.rip = 0x1000 ∧ movFixture.code.LoadedIn initial.memory ∧
      ExitsNormally (system ret) movFixture.support initial [] final ∧
      pair.target.run (project completion initial) = .ok (project completion final) ∧
      final.core.read .rax = 42 ∧ final.core.rip = 0x1005 := by
  have loaded : movFixture.code.LoadedIn fixtureState.memory :=
    movFixture.code.loadedIn_load (by decide)
  have ok : (validate movFixture.base movFixture.bytes movLift).isOk = true := by decide +kernel
  generalize accepted : validate movFixture.base movFixture.bytes movLift = verdict at ok
  cases verdict with
  | error => cases ok
  | ok pair =>
    obtain ⟨final, normal, agrees⟩ := movFixture.validated_exit fixtureGuard completion ret accepted rfl loaded
    have post := (fixture_contract completion ret loaded).1.1 _ [] final rfl normal.witness
    exact ⟨fixtureState, final, pair, accepted, rfl, loaded, normal, agrees, post⟩

example : ¬ (⟨0x1000, 0xfe⟩ : Fragment).Guard := by
  intro guard
  exact guard.leaves (.inr rfl)

example : Silmaril.X86.Ext.step 0 { fixtureState with memory := ⟨[], ∅⟩ } = .fetchFault := rfl

example (completion : Bool) (ret : Word) :
    ∃ (initial final : MState) (pair : Pair), validate 0x1000 movBytes movLift = .ok pair ∧
      Silmaril.Machine.Trace.Runs (system ret).step initial [] final ∧
      pair.target.run (project completion initial) = .ok (project completion final) := by
  obtain ⟨initial, final, pair, accepted, _, _, normal, agrees, _⟩ := fixture_agreement completion ret
  exact ⟨initial, final, pair, accepted, normal.witness.toTraceRuns, agrees⟩

#print axioms Fragment.validated_exit
#print axioms Fragment.validated_beh
#print axioms Fragment.transfer_wp
#print axioms fixture_agreement
#print axioms FirstExit.toTraceRuns
#print axioms Realizes.RefinesExits.matchTraceRuns

end Silmaril.Machine.Vex.AMD64Scalar.MovJump
