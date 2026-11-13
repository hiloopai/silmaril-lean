module

public import Silmaril.Compiler.C.Sem.C1LirMemory.Defs
public import Silmaril.Compiler.C.Sem.RefinedCOwnedBundleFrontend.Defs
/-! Owned annotation contracts interpreted over actual LIR bytes. The target
resource interpretation retains explicit source initialization/writability
witnesses. Under byte-memory relatedness, preconditions, postconditions and the
emitted Lean goals are equivalent for both single pointers and positional bundles.
This is a contract interpretation theorem, not a program execution theorem or
recovery of source permissions from target memory. -/
@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCOwnedLirFrontend
open Silmaril.Cerberus.Assertion
open Silmaril.Machine

/-- Target byte ownership plus independent source access evidence. -/
def TargetHolds (source : C1.Memory) (target : Lir.Memory)
    (ρ : Pure.Env) (formula : Resources.Formula) : Prop :=
  ∃ heap, formula.holds ρ heap ∧ C1LirMemory.Access source heap ∧
    C1LirMemory.Realizes target heap

theorem targetHolds_iff {source : C1.Memory} {target : Lir.Memory}
    (related : C1LirMemory.Rel source target) (ρ : Pure.Env) (formula : Resources.Formula) :
    TargetHolds source target ρ formula ↔ ConcreteResources.Holds ρ formula source :=
  (related.holds_iff ρ formula).symm

namespace Single
abbrev Contract := RefinedCOwnedFrontend.Contract
abbrev LocEnv := RefinedCOwnedFrontend.LocEnv

def pre (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    (args : List Int) (source : C1.Memory) (target : Lir.Memory) : Prop :=
  args = [(locations c.pointer : Int)] ∧ locations c.pointer < 18446744073709551616 ∧
    TargetHolds source target ρ ((RefinedCOwnedByte.singleton (c.input.eval ρ)).owned
      (locations c.pointer) c.input) ∧ c.requires.holds ρ

def post (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    (source : C1.Memory) (target : Lir.Memory) : Prop :=
  TargetHolds source target ρ ((RefinedCOwnedByte.singleton (c.output.eval ρ)).owned
    (locations c.pointer) c.output) ∧ c.ensures.holds ρ

def leanGoal (c : Contract) (before after : Pure.Env) (locations : LocEnv)
    (args : List Int) (initial final : C1.Memory) (targetInitial targetFinal : Lir.Memory) : Prop :=
  pre c before locations args initial targetInitial → post c after locations final targetFinal

theorem pre_iff (c : Contract) (ρ : Pure.Env) (locations : LocEnv) (args : List Int)
    {source : C1.Memory} {target : Lir.Memory} (related : C1LirMemory.Rel source target) :
    pre c ρ locations args source target ↔ c.pre ρ locations args source := by
  simp only [pre, RefinedCOwnedFrontend.Contract.pre, targetHolds_iff related]

theorem post_iff (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    {source : C1.Memory} {target : Lir.Memory} (related : C1LirMemory.Rel source target) :
    post c ρ locations source target ↔ c.post ρ locations source := by
  simp only [post, RefinedCOwnedFrontend.Contract.post, targetHolds_iff related]

theorem leanGoal_iff (c : Contract) (before after : Pure.Env) (locations : LocEnv)
    (args : List Int) {initial final : C1.Memory} {targetInitial targetFinal : Lir.Memory}
    (beforeRelated : C1LirMemory.Rel initial targetInitial)
    (afterRelated : C1LirMemory.Rel final targetFinal) :
    leanGoal c before after locations args initial final targetInitial targetFinal ↔
      c.leanGoal before after locations args initial final := by
  rw [RefinedCOwnedFrontend.Contract.leanGoal_correct]
  simp only [leanGoal, RefinedCOwnedFrontend.Contract.obligation,
    pre_iff c before locations args beforeRelated, post_iff c after locations afterRelated]
end Single

namespace Bundle
abbrev Contract := RefinedCOwnedBundleFrontend.Contract
abbrev LocEnv := RefinedCOwnedBundleFrontend.LocEnv

def pre (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    (args : List Int) (source : C1.Memory) (target : Lir.Memory) : Prop :=
  args = c.cells.map (fun cell => (locations cell.pointer : Int)) ∧
    (c.cells.map (fun cell => locations cell.pointer)).Nodup ∧
    (∀ cell ∈ c.cells, locations cell.pointer < 18446744073709551616) ∧
    (∀ cell ∈ c.cells, TargetHolds source target ρ
      ((RefinedCOwnedByte.singleton (cell.input.eval ρ)).owned
        (locations cell.pointer) cell.input)) ∧ c.requires.holds ρ

def post (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    (source : C1.Memory) (target : Lir.Memory) : Prop :=
  (∀ cell ∈ c.cells, TargetHolds source target ρ
    ((RefinedCOwnedByte.singleton (cell.output.eval ρ)).owned
      (locations cell.pointer) cell.output)) ∧ c.ensures.holds ρ

def leanGoal (c : Contract) (before after : Pure.Env) (locations : LocEnv)
    (args : List Int) (initial final : C1.Memory) (targetInitial targetFinal : Lir.Memory) : Prop :=
  pre c before locations args initial targetInitial → post c after locations final targetFinal

theorem pre_iff (c : Contract) (ρ : Pure.Env) (locations : LocEnv) (args : List Int)
    {source : C1.Memory} {target : Lir.Memory} (related : C1LirMemory.Rel source target) :
    pre c ρ locations args source target ↔ c.pre ρ locations args source := by
  simp only [pre, RefinedCOwnedBundleFrontend.Contract.pre, targetHolds_iff related]

theorem post_iff (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    {source : C1.Memory} {target : Lir.Memory} (related : C1LirMemory.Rel source target) :
    post c ρ locations source target ↔ c.post ρ locations source := by
  simp only [post, RefinedCOwnedBundleFrontend.Contract.post, targetHolds_iff related]

theorem leanGoal_iff (c : Contract) (before after : Pure.Env) (locations : LocEnv)
    (args : List Int) {initial final : C1.Memory} {targetInitial targetFinal : Lir.Memory}
    (beforeRelated : C1LirMemory.Rel initial targetInitial)
    (afterRelated : C1LirMemory.Rel final targetFinal) :
    leanGoal c before after locations args initial final targetInitial targetFinal ↔
      c.leanGoal before after locations args initial final := by
  rw [RefinedCOwnedBundleFrontend.Contract.leanGoal_correct]
  simp only [leanGoal, RefinedCOwnedBundleFrontend.Contract.obligation,
    pre_iff c before locations args beforeRelated, post_iff c after locations afterRelated]
end Bundle

end Silmaril.Compile.C.Sem.RefinedCOwnedLirFrontend
