module

public import Silmaril.Logic.ACL2.X86Run.WithStep.Defs
public import Silmaril.Logic.ACL2.Standard.Pure.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.WithStep.Frontier

open Standard

/-- The step uses the same encoded-record readers as the outer run. -/
def fixedBinding (name : Name) (arity : Nat) : Option ((Fin arity → Object) → Object) :=
  match arity with
  | 1 =>
    let readers := Status.recordPrimitives Status.fieldRules Status.Tlb.recordFields
    if name = faultName then some (fun args => Status.fault.read readers (args 0))
    else if name = msName then some (fun args => Status.ms.read readers (args 0))
    else Pure.binding name 1
  | k => Pure.binding name k

/-- Entries supplied by the checked record readers and pure object helpers. -/
def installedEntries : List (Name × Nat) :=
  X86Step.frontierEntries.filter fun entry => (fixedBinding entry.1 entry.2).isSome

def remainingEntries : List (Name × Nat) :=
  X86Step.frontierEntries.filter fun entry => (fixedBinding entry.1 entry.2).isNone

/-- Restrict the exact step signature to declarations with no fixed binding. -/
def remaining : Signature :=
  ⟨fun name => (X86Step.frontier.arity name).filter fun arity => (fixedBinding name arity).isNone⟩

def remainingInclusion : Signature.Hom remaining X86Step.frontier :=
  ⟨fun h => Option.eq_some_of_filter_eq_some h⟩

abbrev Bindings := Translated.Interpretation remaining

/-- Supply checked operations where available and delegate each remaining call by its exact arity. -/
def extend (bindings : Bindings) : FrontierBindings :=
  fun {k} f args =>
    match h : fixedBinding f.val k with
    | some op => op args
    | none => bindings ⟨f.val, by simp [remaining, f.property, h]⟩ args

def machineBindings (bindings : Bindings) : MachineBindings :=
  WithStep.machineBindings (extend bindings)

end Silmaril.Logic.ACL2.X86Run.WithStep.Frontier
