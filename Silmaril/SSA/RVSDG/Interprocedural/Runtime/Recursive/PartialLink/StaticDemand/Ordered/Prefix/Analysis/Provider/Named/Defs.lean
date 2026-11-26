module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Relocation.Thms

/-! Shared demand for a typed sequence of named provider imports. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)
open Isomorphism.RecursiveCall.Numbered (CaptureCode)
open Isomorphism.RecursiveCall.Numbered.Prefix (CheckedProviderAssembly Row)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {actions : Actions m σ}
variable {ids : GlobalRel} {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
variable {assembly : CheckedProviderAssembly actions ids keys captureCode} {name : String} {ty : Ty V S}

/-- The stored provider result at the requested type of this lookup. -/
def selectedDemandL (lookup : assembly.LookupReceipt name ty) : Outcome m σ [ty] :=
  lookup.port_eq ▸ lookup.entry.provider.selectedL

def selectedDemandR (lookup : assembly.LookupReceipt name ty) : Outcome m σ [ty] :=
  lookup.port_eq ▸ lookup.entry.provider.selectedR

/-- A demand certificate for the exact result selected by name, at the
provider's original link store. -/
structure NamedDemand (assembly : CheckedProviderAssembly actions ids keys captureCode)
    (summary : MemberSummary V S) where
  name : String
  lookup : assembly.LookupReceipt name summary.fn.port
  sound : Export actions summary (selectedDemandL lookup) (selectedDemandR lookup)

/-- Typed names and their demand certificates, in actual client port order. -/
inductive NamedImports (assembly : CheckedProviderAssembly actions ids keys captureCode) :
    Ports (Ty V S) → Type (max u v w + 1) where
  | nil : NamedImports assembly []
  | cons {ports : Ports (Ty V S)} {summary : MemberSummary V S}
      (provider : NamedDemand assembly summary) (rest : NamedImports assembly ports) :
      NamedImports assembly (summary.fn.port :: ports)

def NamedImports.table : {ports : Ports (Ty V S)} → NamedImports assembly ports → MemberSummaries V S
  | _, .nil => (Scope.ordinary m).table
  | _, .cons (summary := summary) source rest => append (prepend summary source.sound.earlier) rest.table

def NamedImports.dispatch : {ports : Ports (Ty V S)} → (sources : NamedImports assembly ports) →
    Dispatch actions sources.table
  | _, .nil => (Scope.Checked.ordinary actions).state.dispatch
  | _, .cons source rest => source.sound.dispatch.combine rest.dispatch

/-- Each materialized named pair equals the actual selected targets. The
ordinary tail is left to the existing typed capture checker. -/
def NamedImports.Matches {extra : Ports (Ty V S)} : {ports : Ports (Ty V S)} →
    (sources : NamedImports assembly ports) → Tuple m.Val (ports ++ extra) → Tuple m.Val (ports ++ extra) → Prop
  | _, .nil, _, _ => True
  | _, .cons source rest, .cons left tailL, .cons right tailR =>
    left = source.sound.targetL ∧ right = source.sound.targetR ∧ rest.Matches tailL tailR

structure NamedImports.Rows {ports extra : Ports (Ty V S)} (sources : NamedImports assembly ports)
    (inputsL inputsR : Tuple m.Val (ports ++ extra)) : Type (max u v w) where
  left : Row (Known sources.dispatch.left) inputsL
  right : Row (Known sources.dispatch.right) inputsR
  matched : sources.Matches inputsL inputsR

/-- The typed import position and captures for a slot supplied by a name.
The other slots in that provider's dispatch need not be imported. -/
structure NamedSlot {summary : MemberSummary V S} {imports : Ports (Ty V S)}
    (left : SlotGuard m summary) (right : SlotGuard m summary)
    (inputsL inputsR : Tuple m.Val imports) where
  port : Port imports summary.fn.port
  capsL : Tuple m.Val summary.captures
  capsR : Tuple m.Val summary.captures
  readyL : left (inputsL.get port) capsL
  readyR : right (inputsR.get port) capsR

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
