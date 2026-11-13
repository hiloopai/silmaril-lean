module

public import Silmaril.Compiler.Native.Optimize.Validation.Acceptance.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Observation.Thms
/-! Concrete defined-register domains for actual successful admitted source
execution. No symbolic or concrete read-success contract is assumed. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.SourceReads
open Silmaril.Machine

def Defined (frame : Lir.Frame Nat) (registers : List Nat) : Prop :=
  ∀ reg ∈ registers, ∃ word, frame.get reg = some word

def DomainExtends (before after : Lir.Frame Nat) : Prop :=
  ∀ reg, (∃ word, before.get reg = some word) → ∃ word, after.get reg = some word

structure Written (before after : Lir.Frame Nat) (registers : List Nat) : Prop where
  domain : DomainExtends before after
  defined : Defined after registers

end Silmaril.Compiler.Native.Optimize.Validation.SourceReads
