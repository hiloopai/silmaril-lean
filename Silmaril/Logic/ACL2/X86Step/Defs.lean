module

public import Silmaril.Logic.ACL2.X86Step.Source

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Step

open Translated

/-- Only external declarations called by this body occur in the signature. -/
def frontier : Signature :=
  ⟨fun name => (frontierEntries.find? fun entry => decide (entry.1 = name)).map Prod.snd⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem sourceChecks : (lower frontier formals source).isSome = true := by decide

/-- The typed definition is indexed by the pinned body and its exact lexical scope. -/
def definition : Definition frontier where
  name := stepName
  formals := formals
  distinct := by decide
  source := source
  body := (lower frontier formals source).get sourceChecks
  fresh := by decide

end Silmaril.Logic.ACL2.X86Step
