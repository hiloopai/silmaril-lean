module

public import Silmaril.Compiler.Core.ElaborationProcess.Defs

/-! Universal specifications for the actual Core program produced by the
restricted typed-Ail literal-main elaborator. Finite prefixes remain behaviors.
This topic adds no independent Ail or ISO C semantics and no native certificate. -/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationTotal
open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics

/-- Every terminal behavior returns this specified integer with empty stdout,
and there is no infinite execution. Finite unfinished prefixes are allowed. -/
def returnsInteger (number : Int) : Silmaril.Cerberus.Institution.Sentence
  | .finite _ state => ∀ outcome, state.control = .halt outcome →
      outcome = .defined (.loaded (.specified (.integer number))) ∧ state.memory.stdout = ""
  | .infinite _ _ => False

end Silmaril.Compiler.Core.ElaborationTotal
