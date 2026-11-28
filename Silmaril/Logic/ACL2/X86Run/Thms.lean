module

public import Silmaril.Logic.ACL2.X86Run.Defs
public import Silmaril.Logic.ACL2.Recursive.Thms
import Silmaril.Proofs.Logic.ACL2.X86Run.Admission

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run

open Recursive

variable {M : Model old} (laws : CountLaws M)

/-- A proof of decrease for the recursive paths in the exported logical body. -/
theorem terminates : declaration.Terminates M (rank laws) :=
  Proofs.Logic.ACL2.X86Run.terminates laws

/-- The conditional model extension of the named ACL2 declaration. -/
def admittedModel : Model declaration.signature :=
  declaration.model M (rank laws) (terminates laws)

theorem equation_holds : (declaration.equation runSymbol).Holds (admittedModel laws) :=
  declaration.equation_holds (terminates laws) runSymbol

theorem fault_exit (args : Env M 2)
    (hf : M.interpret faultSymbol (fun _ => args 1) ≠ M.primitives.nil) :
    run laws (terminates laws) args = args 1 :=
  Proofs.Logic.ACL2.X86Run.fault_exit (terminates laws) args hf

theorem ms_exit (args : Env M 2)
    (hf : M.interpret faultSymbol (fun _ => args 1) = M.primitives.nil)
    (hm : M.interpret msSymbol (fun _ => args 1) ≠ M.primitives.nil) :
    run laws (terminates laws) args = args 1 :=
  Proofs.Logic.ACL2.X86Run.ms_exit (terminates laws) args hf hm

/-- Satisfaction of the exported X86-RUN-HALTED formula. -/
theorem halted_holds : halted.Holds (admittedModel laws) :=
  Proofs.Logic.ACL2.X86Run.halted_holds (terminates laws)

end Silmaril.Logic.ACL2.X86Run
