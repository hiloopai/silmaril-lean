module

public import Silmaril.Logic.ACL2.X86Run.Standard.Defs
public import Silmaril.Logic.ACL2.X86Run.Thms
import Silmaril.Proofs.Logic.ACL2.X86Run.Standard.Admission

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.MachineBindings

open Standard

variable (m : MachineBindings)

/-- The concrete object operations discharge every count premise of the imported body. -/
def countLaws : CountLaws m.objectModel where
  integer := Object.integerValue?
  zp_nil _ h := by exact Proofs.Logic.ACL2.X86Run.Standard.positive_count h
  minus_one := rfl
  add_integers _ _ _ hi hj := by exact Proofs.Logic.ACL2.X86Run.Standard.add_integers hi hj

/-- Admit the generated X86-RUN declaration with the concrete arithmetic bindings. -/
def admittedModel : Model declaration.signature := X86Run.admittedModel m.countLaws

def run (n x86 : Object) : Object := m.admittedModel.interpret (declaration.symbol runSymbol) ![n, x86]

theorem equation_holds : (declaration.equation runSymbol).Holds m.admittedModel :=
  X86Run.equation_holds m.countLaws

theorem fault_exit (n x86 : Object) (hf : m.fault x86 ≠ Object.nil) :
    m.run n x86 = x86 := X86Run.fault_exit m.countLaws ![n, x86] hf

theorem ms_exit (n x86 : Object) (hf : m.fault x86 = Object.nil) (hm : m.ms x86 ≠ Object.nil) :
    m.run n x86 = x86 := X86Run.ms_exit m.countLaws ![n, x86] hf hm

theorem halted_holds : halted.Holds m.admittedModel := X86Run.halted_holds m.countLaws

end Silmaril.Logic.ACL2.X86Run.MachineBindings
