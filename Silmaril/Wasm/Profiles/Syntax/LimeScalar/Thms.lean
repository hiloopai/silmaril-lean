module

public import Silmaril.Wasm.Profiles.Syntax.LimeScalar.Defs
public import Silmaril.Wasm.Profiles.Syntax.Thms
public import Silmaril.Wasm.V1.Intrinsic.Scalar.Thms
import Silmaril.Proofs.Wasm.Profiles.Syntax.LimeScalar.Typing

@[expose] public section

namespace Silmaril.Wasm.Profiles.Syntax.LimeScalar

open Silmaril.Proofs.Wasm.Profiles.Syntax.LimeScalar (instr_sound body_sound module_sound body_erase_ofWasm1)

theorem Instr.sound {context inputs outputs} (term : Instr context inputs outputs) :
    Lime1.Validation.InstrType context term.erase inputs outputs := instr_sound term

theorem Body.sound {context inputs outputs} (term : Body context inputs outputs) :
    Lime1.Validation.ExprType context term.erase inputs outputs := body_sound term

theorem Func.sound {context type sig} (term : Func context type sig) :
    (Lime.functionSyntax context).ok term.erase sig := ⟨term.resolved, trivial, term.body.sound⟩

theorem ClosedModule.sound {sig} (term : ClosedModule sig) : Lime1.Validation.ModuleValid term.erase :=
  module_sound term

theorem Func.erase_ofWasm1 {context type sig} (term : V1.Intrinsic.Scalar.Function context type sig) :
    (Func.ofWasm1 term).erase = term.erase.toLime := by
  exact congrArg (fun body => Lime1.Func.mk type term.locals body) (body_erase_ofWasm1 term.body)

theorem ClosedModule.erase_ofWasm1 {sig} (term : V1.Intrinsic.Scalar.ClosedModule sig) :
    (ClosedModule.ofWasm1 term).erase = term.erase.toLime :=
  congrArg (fun body => Wasm.Scalar.Module.ofFunction sig term.fn.locals body (some term.exportName))
    (body_erase_ofWasm1 term.fn.body)

def functionWitness (context : Lime1.Validation.Context) : Intrinsic (Lime.functionSyntax context) :=
  ⟨fun sig => Σ type, Func context type sig, fun term => term.2.erase, fun term => term.2.sound⟩

def moduleWitness : Intrinsic Lime.moduleSyntax :=
  ⟨fun _ => Σ sig, ClosedModule sig, fun term => term.2.erase, fun term => term.2.sound⟩

def wasm1FunctionWitness (context : V1.Validation.Context) : Intrinsic (functionFamily Wasm1 context) :=
  ⟨fun sig => Σ type, V1.Intrinsic.Scalar.Function context type sig,
    fun term => term.2.erase, fun term => term.2.sound⟩

def wasm1ModuleWitness : Intrinsic (moduleFamily Wasm1) :=
  ⟨fun _ => Σ sig, V1.Intrinsic.Scalar.ClosedModule sig, fun term => term.2.erase, fun term => term.2.sound⟩

/-- The existing native Wasm1 slice maps to native Lime witnesses, not to
transported Core witnesses. Functions retain their resolved type use. -/
def fromWasm1Function (context : V1.Validation.Context) :
    (wasm1FunctionWitness context).Map (functionWitness context.toLime) (wasm1FunctionToLime context) :=
  ⟨fun term => ⟨term.1, Func.ofWasm1 term.2⟩, fun term => Func.erase_ofWasm1 term.2⟩

def fromWasm1Module : wasm1ModuleWitness.Map moduleWitness wasm1ModuleToLime :=
  ⟨fun term => ⟨term.1, ClosedModule.ofWasm1 term.2⟩, fun term => ClosedModule.erase_ofWasm1 term.2⟩

end Silmaril.Wasm.Profiles.Syntax.LimeScalar
