module

public import CompilesToExamples.Straight.Defs
public import CompilesToExamples.Branch.Defs
public import Silmaril.Compiler.C.Compact.Codec

@[expose] public section
namespace CompilesToExamples.Explorer.Compact

open Silmaril.Compiler.C.Compact
open Silmaril.Compile.C.Sem
open Silmaril.Cerberus.Ail

def fixture (ail : TypedProgram) : Projection :=
  (project ail).toOption.getD ⟨⟨0, .ret (.literal 0)⟩, "", [], []⟩

def add3 : Projection := fixture Straight.ail
def max2 : Projection := fixture Branch.ail

/-- Call the single member of the exact Ail file, checking that the empty caller has
no visible global, local or output effect after the call. -/
def observeAil (ail : TypedProgram) (args : List Int) : Option Int := do
  let [(symbol, _)] := ail.2.functionDefinitions | none
  let .ok (value, env) := C0.callFn (C0.prepare ail) 80 symbol args {} | none
  if env.locals.isEmpty && env.globals.isEmpty && env.out.isEmpty then some value else none

end CompilesToExamples.Explorer.Compact
