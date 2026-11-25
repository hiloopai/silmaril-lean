module

public import Silmaril.Compiler.C.Compact.Defs
import Silmaril.Proofs.Compiler.C.Compact
import Silmaril.Proofs.Compiler.C.CompactBody

public section
namespace Silmaril.Compiler.C.Compact

open Silmaril.Compile.C.Sem Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- A successful expression projection preserves the result, including a C0 stop, and
does not change the related Ail environment. This is about C0 expression evaluation,
not a simulation of the full Cerberus Core transition system. -/
theorem ExprProjection.eval_eq {scope : List Silmaril.Cerberus.Sym} {ail : TypedExpression}
    (projection : ExprProjection scope ail) (program : C0.Prog) (fn : C0.FunDef) (env : C0.Env)
    (read : Nat → Except C0.Stop Int)
    (related : ∀ index symbol, scope[index]? = some symbol → read index = C0.readVar fn env symbol)
    (fuel : Nat) (enough : projection.expr.depth ≤ fuel) :
    C0.evalE program fuel fn ail env = (projection.expr.eval read).map (·, env) :=
  Proofs.Compiler.C.Compact.eval_eq projection.projects program fn env read related fuel enough

/-- Acceptance certifies the compact tree's scope and its structural relationship to
the exact original Ail body. It does not rely on comparing results on sample inputs. -/
theorem project_sound {ail : TypedProgram} {result : Projection} (success : project ail = .ok result) :
    FunctionProjects ail result.fn :=
  Proofs.Compiler.C.Compact.extraction success

/-- From related, initialized signed-int parameters and a matching C0 frame layout, the
original Ail body returns the same signed int without effects on globals or output, or
stops with the same signed-overflow UB. The syntax bound excludes exhaustion for every
such entry. This starts after argument setup; it says nothing about Core scheduling. -/
theorem FunctionProjects.activation {ail : TypedProgram} {fn : Function}
    (projection : FunctionProjects ail fn) {symbol : Sym} {source : FunctionDefinition GenTypeCategory}
    (sole : ail.2.functionDefinitions = [(symbol, source)])
    (program : C0.Prog) (fd : C0.FunDef) (caller env : C0.Env) (slots : Array Int)
    (entry : SlotState source.params slots env) (bodyEq : fd.body = source.body)
    (returnType : fd.ret = .int 4 true)
    (localTypes : ∀ bindings statements, source.body.node = .block bindings statements →
      ∀ binding ∈ bindings, fd.locals[binding.1.number]? = some (.int 4 true))
    (fuel : Nat) (enough : fn.body.fuel + 2 ≤ fuel) :
    IntOutcome (fn.run slots) ∧
      observeActivation caller (C0.loop program fuel fd (some fd.body) .stop env) =
        (fn.run slots).map (fun value => (some value, { env with locals := caller.locals })) :=
  Proofs.Compiler.C.Compact.accepted_activation projection sole program fd caller env slots entry bodyEq
    returnType localTypes fuel enough

end Silmaril.Compiler.C.Compact
