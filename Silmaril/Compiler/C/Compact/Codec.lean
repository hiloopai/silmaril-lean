module

public import Silmaril.Compiler.C.Compact.Defs
public import Silmaril.Cerberus.Ail.Codec.Defs

@[expose] public section
namespace Silmaril.Compiler.C.Compact

open Silmaril.Cerberus.Cabs.Wire

def Op.tag : Op → String
  | .add => "add"
  | .gt => "gt"

def Expr.emit : Expr → Out → Out
  | .literal value => fun out => out |> open_ "lit" |> arg (emitInt value) |> close
  | .slot index => fun out => out |> open_ "slot" |> arg (emitNat index) |> close
  | .bin op left right => fun out => out |> open_ op.tag |> arg left.emit |> arg right.emit |> close

def Body.emit : Body → Out → Out
  | .ret value => fun out => out |> open_ "return" |> arg value.emit |> close
  | .bind init next => fun out => out |> open_ "let" |> arg init.emit |> arg next.emit |> close
  | .branch test yes no => fun out => out |> open_ "if" |> arg test.emit |> arg yes.emit |> arg no.emit |> close

/-- Canonical wire bytes do not include commentary, names or source locations. -/
def Function.encode (fn : Function) : String :=
  "" |> open_ "compact-c-i32-v1" |> arg (emitNat fn.arity) |> arg fn.body.emit |> close |> (·.push '\n')

def Expr.decode : Nat → Sx → Except String Expr
  | fuel + 1, .node tag children =>
    match tag, children.toList with
    | "add", [left, right] => return .bin .add (← Expr.decode fuel left) (← Expr.decode fuel right)
    | "gt", [left, right] => return .bin .gt (← Expr.decode fuel left) (← Expr.decode fuel right)
    | "lit", [value] => return .literal (← decodeInt value)
    | "slot", [index] => return .slot (← decodeNat index)
    | _, _ => throw "invalid compact expression"
  | _, _ => throw "invalid compact expression or depth exceeded"

def Body.decode : Nat → Sx → Except String Body
  | fuel + 1, .node tag children =>
    match tag, children.toList with
    | "return", [value] => return .ret (← Expr.decode 256 value)
    | "let", [init, next] => return .bind (← Expr.decode 256 init) (← Body.decode fuel next)
    | "if", [test, yes, no] => do
      return .branch (← Expr.decode 256 test) (← Body.decode fuel yes) (← Body.decode fuel no)
    | _, _ => throw "invalid compact body"
  | _, _ => throw "invalid compact body or depth exceeded"

/-- Read one document, checking constructor arities, literal range and binding scope. -/
def Function.decode (text : String) : Except String Function := do
  let .node "compact-c-i32-v1" children ← read text.toUTF8
    | throw "expected compact-c-i32-v1 document"
  let [parameters, tree] := children.toList | throw "expected arity and body"
  let arity ← decodeNat parameters
  let body ← Body.decode (text.utf8ByteSize + 1) tree
  unless body.scoped arity do throw "literal or slot outside compact signed-int scope"
  return ⟨arity, body⟩

def Origin.emit (entry : Origin × Nat) (out : Out) : Out :=
  out |> open_ "origin" |> arg (emitNat entry.2)
    |> arg (Silmaril.Cerberus.Cabs.Codec.emitLoc entry.1.location)
    |> arg (emitOption emitStr entry.1.binder) |> close

/-- Node IDs are zero-based preorder ordinals in the compact tree, not line numbers in
either representation. The sidecar is bound separately to the same Ail projection. -/
def Projection.originText (projection : Projection) : String :=
  "" |> open_ "compact-c-origins-v1" |> arg (emitStr projection.name)
    |> arg (emitList emitStr projection.arguments)
    |> arg (emitList Origin.emit projection.origins.zipIdx) |> close |> (·.push '\n')

end Silmaril.Compiler.C.Compact
