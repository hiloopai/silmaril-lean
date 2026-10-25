module

public meta import Silmaril.Wasm.Wat.Resolve
public meta import Silmaril.Wasm.Wat.InstructionParser
public meta import Silmaril.Wasm.Wat.Scalar
public meta import Silmaril.Wasm.Wat.Float

/-! # WAT instruction elaboration

Both flat structured syntax and folded expressions expand into the existing AST.
Folded operands are emitted in source order, before their operator. Branch label
names resolve in the innermost enclosing block, loop, if, or function.
-/

public meta section

open Lean
namespace Silmaril.Wasm.Wat

def Profile.scalarSyntax (p : Profile) : ScalarSyntax :=
  ⟨p.ns, p == .lime, "Silmaril.Wasm.V1"⟩

def conversion (p : Profile) (ty op : String) : MacroM (Option Term) :=
  conversionWith p.scalarSyntax ty op

def scalarOp (p : Profile) (ty op : String) : MacroM (Option Term) :=
  scalarOpWith p.scalarSyntax ty op

def memArg (naturalAlign : Nat) (nodes : List Node) : MacroM (Term × List Node) := do
  let (align, offset, rest) ← memoryAttributes 32 naturalAlign nodes
  return (← `(Silmaril.Wasm.V1.MemArg.mk $(natTerm align) $(natTerm offset)), rest)

def memoryOp (p : Profile) (ty op : String) (nodes : List Node) :
    MacroM (Option (Term × List Node)) := do
  let integer := ty == "i32" || ty == "i64"
  let floating := ty == "f32" || ty == "f64"
  unless integer || floating do return none
  let width := if ty == "i32" || ty == "f32" then 32 else 64
  let t ← if integer then integerType ty else floatType ty
  if op == "load" || op == "store" then
    let (arg, rest) ← memArg (if width == 32 then 2 else 3) nodes
    let args ← if integer then do let no ← `(none); pure #[t, no, arg] else pure #[t, arg]
    return some (← consTerm p "Instr"
      ((if integer then "int" else "float") ++ (if op == "load" then "Load" else "Store")) args, rest)
  if integer then
    for (size, log) in [(8, 0), (16, 1), (32, 2)] do
      if size < width then
        let pack ← applyTerm ("Silmaril.Wasm.V1.PackSize.i" ++ toString size)
        if op == "store" ++ toString size then
          let (arg, rest) ← memArg log nodes
          return some (← consTerm p "Instr" "intStore" #[t, ← `(some $pack), arg], rest)
        for (suffix, signed) in [("s", true), ("u", false)] do
          if op == "load" ++ toString size ++ "_" ++ suffix then
            let (arg, rest) ← memArg log nodes
            let sign ← signTerm signed
            return some (← consTerm p "Instr" "intLoad" #[t, ← `(some ($pack, $sign)), arg], rest)
  return none

def plain (scope : Scope) (origin : Node) (nodes : List Node) : Build (Term × List Node) := do
  let op ← atom origin
  let t ← get
  let p := t.profile
  for (wat, lean) in [("nop", "nop"), ("unreachable", "unreachable"), ("drop", "drop"),
      ("select", "select"), ("return", "return_"), ("memory.size", "memorySize"),
      ("memory.grow", "memoryGrow")] do
    if op == wat then return (← consTerm p "Instr" lean, nodes)
  if p == .lime && (op == "memory.copy" || op == "memory.fill") then
    return (← consTerm p "Instr" (if op == "memory.copy" then "memoryCopy" else "memoryFill"), nodes)
  for (wat, lean, names, kind) in [
      ("local.get", "localGet", scope.locals, "local"),
      ("local.set", "localSet", scope.locals, "local"),
      ("local.tee", "localTee", scope.locals, "local"),
      ("global.get", "globalGet", t.globals, "global"),
      ("global.set", "globalSet", t.globals, "global"),
      ("call", "call", t.funcs, "function"),
      ("br", "br", scope.labels, "label"), ("br_if", "brIf", scope.labels, "label")] do
    if op == wat then
      let n :: rest := nodes | watError origin "missing instruction index"
      return (← consTerm p "Instr" lean #[← indexTerm (← index names kind n)], rest)
  if op == "br_table" then
    let mut rest := nodes
    let mut labels := []
    while let n :: tail := rest do
      let some s := n.atom? | break
      unless s.startsWith "$" || (s.toList.head?.any Char.isDigit) do break
      labels := labels ++ [← indexTerm (← index scope.labels "label" n)]
      rest := tail
    let some fallback := labels.getLast? | watError origin "br_table requires a default label"
    return (← consTerm p "Instr" "brTable" #[← listTerm labels.dropLast, fallback], rest)
  if op == "call_indirect" then
    let (i, _, names, rest) ← typeUse origin nodes
    if names.any Option.isSome then
      watError origin "call_indirect parameters must be anonymous"
    return (← consTerm p "Instr" "callIndirect" #[← indexTerm i], rest)
  match op.splitOn "." with
  | [ty, name] =>
    if (ty == "i32" || ty == "i64") && name == "const" then
      let n :: rest := nodes | watError origin "missing integer literal"
      let width := if ty == "i32" then 32 else 64
      let bits ← checked n (integerBits width (← atom n))
      let b ← `(BitVec.ofNat $(natTerm width) $(natTerm bits))
      return (← consTerm p "Instr" "intConst" #[← integerType ty, b], rest)
    if (ty == "f32" || ty == "f64") && name == "const" then
      let n :: rest := nodes | watError origin "missing floating-point literal"
      let width := if ty == "f32" then 32 else 64
      let bits ← checked n (floatBits width (← atom n))
      let b ← `(BitVec.ofNat $(natTerm width) $(natTerm bits))
      return (← consTerm p "Instr" "floatConst" #[← floatType ty, b], rest)
    if let some result ← memoryOp p ty name nodes then return result
    if let some result ← scalarOp p ty name then return (result, nodes)
  | _ => pure ()
  watError origin s!"unsupported instruction '{op}'"

/-- Scalar instruction constructors plug into the profile-independent traversal. -/
def scalarInstructionSyntax : InstructionSyntax Tables where
  plain := plain
  control := fun _ origin op nodes => do
    let p := (← get).profile
    let (ty, rest) ← blockType origin nodes
    return (⟨fun left right => do
      if op == "if" then
        consTerm p "Instr" "if_" #[ty, ← listTerm left, ← listTerm right]
      else consTerm p "Instr" op #[ty, ← listTerm left]⟩, rest)

def instructions (scope : Scope) (nodes : List Node) (stops : List String := []) :
    Build (List Term × List Node) :=
  parseInstructions scalarInstructionSyntax scope nodes stops

def instruction (scope : Scope) (n : Node) (rest : List Node) :
    Build (List Term × List Node) :=
  parseInstruction scalarInstructionSyntax scope n rest


end Silmaril.Wasm.Wat
