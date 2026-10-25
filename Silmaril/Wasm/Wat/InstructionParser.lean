module

public meta import Silmaril.Wasm.Wat.Common

/-! # Shared folded and flat instruction parser

Profiles supply opcode and structured-header elaboration. This traversal alone
controls operand expansion, label scope, `else`/`end`, and the order in which
implicit type uses are resolved after folded operands. It does not validate
instruction stack types.
-/

public meta section

namespace Silmaril.Wasm.Wat

/-- A parsed structured header captures its type and any profile-specific
immediates. The second body is nonempty only for `if`. -/
structure ControlHeader where
  finish : List Term → List Term → Lean.MacroM Term

/-- Profile-specific leaves of the common instruction grammar. `control` sees
the newly introduced label at the head of its scope. `splitFolded` only separates
dialect; it must not allocate implicit type indices before its operands expand. -/
structure InstructionSyntax (σ : Type) where
  plain : Scope → Node → List Node → StateT σ Lean.MacroM (Term × List Node)
  isControl : String → Bool := (["block", "loop", "if"].contains ·)
  control : Scope → Node → String → List Node →
    StateT σ Lean.MacroM (ControlHeader × List Node)
  deferredFolded : String → Bool := (· == "call_indirect")
  splitFolded : Node → List Node → Lean.MacroM (List Node × List Node) :=
    fun _ nodes => pure (nodes.span isTypeUseGroup)

mutual
  partial def parseInstructions {σ : Type} (dialect : InstructionSyntax σ)
      (scope : Scope) (nodes : List Node) (stops : List String := []) :
      StateT σ Lean.MacroM (List Term × List Node) := do
    match nodes with
    | [] => return ([], [])
    | n :: rest =>
      if n.atom?.any (stops.contains ·) then return ([], nodes)
      let (first, rest) ← parseInstruction dialect scope n rest
      let (others, rest) ← parseInstructions dialect scope rest stops
      return (first ++ others, rest)

  partial def parseInstruction {σ : Type} (dialect : InstructionSyntax σ)
      (scope : Scope) (n : Node) (rest : List Node) :
      StateT σ Lean.MacroM (List Term × List Node) := do
    match n with
    | .string .. | .quotedIdentifier .. => watError n "string or identifier is not an instruction"
    | .list _ [] => watError n "empty instruction expression"
    | .list _ (head :: children) =>
      let op ← atom head
      if dialect.isControl op && op != "if" then
        let (name, children) ← takeName children
        let inner := { scope with labels := name :: scope.labels }
        let (header, children) ← dialect.control inner n op children
        let (body, leftover) ← parseInstructions dialect inner children
        unless leftover.isEmpty do watError n "unexpected folded block delimiter"
        return ([← header.finish body []], rest)
      if op == "if" && dialect.isControl op then
        let (name, children) ← takeName children
        let (header, children) := children.span isTypeUseGroup
        let (operands, branches) := children.span (fun n => n.head? != some "then")
        unless operands.all (fun n => match n with | .list .. => true | _ => false) do
          watError n "folded if operands must be folded expressions"
        let (condition, _) ← parseInstructions dialect scope operands
        let inner := { scope with labels := name :: scope.labels }
        let (header, leftover) ← dialect.control inner n op header
        unless leftover.isEmpty do watError n "invalid folded if signature"
        let thenNode :: tail := branches | watError n "folded if requires a (then ...) group"
        let .list _ (_ :: thenBody) := thenNode | watError thenNode "invalid then group"
        let elseBody ← match tail with
          | [] => pure []
          | [.list _ (.atom _ "else" :: body)] => pure body
          | _ => watError n "folded if accepts one then group and an optional else group"
        let (left, _) ← parseInstructions dialect inner thenBody
        let (right, _) ← parseInstructions dialect inner elseBody
        return (condition ++ [← header.finish left right], rest)
      if dialect.deferredFolded op then
        let (header, operands) ← dialect.splitFolded head children
        unless operands.all (fun n => match n with | .list .. => true | _ => false) do
          watError n "folded operands must be parenthesized instructions"
        let (args, _) ← parseInstructions dialect scope operands
        let (term, leftover) ← dialect.plain scope head header
        unless leftover.isEmpty do watError n "invalid folded instruction immediates"
        return (args ++ [term], rest)
      let (op, operands) ← dialect.plain scope head children
      unless operands.all (fun n => match n with | .list .. => true | _ => false) do
        watError n "folded operands must be parenthesized instructions"
      let (args, _) ← parseInstructions dialect scope operands
      return (args ++ [op], rest)
    | .atom _ op =>
      if dialect.isControl op then
        let (name, rest) ← takeName rest
        let inner := { scope with labels := name :: scope.labels }
        let (header, rest) ← dialect.control inner n op rest
        let (left, rest) ← parseInstructions dialect inner rest
          (if op == "if" then ["else", "end"] else ["end"])
        let delim :: tail := rest | watError n "structured instruction requires 'end'"
        let (right, rest) ← if delim.atom? == some "else" then do
          let tail ← endLabel name tail
          let (right, rest) ← parseInstructions dialect inner tail ["end"]
          let _ :: tail := rest | watError n "if requires 'end'"
          pure (right, ← endLabel name tail)
        else pure ([], ← endLabel name tail)
        return ([← header.finish left right], rest)
      let (term, rest) ← dialect.plain scope n rest
      return ([term], rest)
end

end Silmaril.Wasm.Wat
