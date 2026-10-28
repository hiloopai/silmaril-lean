module

public import Silmaril.Formats.ELF.Cst.IsCst
public import Silmaril.Data.BinaryImage.Literal
public meta import Lean.Elab.Command

/-! # `cst_literals`: the raw-literal table of a generated CST

```
cst_literals lits of Cst.cst
-- def lits : List (Option Silmaril.BinaryImage.RawLiteral) := [none, some ⟨4096, 249, [c₀]⟩, …]
-- theorem lits_match : Cst.cst.LiteralsMatch lits
```

For every block of the CST definition, the command finds the raw payload's chunk literals
(`toBitVecBytes (decode chunk size [c₀, …])`, the form `hex_bv8` and `tools/elf-ast` emit) by
walking the definitions syntactically; typed blocks get `none`. `lits_match` is
`File.literalsMatch_of_eq rfl`, added directly to the kernel: it compares the CST's payload terms
with the table's, which are the same literals, without evaluating any byte. Nothing the command
computes is trusted; a wrong table is a kernel error, and `none` entries only make `IsCST` slower.
-/

namespace Silmaril.Formats.ELF.Cst

open Lean Elab Command Meta

/-- Unfold constant definitions at the head (aliases such as `def object := cst`). -/
private meta partial def unfoldHead (env : Environment) (e : Expr) (fuel : Nat := 64) : Expr :=
  match fuel, e with
  | fuel + 1, .letE _ _ value body _ => unfoldHead env (body.instantiate1 value) fuel
  | fuel + 1, .mdata _ inner => unfoldHead env inner fuel
  | _, _ =>
  match fuel, e.getAppFn with
  | fuel + 1, .const name _ =>
    match env.find? name with
    | some (.defnInfo info) =>
      if e.getAppNumArgs == 0 then unfoldHead env info.value fuel else e
    | _ => e
  | _, _ => e

private meta partial def listElems (env : Environment) (e : Expr) : Option (List Expr) :=
  let e := unfoldHead env e
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then do
    let rest ← listElems env e.appArg!
    pure (e.appFn!.appArg! :: rest)
  else none

private meta def arrayElems (env : Environment) (e : Expr) : Option (List Expr) :=
  let e := unfoldHead env e
  if e.isAppOfArity ``List.toArray 2 then listElems env e.appArg!
  else if e.isAppOfArity ``Array.mk 2 then listElems env e.appArg!
  else none

private meta def natValue? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none => e.rawNatLit?

/-- The literal of a raw byte term, as `RawLiteral.mk chunk size chunks`. -/
private meta def literalOf? (env : Environment) (e : Expr) : Option Expr := do
  let (chunk, size, chunks) ← Silmaril.BinaryImage.literalChunks env e
  pure (mkApp3 (mkConst ``Silmaril.BinaryImage.RawLiteral.mk) chunk size chunks)

/-- The literal of a section's raw body, if any. -/
private meta def sectionLiteral? (env : Environment) (sec : Expr) : Option Expr := do
  let sec := unfoldHead env sec
  guard (sec.isAppOfArity ``Section.mk 3)
  let body := unfoldHead env sec.appArg!
  guard (body.isAppOfArity ``SectionBody.raw 1)
  literalOf? env body.appArg!

private meta def blockLiteral? (env : Environment) (sections : Array (Option Expr))
    (block : Expr) : Option Expr := do
  let block := unfoldHead env block
  guard (block.isAppOfArity ``Block.mk 2)
  let part := unfoldHead env block.appArg!
  if part.isAppOfArity ``Part.sectionPayload 1 then
    let index ← natValue? part.appArg!
    (sections[index]?).join
  else if part.isAppOfArity ``Part.raw 2 then
    literalOf? env part.appArg!
  else none

syntax (name := cstLiteralsCmd) "cst_literals " ident " of " ident : command

elab_rules : command
  | `(cst_literals $id of $src) => do
  let srcName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo src
  let env ← getEnv
  let file := unfoldHead env (mkConst srcName)
  unless file.isAppOfArity ``File.mk 4 do
    throwError "cst_literals: `{srcName}` does not unfold to a `Cst.File` structure literal"
  let args := file.getAppArgs
  let some sections := arrayElems env args[1]!
    | throwError "cst_literals: cannot read the section array of `{srcName}`"
  let some blocks := listElems env args[2]!
    | throwError "cst_literals: cannot read the block list of `{srcName}`"
  let sectionLits := sections.toArray.map (sectionLiteral? env)
  let litType := mkApp (mkConst ``Option [0]) (mkConst ``Silmaril.BinaryImage.RawLiteral)
  let entries := blocks.map fun block =>
    match blockLiteral? env sectionLits block with
    | some lit => mkApp2 (mkConst ``Option.some [0]) (mkConst ``Silmaril.BinaryImage.RawLiteral) lit
    | none => mkApp (mkConst ``Option.none [0]) (mkConst ``Silmaril.BinaryImage.RawLiteral)
  let value := entries.foldr (init := mkApp (mkConst ``List.nil [0]) litType)
    fun entry rest => mkApp3 (mkConst ``List.cons [0]) litType entry rest
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addDecl <| .defnDecl
    { name, levelParams := [], type := mkApp (mkConst ``List [0]) litType, value,
      hints := .regular 0, safety := .safe }
  let matchType ← liftTermElabM do
    mkAppM ``File.LiteralsMatch #[mkConst srcName, mkConst name]
  let eqType ← liftTermElabM do
    let lhs ← mkAppM ``File.literalPayloads #[mkConst srcName, mkConst name]
    let fn ← mkAppM ``Option.map #[← withLocalDeclD `lit (mkConst ``Silmaril.BinaryImage.RawLiteral)
      fun lit => do mkLambdaFVars #[lit] (← mkAppM ``Option.some #[← mkAppM ``Silmaril.BinaryImage.RawLiteral.bytes #[lit]])]
    let len ← mkAppM ``List.length #[← mkAppM ``File.blocks #[mkConst srcName]]
    let rhs ← mkAppM ``List.map #[fn, ← mkAppM ``List.take #[len, mkConst name]]
    instantiateMVars (← mkEq lhs rhs)
  let proof := mkApp3 (mkConst ``File.literalsMatch_of_eq) (mkConst srcName) (mkConst name)
    (← liftTermElabM do mkEqRefl (eqType.appFn!.appArg!))
  liftCoreM <| addDecl <| .thmDecl
    { name := (← getCurrNamespace) ++ id.getId.appendAfter "_match", levelParams := [], type := matchType, value := proof }

end Silmaril.Formats.ELF.Cst
