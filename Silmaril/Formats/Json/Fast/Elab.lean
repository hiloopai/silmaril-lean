module

public import Silmaril.Formats.Json.Fast.Thms
public meta import Silmaril.Formats.Json.Fast.Parser.Defs
public meta import Lean.Elab.Tactic
public meta import Lean.Compiler.NoncomputableAttr

/-! `json% "…"` and `json_file name from "path"` normally emit constructor terms. Type
checking those terms does not verify their source. `json_text` independently embeds text
and `json_source` checks a separate `SourceMatches` claim in the kernel. -/

public meta section

open Lean Elab Command
namespace Silmaril.Formats.Json.Fast

register_option silmaril.json.precompute : Bool := {
  defValue := true
  descr := "emit JSON constructor terms at elaboration; when false, embed a logical parser application"
}

namespace Elab

def valueType : Expr := mkConst ``Value
def resultType : Expr := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``Error) valueType
def entryType : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) valueType

def arrayExpr (type : Expr) (items : Array Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [0]) type
  let cons := mkApp (mkConst ``List.cons [0]) type
  mkApp2 (mkConst ``List.toArray [0]) type (items.foldr (mkApp2 cons) nil)

partial def chunkExpr {α : Type} (type : Expr) (item : α → Expr) : ChunkSeq α → Expr
  | .leaf items => mkApp2 (mkConst ``ChunkSeq.leaf [0]) type (arrayExpr type (items.map item))
  | .branch size left right =>
    mkApp4 (mkConst ``ChunkSeq.branch [0]) type (mkNatLit size)
      (chunkExpr type item left) (chunkExpr type item right)

def indexExpr : KeyIndex → Expr
  | .empty => mkConst ``KeyIndex.empty
  | .node hash positions left right =>
    mkApp4 (mkConst ``KeyIndex.node) (mkNatLit hash)
      (arrayExpr (mkConst ``Nat) (positions.map mkNatLit)) (indexExpr left) (indexExpr right)

partial def valueExpr : Value → Expr
  | .null => mkConst ``Value.null
  | .bool boolean => mkApp (mkConst ``Value.bool) (toExpr boolean)
  | .string text => mkApp (mkConst ``Value.string) (mkStrLit text)
  | .number decimal => mkApp (mkConst ``Value.number) <|
    mkApp3 (mkConst ``JsonWire.Decimal.mk) (toExpr decimal.negative) (mkNatLit decimal.coefficient)
      (mkIntLit decimal.exponent)
  | .array items => mkApp (mkConst ``Value.array) (chunkExpr valueType valueExpr items)
  | .object entries index =>
    let members := chunkExpr entryType (fun (key, child) =>
      mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) valueType (mkStrLit key) (valueExpr child)) entries
    let index := match index with
      | none => mkApp (mkConst ``Option.none [0]) (mkConst ``KeyIndex)
      | some index => mkApp2 (mkConst ``Option.some [0]) (mkConst ``KeyIndex) (indexExpr index)
    mkApp2 (mkConst ``Value.object) members index

def timePhase {α : Type} (phase : String) (work : Unit → α) : CoreM α := do
  if !Lean.profiler.get (← getOptions) then return work ()
  let start ← IO.monoNanosNow
  let result ← IO.mkRef (work ())
  let elapsed := (← IO.monoNanosNow) - start
  logInfo m!"JSON: {phase}_ns={elapsed}"
  result.get

def errorExpr (error : Error) : Expr :=
  let kind := match error.kind with
    | .invalidUtf8 => ``ErrorKind.invalidUtf8
    | .syntax => ``ErrorKind.syntax
    | .trailingInput => ``ErrorKind.trailingInput
    | .unpairedSurrogate => ``ErrorKind.unpairedSurrogate
    | .depthLimit => ``ErrorKind.depthLimit
    | .numberLimit => ``ErrorKind.numberLimit
  mkApp2 (mkConst ``Error.mk) (mkNatLit error.offset) (mkConst kind)

def resultExpr (text : String) : CoreM Expr := do
  if !silmaril.json.precompute.get (← getOptions) then
    return mkApp2 (mkConst ``parseText) (mkStrLit text) (mkConst ``defaultLimits)
  let parsed ← timePhase "parse" fun _ => parseText text
  timePhase "emit" fun _ => match parsed with
    | .error error => mkApp3 (mkConst ``Except.error [0, 0]) (mkConst ``Error) valueType (errorExpr error)
    | .ok value => mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``Error) valueType (valueExpr value)

def addDef (name : Name) (type body : Expr) : CoreM Unit :=
  withExporting <| withOptions (Lean.Elab.async.set · false) do
    addDecl (.defnDecl { name, levelParams := [], type, value := body, hints := .abbrev, safety := .safe })
    modifyEnv (addNoncomputable · name)

def readText (path : String) : CommandElabM String := do
  let file := (System.FilePath.mk (← getFileName)).parent.getD "." / path
  let bytes ← IO.FS.readBinFile file
  let some text := String.fromUTF8? bytes | throwError "JSON: invalid UTF-8 in {file}"
  return text

end Elab

elab "json% " text:str : term => Elab.resultExpr text.getString

elab "json_file " name:ident " from " path:str : command => do
  let text ← Elab.readText path.getString
  let name := (← getCurrNamespace) ++ name.getId
  liftCoreM do Elab.addDef name Elab.resultType (← Elab.resultExpr text)

elab "json_text " name:ident " from " path:str : command => do
  let text ← Elab.readText path.getString
  let name := (← getCurrNamespace) ++ name.getId
  liftCoreM <| Elab.addDef name (mkConst ``String) (mkStrLit text)

macro "json_decide" : tactic => `(tactic| decide +kernel)

elab "json_source" : tactic => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``SourceMatches 2 && !target.hasFVar && !target.hasMVar do
    throwError "json_source expects a closed SourceMatches goal"
  let bytes := target.appFn!.appArg!
  let result := target.appArg!
  let limits := mkConst ``defaultLimits
  let ty := Elab.resultType
  let reflexivity := mkApp2 (mkConst ``Eq.refl [1]) ty result
  let proof := if bytes.isAppOfArity ``String.toUTF8 1 then
    let text := bytes.appArg!
    mkApp6 (mkConst ``Eq.trans [1]) ty (mkApp2 (mkConst ``parseBytes) bytes limits)
      (mkApp2 (mkConst ``parseText) text limits) result
      (mkApp2 (mkConst ``parseBytes_toUTF8) text limits) reflexivity
  else reflexivity
  let proofName ← withOptions (Lean.Elab.async.set · false) do Meta.mkAuxLemma [] target proof
  goal.assign (mkConst proofName)
  Tactic.replaceMainGoal []

end Silmaril.Formats.Json.Fast
