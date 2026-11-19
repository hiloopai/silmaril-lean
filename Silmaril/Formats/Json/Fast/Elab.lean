module

public import Silmaril.Formats.Json.Fast.Thms
public meta import Silmaril.Formats.Json.Fast.Parser.Defs
public meta import Lean.Elab.Tactic
public meta import Lean.Compiler.NoncomputableAttr

/-! `json% "…"` and `json_file name from "path"` embed input for the logical parser.
The explicitly named `json_precomputed%` and `json_file_precomputed` instead run the parser
during elaboration and emit constructor terms. Those terms are type checked, not verified
against the source. `json_source` checks a `SourceMatches` claim in the kernel. -/

public meta section

open Lean Elab Command
namespace Silmaril.Formats.Json.Fast

register_option silmaril.json.allowPrecomputed : Bool := {
  defValue := false
  descr := "allow explicitly precomputed JSON terms without proving parser/source agreement"
}

namespace Elab

inductive Mode where
  | source | precomputed

def checkMode (mode : Mode) : CoreM Unit := do
  match mode with
  | .source => pure ()
  | .precomputed =>
    unless silmaril.json.allowPrecomputed.get (← getOptions) do
      throwError "precomputed JSON requires `set_option silmaril.json.allowPrecomputed true`"

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

def resultExpr (mode : Mode) (text : String) (source : Expr) : CoreM Expr := do
  match mode with
  | .source => return mkApp2 (mkConst ``parseText) source (mkConst ``defaultLimits)
  | .precomputed =>
    let parsed ← timePhase "parse" fun _ => parseText text
    match parsed with
    | .error error => throwError "JSON: {repr error.kind} at byte {error.offset}"
    | .ok value =>
      timePhase "emit" (fun _ => mkApp3 (Lean.mkConst ``Except.ok [0, 0])
        (Lean.mkConst ``Error) valueType (valueExpr value))

def addDef (name : Name) (type body : Expr) : CoreM Unit :=
  withExporting <| withOptions (Lean.Elab.async.set · false) do
    addDecl (.defnDecl { name, levelParams := [], type, value := body, hints := .abbrev, safety := .safe })
    modifyEnv (addNoncomputable · name)

def fromFile (mode : Mode) (name : Name) (path : String) : CommandElabM Unit := do
  liftCoreM <| checkMode mode
  let file := (System.FilePath.mk (← getFileName)).parent.getD "." / path
  let bytes ← IO.FS.readBinFile file
  let some text := String.fromUTF8? bytes | throwError "JSON: invalid UTF-8 in {file}"
  let name := (← getCurrNamespace) ++ name
  let source := name ++ `source
  let result ← liftCoreM <| resultExpr mode text (mkConst source)
  liftCoreM do
    addDef source (mkConst ``String) (mkStrLit text)
    addDef name resultType result

end Elab

elab "json% " text:str : term => do
  let source := text.getString
  Elab.resultExpr .source source (mkStrLit source)

elab "json_precomputed% " text:str : term => do
  Elab.checkMode .precomputed
  let source := text.getString
  Elab.resultExpr .precomputed source (mkStrLit source)

elab "json_file " name:ident " from " path:str : command =>
  Elab.fromFile .source name.getId path.getString

elab "json_file_precomputed " name:ident " from " path:str : command =>
  Elab.fromFile .precomputed name.getId path.getString

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
