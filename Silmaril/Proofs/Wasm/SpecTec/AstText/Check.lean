module

public meta import Lean
public import Silmaril.Wasm.SpecTec.AstText.Defs
public meta import Silmaril.Wasm.SpecTec.AstText.Defs
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import

/-!
# Build-time checks of the pinned `--ast` files

Two commands, run in compiled code at elaboration time. They are **tests**, not proofs: nothing
they establish reaches the kernel, and no `ofReduceBool` or native code is involved.

* `spectec_check_stream S against "file"` reads `file`, runs the **verified** reader
  `SExp.parseStream?` on its contents (not the unverified `SExp.parseStream` that
  `spectec_import` uses), and fails the build unless
  1. the result is exactly `IL.scriptS S` (compared with `SExp`'s `DecidableEq`), and
  2. the printer reproduces the file: `astFile 80 (IL.scriptS S)` equals the contents byte for
     byte (SpecTec's default `--ast-width`, `spectec/src/backend-ast/config.ml:9`).

  `S` is a script constant (for example `Specs.wasm30`) whose value is a list of definition
  constants or a list of reflected definitions; its value is read back from the environment, the
  term the kernel accepted, with `IL.unqDef` from `Import.lean`. Given (1), the theorem
  `IL.decodeScript?_scriptS` gives `importAstText? contents = some S`; (2) is silmaril's Python
  printer test rerun in Lean.
* `spectec_check_slice C against "file" lines a b` checks that the constant `C : List Char`,
  written with `spectec_chars% "…"`, is exactly lines `a` to `b` (1-based, inclusive) of `file`,
  each followed by its newline.

`spectec_chars% "…"` elaborates a string literal to the explicit list of its characters, so the
kernel can run the lexer on it without first reducing `String.toList` of a UTF-8 literal.
-/

public meta section

namespace Silmaril.Wasm.SpecTec.AstText

open Lean Elab Command Term Meta
open Silmaril.SpecTec

/-- The value the kernel accepted for the constant `n`. -/
def checkConstValue (cmd : String) (n : Name) : CommandElabM Expr := do
  let some info := (← getEnv).find? n
    | throwError "{cmd}: unknown constant {n}"
  let some value := info.value?
    | throwError "{cmd}: {n} has no value"
  pure value

/-- Read back the script a constant denotes: either a list of definition constants (as
`spectec_import` emits) or a list of reflected definitions. -/
def unqScriptConst (n : Name) : CommandElabM IL.Script := do
  let cmd := "spectec_check_stream"
  let value ← checkConstValue cmd n
  match IL.unqList (·.constName?) value with
  | some names =>
      names.mapM fun c => do
        let some d := IL.unqDef (← checkConstValue cmd c)
          | throwError "{cmd}: {c} is not a reflected IL.Def"
        pure d
  | none =>
      match IL.unqDefs value with
      | some ds => pure ds
      | none => throwError "{cmd}: {n} is neither a list of definition constants nor of definitions"

/-- The first index at which two lists differ, if any. -/
def firstDiff {α : Type} [DecidableEq α] : List α → List α → Nat → Option Nat
  | [], [], _ => none
  | x :: xs, y :: ys, i => if x = y then firstDiff xs ys (i + 1) else some i
  | _, _, i => some i

/-- `spectec_check_stream S against "file"`; see the module documentation. -/
syntax (name := spectecCheckStream) "spectec_check_stream " ident &" against " str : command

@[command_elab spectecCheckStream]
def elabSpectecCheckStream : CommandElab := fun stx => do
  let `(command| spectec_check_stream $id:ident against $path:str) := stx
    | throwUnsupportedSyntax
  let path := path.getString
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  unless (← System.FilePath.pathExists path) do
    throwError "spectec_check_stream: no such file: {path} (relative to {← IO.currentDir})"
  let contents ← IO.FS.readFile path
  let script ← unqScriptConst n
  let printed := IL.scriptS script
  let start ← IO.monoMsNow
  let some forms := SExp.parseStream? contents
    | throwError "spectec_check_stream: the verified reader rejects {path}"
  let parsed ← IO.monoMsNow
  unless forms.length == printed.length do
    throwError "spectec_check_stream: {path} has {forms.length} top-level forms, \
      {n} prints to {printed.length}"
  if let some (i : Nat) := firstDiff forms printed 0 then
    throwError "spectec_check_stream: form {i} of {path} is not definition {i} of {n} printed"
  let text := SExp.astFile SExp.defaultWidth printed
  unless text == contents do
    let off := (firstDiff text.toList contents.toList 0).getD 0
    throwError "spectec_check_stream: astFile {SExp.defaultWidth} (scriptS {n}) differs from \
      {path} at character {off}"
  let done ← IO.monoMsNow
  logInfo m!"spectec_check_stream {n}: the verified reader reads {path} \
    ({contents.utf8ByteSize} bytes) as scriptS {n} ({forms.length} definitions, {parsed - start} ms), \
    and astFile {SExp.defaultWidth} reprints it byte for byte ({done - parsed} ms)"

/-- `spectec_chars% "…"`: the explicit `List Char` of a string literal. -/
syntax (name := spectecChars) "spectec_chars% " str : term

@[term_elab spectecChars]
def elabSpectecChars : TermElab := fun stx _ => do
  let `(spectec_chars% $s:str) := stx | throwUnsupportedSyntax
  let charTy := Lean.mkConst ``Char
  let nil := mkApp (Lean.mkConst ``List.nil [Level.zero]) charTy
  pure <| s.getString.toList.foldr (init := nil) fun c acc =>
    mkAppN (Lean.mkConst ``List.cons [Level.zero])
      #[charTy, mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit c.toNat), acc]

/-- Read back a `List Char` emitted by `spectec_chars%`. -/
def unqChars (e : Expr) : Option (List Char) :=
  IL.unqList (fun c => match c.getAppFnArgs with
    | (``Char.ofNat, #[.lit (.natVal k)]) => some (Char.ofNat k)
    | _ => none) e

/-- `spectec_check_slice C against "file" lines a b`; see the module documentation. -/
syntax (name := spectecCheckSlice)
  "spectec_check_slice " ident &" against " str &" lines " num num : command

@[command_elab spectecCheckSlice]
def elabSpectecCheckSlice : CommandElab := fun stx => do
  let `(command| spectec_check_slice $id:ident against $path:str lines $a:num $b:num) := stx
    | throwUnsupportedSyntax
  let path := path.getString
  let (a, b) := (a.getNat, b.getNat)
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some cs := unqChars (← checkConstValue "spectec_check_slice" n)
    | throwError "spectec_check_slice: {n} is not a literal written with spectec_chars%"
  unless (← System.FilePath.pathExists path) do
    throwError "spectec_check_slice: no such file: {path} (relative to {← IO.currentDir})"
  let fileLines := (← IO.FS.readFile path).splitOn "\n"
  unless 1 ≤ a ∧ a ≤ b ∧ b < fileLines.length do
    throwError "spectec_check_slice: lines {a} to {b} are not lines of {path}"
  let expected := String.join ((fileLines.drop (a - 1)).take (b - a + 1) |>.map (· ++ "\n"))
  unless String.ofList cs == expected do
    let off := (firstDiff cs expected.toList 0).getD 0
    throwError "spectec_check_slice: {n} differs from {path} lines {a}-{b} at character {off}"
  logInfo m!"spectec_check_slice {n}: lines {a}-{b} of {path} ({cs.length} characters)"

end Silmaril.Wasm.SpecTec.AstText
