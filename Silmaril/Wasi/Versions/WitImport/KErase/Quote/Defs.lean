module

public import Silmaril.Wasi.Versions.WitImport.KQuote.Defs
public import Silmaril.Wasi.Versions.WitImport.KErase.Defs
public meta import Silmaril.Wasi.Versions.WitImport.KQuote.Defs
public meta import Lean.Elab.Command

@[expose] public section

/-!
# `wit_kfulltoks`: the tokens of a text with its doc comments, quoted

`wit_kfulltoks F "a.wit"` (after `wit_klex F`, which defines `F.full`, the glued text with its
doc comments as `wit_src%` gives it) lexes `F.full` in Lean's evaluator, quotes the tokens as
`F.toksF : (List Char → String) → List Tok` (strings as `mk [c₁, …]`, see
`Silmaril.Wasi.Versions.WitImport.KQuote`), and proves `F.lexF : lexK (F.full.length + 1) F.full =
some (F.toksF String.ofList)` by kernel definitional equality (`kernel_rfl`). The quoted tokens
are only a certificate. With them, the kernel check that the parse of a doc-heavy file, erased,
is the parse without doc comments (`KCert/Erase/*`) is split into the lexer run and the parser
run, in separate modules.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Lean Elab Command Term
open Silmaril.Wasm.Wit

/-- `wit_kfulltoks F "a.wit"`: see the module documentation. -/
syntax (name := witKFullToks) "wit_kfulltoks " ident ppSpace str : command

@[command_elab witKFullToks] meta def elabWitKFullToks : CommandElab := fun stx => do
  let `(wit_kfulltoks $f:ident $p:str) := stx | throwUnsupportedSyntax
  let F := f.getId
  let some s := (← readSrcsK [p.getString]).head? | throwError "no source"
  let some toks := Text.lex (withHeader s.1 (demoteParamDocs s.2.2)).toList
    | throwError "not WIT text the lexer accepts"
  let tokT := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Silmaril.Wasm.Wit.Text.Tok)
  addDefK (kn F "toksF") (arrE mkTy tokT) (genE (toExpr toks))
  elabCommand (← `(theorem $(kid F "lexF") :
    lexK ($(kid F "full").length + 1) $(kid F "full") = some ($(kid F "toksF") String.ofList) := by
      kernel_rfl))

end Silmaril.Wasi.Versions.WitImport
