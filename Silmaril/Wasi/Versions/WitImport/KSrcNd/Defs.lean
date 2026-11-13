module

public import Silmaril.Wasi.Versions.WitImport.KNoDoc.Defs
public meta import Silmaril.Wasi.Versions.WitImport.KNoDoc.Defs
public meta import Lean.Elab.Term

@[expose] public section

/-!
# `wit_srcnd%`: glued WIT text without doc comments

`wit_srcnd% "f.wit"` is the text `wit_src% "f.wit"` quotes (`Silmaril.Wasi.Versions.WitImport.KLex`:
the header of its directory prepended, parameter docs demoted) with every doc comment demoted
to a plain comment (`demoteDocs`, `Silmaril.Wasi.Versions.WitImport.KNoDoc`), as a list literal of
`Char.ofNat` codes. The glue runs during elaboration; the kernel sees the characters.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Lean Elab Term in
/-- `wit_srcnd% "f.wit"`: `wit_src% "f.wit"` with its doc comments demoted (`demoteDocs`), as a
list literal of `Char.ofNat` codes. -/
syntax (name := witSrcNd) "wit_srcnd% " str : term

open Lean Elab Term in
@[term_elab witSrcNd] meta def elabWitSrcNd : TermElab := fun stx _ => do
  let `(wit_srcnd% $p:str) := stx | throwUnsupportedSyntax
  let source := System.FilePath.mk (← readThe Core.Context).fileName
  let some directory := source.parent | throwError "cannot find source directory for {source}"
  let file := directory / p.getString
  let text ← try IO.FS.readFile file catch e => throwError "cannot read {file}: {e.toMessageData}"
  let some dir := file.parent | throwError "no directory for {file}"
  let mut hdr := (headerOf text).getD ""
  if hdr.isEmpty then
    let es ← dir.readDir
    for e in es.qsort (·.fileName < ·.fileName) do
      if hdr.isEmpty && e.fileName.endsWith ".wit" then
        if let some h := headerOf (← IO.FS.readFile e.path) then hdr := h
  if hdr.isEmpty then throwError "no package header for {file}"
  let glued := demoteDocs (withHeader hdr (demoteParamDocs text))
  let charE := Lean.mkConst ``Char
  return glued.toList.foldr
    (fun c rest => mkApp3 (Lean.mkConst ``List.cons [0]) charE
      (mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit c.toNat)) rest)
    (mkApp (Lean.mkConst ``List.nil [0]) charE)

end Silmaril.Wasi.Versions.WitImport
