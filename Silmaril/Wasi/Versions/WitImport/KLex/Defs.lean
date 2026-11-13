module

public import Silmaril.Wasm.Wit.Text.Parse.Defs
public meta import Lean.Elab.Term
public meta import Silmaril.Wasi.Versions.WitImport.Defs

@[expose] public section

/-!
# A kernel-reducible WIT lexer

`Silmaril.Wasm.Wit.Text.lex` is defined by well-founded recursion, which the kernel does not
unfold usefully, and its helper `takeLine` computes `(takeLine r).1` and `(takeLine r).2`
separately (two recursive calls per character). This module restates the lexer with fuel:

* `takeLineK`: `takeLine` in one pass;
* `lexBody rec cs`: one step of the lexer, calling `rec` on the rest;
* `lexK n cs`: `n` steps of fuel.

`Silmaril.Wasi.Versions.WitImport.KLex.Thms` proves `lexK n cs = lex cs` for `cs.length < n`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit.Text

/-- `takeLine` in one pass. -/
def takeLineK : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r =>
    if c = '\n' then ([], r)
    else match takeLineK r with
      | (a, b) => (c :: a, b)

/-- `takeNum` in one pass. -/
def takeNumK : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r =>
    if wordCont c || ((c == '.' || c == '+') && (r.head?.map wordCont).getD false) then
      match takeNumK r with
      | (a, b) => (c :: a, b)
    else ([], c :: r)

/-- `takeLineK` is `takeLine`. -/
theorem takeLineK_eq : ∀ cs, takeLineK cs = takeLine cs
  | [] => rfl
  | c :: r => by
    by_cases hc : c = '\n'
    · subst hc; simp [takeLineK, takeLine]
    · simp only [takeLineK, hc, ↓reduceIte, takeLineK_eq r]
      simp only [takeLine]

/-- `takeNumK` is `takeNum`. -/
theorem takeNumK_eq : ∀ cs, takeNumK cs = takeNum cs
  | [] => rfl
  | c :: r => by
    rw [takeNumK, takeNum, takeNumK_eq r]

theorem takeLineK_snd_le (cs : List Char) : (takeLineK cs).2.length ≤ cs.length := by
  rw [takeLineK_eq]; exact takeLine_length_le cs

theorem takeNumK_snd_le (cs : List Char) : (takeNumK cs).2.length ≤ cs.length := by
  rw [takeNumK_eq]; exact takeNum_length_le cs

/-- One step of the lexer; `rec` lexes strictly shorter lists. -/
def lexBody (cs : List Char) (rec : (cs' : List Char) → cs'.length < cs.length → Option (List Tok)) :
    Option (List Tok) :=
  match cs, rec with
  | [], _ => some []
  | '/' :: '/' :: '/' :: r, rec =>
    if r.head? = some '/' then
      rec (takeLineK r).2 (by have := takeLineK_snd_le r; simp only [List.length_cons]; omega)
    else (Tok.doc (String.ofList (takeLineK r).1) :: ·) <$>
      rec (takeLineK r).2 (by have := takeLineK_snd_le r; simp only [List.length_cons]; omega)
  | '/' :: '/' :: r, rec =>
    rec (takeLineK r).2 (by have := takeLineK_snd_le r; simp only [List.length_cons]; omega)
  | '/' :: '*' :: r, rec =>
    match h : skipBlock 0 r with
    | none => none
    | some r' => rec r' (by have := skipBlock_length_le 0 r r' h; simp only [List.length_cons]; omega)
  | '-' :: '>' :: r, rec => (Tok.arrow :: ·) <$> rec r (by simp only [List.length_cons]; omega)
  | '%' :: c :: r, rec =>
    if isLetter c then
      (Tok.id (String.ofList (c :: r.takeWhile wordCont)) :: ·) <$>
        rec (r.dropWhile wordCont)
          (by have := dropWhile_length_le' wordCont r; simp only [List.length_cons]; omega)
    else none
  | c :: r, rec =>
    if isWs c then rec r (by simp only [List.length_cons]; omega)
    else if isDigitC c then
      (Tok.num (String.ofList (c :: (takeNumK r).1)) :: ·) <$>
        rec (takeNumK r).2 (by have := takeNumK_snd_le r; simp only [List.length_cons]; omega)
    else if wordStart c then
      (wordTok (String.ofList (c :: r.takeWhile wordCont)) :: ·) <$>
        rec (r.dropWhile wordCont)
          (by have := dropWhile_length_le' wordCont r; simp only [List.length_cons]; omega)
    else if symChars.contains c then
      (Tok.sym c :: ·) <$> rec r (by simp only [List.length_cons]; omega)
    else none

/-- The lexer with `n` steps of fuel. -/
def lexK : Nat → List Char → Option (List Tok)
  | 0, _ => none
  | n + 1, cs => lexBody cs fun cs' _ => lexK n cs'

open Lean Elab Term in
/-- `wit_chars% "f.wit"`: the characters of a file (path relative to the Lean source), as a
list literal of `Char.ofNat` codes, so that the kernel never decodes a string literal. -/
syntax (name := witChars) "wit_chars% " str : term

open Lean Elab Term in
@[term_elab witChars] meta def elabWitChars : TermElab := fun stx _ => do
  let `(wit_chars% $p:str) := stx | throwUnsupportedSyntax
  let source := System.FilePath.mk (← readThe Core.Context).fileName
  let some directory := source.parent | throwError "cannot find source directory for {source}"
  let file := directory / p.getString
  let text ← try IO.FS.readFile file catch e => throwError "cannot read {file}: {e.toMessageData}"
  let charE := Lean.mkConst ``Char
  return text.toList.foldr
    (fun c rest => mkApp3 (Lean.mkConst ``List.cons [0]) charE
      (mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit c.toNat)) rest)
    (mkApp (Lean.mkConst ``List.nil [0]) charE)

open Lean Elab Term in
/-- `wit_src% "f.wit"`: the characters of the text the WIT importer parses for a file
(`WitImport.withHeader` with the header of its directory, after `WitImport.demoteParamDocs`),
computed during elaboration by the same glue as `wit_table%`, as a list literal of
`Char.ofNat` codes. -/
syntax (name := witSrc) "wit_src% " str : term

open Lean Elab Term in
@[term_elab witSrc] meta def elabWitSrc : TermElab := fun stx _ => do
  let `(wit_src% $p:str) := stx | throwUnsupportedSyntax
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
  let glued := withHeader hdr (demoteParamDocs text)
  let charE := Lean.mkConst ``Char
  return glued.toList.foldr
    (fun c rest => mkApp3 (Lean.mkConst ``List.cons [0]) charE
      (mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit c.toNat)) rest)
    (mkApp (Lean.mkConst ``List.nil [0]) charE)

/-- The parser of `Silmaril.Wasm.Wit.Text` over the fuelled lexer, on characters. -/
def parseCharsK (cs : List Char) : Option Silmaril.Wasm.Wit.Document :=
  (lexK (cs.length + 1) cs).bind Parse.document

end Silmaril.Wasi.Versions.WitImport
