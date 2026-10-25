module

public import Silmaril.Formats.SExp.EncodingWatByteLexer
public import Silmaril.Formats.SExp.PrinterChunks
public import Silmaril.Wasm.Wat.Print.Common

@[expose] public section

/-! # Checked rendering of canonical WAT documents

The proposed text is accepted only when an executable WAT lexer and bracketer
recover the complete input document exactly. Their established
soundness theorem then relates the text to the independent WAT lexical grammar.
The original escaped-byte printer is tried first. If it fails the check, a
second proposal writes valid UTF-8 strings using plain Unicode characters.
Only after both old routes fail, the byte-capable lexer checks hexadecimal
escapes from the original printer. Mnemonic and Unicode escapes remain unsupported.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

open Silmaril.Formats Silmaril.Formats.SExpEncoding

/-- Render tagged WAT atoms; the final lexical check rejects unsupported or
ambiguous representations rather than trusting this proposal. -/
def watAtomText : Atom → String
  | .sym text => text
  | .id name => "$" ++ name
  | .str bytes => Wasm.Wat.Print.string bytes

/-- An alternative proposal for strings the executable lexer can read without
escapes. UTF-8 decoding and character checks are only proposal construction;
the complete document must still pass the exact lexical check. -/
def watPlainUtf8AtomText : Atom → String
  | .str bytes =>
      match String.fromUTF8? bytes.toByteArray with
      | some text =>
          if text.toList.all (fun c => decide (SExpEncoding.Wat.PlainStrChar c)) then
            "\"" ++ text ++ "\""
          else Wasm.Wat.Print.string bytes
      | none => Wasm.Wat.Print.string bytes
  | atom => watAtomText atom

/-- Propose a proper WAT document using the supplied atom printer, then check
exact lexing and bracketing. -/
def renderWatDocumentWith? (atomText : Atom → String)
    (tree : SExpEncoding.SExp) : Option String := do
  let trees ← toList? tree
  let text := String.intercalate "\n" (trees.map (SExpPrinter.printSExp2With atomText))
  if SExpEncoding.Wat.sexpWatExec? .core3 text = some tree then some text else none

/-- The exact lexical check certifies any accepted atom-printer proposal. -/
theorem renderWatDocumentWith?_sound {atomText : Atom → String}
    {tree : SExpEncoding.SExp} {text : String}
    (h : renderWatDocumentWith? atomText tree = some text) :
    SExpEncoding.Wat.sexpWat3 text tree := by
  unfold renderWatDocumentWith? at h
  cases ht : toList? tree with
  | none => simp [ht] at h
  | some trees =>
    rw [ht] at h
    let proposed := String.intercalate "\n" (trees.map (SExpPrinter.printSExp2With atomText))
    change (if SExpEncoding.Wat.sexpWatExec? .core3 proposed = some tree then
      some proposed else none) = some text at h
    split at h
    · rw [← Option.some.inj h]
      exact SExpEncoding.Wat.sexpWat_of_exec ‹_›
    · cases h

/-- Byte-capable proposal, checked against the same independent lexical grammar.
The old rendering routes are tried first to preserve their exact accepted text. -/
def renderWatByteDocumentWith? (atomText : Atom → String)
    (tree : SExpEncoding.SExp) : Option String := do
  let trees ← toList? tree
  let text := String.intercalate "\n" (trees.map (SExpPrinter.printSExp2With atomText))
  if SExpEncoding.Wat.sexpWatByteExec? .core3 text = some tree then some text else none

theorem renderWatByteDocumentWith?_sound {atomText : Atom → String}
    {tree : SExpEncoding.SExp} {text : String}
    (h : renderWatByteDocumentWith? atomText tree = some text) :
    SExpEncoding.Wat.sexpWat3 text tree := by
  unfold renderWatByteDocumentWith? at h
  cases ht : toList? tree with
  | none => simp [ht] at h
  | some trees =>
    rw [ht] at h
    let proposed := String.intercalate "\n" (trees.map (SExpPrinter.printSExp2With atomText))
    change (if SExpEncoding.Wat.sexpWatByteExec? .core3 proposed = some tree then
      some proposed else none) = some text at h
    split at h
    · rw [← Option.some.inj h]
      exact SExpEncoding.Wat.sexpWat_of_byteExec ‹_›
    · cases h

/-- Preserve both original rendering routes exactly. Only after both fail, retry
the original escaped-byte printer with the additive byte-escape lexer. -/
def renderWatDocument? (tree : SExpEncoding.SExp) : Option String :=
  match renderWatDocumentWith? watAtomText tree with
  | some text => some text
  | none =>
      match renderWatDocumentWith? watPlainUtf8AtomText tree with
      | some text => some text
      | none => renderWatByteDocumentWith? watAtomText tree

/-- Every previous successful rendering is retained with identical text. -/
theorem renderWatDocument?_of_original {tree : SExpEncoding.SExp} {text : String}
    (h : renderWatDocumentWith? watAtomText tree = some text) :
    renderWatDocument? tree = some text := by
  simp [renderWatDocument?, h]

/-- Previously successful plain-UTF8 fallback text is preserved exactly. -/
theorem renderWatDocument?_of_plainUtf8 {tree : SExpEncoding.SExp} {text : String}
    (ho : renderWatDocumentWith? watAtomText tree = none)
    (h : renderWatDocumentWith? watPlainUtf8AtomText tree = some text) :
    renderWatDocument? tree = some text := by
  simp [renderWatDocument?, ho, h]

/-- Every accepted rendering denotes exactly the requested WAT document under
its independently defined lexical and S-expression grammar. -/
theorem renderWatDocument?_sound {tree : SExpEncoding.SExp} {text : String}
    (h : renderWatDocument? tree = some text) : SExpEncoding.Wat.sexpWat3 text tree := by
  unfold renderWatDocument? at h
  cases original : renderWatDocumentWith? watAtomText tree with
  | some proposed =>
    rw [original] at h
    cases h
    exact renderWatDocumentWith?_sound original
  | none =>
    rw [original] at h
    cases plain : renderWatDocumentWith? watPlainUtf8AtomText tree with
    | some proposed =>
      rw [plain] at h
      cases h
      exact renderWatDocumentWith?_sound plain
    | none =>
      rw [plain] at h
      exact renderWatByteDocumentWith?_sound h

attribute [local cbv_eval] String.intercalate_singleton

/-- A real module document renders without an extra top-level list wrapper. -/
example : renderWatDocument? (doc [listOf [kw "module", listOf [kw "export",
      .atom (.str [97, 100, 100]), listOf [kw "func", kw "0"]]]]) =
    some "(module (export \"add\" (func 0)))" := by cbv

/-- The original plain lexer still rejects escaped quotes. -/
example : renderWatDocumentWith? watAtomText (doc [listOf [kw "module", listOf [kw "export",
      .atom (.str [34]), listOf [kw "func", kw "0"]]]]) = none := by cbv

/-- The additive route renders arbitrary bytes using hexadecimal escapes. -/
example : renderWatDocument? (doc [listOf [kw "module", listOf [kw "data",
      .atom (.str [0, 255, 34, 92])]]]) =
    some "(module (data \"\\00\\ff\\22\\5c\"))" := by cbv

end Silmaril.Wasm.Binaryen.Toolkit
