module

public import Silmaril.Wasi.Versions.WitImport.KLex.Defs

@[expose] public section

/-!
# WIT text without doc comments

`demoteDocs t` turns every doc comment line of `t` (a line starting, after spaces, with `///`
but not `////`) into a plain comment line (`//`). The lexer skips plain comments and turns doc
comments into `Tok.doc` tokens, which the parser only reads into the `docs` fields of the items
they precede. Doc comments never reach a signature table (`table`, `drops`) or a resolved
package (`rtable`, `envOf`, whose kinds drop label docs by `plainKind`).

`wit_srcnd% "f.wit"` (`Silmaril.Wasi.Versions.WitImport.KSrcNd`) is `wit_src% "f.wit"` after
`demoteDocs`.

Why: the parser reads a doc comment through `String.toList`, which the kernel evaluates by
UTF-8 decoding, a well-founded recursion over a list-backed byte array, in time quadratic in
the line length (a 120-character string: about 1 s). The vendored 0.2.12 files have 1817 doc
comment lines; `io/streams.wit` alone took about 50 s to parse in the kernel with its docs.
Without docs the parse of the same file takes well under a second.

Like `withHeader` and `demoteParamDocs`, `demoteDocs` is unverified text glue: it runs during
elaboration, and the kernel sees its output. Its effect is checked per file in the kernel
(`KCert/Lex/*`, `parseCharsK_of_lex` in `Silmaril.Wasi.Versions.WitImport.KNoDoc.Thms`): the
tokens of the demoted text are the tokens of the text with its docs (`wit_src%`) without the
doc-comment tokens (`notDoc`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

/-- A token other than a doc comment. -/
def notDoc : Silmaril.Wasm.Wit.Text.Tok → Bool
  | .doc _ => false
  | _ => true

/-- A line that is a doc comment: `///` after spaces, but not `////`. -/
def isDocOnly (l : String) : Bool :=
  let t := l.trimAsciiStart.toString
  t.startsWith "///" && !t.startsWith "////"

/-- Doc comment lines become plain comment lines (`///` to `//`). -/
def demoteDocs (t : String) : String :=
  "\n".intercalate ((t.splitOn "\n").map fun l =>
    if isDocOnly l then "//" ++ String.ofList (l.trimAsciiStart.toString.toList.drop 3) else l)

end Silmaril.Wasi.Versions.WitImport
