module

public import Silmaril.Logic.Metamath.Verify.Check
public import Silmaril.Logic.Metamath.Text.Parser

@[expose] public section

/-!
# Metamath text verification

`verifyText` parses a source string and checks its declarations and proofs.
The source must have no unresolved `$[ file $]` commands. Its success contract
is in `Silmaril.Logic.Metamath.Verify.Thms`.
-/

namespace Silmaril.Logic.Metamath.Verify

open Text

/-- Parse and check a Metamath source text. -/
def verifyText (text : String) : Except String (Database String String) :=
  match parse text with
  | .error e => .error s!"parse error: {repr e}"
  | .ok src =>
    match check src with
    | .error e => .error s!"check error: {repr e}"
    | .ok db => .ok db


end Silmaril.Logic.Metamath.Verify
