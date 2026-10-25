module

public import Silmaril.Logic.Metamath.Text.Parser

@[expose] public section

/-!
# Metamath printer

Statements are printed as their token sequences. Each statement goes on its
own line, with its tokens separated by single spaces; a comment keeps its raw
text. `Stmt.valid` states what the printer needs for its output to parse back:
labels, math symbols, file names, proof steps and compressed proof letters are
well formed, comment text is valid comment text, `$c` and `$v` statements are
nonempty and `$d` statements have at least two variables. The round trip
theorems are in `Silmaril.Logic.Metamath.Text.RoundTrip`.
-/

namespace Silmaril.Logic.Metamath.Text

namespace ProofText

/-- The tokens of a proof. A compressed proof's letter block is one token. -/
def tokens : ProofText → List Token
  | .normal steps => steps.map .sym
  | .compressed labels letters =>
    .sym "(" :: labels.map .sym ++ .sym ")" :: if letters = "" then [] else [.sym letters]

/-- A proof is well formed: normal proof steps are labels or `?`; compressed
proof labels are labels, and letters are `A`–`Z` or `?`. -/
def valid : ProofText → Bool
  | .normal steps => steps.all isProofStep
  | .compressed labels letters => labels.all isLabel && isLetterToken letters

end ProofText

namespace Stmt

/-- The tokens of a statement. -/
def tokens : Stmt → List Token
  | .comment t => [.comment t]
  | .constants ss => .kw .c :: ss.map .sym ++ [.kw .stop]
  | .variables ss => .kw .v :: ss.map .sym ++ [.kw .stop]
  | .disjoint ss => .kw .d :: ss.map .sym ++ [.kw .stop]
  | .floating l tc v => [.sym l, .kw .f, .sym tc, .sym v, .kw .stop]
  | .essential l tc body => .sym l :: .kw .e :: .sym tc :: body.map .sym ++ [.kw .stop]
  | .axiom l tc body => .sym l :: .kw .a :: .sym tc :: body.map .sym ++ [.kw .stop]
  | .provable l tc body pf =>
    .sym l :: .kw .p :: .sym tc :: body.map .sym ++ .kw .eq :: pf.tokens ++ [.kw .stop]
  | .openScope => [.kw .openScope]
  | .closeScope => [.kw .closeScope]
  | .include f => [.kw .openInclude, .sym f, .kw .closeInclude]

/-- A statement is well formed. -/
def valid : Stmt → Bool
  | .comment t => isCommentText t
  | .constants ss => !ss.isEmpty && ss.all isMathSymbol
  | .variables ss => !ss.isEmpty && ss.all isMathSymbol
  | .disjoint ss => 2 ≤ ss.length && ss.all isMathSymbol
  | .floating l tc v => isLabel l && isMathSymbol tc && isMathSymbol v
  | .essential l tc body => isLabel l && isMathSymbol tc && body.all isMathSymbol
  | .axiom l tc body => isLabel l && isMathSymbol tc && body.all isMathSymbol
  | .provable l tc body pf => isLabel l && isMathSymbol tc && body.all isMathSymbol && pf.valid
  | .openScope => true
  | .closeScope => true
  | .include f => isMathSymbol f

end Stmt

/-- Print tokens on one line, separated by spaces and ended by a line feed. -/
def printLine : List Token → String
  | [] => ""
  | [t] => t.print ++ "\n"
  | t :: ts => t.print ++ " " ++ printLine ts

/-- Print a statement on one line. -/
def Stmt.print (s : Stmt) : String := printLine s.tokens

namespace Source

/-- The tokens of a source file. -/
def tokens (src : Source) : List Token := src.flatMap Stmt.tokens

/-- Every statement of the source is well formed. -/
def Valid (src : Source) : Prop := ∀ s ∈ src, s.valid

instance (src : Source) : Decidable src.Valid :=
  inferInstanceAs (Decidable (∀ s ∈ src, s.valid))

/-- Print a source file, one statement per line. -/
def print (src : Source) : String := String.join (src.map Stmt.print)

end Source

/-- Print tokens separated by single spaces. -/
def printTokens : List Token → String
  | [] => ""
  | [t] => t.print
  | t :: ts => t.print ++ " " ++ printTokens ts

end Silmaril.Logic.Metamath.Text
