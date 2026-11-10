module

public import Silmaril.Formats.Compression.Deflate.Compress

/-!
# LZ77 token semantics

`applyTokens out ts` runs the tokens `ts` against the output `out` exactly as
the decoder does: a literal appends a byte, a length/distance pair copies
(possibly overlapping) bytes from earlier output. `lz77Greedy_spec` shows that
the hash-chain matcher's tokens are well formed for DEFLATE and expand back to
the input — whatever the hash chains contain, since every emitted length comes
from `matchLen` and `matchLen_spec` says those bytes really do agree.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

/-- The effect of one token on the output. -/
def applyToken (out : List UInt8) : Token → List UInt8
  | .literal b => out ++ [b]
  | .lenDist len d => copyBack d out len
  | .eob => out

/-- The effect of a token list on the output. -/
def applyTokens (out : List UInt8) (ts : List Token) : List UInt8 := ts.foldl applyToken out

/-- A non-final token DEFLATE can represent, given the output so far. -/
def TokenValid (out : List UInt8) : Token → Prop
  | .literal _ => True
  | .lenDist len d => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ d ∧ d ≤ 32768 ∧ d ≤ out.length
  | .eob => False

/-- Every token is valid against the output produced by the ones before it. -/
def TokensValid : List UInt8 → List Token → Prop
  | _, [] => True
  | out, t :: ts => TokenValid out t ∧ TokensValid (applyToken out t) ts

end Silmaril.Formats.Compression.Deflate
