module

public import Silmaril.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Bits.BitstreamLemmas

/-!
# Huffman codes: encode/decode round trip

`HuffmanTable.CodeOK t s c l` packages what the LSB decoder needs to recover
symbol `s` from its code `c` of length `l`: the code fits in `l` bits, the table
maps `(c, l)` back to `s`, and no proper prefix of `c` is itself a code
(prefix-freeness). `readSymbolLSB_of_codeOK` is the decoder lemma.

`ofLengths_symOK` proves those properties for every symbol with a *nonzero* code
length in a canonical table built by `HuffmanTable.ofLengths` (RFC 1951 §3.2.2),
from the Kraft inequality and the length cap checked by `isValidLengths`.
Symbols whose code length is 0 have no code at all and are necessarily outside
the statement.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

/-- Symbol `s` has code `c` of length `l` in `t`, and the decoder can recover it. -/
structure HuffmanTable.CodeOK (t : HuffmanTable) (s c l : Nat) : Prop where
  pos : 0 < l
  le : l ≤ t.maxBits
  lt : c < 2 ^ l
  found : lookupEntry t.entries c l = some s
  prefixFree : ∀ k < l, lookupEntry t.entries (c >>> (l - k)) k = none

/-- Symbol `s` is encodable in `t`, by a code the decoder recovers. -/
def HuffmanTable.SymOK (t : HuffmanTable) (s : Nat) : Prop :=
  ∃ c l, t.encodeSymbol s = some (c, l) ∧ t.CodeOK s c l

/-! ### Canonical codes -/

section Canonical

variable (L : CodeLengths) (M : Nat)

/-- The entry `assignCodes` produces for a symbol, given the next-code table and
the symbol's rank among earlier symbols of the same length. -/
def canonEntry (ncR : List Nat) (i len rank : Nat) : CodeEntry :=
  if len = 0 ∨ len > M then { symbol := i, code := 0, length := 0 }
  else { symbol := i, code := ncR.getD (len - 1) 0 + rank, length := len }

/-! #### Kraft inequality -/

/-- The code space used by the lengths `1, …, k`, in units of `2^-M`. -/
def kraftUpTo (k : Nat) : Nat :=
  (L.map (fun x => if 1 ≤ x ∧ x ≤ k then 2 ^ (M - x) else 0)).sum

/-- The code space used by all lengths (as summed by `isValidLengths`). -/
def kraftTotal : Nat := (L.map (fun x => if x = 0 then 0 else 2 ^ (M - x))).sum

/-! #### Next-code table -/

/-- First code of length `m + 1`. -/
abbrev firstCode (m : Nat) : Nat := (nextCode (countByLength L M)).getD m 0

end Canonical

end Silmaril.Formats.Compression
