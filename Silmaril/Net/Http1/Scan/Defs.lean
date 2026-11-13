module

public import Silmaril.Parse.ByteParse.Defs

/-!
# Scanning runs of bytes

Text protocols such as HTTP/1.1 (RFC 9112) delimit most of their elements by a byte that
cannot occur inside them: a method ends at `SP`, a field name at `:`, a line at `CR`. The
cursor parsers of `Silmaril.Parse.ByteParse` read fixed or length-prefixed items; this module adds
the one primitive such grammars need, a *run* of bytes of a class, ended by the first byte
outside the class:

* `scanWhile pred bs st i`: the first position at or after `i` in the window whose byte fails
  `pred` (or the end of the window); a self tail call, so a loop;
* `runThen pred`: the run, copied once, and the byte that ended it (consumed).

`Spec.runThen pred l (v, c)` says `l = v ++ [c]`, every byte of `v` satisfies `pred`, and `c`
does not. The parser is sound and complete for it (`Silmaril.Net.Http1.Scan.Thms`): completeness
holds because the ending byte is part of the production, so the parser's maximal munch never
reads beyond the bytes of the encoding.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

/-- The first position at or after `i`, inside the window `st` and the input, whose byte does
not satisfy `pred`; the end of the window (or input) if there is none. -/
def scanWhile (pred : UInt8 → Bool) (bs : ByteArray) (st i : Nat) : Nat :=
  if h : i < st ∧ i < bs.size then
    if pred bs[i] then scanWhile pred bs st (i + 1) else i
  else i
termination_by st - i

/-- A run of bytes satisfying `pred`, then the byte that ends it (consumed). Fails with `eof`
if the window ends inside the run. -/
@[inline] def runThen (pred : UInt8 → Bool) : Parser (Bytes × UInt8) := fun bs st i =>
  let k := scanWhile pred bs st i
  if h : k < st ∧ k < bs.size then .ok ((bs.extract i k).data.toList, bs[k]) (k + 1)
  else .err ⟨k, .eof⟩

namespace Spec

/-- A run `v` of `pred` bytes ended by a byte `c` outside `pred`. -/
def runThen (pred : UInt8 → Bool) : Bytes → Bytes × UInt8 → Prop :=
  fun l r => l = r.1 ++ [r.2] ∧ (∀ b ∈ r.1, pred b = true) ∧ pred r.2 = false

end Spec

end Silmaril.Net.Http1
