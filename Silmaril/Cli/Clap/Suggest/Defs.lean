module

/-!
# clap's "a similar argument exists" suggestions

clap 4.6 (`clap_builder::parser::features::suggestions`, the argument parser of
`wasm-tools 1.262.0`) suggests a known long flag or subcommand for an unknown one when their Jaro
similarity (strsim 0.11.1, `strsim::jaro`, over `char`s) is above 0.7; among the candidates above
the threshold it takes the most similar, and among equally similar ones the last in the order the
candidates are listed (the keymap order: arguments in definition order, then `help`).

`jaro` computes the similarity with the same IEEE double operations as strsim
(`(m / |a| + m / |b| + (m - t) / m) / 3`), so the threshold comparison and the ranking agree with
upstream bit for bit.

The clap dialect's copy (`Silmaril.Cli.Clap.Exact` uses it for the tips of usage errors); the same
definitions as `Silmaril.Wasm.Tools.Suggest`, which the wave-1 `wasm-tools` front end imports and
which should become an alias of this module once that release is out (the Cli region cannot
import Wasm).
-/

@[expose] public section

namespace Silmaril.Cli.Clap.Suggest

/-- The matching characters of `a` in `b` (strsim's first pass): for each character of `a`, the
first unflagged equal character of `b` within the search window is flagged. Returns the flags of
`a` and of `b`. -/
def matchFlags (a b : Array Char) : Array Bool × Array Bool := Id.run do
  let range := (Nat.max a.size b.size / 2) - 1
  let mut af := Array.replicate a.size false
  let mut bf := Array.replicate b.size false
  for i in [0:a.size] do
    let lo := i - range
    let hi := Nat.min b.size (i + range + 1)
    for j in [lo:hi] do
      if a[i]! == b[j]! && !bf[j]! then
        af := af.set! i true
        bf := bf.set! j true
        break
  return (af, bf)

/-- **strsim's `jaro`.** -/
def jaro (a b : String) : Float :=
  let a := a.toList.toArray
  let b := b.toList.toArray
  if a.size == 0 && b.size == 0 then 1.0
  else if a.size == 0 || b.size == 0 then 0.0
  else
    let (af, bf) := matchFlags a b
    let m := (af.toList.filter id).length
    if m == 0 then 0.0 else
    -- the flagged characters of `a` and of `b`, in order; transpositions are the positions
    -- where they differ, halved
    let am := (a.toList.zip af.toList).filterMap fun (c, f) => if f then some c else none
    let bm := (b.toList.zip bf.toList).filterMap fun (c, f) => if f then some c else none
    let t := ((am.zip bm).filter fun (x, y) => x != y).length / 2
    (m.toFloat / a.size.toFloat + m.toFloat / b.size.toFloat + (m - t).toFloat / m.toFloat) / 3.0

/-- **`did_you_mean(v, candidates).pop()`**: the most similar candidate above 0.7, the last one
among equals. -/
def didYouMean (v : String) (cands : List String) : Option String :=
  (cands.foldl (fun (best : Option (Float × String)) c =>
    let s := jaro v c
    if s > 0.7 then
      match best with
      | some (bs, _) => if s ≥ bs then some (s, c) else best
      | none => some (s, c)
    else best) none).map (·.2)

/-- Insert `(s, c)` before the first entry more similar than `s` (clap's `binary_search_by`
with a comparator that is never `Equal`, on a list sorted by similarity). -/
def insertAsc (s : Float) (c : String) : List (Float × String) → List (Float × String)
  | [] => [(s, c)]
  | (t, d) :: rest => if t > s then (s, c) :: (t, d) :: rest else (t, d) :: insertAsc s c rest

/-- **`did_you_mean(v, candidates)`**: every candidate whose similarity is above 0.7, in
ascending order of similarity, equally similar ones in candidate order; the most similar
comes last (its last element is `didYouMean v cands`, tested by the `top-level` golden suite
of `tools/wasm-tools/test-cli.py`). clap lists all of them for an unknown subcommand ("some
similar subcommands exist: …"). -/
def didYouMeanAll (v : String) (cands : List String) : List String :=
  (cands.foldl (fun acc c =>
    let s := jaro v c
    if s > 0.7 then insertAsc s c acc else acc) []).map (·.2)

end Silmaril.Cli.Clap.Suggest

end
