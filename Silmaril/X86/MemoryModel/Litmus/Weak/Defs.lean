module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs
public import Silmaril.X86.Litmus.WeakExtract.Defs

/-!
# Litmus traces over `Weak9`: every corpus thread from its bytes

`Test.traces` extracts each thread with the `Atomic9` extractor; the writers of the six
non-temporal and string-store loose corners could not be extracted and were transcribed by hand.
`Test.wtraces` extracts **every** thread with `wextract` (`Weak9`: `Atomic9` plus `movnti`,
`rep stosb` and `Str9`'s forms), over a value domain built as `Test.domain` is:

* `Test.wfuel`: the fuel plus 64 steps for the elements of `rep` forms;
* `Test.wdomain`: the initial values and the condition's values, extended at most `n` times
  (`n` the number of instructions) by every value an extracted trace writes.

`Test.wtraces` is used by the loose-corner verdicts (`Test.looseTraces`), so their writers come
from the bytes; `Hand.*` remain as a cross-check (`Silmaril.X86.MemoryModel.Litmus.Weak.Thms`).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

/-- Steps per thread: the bound plus 64 `rep` elements. -/
def Test.wfuel (t : Test) : Nat := t.fuel + 64

/-- Every thread's candidate traces over `Weak9`, over the value domain `dom`. -/
def Test.wextractOver (t : Test) (dom : List Nat) : Option (List (List XTrace)) :=
  (t.threads.mapIdx fun k th =>
    Silmaril.X86.Litmus.wextract (t.xthread k th) dom t.wfuel).mapM id

/-- Add every value an extracted trace writes. -/
def Test.wdomStep (t : Test) (d : List Nat) : List Nat :=
  match t.wextractOver d with
  | none => d
  | some T => uniq (d ++ T.flatten.flatMap XTrace.written)

/-- `wdomStep`, at most `k` times, stopping when nothing new is written. -/
def Test.wdomIter (t : Test) : Nat → List Nat → List Nat
  | 0, d => d
  | k + 1, d =>
    let d' := t.wdomStep d
    if d'.length = d.length then d else t.wdomIter k d'

/-- The value domain of `wtraces` (as `Test.domain`, with `wextract`). -/
def Test.wdomain (t : Test) : List Nat :=
  t.wdomIter (t.threads.flatMap Thread.insns).length
    (uniq ((t.locs.map Loc.init) ++ t.cond.atoms.map Atom.value))

/-- **The candidate traces of every thread, extracted from the bytes over `Weak9`.** -/
def Test.wtraces (t : Test) : Option (List (List XTrace)) := t.wextractOver t.wdomain

end Silmaril.X86.MemoryModel.Litmus
