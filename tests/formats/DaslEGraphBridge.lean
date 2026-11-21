module

import Silmaril.Formats.Dasl.EGraph.Thms
meta import Silmaril.Formats.Dasl.EGraph.Defs

open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.PER.EGraph
open Silmaril.Formats.Dasl.EGraph Silmaril.Formats.Dasl.IndexSequence

private def tinyTerms : Array (Node Bool Nat) := #[⟨false, []⟩, ⟨true, []⟩]
private def tiny : Dag Bool := ⟨tinyTerms, by decide⟩
private def noSeeds : Seeds tiny.val.size := fun _ _ => false

private def collapsed : Table tiny String 1 where
  rows := ⟨[("left", 0), ("right", 0)], by decide⟩
  width := rfl

private def separates : Model tiny noSeeds where
  per := PER.kernel fun id => tiny.val[id].label
  reflexive := fun _ => rfl
  asserts := fun _ _ impossible => Bool.noConfusion impossible
  congruent := fun _ _ label _ => label

theorem collapsed_unsound : ¬ tiny.Sound noSeeds collapsed.partition := by
  intro sound
  let left : tiny.Id := ⟨0, by decide⟩
  let right : tiny.Id := ⟨1, by decide⟩
  have related : collapsed.partition.per.rel left right := rfl
  exact Bool.noConfusion (show false = true from sound related separates)

private def namesFor (byRow : List String) : String → Nat → Prop :=
  fun name id => byRow[id]? = some name

private instance (byRow : List String) : DecidableRel (namesFor byRow) :=
  fun name id => inferInstanceAs (Decidable (byRow[id]? = some name))

private def index : Encode.TotalCodec Nat (Shallow String) :=
  ⟨fun count => Encode.list.encode (List.replicate count .null),
    fun tree => (Encode.list.decode? tree).map List.length,
    fun count => by rw [Encode.list.recovers]; simp⟩

private def expect (success : Bool) (label : String) : IO Unit :=
  unless success do throw (IO.userError label)

public def main : IO Unit := do
  let tinyNames := ["left", "right"]
  expect ((checkTable? tiny (namesFor tinyNames) collapsed.rows).isSome) "collapsed table is structurally valid and named"
  expect ((certify? tiny noSeeds (namesFor tinyNames) [] collapsed.rows).isNone) "empty evidence must not certify collapse"
  let terms := (#[⟨"a", []⟩, ⟨"b", []⟩, ⟨"f", [0]⟩, ⟨"f", [1]⟩] : Array (Node String Nat))
  let some dag := checkDag? terms | throw (IO.userError "fixture term DAG")
  let idAt := termId? dag.val.size
  let some termA := idAt 0 | throw (IO.userError "missing a")
  let some termB := idAt 1 | throw (IO.userError "missing b")
  let some termFA := idAt 2 | throw (IO.userError "missing f(a)")
  let some termFB := idAt 3 | throw (IO.userError "missing f(b)")
  let names := ["A", "B", "FA", "FB"]
  let seeds : Seeds dag.val.size := fun left right => left == termA && right == termB
  let partition := fun classOf => (⟨dag.val.size, classOf⟩ : Partition dag.val.size)
  let seeded := partition fun id => if id = termB then termA else id
  let rebuilt := partition fun id => if id = termFB then termFA else seeded.classOf id
  let log : List (Step dag.val.size) := [⟨termA, termB, .seed, seeded⟩, ⟨termFA, termFB, .collision, rebuilt⟩]
  let entries : Entries String := [("A", 2), ("B", 2), ("FA", 1), ("FB", 1)]
  let some rows := check? (.classId 3) entries | throw (IO.userError "fixture class bounds")
  expect ((certify? dag seeds (namesFor names) [] rows).isNone) "a seed assertion alone is not an executed merge"
  expect ((certify? dag seeds (namesFor names) log.reverse rows).isNone) "collision cannot precede its child merge"
  expect ((certify? dag seeds (namesFor names.reverse) log rows).isNone) "wrong name-to-term witness"
  let some short := check? (.classId 3) entries.tail | throw (IO.userError "short fixture bounds")
  expect ((checkTable? dag (namesFor names) short).isNone) "one row required per witness"
  let width : { size : Nat // 0 < size } := ⟨3, by decide⟩
  let entry := entryCodec Encode.text index
  for codec in [flat entry, paged width entry, parallel (flat Encode.text) (flat index),
      parallel (paged width Encode.text) (paged ⟨2, by decide⟩ index)] do
    let raw := (checked (.classId 3) codec).encode rows
    let some certificate := decodeCertified? dag seeds (namesFor names) log 3 codec raw |
      throw (IO.userError "seed and rebuild certificate did not transport")
    let observed := certificate.val.partition
    expect (certificate.val.rows.val == entries && (observed.classOf termA).val == 2 &&
      (observed.classOf termFB).val == 1) "preserve the table's own class numbering"
    expect (decide (observed.classOf termA = observed.classOf termB ∧
      observed.classOf termFA = observed.classOf termFB ∧ observed.classOf termA ≠ observed.classOf termFA))
      "exact replayed equivalence, despite renumbering the classes"
    expect (decide (dag.Rebuilt observed)) "rebuilt on witnessed terms"
