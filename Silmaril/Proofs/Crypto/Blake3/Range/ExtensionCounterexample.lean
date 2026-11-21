module

public import Silmaril.Crypto.Blake3.Range.Check.Defs
public import Silmaril.Crypto.Blake3.Range.Extension.Defs
public import Silmaril.Semantics.Naming.ByteRange.Extension.Thms
import Silmaril.Proofs.Crypto.Blake3.Range.Extension
import Silmaril.Proofs.Crypto.Blake3.Words
import Init.Data.List.Find

public section

namespace Silmaril.Proofs.Crypto.Blake3.Range.ExtensionCounterexample

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming
open Silmaril.Semantics.Naming.ByteRange (Fact Observations)

private def tag (index : Nat) : CV := #v[UInt32.ofNat index, 0, 0, 0, 0, 0, 0, 0]

private def shortLeaf : Input := chunkInput false true true 1 iv [1]
private def leftFork : Input := parentInput false (tag 19) (tag 15)
private def rootFork : Input := parentInput true (tag 17) (tag 16)

/-- Sixteen block inputs for a full zero chunk at counter 1, then the short
chunk at counter 1, the non-ROOT fork, and the ROOT fork. All other inputs fail. -/
private def rows : List Input := (List.range 16).map (fun index =>
    chunkInput false (index == 0) (index == 15) 1 (if index = 0 then iv else tag (index - 1))
      (List.replicate 64 0)) ++ [shortLeaf, leftFork, rootFork]

private def run (input : Input) : Option CV := (rows.findIdx? fun row => decide (row = input)).map tag
private def rel : Compression := Compression.graph run
private def digest : Bytes := digestBytes (tag 18)

private def smallOpening : Opening := .fork (.opaque (tag 17)) (.leaf [1])
private def largeOpening : Opening :=
  .fork (.fork (.opaque (tag 19)) (.leaf (List.replicate 1024 0))) (.opaque (tag 16))

private theorem free : ¬ Compression.Collision rel := by
  rintro ⟨lhs, rhs, output, ne, left, right⟩
  change run lhs = some output at left
  change run rhs = some output at right
  unfold run at left right
  obtain ⟨li, lfind, lout⟩ := Option.map_eq_some_iff.mp left
  obtain ⟨ri, rfind, rout⟩ := Option.map_eq_some_iff.mp right
  obtain ⟨lbound, lhit, _⟩ := List.findIdx?_eq_some_iff_getElem.mp lfind
  obtain ⟨rbound, rhit, _⟩ := List.findIdx?_eq_some_iff_getElem.mp rfind
  have length : rows.length = 19 := by decide +kernel
  have tags := congrArg (fun cv : CV => cv[0].toNat) (lout.trans rout.symm)
  change li % 4294967296 = ri % 4294967296 at tags
  have indices : li = ri := by omega
  subst ri
  exact ne ((of_decide_eq_true lhit).symm.trans (of_decide_eq_true rhit))

private theorem checkedSmall : Checked rel 1025 digest 1024 [1] ∧ CheckedEOF rel 1025 digest := by
  have got : (verifyRangeWithEOF? run 1025 1025 digest smallOpening 1024 1).map Subtype.val = some [1] := by
    decide +kernel
  obtain ⟨result, _, eq⟩ := Option.map_eq_some_iff.mp got
  exact ⟨eq ▸ result.property.1, result.property.2.1⟩

private theorem checkedLarge : Checked rel 2049 digest 1024 [0] := by
  have got : (verifyRange? run 2049 2049 digest largeOpening 1024 1).map Subtype.val = some [0] := by
    decide +kernel
  obtain ⟨result, _, eq⟩ := Option.map_eq_some_iff.mp got
  exact eq ▸ result.property.1

private theorem smallGeometry : geometry 0 1025 = .fork (.leaf 0 1024) (.leaf 1 1) := by
  rw [geometry, dite_eq_right (by decide : ¬ 1025 ≤ 1024)]
  have split : splitBytes 1025 = 1024 := by decide +kernel
  rw [split, geometry, dite_eq_left (by decide : 1024 ≤ 1024)]
  change Shape.fork (.leaf 0 1024) (geometry 1 1) = _
  rw [geometry, dite_eq_left (by decide : 1 ≤ 1024)]

private theorem chain_final {table : Compression} {root first : Bool} {chunk more : Nat}
    {cv output : CV} {bytes : Bytes} (chain : Chain table root chunk more first cv bytes output) :
    ∃ began prior tail, table (chunkInput root began true chunk prior tail) output := by
  induction chain with
  | last _ hit => exact ⟨_, _, _, hit⟩
  | step _ _ _ ih => exact ih

private theorem no_name {extension : Compression} (extendsRel : rel.Extends extension)
    (collisionFree : ¬ extension.Collision) (bytes : Bytes) : ¬ Named extension digest bytes := by
  intro named
  obtain ⟨opening, ⟨valid, cv, trace, eq⟩, edge⟩ := checkedSmall.2
  have eof : CheckedEOF extension 1025 digest :=
    ⟨opening, ⟨valid, cv, Extension.trace_mono extendsRel trace, eq⟩, edge⟩
  have extent := (eof.extentOrCollision named).resolve_right collisionFree
  obtain ⟨_, output, full, digestEq⟩ := named
  have sameOutput : output = tag 18 := digest_inj digestEq
  subst output
  rw [← extent, smallGeometry] at full
  change Trace extension true (.fork (.leaf 0 1024) (.leaf 1 1))
    (.fork (.leaf (bytes.take 1024)) (.leaf (bytes.drop 1024))) (tag 18) at full
  cases full with
  | fork left _ parent =>
    have sameParent := Extension.same_input collisionFree parent
      (extendsRel (show rel rootFork (tag 18) by change run rootFork = some (tag 18); decide +kernel))
    obtain ⟨sameLeft, _⟩ := parent_inj (show _ = parentInput true (tag 17) (tag 16) from sameParent)
    rw [sameLeft] at left
    cases left with
    | leaf _ chain =>
      obtain ⟨began, prior, tail, last⟩ := chain_final chain
      have sameFinal := Extension.same_input collisionFree last
        (extendsRel (show rel leftFork (tag 17) by change run leftFork = some (tag 17); decide +kernel))
      have flags := congrArg Input.flags sameFinal
      cases began with
      | false => exact (by decide : (2 : UInt32) ≠ 4) flags
      | true => exact (by decide : (3 : UInt32) ≠ 4) flags

theorem blocked : ∃ run digest,
    let base := Compression.graph run
    base.Canonical ∧ ¬ base.Collision ∧ Checked base 1025 digest 1024 [1] ∧ CheckedEOF base 1025 digest ∧
    ∀ extension, base.Extends extension → (¬ extension.Collision) → ∀ bytes, ¬ Named extension digest bytes :=
  ⟨run, digest, Compression.graph_canonical run, free, checkedSmall.1, checkedSmall.2, fun _ => no_name⟩

theorem overlap : ∃ run digest,
    let base := Compression.graph run
    base.Canonical ∧ ¬ base.Collision ∧ Checked base 1025 digest 1024 [1] ∧ Checked base 2049 digest 1024 [0] ∧
    ¬ ∃ bytes, (Fact.range 1024 [1]).Holds bytes ∧ (Fact.range 1024 [0]).Holds bytes := by
  refine ⟨run, digest, Compression.graph_canonical run, free, checkedSmall.1, checkedLarge, ?_⟩
  rintro ⟨bytes, left, right⟩
  have lhs := left.2.2 1024 1 ⟨0, rfl, rfl⟩
  have rhs := right.2.2 1024 0 ⟨0, rfl, rfl⟩
  exact (by decide : (1 : UInt8) ≠ 0) (Option.some.inj (lhs.symm.trans rhs))

end Silmaril.Proofs.Crypto.Blake3.Range.ExtensionCounterexample
