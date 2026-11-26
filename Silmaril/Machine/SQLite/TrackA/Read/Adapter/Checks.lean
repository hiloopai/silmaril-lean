module

import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
import Silmaril.Machine.SQLite.TrackA.Read.Checks
import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms
meta import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
meta import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs
meta import Silmaril.Semantics.TrackA.Interaction.Defs

namespace Silmaril.Machine.SQLite.TrackA.Read.Adapter

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics.TrackA.Interaction (Signature ITree Coalgebra)

-- Evaluate the actual handled trees through the single acquisition step.
private def run {S : Signature} (tree : ITree S LeafResult)
    (handler : Coalgebra.Handler S (Recorded FileState)) (file : FileState) :
    Option (Read.Outcome FileState) :=
  let interpreted := tree.unfold.handle (T := VfsSignature) handler
  let initial := (tree.root (), file, [])
  let final := match interpreted initial with
    | .tau next => next
    | _ => initial
  match interpreted final with
  | .ret (result, cache) => some ⟨result, final.2.1, cache, final.2.2⟩
  | _ => none

private def matchesOutcome (request : Acquire) (file : FileState) (bytes : Bytes)
    (expected : Option Value) (cold : Bool) (outcome : Read.Outcome FileState) : Bool :=
  outcome.result.toOption == some expected && outcome.file == file &&
    outcome.cache request.target == some (.resident request.page bytes) &&
    match outcome.exchanges with
    | [] => !cold
    | [⟨.read handle offset count, .ok data⟩] =>
        cold && handle == request.page.handle && offset == 512 && count == 512 && data == bytes
    | _ => false

private def caseChecks (key : Int64) (expected : Option Value) : Option Bool := do
  let snapshot : WriteProfile.Snapshot := ⟨[⟨42, 7⟩], by decide⟩
  let source ← (WriteProfile.Image.encode snapshot).toOption
  let image ← File.parse? source
  let view ← image.page? 2
  let file : FileState := ⟨source.toList, some .readOnly, 0⟩
  let request : Acquire := ⟨0, ⟨⟨0⟩, 2, image.header.pageSize⟩⟩
  let bytes := view.materialize.toList
  let vacant : PageRead.Cache := fun slot => if slot = 0 then some .vacant else none
  let backing := readOnly 1024
  let staged cache := run (pagerTree (stagedCall request key)) (handlePager backing cache) file
  let composed cache := run (lower (vmCall request key) cache) (handleVfs backing) file
  let stagedCold ← staged vacant
  let composedCold ← composed vacant
  let stagedWarm ← staged stagedCold.cache
  let composedWarm ← composed composedCold.cache
  return matchesOutcome request file bytes expected true stagedCold &&
    matchesOutcome request file bytes expected true composedCold &&
    matchesOutcome request file bytes expected false stagedWarm &&
    matchesOutcome request file bytes expected false composedWarm

#guard (caseChecks 42 (some (.integer 7))) == some true
#guard (caseChecks 41 none) == some true

#print axioms lowered_observations_eq
#print axioms interpretations_agree

end Silmaril.Machine.SQLite.TrackA.Read.Adapter
