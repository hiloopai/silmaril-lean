module

public import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs
import Silmaril.Proofs.Machine.SQLite.TrackA.Read.Adapter.Correspondence

public section

namespace Silmaril.Machine.SQLite.TrackA.Read.Adapter

open Silmaril.Machine.SqliteVfs

/-- Substituting the VM leaf for the staged lookup preserves the full set
of open VFS tree observations. -/
theorem lowered_observations_eq (request : Acquire) (key : Int64) (cache : PageRead.Cache) :
    (lower (stagedCall request key) cache).observes = (lower (vmCall request key) cache).observes :=
  Proofs.Machine.SQLite.TrackA.Read.Adapter.lowered_observations_eq request key cache

/-- The staged Pager handler and the composed VFS handler reach the same
result, cache, file and exchange history. The actual request/reply history
is valid for the backing and labels a complete observation of the open tree. -/
theorem interpretations_agree {Backing : Type} (backing : Handler Backing) (file : Backing)
    (cache : PageRead.Cache) (request : Acquire) (key : Int64) :
    let out := Read.runStaged backing file cache request.target request.page key
    Returns (pagerTree (stagedCall request key)) (handlePager backing cache) file out ∧
      Returns (lower (vmCall request key) cache) (handleVfs backing) file out ∧
      Trace.Valid backing file out.exchanges out.file ∧
      Observes (lower (vmCall request key) cache) out :=
  Proofs.Machine.SQLite.TrackA.Read.Adapter.interpretations_agree backing file cache request key

end Silmaril.Machine.SQLite.TrackA.Read.Adapter
