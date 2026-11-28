module

public import Silmaril.Process.Mt.Tso.ByteView.Defs
import Silmaril.Proofs.Process.Mt.Tso.ByteView

public section

namespace Silmaril.Process.Mt.Tso.ByteView

open Silmaril.Process (ByteMemory Memory)
open Silmaril.Process.Mt (TsoS BufEntry overlay tso)
open Silmaril.X86.MemoryModel.Tso

/-- The process overlay and byte FIFO model forward the same backing byte. -/
theorem view_projects (s : TsoS) (tid address : Nat) :
    (tso.view s tid).bytes.get? address = viewMem (byteState s) tid address :=
  Silmaril.Proofs.Process.Mt.Tso.ByteView.view_projects s tid address

/-- A silent process step flushes the oldest FIFO entry and preserves mapping regions. -/
theorem silent_projects {s t : TsoS} (edge : tso.silent s t) :
    XFlush (byteState s) (byteState t) ∧ t.mem.regions = s.mem.regions :=
  Silmaril.Proofs.Process.Mt.Tso.ByteView.silent_projects edge

/-- Finite silent process paths project to finite FIFO flush paths and preserve mapping regions. -/
theorem silent_path_projects {s t : TsoS} (path : Relation.ReflTransGen tso.silent s t) :
    XFlushes (byteState s) (byteState t) ∧ t.mem.regions = s.mem.regions :=
  Silmaril.Proofs.Process.Mt.Tso.ByteView.silent_path_projects path

end Silmaril.Process.Mt.Tso.ByteView
