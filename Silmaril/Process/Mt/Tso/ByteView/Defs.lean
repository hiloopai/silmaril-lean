module

public import Silmaril.Process.Mt.Defs
public import Silmaril.X86.MemoryModel.Tso.Defs

@[expose] public section

namespace Silmaril.Process.Mt.Tso.ByteView

open Silmaril.X86.MemoryModel.Tso

/-- Project process TSO backing bytes and the oldest-first buffers. -/
def byteState (s : TsoS) : XState Nat :=
  ⟨fun address => s.mem.bytes.get? address, s.buf⟩

end Silmaril.Process.Mt.Tso.ByteView
