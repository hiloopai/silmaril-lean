module

public import Silmaril.X86.Litmus.Extract.Defs

/-!
# The pinned code of the C11 refcount library

**Generated** by `examples/litmus-c/rc/pin.sh` from the pinned objects
`examples/litmus-c/rc/obj/*.o` (gcc 13.3.0, `-O2 -fcf-protection=none
-fno-asynchronous-unwind-tables -g0`; `objects.sha256`). Each list is one function's bytes
from its symbol up to, not including, its final `ret` (`C3`). `pin.sh --check` regenerates
this file from the objects and compares it byte for byte. Do not edit.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Rc.Code

/-- Bytes from a list of naturals. -/
def bs (l : List Nat) : List (BitVec 8) := l.map (BitVec.ofNat 8)

/-- `rc_clone` (`rc.o`, 4 bytes before its `ret`). -/
def rcClone : List (BitVec 8) := bs
  [0xf0, 0x83, 0x07, 0x01]

/-- `rc_drop` (`rc.o`, 6 bytes before its `ret`). -/
def rcDrop : List (BitVec 8) := bs
  [0xf0, 0x83, 0x2f, 0x01, 0x74, 0x0a]

/-- `rc_publish` (`rc.o`, 11 bytes before its `ret`). -/
def rcPublish : List (BitVec 8) := bs
  [0x8b, 0x47, 0x04, 0x89, 0x06, 0xf0, 0x83, 0x2f, 0x01, 0x74, 0x05]

/-- `rc_share2` (`rc.o`, 14 bytes before its `ret`). -/
def rcShare2 : List (BitVec 8) := bs
  [0xf0, 0x83, 0x07, 0x01, 0xf0, 0x83, 0x07, 0x01, 0xf0, 0x83, 0x2f, 0x01, 0x74, 0x02]

end Silmaril.X86.Concurrency.Cir.Rc.Code
