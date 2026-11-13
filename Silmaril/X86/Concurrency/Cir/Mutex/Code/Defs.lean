module

public import Silmaril.X86.Litmus.Extract.Defs

/-!
# The pinned code of the mutex

**Generated** by `examples/litmus-c/mutex/pin.sh` from the pinned objects
`examples/litmus-c/mutex/obj/*.o` (gcc 13.3.0, `-O2 -fcf-protection=none
-fno-asynchronous-unwind-tables -g0`; `objects.sha256`). Each list is one function's bytes
from its symbol up to, not including, its final `ret` (`C3`). `pin.sh --check` regenerates
this file from the objects and compares it byte for byte. Do not edit.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex.Code

/-- Bytes from a list of naturals. -/
def bs (l : List Nat) : List (BitVec 8) := l.map (BitVec.ofNat 8)

/-- `mutex_lock` (`mutex.o`, 32 bytes before its `ret`). -/
def mutexLock : List (BitVec 8) := bs
  [0xba, 0x01, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x00, 0x89, 0xd0, 0x87, 0x07, 0x85, 0xc0, 0x74,
   0x10, 0x8b, 0x07, 0x85, 0xc0, 0x74, 0xf2, 0xf3, 0x90, 0xeb, 0xf6, 0x66, 0x0f, 0x1f, 0x44,
   0x00, 0x00]

/-- `mutex_unlock` (`mutex.o`, 4 bytes before its `ret`). -/
def mutexUnlock : List (BitVec 8) := bs
  [0x31, 0xc0, 0x87, 0x07]

/-- `mutex_unlock_sc` (`mutex.o`, 4 bytes before its `ret`). -/
def mutexUnlockSc : List (BitVec 8) := bs
  [0x31, 0xc0, 0x87, 0x07]

end Silmaril.X86.Concurrency.Cir.Mutex.Code
