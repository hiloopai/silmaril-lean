module

public import Silmaril.Machine.Abi.OpenMachine.Defs
/-! # The FFI thread pointer and the machine's FS base

the ABI model's `Ffi.State` (`Silmaril.Machine.SystemV.Abi.Ffi.Defs`, not edited here) carries its own
`fsBase : BitVec 64` next to `machine : MState`, and `Ffi.Return.threadPointer` is
`final.fsBase = call.initial.fsBase`. The field that `%fs:` operands actually read is
`machine.core.fsBase` (`Silmaril.X86.Ext.Base.value .fs`). Nothing relates the two.

Both consumers on the open machine, A's `Open.ffiExecute` and C's `OpenMachine.callModel`,
build the final state as `{ initial with machine := … }`. So five `Ffi.Return` /
`Win64.Returns` obligations **hold by the model, whatever the code does**:

| obligation | field | why it holds |
| --- | --- | --- |
| `threadPointer` | `fsBase` (the FFI copy) | carried unchanged |
| `direction` | `direction` | carried unchanged (and `Entry.direction` gives `false`) |
| `x87Mode` | `x87Mode` | carried unchanged (and `Entry.x87Mode` gives `true`) |
| `mxcsrControl` | `mxcsr` | carried unchanged |
| `x87Control` | `x87Control` | carried unchanged |

(`Thms.ffiExecute_carried`, `Thms.callModel_carried`.) The same holds for `vectors` and `x87`
(`Win64.Returns.vectorsSaved`), which `ffiExecute`'s docstring already discloses. These are
statements about the **model**, not proved about the code: they are sound only because the
integer models (`X86.Ext`, `Ext8`) have no instruction that reads or writes that state, and
they would silently stay true for code that did.

For the thread pointer this module gives the code-level reading:

* `FsCoherent s`: the **entry invariant** `s.fsBase = s.machine.core.fsBase`. A call whose
  initial state meets it has an FFI thread pointer that is the real one.
* `Task.openStepKeepsFs`: no open-machine step writes `core.fsBase` (Silmaril's
  `Ext.Semantics` says "`fsBase` is never written", but proves no lemma; open).
* `Thms.ffiExecute_fsBase`, `Thms.callModel_fsBase` (conditional on the Task): from a
  coherent initial state, the final state is coherent and its **machine** FS base equals the
  initial one, so `Return.threadPointer` then also holds of the register `%fs:` reads.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.FsBase

open Silmaril.X86 (MState)
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86

/-- The entry invariant: the FFI thread pointer is the machine's FS base. -/
def FsCoherent (s : Ffi.State) : Prop := s.fsBase = s.machine.core.fsBase

/-- The FFI-only control state of `s'` is that of `s` (the part the open-machine models carry
unchanged). -/
structure Carried (s s' : Ffi.State) : Prop where
  fsBase : s'.fsBase = s.fsBase
  direction : s'.direction = s.direction
  x87Mode : s'.x87Mode = s.x87Mode
  mxcsr : s'.mxcsr = s.mxcsr
  x87Control : s'.x87Control = s.x87Control
  vectors : s'.vectors = s.vectors
  x87 : s'.x87 = s.x87

/-- Open goal: no step of the open machine writes the FS base. -/
def Task.openStepKeepsFs : Prop :=
  ∀ m m' : MState, Open.step m = some m' → m'.core.fsBase = m.core.fsBase

end Silmaril.Machine.Abi.FsBase
