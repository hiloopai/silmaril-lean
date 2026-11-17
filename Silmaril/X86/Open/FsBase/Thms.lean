module

public import Silmaril.X86.Open9.Defs
import Silmaril.Proofs.X86.Open.FsBase

/-!
# No step of the open machines writes the FS base

`State.fsBase` is the hidden base of the FS segment. `fs:` operands read it
(`Ext.Base.value .fs`); no instruction of `X86.Ext`, `Ext8` or `Ext9` writes it (the model
has no `wrfsbase` and no MSR writes). So it is a parameter of every open-machine run:

* `Open.step_fsBase`: a step of the open machine over `Ext8` keeps `core.fsBase`;
* `Open9.step_fsBase`: so does a step of the open machine over `Ext9`.

Proofs: `Silmaril.Proofs.X86.Open.FsBase` (one lemma per state helper, then a case split on
the instruction). This header imports only the `Open9` definitions, so it does not pull in
the function-contract or ABI closures.
-/

@[expose] public section

namespace Silmaril.X86.Open

/-- No step of the open machine writes the FS base. -/
theorem step_fsBase {m m' : MState} (h : step m = some m') : m'.core.fsBase = m.core.fsBase :=
  Silmaril.Proofs.X86.Open.FsBase.openStep_fsBase m m' h

end Silmaril.X86.Open

namespace Silmaril.X86.Open9

/-- No step of the open machine over `Ext9` writes the FS base. -/
theorem step_fsBase {m m' : MState} (h : step m = some m') : m'.core.fsBase = m.core.fsBase :=
  Silmaril.Proofs.X86.Open.FsBase.open9Step_fsBase m m' h

end Silmaril.X86.Open9
