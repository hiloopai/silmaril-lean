module

public import Silmaril.X86.FnContract.RightRot.Defs
import Silmaril.Proofs.X86.FnContract.RightRot
/-!
# `right_rot` realizes its C signature on the open machine

The first concrete `Silmaril.Machine.SystemV.Realizes` certificate: for every entry stack pointer
`sp0`, the `clang -O0` `right_rot` bytes, run on the open machine from any System V entry in
the domain, reach a state that has returned to the caller with `eax` holding
`rightRotSpec value count`, callee-saved registers and `rsp` restored, and memory changed
only in the sixteen bytes below `sp0`. It is `FnContract.toRealizes` applied to `contract`
(`FnContract.ofDecompiled` of `Silmaril.X86.Decompile.RightRot.decompiled`); no new symbolic
execution.
-/

@[expose] public section

namespace Silmaril.X86.FnContract.RightRot

open Silmaril.Machine.Execution (Reaches)

theorem realizes (sp0 : Silmaril.X86.Word) :
    Silmaril.Machine.SystemV.Realizes signature result (writes sp0) (Domain sp0)
      (fun call final => Reaches Open.step call.initial final) :=
  Silmaril.Proofs.X86.FnContract.RightRot.realizes sp0

end Silmaril.X86.FnContract.RightRot
