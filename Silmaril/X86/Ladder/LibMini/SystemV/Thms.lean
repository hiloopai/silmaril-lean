module

public import Silmaril.X86.Ladder.LibMini.SystemV.Defs
public import Silmaril.X86.Ladder.LibMini.Thms
public import Silmaril.X86.FnContract.SystemV.Thms
import Silmaril.Proofs.X86.Ladder.LibMini.Realizes

/-!
# `libmini`: integer System V certificates

The state-level contracts of `memcpy`, `memset` and `strlen` (`Ladder.LibMini.Thms`) as integer
System V `Realizes` certificates, through `FnContract.toRealizes` with the C signatures of
`SystemV/Defs.lean`; the domain of each is the contract's entry condition. `strlen`'s result is
not a function of its argument, so its certificate is indexed by the string length `k`, which
the domain fixes. Proofs in `Silmaril/Proofs/X86/Ladder/LibMini/Realizes.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.LibMini

open Silmaril.X86 (Word)
open Silmaril.X86.Stencils.ByteLoop

theorem memcpy_realizes (entry : Word) :
    Silmaril.Machine.SystemV.Realizes sigCopy firstResult blockWrites
      (fun _ call => (copyContract memcpyCode entry).entry call.initial)
      (fun call final => Silmaril.Machine.Execution.Reaches Silmaril.X86.Open.step
        call.initial final) :=
  Silmaril.Proofs.X86.Ladder.LibMini.memcpy_realizes entry

theorem memset_realizes (entry : Word) :
    Silmaril.Machine.SystemV.Realizes sigFill firstResult blockWrites
      (fun _ call => (fillContract memsetCode entry).entry call.initial)
      (fun call final => Silmaril.Machine.Execution.Reaches Silmaril.X86.Open.step
        call.initial final) :=
  Silmaril.Proofs.X86.Ladder.LibMini.memset_realizes entry

theorem strlen_realizes (entry : Word) (k : Nat) :
    Silmaril.Machine.SystemV.Realizes sigScan (fun _ => BitVec.ofNat 64 k) (fun _ _ => False)
      (fun _ call => (scanContract strlenCode entry).entry call.initial ∧
        CStr call.initial.memory (arg0 call.initial) k)
      (fun call final => Silmaril.Machine.Execution.Reaches Silmaril.X86.Open.step
        call.initial final) :=
  Silmaril.Proofs.X86.Ladder.LibMini.strlen_realizes entry k

end Silmaril.X86.Ladder.LibMini
