module

public import Silmaril.Machine.Abi.Conformance.SysvScalar.Sret.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.Sret

/-!
# `sysvScalar`: the result storage of a MEMORY result in admitted calls

`Admit` requires every byte of `sysvScalar.owned` (`[rdi, rdi + size)` for a MEMORY result) to
be readable, writable and apart from the stack window, the code, its data, the image and the
caller-visible objects (`Stack.owned*`). These theorems show the requirement is satisfiable and
that it refuses aliasing storage:

* `admitted`: `struct big f(void)` (24 bytes, MEMORY) entered on the leaf-arith witness state
  with RDI = `0x10000` is an admitted call, on every machine live there: the requirement is
  not vacuous. Its owned memory is exactly `[0x10000, 0x10018)` (`owned_iff`);
* `not_admitted_code`: with RDI at the code (`0x401370`), no call is admitted, whatever the
  spec;
* `not_admitted_stack`: with RDI at the return address (`rsp = 0x8ff8`), likewise;
* `not_admitted_objects`: if the spec makes a byte of the storage caller-visible, likewise.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.SysvScalar.Sret

open Silmaril.Machine.Abi.Conformance

theorem owned_iff (r : Silmaril.X86.Word) (x : Nat) :
    sysvScalar.owned sretProto (sretSt r) x ↔ r.toNat ≤ x ∧ x < r.toNat + 24 := Iff.rfl

theorem admitted (M : Mach) (hl : M.live (sretSt 0x10000).machine) :
    Admit sysvScalar M sretProto sretCode 0 (CallSpec.abiPure _ _) sretArgs (sretSt 0x10000) :=
  Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.Sret.admitted M hl

theorem not_admitted_code (M : Mach) (S : CallSpec sysvScalar.V sretProto) (a) :
    ¬ Admit sysvScalar M sretProto sretCode 0 S a (sretSt Silmaril.X86.Ladder.LeafArith.base) :=
  Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.Sret.not_admitted_code M S a

theorem not_admitted_stack (M : Mach) (S : CallSpec sysvScalar.V sretProto) (a) :
    ¬ Admit sysvScalar M sretProto sretCode 0 S a (sretSt 0x8ff8) :=
  Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.Sret.not_admitted_stack M S a

theorem not_admitted_objects (M : Mach) (S : CallSpec sysvScalar.V sretProto) (a)
    (h : S.objects a (sretSt 0x10000).machine.memory 0x10008) :
    ¬ Admit sysvScalar M sretProto sretCode 0 S a (sretSt 0x10000) :=
  Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.Sret.not_admitted_objects M S a h

end Silmaril.Machine.Abi.Conformance.SysvScalar.Sret

end
