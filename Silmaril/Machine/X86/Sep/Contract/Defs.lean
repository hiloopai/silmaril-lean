module

public import Silmaril.Machine.X86.Sep.SysV.Defs
public import Silmaril.Machine.X86.FnContract.Defs

/-!
# System V specs as WP3 function contracts: the contract spec

`FnSpec.contractSpec S C entry` is the `Silmaril.Machine.X86.FnContract.Spec` of a System V spec
on the open machine; `FnSpec.Sat.toFnContract` (in `Sep/SysV/Thms.lean`) packages it with its
totality proof.

* entry: some logical argument `x` and fragment `h` of the entry state satisfy
  `C ∗ S.SysVPre x entry rsp ret` (with `ret` the return address at `[rsp]`), with room for the
  budget, and `h` owns neither the mapping list nor a callee-saved register (`Avoids`);
* footprint: the byte addresses owned by such a fragment;
* post: `C ∗ S.SysVPost x rsp ret` holds of part of the final state, for some `x`.

The postcondition is not tied to the `x` of the entry condition: for a spec whose `Arg` is not
determined by the entry state, this contract is weaker than the spec.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Sep

open Silmaril.X86 (MState Word sysv64)
open Frag (Le)

/-- The fragment owns neither the mapping list nor a callee-saved register. -/
def Avoids (h : Frag) : Prop := h .regions = none ∧ ∀ r ∈ sysv64.calleeSaved, h (.reg r) = none

namespace FnSpec

/-- The entry condition of the contract of a System V spec, for argument `x` and fragment `h`. -/
def ContractEntry (S : FnSpec) (C : SProp) (entry : Word) (m : MState) (x : S.Arg) (h : Frag) :
    Prop :=
  (C ∗ S.SysVPre x entry (m.core.read .rsp) (Silmaril.Machine.X86.Open.retOf m.core m.memory)) h ∧
    Le h (toFrag m) ∧ S.stack ≤ (m.core.read .rsp).toNat ∧ Avoids h

/-- **The contract spec of a System V spec.** -/
def contractSpec (S : FnSpec) (C : SProp) (entry : Word) : Silmaril.Machine.X86.FnContract.Spec MState where
  entry m := ∃ x h, S.ContractEntry C entry m x h
  footprint m a := ∃ x h, S.ContractEntry C entry m x h ∧ (h (.mem a)).isSome
  post m fin := ∃ x, Holds (C ∗ S.SysVPost x (m.core.read .rsp)
    (Silmaril.Machine.X86.Open.retOf m.core m.memory)) fin

end FnSpec

end Silmaril.Machine.X86.Sep
