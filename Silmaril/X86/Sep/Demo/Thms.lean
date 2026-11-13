module

public import Silmaril.X86.Sep.Demo.Defs
public import Silmaril.X86.Sep.SysV.Thms
import Silmaril.Proofs.X86.Sep.Demo.Leaf
import Silmaril.Proofs.X86.Sep.Demo.Md5Memcpy
import Silmaril.Proofs.X86.Sep.Demo.NonVacuity
/-!
# Example System V specs: proofs

* `leaf_sat`: the addition leaf meets `leafSpec`, from `Silmaril.X86.Leaf.leaf_returns`.
* `caller_sat`: the caller `call leaf; ret` meets `callerSpec`, by `call_rule` applied to
  `leaf_sat` and `ret_step`, **without** `Leaf.caller_returns`; `caller_returns_open` is the
  resulting state-level statement on the open machine (the analogue of
  `Leaf.caller_returns`). Both use `SatWith (fun _ => True)`: the caller's own call site is not
  16-byte aligned, and the base model has no alignment checks.
* `md5_memcpy_SPEC`: `MD5_memcpy` meets `md5Spec` under the System V ABI, from the existing
  `Decompile.Md5Memcpy.md5_memcpy_returns` certificate, with no new symbolic execution;
  `md5_memcpy_contract` is the same as a WP3 `FnContract` on the open machine.
* `leafSpec_pre_satisfiable`: non-vacuity of the template. A concrete machine state (leaf
  code at `0x400000`, `rsp = 0x7000`, return address `0x401000`, `rdi = 2`, `rsi = 3`)
  satisfies the leaf's code and System V precondition, so `leaf_sat` is not vacuously true.
  (No such witness is given for `md5Spec` or `callerSpec`.)
-/

@[expose] public section

namespace Silmaril.X86.Sep.Demo

open Silmaril.X86 (MState Word)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.Sep


/-- **The addition leaf meets `leafSpec`.** -/
theorem leaf_sat (leaf : Word) :
    leafSpec.SatWith Silmaril.X86.Open.isa (fun _ => True)
      (codePt leaf.toNat Silmaril.X86.Leaf.bytes) leaf :=
  Silmaril.Proofs.X86.SepDemo.leaf_sat leaf

/-- **The caller meets `callerSpec`**, by the call rule. -/
theorem caller_sat {caller leaf : Word} {rel : BitVec 32}
    (hf : caller + 5#64 + rel.signExtend 64 = leaf) (hfit : caller.toNat + 6 ≤ 2 ^ 64) :
    callerSpec.SatWith Silmaril.X86.Open.isa (fun _ => True)
      (codePt caller.toNat (Silmaril.X86.Leaf.callerBytes rel) ∗
        codePt leaf.toNat Silmaril.X86.Leaf.bytes) caller :=
  Silmaril.Proofs.X86.SepDemo.caller_sat hf hfit

/-- **`Leaf.caller_returns`, re-derived on the open machine** from `leaf_returns` and the call
rule. -/
theorem caller_returns_open {caller leaf : Word} {rel : BitVec 32}
    (hf : caller + 5#64 + rel.signExtend 64 = leaf) (hfit : caller.toNat + 6 ≤ 2 ^ 64)
    {a b sp ret : Word} (hst : 8 ≤ sp.toNat) {m : MState} {h : Frag}
    (hpre : ((codePt caller.toNat (Silmaril.X86.Leaf.callerBytes rel) ∗
        codePt leaf.toNat Silmaril.X86.Leaf.bytes) ∗ callerSpec.SysVPre (a, b) caller sp ret) h)
    (hl : Frag.Le h (toFrag m)) :
    ∃ fin, Reaches Silmaril.X86.Open.step m fin ∧ fin.core.rip = ret ∧
      fin.core.read .rax = a + b ∧ fin.core.read .rsp = sp + 8#64 ∧
      ∀ l, h l = none → toFrag fin l = toFrag m l :=
  Silmaril.Proofs.X86.SepDemo.caller_returns_open hf hfit hst hpre hl

/-- **`MD5_memcpy` meets `md5Spec`** (`md5_memcpy_SPEC`). -/
theorem md5_memcpy_SPEC (entry : Word) :
    md5Spec.Sat Silmaril.X86.Open.isa (codePt entry.toNat Silmaril.X86.Decompile.Md5Memcpy.code) entry :=
  Silmaril.Proofs.X86.SepDemo.md5_memcpy_SPEC entry

/-- `MD5_memcpy` as a total WP3 function contract on the open machine. -/
def md5_memcpy_contract (entry : Word) : Silmaril.X86.FnContract Silmaril.X86.Open.isa :=
  (md5_memcpy_SPEC entry).toFnContract Silmaril.X86.Sep.flat_open

/-- **The System V template is satisfiable**: a concrete machine state satisfies the leaf's
code and precondition (`Proofs/.../Demo/NonVacuity.lean`, which also derives the concrete
run returning `rax = 5` from `leaf_sat`). -/
theorem leafSpec_pre_satisfiable :
    ∃ (m : MState) (h : Frag),
      (codePt (0x400000 : Word).toNat Silmaril.X86.Leaf.bytes ∗
        leafSpec.SysVPre ((2 : Word), (3 : Word)) 0x400000 0x7000 0x401000) h ∧
      Frag.Le h (toFrag m) :=
  ⟨_, Silmaril.Proofs.X86.SepDemo.NonVacuity.leaf_pre_holds⟩

end Silmaril.X86.Sep.Demo
