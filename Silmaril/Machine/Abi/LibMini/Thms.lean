module

public import Silmaril.Machine.Abi.LibMini.Defs
public import Silmaril.Machine.Abi.OpenMachine.Thms
public import Silmaril.Machine.Abi.CallFootprint.Thms
public import Silmaril.X86.Ladder.LibMini.Thms
import Silmaril.Proofs.Machine.Abi.LibMini.Basic
/-! # libmini against the System V comorphism: theorems

PROVED (standard axioms; proofs in `Silmaril.Proofs.Machine.Abi.LibMini.Basic`):

* `strlen_sysv_sat`: **ABI correctness of libmini's `strlen` in the institution sense.**
  For every System V profile, every load address `entry` and every length `k`, the decoded
  `strlen` satisfies the System V translation of "returns `k`" (`strlenC k`) under the
  open machine's first-return call relation `callModel`, on entry states whose argument
  points to a NUL-terminated string of length `k`, with the code loaded at `entry`, the
  entry at `entry` and the return address outside the code (`StrlenRoom`).
* `memcpy_sysv_sat`: the same for `memcpy` and "returns its first argument" (`memcpyC`)
  on `MemcpyRoom` (buffers readable/writable and apart). The copy itself is not a
  value-level sentence (see `Defs`); it is in `memcpy_ffiRealizesCall` and in `copySpec`.
* `strlen_ffiRealizes`: per length `k`, the ABI model's typed `Ffi.Realizes` for
  `usize strlen(const char *)` with result `k` and empty footprint.
* `strlen_ffiRealizesCall`: **the exported form**: one call-dependent `FfiRealizesCall` whose
  result is `cstrLen` of the argument string (the round-2 `RealizesCall` design, now on the
  typed FFI signature and consumed by rung 12's link-edge theorem).
* `memcpy_ffiRealizesCall`: `memcpy` as an `FfiRealizesCall` with the call-dependent
  footprint `[rdi, rdi + rdx)` and result its first argument.

All five are derived from track A's stencil certificates (`strlen_strict`/`strlen_total`,
`memcpy_strict`/`memcpy_total`), the same certificates the separation-logic `FnSpec`s
`scanSpec`/`copySpec` (and so rung 12's link logic) are derived from.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.LibMini

open Silmaril.X86 (Word)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Stencils.ByteLoop (arg0 arg2)
open Silmaril.Machine.Abi.SystemV (sysv Options)
open Silmaril.Machine.Abi.OpenMachine (callModel)

/-- `strlen`'s stencil contract as a total WP3 contract on the open machine. -/
def strlenFn (entry : Word) : FnContract Open.isa :=
  ⟨Silmaril.X86.Stencils.ByteLoop.scanContract Silmaril.X86.Ladder.LibMini.strlenCode
    entry, Silmaril.X86.Ladder.LibMini.strlen_total entry⟩

/-- `memcpy`'s stencil contract as a total WP3 contract on the open machine. -/
def memcpyFn (entry : Word) : FnContract Open.isa :=
  ⟨Silmaril.X86.Stencils.ByteLoop.copyContract Silmaril.X86.Ladder.LibMini.memcpyCode
    entry, Silmaril.X86.Ladder.LibMini.memcpy_total entry⟩

/-- **`strlen` is System V-correct in the institution sense** (first-return `callModel`). -/
theorem strlen_sysv_sat (o : Options) (entry : Word) (k : Nat) :
    Contracts.Sat callModel
      (within ((sysv o).translate strlenProto (strlenC k)) (StrlenRoom entry k)) :=
  Silmaril.Proofs.Machine.Abi.LibMini.strlen_sysv_sat o entry k

/-- **`memcpy` is System V-correct in the institution sense** (it returns `d`). -/
theorem memcpy_sysv_sat (o : Options) (entry : Word) :
    Contracts.Sat callModel
      (within ((sysv o).translate memcpyProto memcpyC) (MemcpyRoom entry)) :=
  Silmaril.Proofs.Machine.Abi.LibMini.memcpy_sysv_sat o entry

theorem strlen_ffiRealizes (profile : Profile) (entry : Word) (k : Nat) :
    Ffi.Realizes (strlenProto.ffi profile (SystemV.plan_intPlan profile))
      (fun _ => BitVec.ofNat 64 k) (fun _ _ => False) (fun _ _ _ => True)
      (strlenDomain entry k) Open.ffiExecute :=
  Silmaril.Proofs.Machine.Abi.LibMini.strlen_ffiRealizes profile entry k

/-- **`strlen` as an exported call-dependent typed certificate.** -/
theorem strlen_ffiRealizesCall (profile : Profile) (entry : Word) :
    CallFootprint.FfiRealizesCall (strlenProto.ffi profile (SystemV.plan_intPlan profile))
      (fun _ call => BitVec.ofNat 64
        (CallFootprint.cstrLen call.initial.machine.memory (arg0 call.initial.machine)))
      (fun _ _ _ => False) (fun _ _ _ => True)
      (fun a call => strlenDomain entry
        (CallFootprint.cstrLen call.initial.machine.memory (arg0 call.initial.machine)) a call)
      Open.ffiExecute :=
  Silmaril.Proofs.Machine.Abi.LibMini.strlen_ffiRealizesCall profile entry

/-- **`memcpy` as an exported call-dependent typed certificate** (footprint `[d, d + n)`). -/
theorem memcpy_ffiRealizesCall (profile : Profile) (entry : Word) :
    CallFootprint.FfiRealizesCall (memcpyProto.ffi profile (SystemV.plan_intPlan profile))
      (fun v _ => v.1)
      (fun _ call a => arg0 call.initial.machine ≤ a ∧
        a < arg0 call.initial.machine + arg2 call.initial.machine)
      (fun _ _ _ => True) (memcpyDomain entry) Open.ffiExecute :=
  Silmaril.Proofs.Machine.Abi.LibMini.memcpy_ffiRealizesCall profile entry

/-- The exported `strlen` certificate gives back each per-length `Ffi.Realizes`
(`FfiRealizesCall.restrict`; a round-trip check of the export form). -/
theorem strlen_ffiRealizes_of_call (profile : Profile) (entry : Word) (k : Nat) :
    Ffi.Realizes (strlenProto.ffi profile (SystemV.plan_intPlan profile))
      (fun _ => BitVec.ofNat 64 k) (fun _ _ => False) (fun _ _ _ => True)
      (strlenDomain entry k) Open.ffiExecute :=
  (strlen_ffiRealizesCall profile entry).restrict
    (fun _ call d => by
      rw [CallFootprint.cstrLen_eq d.2.2]; exact d)
    (fun _ call d => by rw [CallFootprint.cstrLen_eq d.2.2])
    (fun _ _ _ => rfl)

end Silmaril.Machine.Abi.LibMini
