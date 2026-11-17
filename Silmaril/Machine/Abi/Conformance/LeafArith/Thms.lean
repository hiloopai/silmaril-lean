module

public import Silmaril.Machine.Abi.Conformance.LeafArith.Witness.Defs
public import Silmaril.Machine.Abi.Conformance.Thms
import Silmaril.Proofs.Machine.Abi.Conformance.LeafArith
import Silmaril.Proofs.Machine.Abi.Conformance.Negative

/-! # ABI conformance of rung 01: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Machine.Abi.Conformance.LeafArith` and
`….Negative`. Every statement is on the open machine *model* `Open` (or, for the schema tests,
a small machine given by its step function), not on real x86.

* `clamp_conforms`, `sat_conforms`: gcc -O2 `clamp_i32` and `sat_add_u32` conform to the
  System V AMD64 psABI INTEGER fragment (`sysvInt`) as `arith.h` declares them, with their
  source functions as C specs, no stack frame, no memory written, the thread pointer kept, on
  `Open`, in both modes;
* `header_sat`: **partial** satisfaction of `arith.h` (with `rt.h`): the two functions are
  claimed and conform, and every other declaration is excluded with a checked reason.

Negative (the statement rejects):

* `clamp_rejects_first`: a wrong postcondition ("returns its first argument");
* `open_mid_not`: **stuck code on `Open`**: `clamp_i32`'s prototype entered in the middle of an
  instruction is undecodable (`open_stuck_mid`), and it conforms in neither mode, for any spec;
* `stuck_not`, `clobber_not`, `unbalanced_not`, `scribble_not` (schema tests on small
  machines): a machine that cannot step; a return with `rbx` changed; a "return" with `rsp`
  16 above the entry, which never returns and gets stuck; a write at `rsp − 8` with no frame;
* `wrong_prototype`, `wrong_signedness`: `long clamp_i32(long, long, long)` (widths) and
  `unsigned clamp_i32(int, int, int)` (result signedness) are not what `arith.h` declares;
* `wrong_header_not`: against a header declaring an `unsigned` result, `clamp_i32`'s code
  conforms to the `int` prototype on no machine, in no mode, for no spec;
* `not_available`: the `arith.h` coverage leaves functions unclaimed, so no implementation
  map makes it available (or complete) header satisfaction.

OPEN (`Task`): the first-return rows of `gcd_u32` and `bswap32_manual`, whose block
certificates are proved (`Silmaril.X86.Ladder.LeafArith`) but not in first-return form.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.LeafArith

open Silmaril.X86 (Open.isa)

theorem clamp_conforms (mode : Mode) :
    Conforms sysvInt Open.isa mode hdr "clamp_i32" clampProto clampCode 0 clampS :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.clamp_conforms mode

theorem sat_conforms (mode : Mode) :
    Conforms sysvInt Open.isa mode hdr "sat_add_u32" satProto satCode 0 satS :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.sat_conforms mode

theorem clamp_rejects_first (mode : Mode) :
    ¬ Conforms sysvInt Open.isa mode hdr "clamp_i32" clampProto clampCode 0 clampFirstS :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.clamp_rejects_first mode

theorem coverage_check : coverage.check sysvInt hdr = true :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.coverage_check

theorem header_sat : HeaderSatPartial sysvInt Open.isa hdr coverage impl :=
  Silmaril.Proofs.Machine.Abi.Conformance.LeafArith.header_sat

section Negative
open Silmaril.Machine.Abi.Conformance.LeafArith.Witness

theorem open_stuck_mid :
    Silmaril.X86.Open.step (st 1 5 0 3) = none :=
  Silmaril.Proofs.Machine.Abi.Conformance.Negative.open_stuck_mid

theorem open_mid_not (mode : Mode) (S : CallSpec sysvInt.V clampProto)
    (hS : S.objects clampArgs
      (ffiSt 1 5 0 3).machine.memory = fun _ => False)
    (hpre : S.pre clampArgs
      (ffiSt 1 5 0 3).machine.memory) :
    ¬ Conforms sysvInt Open.isa mode hdr "clamp_i32" clampProto (region 1 19) 0 S :=
  Silmaril.Proofs.Machine.Abi.Conformance.Negative.open_mid_not mode S hS hpre

theorem stuck_not (mode : Mode) (S : CallSpec sysvInt.V clampProto)
    (hS : S.objects clampArgs s0.machine.memory =
      fun _ => False)
    (hpre : S.pre clampArgs s0.machine.memory) :
    ¬ Conforms sysvInt (toy fun _ => none) mode hdr "clamp_i32" clampProto clampCode 0 S :=
  Silmaril.Proofs.Machine.Abi.Conformance.Negative.stuck_not mode S hS hpre

theorem clobber_not (mode : Mode) :
    ¬ Conforms sysvInt (toy (oneStep clobbered
      s0.machine.memory)) mode hdr "clamp_i32" clampProto clampCode 0
      (CallSpec.abiPure sysvInt.V clampProto) :=
  Silmaril.Proofs.Machine.Abi.Conformance.Negative.clobber_not mode

theorem unbalanced_not (mode : Mode) :
    ¬ Conforms sysvInt (toy unbalancedStep) mode hdr "clamp_i32" clampProto clampCode 0
      (CallSpec.abiPure sysvInt.V clampProto) :=
  Silmaril.Proofs.Machine.Abi.Conformance.Negative.unbalanced_not mode

theorem scribble_not (mode : Mode) :
    ¬ Conforms sysvInt (toy (oneStep
      s0.machine.core scribbled)) mode hdr "clamp_i32" clampProto clampCode 0
      (CallSpec.abiPure sysvInt.V clampProto) :=
  Silmaril.Proofs.Machine.Abi.Conformance.Negative.scribble_not mode

theorem wrong_prototype : ¬ Declares sysvInt hdr "clamp_i32" longProto :=
  Silmaril.Proofs.Machine.Abi.Conformance.Negative.wrong_prototype

theorem wrong_signedness : ¬ Declares sysvInt hdr "clamp_i32" uRetProto :=
  Silmaril.Proofs.Machine.Abi.Conformance.Negative.wrong_signedness

theorem wrong_header_not {M : Mach} {mode : Mode} {c : Code} {frame : Nat}
    {S : CallSpec sysvInt.V clampProto} :
    ¬ Conforms sysvInt M mode hdrU "clamp_i32" clampProto c frame S :=
  fun h => Silmaril.Proofs.Machine.Abi.Conformance.Negative.wrong_header h.declared

theorem not_available {M : Mach} {impl : String → Option (Impl sysvInt)} :
    ¬ HeaderSatAvailable sysvInt M hdr coverage impl :=
  fun h => absurd h.2.1 (by decide +kernel)

end Negative

end Silmaril.Machine.Abi.Conformance.LeafArith

end
