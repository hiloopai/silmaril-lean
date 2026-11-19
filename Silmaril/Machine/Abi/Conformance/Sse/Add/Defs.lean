module

public import Silmaril.Machine.Abi.Conformance.Sse.Defs
public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs

/-!
# The first floating-point row: `double add(double, double)` as `addsd %xmm1, %xmm0; ret`

**The code** (`code`): the five bytes `F2 0F 58 C1 C3` (`addsd %xmm1, %xmm0; ret`, what GCC and
Clang emit for `return a + b;` at `-O1` and above) at `0x401000`, entered at offset 0, extent 5.

**The prototype**: `double add(double a, double b);`, read from a header text (`hdr`) and
lowered by `sysvScalar` (`proto`: two SSE-class `double`s in XMM0 and XMM1, the result in XMM0).

**The ABI**: `sysvScalar.defaultEnv`, the **default-environment subset** of the System V scalar
fragment (identity `…/scalar-aggregates/default-env-subset`): a call is admitted only when it
enters with the default MXCSR **control bits** (`mxcsr &&& 0xffc0 = 0x1F80`: round to nearest,
every exception masked, DAZ and FTZ off), with **any status flags** (they are sticky: a caller
that has done an inexact operation enters with `0x1FA0`, `Thms.admitted_pe`). Why not the full
`sysvScalar`:
* with an exception unmasked in MXCSR, `addsd` raises `#XM` on some operands (overflow,
  inexact, invalid, denormal), which the machine models as a fault (no step). The code then
  does not return, and on hardware the caller gets `SIGFPE`. The full row is **false**, not
  just unproved: `Conforms` requires every admitted call to reach a return;
* a spec precondition cannot name MXCSR (`CallSpec.pre` sees the arguments and the memory
  only, by design), so "exceptions masked" can only be an entry-environment requirement.
The default environment is the one requirement of that kind `Conformance.Defs` defines. A
narrower environment ("every exception masked, any rounding mode, DAZ and FTZ") would cover
more callers; it is not defined here.

**The IEEE domain** (`spec`, `sum`): the result is `X86.Float.Scalar.binary` of the **entry
MXCSR** (`s.mxcsr`) on binary64 `add`: `Numeric.Float`'s x86 SSE profile
(`MXCSR.profile = Profile.x86SSE`), with the rounding direction of MXCSR.RC, DAZ (denormal
inputs read as zero) and FTZ (tiny results flushed to zero while underflow is masked) as MXCSR
sets them, and the profile's NaN rules (a NaN operand is propagated quieted, the first source
operand's NaN taking precedence; an invalid operation without NaN operands gives the QNaN
indefinite `FFF8000000000000`), with tininess detected after rounding. `sum` reads **only the
control bits** of the MXCSR it is given (`Thms.sum_control`): the entry status flags do not
change the result, so the post states `sum` of the entry MXCSR as it is. Under this ABI the
control bits are `0x1F80`: round to nearest even, DAZ and FTZ off, all exceptions masked, so
`addsd` never faults, for every operand pair and every status flag. The status flags the
addition raises are ORed into MXCSR (`Return` leaves them free and requires the control bits
kept).

**Model scope.** The row is on a machine model, not real x86 (that needs `Faithful`). It holds
for every completion: any time-stamp stream, either CET flag (so it is about processes **without
user shadow stacks**; `ret` checks no shadow stack, and code reaching `rdssp` would have no row),
and any x87 TOP and tag word (more than the psABI's empty x87 stack at entry, harmless here: the
code does not touch x87). The FFI thread pointer is carried: `Admit.fsCoherent` ties it to the
core's FS base at entry, code that accesses TLS reads the core's, and `Good.fsBase` is proved on
the core's (the code does not touch it).

**The machine**: `Mach.str9L FeatureSet.baseline64 Features.sseExts`: the tower with the
legacy SSE/SSE2 lanes on the x86-64 baseline processor.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Sse.Add

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.Conformance

/-- `add.h`: `double add(double a, double b);`. -/
def hdr : HeaderSrc := ⟨[("add.h", "double add(double a, double b);")], "add.h"⟩

/-- `double add(double, double)` in the scalar fragment. -/
def proto : Silmaril.Machine.Abi.SystemV.Scalar.Proto :=
  ⟨[.scalar .double, .scalar .double], some (.scalar .double), by decide⟩

/-- `addsd %xmm1, %xmm0; ret`. -/
def bytes : List Silmaril.X86.Byte := [0xF2, 0x0F, 0x58, 0xC1, 0xC3]

/-- The code at `0x401000`, entered at offset 0, five bytes long. -/
def code : Code := ⟨0x401000, bytes, 0, 5, [], []⟩

/-- The ABI of the row: the default-environment subset of `sysvScalar`. -/
abbrev abi : AbiDef := sysvScalar.defaultEnv

/-- **binary64 `a + b` as `addsd` computes it under MXCSR `m`**: `Numeric.Float`'s x86 SSE
profile of `m` (rounding MXCSR.RC, DAZ, FTZ when underflow is masked, the profile's NaN rules). -/
def sum (m : BitVec 32) (a b : BitVec 64) : BitVec 64 :=
  (Silmaril.X86.Float.Scalar.binary ⟨m⟩ .double .add a b).value

/-- **The C spec**: every call is admitted, nothing is written, and the result is `sum` of the
entry MXCSR and the arguments. -/
def spec : CallSpec abi.V proto where
  pre _ _ := True
  post a s r _ := r = sum s.mxcsr a.1 a.2.1

/-- The machine of the row. -/
abbrev mach : Mach :=
  Mach.str9L Silmaril.X86.Features.FeatureSet.baseline64 Silmaril.X86.Features.sseExts

end Silmaril.Machine.Abi.Conformance.Sse.Add

end
