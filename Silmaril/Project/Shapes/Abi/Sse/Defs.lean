module

public import Silmaril.Project.Shapes.Abi.Defs
public import Silmaril.Machine.Abi.Conformance.Sse.Add.Defs

/-!
# ABI conformance on the SSE model machine `Mach.str9L`: shape and the first row

| name | statement |
| --- | --- |
| `silmaril.shapes.abi.conforms.sysv_scalar_default_env_str9l` | `Conforms` for `sysvScalar.defaultEnv` (System V scalar fragment, **default-environment subset**: MXCSR control bits `0x1F80` at entry, status flags free) on the **model machine** `Mach.str9L baseline64 sseExts` |
| `silmaril.abi.sse.add` | `addsd %xmm1, %xmm0; ret` (`F2 0F 58 C1 C3` at `0x401000`) as `double add(double, double)`, total, frame 0, result the IEEE binary64 sum under the entry MXCSR (`Numeric.Float` x86 SSE profile) |

**Scope, in every title.** The ABI is the default-environment subset, not full System V: under
plain `sysvScalar` (any MXCSR at entry) the row is false, since an unmasked exception makes
`addsd` fault. The machine is a **model**: reading a row about real x86 needs `Faithful` of a
reference machine to `Mach.str9L`, which is not proved. `Mach.str9L` models the integer
state, the whole vector field, x87, the direction flag, MXCSR and the x87 control word, and
carries x87 mode and the FFI FS-base copy (`Sse.str9L_models`, `Sse.str9L_carried`); its
completions are every time-stamp stream and CET flag (`Sse.str9L_fillsAll`); rows hold for
processes without user shadow stacks; VEX/BMI forms take no step on `baseline64`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Abi.Sse

silmaril instance silmaril.shapes.abi.conforms.sysv_scalar_default_env_str9l
    (title := "conforms, System V scalar fragment, DEFAULT-ENVIRONMENT SUBSET (MXCSR control 0x1F80), on the SSE MODEL machine Mach.str9L baseline64 (real x86 needs Faithful, not proved)") :=
  silmaril.shapes.abi.conforms
    (A := Silmaril.Machine.Abi.Conformance.Sse.Add.abi)
    (M := Silmaril.Machine.Abi.Conformance.Sse.Add.mach)

silmaril instance silmaril.abi.sse.add
    (title := "addsd; ret conforms as double add(double, double): System V scalar DEFAULT-ENVIRONMENT SUBSET, SSE MODEL machine Mach.str9L (not real x86: Faithful unproved), total, frame 0, IEEE binary64 sum") :=
  silmaril.shapes.abi.conforms.sysv_scalar_default_env_str9l (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.Sse.Add.hdr) (f := "add")
    (p := Silmaril.Machine.Abi.Conformance.Sse.Add.proto)
    (c := Silmaril.Machine.Abi.Conformance.Sse.Add.code) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.Sse.Add.spec)

end Silmaril.Project.Shapes.Abi.Sse

end
