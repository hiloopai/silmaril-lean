# IEEE 754 process support

The standard numeric entry point is `Silmaril.Numeric.Ieee754.Std.Defs`, with
the theorem entry point in `Std.Thms`. The release uses the exact IEEE core for
the RV64 floating-point process model and the TestFloat-backed checks under
`Silmaril.RiscV.LPS`.

The published RISC-V process headers are:

- `Silmaril.Process.RiscV.Defs` for the RV64/FPU definitions;
- `Silmaril.Process.RiscV.Thms` for the checked TestFloat links.

The source snapshot includes binary formats, rounding-mode cases, NaN variants,
and the pinned TestFloat input table. Regenerate or update that table only
through the upstream generator; the release build checks the Lean roots and
the checked-in data hash.
