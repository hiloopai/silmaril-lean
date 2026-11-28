# IEEE scalar digital simulation

Import `Silmaril.Logic.DigitalSimulation.Defs` for executable operations on
`VerilogBit` and `StdULogic`. Import `Silmaril.Logic.DigitalSimulation.Thms`
for preservation laws and counterexamples.

## Standards and resolution

- **Verilog/SystemVerilog.** IEEE Std 1800-2017 §6.3.1 gives `0/1/X/Z`. The
  scalar gates implement bitwise `~`, `&`, `|`, and `^` from §11.4.8,
  Tables 11-15, 11-11, 11-12, and 11-13. `resolvePair` uses the ordinary
  `wire`/`tri` table from §6.6.1, Table 6-2, which assumes equal drive
  strengths. `resolve` folds that table from `Z`, the undriven value
  specified by §6.6. The scope is scalar combinational evaluation. It
  excludes unequal or ambiguous strengths, other net types, event scheduling
  and expression sizing. [IEEE 1800-2017][sv] · [Checked PDF][sv-pdf]
- **VHDL.** The IEEE 1076-2019 `STD_LOGIC_1164` declaration gives
  `U/X/0/1/Z/W/L/H/-`. The scalar gates implement `not_table`,
  `and_table`, `or_table` and `xor_table`. Their results are in the
  `UX01` subset of `STD_ULOGIC`. `resolvePair` implements
  `resolution_table`. `resolve` implements `resolved` with the list in
  vector traversal order. It returns `Z` for an empty list and returns a
  singleton unchanged, even if its value is `-`. The table maps the pair
  `(Z, -)` to `X`. A weak `L/H` conflict produces `W`, while a forcing
  `0` overrides `H`. The package source is Apache-2.0, copyright 2019
  IEEE P1076 WG Authors. The checked body is byte-identical to the copy in
  GHDL v5.1.1. [IEEE 1076-2019][vhdl] ·
  [Package declaration][vhdl-decl] · [Package body][vhdl-body] · [GHDL copy][ghdl]

The gates and driver resolution model different operations. For example,
`and Z Z = X` and `or Z Z = X` on both carriers, so the gate tables
violate idempotence. The equal-strength Verilog resolution table acts as
join in the diamond with bottom `Z`, incomparable `0` and `1`, and top
`X`. The IEEE 1164 pair table violates idempotence because `(-, -)`
resolves to `X`. The Lean API leaves the carriers unordered and exposes
named operations.

## Conversions

| Map | What it preserves |
| --- | --- |
| `ofBool` on either carrier | Boolean NOT, AND, OR and XOR on known bits. VHDL embeds at forcing strength. Resolution can leave the image, for example on conflicting bits. |
| `toBool?` and `ofOptionBool` | Known levels round-trip through the observation. The observer reads VHDL weak `L/H` as false/true. The embedding uses `X` for `none`. At the observation level, `none` denotes an unknown operand, with false controlling AND and true controlling OR. The observation loses the distinctions used by resolution. For example, Verilog `Z` and `X` both observe as `none`, yet a `1` driver resolves with them to `1` and `X` respectively. |
| `StdULogic.toVerilog` | All four gates. It maps `L/H` to `0/1`, `U/W/-` to `X`, and keeps `0/1/X/Z`. Observing a Boolean before or after projection agrees. Resolving `0` against `H` yields `0`, while projecting those drivers first yields a Verilog conflict `X`. |
| `VerilogBit.toStdULogic` | All four gates, pair and list resolution, including the empty list. It embeds as forcing `0/1/X` and high impedance `Z`. Projecting after embedding is the identity. The opposite round trip can change the value, for example `H` becomes forcing `1`. |

## Checked example

A scalar bus has a weak pull-up and another driver. Resolve the drivers,
apply the receiver's enable, then observe a Boolean. The checked example
reads true when the driver releases the bus, false when it drives a
forcing zero, and `none` for a don't-care driver while the receiver is enabled.
Its module also checks every unary and binary table entry and the empty and
singleton resolution cases. [Example and table regressions][examples]

```sh
lake build --wfail +Silmaril.Logic.DigitalSimulation.Thms +Silmaril.Logic.DigitalSimulation.Examples
make check CHECK_TARGETS='+Silmaril.Logic.DigitalSimulation.Thms +Silmaril.Logic.DigitalSimulation.Examples'
```

Source editions and SHA-256 hashes are in `references.bib` under
`ieee-1800-2017`, `ieee-1076-2019`, `ieee-1076-2019-std-logic-1164`
and `ieee-1076-2019-std-logic-1164-body`. [Bibliography][bib]

[sv]: https://doi.org/10.1109/IEEESTD.2018.8299595
[sv-pdf]: https://fpga.mit.edu/6205/_static/F23/documentation/1800-2017.pdf
[vhdl]: https://doi.org/10.1109/IEEESTD.2019.8938196
[vhdl-decl]: https://opensource.ieee.org/vasg/Packages/-/blob/16a012320947d378611cc7457f64ed76cb52bac4/ieee/std_logic_1164.vhdl
[vhdl-body]: https://opensource.ieee.org/vasg/Packages/-/blob/16a012320947d378611cc7457f64ed76cb52bac4/ieee/std_logic_1164-body.vhdl
[ghdl]: https://github.com/ghdl/ghdl/blob/ba3368ed3ff7235650169a5f3c98f391199b411c/libraries/ieee2008/std_logic_1164-body.vhdl
[examples]: ../../Silmaril/Logic/DigitalSimulation/Examples.lean
[bib]: ../../references.bib
