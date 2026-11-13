| test | covered by | witness outcome | execution (`Witness.*_row`) | sc | tso | ra | xl | cf | cfPlain | lattice-cores-d64 | lattice-smt-d64 | lattice-cores-d512 | lattice-smt-d512 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| SB | tso | `0:r0=0 1:r0=0` | `Sanity.sb` | ✗ | ✓ | ✓ | ✓ | ✓ | ✓ | 4000347 / 50000000 | 1768369 / 50000000 | 1139546 / 50000000 | 364784 / 50000000 |
| SB+mfences | tso | `0:r0=0 1:r0=0` | `Sanity.sbMfence` | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| SB+xchgs | tso | `0:r0=0 1:r0=0` | `sbXchg` | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| MP | tso | `1:r0=1 1:r1=0` | `Lattice.mp` | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| LB | tso | `0:r0=1 1:r0=1` | `Lattice.lb` | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| IRIW | tso | `2:r0=1 2:r1=0 3:r0=1 3:r1=0` | `Lattice.iriw` | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| 2+2W | tso | `x=1 y=1` | `Lattice.w22` | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| MP+movnti | xl | `1:r0=1 1:r1=0` | `Sanity.mpNt` | ✗ | ✗ | ✗ | ✓ | ✗ | ✗ | 476642 / 50000000 | 0 / 50000000 | 26429 / 50000000 | 0 / 50000000 |
| MP+movnti+sfence | xl | `1:r0=1 1:r1=0` | `Sanity.mpNtSfence` | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| SPLIT8 | xl | `1:r0=torn` | `Sanity.torn` | ✗ | ✗ | ✗ | ✓ | ✓ | ✓ | 251933 / 50000000 | 441891 / 50000000 | 15951 / 50000000 | 50641 / 50000000 |
| TORN2-inline | xl | `1:r0=torn` | `Sanity.torn` | ✗ | ✗ | ✗ | ✓ | ✓ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| TORN2-cross | xl | `1:r0=torn` | `Sanity.torn` | ✗ | ✗ | ✗ | ✓ | ✓ | ✓ | 13970 / 50000000 | 355637 / 50000000 | 1296 / 50000000 | 56411 / 50000000 |
| INC2 | tso | `x=1` | `inc2` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 3708352 / 50000000 | 2469774 / 50000000 | 1771320 / 50000000 | 514291 / 50000000 |
| LOCKINC2 | tso | `x=1` | `Sanity.lockInc` | ✗ | ✗ | ✗ | ✗ | ✗ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| CoWR | tso | `0:r0=0 x=1` | `coWR2` | ✗ | ✗ | ✗ | ✗ | ✓ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| CoWR | tso | `0:r0=0 x=2` | `coWR2` | ✗ | ✗ | ✗ | ✗ | ✓ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |
| CoWR | tso | `0:r0=2 x=1` | `coWR2b` | ✗ | ✗ | ✗ | ✗ | ✓ | ✓ | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 | 0 / 50000000 |

| edge | separating outcomes (allowed by the upper model, forbidden by the lower) | observed on hardware |
|---|---|---|
| sc ⊏ tso | SB `0:r0=0 1:r0=0`: 7273046 | yes, on TSO-covered tests |
| tso ⊏ xl | MP+movnti (XL-only) `1:r0=1 1:r1=0`: 503071, SPLIT8 (XL-only) `1:r0=torn`: 760416, TORN2-inline (XL-only) `1:r0=torn`: 0, TORN2-cross (XL-only) `1:r0=torn`: 427314 | only on XL-only tests (misaligned or non-temporal) |
| tso ⊏ ra | SB+mfences `0:r0=0 1:r0=0`: 0, SB+xchgs `0:r0=0 1:r0=0`: 0, IRIW `2:r0=1 2:r1=0 3:r0=1 3:r1=0`: 0, 2+2W `x=1 y=1`: 0 | no |
| tso ⊏ cf | SB+mfences `0:r0=0 1:r0=0`: 0, SB+xchgs `0:r0=0 1:r0=0`: 0, IRIW `2:r0=1 2:r1=0 3:r0=1 3:r1=0`: 0, 2+2W `x=1 y=1`: 0, SPLIT8 (XL-only) `1:r0=torn`: 760416, TORN2-inline (XL-only) `1:r0=torn`: 0, TORN2-cross (XL-only) `1:r0=torn`: 427314, CoWR `0:r0=0 x=1`: 0, CoWR `0:r0=0 x=2`: 0, CoWR `0:r0=2 x=1`: 0 | only on XL-only tests (misaligned or non-temporal) |
| ra ⊏ cfPlain | SPLIT8 (XL-only) `1:r0=torn`: 760416, TORN2-inline (XL-only) `1:r0=torn`: 0, TORN2-cross (XL-only) `1:r0=torn`: 427314, LOCKINC2 `x=1`: 0, CoWR `0:r0=0 x=1`: 0, CoWR `0:r0=0 x=2`: 0, CoWR `0:r0=2 x=1`: 0 | only on XL-only tests (misaligned or non-temporal) |
| cf ⊏ cfPlain | LOCKINC2 `x=1`: 0 | no |
| xl ⊏ top | SB+mfences `0:r0=0 1:r0=0`: 0, SB+xchgs `0:r0=0 1:r0=0`: 0, MP `1:r0=1 1:r1=0`: 0, LB `0:r0=1 1:r0=1`: 0, IRIW `2:r0=1 2:r1=0 3:r0=1 3:r1=0`: 0, 2+2W `x=1 y=1`: 0, MP+movnti+sfence (XL-only) `1:r0=1 1:r1=0`: 0, LOCKINC2 `x=1`: 0, CoWR `0:r0=0 x=1`: 0, CoWR `0:r0=0 x=2`: 0, CoWR `0:r0=2 x=1`: 0 | no |
| cfPlain ⊏ top | MP `1:r0=1 1:r1=0`: 0, LB `0:r0=1 1:r0=1`: 0, MP+movnti (XL-only) `1:r0=1 1:r1=0`: 503071, MP+movnti+sfence (XL-only) `1:r0=1 1:r1=0`: 0 | only on XL-only tests (misaligned or non-temporal) |
OK: every observed outcome is allowed by every model covering its test
