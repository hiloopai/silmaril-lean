module

public import Silmaril.Numeric.Libm.Lattice.Defs

/-!
# Documented error bounds of glibc 2.40

glibc records, per architecture, the largest error its test suite observes for
each function in `sysdeps/<arch>/libm-test-ulps`. The error is measured in
ulps of the correctly rounded result, as in `CRWithin`. These are observed
maxima of a test suite, not proofs: as specifications they are *assumptions*
("sane bounds") that a problem may state.

`most` is the larger of the x86-64 and AArch64 entries (`sysdeps/x86_64/fpu`,
`sysdeps/aarch64`); `all` is the maximum over the eleven files of the
glibc-2.40 tag listed below, with an absent entry read as 0:

| file | SHA-256 |
| --- | --- |
| `sysdeps/aarch64/libm-test-ulps` | `20189f5a2e01e2e2f1e22d81f6a1c9041ba33ad8c5701cc156a631f7af74cace` |
| `sysdeps/arm/libm-test-ulps` | `86f9dcab08235e1d1a3a80f1c2e09ff85d95859a43eb2048b8ddab16209ccdd7` |
| `sysdeps/i386/fpu/libm-test-ulps` | `8d7afffa2d42a38f488af62d862e75ca3559e9fdbe5ec6832c58b25b0753def7` |
| `sysdeps/loongarch/lp64/libm-test-ulps` | `d150034b00ca97c47e401bf76fe4314d2eedfd785739d078bb72b70906a91e04` |
| `sysdeps/mips/mips64/libm-test-ulps` | `6a253fed61edf3ffa61c15569ace2e6bdf46c7f19f398d0b69af526376c80d0d` |
| `sysdeps/powerpc/fpu/libm-test-ulps` | `588a5785eeb5e8ba7db24cf11281bec67ae6dacf443ec20c4b8d28f0475e6fc6` |
| `sysdeps/riscv/nofpu/libm-test-ulps` | `58e0969eef555ca62a848e50f1df95901794434de35805269d78140ae2d5e8eb` |
| `sysdeps/riscv/rvd/libm-test-ulps` | `b2bc7130370408e50184df8377d74c92455a72237f3f244adeef6b2c899cb69c` |
| `sysdeps/s390/fpu/libm-test-ulps` | `7e593fadd82be7cd6b6867d4ffb9785f51269677ef5e295355a1c9bbb031fb94` |
| `sysdeps/sparc/fpu/libm-test-ulps` | `eef8f7fa15de3d145636db2f32b8b84de7a4f3dafd539d2cb6ca981132af1d98` |
| `sysdeps/x86_64/fpu/libm-test-ulps` | `c91eb17100771f147b34f85110e7a6ded121d78ce6ed2a0d45472829670340de` |

Only the round-to-nearest `double` rows (`Function: "f":`, `double:`) are used.
Source: <https://sourceware.org/git/?p=glibc.git;a=tree;hb=glibc-2.40>.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.Glibc

/-- A documented bound: ulps from the correctly rounded result. -/
structure Documented where
  name : String
  most : ℕ
  all : ℕ
  deriving DecidableEq, Repr

/-- glibc 2.40, `double`, round to nearest. -/
def double240 : List Documented := [
  ⟨"acos", 1, 1⟩,
  ⟨"acosh", 2, 2⟩,
  ⟨"asin", 1, 1⟩,
  ⟨"asinh", 2, 2⟩,
  ⟨"atan", 1, 1⟩,
  ⟨"atan2", 0, 1⟩,
  ⟨"atanh", 2, 2⟩,
  ⟨"cbrt", 4, 4⟩,
  ⟨"cos", 1, 1⟩,
  ⟨"cosh", 2, 2⟩,
  ⟨"exp", 1, 1⟩,
  ⟨"exp10", 2, 2⟩,
  ⟨"exp2", 1, 1⟩,
  ⟨"expm1", 1, 1⟩,
  ⟨"hypot", 1, 1⟩,
  ⟨"lgamma", 4, 4⟩,
  ⟨"log", 1, 1⟩,
  ⟨"log10", 2, 2⟩,
  ⟨"log1p", 1, 1⟩,
  ⟨"log2", 2, 2⟩,
  ⟨"pow", 1, 1⟩,
  ⟨"sin", 1, 1⟩,
  ⟨"sinh", 2, 2⟩,
  ⟨"tan", 0, 1⟩,
  ⟨"tanh", 2, 2⟩,
  ⟨"tgamma", 9, 9⟩]

/-- The documented bound selected by `sel`; functions without an entry are
correctly rounded in glibc's tests (bound 0). -/
def bound (sel : Documented → ℕ) (name : String) : ℕ :=
  ((double240.find? (·.name == name)).map sel).getD 0

/-- The sane bound assumed on x86-64 and AArch64. -/
def mostPlatforms (name : String) : Accuracy := .glibc (bound Documented.most name)

/-- The sane bound assumed on every listed glibc port. -/
def allPlatforms (name : String) : Accuracy := .glibc (bound Documented.all name)

end Silmaril.Numeric.Libm.Glibc
