module

public import Silmaril.Numeric.Libm.Exact.Defs
public import Silmaril.Numeric.Libm.Lattice.Thms
import Silmaril.Proofs.Numeric.Libm.Exact

/-!
# Batch 1: proved nodes and sample evaluations

* The integral roundings `floor`, `ceil`, `trunc`, `round`, `rint` and
  `nearbyint` of `Ref` are `Exact`, hence correctly rounded and within 1/2 ulp.
* `Ref.sqrt` is `CorrectlyRounded`, hence within 1/2 ulp.
* Any implementation bit-exact with these references inherits the same nodes.
* `Exact.Tests` evaluates the references on sample inputs and checks them
  against every applicable special case on `B64.samples` (pairs on
  `B64.samplePairs`).

Not yet proved: the `Exact` node for `fabs`, `copysign`, `fmod`, `remainder`,
`fmin`, `fmax`, the `CorrectlyRounded` node for `ldexp`/`scalbn`, `FrexpOk` and
`ModfOk` for the references, and the special-value nodes as theorems over all
inputs (they are checked on samples only). They are stated as `Task`s.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.Double

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec Silmaril.Numeric.Libm.B64

/-! ## Proved nodes -/

theorem integral_exact (name : String) (mode : RoundingMode) (inexact : Bool) :
    (integral name mode inexact).Exact (Outcome.pure (F64.roundIntegral mode)) :=
  Proofs.Numeric.Libm.Exact.integral_exact name mode inexact

theorem floor_exact : floor.Exact (Outcome.pure Ref.floor) := integral_exact _ _ _
theorem ceil_exact : ceil.Exact (Outcome.pure Ref.ceil) := integral_exact _ _ _
theorem trunc_exact : trunc.Exact (Outcome.pure Ref.trunc) := integral_exact _ _ _
theorem round_exact : round.Exact (Outcome.pure Ref.round) := integral_exact _ _ _
theorem rint_exact : rint.Exact (Outcome.pure Ref.rint) := integral_exact _ _ _
theorem nearbyint_exact : nearbyint.Exact (Outcome.pure Ref.nearbyint) := integral_exact _ _ _

/-- `Ref.sqrt` is correctly rounded (IEEE 754 §5.4.1). -/
theorem sqrt_correctlyRounded : sqrt.CorrectlyRounded (Outcome.pure Ref.sqrt) :=
  Proofs.Numeric.Libm.Exact.sqrt_correctlyRounded

/-- Hence within half an ulp of `Real.sqrt` on every nonnegative finite input. -/
theorem sqrt_errorGlobal_half : sqrt.ErrorGlobal (Outcome.pure Ref.sqrt) (1 / 2) :=
  sqrt_correctlyRounded.errorGlobal_half

/-- An implementation returning the encodings of `Ref.sqrt` is correctly rounded. -/
theorem sqrt_correctlyRounded_of_bitExact {impl : F64 → Outcome F64}
    (h : BitExact impl Ref.sqrt) : sqrt.CorrectlyRounded impl :=
  h.correctlyRounded sqrt_correctlyRounded

theorem floor_correctlyRounded_of_bitExact {impl : F64 → Outcome F64}
    (h : BitExact impl Ref.floor) : floor.CorrectlyRounded impl :=
  (h.exact floor_exact).correctlyRounded

/-! ## Open goals

Stated, not proved. Each is the corresponding node for the reference. -/

namespace Task

def fabs_exact : Prop := fabs.Exact (Outcome.pure Ref.fabs)
def copysign_exact : Prop := copysign.Exact (Outcome.pure Ref.copysign)
def fmod_exact : Prop := fmod.Exact (Outcome.pure Ref.fmod)
def remainder_exact : Prop := remainder.Exact (Outcome.pure Ref.remainder)
def fmin_exact : Prop := fmin.Exact (Outcome.pure Ref.fmin)
def fmax_exact : Prop := fmax.Exact (Outcome.pure Ref.fmax)
def ldexp_correctlyRounded : Prop := ldexp.CorrectlyRounded (Outcome.pure Ref.ldexp)
def frexp_ok : Prop := ∀ x, FrexpOk x (Ref.frexp x)
def modf_ok : Prop := ∀ x, ModfOk x (Ref.modf x)
/-- The special values of every batch-1 `Spec`, over all inputs. -/
def floor_specialValues : Prop := floor.SpecialValues (Outcome.pure Ref.floor)

end Task

end Silmaril.Numeric.Libm.Double
