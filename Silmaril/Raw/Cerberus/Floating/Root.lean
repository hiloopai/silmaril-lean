module

public import Silmaril.Cerberus.Ctype.Defs
public import Silmaril.Numeric.Float.Instances
public import Silmaril.Numeric.Ieee754.Decimal

/-! The OCaml amd64 floating environment at Cerberus b3e11ea3. All three
real C types carry binary64 values. The producer uses nearest-even, gradual
underflow and masked exceptions. Arithmetic and conversions use the shared
IEEE model; status flags are unobserved by this concrete memory model.
References are to memory/concrete/impl_mem.ml unless otherwise indicated. -/

@[expose] public section
namespace Silmaril.Cerberus.Floating
open Silmaril.Numeric.Ieee754
open Silmaril.Numeric.Float

/-- The measured producer's MXCSR controls: RNE, DAZ clear, FZ clear. -/
def profile : Profile := Profile.x86SSE {}

/-- Lines 2347-2356. OCaml arithmetic, retaining the x86 NaN choices. -/
def binary (op : ArithOp) (x y : F64) : F64 :=
  ⟨UInt64.ofBitVec (profile.binary .binary64 op .nearestTiesToEven
    x.bits.toBitVec y.bits.toBitVec).value⟩

/-- Lines 2358-2365. IEEE comparisons, with exceptions masked. -/
def compare (predicate : Predicate) (x y : F64) : Bool :=
  (profile.comparePredicate predicate (fmt := .binary64)
    x.bits.toBitVec y.bits.toBitVec).value

/-- Lines 2367-2369. Correct rounding of the exact decimal integer string. -/
def ofInt (n : Int) : F64 :=
  ⟨UInt64.ofBitVec (profile.ofInt .binary64 .nearestTiesToEven n).value⟩

/-- Lines 2371-2372. Zarith truncates to an unbounded integer. NaN and
infinity raise Z.Overflow in the producer and have no normal observation. -/
def toInt? (x : F64) : Option Int := x.toInt? .towardZero

/-- ocaml_implementation.ml:206-212,247-253: every real type is binary64. -/
def realType : Ctype → Option RealFloatingType
  | .mk _ (.basic (.floating (.realFloating ty))) => some ty
  | _ => none

/-- formatted.lem:579-610, decode.ml:228-233. Fixed decimal formatting
uses the exact dyadic value scaled by 10^precision and shared nearest-even
integer rounding. The sign of zero is preserved; OCaml retains the NaN
sign in fixed formatting. Width and flags belong to the format parser. -/
def fixed (precision : Nat) (x : F64) : String :=
  let sign := if x.signBit then "-" else ""
  if x.isNaN then sign ++ "nan"
  else
    if x.isInfinite then sign ++ "inf"
    else
      let scaled := match x.model.unpack with
        | .finite _ m e _ =>
            Rounding.ofDyadic (m * 5 ^ precision) (e + precision)
        | _ => Rounding.ofInt 0
      let n := (Rounding.toInt? .nearestTiesToEven scaled).getD 0
      let digits := toString n.natAbs
      let padded := Decimal.zeros (precision + 1 - digits.length) ++ digits
      let point := padded.length - precision
      sign ++ String.ofList (padded.toList.take point) ++
        (if precision == 0 then "" else "." ++ String.ofList (padded.toList.drop point))

/-- The adapter retains gradual underflow in both directions. -/
theorem gradual_underflow : profile.flushInputs = false ∧ profile.flushResults = false :=
  ⟨rfl, rfl⟩

end Silmaril.Cerberus.Floating
