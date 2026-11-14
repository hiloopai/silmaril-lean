module

public import Silmaril.Numeric.Libm.Exact.Defs
public import Silmaril.Numeric.Libm.Elementary.Defs
public import Silmaril.Numeric.Libm.Glibc.Defs

/-!
# Combined libm problems

`catalogue` lists every specified `double` function (batch 1 and batch 2). A
`Profile` picks one accuracy level per function; `ValidLibmDouble p impl` is
"`impl` exports a valid libm at profile `p`", the conjunction over the
catalogue of the per-function problems `ValidFunction p S impl` ("exports a
valid `f`"). The exact functions of batch 1 are required exact and `sqrt`,
`ldexp` and `scalbn` correctly rounded in every profile except `specialOnly`.

| profile | elementary functions |
| --- | --- |
| `correctlyRounded` | correctly rounded (CORE-MATH, LLVM libc's goal) |
| `glibcMost` | glibc 2.40's documented bound on x86-64 and AArch64 |
| `glibcAll` | glibc 2.40's documented bound on every listed port |
| `faithful` | within 1 ulp of the exact result |
| `specialOnly` | special cases only |
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.Double

/-- Accuracy profiles of a whole libm. -/
inductive Profile where
  | correctlyRounded
  | glibcMost
  | glibcAll
  | faithful
  | specialOnly
  deriving DecidableEq, Repr

/-- Functions whose results are exact in every conforming libm. -/
def exactNames : List String :=
  ["fabs", "copysign", "floor", "ceil", "trunc", "round", "rint", "nearbyint", "fmod",
    "remainder", "fmin", "fmax", "frexp", "modf"]

/-- Functions that IEEE 754 or C require to be correctly rounded. -/
def roundedNames : List String := ["sqrt", "ldexp", "scalbn"]

/-- The accuracy level of function `name` at profile `p`. -/
def level (p : Profile) (name : String) : Accuracy :=
  if p = .specialOnly then .none
  else if name ∈ exactNames then .exact
  else if name ∈ roundedNames then .correctlyRounded
  else match p with
    | .correctlyRounded => .correctlyRounded
    | .glibcMost => Glibc.mostPlatforms name
    | .glibcAll => Glibc.allPlatforms name
    | .faithful => .ulps 1
    | .specialOnly => .none

/-- `p` asks at least as much as `q` of every function. -/
def Profile.Stronger : Profile → Profile → Prop
  | _, .specialOnly => True
  | .correctlyRounded, _ => True
  | .glibcMost, .glibcMost | .glibcMost, .glibcAll | .glibcAll, .glibcAll => True
  | .faithful, .faithful => True
  | _, _ => False

/-- Every specified `double` function. -/
noncomputable def catalogue : List Entry := batch1 ++ batch2

/-- "Exports a valid `f` at profile `p`". -/
def ValidFunction {α τ : Type} [LibmFloat τ] (p : Profile) (S : Spec α τ)
    (impl : α → Outcome τ) : Prop :=
  S.Valid impl (level p S.name)

/-- "Exports a valid `double` libm at profile `p`": one subproblem per function. -/
noncomputable def ValidLibmDouble (p : Profile) (impl : LibmImpl) : Prop :=
  ValidLibm catalogue (level p) impl

end Silmaril.Numeric.Libm.Double
