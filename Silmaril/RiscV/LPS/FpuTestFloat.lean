module

public import Silmaril.RiscV.LPS.FpuLattice

/-!
# Berkeley TestFloat vectors, RISC-V specialization

`data/riscv/testfloat-riscv.txt` holds 19456 vectors produced by Berkeley TestFloat 3e's
`testfloat_gen` linked against Berkeley SoftFloat 3 built with `SPECIALIZE_TYPE=RISCV`
(canonical NaN results, RISC-V integer-conversion saturation), with tininess after
rounding and `-exact` conversions (NX raised by inexact float-to-integer conversions, as
RISC-V `FCVT` does). 128 vectors per group, sampled at an even stride from TestFloat's
level-1 case lists, cover, for binary32 and binary64 and every one of the five rounding
modes: add, sub, mul, div, sqrt, fused multiply-add, the four integer→float and four
float→integer conversions, and binary64→binary32; plus binary32→binary64, `feq`, `flt`
and `fle`. The generator and the sha256 pins of its inputs are in
`scripts/riscv/testfloat-vectors.py`.

Each vector is run through both kernels of the lattice (`FpuImpl.lps` and
`FpuImpl.ieee`) as an `FpReq`, comparing result bits and all five flags. The checks
(`Silmaril.RiscV.LPS.FpuTestFloatChecks`) are compiled evaluations (`#guard`), not kernel
proofs: they are test evidence that
the `agreed` variant is close to total, and no theorem depends on them.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS.TestFloat

/-- A hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A hexadecimal numeral. -/
def hex? (s : String) : Option Nat :=
  s.foldl (fun acc c => do let a ← acc; let d ← hexDigit? c; pure (16 * a + d)) (some 0)

/-- TestFloat's flag byte (NX = 1, UF = 2, OF = 4, DZ = 8, NV = 16) as `FFlags`. -/
def flagsOf (n : Nat) : FFlags :=
  ⟨n.testBit 4, n.testBit 3, n.testBit 2, n.testBit 1, n.testBit 0⟩

def fmt? : String → Option FpFormat
  | "f32" => some fmtSingle
  | "f64" => some fmtDouble
  | _ => none

def mode? : String → Option RMode
  | "rne" => some .rne
  | "rtz" => some .rtz
  | "rdn" => some .rdn
  | "rup" => some .rup
  | "rmm" => some .rmm
  | _ => none

/-- Signedness and width of a TestFloat integer type. -/
def int? : String → Option (Bool × Nat)
  | "i32" => some (true, 32)
  | "ui32" => some (false, 32)
  | "i64" => some (true, 64)
  | "ui64" => some (false, 64)
  | _ => none

/-- One vector line as a request and its expected answer. -/
def parse? (line : String) : Option (FpReq × (Nat × FFlags)) := do
  match (line.splitOn " ").filter (· ≠ "") with
  | ["sqrt", f, md, a, z, fl] =>
    pure (.sqrt (← fmt? f) (← mode? md) (← hex? a), (← hex? z, flagsOf (← hex? fl)))
  | ["fma", f, md, a, b, c, z, fl] =>
    pure (.fma (← fmt? f) (← mode? md) (← hex? a) (← hex? b) (← hex? c),
      (← hex? z, flagsOf (← hex? fl)))
  | ["ofInt", f, it, md, a, z, fl] =>
    let (s, bits) ← int? it
    pure (.ofInt (← fmt? f) (← mode? md) s bits (← hex? a), (← hex? z, flagsOf (← hex? fl)))
  | ["toInt", f, it, md, a, z, fl] =>
    let (s, bits) ← int? it
    pure (.toInt (← fmt? f) (← mode? md) s bits (← hex? a), (← hex? z, flagsOf (← hex? fl)))
  | ["convert", src, dst, md, a, z, fl] =>
    pure (.convert (← fmt? src) (← fmt? dst) (← mode? md) (← hex? a),
      (← hex? z, flagsOf (← hex? fl)))
  | [op, f, md, a, b, z, fl] =>
    let f ← fmt? f
    let md ← mode? md
    let a ← hex? a
    let b ← hex? b
    let z ← hex? z
    let fl := flagsOf (← hex? fl)
    let req ← match op with
      | "add" => some (FpReq.add f md a b)
      | "sub" => some (FpReq.sub f md a b)
      | "mul" => some (FpReq.mul f md a b)
      | "div" => some (FpReq.div f md a b)
      | "eq" => some (FpReq.eq f a b)
      | "lt" => some (FpReq.lt f a b)
      | "le" => some (FpReq.le f a b)
      | _ => none
    pure (req, (z, fl))
  | _ => none

/-- The vector table. -/
def raw : String := include_str "../../../data/riscv/testfloat-riscv.txt"

/-- The vector lines. -/
def lines : List String := (raw.splitOn "\n").filter (· ≠ "")

/-- Lines that do not parse (there are none). -/
def unparsed : List String := lines.filter fun l => (parse? l).isNone

/-- The lines on which a kernel's bits or flags differ from TestFloat's. -/
def mismatches (I : FpuImpl) : List String :=
  lines.filter fun l =>
    match parse? l with
    | some (req, expected) => I.run req != expected
    | none => true

/-! ## Special-value differential tables

Every request over a pool of special and boundary encodings (signed zeros, the
smallest and largest subnormals, the smallest normal, one, the largest finite value,
infinities, quiet and signalling NaNs of both signs, the integer-precision boundary
and a few ordinary values), in every rounding mode, run through both kernels. These
include `fmin`/`fmax`, `fclass` and the comparisons, which TestFloat does not cover (and
which `Silmaril.RiscV.LPS.FpuAgree` proves for every operand). -/

/-- The binary32 pool. -/
def pool32 : List Nat :=
  [0x00000000, 0x80000000, 0x00000001, 0x80000001, 0x007fffff, 0x807fffff, 0x00800000,
   0x80800000, 0x3f800000, 0xbf800000, 0x7f7fffff, 0xff7fffff, 0x7f800000, 0xff800000,
   0x7fc00000, 0xffc00000, 0x7f800001, 0xff812345, 0x4b800000, 0x3fc00000, 0x40400000,
   0x3dcccccd, 0xcf000000, 0x4f800000]

/-- The binary64 pool. -/
def pool64 : List Nat :=
  [0x0000000000000000, 0x8000000000000000, 0x0000000000000001, 0x8000000000000001,
   0x000fffffffffffff, 0x800fffffffffffff, 0x0010000000000000, 0x8010000000000000,
   0x3ff0000000000000, 0xbff0000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
   0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000000,
   0x7ff0000000000001, 0xfff4000000000000, 0x4340000000000000, 0x3ff8000000000000,
   0x4008000000000000, 0x3fb999999999999a, 0xc3e0000000000000, 0x43f0000000000000]

def modes : List RMode := [.rne, .rtz, .rdn, .rup, .rmm]

/-- The pool requests of one format. -/
def poolReqs (f : FpFormat) (pool : List Nat) : List FpReq :=
  let pairs := pool.flatMap fun a => pool.map fun b => (a, b)
  let small := pool.take 16
  (modes.flatMap fun md =>
    (pairs.flatMap fun (a, b) => [FpReq.add f md a b, .sub f md a b, .mul f md a b,
      .div f md a b]) ++
    (pool.flatMap fun a => [FpReq.sqrt f md a, .toInt f md true 32 a, .toInt f md false 32 a,
      .toInt f md true 64 a, .toInt f md false 64 a]) ++
    (small.flatMap fun a => small.flatMap fun b => small.map fun c => FpReq.fma f md a b c)) ++
  (pairs.flatMap fun (a, b) => [FpReq.minMax f false a b, .minMax f true a b, .eq f a b,
    .lt f a b, .le f a b]) ++
  pool.map (FpReq.cls f)

/-- Integer operands for `fcvt.{s,d}.{w,wu,l,lu}`. -/
def intPool : List Nat :=
  [0, 1, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 24 + 1, 2 ^ 53 + 1, 2 ^ 63, 2 ^ 64 - 1,
   0x123456789abcdef1, 0xfedcba9876543211]

/-- All pool requests. -/
def poolAll : List FpReq :=
  poolReqs fmtSingle pool32 ++ poolReqs fmtDouble pool64 ++
  (modes.flatMap fun md =>
    (pool64.map (FpReq.convert fmtDouble fmtSingle md)) ++
    (pool32.map (FpReq.convert fmtSingle fmtDouble md)) ++
    ([fmtSingle, fmtDouble].flatMap fun f => intPool.flatMap fun v =>
      [FpReq.ofInt f md true 32 v, .ofInt f md false 32 v, .ofInt f md true 64 v,
        .ofInt f md false 64 v]))

/-- The pool requests on which the two kernels differ. -/
def poolDisagreements : List FpReq :=
  poolAll.filter fun r => FpuImpl.lps.run r != FpuImpl.ieee.run r

end Silmaril.RiscV.LPS.TestFloat
