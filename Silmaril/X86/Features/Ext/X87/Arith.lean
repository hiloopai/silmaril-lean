module

public import Silmaril.X86.Features.State

/-!
# x87 extended-precision arithmetic

Exact arithmetic on the x87 data formats (SDM Vol. 1, §4.2, §4.8 and §8.2) with
correct rounding, written on natural-number significands and integer exponents:

* `classify` reads an 80-bit register image as a `Val` (zero, finite with its
  exact value `m · 2^e`, infinity, NaN, or an unsupported encoding: an unnormal,
  pseudo-infinity or pseudo-NaN, which the 387 and later reject, §8.2.2);
* `round` rounds an exact value `(m + f) · 2^e` (`0 ≤ f < 1`, `f > 0` exactly
  when `sticky`) to `p` significant bits in the rounding direction, in an
  exponent range with gradual underflow, and reports inexactness, underflow
  and overflow (§4.9.1);
* `add`, `mul`, `div`, `sqrt`, `roundInt`, `scale`, `prem` and the format
  conversions build on it.

## Conventions observed on hardware

These points are implementation choices the SDM leaves open or states only
loosely; each was checked on an Intel Core i7-8700 by the differential vectors
(`scripts/x86-features/gen_x87_vectors.py`):

* tininess is detected *after* rounding (an exact product `(1 - 2^-66) · 2^-16382`
  rounds to the smallest normal and does not signal underflow);
* precision control applies to tiny results as well, at a fixed position:
  the quantum is `max(2^(L-p+1), 2^(-16382-p+1))` for a result with leading
  bit `2^L`, so the low `64 - p` bits of the significand field are always zero
  (a product that underflows completely under double precision, rounded up, is
  `0x800 · 2^-16445`, not `2^-16445`);
* of two quiet NaNs with equal significands the result is negative only if
  both are (SDM Vol. 1, Table 4-7 covers only unequal significands);
* FPREM and FPREM1 with an exponent difference `D ≥ 64` reduce by
  `2^(D - N)` with `N = 32 + (D mod 32)` (the SDM says only "an
  implementation-dependent number between 32 and 63"), and clear C0, C1 and
  C3 (which the SDM leaves undefined) when the reduction is incomplete;
* FSQRT of a negative denormal signals invalid only, and a denormal divided
  by zero signals divide-by-zero only, not denormal-operand;
* an unsupported operand (unnormal, pseudo-NaN, pseudo-infinity) is invalid
  even when the other operand is a NaN.
-/

@[expose] public section

namespace Silmaril.X86.Features.Fpu

/-! ## Rounding control and exception flags -/

/-- The x87 rounding control (control word bits 11:10, SDM Vol. 1, Table 4-8). -/
inductive RC where
  | nearest | down | up | zero
  deriving DecidableEq, Repr

def RC.ofBits (b : BitVec 2) : RC :=
  match b.toNat with
  | 0 => .nearest
  | 1 => .down
  | 2 => .up
  | _ => .zero

/-- The six x87 exception conditions (status word bits 5:0) and the stack
fault (bit 6, which always accompanies `ie`). -/
structure Exc where
  ie : Bool := false
  de : Bool := false
  ze : Bool := false
  oe : Bool := false
  ue : Bool := false
  pe : Bool := false
  sf : Bool := false
  deriving DecidableEq, Repr

namespace Exc

def none : Exc := {}

def union (a b : Exc) : Exc :=
  ⟨a.ie || b.ie, a.de || b.de, a.ze || b.ze, a.oe || b.oe, a.ue || b.ue, a.pe || b.pe,
    a.sf || b.sf⟩

/-- The flags as status-word bits 6:0. -/
def bits (x : Exc) : BitVec 16 :=
  (if x.ie then 1 else 0) ||| (if x.de then 2 else 0) ||| (if x.ze then 4 else 0) |||
    (if x.oe then 8 else 0) ||| (if x.ue then 0x10 else 0) ||| (if x.pe then 0x20 else 0) |||
    (if x.sf then 0x40 else 0)

/-- The pre-computation conditions (invalid, denormal operand, divide by zero). -/
def pre (x : Exc) : Exc := { ie := x.ie, de := x.de, ze := x.ze, sf := x.sf }

end Exc

/-! ## Bit lengths -/

/-- The number of significant bits of `n` (0 for 0). -/
def bitlen (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-! ## Correct rounding -/

/-- A rounded magnitude `q · 2^k`, whether it differs from the exact value,
and whether its magnitude is larger (x87 C1, "rounded up"). -/
structure Rounded where
  q : Nat
  k : Int
  inexact : Bool
  up : Bool
  deriving DecidableEq, Repr

/-- Round the magnitude `(m + f) · 2^e` of a value with sign `s` to a multiple
of `2^k`. `sticky` says `f > 0`; callers supply `k > e` whenever `sticky`. -/
def roundAt (rc : RC) (s : Bool) (m : Nat) (e : Int) (sticky : Bool) (k : Int) : Rounded :=
  if k ≤ e then ⟨m <<< (e - k).toNat, k, sticky, false⟩
  else
    let d := (k - e).toNat
    let q := m >>> d
    let r := m % 2 ^ d
    let half := 2 ^ (d - 1)
    let inexact := r != 0 || sticky
    let up := match rc with
      | .nearest => decide (r > half) || (r == half && (sticky || q % 2 == 1))
      | .zero => false
      | .down => s && inexact
      | .up => !s && inexact
    ⟨if up then q + 1 else q, k, inexact, up⟩

/-- A binary floating-point format for rounding: `p` significant bits, normal
exponents from `emin` to `emax` (of the leading bit), and the quantum of the
subnormals `2^(emin - fullPrec + 1)`. For the IEEE memory formats `fullPrec = p`;
for the x87 registers the subnormal quantum follows the precision control as
well (observed on hardware), so `Fmt.ext p` also has `fullPrec = p`. -/
structure Fmt where
  p : Nat
  fullPrec : Nat
  emin : Int
  emax : Int
  deriving DecidableEq, Repr

/-- The x87 register format with precision control `p` (24, 53 or 64). -/
def Fmt.ext (p : Nat) : Fmt := ⟨p, p, -16382, 16383⟩
def Fmt.single : Fmt := ⟨24, 24, -126, 127⟩
def Fmt.double : Fmt := ⟨53, 53, -1022, 1023⟩

def Fmt.kmin (f : Fmt) : Int := f.emin - f.fullPrec + 1

/-- The outcome of rounding a nonzero exact value. -/
inductive RoundOut where
  /-- A finite result `q · 2^k` (possibly zero after underflow). -/
  | finite (r : Rounded) (tiny : Bool)
  /-- The rounded value exceeds the largest finite number. -/
  | overflow
  deriving DecidableEq, Repr

/-- The leading-bit exponent of `m · 2^e`, `m > 0`. -/
def lead (m : Nat) (e : Int) : Int := e + (bitlen m : Int) - 1

/-- Round a nonzero exact magnitude `(m + f) · 2^e` to the format. Tininess is
detected after rounding (with an unbounded exponent range); the result is
rounded at the larger of the precision quantum and the subnormal quantum. -/
def round (fmt : Fmt) (rc : RC) (s : Bool) (m : Nat) (e : Int) (sticky : Bool) : RoundOut :=
  let ku := lead m e - fmt.p + 1
  let ru := roundAt rc s m e sticky ku
  let tiny := decide (lead ru.q ru.k < fmt.emin)
  let r := roundAt rc s m e sticky (max ku fmt.kmin)
  if r.q != 0 && lead r.q r.k > fmt.emax then .overflow else .finite r tiny

/-- The largest finite magnitude `(2^p - 1) · 2^(emax - p + 1)`. -/
def Fmt.maxQ (f : Fmt) : Nat × Int := (2 ^ f.p - 1, f.emax - f.p + 1)

/-- Whether a masked overflow delivers infinity (otherwise the largest finite
value), SDM Vol. 1, Table 4-10. -/
def RC.overflowsToInf (rc : RC) (s : Bool) : Bool :=
  match rc with
  | .nearest => true
  | .zero => false
  | .down => s
  | .up => !s

/-! ## The 80-bit format -/

/-- The fields of a register image. -/
def sign80 (x : BitVec 80) : Bool := x.getLsbD 79
def exp80 (x : BitVec 80) : Nat := (x.extractLsb' 64 15).toNat
def sig80 (x : BitVec 80) : Nat := (x.extractLsb' 0 64).toNat

def mk80 (s : Bool) (e : Nat) (sig : Nat) : BitVec 80 :=
  BitVec.ofBool s ++ BitVec.ofNat 15 e ++ BitVec.ofNat 64 sig

/-- The real indefinite: the default QNaN (SDM Vol. 1, Table 4-3). -/
def indefinite : BitVec 80 := mk80 true 0x7FFF 0xC000000000000000

def zero80 (s : Bool) : BitVec 80 := mk80 s 0 0
def inf80 (s : Bool) : BitVec 80 := mk80 s 0x7FFF 0x8000000000000000

/-- A classified register value. Finite values carry their exact magnitude
`m · 2^e`. -/
inductive Val where
  | zero (s : Bool)
  | fin (s : Bool) (m : Nat) (e : Int)
  | inf (s : Bool)
  /-- A NaN, with its register image. -/
  | nan (x : BitVec 80)
  /-- Unnormal, pseudo-infinity or pseudo-NaN (SDM Vol. 1, §8.2.2). -/
  | unsupported
  deriving DecidableEq, Repr

def classify (x : BitVec 80) : Val :=
  let s := sign80 x
  let E := exp80 x
  let m := sig80 x
  let j := decide (m ≥ 2 ^ 63)
  if E = 0 then
    if m = 0 then .zero s else .fin s m (-16445)
  else if E = 0x7FFF then
    if !j then .unsupported
    else if m = 2 ^ 63 then .inf s else .nan x
  else if !j then .unsupported
  else .fin s m ((E : Int) - 16446)

/-- A denormal or pseudo-denormal register value (exponent field 0, nonzero
significand): the denormal-operand condition. -/
def isDenormal80 (x : BitVec 80) : Bool := exp80 x == 0 && sig80 x != 0

/-- An SNaN: a NaN with significand bit 62 clear. -/
def isSNaN80 (x : BitVec 80) : Bool :=
  match classify x with
  | .nan _ => !x.getLsbD 62
  | _ => false

def isNaN80 (x : BitVec 80) : Bool :=
  match classify x with
  | .nan _ => true
  | _ => false

/-- Quiet a NaN: set significand bit 62. -/
def quiet80 (x : BitVec 80) : BitVec 80 := x ||| (1#80 <<< 62)

/-- Pack a rounded magnitude `q · 2^k` with sign `s`: normal when the leading
bit is at least `2^-16382`, denormal otherwise. -/
def pack80 (s : Bool) (q : Nat) (k : Int) : BitVec 80 :=
  if q = 0 then zero80 s
  else
    let b := bitlen q
    let L := lead q k
    if L ≥ -16382 then
      mk80 s (L + 16383).toNat (if b ≤ 64 then q <<< (64 - b) else q >>> (b - 64))
    else mk80 s 0 (q <<< (k + 16445).toNat)

/-! ## Results of arithmetic -/

/-- A delivered value with the conditions detected and C1 ("rounded up"). -/
structure Out where
  value : BitVec 80
  exc : Exc := {}
  c1 : Bool := false
  /-- The result is tiny (after rounding); `exc.ue` is the masked underflow
  condition, tiny and inexact. -/
  tiny : Bool := false
  deriving DecidableEq, Repr

/-- The masked response to an invalid operation: the indefinite. -/
def invalid : Out := ⟨indefinite, { ie := true }, false, false⟩

/-- Round an exact nonzero magnitude to a register value with precision `p`. -/
def roundExt (p : Nat) (rc : RC) (s : Bool) (m : Nat) (e : Int) (sticky : Bool) (exc : Exc) :
    Out :=
  match round (Fmt.ext p) rc s m e sticky with
  | .overflow =>
    if rc.overflowsToInf s then ⟨inf80 s, { exc with oe := true, pe := true }, true, false⟩
    else
      let mq := (Fmt.ext p).maxQ
      ⟨pack80 s mq.1 mq.2, { exc with oe := true, pe := true }, false, false⟩
  | .finite r tiny =>
    ⟨pack80 s r.q r.k, { exc with ue := tiny && r.inexact, pe := r.inexact }, r.up, tiny⟩

/-- The NaN result of a two-operand operation with at least one NaN operand
(SDM Vol. 1, Table 4-7, x87 column): an SNaN signals invalid and is quieted; a
QNaN wins over an SNaN; of two NaNs of the same kind the larger significand
wins, and on a tie the result is negative only if both are. -/
def nan2 (x y : BitVec 80) : Out :=
  let ie := isSNaN80 x || isSNaN80 y
  let pick :=
    if isNaN80 x && isNaN80 y then
      if isSNaN80 x != isSNaN80 y then (if isSNaN80 x then y else x)
      else if sig80 x > sig80 y then x
      else if sig80 y > sig80 x then y
      else if sign80 x then y else x
    else if isNaN80 x then x else y
  ⟨quiet80 pick, { ie }, false, false⟩

/-- The NaN result of a one-operand operation. -/
def nan1 (x : BitVec 80) : Out := ⟨quiet80 x, { ie := isSNaN80 x }, false, false⟩

/-- The denormal-operand condition of the operands. -/
def deOf (xs : List (BitVec 80)) : Exc := { de := xs.any isDenormal80 }

/-- The sign of an exact zero sum (SDM Vol. 1, §4.8.3.4 and Table 4-?): the
common sign, or `-0` only when rounding down. -/
def zeroSumSign (rc : RC) (sx sy : Bool) : Bool := if sx == sy then sx else rc == .down

/-- `x + y` with the signs `sx`, `sy` (subtraction negates `sy`). -/
def addVals (p : Nat) (rc : RC) (x y : BitVec 80) (negY : Bool) (xde : Bool := false) : Out :=
  let de : Exc := { de := xde || (deOf [x, y]).de }
  match classify x, classify y with
  | .unsupported, _ | _, .unsupported => invalid
  | .nan _, _ | _, .nan _ => nan2 x y
  | .inf sx, .inf sy =>
    if sx == (sy != negY) then ⟨inf80 sx, {}, false, false⟩ else invalid
  | .inf sx, _ => ⟨inf80 sx, de, false, false⟩
  | _, .inf sy => ⟨inf80 (sy != negY), de, false, false⟩
  | vx, vy =>
    let part : Val → Bool × Nat × Int := fun
      | .fin s m e => (s, m, e)
      | .zero s => (s, 0, 0)
      | _ => (false, 0, 0)
    let (sx, mx, ex) := part vx
    let (sy0, my, ey) := part vy
    let sy := sy0 != negY
    if mx = 0 && my = 0 then ⟨zero80 (zeroSumSign rc sx sy), de, false, false⟩
    else
      let e := if mx = 0 then ey else if my = 0 then ex else min ex ey
      let ax := mx <<< (ex - e).toNat
      let ay := my <<< (ey - e).toNat
      if sx == sy then roundExt p rc sx (ax + ay) e false de
      else if ax == ay then ⟨zero80 (zeroSumSign rc sx sy), de, false, false⟩
      else if ax > ay then roundExt p rc sx (ax - ay) e false de
      else roundExt p rc sy (ay - ax) e false de

def mulVals (p : Nat) (rc : RC) (x y : BitVec 80) (xde : Bool := false) : Out :=
  let de : Exc := { de := xde || (deOf [x, y]).de }
  match classify x, classify y with
  | .unsupported, _ | _, .unsupported => invalid
  | .nan _, _ | _, .nan _ => nan2 x y
  | .inf _, .zero _ | .zero _, .inf _ => invalid
  | .inf sx, .inf sy | .inf sx, .fin sy _ _ | .fin sx _ _, .inf sy => ⟨inf80 (sx != sy), de, false, false⟩
  | .zero sx, .zero sy | .zero sx, .fin sy _ _ | .fin sx _ _, .zero sy =>
    ⟨zero80 (sx != sy), de, false, false⟩
  | .fin sx mx ex, .fin sy my ey => roundExt p rc (sx != sy) (mx * my) (ex + ey) false de

/-- `x / y`. -/
def divVals (p : Nat) (rc : RC) (x y : BitVec 80) (xde : Bool := false) : Out :=
  let de : Exc := { de := xde || (deOf [x, y]).de }
  match classify x, classify y with
  | .unsupported, _ | _, .unsupported => invalid
  | .nan _, _ | _, .nan _ => nan2 x y
  | .inf _, .inf _ | .zero _, .zero _ => invalid
  | .inf sx, .fin sy _ _ | .inf sx, .zero sy => ⟨inf80 (sx != sy), de, false, false⟩
  | .fin sx _ _, .inf sy | .zero sx, .inf sy | .zero sx, .fin sy _ _ =>
    ⟨zero80 (sx != sy), de, false, false⟩
  -- divide-by-zero takes precedence over a denormal dividend (observed on hardware)
  | .fin sx _ _, .zero sy => ⟨inf80 (sx != sy), { ze := true }, false, false⟩
  | .fin sx mx ex, .fin sy my ey =>
    -- at least 66 quotient bits, so the remainder is below the rounding point
    let sh := 66 + bitlen my - bitlen mx + 1
    let q := (mx <<< sh) / my
    let r := (mx <<< sh) % my
    roundExt p rc (sx != sy) q (ex - ey - sh) (r != 0) de

/-- The integer square root, by binary digits from the top (`fuel` digits). -/
def isqrtAux : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let c := acc ||| (1 <<< fuel)
    isqrtAux fuel n (if c * c ≤ n then c else acc)

/-- `⌊√n⌋`. -/
def isqrt (n : Nat) : Nat := isqrtAux (bitlen n / 2 + 1) n 0

def sqrtVal (p : Nat) (rc : RC) (x : BitVec 80) : Out :=
  let de := deOf [x]
  match classify x with
  | .nan _ => nan1 x
  | .unsupported => invalid
  | .zero s => ⟨zero80 s, {}, false, false⟩
  | .inf false => ⟨inf80 false, {}, false, false⟩
  | .inf true => invalid
  | .fin true _ _ => invalid
  | .fin false m e =>
    -- shift so that the exponent is even and the root has at least 66 bits
    let sh0 := 140 - bitlen m
    let sh := if (e - sh0) % 2 = 0 then sh0 else sh0 + 1
    let n := m <<< sh
    let q := isqrt n
    roundExt p rc false q ((e - sh) / 2) (q * q != n) de

/-! ## Comparisons -/

/-- The order of two non-NaN supported values. -/
def cmpFinite (vx vy : Val) : Ordering :=
  let mag : Val → Bool × Nat × Int := fun
    | .fin s m e => (s, m, e)
    | _ => (false, 0, 0)
  match vx, vy with
  | .inf a, .inf b => if a == b then .eq else if a then .lt else .gt
  | .inf a, _ => if a then .lt else .gt
  | _, .inf b => if b then .gt else .lt
  | .zero _, .zero _ => .eq
  | _, _ =>
    let (sx, mx, ex) := mag vx
    let (sy, my, ey) := mag vy
    let zx := match vx with | .zero _ => true | _ => false
    let zy := match vy with | .zero _ => true | _ => false
    -- signed comparison of mx·2^ex and my·2^ey
    let e := min ex ey
    let ax : Int := if zx then 0 else (if sx then -1 else 1) * ((mx <<< (ex - e).toNat : Nat) : Int)
    let ay : Int := if zy then 0 else (if sy then -1 else 1) * ((my <<< (ey - e).toNat : Nat) : Int)
    compare ax ay

/-- Compare two register values: `none` is unordered. `signaling` raises
invalid on every NaN (FCOM, FCOMI, FTST, FICOM); otherwise only on SNaNs
(FUCOM, FUCOMI). Unsupported operands always raise invalid. -/
def compareVals (signaling : Bool) (x y : BitVec 80) (xde : Bool := false) :
    Option Ordering × Exc :=
  match classify x, classify y with
  | .unsupported, _ | _, .unsupported => (none, { ie := true })
  | .nan _, _ | _, .nan _ =>
    (none, { ie := signaling || isSNaN80 x || isSNaN80 y })
  | vx, vy => (some (cmpFinite vx vy), { de := xde || (deOf [x, y]).de })

/-! ## Conversions -/

/-- The exact register value of an IEEE single or double (`p` significant bits
including the hidden one, exponent width `w`). An SNaN stays signaling. -/
def ofIeee (p w : Nat) (bits : Nat) : BitVec 80 :=
  let s := bits >>> (p - 1 + w) % 2 == 1
  let E := (bits >>> (p - 1)) % 2 ^ w
  let f := bits % 2 ^ (p - 1)
  let bias : Int := 2 ^ (w - 1) - 1
  if E = 0 then
    if f = 0 then zero80 s
    else pack80 s f (1 - bias - (p - 1 : Nat))
  else if E = 2 ^ w - 1 then
    if f = 0 then inf80 s
    else mk80 s 0x7FFF (2 ^ 63 + f <<< (64 - p))
  else pack80 s (2 ^ (p - 1) + f) ((E : Int) - bias - (p - 1 : Nat))

/-- Whether an IEEE single/double image is denormal, or an SNaN. -/
def ieeeDenormal (p w : Nat) (bits : Nat) : Bool :=
  (bits >>> (p - 1)) % 2 ^ w == 0 && bits % 2 ^ (p - 1) != 0

/-- An IEEE single or double result of FST: the image, the conditions, C1 and
tininess. -/
structure IOut where
  bits : Nat
  exc : Exc := {}
  c1 : Bool := false
  tiny : Bool := false
  deriving DecidableEq, Repr

/-- The IEEE indefinite of a format with `p` significant bits and exponent
width `w`. -/
def ieeeIndefinite (p w : Nat) : Nat :=
  (1 <<< (p - 1 + w)) ||| ((2 ^ w - 1) <<< (p - 1)) ||| (1 <<< (p - 2))

/-- Round a register value to an IEEE single or double for FST (precision
control does not apply). -/
def toIeee (fmt : Fmt) (w : Nat) (rc : RC) (x : BitVec 80) : IOut :=
  let p := fmt.p
  let bias : Int := 2 ^ (w - 1) - 1
  let s := sign80 x
  let sbits : Nat := if s then 1 <<< (p - 1 + w) else 0
  let infBits := sbits ||| ((2 ^ w - 1) <<< (p - 1))
  let packI : Nat → Int → Nat := fun q k =>
    if q = 0 then sbits
    else
      let L := lead q k
      if L ≥ fmt.emin then
        let b := bitlen q
        let qq := if b ≤ p then q <<< (p - b) else q >>> (b - p)
        sbits ||| (((L + bias).toNat) <<< (p - 1)) ||| (qq - 2 ^ (p - 1))
      else sbits ||| (q <<< (k - fmt.kmin).toNat)
  match classify x with
  | .zero _ => ⟨sbits, {}, false, false⟩
  | .inf _ => ⟨infBits, {}, false, false⟩
  | .unsupported => ⟨ieeeIndefinite p w, { ie := true }, false, false⟩
  | .nan _ =>
    let frac := (sig80 x % 2 ^ 63) >>> (64 - p)
    ⟨infBits ||| frac ||| (1 <<< (p - 2)), { ie := isSNaN80 x }, false, false⟩
  | .fin _ m e =>
    match round fmt rc s m e false with
    | .overflow =>
      if rc.overflowsToInf s then ⟨infBits, { oe := true, pe := true }, true, false⟩
      else
        let mq := fmt.maxQ
        ⟨packI mq.1 mq.2, { oe := true, pe := true }, false, false⟩
    | .finite r tiny =>
      ⟨packI r.q r.k, { ue := tiny && r.inexact, pe := r.inexact }, r.up, tiny⟩

/-- The register value of a two's-complement integer of `n` bits. -/
def ofInt (n : Nat) (v : Nat) : BitVec 80 :=
  let neg := v >>> (n - 1) % 2 == 1
  let mag := if neg then 2 ^ n - v else v
  if mag = 0 then zero80 false else pack80 neg mag 0

/-- Round a register value to an integer in the rounding direction (`trunc`
for FISTTP). Returns the rounded magnitude with its sign, inexactness and C1. -/
def toIntegral (rc : RC) (x : BitVec 80) : Option (Bool × Nat × Bool × Bool) :=
  match classify x with
  | .zero s => some (s, 0, false, false)
  | .fin s m e =>
    let r := roundAt rc s m e false 0
    some (s, r.q, r.inexact, r.up)
  | _ => none

/-- FIST/FISTP/FISTTP: the `n`-bit integer image, or the integer indefinite
with invalid for NaN, infinity, unsupported and out-of-range values. -/
def toInt (n : Nat) (rc : RC) (x : BitVec 80) : Nat × Exc × Bool :=
  let indef := 2 ^ (n - 1)
  match toIntegral rc x with
  | none => (indef, { ie := true }, false)
  | some (s, q, inexact, up) =>
    if (s && q > 2 ^ (n - 1)) || (!s && q ≥ 2 ^ (n - 1)) then (indef, { ie := true }, false)
    else ((if s then (2 ^ n - q) % 2 ^ n else q), { pe := inexact }, up)

/-- FRNDINT: round to an integral value, kept in the register format. -/
def roundIntVal (rc : RC) (x : BitVec 80) : Out :=
  match classify x with
  | .nan _ => nan1 x
  | .unsupported => invalid
  | .zero _ | .inf _ => ⟨x, {}, false, false⟩
  | .fin s m e =>
    let r := roundAt rc s m e false 0
    ⟨if r.q = 0 then zero80 s else pack80 s r.q 0, { deOf [x] with pe := r.inexact }, r.up, false⟩

/-- `x · 2^n` for FSCALE, with `n` already truncated toward zero. -/
def scaleVal (rc : RC) (x : BitVec 80) (n : Int) : Out :=
  match classify x with
  | .fin s m e =>
    -- beyond ±2^17 every finite value over- or underflows
    let n := max (-70000) (min 70000 n)
    roundExt 64 rc s m (e + n) false (deOf [x])
  | _ => ⟨x, {}, false, false⟩

/-- The scale of FSCALE: ST(1) truncated toward zero. Magnitudes of at least
`2^104` are replaced by `±10^6`, which over- or underflows every finite value
just as the true scale does. -/
def truncScale (x : BitVec 80) : Int :=
  match classify x with
  | .fin s m e =>
    if e > 40 then (if s then -1000000 else 1000000)
    else
      let mag : Nat := if e ≥ 0 then (m <<< e.toNat) else m >>> (-e).toNat
      if s then -(mag : Int) else mag
  | _ => 0

def FSCALE (rc : RC) (x y : BitVec 80) : Out :=
  match classify x, classify y with
  | .unsupported, _ | _, .unsupported => invalid
  | .nan _, _ | _, .nan _ => nan2 x y
  | .inf sx, .inf false => ⟨inf80 sx, {}, false, false⟩
  | .inf _, .inf true => invalid
  | .zero _, .inf false => invalid
  | .zero sx, .inf true => ⟨zero80 sx, deOf [x, y], false, false⟩
  | .fin sx _ _, .inf false => ⟨inf80 sx, deOf [x, y], false, false⟩
  | .fin sx _ _, .inf true => ⟨zero80 sx, deOf [x, y], false, false⟩
  | .inf sx, _ => ⟨inf80 sx, deOf [x, y], false, false⟩
  | .zero sx, _ => ⟨zero80 sx, deOf [x, y], false, false⟩
  | .fin _ _ _, _ =>
    let o := scaleVal rc x (truncScale y)
    { o with exc := o.exc.union (deOf [x, y]) }

/-! ## Partial remainder -/

/-- The result of FPREM/FPREM1: the value, the conditions, and the condition
codes C0, C1, C2, C3 (`none` leaves the code unchanged). -/
structure PremOut where
  value : BitVec 80
  exc : Exc
  c0 : Option Bool
  c1 : Option Bool
  c2 : Option Bool
  c3 : Option Bool
  deriving DecidableEq, Repr

/-- FPREM (`nearest = false`, truncating quotient) and FPREM1 (`nearest =
true`, IEEE remainder). -/
def premVal (nearest : Bool) (x y : BitVec 80) : PremOut :=
  let inv : PremOut := ⟨indefinite, { ie := true }, none, some false, some false, none⟩
  match classify x, classify y with
  | .unsupported, _ | _, .unsupported => inv
  | .nan _, _ | _, .nan _ =>
    let o := nan2 x y
    ⟨o.value, o.exc, none, some false, some false, none⟩
  | .inf _, _ => inv
  | _, .zero _ => inv
  | .zero _, _ => ⟨x, deOf [x, y], some false, some false, some false, some false⟩
  | .fin _ _ _, .inf _ => ⟨x, deOf [x, y], some false, some false, some false, some false⟩
  | .fin sx mx ex, .fin _ my ey =>
    let de := deOf [x, y]
    let d := lead mx ex - lead my ey
    let e := min ex ey
    let ax := mx <<< (ex - e).toNat
    let ay := my <<< (ey - e).toNat
    if d < 64 then
      let q0 := ax / ay
      let r0 := ax % ay
      -- FPREM1 rounds the quotient to nearest, ties to even
      let up := nearest && (2 * r0 > ay || (2 * r0 == ay && q0 % 2 == 1))
      let q := if up then q0 + 1 else q0
      let value :=
        if up then (if ay - r0 = 0 then zero80 sx else pack80 (!sx) (ay - r0) e)
        else if r0 = 0 then zero80 sx else pack80 sx r0 e
      ⟨value, de, some (q / 4 % 2 == 1), some (q % 2 == 1), some false, some (q / 2 % 2 == 1)⟩
    else
      let n : Int := 32 + d % 32
      let shift := (d - n).toNat
      let ys := ay <<< shift
      let r := ax % ys
      ⟨if r = 0 then zero80 sx else pack80 sx r e, de, some false, some false, some true,
        some false⟩

/-! ## FXTRACT -/

/-- FXTRACT: the exponent (to ST(1)) and the significand (to ST(0)), or `none`
for the conditions only. -/
def xtractVal (x : BitVec 80) : BitVec 80 × BitVec 80 × Exc :=
  match classify x with
  | .nan _ => let o := nan1 x; (o.value, o.value, o.exc)
  | .unsupported => (indefinite, indefinite, { ie := true })
  | .zero s => (inf80 true, zero80 s, { ze := true })
  | .inf s => (inf80 false, inf80 s, {})
  | .fin s m e =>
    let L := lead m e
    let expo : BitVec 80 := if L = 0 then zero80 false else pack80 (L < 0) L.natAbs 0
    (expo, pack80 s m (e - L), deOf [x])

/-! ## Constants -/

/-- The constants of FLD1, FLDL2T, FLDL2E, FLDPI, FLDLG2, FLDLN2 and FLDZ as
128-bit truncations with their binary exponent (value `m · 2^e`, `m` with
leading bit 2^127) and whether the truncation is exact. They are rounded to 64
bits in the rounding direction without signalling precision (SDM Vol. 2,
FLD1/FLDL2T/...: "rounded as specified by RC"). -/
def constant : Nat → Option (Nat × Int × Bool)
  | 0 => some (2 ^ 127, -127, false)                                           -- 1
  | 1 => some (0xD49A784BCD1B8AFE492BF6FF4DAFDB4C, -126, true)                 -- log2 10
  | 2 => some (0xB8AA3B295C17F0BBBE87FED0691D3E88, -127, true)                 -- log2 e
  | 3 => some (0xC90FDAA22168C234C4C6628B80DC1CD1, -126, true)                 -- pi
  | 4 => some (0x9A209A84FBCFF7988F8959AC0B7C9178, -129, true)                 -- log10 2
  | 5 => some (0xB17217F7D1CF79ABC9E3B39803F2F6AF, -128, true)                 -- ln 2
  | _ => none

/-- The register value of a constant, rounded in direction `rc`. -/
def constVal (rc : RC) (c : Nat) : BitVec 80 :=
  match constant c with
  | some (m, e, sticky) =>
    let r := roundAt rc false m e sticky (e + 64)
    pack80 false r.q r.k
  | none => zero80 false

end Silmaril.X86.Features.Fpu
