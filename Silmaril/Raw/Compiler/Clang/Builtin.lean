module

public import Silmaril.Cerberus.Ail.Syntax.Defs

/-! # GNU semantic builtins lowered to synthesized functions

Typed Ail has no node for GCC's semantic builtins, so the Clang frontend lowers them itself. Each call becomes a call of a static function that the translation defines once
per builtin and operand types (`__cfront_builtin<k>`), so every operand is evaluated exactly
once, as an argument, and the builtin's own evaluation order (unspecified, like a call's) is
kept. The bodies, built here, use only ordinary C operators on `float`, `double` and the
integer types, with gcc's x86-64 results at `-O0`:

* **Comparisons** (`compare`): `isgreater` `>`, `isgreaterequal` `>=`, `isless` `<`,
  `islessequal` `<=`, `islessgreater` `a < b || a > b`, `isunordered` `a != a || b != b`, on the
  operands as Clang converted them (one floating type).
* **Classification** (`classify`): `isnan` `x != x`, `isinf` `x != x ? 0 : x - x != x - x`,
  `isfinite` `x - x == x - x` (IEEE: `x - x` is `0` for a finite `x`, NaN otherwise), and
  `signbit`, the sign bit read from the bytes of the value as a `double` (exact for a `float`
  too): `1` for a `double` and `INT_MIN` for a `float`, as gcc gives them.
* **Bit-exact values**: `copysign` (`copysign`) sets the sign byte of a `double` copy of its
  first operand to that of its second; `nan("")` (`nan`) builds gcc's quiet NaN
  `0x7ff8000000000000` byte by byte (a `float` is that value converted).
* **Overflow** (`overflow`, `overflowCore`): `__builtin_{add,sub,mul}_overflow(a, b, &r)` and
  the typed `s`/`u` forms compute the exact result as a sign and a 128-bit magnitude in
  `unsigned long` limbs, store it modulo `2^N` into `*r` and return whether it does not fit in
  `r`'s type.

The constants `__builtin_inf()` and `__builtin_huge_val()` are `1.0 / 0.0` (no helper, so they
stay constant expressions); `__builtin_prefetch` evaluates and discards its address.
-/

@[expose] public section

namespace Silmaril.Clang.Builtin

open Silmaril.Cerberus Ail

def noQ : Qualifiers := ⟨false, false, false⟩

def ty (n : CtypeNode) : Ctype := .mk [] n
def intT : Ctype := ty (.basic (.integer (.signed .int)))
def ulT : Ctype := ty (.basic (.integer (.unsigned .long)))
def ucharT : Ctype := ty (.basic (.integer (.unsigned .ichar)))
def boolT : Ctype := ty (.basic (.integer .bool))
def dblT : Ctype := ty (.basic (.floating (.realFloating .double)))
def ptrT (t : Ctype) : Ctype := ty (.pointer noQ t)

/-- The type of an rvalue of an integer, floating or pointer type. -/
def gen : Ctype → GenType
  | .mk _ (.basic (.integer it)) => .basic (.integer (.concrete it))
  | .mk _ (.basic (.floating ft)) => .basic (.floating ft)
  | .mk _ (.pointer q t) => .pointer q t
  | _ => .void

def lv (t : Ctype) (n : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk (.lvalue noQ t false) [] .unknown n

def rv (t : Ctype) (n : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk (.rvalue (gen t)) [] .unknown n

def load (t : Ctype) (e : TypedExpression) : TypedExpression := rv t (.rvalue e)

/-- The value of the parameter or local `s` of type `t`. -/
def get (t : Ctype) (s : Sym) : TypedExpression := load t (lv t (.ident s))

def stmt (n : StatementNode GenTypeCategory) : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) n

def int (v : Int) : TypedExpression :=
  rv intT (.const (.integer (.iconstant v (if v == 0 then .octal else .decimal) none)))

def ul (v : Nat) : TypedExpression :=
  rv ulT (.const (.integer (.iconstant v (if v == 0 then .octal else .decimal) (some .ul))))

/-- `a op b` of the arithmetic operator `op`, of type `t` (operands already of type `t`). -/
def arith (t : Ctype) (op : ArithmeticOperator) (a b : TypedExpression) : TypedExpression :=
  rv t (.binary a (.arithmetic op) b)

/-- A comparison or logical operator: an `int`. -/
def test (op : BinaryOperator) (a b : TypedExpression) : TypedExpression := rv intT (.binary a op b)

def cast (t : Ctype) (e : TypedExpression) : TypedExpression := rv t (.cast noQ t e)

def cond (t : Ctype) (c a b : TypedExpression) : TypedExpression := rv t (.cond c (some a) b)

def ret (e : TypedExpression) : TypedStatement := stmt (.return_ e)

/-- A block declaring `locals` with their initialisers, in order, then `body`. -/
def block (locals : List (Sym × Ctype × TypedExpression)) (body : List TypedStatement) :
    TypedStatement :=
  stmt (.block (locals.map fun (s, t, _) => (s, ((.unknown, .automatic, false), none, noQ, t)))
    (locals.map (fun (s, _, e) => stmt (.declaration [(s, some e)])) ++ body))

/-- Byte `i` of the `double` object `d` (little-endian, so byte 7 holds the sign and the high
exponent bits): an `unsigned char` lvalue. -/
def byteOf (d : Sym) (i : Nat) : TypedExpression :=
  let p := cast (ptrT ucharT) (rv (ptrT dblT) (.unary .address (lv dblT (.ident d))))
  lv ucharT (.unary .indirection (rv (ptrT ucharT) (.binary p (.arithmetic .add) (int i))))

/-! ## Floating comparisons and classification -/

/-- `return a op b;` for the comparison builtin `name` (parameters `a`, `b` of type `t`). -/
def compare (name : String) (t : Ctype) (a b : Sym) : Option TypedStatement := do
  let x := get t a
  let y := get t b
  let e ← match name with
    | "isgreater" => some (test .gt x y)
    | "isgreaterequal" => some (test .ge x y)
    | "isless" => some (test .lt x y)
    | "islessequal" => some (test .le x y)
    | "islessgreater" => some (test .or (test .lt x y) (test .gt x y))
    | "isunordered" => some (test .or (test .ne x x) (test .ne y y))
    | _ => none
  return ret e

/-- The body of the classification builtin `name` of a parameter `x` of type `t` (`float` when
`isFloat`); `d` is a local `double`. -/
def classify (name : String) (t : Ctype) (isFloat : Bool) (x d : Sym) : Option TypedStatement := do
  let v := get t x
  let diff := arith t .sub v v
  match name with
  | "isnan" => return ret (test .ne v v)
  | "isinf" => return ret (cond intT (test .ne v v) (int 0) (test .ne diff diff))
  | "isfinite" => return ret (test .eq diff diff)
  | "signbit" =>
    let bit := arith intT .shr (load ucharT (byteOf d 7)) (int 7)
    let r := if isFloat then cond intT bit (rv intT (.const (.integer (.min (.signed .int))))) (int 0)
      else bit
    return block [(d, dblT, cast dblT v)] [ret r]
  | _ => none

/-- `copysign(x, y)` (parameters of type `t`): through `double` locals `dx` and `dy`, the sign
byte of `dx` takes the sign bit of `dy`. -/
def copysign (t : Ctype) (x y dx dy : Sym) : TypedStatement :=
  let hi := byteOf dx 7
  let v := arith intT .bor (arith intT .band (load ucharT hi) (int 127))
    (arith intT .band (load ucharT (byteOf dy 7)) (int 128))
  block [(dx, dblT, cast dblT (get t x)), (dy, dblT, cast dblT (get t y))]
    [stmt (.expr (rv ucharT (.assign hi (cast ucharT v)))), ret (cast t (get dblT dx))]

/-- `nan("")` of type `t`: gcc's quiet NaN `0x7ff8000000000000` in the local `d`. -/
def nan (t : Ctype) (d : Sym) : TypedStatement :=
  block [(d, dblT, rv dblT (.const (.floating ("0.0", none))))]
    [stmt (.expr (rv ucharT (.assign (byteOf d 6) (cast ucharT (int 248))))),
     stmt (.expr (rv ucharT (.assign (byteOf d 7) (cast ucharT (int 127))))),
     ret (cast t (get dblT d))]

/-! ## Integer overflow -/

/-- The locals of `overflowCore`, in order. -/
def coreLocals : Nat := 13

/-- `int core(int mul, int sa, UL ma, int sb, UL mb, int rs, UL rmax, UL *w)`: the exact
`(sa ? -ma : ma) + (sb ? -mb : mb)` (or `*` when `mul`), with magnitude `hi:lo`; stores its
value modulo `2^64` in `*w` and returns whether it lies outside `[rs ? -rmax-1 : 0, rmax]`.

```c
UL m32 = 4294967295UL, a0 = ma & m32, a1 = ma >> 32, b0 = mb & m32, b1 = mb >> 32,
   p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1,
   mid = (p00 >> 32) + (p01 & m32) + (p10 & m32);
UL lo = 0, hi = 0; int neg = 0;
if (mul) { lo = mid << 32 | p00 & m32; hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
           neg = sa != sb; }
else if (sa == sb) { lo = ma + mb; hi = lo < ma; neg = sa; }
else if (ma >= mb) { lo = ma - mb; neg = sa; }
else { lo = mb - ma; neg = sb; }
if (hi == 0 && lo == 0) neg = 0;
*w = neg ? 0 - lo : lo;
return hi != 0 || (neg ? (rs ? lo > rmax + 1 : 1) : lo > rmax);
```
-/
def overflowCore (ps : List Sym) (ls : List Sym) : Option TypedStatement := do
  let [mul, sa, ma, sb, mb, rs, rmax, w] := ps | none
  let [m32, a0, a1, b0, b1, p00, p01, p10, p11, mid, lo, hi, neg] := ls | none
  let u := get ulT
  let i := get intT
  let set := fun (t : Ctype) (s : Sym) (e : TypedExpression) =>
    stmt (.expr (rv t (.assign (lv t (.ident s)) e)))
  let and_ := arith ulT .band
  let shr := fun e => arith ulT .shr e (ul 32)
  let add := arith ulT .add
  let mulBranch := stmt (.block [] [
    set ulT lo (arith ulT .bor (arith ulT .shl (u mid) (ul 32)) (and_ (u p00) (u m32))),
    set ulT hi (add (add (add (u p11) (shr (u p01))) (shr (u p10))) (shr (u mid))),
    set intT neg (test .ne (i sa) (i sb))])
  let sameSign := stmt (.block [] [
    set ulT lo (add (u ma) (u mb)),
    set ulT hi (cast ulT (test .lt (u lo) (u ma))),
    set intT neg (i sa)])
  let aBigger := stmt (.block [] [set ulT lo (arith ulT .sub (u ma) (u mb)), set intT neg (i sa)])
  let bBigger := stmt (.block [] [set ulT lo (arith ulT .sub (u mb) (u ma)), set intT neg (i sb)])
  let addBranch := stmt (.if_ (test .eq (i sa) (i sb)) sameSign
    (stmt (.if_ (test .ge (u ma) (u mb)) aBigger bBigger)))
  let wp := ptrT ulT
  let out := lv ulT (.unary .indirection (get wp w))
  let outside := test .or (test .ne (u hi) (ul 0))
    (cond intT (i neg) (cond intT (i rs) (test .gt (u lo) (add (u rmax) (ul 1))) (int 1))
      (test .gt (u lo) (u rmax)))
  return block
    [(m32, ulT, ul 4294967295), (a0, ulT, and_ (u ma) (u m32)), (a1, ulT, shr (u ma)),
     (b0, ulT, and_ (u mb) (u m32)), (b1, ulT, shr (u mb)),
     (p00, ulT, arith ulT .mul (u a0) (u b0)), (p01, ulT, arith ulT .mul (u a0) (u b1)),
     (p10, ulT, arith ulT .mul (u a1) (u b0)), (p11, ulT, arith ulT .mul (u a1) (u b1)),
     (mid, ulT, add (add (shr (u p00)) (and_ (u p01) (u m32))) (and_ (u p10) (u m32))),
     (lo, ulT, ul 0), (hi, ulT, ul 0), (neg, intT, int 0)]
    [stmt (.if_ (test .ne (i mul) (int 0)) mulBranch addBranch),
     stmt (.if_ (test .and (test .eq (u hi) (ul 0)) (test .eq (u lo) (ul 0)))
       (set intT neg (int 0)) (stmt .skip)),
     stmt (.expr (rv ulT (.assign out (cond ulT (i neg) (arith ulT .sub (ul 0) (u lo)) (u lo))))),
     ret outside]

/-- The parameter types of `overflowCore`. -/
def coreParams : List Ctype := [intT, intT, ulT, intT, ulT, intT, ulT, ptrT ulT]

/-- `_Bool f(A a, B b, R *r)` for `op` (`add`, `sub` or `mul`), calling the core `core` (a
designator) with the signs and magnitudes of `a` and `b` (`b` negated for `sub`), `R`'s
signedness `rs` and maximum `rmax`; `w` is a local `unsigned long`.

```c
UL w = 0;
int o = core(mul, a < 0, a < 0 ? 0 - (UL)a : (UL)a, (b < 0) != sub, b < 0 ? 0 - (UL)b : (UL)b,
             rs, rmax, &w);
*r = (R)w;
return (_Bool)o;
```
-/
def overflow (op : String) (core : TypedExpression) (at_ bt rt : Ctype) (rq : Qualifiers)
    (rs : Bool) (rmax : Nat) (a b r w o : Sym) : TypedStatement :=
  let neg := fun (t : Ctype) (s : Sym) => test .lt (get t s) (int 0)
  let mag := fun (t : Ctype) (s : Sym) =>
    cond ulT (neg t s) (arith ulT .sub (ul 0) (cast ulT (get t s))) (cast ulT (get t s))
  let sbit := if op == "sub" then test .eq (neg bt b) (int 0) else neg bt b
  let args := [int (if op == "mul" then 1 else 0), neg at_ a, mag at_ a, sbit, mag bt b,
    int (if rs then 1 else 0), ul rmax, rv (ptrT ulT) (.unary .address (lv ulT (.ident w)))]
  let rp : Ctype := ty (.pointer rq rt)
  let target : TypedExpression := .mk (.lvalue rq rt false) [] .unknown
    (.unary .indirection (get rp r))
  block [(w, ulT, ul 0), (o, intT, rv intT (.call core args))]
    [stmt (.expr (rv rt (.assign target (cast rt (get ulT w))))), ret (cast boolT (get intT o))]

end Silmaril.Clang.Builtin
