module

public import Silmaril.Compiler.Clang.Bitfield.Defs
public import Silmaril.Cerberus.Ail.Syntax.Defs

/-! # GNU vector types lowered to lane structs

Typed Ail has no vector types, so the Clang frontend desugars GCC's generic vectors
(`__attribute__((vector_size(S)))`) itself, as it does bit-fields (`Bitfield`):

* **Type.** A vector of `N` lanes of `T` (`T` an integer type other than `_Bool`, `float` or
  `double`) is a struct of `N` members `l0 … l(N-1)` of type `T`, one struct per lane type and
  lane count (`__cfront_vector<k>`). The members of one type leave no padding, so the struct has
  gcc's size wherever ccomp's `T` has gcc's size; its first member carries the vector's alignment
  (`_Alignas(N * sizeof(T))`, gcc's, or ccomp's alignment of `T` if that is stronger: a `float`
  is 8 bytes in ccomp). A vector is copied, assigned, passed and returned as that
  struct.
* **Operators** become calls of synthesized static functions, one per operator and vector type,
  so every operand is evaluated once, as the operator evaluates it: the lane-wise
  `+ - * / % & | ^ << >>` (`binary`), `-` and `~` (`unary`), the comparisons, whose lanes are
  `-1` or `0` in the signed integer vector Clang gives as their type (`compare`), a compound
  assignment through a pointer to its left operand (`assignOp`), the broadcast of a scalar
  (`splat`, Clang's `VectorSplat`), and a reinterpretation of the bytes of one type as another of
  the same size (`bitcast`, through a union of the two). A lane's arithmetic is C's on that lane
  (its integer promotions, then the conversion back to the lane type), which is gcc's
  lane-wise arithmetic.
* **Lanes.** `v[k]` for a constant `k` is the member `lk` (an lvalue of an lvalue vector).

Everything else on a vector (a variable subscript, `!`, `&&`, `||`, `++`, `--`, `?:` with a vector
condition, shuffles, `ext_vector_type` swizzles, a bit cast of `float` lanes, whose size in ccomp
is not gcc's) is rejected by the translation. There is no Cerberus differential for these
programs: they are judged against gcc only.
-/

@[expose] public section

namespace Silmaril.Clang.Vector

open Silmaril.Cerberus Ail

def noQ : Qualifiers := ⟨false, false, false⟩

/-- The name of lane `i`. -/
def lane (i : Nat) : Identifier := .mk .unknown s!"l{i}"

/-- The lane type of a vector, and gcc's size of it, if vectors of it are supported. -/
def laneSize : Ctype → Except String Nat
  | .mk _ (.basic (.integer .bool)) => throw "a vector of _Bool"
  | .mk _ (.basic (.integer (.enum _))) => throw "a vector of an enumerated type"
  | .mk _ (.basic (.integer it)) => Bitfield.intSize it
  | .mk _ (.basic (.floating (.realFloating .float))) => return 4
  | .mk _ (.basic (.floating (.realFloating .double))) => return 8
  | _ => throw "a vector of an unsupported lane type"

/-- The members of the lane struct of `n` lanes of `t`, aligned to `align`. -/
def members (t : Ctype) (n align : Nat) :
    List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) :=
  (List.range n).map fun i =>
    (lane i, (.mk [], if i == 0 then some (.integer align) else none, noQ, t))

/-- The type of an rvalue of a lane, struct or pointer type. -/
def gen : Ctype → GenType
  | .mk _ (.basic (.integer it)) => .basic (.integer (.concrete it))
  | .mk _ (.basic (.floating ft)) => .basic (.floating ft)
  | .mk _ (.struct s) => .struct s
  | .mk _ (.union s) => .union s
  | .mk _ (.pointer q t) => .pointer q t
  | _ => .void

/-- A lane type after the integer promotions (STD §6.3.1.1#2): `int` below `int`'s rank. -/
def promoted (t : Ctype) : Ctype :=
  match t with
  | .mk _ (.basic (.integer it)) =>
    match Bitfield.intSize it with
    | .ok w => if w < 4 then .mk [] (.basic (.integer (.signed .int))) else t
    | .error _ => t
  | t => t

def lv (t : Ctype) (n : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk (.lvalue noQ t false) [] .unknown n

def rv (t : Ctype) (n : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk (.rvalue (gen t)) [] .unknown n

def load (t : Ctype) (e : TypedExpression) : TypedExpression := rv t (.rvalue e)

def stmt (n : StatementNode GenTypeCategory) : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) n

/-- The struct type of a tag. -/
def structTy (s : Sym) : Ctype := .mk [] (.struct s)

/-- Lane `i` of a vector lvalue `v`. -/
def laneOf (t : Ctype) (v : TypedExpression) (i : Nat) : TypedExpression := lv t (.memberof v (lane i))

/-- `{ V r; r.l0 = f 0; …; return r; }`: the body of a function computing a vector lane-wise
into its local `r`. -/
def lanewise (v : Sym) (t : Ctype) (n : Nat) (r : Sym) (f : Nat → TypedExpression) :
    TypedStatement :=
  let vt := structTy v
  let res := lv vt (.ident r)
  let assigns := (List.range n).map fun i =>
    stmt (.expr (rv t (.assign (laneOf t res i) (f i))))
  stmt (.block [(r, ((.unknown, .automatic, false), none, noQ, vt))]
    ([stmt (.declaration [(r, none)])] ++ assigns ++ [stmt (.return_ (load vt res))]))

/-- `a op b` lane-wise (parameters `a`, `b`; local `r`). -/
def binary (v : Sym) (t : Ctype) (n : Nat) (op : ArithmeticOperator) (a b r : Sym) : TypedStatement :=
  let vt := structTy v
  lanewise v t n r fun i =>
    rv (promoted t) (.binary (load t (laneOf t (lv vt (.ident a)) i)) (.arithmetic op)
      (load t (laneOf t (lv vt (.ident b)) i)))

/-- `op a` lane-wise, for `-` and `~`. -/
def unary (v : Sym) (t : Ctype) (n : Nat) (op : UnaryOperator) (a r : Sym) : TypedStatement :=
  lanewise v t n r fun i => rv (promoted t) (.unary op (load t (laneOf t (lv (structTy v) (.ident a)) i)))

/-- A comparison of `a` and `b` (lanes `t`) into the mask vector `m` (lanes `mt`):
`r.li = -(a.li op b.li)`, `-1` where it holds. -/
def compare (v : Sym) (t : Ctype) (n : Nat) (m : Sym) (mt : Ctype) (op : BinaryOperator) (a b r : Sym) :
    TypedStatement :=
  let vt := structTy v
  let int_ : Ctype := .mk [] (.basic (.integer (.signed .int)))
  lanewise m mt n r fun i =>
    rv int_ (.unary .minus (rv int_ (.binary (load t (laneOf t (lv vt (.ident a)) i)) op
      (load t (laneOf t (lv vt (.ident b)) i)))))

/-- The scalar `x` (of the lane type) in every lane. -/
def splat (v : Sym) (t : Ctype) (n : Nat) (x r : Sym) : TypedStatement :=
  lanewise v t n r fun _ => load t (lv t (.ident x))

/-- `*p op= b`, lane-wise, and its value: `p->li = p->li op b.li; …; return *p;`. -/
def assignOp (v : Sym) (t : Ctype) (n : Nat) (op : ArithmeticOperator) (p b : Sym) : TypedStatement :=
  let vt := structTy v
  let pt : Ctype := .mk [] (.pointer noQ vt)
  let target := fun i => lv t (.memberofptr (load pt (lv pt (.ident p))) (lane i))
  let assigns := (List.range n).map fun i =>
    stmt (.expr (rv t (.assign (target i)
      (rv (promoted t) (.binary (load t (target i)) (.arithmetic op)
        (load t (laneOf t (lv vt (.ident b)) i)))))))
  stmt (.block [] (assigns ++
    [stmt (.return_ (load vt (lv vt (.unary .indirection (load pt (lv pt (.ident p)))))))]))

/-- The members of the union through which `bitcast` reinterprets `from` as `to`. -/
def punMembers (src dst : Ctype) :
    List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) :=
  [(.mk .unknown "from", (.mk [], none, noQ, src)), (.mk .unknown "to", (.mk [], none, noQ, dst))]

/-- `{ union U u; u.from = a; return u.to; }`. -/
def bitcast (u : Sym) (src dst : Ctype) (a l : Sym) : TypedStatement :=
  let ut : Ctype := .mk [] (.union u)
  let un := lv ut (.ident l)
  stmt (.block [(l, ((.unknown, .automatic, false), none, noQ, ut))]
    [stmt (.declaration [(l, none)]),
     stmt (.expr (rv src (.assign (lv src (.memberof un (.mk .unknown "from")))
       (load src (lv src (.ident a)))))),
     stmt (.return_ (load dst (lv dst (.memberof un (.mk .unknown "to")))))])

end Silmaril.Clang.Vector
