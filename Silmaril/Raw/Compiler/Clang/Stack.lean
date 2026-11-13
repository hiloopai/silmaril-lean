module

public import Silmaril.Compiler.Clang.Builtin.Defs

/-! # Dynamic stack storage in a static arena

Typed Ail has no variable-length array type (an array's size is a constant) and no
`alloca`, so the Clang frontend gives both a stack of its own: a file-scope
arena `static double __cfront_stack[arenaWords]` and its top `static unsigned long
__cfront_top`, the number of bytes in use. A synthesized `char *push(unsigned long n)` returns
the next 16-byte aligned block of `n` bytes below those in use and raises the top past it: the
arena grows down from its end, as the machine stack does, so later blocks have lower addresses
(tinycc's `vla_test` compares them).

* A function that uses the arena saves the top at entry (`base`) and restores it on every
  return and at the end of its body.
* A variable-length array `T a[e]` becomes a pointer `T *a`, its length `len = e` (evaluated
  once, at the declaration, as C requires) and its end mark `end` (the top after its block):
  `__cfront_top = mark; len = e; a = (T *)push(len * sizeof(T)); end = __cfront_top;`.
  `mark` is the end mark of the nearest variable-length array in scope, or `base`. C forbids
  a jump into the scope of a variable-length array, so every array in scope at a declaration
  has been allocated last by its own declaration, and the arrays above `mark` are out of
  scope: a backward `goto` or a loop reallocates instead of growing the arena.
* `__builtin_alloca(n)` is `(void *)push(n)`: its block lives until the function returns.
  A function may not mix the two (a declaration would release later `alloca` blocks).

The arena is 8 MiB, the default stack limit of Linux, and an overflow stores through a null
pointer: the program stops with a segmentation fault, as it does on a stack overflow, and
never reads storage that it does not own. The addresses of the blocks differ from gcc's, and
the distances between them too: a program that depends on them can differ.
-/

@[expose] public section

namespace Silmaril.Clang.Stack

open Silmaril.Cerberus Ail Builtin

/-- The arena's length in `double`s (8 MiB). -/
def arenaWords : Nat := 1048576

def arenaBytes : Nat := 8 * arenaWords

def arenaType : Ctype := ty (.array dblT (some arenaWords))

def charT : Ctype := ty (.basic (.integer .char))

/-- `x = e;` for an object `x` of type `t`. -/
def assign (t : Ctype) (x : Sym) (e : TypedExpression) : TypedStatement :=
  stmt (.expr (rv t (.assign (lv t (.ident x)) e)))

/-- The body of `char *push(unsigned long n)` over the arena `arena` and its top `top`, with
the locals `r`, `e` and `m`. The arena grows down from its end, as the machine stack does.

```c
unsigned long r = __cfront_top;
char *e = (char *)__cfront_stack + arenaBytes;
unsigned long m = (n + 15) / 16 * 16;
if (m < n || m > arenaBytes - r) *(volatile char *)0 = 0;
r = r + m;
r = r + ((unsigned long)(e - r) & 15);
if (r > arenaBytes) *(volatile char *)0 = 0;
__cfront_top = r;
return e - r;
```
-/
def push (arena top : Sym) (ps ls : List Sym) : Option TypedStatement := do
  let [n] := ps | none
  let [r, e, m] := ls | none
  let u := get ulT
  let cp := ptrT charT
  let base := rv (ptrT dblT) (.arrayDecay (lv arenaType (.ident arena)))
  let below := rv cp (.binary (get cp e) (.arithmetic .sub) (u r))
  let vcp : Ctype := ty (.pointer ⟨false, false, true⟩ charT)
  let null : TypedExpression := .mk (.lvalue ⟨false, false, true⟩ charT false) [] .unknown
    (.unary .indirection (cast vcp (int 0)))
  let crash := fun c => stmt (.if_ c (stmt (.expr (rv charT (.assign null (cast charT (int 0))))))
    (stmt .skip))
  return block
    [(r, ulT, get ulT top),
     (e, cp, rv cp (.binary (cast cp base) (.arithmetic .add) (ul arenaBytes))),
     (m, ulT, arith ulT .mul (arith ulT .div (arith ulT .add (u n) (ul 15)) (ul 16)) (ul 16))]
    [crash (test .or (test .lt (u m) (u n)) (test .gt (u m) (arith ulT .sub (ul arenaBytes) (u r)))),
     assign ulT r (arith ulT .add (u r) (u m)),
     assign ulT r (arith ulT .add (u r) (arith ulT .band (cast ulT below) (ul 15))),
     crash (test .gt (u r) (ul arenaBytes)),
     assign ulT top (u r),
     ret below]

end Silmaril.Clang.Stack
