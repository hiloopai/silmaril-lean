module

public import Silmaril.Compiler.C.Sem.C7Interp.Defs
@[expose] public section

/-!
# C7: stdio streams, floating `printf` conversions and `va_list` arguments of the printf family

C7 extends C6 with the parts of `<stdio.h>` that write to the standard streams, format
floating values, and take a variable argument list as a `va_list`.
Everything else is C6's. Cerberus's runtime headers declare the library: `FILE` is
`struct _IO_FILE`, an incomplete type, so no program reads or writes a `FILE` object, and
`va_list` is `int` (C4's cursor handle).

## Floating conversions (STD §7.21.6.1)

`printf`, `fprintf`, `sprintf`, `snprintf` and their `v` forms take arguments of type `double`
(a `float` argument is promoted to `double`, STD §6.5.2.2#7) for the conversions
`%f %F %e %E %g %G`, with the flags `- + space # 0`, a width and a precision (each possibly
`*`), and the length modifier `l` (which has no effect). For a binary64 value `v` and precision
`P` (6 when absent):

* **Rounding.** A finite `v` is converted from its exact binary value, rounded to the digits
  the conversion prints, to nearest with ties to even (glibc in the default rounding mode,
  which C7 never changes; STD §7.21.6.1#13 asks for correct rounding).
* **`%f`, `%F`**: `[-]ddd.ddd`, with at least one digit before the decimal point and `P`
  digits after it; with `P = 0` the point is omitted unless the `#` flag is given.
* **`%e`, `%E`**: `[-]d.ddde±dd`, with one digit before the point (nonzero unless `v = 0`), `P`
  digits after it (the point omitted when `P = 0` without `#`), and an exponent of at least two
  digits; `E` for `%E`.
* **`%g`, `%G`**: let `P' = P` (1 when `P = 0`) and `X` the exponent `%e` would print at
  precision `P' - 1`. If `P' > X ≥ -4`, the conversion is `%f` at precision `P' - 1 - X`,
  otherwise `%e` (`%E` for `%G`) at precision `P' - 1`. Without `#`, trailing zeros of the
  fraction are then removed, and the decimal point when no fraction remains.
* **Sign.** `-` when the sign bit of `v` is set, so also for `-0.0` and for negative values
  that round to zero; otherwise `+` with the `+` flag and a space with the space flag.
* **Infinities and NaNs**: `inf`, `nan` (`INF`, `NAN` for `%F %E %G`), with `-` when the sign
  bit is set (glibc's `-nan`); the precision and `#` are ignored, and the `0` flag pads with
  spaces (STD §7.21.6.1#6).
* **Width.** The result is padded to the width with spaces on the left, on the right with the
  `-` flag, or with zeros after the sign with the `0` flag (ignored with `-`).

A floating conversion whose argument is not a `double`, or a `d i o u x X c s` conversion whose
argument is a `double`, is undefined (STD §7.21.6.1#9). `%a`, `%A`, the modifier `L`
(`long double`) and the conversions C1 leaves out stay outside C7 (`unsupported` at the call).
The other conversions are C1's, with C1's treatment of their integer arguments.

**Reference discrepancy (coordinator-approved).** glibc 2.39 drops fractional zeros for
some `%#g` exponent carries: `%#.2g` of 99.5 and its next larger binary64 value print
`1.e+02`, whereas C11 and C7 retain `1.0e+02`; `%#g`/`%#.6g` of the binary64 predecessor
of 1e6 similarly prints `1.e+06` instead of `1.00000e+06`. Both signs and uppercase `G`
are affected (16 cases in the boundary matrix). C7 retains the stated C11 rule.

## Streams

A stream is designated by a *handle*: a distinct nonzero pointer value that addresses no
object and no function.

`stdout` and `stderr` (Cerberus's `__stdout` and `__stderr`) are const objects of static
storage duration holding the standard output and error handles. `stdin` (`__stdin`) is
outside C7 (`check`). No file system or other streams are provided.

**Observation.** A behaviour (`Basic.Obs`) is the exit and the standard output. Every byte
written to the standard output, by `putchar`, `puts`, `printf`, `vprintf` or a stream function
on `stdout`, is appended to it in program order. Bytes written to `stderr` are not observed;
the functions that write them return what they return for `stdout`. Streams are unbuffered:
`fflush(f)` and `fflush(NULL)` return 0 and do nothing else, and `abort` keeps the output
written so far, as in C1.

Output functions are `fprintf`, `vfprintf` (formatted bytes, returning their count),
`fputs(s, f)` (bytes before NUL; returns 1, glibc's nonnegative choice), `fputc(c, f)` and
`putc(c, f)` (the unsigned character byte, returning it), and `fwrite(p, size, n, f)`
(`size * n` bytes, returning `n`; zero size or count returns zero without reading `p`).
`ferror` returns zero and `clearerr` does nothing: this rung models successful standard
output/error writes. File opening, closing and input (`fopen`, `fclose`, `fread`, `fgets`,
`fgetc`, `getc`, `feof`) are outside `check`.

Passing a value that is not the handle of a standard stream (`NULL` or any other pointer) where a
stream is expected is undefined (STD §7.1.4#1). Memory accesses by these
functions (`fwrite`, `fputs` and the `%s` arguments) are checked as C5's
external functions check them.

## `va_list` arguments

`vprintf(fmt, ap)`, `vfprintf(f, fmt, ap)`, `vsprintf(s, fmt, ap)` and `vsnprintf(s, n, fmt,
ap)` take a live C4 cursor `ap` and behave as `printf`, `fprintf`, `sprintf` and `snprintf`
called with the arguments that remain on the cursor, in order, with their (promoted) types.
Afterwards the cursor's value is indeterminate (STD §7.21.6.8#2, footnote 288): `va_end` is the
only further use that is defined, as on a cursor C4 has invalidated. A cursor that is not live
is undefined, as in C4.

## Function designators

The addresses of the functions above are C4's code tokens, and an indirect call of one behaves
as the direct call.

Outside C7 still: `stdin` and every input from it (`getchar`, `scanf`, …), the update modes,
positioning (`fseek`, `ftell`, `rewind`, `fgetpos`, `fsetpos`), `ungetc`, `freopen`,
`setbuf`/`setvbuf`, `remove`, `rename`, `tmpfile`, the `scanf` family, `long double`, and the
floating arguments of external functions other than the printf family and C3's `<math.h>`.

The fragment is `check` below: C6's check with the externals above added, floating arguments
allowed in calls of `printf`, `fprintf`, `sprintf` and `snprintf`, and `stdin` rejected. Conversions and stream handles are checked when the call runs.
Width or precision above 100,000 is outside C7 as a resource bound.

## Statement: C7 extends C6 on C6's fragment

The ladder law `C6.sem ⊑[C6.fragment] C7.sem` holds with equality of behaviours, by
construction: `run` delegates to C6 when `C6.check` succeeds (target `c7_extends_c6`,
`TargetsC7Ladder.lean`). So on C6's fragment C7 also inherits C6's answers where they differ
from the hosted library: C1 to C6 treat an external object without a definition as zero, so a
C6 program that reads `stdout` or `stderr` without calling a stream function sees `NULL`.

The extended evaluator lives in `C7Interp.lean`, with exact decimal formatting in
`C7Format.lean` and the stream/cursor library in `C7Library.lean`. `checkC7`
(`ValidatorC7.lean`, target `ccomp_rt_tv_sound_c7`) remains a validator stub.
-/

namespace Silmaril.Compile.C.Sem.C7

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C Silmaril.Compile.Category
open C0 (Result)
open C1 (FunDef externals plainString)
open C2 (aggOf)
open C4 (Prog prepare isFunction checkFloat checkC callTypes)
open C5 (heapExternals checkCallShape)
open C6 (checkLocals bindingTypes seGuard reachable callsE)

/-! ## The library -/

/-- The external functions of the printf family whose floating arguments C7 formats. -/
def floatFormatters : List String := ["printf", "fprintf", "sprintf", "snprintf"]

/-- The external functions C7 adds to C6's, by name. -/
def streamExternals : List String :=
  ["fprintf", "vprintf", "vfprintf", "vsprintf", "vsnprintf", "fputs", "fputc", "putc",
   "fwrite", "fflush", "ferror", "clearerr"]

/-- Is `name` an external function of C7 (C6's or a stream function)? -/
def isExternal (name : String) : Bool :=
  externals.contains name || heapExternals.contains name || (C3.F.libm name).isSome ||
    streamExternals.contains name

/-- The standard input stream (Cerberus's name), outside C7. -/
def stdinName : String := "__stdin"

/-! ## The interpreter -/

/-- The C7 interpreter delegates to C6 on its fragment, preserving every fuel-indexed result. -/
def run (fuel : Nat) (p : TypedProgram) : Result :=
  if C6.check p = .ok () then C6.run fuel p else runExtended fuel p

/-- The preservation law is by construction, including UB and divergence. -/
theorem run_eq_c6 {p : TypedProgram} (h : C6.InFragment p) (fuel : Nat) :
    run fuel p = C6.run fuel p := by
  simp only [run, C6.InFragment] at *
  rw [ite_eq_left h]

/-! ## Behaviours and the language -/

/-- The behaviours of a program under C7, as for C0 (`C0.beh`). -/
def beh (p : TypedProgram) : Set Obs := {o |
  (∃ n, run n p = .done o) ∨ (∃ n why, run n p = .undefined why) ∨
    (o = ⟨[], .diverges⟩ ∧ ∀ n, run n p = .outOfFuel)}

/-- C7 as a semantics of C. -/
def sem : Semantics := beh

/-- C7 as a language of the zoo. -/
def lang : Language.{0} := cSyntax.lang sem

/-! ## The fragment -/

/-- Check the shape of a call: a direct call of a stream function or of a function of the
printf family (floating arguments allowed there), and C6's rules otherwise. -/
def checkCall (P : Prog) (f : TypedExpression) (args : List TypedExpression) :
    Except String Unit := do
  match f.node with
  | .functionDecay ⟨_, _, _, .ident g⟩ =>
    let name := P.name g
    if !P.funcs.contains g.number &&
        (streamExternals.contains name || floatFormatters.contains name) then
      match callTypes f with
      | .error _ => throw "call of a non-function"
      | .ok _ => pure ()
      if args.any (fun a => (aggOf (typeOf a)).isSome) then
        throw s!"an aggregate argument of the external function {name}"
      if !floatFormatters.contains name && args.any (fun a => (typeOf a).isFloat) then
        throw s!"a floating argument of the external function {name}"
    else checkCallShape P f args
  | _ => checkCallShape P f args

mutual
/-- Check a function designator, including the targets whose addresses escape. -/
def checkF (P : Prog) (c : C6.Ctx) : TypedExpression → Except String Unit
  | .mk _ _ _ node => do
  match node with
  | .ident g =>
    if !P.symbols.contains g.number then throw "an undeclared function designator"
    if !P.funcs.contains g.number && !isExternal (P.name g) then
      throw s!"address of the external function {P.name g}"
  | .unary .indirection p => checkE P c p
  | .annot _ a => checkF P c a
  | _ => throw "a function designator outside C7"

/-- Check that an rvalue is in the fragment. -/
def checkE (P : Prog) (c : C6.Ctx) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue .. => throw "an lvalue in value position"
    | .rvalue g =>
      let t := ofGenType g
      if P.aggType t then checkA P c node
      else
        if !P.valueType t then throw "an expression of a type outside C7"
        checkN P c node
/-- Check an expression of a struct or union type. -/
def checkA (P : Prog) (c : C6.Ctx) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a => checkLv P c a
  | .vaArg ap _ => checkE P c ap
  | .assign l r => do checkLv P c l; checkE P c r
  | .call f args => do checkCall P f args; checkE P c f; checkL P c args
  | .cond c' (some a) b => do checkE P c c'; checkE P c a; checkE P c b
  | .binary a .comma b => do checkE P c a; checkE P c b
  | .annot _ a => checkE P c a
  | .memberof a _ =>
    match a with
    | .mk (.lvalue ..) _ _ _ => checkLv P c a
    | .mk (.rvalue _) _ _ _ => checkE P c a
  | .gccStatement bs ss => do seGuard P c bs ss true; checkSL P (c.enterSE bs) ss
  | _ => throw "an aggregate expression outside C7"
def checkN (P : Prog) (c : C6.Ctx) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a | .arrayDecay a => checkLv P c a
  | .functionDecay a => checkF P c a
  | .vaStart _ _ => pure ()
  | .vaArg a _ | .vaEnd a => checkE P c a
  | .vaCopy _ b => checkE P c b
  | .const k =>
    match k with
    | .integer _ | .character _ | .predefined _ | .null => pure ()
    | .floating fc => checkFloat fc
    | _ => throw "a constant outside C7"
  | .annot _ a | .cast _ _ a | .assert a => checkE P c a
  | .unary op a =>
    match op with
    | .plus | .minus | .bnot => checkE P c a
    | .address => if isFunction a then checkF P c a else checkLv P c a
    | .postfixIncr | .postfixDecr => checkLv P c a
    | .indirection => throw "an indirection outside an lvalue"
  | .binary a _ b => do checkE P c a; checkE P c b
  | .assign l r | .compoundAssign l _ r => do checkLv P c l; checkE P c r
  | .cond c' a b => do
    checkE P c c'
    match a with
    | some a => checkE P c a
    | none => pure ()
    checkE P c b
  | .call f args => do checkCall P f args; checkE P c f; checkL P c args
  | .sizeof _ ty | .alignof _ ty => P.sized ty
  | .offsetof ty m => do let _ ← P.memberS ty m
  | .sizeofExpr _ => pure ()
  | .generic _ (some _) assocs => checkG P c assocs
  | .memberof a _ =>
    match a with
    | .mk (.lvalue ..) _ _ _ => checkLv P c a
    | .mk (.rvalue _) _ _ _ => checkE P c a
  | .gccStatement bs ss => do seGuard P c bs ss false; checkSL P (c.enterSE bs) ss
  | _ => throw "an expression outside the fragment"
/-- Check that an lvalue is in the fragment. -/
def checkLv (P : Prog) (c : C6.Ctx) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue _ ty _ => if !P.obj ty then throw "an object of a type outside C7"
    | .rvalue _ => throw "an rvalue in lvalue position"
    match node with
    | .ident x => if P.name x == stdinName then throw "the stream stdin"
    | .unary .indirection p => checkE P c p
    | .memberof a _ => checkLv P c a
    | .memberofptr p _ => do
      checkE P c p
      match typeOf p with
      | .ptr sty => if !P.obj sty then throw "a member of an incomplete struct or union"
      | _ => throw "a member through a non-pointer"
    | .str s => if !plainString s then throw "a wide string literal"
    | .annot _ a => checkLv P c a
    | .compound _ ty init => do
      if c.fileScope then throw "a compound literal at file scope"
      checkI P c ty init
    | _ => throw "an lvalue outside C7"
def checkL (P : Prog) (c : C6.Ctx) : List TypedExpression → Except String Unit
  | [] => pure ()
  | e :: es => do checkE P c e; checkL P c es
def checkG (P : Prog) (c : C6.Ctx) : List (GenericAssociation GenTypeCategory) →
    Except String Unit
  | [] => pure ()
  | .type_ _ _ e :: gs | .default e :: gs => do checkE P c e; checkG P c gs

/-- Check an initializer of an object of type `ty` (C6's `checkI`). -/
def checkI (P : Prog) (c : C6.Ctx) : Ctype → TypedExpression → Except String Unit
  | ty, .mk ann _ _ node =>
    match ty, node with
    | .mk _ (.array et _), .array _ _ elems => checkIO P c et elems
    | .mk _ (.array _ _), .str s => if plainString s then pure () else throw "a wide string literal"
    | .mk _ (.array _ _), .const k => checkC k
    | .mk _ (.array _ _), _ => throw "an array initializer outside C7"
    | .mk _ (.struct _), .struct _ ms | .mk _ (.union _), .struct _ ms => checkIM P c ty ms
    | .mk _ (.struct _), .union _ m (some x) | .mk _ (.union _), .union _ m (some x) => do
      checkI P c (← P.memberS ty m).2 x
    | .mk _ (.struct _), .union _ _ none | .mk _ (.union _), .union _ _ none => pure ()
    | .mk _ (.struct _), .const k | .mk _ (.union _), .const k => checkC k
    | _, nd => do
      let agg := match ty with
        | .mk _ (.struct _) | .mk _ (.union _) => true
        | _ => false
      if !agg && !P.valueType (ofCtype ty) then
        throw "an initializer of an object without values in C7"
      match ann with
      | .lvalue .. => throw "an lvalue in value position"
      | .rvalue g =>
        let t := ofGenType g
        if P.aggType t then checkA P c nd
        else
          if !P.valueType t then throw "an expression of a type outside C7"
          checkN P c nd
def checkIO (P : Prog) (c : C6.Ctx) (et : Ctype) :
    List (Option TypedExpression) → Except String Unit
  | [] => pure ()
  | some x :: xs => do checkI P c et x; checkIO P c et xs
  | none :: xs => checkIO P c et xs
def checkIM (P : Prog) (c : C6.Ctx) (ty : Ctype) :
    List (Identifier × Option TypedExpression) → Except String Unit
  | [] => pure ()
  | (m, some x) :: ms => do checkI P c (← P.memberS ty m).2 x; checkIM P c ty ms
  | (_, none) :: ms => checkIM P c ty ms

def checkS (P : Prog) (c : C6.Ctx) : TypedStatement → Except String Unit
  | .mk _ _ _ node => checkSN P c node
def checkSN (P : Prog) (c : C6.Ctx) : StatementNode GenTypeCategory → Except String Unit
  | .skip | .break_ | .continue_ | .returnVoid | .goto _ => pure ()
  | .expr e | .return_ e => checkE P c e
  | .block bs ss => do
    checkLocals P bs
    checkSL P (if c.inSE then { c with seLocals := bindingTypes bs ++ c.seLocals } else c) ss
  | .if_ e a b => do checkE P c e; checkS P c a; checkS P c b
  | .while_ e b _ | .do_ b e _ => do checkE P c e; checkS P c b
  | .switch e b => do checkE P c e; checkS P c b
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => checkS P c b
  | .declaration ds => checkD P c ds
  | _ => throw "a statement outside the fragment"
def checkSL (P : Prog) (c : C6.Ctx) : List TypedStatement → Except String Unit
  | [] => pure ()
  | s :: ss => do checkS P c s; checkSL P c ss
def checkD (P : Prog) (c : C6.Ctx) : List (Sym × Option TypedExpression) → Except String Unit
  | [] => pure ()
  | (x, some e) :: ds => do
    match c.fd.memLocals.find? (·.1 == x.number) with
    | some (_, ty) => checkI P c ty e
    | none =>
      match c.seLocals.find? (·.1 == x.number) with
      | some (_, ty) => checkI P c ty e
      | none => checkE P c e
    checkD P c ds
  | (_, none) :: ds => checkD P c ds
end

/-- Is the program in the C7 fragment? The reason when it is not. As in C6, only the
functions reachable from `main` are checked, and the initializers of the objects of static
storage duration whose type is in C7. -/
def check (p : TypedProgram) : Except String Unit := do
  let P := prepare p
  let some m := P.main | throw "no main"
  let some _ := P.funcs[m]? | throw "main is not defined"
  let live := reachable P
    (m :: (P.statics.flatMap fun (_, _, i) => (i.map callsE).getD []))
  for (x, (_, _, d)) in p.2.declarations do
    match d with
    | .function _ (_, ret) ps _ _ _ =>
      if live.contains x.number then
        let r := ofCtype ret
        if !P.valueType r && !P.aggType r then
          throw s!"a function with a result outside C7: {Silmaril.Compile.Forks.Csem.C.symName x}"
        if ps.any fun (_, t, _) =>
            !P.obj t || !((C3.width (ofCtype t)).isSome || P.aggType (ofCtype t)) then
          throw s!"a function with a parameter outside C7: {Silmaril.Compile.Forks.Csem.C.symName x}"
    | .object .. => pure ()
  for (_, ty, init) in P.statics do
    if P.obj ty then
      if let some e := init then checkI P { fd := C1.topFrame, fileScope := true } ty e
  for f in live do
    if let some fd := P.funcs[f]? then checkS P { fd } fd.body

/-- The C7 fragment. -/
def InFragment (p : TypedProgram) : Prop := check p = .ok ()

instance (p : TypedProgram) : Decidable (InFragment p) :=
  inferInstanceAs (Decidable (check p = .ok ()))

/-- The fragment as a set of programs. -/
def fragment : Set TypedProgram := {p | InFragment p}

/-! ## Statement-stage checks -/

/-- The stream functions are new: none is an external of C6. -/
example : streamExternals.all (fun n => !externals.contains n && !heapExternals.contains n) :=
  by decide

/-- The printf family is external in C7. -/
example : floatFormatters.all isExternal := by decide

/-- Input from `stdin`, positioning, `ungetc`, `freopen` and `<ctype.h>` stay outside. -/
example : !isExternal "fopen" && !isExternal "fclose" && !isExternal "fread" &&
    !isExternal "fgets" && !isExternal "fscanf" && !isExternal "getchar" && !isExternal "fseek" &&
    !isExternal "ungetc" && !isExternal "freopen" && !isExternal "isprint" := by decide

end Silmaril.Compile.C.Sem.C7
