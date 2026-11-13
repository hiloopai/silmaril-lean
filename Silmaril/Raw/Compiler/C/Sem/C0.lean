module

public import Silmaril.Compiler.C.Sem.Basic.Defs
public import Silmaril.Compiler.Forks.Csem.C.ToMir.Defs
@[expose] public section

/-!
# C0: integers and structured control flow, on typed Ail

The first rung of the C semantics ladder. C0 is an executable,
deterministic interpreter of typed Ail (`Ail.TypedProgram`) for the **C0 fragment**
(`C0.InFragment`, decided by `C0.check`):

* integer types and conversions only (`_Bool`, `char`, `short`, `int`, `long`, `long long`,
  signed and unsigned, enumerations as `int`), with Cerberus's LP64 layout and signed plain
  `char` (`Silmaril.Compile.C.intLayout`); no pointers, arrays, structs, unions or floats;
* objects: automatic locals and parameters that are never address-taken (no `&` anywhere),
  and, as an extension of the ladder's C0, scalar integer globals and `static` locals (also never
  address-taken: they need no memory either);
* all structured control flow: `if`, `while`, `do`, `for` (desugared), `break`, `continue`,
  `switch` (with fall-through, `default`, GNU case ranges), labels and `goto`, `return`;
* direct calls of functions defined in the program (recursion included), and three
  memory-free externals: `abort()` (signal 6), `exit(n)`/`_Exit(n)`, and `putchar(c)` (one
  byte of output; an extension so that C0 programs can print).

## Choices: C0 is more defined and more deterministic than C

These choices make C0 a refinement of the full semantics (`S(p) ⊆ ⟦p⟧`), never a
contradiction of it:

* evaluation order is left to right (operands, arguments), except that a compound assignment
  evaluates its right operand first (as ccomp does); C leaves these unspecified, so any fixed
  order is one of the allowed behaviours;
* conversions to a signed type reduce modulo `2ᴺ` (implementation-defined; Cerberus's and
  gcc's choice), `>>` of a negative value is arithmetic (implementation-defined);
* undefined behaviour is detected and reported (`Result.undefined`): signed overflow of
  `+ - * / % <<` and unary `-`, division by zero, shift counts out of range, left shifts of
  negative values, reads of uninitialised locals. Its behaviour set is everything
  (`beh_of_undefined`): UB permits every behaviour, so this is the weakest possible claim;
* a non-`void` function that ends without `return` returns `0`; using that value is UB in C,
  so any value refines it (and `main` returns `0` by C99 §5.1.2.2.3).

## Statement: C0 refines Cerberus on the fragment

Let `⟦·⟧ : C.Semantics` be the full single-threaded C semantics (the
`Ail → Core` elaboration followed by the complete Core dynamics with PNVI-ae-udi memory,
behaviours of the startup run of `main`, undefined behaviour closed to `Set.univ`). The
intended theorem for this rung is

  `C0.beh ⊑[C0.InFragment] ⟦·⟧`, i.e. `∀ p, C0.InFragment p → C0.beh p ⊆ ⟦p⟧`

(`Syntax.RefinesOn`, `Silmaril.Compile.Category.Lattice`). It is tested, not proved: the
`csem` campaign compares `C0.run` with gcc -O0 and Cerberus on the corpus. With it, any
compiler valid for `C0` on the fragment is valid for C there (`Syntax.ValidOn.of_refinesOn`).

## Executable form

`run fuel p` is the interpreter: fuel bounds every recursion (statement steps, expression
depth, call depth), so `run` is a total, structurally recursive function. `beh p` collects the
results over all fuels; `beh_of_done` and `beh_of_undefined` read results back as behaviours.
The intended theorems `run_mono` (more fuel does not change a final result) and
`beh_subsingleton_or_univ` (determinism) are targets of the `csem` campaign.

The constant decoders (`intConstValue`, `charValue`) and the integer type resolution
(`typeOf`, `resolve`, `usual`, `promote`) are shared with ccomp's `ToMir`; a common-mode error
there would not be caught by differential testing against ccomp, only against gcc.
-/

namespace Silmaril.Compile.C.Sem.C0

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C
open Silmaril.Compile.Category

/-! ## Integers -/

/-- Reduce `v` into the integer type of `w` bytes and signedness `s`, modulo `2^(8w)`. -/
def wrap (w : Nat) (s : Bool) (v : Int) : Int :=
  let m : Int := 2 ^ (8 * w)
  let r := v % m
  if s && r ≥ m / 2 then r - m else r

/-- `v` is a value of the integer type `(w, s)`. -/
def inRange (w : Nat) (s : Bool) (v : Int) : Bool :=
  if s then decide (-(2 ^ (8 * w - 1) : Int) ≤ v ∧ v < 2 ^ (8 * w - 1))
  else decide (0 ≤ v ∧ v < 2 ^ (8 * w))

/-- Why a run stops before its end. -/
inductive Stop where
  | exit (code : Int) (out : ByteArray)
  | abort (out : ByteArray)
  | undefined (why : String)
  | outOfFuel
  | unsupported (why : String)

/-- Convert a value to a type (`void`: discard). -/
def convTo : CType → Int → Except Stop Int
  | .bool, v => .ok (if v = 0 then 0 else 1)
  | .int w s, v => .ok (wrap w s v)
  | .void, _ => .ok 0
  | _, _ => .error (.unsupported "a conversion to a non-integer type")

/-- The integer shape of a type of C0. -/
def shape : CType → Except Stop (Nat × Bool)
  | .int w s => .ok (w, s)
  | .bool => .ok (1, false)
  | _ => .error (.unsupported "a non-integer operand")

def ub {α : Type} (why : String) : Except Stop α := .error (.undefined why)

/-- Bitwise operators, on the two's-complement representation. -/
def bitwise (f : Nat → Nat → Nat) (w : Nat) (s : Bool) (a b : Int) : Int :=
  wrap w s (f (wrap w false a).toNat (wrap w false b).toNat)

/-- `a aop b` in the integer type `(w, s)`, on values of that type; for shifts `b` is the
count, a value of its own type. -/
def arith (aop : ArithmeticOperator) (w : Nat) (s : Bool) (a b : Int) : Except Stop Int :=
  let chk (r : Int) : Except Stop Int :=
    if s then (if inRange w s r then .ok r else ub "signed integer overflow")
    else .ok (wrap w false r)
  let count : Except Stop Nat :=
    if 0 ≤ b ∧ b < 8 * w then .ok b.toNat else ub "shift count out of range"
  match aop with
  | .add => chk (a + b)
  | .sub => chk (a - b)
  | .mul => chk (a * b)
  | .div => if b = 0 then ub "division by zero" else chk (a.tdiv b)
  | .mod =>
    if b = 0 then ub "division by zero"
    else do let _ ← chk (a.tdiv b); .ok (a.tmod b)
  | .band => .ok (bitwise (· &&& ·) w s a b)
  | .bor => .ok (bitwise (· ||| ·) w s a b)
  | .bxor => .ok (bitwise (· ^^^ ·) w s a b)
  | .shl => do
    let k ← count
    if s && a < 0 then ub "left shift of a negative value" else chk (a * 2 ^ k)
  | .shr => do
    let k ← count
    .ok (a / 2 ^ k)

/-- The comparison of a relational or equality operator. -/
def compare (op : BinaryOperator) (a b : Int) : Option Bool :=
  match op with
  | .lt => some (decide (a < b))
  | .gt => some (decide (a > b))
  | .le => some (decide (a ≤ b))
  | .ge => some (decide (a ≥ b))
  | .eq => some (decide (a = b))
  | .ne => some (decide (a ≠ b))
  | _ => none

/-! ## Programs -/

/-- A function definition, prepared. -/
structure FunDef where
  /-- Parameter symbols (by number) and types. -/
  params : List (Nat × CType)
  ret : CType
  body : TypedStatement
  /-- The automatic locals of the body (block bindings), by symbol number. -/
  locals : Std.HashMap Nat CType

/-- A prepared program. -/
structure Prog where
  funcs : Std.HashMap Nat FunDef
  /-- Parameter types of every declared function (for argument conversion). -/
  protos : Std.HashMap Nat (List CType)
  /-- The source name of every declared function (externals are found by name). -/
  names : Std.HashMap Nat String
  /-- Objects of static storage duration: symbol number, type, initializer. -/
  globals : List (Nat × CType × Option TypedExpression)
  tags : Mem.Concrete.Tags
  main : Option Nat

mutual
/-- Automatic locals declared in a statement. -/
def localsS : TypedStatement → List (Nat × CType)
  | .mk _ _ _ node => localsN node
/-- Automatic locals declared in a statement node. -/
def localsN : StatementNode GenTypeCategory → List (Nat × CType)
  | .block bs ss =>
    (bs.filterMap fun (x, ((_, dur, _), _, _, ty)) =>
      if dur == .automatic then some (x.number, ofCtype ty) else none) ++ localsL ss
  | .if_ _ a b => localsS a ++ localsS b
  | .while_ _ b _ | .do_ b _ _ | .switch _ b | .case_ _ b | .caseRangeGnu _ _ b | .default b
  | .label _ b _ | .marker _ b => localsS b
  | .par ss => localsL ss
  | _ => []
/-- Automatic locals declared in a list of statements. -/
def localsL : List TypedStatement → List (Nat × CType)
  | [] => []
  | s :: ss => localsS s ++ localsL ss
end

/-- Prepare a typed-Ail program. -/
def prepare (p : TypedProgram) : Prog := Id.run do
  let σ := p.2
  let mut protos : Std.HashMap Nat (List CType) := {}
  let mut rets : Std.HashMap Nat CType := {}
  let mut names : Std.HashMap Nat String := {}
  let mut globals : Array (Nat × CType × Option TypedExpression) := #[]
  let inits : Std.HashMap Nat TypedExpression :=
    σ.objectDefinitions.foldl (fun m (x, e) => m.insert x.number e) {}
  for (x, (_, _, d)) in σ.declarations do
    names := names.insert x.number (Silmaril.Compile.Forks.Csem.C.symName x)
    match d with
    | .function _ (_, ret) ps _ _ _ =>
      protos := protos.insert x.number (ps.map fun (_, t, _) => ofCtype t)
      rets := rets.insert x.number (ofCtype ret)
    | .object (dur, _) _ _ ty =>
      if dur != .automatic then globals := globals.push (x.number, ofCtype ty, inits[x.number]?)
  let mut funcs : Std.HashMap Nat FunDef := {}
  for (x, fd) in σ.functionDefinitions do
    let pts := (protos[x.number]?).getD []
    let params := fd.params.zipIdx.map fun (y, i) => (y.number, (pts[i]?).getD (.int 4 true))
    let locals := (localsS fd.body).foldl (fun m (n, t) => m.insert n t)
      (params.foldl (fun m (n, t) => m.insert n t) {})
    funcs := funcs.insert x.number
      { params, ret := (rets[x.number]?).getD (.int 4 true), body := fd.body, locals }
  return { funcs, protos, names, globals := globals.toList, tags := tagsOf σ,
           main := p.1.map (·.number) }

/-! ## States -/

/-- The store: locals of the current activation, globals, and the output so far. -/
structure Env where
  locals : Std.HashMap Nat Int := {}
  globals : Std.HashMap Nat Int := {}
  out : ByteArray := .empty


/-- Continuations of the statement machine of one activation. -/
inductive Kont where
  | stop
  | seq (rest : List TypedStatement) (k : Kont)
  | while_ (c : TypedExpression) (body : TypedStatement) (k : Kont)
  | do_ (body : TypedStatement) (c : TypedExpression) (k : Kont)
  | switch (k : Kont)

/-- `break`: the continuation after the innermost loop or switch. -/
def Kont.breakTo : Kont → Option Kont
  | .stop => none
  | .seq _ k => k.breakTo
  | .while_ _ _ k | .do_ _ _ k | .switch k => some k

/-- `continue`: the innermost loop continuation, which re-tests its condition. -/
def Kont.continueTo : Kont → Option Kont
  | .stop => none
  | .seq _ k | .switch k => k.continueTo
  | k@(.while_ ..) | k@(.do_ ..) => some k

mutual
/-- The statement labelled `l` inside `s`, and its continuation, for `goto l`. -/
def findLabel (l : Nat) : TypedStatement → Kont → Option (TypedStatement × Kont)
  | .mk _ _ _ node, k => findLabelN l node k
def findLabelN (l : Nat) : StatementNode GenTypeCategory → Kont → Option (TypedStatement × Kont)
  | .block _ ss, k => findLabelL l ss k
  | .if_ _ a b, k => (findLabel l a k).or (findLabel l b k)
  | .while_ c b _, k => findLabel l b (.while_ c b k)
  | .do_ b c _, k => findLabel l b (.do_ b c k)
  | .switch _ b, k => findLabel l b (.switch k)
  | .case_ _ b, k | .caseRangeGnu _ _ b, k | .default b, k | .marker _ b, k => findLabel l b k
  | .label x b _, k => if x.number = l then some (b, k) else findLabel l b k
  | _, _ => none
def findLabelL (l : Nat) : List TypedStatement → Kont → Option (TypedStatement × Kont)
  | [], _ => none
  | s :: ss, k => (findLabel l s (.seq ss k)).or (findLabelL l ss k)
end

/-- Does a `case` label match the switch value `v` of type `(w, s)`? `none` matches
`default`. -/
def caseMatches (w : Nat) (s : Bool) (v : Int) : Option (Int × Int) → Bool
  | some (lo, hi) => decide (wrap w s lo ≤ v ∧ v ≤ wrap w s hi)
  | none => false

mutual
/-- The `case` (or, with `dflt`, the `default`) of the switch body `s` selected by `v`, not
entering nested switches. -/
def findCase (sel : Option (Int × Int) → Bool) : TypedStatement → Kont →
    Option (TypedStatement × Kont)
  | .mk _ _ _ node, k => findCaseN sel node k
def findCaseN (sel : Option (Int × Int) → Bool) : StatementNode GenTypeCategory → Kont →
    Option (TypedStatement × Kont)
  | .block _ ss, k => findCaseL sel ss k
  | .if_ _ a b, k => (findCase sel a k).or (findCase sel b k)
  | .while_ c b _, k => findCase sel b (.while_ c b k)
  | .do_ b c _, k => findCase sel b (.do_ b c k)
  | .case_ v b, k => if sel (some (v, v)) then some (b, k) else findCase sel b k
  | .caseRangeGnu lo hi b, k => if sel (some (lo, hi)) then some (b, k) else findCase sel b k
  | .default b, k => if sel none then some (b, k) else findCase sel b k
  | .label _ b _, k | .marker _ b, k => findCase sel b k
  | _, _ => none
def findCaseL (sel : Option (Int × Int) → Bool) : List TypedStatement → Kont →
    Option (TypedStatement × Kont)
  | [], _ => none
  | s :: ss, k => (findCase sel s (.seq ss k)).or (findCaseL sel ss k)
end

/-- One step of the statement machine: the next configuration, or the function's return. -/
inductive Next where
  | running (focus : Option TypedStatement) (k : Kont)
  | returned (v : Option Int)

/-- The source name of a symbol, through the program's declarations. -/
def Prog.name (P : Prog) (x : Sym) : String := (P.names[x.number]?).getD (Silmaril.Compile.Forks.Csem.C.symName x)

/-- The value of a constant of type `t`. -/
def constVal (c : Constant) (t : CType) : Except Stop Int :=
  match c with
  | .integer ic => convTo t (Silmaril.Compile.Forks.Csem.C.intConstValue ic)
  | .character cc =>
    -- a prefixed (wide) constant of one character is that character's value (ccomp's
    -- `charValue` reduces every character modulo 256, wrong for `L'\400'`)
    let text := match cc.2 with
      | .utf8 t => t.toList
      | .bytes d => d.toList.map fun b => Char.ofNat b.toNat
    match cc.1, Silmaril.Compile.Forks.Csem.C.escapeValue text with
    | some _, some (v, []) => convTo t v
    | _, _ => convTo t (Silmaril.Compile.Forks.Csem.C.charValue cc)
  | .predefined .false_ => .ok 0
  | .predefined .true_ => .ok 1
  | _ => .error (.unsupported "a non-integer constant")

/-- The object an lvalue designates: an identifier. -/
def lvalSym (e : TypedExpression) : Except Stop Sym :=
  match e.node with
  | .ident x => .ok x
  | _ => .error (.unsupported "an lvalue other than an identifier")

/-- Read an object. -/
def readVar (fd : FunDef) (env : Env) (x : Sym) : Except Stop Int :=
  match env.locals[x.number]? with
  | some v => .ok v
  | none =>
    if fd.locals.contains x.number then ub s!"read of the uninitialised local {Silmaril.Compile.Forks.Csem.C.symName x}"
    else match env.globals[x.number]? with
      | some v => .ok v
      | none => .error (.unsupported s!"object {Silmaril.Compile.Forks.Csem.C.symName x} outside the fragment")

/-- Write an object. -/
def writeVar (fd : FunDef) (env : Env) (x : Sym) (v : Int) : Except Stop Env :=
  if fd.locals.contains x.number then .ok { env with locals := env.locals.insert x.number v }
  else if env.globals.contains x.number then
    .ok { env with globals := env.globals.insert x.number v }
  else .error (.unsupported s!"object {Silmaril.Compile.Forks.Csem.C.symName x} outside the fragment")

/-- The usual arithmetic conversions of two operand types, as a C0 type. -/
def usualOf (ta tb : CType) : Except Stop CType := do
  let (w, s) := usual (← shape ta) (← shape tb)
  return .int w s

/-- Externals of the fragment, by name. -/
def external (name : String) (args : List Int) (env : Env) : Except Stop (Int × Env) :=
  match name, args with
  | "abort", [] => .error (.abort env.out)
  | "exit", [c] | "_Exit", [c] => .error (.exit c env.out)
  | "putchar", [c] =>
    let b := wrap 1 false c
    .ok (b, { env with out := env.out.push b.toNat.toUInt8 })
  | n, _ => .error (.unsupported s!"call of the external function {n}")

mutual
/-- Evaluate an expression to a value of its type (`typeOf e`). -/
def evalE (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Int × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    let t := typeOf e
    match e.node with
    | .rvalue a => do
      let x ← lvalSym a
      return (← readVar fd env x, env)
    | .const c => do return (← constVal c t, env)
    | .annot _ a | .cast _ _ a => do
      let (v, env) ← evalE P n fd a env
      return (← convTo t (← convTo (typeOf a) v), env)
    | .unary op a => do
      match op with
      | .plus => let (v, env) ← evalE P n fd a env; return (← convTo t v, env)
      | .minus =>
        let (v, env) ← evalE P n fd a env
        let (w, s) ← shape t
        return (← arith .sub w s 0 (← convTo t v), env)
      | .bnot =>
        let (v, env) ← evalE P n fd a env
        let (w, s) ← shape t
        return (wrap w s (-(← convTo t v) - 1), env)
      | .postfixIncr | .postfixDecr =>
        let x ← lvalSym a
        let ta := typeOf a
        let old ← readVar fd env x
        let (w, s) := usual (← shape ta) (4, true)
        let r ← arith (if op == .postfixIncr then .add else .sub) w s (wrap w s old) 1
        let env ← writeVar fd env x (← convTo ta r)
        return (old, env)
      | _ => .error (.unsupported "address-of or indirection")
    | .binary a op b => do
      match op with
      | .arithmetic aop =>
        let (va, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        let (w, s) ← shape t
        let ca ← convTo t va
        let cb ← if aop == .shl || aop == .shr then pure vb else convTo t vb
        return (← arith aop w s ca cb, env)
      | .comma =>
        let (_, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        return (← convTo t vb, env)
      | .and | .or =>
        let (va, env) ← evalE P n fd a env
        if (op == .and) == (va == 0) then return (if op == .and then 0 else 1, env)
        let (vb, env) ← evalE P n fd b env
        return (if vb == 0 then 0 else 1, env)
      | _ =>
        let (va, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        let u ← usualOf (typeOf a) (typeOf b)
        let some r := compare op (← convTo u va) (← convTo u vb)
          | .error (.unsupported "a binary operator")
        return (if r then 1 else 0, env)
    | .assign l r => do
      let x ← lvalSym l
      let (v, env) ← evalE P n fd r env
      let v ← convTo (typeOf l) v
      return (v, ← writeVar fd env x v)
    | .compoundAssign l aop r => do
      let x ← lvalSym l
      let (vr, env) ← evalE P n fd r env
      let old ← readVar fd env x
      let tl := typeOf l
      let (w, s) ← if aop == .shl || aop == .shr then pure (promote (← shape tl))
        else pure (usual (← shape tl) (← shape (typeOf r)))
      let cr := if aop == .shl || aop == .shr then vr else wrap w s vr
      let res ← convTo tl (← arith aop w s (wrap w s old) cr)
      return (res, ← writeVar fd env x res)
    | .cond c a b => do
      let (vc, env) ← evalE P n fd c env
      if vc != 0 then
        match a with
        | some a => let (v, env) ← evalE P n fd a env; return (← convTo t v, env)
        | none => return (← convTo t vc, env)
      else
        let (v, env) ← evalE P n fd b env
        return (← convTo t v, env)
    | .call f args => do
      let .functionDecay ⟨_, _, _, .ident g⟩ := f.node
        | .error (.unsupported "an indirect call")
      let pts := (P.protos[g.number]?).getD []
      let (vs, env) ← evalArgs P n fd pts args env
      let (v, env) ← callFn P n g vs env
      return (← convTo t v, env)
    | .assert a => do
      let (v, env) ← evalE P n fd a env
      if v == 0 then .error (.abort env.out) else return (0, env)
    | .sizeof _ ty => do
      let (sz, _) ← (sizeAlign P.tags ty).mapError Stop.unsupported
      return (sz, env)
    | .alignof _ ty => do
      let (_, al) ← (sizeAlign P.tags ty).mapError Stop.unsupported
      return (al, env)
    | .sizeofExpr a => do
      match a.annotation with
      | .lvalue _ ty _ =>
        let (sz, _) ← (sizeAlign P.tags ty).mapError Stop.unsupported
        return (sz, env)
      | .rvalue _ => return ((← shape (typeOf a)).1, env)
    | .generic _ (some i) assocs =>
      match assocs[i]? with
      | some (.type_ _ _ a) | some (.default a) => do
        let (v, env) ← evalE P n fd a env
        return (← convTo t v, env)
      | none => .error (.unsupported "_Generic without selection")
    | _ => .error (.unsupported "an expression outside the fragment")

/-- Evaluate arguments left to right, converted to the parameter types `pts` (default
argument promotions beyond them). -/
def evalArgs (P : Prog) : Nat → FunDef → List CType → List TypedExpression → Env → Except Stop ((List Int) × Env)
  | 0, _, _, _, _ => .error .outOfFuel
  | _ + 1, _, _, [], env => .ok ([], env)
  | n + 1, fd, pts, a :: as, env => do
    let (v, env) ← evalE P n fd a env
    let v ← match pts with
      | pt :: _ => convTo pt v
      | [] => do let (w, s) := promote (← shape (typeOf a)); pure (wrap w s v)
    let (vs, env) ← evalArgs P n fd pts.tail as env
    return (v :: vs, env)

/-- Call the function `g` on argument values. -/
def callFn (P : Prog) : Nat → Sym → List Int → Env → Except Stop (Int × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, g, vs, env =>
    match P.funcs[g.number]? with
    | none => external (P.name g) vs env
    | some fd => do
      if fd.params.length != vs.length then
        .error (.unsupported s!"call of {P.name g} with {vs.length} arguments")
      let mut locals : Std.HashMap Nat Int := {}
      for ((x, pt), v) in fd.params.zip vs do
        locals := locals.insert x (← convTo pt v)
      let caller := env.locals
      let (r, env) ← loop P n fd (some fd.body) .stop { env with locals }
      return ((← convTo fd.ret (r.getD 0)), { env with locals := caller })

/-- Run the statement machine of one activation to its return. -/
def loop (P : Prog) : Nat → FunDef → Option TypedStatement → Kont → Env → Except Stop ((Option Int) × Env)
  | 0, _, _, _, _ => .error .outOfFuel
  | n + 1, fd, focus, k, env =>
    match step P n fd focus k env with
    | .ok (.running focus k, env) => loop P n fd focus k env
    | .ok (.returned v, env) => .ok (v, env)
    | .error e => .error e

/-- One step of the statement machine. -/
def step (P : Prog) : Nat → FunDef → Option TypedStatement → Kont → Env → Except Stop (Next × Env)
  | 0, _, _, _, _ => .error .outOfFuel
  | n + 1, fd, none, k, env =>
    match k with
    | .stop => .ok (.returned none, env)
    | .seq [] k => .ok (.running none k, env)
    | .seq (s :: ss) k => .ok (.running (some s) (.seq ss k), env)
    | .while_ c b k' => do
      let (v, env) ← evalE P n fd c env
      return (if v != 0 then .running (some b) k else .running none k', env)
    | .do_ b c k' => do
      let (v, env) ← evalE P n fd c env
      return (if v != 0 then .running (some b) k else .running none k', env)
    | .switch k => .ok (.running none k, env)
  | n + 1, fd, some s, k, env =>
    match s.node with
    | .skip => .ok (.running none k, env)
    | .expr e => do let (_, env) ← evalE P n fd e env; return (.running none k, env)
    | .block _ ss => .ok (.running none (.seq ss k), env)
    | .declaration ds => do
      let mut env := env
      for (x, init) in ds do
        match init with
        | some e =>
          let (v, env') ← evalE P n fd e env
          let v ← convTo ((fd.locals[x.number]?).getD (typeOf e)) v
          env := { env' with locals := env'.locals.insert x.number v }
        | none => env := { env with locals := env.locals.erase x.number }
      return (.running none k, env)
    | .if_ c a b => do
      let (v, env) ← evalE P n fd c env
      return (.running (some (if v != 0 then a else b)) k, env)
    | .while_ c b _ => .ok (.running none (.while_ c b k), env)
    | .do_ b c _ => .ok (.running (some b) (.do_ b c k), env)
    | .break_ =>
      match k.breakTo with
      | some k => .ok (.running none k, env)
      | none => .error (.unsupported "break outside a loop or switch")
    | .continue_ =>
      match k.continueTo with
      | some k => .ok (.running none k, env)
      | none => .error (.unsupported "continue outside a loop")
    | .returnVoid => .ok (.returned none, env)
    | .return_ e => do
      let (v, env) ← evalE P n fd e env
      return (.returned (some (← convTo fd.ret v)), env)
    | .switch e body => do
      let (v, env) ← evalE P n fd e env
      let (w, sg) := promote (← shape (typeOf e))
      let v := wrap w sg v
      match findCase (caseMatches w sg v) body (.switch k) with
      | some (s', k') => return (.running (some s') k', env)
      | none =>
        match findCase (fun c => c.isNone) body (.switch k) with
        | some (s', k') => return (.running (some s') k', env)
        | none => return (.running none k, env)
    | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b =>
      .ok (.running (some b) k, env)
    | .goto l =>
      match findLabel l.number fd.body .stop with
      | some (s', k') => .ok (.running (some s') k', env)
      | none => .error (.unsupported s!"goto an unknown label {Silmaril.Compile.Forks.Csem.C.symName l}")
    | _ => .error (.unsupported "a statement outside the fragment")
end

/-! ## Whole programs -/

/-- The result of a run. -/
inductive Result where
  | done (o : Obs)
  | undefined (why : String)
  | outOfFuel
  | unsupported (why : String)

/-- The function of a dummy activation (for global initializers). -/
def topFrame : FunDef := ⟨[], .void, .mk .unknown ⟨false, none⟩ (.mk []) .skip, {}⟩

/-- Initialize the objects of static storage duration, in declaration order. -/
def initGlobals (P : Prog) (fuel : Nat) : List (Nat × CType × Option TypedExpression) → Env →
    Except Stop Env
  | [], env => .ok env
  | (x, t, init) :: gs, env => do
    let env ← match t with
      | .int .. | .bool =>
        match init with
        | some e => do
          let (v, env) ← evalE P fuel topFrame e env
          pure { env with globals := env.globals.insert x (← convTo t v) }
        | none => pure { env with globals := env.globals.insert x 0 }
      | _ => pure env
    initGlobals P fuel gs env

def toStatus (c : Int) : Exit := .status (c % 256).toNat

/-- **The C0 interpreter.** Run `main` with `fuel`. -/
def run (fuel : Nat) (p : TypedProgram) : Result :=
  let P := prepare p
  let r : Except Stop (Int × Env) := do
    let env ← initGlobals P fuel P.globals {}
    let some m := P.main | .error (.unsupported "no main")
    let some fd := P.funcs[m]? | .error (.unsupported "main is not defined")
    -- `main(int argc, char **argv)`: `argc = 1`; `argv` is outside the fragment (its reads
    -- are rejected by `check`), so it is left unset
    let locals : Std.HashMap Nat Int := match fd.params with
      | (x, .int ..) :: _ => ({} : Std.HashMap Nat Int).insert x 1
      | _ => {}
    let (r, env) ← loop P fuel fd (some fd.body) .stop { env with locals }
    return (r.getD 0, env)
  match r with
  | .ok (v, env) => .done ⟨env.out.toList, toStatus v⟩
  | .error (.exit c out) => .done ⟨out.toList, toStatus c⟩
  | .error (.abort out) => .done ⟨out.toList, .signal 6⟩
  | .error (.undefined why) => .undefined why
  | .error .outOfFuel => .outOfFuel
  | .error (.unsupported why) => .unsupported why

/-! ## Behaviours and the language -/

/-- The behaviours of a program under C0: the observation of a terminating run, everything
after undefined behaviour, divergence when no fuel suffices. Programs outside the fragment
(runs ending `unsupported`) have no behaviour: C0 makes no claim about them. -/
def beh (p : TypedProgram) : Set Obs := {o |
  (∃ n, run n p = .done o) ∨ (∃ n why, run n p = .undefined why) ∨
    (o = ⟨[], .diverges⟩ ∧ ∀ n, run n p = .outOfFuel)}

/-- C0 as a semantics of C. -/
def sem : Semantics := beh

/-- C0 as a language of the zoo. -/
def lang : Language.{0} := cSyntax.lang sem

theorem beh_of_done {p : TypedProgram} {n : Nat} {o : Obs} (h : run n p = .done o) :
    o ∈ beh p := .inl ⟨n, h⟩

/-- Undefined behaviour allows every behaviour. -/
theorem beh_of_undefined {p : TypedProgram} {n : Nat} {why : String}
    (h : run n p = .undefined why) : beh p = Set.univ :=
  Set.eq_univ_of_forall fun _ => .inr (.inl ⟨n, why, h⟩)

/-! ## The fragment -/

/-- Is `t` a type of C0 values? -/
def intType : CType → Bool
  | .int .. | .bool => true
  | _ => false

mutual
/-- Check that an expression is in the fragment. -/
def checkE (P : Prog) : TypedExpression → Except String Unit
  | .mk _ _ _ node => checkN P node
def checkN (P : Prog) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a => do
    match a.node with
    | .ident x =>
      if !intType (typeOf a) then throw s!"object {Silmaril.Compile.Forks.Csem.C.symName x} of a non-integer type"
    | _ => throw "an lvalue other than an identifier"
  | .const c =>
    match c with
    | .integer _ | .character _ | .predefined _ => pure ()
    | _ => throw "a non-integer constant"
  | .annot _ a | .cast _ _ a | .assert a => checkE P a
  | .unary op a =>
    match op with
    | .plus | .minus | .bnot => checkE P a
    | .postfixIncr | .postfixDecr => checkLv P a
    | .address => throw "address-of"
    | .indirection => throw "indirection"
  | .binary a _ b => do checkE P a; checkE P b
  | .assign l r | .compoundAssign l _ r => do checkLv P l; checkE P r
  | .cond c a b => do
    checkE P c
    match a with
    | some a => checkE P a
    | none => pure ()
    checkE P b
  | .call f args => do
    match f.node with
    | .functionDecay ⟨_, _, _, .ident g⟩ =>
      if !P.funcs.contains g.number &&
          !(["abort", "exit", "_Exit", "putchar"].contains (P.name g)) then
        throw s!"call of the external function {P.name g}"
    | _ => throw "an indirect call"
    checkL P args
  | .sizeof .. | .alignof .. => pure ()
  | .sizeofExpr _ => pure ()
  | .generic _ (some _) assocs => checkG P assocs
  | _ => throw "an expression outside the fragment"
def checkLv (_P : Prog) : TypedExpression → Except String Unit
  | .mk a _ _ (.ident x) =>
    match a with
    | .lvalue _ ty _ =>
      if intType (ofCtype ty) then pure () else throw s!"object {Silmaril.Compile.Forks.Csem.C.symName x} of a non-integer type"
    | .rvalue _ => throw "an rvalue in lvalue position"
  | _ => throw "an lvalue other than an identifier"
def checkL (P : Prog) : List TypedExpression → Except String Unit
  | [] => pure ()
  | e :: es => do checkE P e; checkL P es
def checkG (P : Prog) : List (GenericAssociation GenTypeCategory) → Except String Unit
  | [] => pure ()
  | .type_ _ _ e :: gs | .default e :: gs => do checkE P e; checkG P gs
end

/-- The expression types of the fragment: every expression (except called function
designators) has an integer or `void` type. -/
def checkTypes (e : TypedExpression) : Except String Unit :=
  match typeOf e with
  | .int .. | .bool | .void => pure ()
  | _ => throw "an expression of a non-integer type"

mutual
def checkS (P : Prog) : TypedStatement → Except String Unit
  | .mk _ _ _ node => checkSN P node
def checkSN (P : Prog) : StatementNode GenTypeCategory → Except String Unit
  | .skip | .break_ | .continue_ | .returnVoid | .goto _ => pure ()
  | .expr e | .return_ e => do checkTypes e; checkE P e
  | .block bs ss => do
    for (x, (_, _, _, ty)) in bs do
      if !intType (ofCtype ty) then throw s!"local {Silmaril.Compile.Forks.Csem.C.symName x} of a non-integer type"
    checkSL P ss
  | .if_ c a b => do checkTypes c; checkE P c; checkS P a; checkS P b
  | .while_ c b _ | .do_ b c _ => do checkTypes c; checkE P c; checkS P b
  | .switch e b => do checkTypes e; checkE P e; checkS P b
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => checkS P b
  | .declaration ds => checkD P ds
  | _ => throw "a statement outside the fragment"
def checkSL (P : Prog) : List TypedStatement → Except String Unit
  | [] => pure ()
  | s :: ss => do checkS P s; checkSL P ss
def checkD (P : Prog) : List (Sym × Option TypedExpression) → Except String Unit
  | [] => pure ()
  | (_, some e) :: ds => do checkTypes e; checkE P e; checkD P ds
  | (_, none) :: ds => checkD P ds
end

mutual
/-- The functions an expression calls directly. -/
def callsE : TypedExpression → List Nat
  | .mk _ _ _ node => callsN node
def callsN : ExpressionNode GenTypeCategory → List Nat
  | .call f args =>
    (match f.node with
      | .functionDecay ⟨_, _, _, .ident g⟩ => [g.number]
      | _ => callsE f) ++ callsEL args
  | .unary _ a | .annot _ a | .cast _ _ a | .assert a | .rvalue a | .sizeofExpr a
  | .functionDecay a | .arrayDecay a | .memberof a _ | .memberofptr a _ => callsE a
  | .binary a _ b | .assign a b | .compoundAssign a _ b => callsE a ++ callsE b
  | .cond c a b => callsE c ++ (match a with | some a => callsE a | none => []) ++ callsE b
  | _ => []
def callsEL : List TypedExpression → List Nat
  | [] => []
  | e :: es => callsE e ++ callsEL es
end

mutual
/-- The functions a statement calls directly. -/
def callsS : TypedStatement → List Nat
  | .mk _ _ _ node => callsSN node
def callsSN : StatementNode GenTypeCategory → List Nat
  | .expr e | .return_ e => callsE e
  | .block _ ss | .par ss => callsSL ss
  | .if_ c a b => callsE c ++ callsS a ++ callsS b
  | .while_ c b _ | .do_ b c _ | .switch c b => callsE c ++ callsS b
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => callsS b
  | .declaration ds => callsD ds
  | _ => []
def callsSL : List TypedStatement → List Nat
  | [] => []
  | s :: ss => callsS s ++ callsSL ss
def callsD : List (Sym × Option TypedExpression) → List Nat
  | [] => []
  | (_, some e) :: ds => callsE e ++ callsD ds
  | (_, none) :: ds => callsD ds
end

/-- The functions defined in the program and reachable from `roots` by direct calls. -/
def reachable (P : Prog) (roots : List Nat) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo := roots
  let mut out : Array Nat := #[]
  for _ in [0:P.funcs.size + roots.length + 1] do
    let mut next : List Nat := []
    for f in todo do
      if seen.contains f then continue
      seen := seen.insert f
      if let some fd := P.funcs[f]? then
        out := out.push f
        next := callsS fd.body ++ next
    todo := next
  return out.toList

/-- Is the program in the C0 fragment? The reason when it is not. Only the functions reachable
from `main` are checked (headers declare, and `cerberus.h` defines, many functions and objects
outside the fragment); a use of anything else is rejected where it occurs (`checkN`,
`checkLv`). -/
def check (p : TypedProgram) : Except String Unit := do
  let P := prepare p
  let some m := P.main | throw "no main"
  let some _ := P.funcs[m]? | throw "main is not defined"
  let live := reachable P (m :: (P.globals.flatMap fun (_, _, i) => (i.map callsE).getD []))
  for (x, (_, _, d)) in p.2.declarations do
    match d with
    | .function _ (_, ret) ps variadic _ _ =>
      if live.contains x.number && x.number != m then
        if variadic then throw s!"a variadic function {Silmaril.Compile.Forks.Csem.C.symName x}"
        if !(intType (ofCtype ret) || ofCtype ret matches .void) then
          throw s!"a function with a non-integer result: {Silmaril.Compile.Forks.Csem.C.symName x}"
        if ps.any fun (_, t, _) => !intType (ofCtype t) then
          throw s!"a function with a non-integer parameter: {Silmaril.Compile.Forks.Csem.C.symName x}"
    | .object .. => pure ()
  for (_, t, init) in P.globals do
    if intType t then
      if let some e := init then checkE P e
  for f in live do
    if let some fd := P.funcs[f]? then checkS P fd.body
  -- no address is ever taken (`checkN` rejects `&`), so every local is a register

/-- The C0 fragment. -/
def InFragment (p : TypedProgram) : Prop := check p = .ok ()

instance (p : TypedProgram) : Decidable (InFragment p) :=
  inferInstanceAs (Decidable (check p = .ok ()))

/-- The fragment as a set of programs. -/
def fragment : Set TypedProgram := {p | InFragment p}

end Silmaril.Compile.C.Sem.C0
