module

public import Silmaril.Compiler.C.Sem.C3.Defs
public import Silmaril.Cerberus.Core.Compatibility.Defs
@[expose] public section

/-!
# C4: function pointers and typed variadic calls

C4 extends C3 with function designators, indirect calls, variadic definitions and
`va_start`, `va_arg`, `va_copy`, `va_end`. Function addresses are distinct nonzero
code tokens, separate from object memory. Calls use the expression's prototype;
extra arguments receive the default promotions (including float to double).

Cerberus lowers `va_list` to an integer and start/copy to assignments of builtin
results. C4 interprets that integer as an opaque cursor handle. Passing a handle
shares its position; copying creates an independent position; ending invalidates
it. Each activation owns its cursors, which expire on return. Arguments retain
their promoted types and aggregate byte snapshots: exhausting a list, using an
expired handle or requesting an incompatible type is undefined. This models C's
abstract variadic interface, rather than the host register-save-area layout.
Raw code addresses and cursor integers are implementation choices, not a SysV ABI.
Externals remain C3's (in particular no FILE streams or floating printf).

The intended ladder law is `C3.sem ⊑[C3.fragment] C4.sem`. C3 programs have no
function values or variadic builtins, so the additional state is inert. This law
is stated, not proved; the driver preserves C1 → C2 → C3 dispatch before C4.
-/

namespace Silmaril.Compile.C.Sem.C4

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C Silmaril.Compile.Category
open C0 (Stop ub Kont Result)
open C1 (Memory Place FunDef wrap convTo shape store base externals plainString)
open C2 (Layout Agg Val Next aggOf lvType readAgg writeAgg depth)
open C3 (ofInt truthOf floatConst storeV layoutOf sizeAlignOf)

/-- A value together with its parameter type or default-promoted argument type. -/
structure Arg where
  ty : CType
  val : Val

/-- A cursor belongs to one live activation, even when passed to a helper. -/
structure Cursor where
  owner : Nat
  remaining : List Arg

/-- C3's store, plus abstract variadic activation and cursor state. -/
structure Env extends toC1 : C1.Env where
  extra : Option (List Arg) := none
  lastParam : Option Nat := none
  activation : Nat := 0
  nextActivation : Nat := 1
  cursors : Std.HashMap Nat Cursor := {}
  nextCursor : Nat := 1

@[inline] def Env.withMem (env : Env) (f : Memory → Except Stop Memory) : Except Stop Env := do
  return { env with mem := ← f env.mem }

@[inline] def Env.setReg (env : Env) (x : Nat) (v : Int) : Env :=
  { env with regs := env.regs.insert x v }

/-- Allocate an independent abstract cursor (handles fit Cerberus's signed int). -/
def Env.newCursor (env : Env) (c : Cursor) : Except Stop (Int × Env) := do
  if env.nextCursor ≥ 2^31 then throw (.unsupported "variadic cursor handles exhausted")
  return (env.nextCursor, { env with
    cursors := env.cursors.insert env.nextCursor c, nextCursor := env.nextCursor + 1 })

/-- Consume a variadic argument, updating the shared cursor. -/
def Env.takeArg (env : Env) (h : Int) : Except Stop (Arg × Env) := do
  if h ≤ 0 then ub "an invalid va_list"
  let some c := env.cursors[h.toNat]? | ub "an expired or invalid va_list"
  let a :: rest := c.remaining | ub "va_arg past the last argument"
  return (a, { env with cursors := env.cursors.insert h.toNat { c with remaining := rest } })

/-- Invalidate every cursor into the arguments of an activation that has returned. -/
def Env.expire (env : Env) (activation : Nat) : Env :=
  { env with cursors := env.cursors.filter (fun _ c => c.owner != activation) }

/-- Reuse C3's scalar memory and local-value operations. -/
def readPlace (fd : FunDef) (env : Env) (t : CType) (pl : Place) : Except Stop Int :=
  C3.readPlace fd env.toC1 t pl

def writePlace (env : Env) (t : CType) (v : Int) : Place → Except Stop Env
  | .reg x => .ok (env.setReg x v)
  | .mem a => env.withMem (storeV · t a v)

def external (name : String) (args : List Int) (env : Env) : Except Stop (Int × Env) := do
  let (v, e) ← C1.external name args env.toC1
  return (v, { env with toC1 := e })

/-- Function designators have rvalue function annotations in typed Ail. -/
def isFunction (e : TypedExpression) : Bool :=
  match typeOf e with
  | .func _ => true
  | _ => false

mutual
/-- Is `t` the type of an object of C4: an integer, a real floating type (a `long double`
object has no value in C4, but it can be laid out, copied and pointed to), a pointer to an object
type of C4, to a struct or union or to `void`, an array of known size of objects of C4, or a
struct or union of C4 whose members are objects of C4? -/
def objType (L : Layout) : Nat → Ctype → Bool
  | 0, _ => false
  | n + 1, .mk _ node =>
    match node with
    | .basic (.integer _) => true
    | .basic (.floating (.realFloating _)) => true
    | .pointer _ t => pointee L n t
    | .array t (some _) => objType L n t
    | .struct tag | .union tag =>
      match L.fields[tag.number]? with
      | some ts => ts.all (objType L n ·)
      | none => false
    | _ => false
/-- Can `t` be pointed to? -/
def pointee (L : Layout) : Nat → Ctype → Bool
  | 0, _ => false
  | n + 1, t@(.mk _ node) =>
    match node with
    | .void | .struct _ | .union _ | .function .. | .functionNoParams _ => true
    | _ => objType L n t
end

mutual
/-- The string literals (bytes) and address-taken symbols of an expression (`C1.scanE`, also
in struct and union initializers). -/
def scanE : TypedExpression → List (List UInt8) × List Nat
  | .mk _ _ _ node => scanN node
def scanN : ExpressionNode GenTypeCategory → List (List UInt8) × List Nat
  | .str s => ([(Silmaril.Compile.Forks.Csem.C.stringBytes s).toList], [])
  | .unary .address a =>
    let (l, t) := scanE a
    match a.node with
    | .ident x => (l, x.number :: t)
    | _ => (l, t)
  | .unary _ a | .annot _ a | .cast _ _ a | .assert a | .rvalue a | .arrayDecay a
  | .functionDecay a | .memberof a _ | .memberofptr a _ | .compound _ _ a
  | .vaStart a _ | .vaArg a _ | .vaEnd a => scanE a
  | .binary a _ b | .assign a b | .compoundAssign a _ b | .vaCopy a b =>
    let (l1, t1) := scanE a
    let (l2, t2) := scanE b
    (l1 ++ l2, t1 ++ t2)
  | .cond c a b =>
    let (l1, t1) := scanE c
    let (l2, t2) := match a with
      | some a => scanE a
      | none => ([], [])
    let (l3, t3) := scanE b
    (l1 ++ l2 ++ l3, t1 ++ t2 ++ t3)
  | .call f args =>
    let (l1, t1) := scanE f
    let (l2, t2) := scanL args
    (l1 ++ l2, t1 ++ t2)
  | .array _ _ es => scanO es
  | .struct _ ms => scanM ms
  | .union _ _ (some e) => scanE e
  | .generic _ _ gs => scanG gs
  | _ => ([], [])
def scanL : List TypedExpression → List (List UInt8) × List Nat
  | [] => ([], [])
  | e :: es =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanL es
    (l1 ++ l2, t1 ++ t2)
def scanO : List (Option TypedExpression) → List (List UInt8) × List Nat
  | [] => ([], [])
  | none :: es => scanO es
  | some e :: es =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanO es
    (l1 ++ l2, t1 ++ t2)
def scanM : List (Identifier × Option TypedExpression) → List (List UInt8) × List Nat
  | [] => ([], [])
  | (_, none) :: es => scanM es
  | (_, some e) :: es =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanM es
    (l1 ++ l2, t1 ++ t2)
def scanG : List (GenericAssociation GenTypeCategory) → List (List UInt8) × List Nat
  | [] => ([], [])
  | .type_ _ _ e :: gs | .default e :: gs =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanG gs
    (l1 ++ l2, t1 ++ t2)
end

mutual
/-- The string literals and address-taken symbols of a statement. -/
def scanS : TypedStatement → List (List UInt8) × List Nat
  | .mk _ _ _ node => scanSN node
def scanSN : StatementNode GenTypeCategory → List (List UInt8) × List Nat
  | .expr e | .return_ e => scanE e
  | .block _ ss | .par ss => scanSL ss
  | .if_ c a b =>
    let (l1, t1) := scanE c
    let (l2, t2) := scanS a
    let (l3, t3) := scanS b
    (l1 ++ l2 ++ l3, t1 ++ t2 ++ t3)
  | .while_ c b _ | .do_ b c _ | .switch c b =>
    let (l1, t1) := scanE c
    let (l2, t2) := scanS b
    (l1 ++ l2, t1 ++ t2)
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => scanS b
  | .declaration ds => scanD ds
  | _ => ([], [])
def scanSL : List TypedStatement → List (List UInt8) × List Nat
  | [] => ([], [])
  | s :: ss =>
    let (l1, t1) := scanS s
    let (l2, t2) := scanSL ss
    (l1 ++ l2, t1 ++ t2)
def scanD : List (Sym × Option TypedExpression) → List (List UInt8) × List Nat
  | [] => ([], [])
  | (_, some e) :: ds =>
    let (l1, t1) := scanE e
    let (l2, t2) := scanD ds
    (l1 ++ l2, t1 ++ t2)
  | (_, none) :: ds => scanD ds
end

/-! ## Programs -/

/-- A prepared program: C2's, with C4's layout. -/
structure Prog extends toC3 : C3.Prog where
  variadics : Std.HashSet Nat := {}
  symbols : Std.HashMap Nat Sym := {}

/-- Size and alignment of a type. -/
def Prog.sizeAlign (P : Prog) (ty : Ctype) : Except Stop (Nat × Nat) :=
  (sizeAlignOf P.layout depth ty).mapError Stop.unsupported

/-- The size of the pointee of a pointer type, for pointer arithmetic (`void`: 1). -/
def Prog.pointee (P : Prog) : CType → Except Stop Nat
  | .ptr ty => do return max 1 (← P.sizeAlign ty).1
  | _ => throw (.unsupported "pointer arithmetic on a non-pointer")

/-- Is `t` the type of an object of C4? -/
def Prog.obj (P : Prog) (t : Ctype) : Bool := objType P.layout depth t

/-- Prepare a typed-Ail program and lay out its static memory (`C2.prepare`, with C4's layout
and floating locals in registers). -/
def prepare (p : TypedProgram) : Prog := Id.run do
  let σ := p.2
  let tags := tagsOf σ
  let layout := layoutOf σ
  let sizeOf (ty : Ctype) : Except String (Nat × Nat) := sizeAlignOf layout depth ty
  let mut variadics : Std.HashSet Nat := {}
  let mut symbols : Std.HashMap Nat Sym := {}
  let mut protos : Std.HashMap Nat (List CType) := {}
  let mut pctys : Std.HashMap Nat (List Ctype) := {}
  let mut rets : Std.HashMap Nat CType := {}
  let mut names : Std.HashMap Nat String := {}
  let mut statics : Array (Nat × Ctype × Option TypedExpression) := #[]
  let inits : Std.HashMap Nat TypedExpression :=
    σ.objectDefinitions.foldl (fun m (x, e) => m.insert x.number e) {}
  for (x, (_, _, d)) in σ.declarations do
    names := names.insert x.number (Silmaril.Compile.Forks.Csem.C.symName x)
    match d with
    | .function _ (_, ret) ps variadic _ _ =>
      symbols := symbols.insert x.number x
      if variadic then variadics := variadics.insert x.number
      protos := protos.insert x.number (ps.map fun (_, t, _) => ofCtype t)
      pctys := pctys.insert x.number (ps.map fun (_, t, _) => t)
      rets := rets.insert x.number (ofCtype ret)
    | .object (dur, _) _ _ ty =>
      if dur != .automatic then statics := statics.push (x.number, ty, inits[x.number]?)
  let mut lits : List (List UInt8) := []
  for (_, e) in σ.objectDefinitions do
    lits := lits ++ (scanE e).1
  let mut funcs : Std.HashMap Nat FunDef := {}
  for (x, fd) in σ.functionDefinitions do
    let pts := (protos[x.number]?).getD []
    let pcs := (pctys[x.number]?).getD []
    let params := fd.params.zipIdx.map fun (y, i) => (y.number, (pts[i]?).getD (.int 4 true))
    let blockLocals := C1.localsS fd.body
    let locals := blockLocals.foldl (fun m (n, t) => m.insert n (ofCtype t))
      (params.foldl (fun m (n, t) => m.insert n t) {})
    let (ls, taken) := scanS fd.body
    lits := lits ++ ls
    let all := fd.params.zipIdx.map (fun (y, i) => (y.number, (pcs[i]?).getD (.mk [] .void)))
      ++ blockLocals
    let memLocals := all.filter fun (n, t) =>
      taken.contains n || (C3.width (ofCtype t)).isNone
    funcs := funcs.insert x.number
      { params, ret := (rets[x.number]?).getD (.int 4 true), body := fd.body, locals,
        memLocals, inMem := memLocals.foldl (fun s (n, _) => s.insert n) {} }
  -- layout: string literals, objects of static storage duration, argv
  let mut a := base
  let mut strs : Std.HashMap (List UInt8) Nat := {}
  for l in lits do
    if !strs.contains l then
      strs := strs.insert l a
      a := a + l.length + 1
  let roTop := a
  let mut gaddr : Std.HashMap Nat Nat := {}
  for (x, ty, _) in statics do
    if gaddr.contains x then continue
    match sizeOf ty with
    | .ok (size, align) =>
      a := C1.alignUp a (max align 1)
      gaddr := gaddr.insert x a
      a := a + max size 1
    | .error _ => pure ()
  let argv := C1.alignUp a 16
  return { funcs, protos, names, statics := statics.toList, tags, main := p.1.map (·.number),
           strs, gaddr, argv, roTop, top := C1.alignUp (argv + 17) 16, layout, variadics, symbols }

/-- Code tokens occupy the high half of the pointer space. -/
def codeAddress (x : Nat) : Nat := 2^63 + x

/-- Recover a declared function from its token. -/
def Prog.resolve (P : Prog) (v : Int) : Except Stop Sym := do
  if v < (2^63 : Nat) then ub "call through an invalid function pointer"
  let some g := P.symbols[(v - (2^63 : Nat)).toNat]?
    | ub "call through an invalid function pointer"
  return g

/-- Parameter types from the call expression's static function type. -/
def callTypes (f : TypedExpression) : Except Stop (List CType) :=
  match typeOf f with
  | .ptr (.mk _ (.function _ ps _)) => .ok (ps.map fun (_, t, _) => ofCtype t)
  | .ptr (.mk _ (.functionNoParams _)) => .ok []
  | _ => .error (.unsupported "call of a non-function")

/-- Equality relevant to a variadic argument's type; source locations and typedef
annotations are immaterial. Integer signed/unsigned exceptions require representability. -/
def vaCompatible (actual requested : CType) (v : Val) : Bool :=
  match actual, requested with
  | .int w s, .int w' s' => w == w' && (s == s' ||
      (C1.inRange w s v.int && C1.inRange w' s' v.int))
  | .float w, .float w' => w == w'
  | .ptr a, .ptr b =>
    let voidChar : Ctype → Ctype → Bool := fun x y => match x, y with
      | .mk _ .void, .mk _ (.basic (.integer .char))
      | .mk _ .void, .mk _ (.basic (.integer (.signed .ichar)))
      | .mk _ .void, .mk _ (.basic (.integer (.unsigned .ichar)))
      | .mk _ (.basic (.integer .char)), .mk _ .void
      | .mk _ (.basic (.integer (.signed .ichar))), .mk _ .void
      | .mk _ (.basic (.integer (.unsigned .ichar))), .mk _ .void => true
      | _, _ => false
    voidChar a b || (Silmaril.Cerberus.Core.compatible depth
      Silmaril.Cerberus.Core.noQualifiers a Silmaril.Cerberus.Core.noQualifiers b).toOption.getD false
  | .agg (.mk _ (.struct a)), .agg (.mk _ (.struct b))
  | .agg (.mk _ (.union a)), .agg (.mk _ (.union b)) => a.number == b.number
  | _, _ => false

/-! ## Initializers -/

mutual
/-- Write the constant `c` of type `ty` at `a` (the object is already zeroed). -/
def writeConst (P : Prog) (m : Memory) (a : Nat) (ty : Ctype) : Constant → Except Stop Memory
  | .array et cs => do
    let (esize, _) ← P.sizeAlign et
    writeConsts P m a esize et cs
  | .struct _ ms => writeMembers P m a ty ms
  | .union _ x c => do
    let (off, mty) ← P.member ty x
    writeConst P m (a + off) mty c
  | .indeterminate _ | .null => .ok m
  | .integer ic => do
    let t := ofCtype ty
    storeV m t a (← ofInt t (Silmaril.Compile.Forks.Csem.C.intConstValue ic))
  | .character cc => do
    let t := ofCtype ty
    storeV m t a (← ofInt t (Silmaril.Compile.Forks.Csem.C.charValue cc))
  | .predefined pc => do
    let t := ofCtype ty
    storeV m t a (← ofInt t (if pc matches .true_ then 1 else 0))
  | .floating fc => do
    let t := ofCtype ty
    let (w, x) ← floatConst fc
    storeV m t a (← C3.conv (.float w) t x)
def writeConsts (P : Prog) (m : Memory) (a esize : Nat) (et : Ctype) :
    List Constant → Except Stop Memory
  | [] => .ok m
  | c :: cs => do
    let m ← writeConst P m a et c
    writeConsts P m (a + esize) esize et cs
def writeMembers (P : Prog) (m : Memory) (a : Nat) (ty : Ctype) :
    List (Identifier × Constant) → Except Stop Memory
  | [] => .ok m
  | (x, c) :: cs => do
    let (off, mty) ← P.member ty x
    let m ← writeConst P m (a + off) mty c
    writeMembers P m a ty cs
end

/-! ## Evaluation -/

/-- The usual arithmetic conversions of two operand types (STD §6.3.1.8): the wider floating
type if one is floating, else C1's. -/
def usualOf (ta tb : CType) : Except Stop CType :=
  match floatCommon ta tb with
  | some u => .ok u
  | none => C1.usualOf ta tb

mutual
/-- Evaluate a function designator without reading object memory. -/
def evalF (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Int × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    match e.node with
    | .ident g =>
      if P.symbols.contains g.number then .ok (codeAddress g.number, env)
      else .error (.unsupported "an undeclared function designator")
    | .unary .indirection p => evalE P n fd p env
    | .annot _ a => evalF P n fd a env
    | _ => .error (.unsupported "a function designator outside C4")

/-- The place an lvalue designates. -/
def evalL (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Place × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    match e.node with
    | .ident x =>
      if fd.locals.contains x.number && !fd.inMem.contains x.number then
        .ok (.reg x.number, env)
      else match env.frame[x.number]? with
        | some a => .ok (.mem a, env)
        | none => match P.gaddr[x.number]? with
          | some a => .ok (.mem a, env)
          | none => .error (.unsupported s!"object {Silmaril.Compile.Forks.Csem.C.symName x} outside the fragment")
    | .unary .indirection p => do
      let (v, env) ← evalE P n fd p env
      return (.mem v.toNat, env)
    | .memberof a m => do
      let (pl, env) ← evalL P n fd a env
      let b ← pl.addr
      let (off, _) ← P.member (lvType a) m
      return (.mem (b + off), env)
    | .memberofptr p m => do
      let (v, env) ← evalE P n fd p env
      let .ptr sty := typeOf p | .error (.unsupported "a member through a non-pointer")
      let (off, _) ← P.member sty m
      return (.mem (v.toNat + off), env)
    | .str s =>
      match P.strs[(Silmaril.Compile.Forks.Csem.C.stringBytes s).toList]? with
      | some a => .ok (.mem a, env)
      | none => .error (.unsupported "an unknown string literal")
    | .annot _ a => evalL P n fd a env
    | _ => .error (.unsupported "an lvalue outside the fragment")

/-- Evaluate an expression of a struct or union type to its bytes. -/
def evalA (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Agg × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    match e.node with
    | .vaArg ap ty => do
      let (h, env) ← evalE P n fd ap env
      let (arg, env) ← env.takeArg h
      if !vaCompatible arg.ty (ofCtype ty) arg.val then ub "va_arg with an incompatible type"
      match arg.val with
      | .agg v => return (v, env)
      | .scalar _ => ub "va_arg of a scalar as an aggregate"
    | .rvalue a => do
      let (pl, env) ← evalL P n fd a env
      let b ← pl.addr
      let (size, _) ← P.sizeAlign (lvType a)
      return (← readAgg env.mem b size, env)
    | .assign l r => do
      let (v, env) ← evalA P n fd r env
      let (pl, env) ← evalL P n fd l env
      let b ← pl.addr
      return (v, ← env.withMem (writeAgg · b v))
    | .call f args => do
      let (target, env) ← evalE P n fd f env
      let g ← P.resolve target
      let pts ← callTypes f
      let (vs, env) ← evalArgs P n fd pts args env
      let (v, env) ← callFn P n g vs env
      match v with
      | .agg v => return (v, env)
      | .scalar _ => .error (.unsupported "a scalar result of an aggregate call")
    | .cond c a b => do
      let (vc, env) ← evalE P n fd c env
      if truthOf (typeOf c) vc then
        match a with
        | some a => evalA P n fd a env
        | none => .error (.unsupported "an aggregate ?: without a middle operand")
      else evalA P n fd b env
    | .binary a .comma b => do
      let env ← evalD P n fd a env
      evalA P n fd b env
    | .annot _ a => evalA P n fd a env
    | _ => .error (.unsupported "an aggregate expression outside C4")

/-- Evaluate an expression for its effects only. -/
def evalD (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop Env
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    match aggOf (typeOf e) with
    | some _ => do let (_, env) ← evalA P n fd e env; return env
    | none => do let (_, env) ← evalE P n fd e env; return env

/-- Evaluate an expression to a value of its scalar type (`typeOf e`). -/
def evalE (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Int × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    let t := typeOf e
    match e.node with
    | .functionDecay a => evalF P n fd a env
    | .vaStart _ last => do
      let some args := env.extra | ub "va_start outside a variadic activation"
      if env.lastParam != some last.number then ub "va_start with another last parameter"
      env.newCursor ⟨env.activation, args⟩
    | .vaCopy _ src => do
      let (h, env) ← evalE P n fd src env
      if h ≤ 0 then ub "va_copy of an invalid va_list"
      let some c := env.cursors[h.toNat]? | ub "va_copy of an expired va_list"
      env.newCursor c
    | .vaEnd ap => do
      let (h, env) ← evalE P n fd ap env
      if h ≤ 0 || !env.cursors.contains h.toNat then ub "va_end of an invalid va_list"
      return (0, { env with cursors := env.cursors.erase h.toNat })
    | .vaArg ap ty => do
      let (h, env) ← evalE P n fd ap env
      let (arg, env) ← env.takeArg h
      if !vaCompatible arg.ty (ofCtype ty) arg.val then ub "va_arg with an incompatible type"
      match arg.val with
      | .scalar v => return (← C3.conv arg.ty (ofCtype ty) v, env)
      | .agg _ => ub "va_arg of an aggregate as a scalar"
    | .rvalue a => do
      let (pl, env) ← evalL P n fd a env
      return (← readPlace fd env (typeOf a) pl, env)
    | .arrayDecay a => do
      let (pl, env) ← evalL P n fd a env
      return (← pl.addr, env)
    | .const .null => .ok (0, env)
    | .const (.integer ic) => do return (← ofInt t (Silmaril.Compile.Forks.Csem.C.intConstValue ic), env)
    | .const (.floating fc) => do
      let (w, x) ← floatConst fc
      return (← C3.conv (.float w) t x, env)
    | .const c => do return (← C0.constVal c t, env)
    | .annot _ a | .cast _ _ a => do
      let (v, env) ← evalE P n fd a env
      let ta := typeOf a
      if ta.isFloat || t.isFloat then return (← C3.conv ta t v, env)
      return (← convTo t (← convTo ta v), env)
    | .unary op a => do
      match op with
      | .plus => let (v, env) ← evalE P n fd a env; return (← C3.conv (typeOf a) t v, env)
      | .minus =>
        let (v, env) ← evalE P n fd a env
        match t with
        | .float w => return (C3.F.neg w (← C3.conv (typeOf a) t v).toNat, env)
        | _ =>
          let (w, s) ← shape t
          return (← C1.arith .sub w s 0 (← convTo t v), env)
      | .bnot =>
        let (v, env) ← evalE P n fd a env
        let (w, s) ← shape t
        return (wrap w s (-(← convTo t v) - 1), env)
      | .address =>
        if isFunction a then evalF P n fd a env else do
          let (pl, env) ← evalL P n fd a env
          return (← pl.addr, env)
      | .postfixIncr | .postfixDecr =>
        let (pl, env) ← evalL P n fd a env
        let ta := typeOf a
        let old ← readPlace fd env ta pl
        let r ← match ta with
          | .ptr _ => do
            let k ← P.pointee ta
            pure (wrap 8 false (if op == .postfixIncr then old + k else old - k))
          | .float w =>
            C3.F.arith w (if op == .postfixIncr then .add else .sub) old.toNat
              (FloatConst.ofInt w 1)
          | _ => do
            let (w, s) := usual (← shape ta) (4, true)
            convTo ta (← C1.arith (if op == .postfixIncr then .add else .sub) w s (wrap w s old) 1)
        return (old, ← writePlace env ta r pl)
      | .indirection => .error (.unsupported "an indirection outside an lvalue")
    | .binary a op b => do
      match op with
      | .arithmetic aop =>
        let (va, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        let ta := typeOf a
        let tb := typeOf b
        match t, ta, tb with
        | .ptr _, .ptr _, _ =>
          let k ← P.pointee ta
          return (wrap 8 false (if aop == .sub then va - vb * k else va + vb * k), env)
        | .ptr _, _, .ptr _ =>
          let k ← P.pointee tb
          return (wrap 8 false (va * k + vb), env)
        | _, .ptr _, .ptr _ =>
          let k ← P.pointee ta
          return (← convTo t ((va - vb).tdiv k), env)
        | .float w, _, _ =>
          let ca ← C3.conv ta t va
          let cb ← C3.conv tb t vb
          return (← C3.F.arith w aop ca.toNat cb.toNat, env)
        | _, _, _ =>
          let (w, s) ← shape t
          let ca ← convTo t va
          let cb ← if aop == .shl || aop == .shr then pure vb else convTo t vb
          return (← C1.arith aop w s ca cb, env)
      | .comma =>
        let env ← evalD P n fd a env
        let (vb, env) ← evalE P n fd b env
        return (← C3.conv (typeOf b) t vb, env)
      | .and | .or =>
        let (va, env) ← evalE P n fd a env
        if (op == .and) == !(truthOf (typeOf a) va) then return (if op == .and then 0 else 1, env)
        let (vb, env) ← evalE P n fd b env
        return (if truthOf (typeOf b) vb then 1 else 0, env)
      | _ =>
        let (va, env) ← evalE P n fd a env
        let (vb, env) ← evalE P n fd b env
        let ta := typeOf a
        let tb := typeOf b
        if ta matches .ptr _ || tb matches .ptr _ then
          let some r := C0.compare op (wrap 8 false va) (wrap 8 false vb)
            | .error (.unsupported "a binary operator")
          return (if r then 1 else 0, env)
        let u ← usualOf ta tb
        let ca ← C3.conv ta u va
        let cb ← C3.conv tb u vb
        let r := match u with
          | .float w => C3.F.compareOp op w ca.toNat cb.toNat
          | _ => C0.compare op ca cb
        let some r := r | .error (.unsupported "a binary operator")
        return (if r then 1 else 0, env)
    | .assign l r => do
      let (v, env) ← evalE P n fd r env
      let (pl, env) ← evalL P n fd l env
      let v ← C3.conv (typeOf r) (typeOf l) v
      return (v, ← writePlace env (typeOf l) v pl)
    | .compoundAssign l aop r => do
      let (vr, env) ← evalE P n fd r env
      let (pl, env) ← evalL P n fd l env
      let tl := typeOf l
      let tr := typeOf r
      let old ← readPlace fd env tl pl
      let res ← match tl, floatCommon tl tr with
        | .ptr _, _ => do
          let k ← P.pointee tl
          pure (wrap 8 false (if aop == .sub then old - vr * k else old + vr * k))
        | _, some u@(.float w) => do
          let x ← C3.F.arith w aop (← C3.conv tl u old).toNat (← C3.conv tr u vr).toNat
          C3.conv u tl x
        | _, _ => do
          let (w, s) ← if aop == .shl || aop == .shr then pure (promote (← shape tl))
            else pure (usual (← shape tl) (← shape tr))
          let cr := if aop == .shl || aop == .shr then vr else wrap w s vr
          convTo tl (← C1.arith aop w s (wrap w s old) cr)
      return (res, ← writePlace env tl res pl)
    | .cond c a b => do
      let (vc, env) ← evalE P n fd c env
      if truthOf (typeOf c) vc then
        match a with
        | some a => let (v, env) ← evalE P n fd a env; return (← C3.conv (typeOf a) t v, env)
        | none => return (← C3.conv (typeOf c) t vc, env)
      else
        let (v, env) ← evalE P n fd b env
        return (← C3.conv (typeOf b) t v, env)
    | .call f args => do
      let (target, env) ← evalE P n fd f env
      let g ← P.resolve target
      let pts ← callTypes f
      let (vs, env) ← evalArgs P n fd pts args env
      let (v, env) ← callFn P n g vs env
      match v with
      | .scalar v => return (← if t.isFloat then pure v else convTo t v, env)
      | .agg _ => .error (.unsupported "an aggregate result in a scalar position")
    | .assert a => do
      let (v, env) ← evalE P n fd a env
      if !truthOf (typeOf a) v then .error (.abort env.out) else return (0, env)
    | .sizeof _ ty => do return ((← P.sizeAlign ty).1, env)
    | .alignof _ ty => do return ((← P.sizeAlign ty).2, env)
    | .offsetof ty m => do return ((← P.member ty m).1, env)
    | .sizeofExpr a => do
      match a.annotation with
      | .lvalue _ ty _ => return ((← P.sizeAlign ty).1, env)
      | .rvalue _ =>
        match aggOf (typeOf a) with
        | some ty => return ((← P.sizeAlign ty).1, env)
        | none =>
          let some w := C3.width (typeOf a) | .error (.unsupported "sizeof of an expression")
          return (w, env)
    | .generic _ (some i) assocs =>
      match assocs[i]? with
      | some (.type_ _ _ a) | some (.default a) => do
        let (v, env) ← evalE P n fd a env
        return (← C3.conv (typeOf a) t v, env)
      | none => .error (.unsupported "_Generic without selection")
    | _ => .error (.unsupported "an expression outside the fragment")

/-- Evaluate arguments left to right, with prototype conversions and default promotions.
Aggregate values are immutable snapshots, including their uninitialised bytes. -/
def evalArgs (P : Prog) : Nat → FunDef → List CType → List TypedExpression → Env →
    Except Stop (List Arg × Env)
  | 0, _, _, _, _ => .error .outOfFuel
  | _ + 1, _, _, [], env => .ok ([], env)
  | n + 1, fd, pts, a :: as, env => do
    let ta := typeOf a
    let (arg, env) ← match aggOf ta with
      | some _ => do
        let (v, env) ← evalA P n fd a env
        pure (Arg.mk (pts.headD ta) (.agg v), env)
      | none => do
        let (v, env) ← evalE P n fd a env
        let pt ← match pts, ta with
          | pt :: _, _ => pure pt
          | [], .ptr _ => pure ta
          | [], .float _ => pure (.float 8)
          | [], _ => do let (w, s) := promote (← shape ta); pure (.int w s)
        pure (Arg.mk pt (.scalar (← C3.conv ta pt v)), env)
    let (vs, env) ← evalArgs P n fd pts.tail as env
    return (arg :: vs, env)

/-- Write the object of type `ty` at `a` from its initializer `init`. -/
def initAt (P : Prog) : Nat → FunDef → Nat → Ctype → TypedExpression → Env → Except Stop Env
  | 0, _, _, _, _, _ => .error .outOfFuel
  | n + 1, fd, a, ty, init, env =>
    match ty with
    | .mk _ (.array et _) => do
      let (size, _) ← P.sizeAlign ty
      let mut env ← env.withMem (·.writeBytes a (Array.replicate size 0))
      match init.node with
      | .array _ _ elems =>
        let (esize, _) ← P.sizeAlign et
        for (el, i) in elems.zipIdx do
          if let some x := el then
            if (i + 1) * esize > size then throw (.unsupported "an initializer too long")
            env ← initAt P n fd (a + i * esize) et x env
        return env
      | .str s =>
        let bs := (Silmaril.Compile.Forks.Csem.C.stringBytes s).toList.take size
        env.withMem (·.writeBytes a bs.toArray)
      | .const c => env.withMem (writeConst P · a ty c)
      | _ => .error (.unsupported "an array initializer outside the fragment")
    | .mk _ (.struct _) | .mk _ (.union _) => do
      let (size, _) ← P.sizeAlign ty
      match init.node with
      | .struct _ ms =>
        let mut env ← env.withMem (·.writeBytes a (Array.replicate size 0))
        for (x, el) in ms do
          if let some el := el then
            let (off, mty) ← P.member ty x
            env ← initAt P n fd (a + off) mty el env
        return env
      | .union _ x el =>
        let env ← env.withMem (·.writeBytes a (Array.replicate size 0))
        match el with
        | some el =>
          let (off, mty) ← P.member ty x
          initAt P n fd (a + off) mty el env
        | none => return env
      | .const c =>
        let env ← env.withMem (·.writeBytes a (Array.replicate size 0))
        env.withMem (writeConst P · a ty c)
      | _ =>
        let (v, env) ← evalA P n fd init env
        env.withMem (writeAgg · a v)
    | _ => do
      let t := ofCtype ty
      let (v, env) ← evalE P n fd init env
      let v ← C3.conv (typeOf init) t v
      env.withMem (storeV · t a v)

/-- Call the function `g` on argument values (already converted to its parameter types). -/
def callFn (P : Prog) : Nat → Sym → List Arg → Env → Except Stop (Val × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, g, vs, env =>
    match P.funcs[g.number]? with
    | none => do
      if vs.any (fun a => a.ty.isFloat) && (C3.F.libm (P.name g)).isNone then
        throw (.unsupported "a floating argument of an external function")
      let ints ← vs.mapM fun a => match a.val with
        | .scalar v => pure v
        | .agg _ => throw (.unsupported "an aggregate argument of an external function")
      match C3.F.libm (P.name g), ints with
      | some (_, f), [x] => return (.scalar (f x.toNat), env)
      | _, _ =>
        let (v, env) ← external (P.name g) ints env
        return (.scalar v, env)
    | some fd => do
      if vs.length < fd.params.length ||
          (!P.variadics.contains g.number && fd.params.length != vs.length) then
        .error (.unsupported s!"call of {P.name g} with {vs.length} arguments")
      let sp := env.mem.sp
      let activation := env.nextActivation
      let mut mem := env.mem
      let mut frame : Std.HashMap Nat Nat := {}
      for (x, ty) in fd.memLocals do
        let (size, align) ← P.sizeAlign ty
        let (a, m) ← mem.alloc size align
        mem := m
        frame := frame.insert x a
      let mut regs : Std.HashMap Nat Int := {}
      for ((x, pt), v) in fd.params.zip vs do
        match v.val, frame[x]? with
        | .agg v, some a => mem ← writeAgg mem a v
        | .agg _, none => throw (.unsupported "an aggregate parameter outside memory")
        | .scalar v, some a => mem ← storeV mem pt a (← C3.conv pt pt v)
        | .scalar v, none => regs := regs.insert x (← C3.conv pt pt v)
      let callee : Env := { env with
        regs := regs
        frame := frame
        mem := mem
        activation := activation
        nextActivation := activation + 1
        extra := if P.variadics.contains g.number then some (vs.drop fd.params.length) else none
        lastParam := fd.params.getLast?.map (·.1) }
      let (r, e) ← loop P n fd (some fd.body) .stop callee
      let r ← match aggOf fd.ret, r with
        | some _, some (.agg v) => pure (Val.agg v)
        | some ty, _ => do
          -- a struct function that ends without `return`: an indeterminate value
          let (size, _) ← P.sizeAlign ty
          pure (Val.agg ⟨ByteArray.mk (Array.replicate size 0), ByteArray.mk (Array.replicate size 0)⟩)
        | none, some (.agg _) => throw (.unsupported "an aggregate result of a scalar function")
        | none, r => pure (Val.scalar (← C3.conv fd.ret fd.ret ((r.map Val.int).getD 0)))
      let e := e.expire activation
      return (r, { e with
        regs := env.regs
        frame := env.frame
        mem := { e.mem with sp }
        extra := env.extra
        lastParam := env.lastParam
        activation := env.activation })

/-- Run the statement machine of one activation to its return. -/
def loop (P : Prog) : Nat → FunDef → Option TypedStatement → Kont → Env →
    Except Stop ((Option Val) × Env)
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
      return (if truthOf (typeOf c) v then .running (some b) k else .running none k', env)
    | .do_ b c k' => do
      let (v, env) ← evalE P n fd c env
      return (if truthOf (typeOf c) v then .running (some b) k else .running none k', env)
    | .switch k => .ok (.running none k, env)
  | n + 1, fd, some s, k, env =>
    match s.node with
    | .skip => .ok (.running none k, env)
    | .expr e => do let env ← evalD P n fd e env; return (.running none k, env)
    | .block _ ss => .ok (.running none (.seq ss k), env)
    | .declaration ds => do
      let mut env := env
      for (x, init) in ds do
        match env.frame[x.number]?, init with
        | some a, some e =>
          let ty := ((fd.memLocals.find? (·.1 == x.number)).map (·.2)).getD (.mk [] .void)
          env ← initAt P n fd a ty e env
        | some a, none =>
          let ty := ((fd.memLocals.find? (·.1 == x.number)).map (·.2)).getD (.mk [] .void)
          let (size, _) ← P.sizeAlign ty
          env ← env.withMem (fun m => .ok (m.clear a size))
        | none, some e =>
          if !fd.locals.contains x.number then continue
          let (v, env') ← evalE P n fd e env
          let v ← C3.conv (typeOf e) ((fd.locals[x.number]?).getD (typeOf e)) v
          env := env'.setReg x.number v
        | none, none =>
          env := { env with regs := env.regs.erase x.number }
      return (.running none k, env)
    | .if_ c a b => do
      let (v, env) ← evalE P n fd c env
      return (.running (some (if truthOf (typeOf c) v then a else b)) k, env)
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
      match aggOf fd.ret with
      | some _ =>
        let (v, env) ← evalA P n fd e env
        return (.returned (some (.agg v)), env)
      | none =>
        let (v, env) ← evalE P n fd e env
        return (.returned (some (.scalar (← C3.conv (typeOf e) fd.ret v))), env)
    | .switch e body => do
      let (v, env) ← evalE P n fd e env
      let (w, sg) := promote (← shape (typeOf e))
      let v := wrap w sg v
      match C0.findCase (C0.caseMatches w sg v) body (.switch k) with
      | some (s', k') => return (.running (some s') k', env)
      | none =>
        match C0.findCase (fun c => c.isNone) body (.switch k) with
        | some (s', k') => return (.running (some s') k', env)
        | none => return (.running none k, env)
    | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b =>
      .ok (.running (some b) k, env)
    | .goto l =>
      match C0.findLabel l.number fd.body .stop with
      | some (s', k') => .ok (.running (some s') k', env)
      | none => .error (.unsupported s!"goto an unknown label {Silmaril.Compile.Forks.Csem.C.symName l}")
    | _ => .error (.unsupported "a statement outside the fragment")
end

/-! ## Whole programs -/

/-- The initial memory: string literals, objects of static storage duration (zeroed, then
written from their initializers in declaration order) and `argv`. -/
def initMemory (P : Prog) (fuel : Nat) : Except Stop Env := do
  let size := P.top - base
  let mut mem : Memory :=
    { bytes := ByteArray.mk (Array.replicate size 0), init := ByteArray.mk (Array.replicate size 1),
      roTop := base, sp := P.top }
  for (l, a) in P.strs.toList do
    mem ← mem.writeBytes a l.toArray
  mem := { mem with roTop := P.roTop }
  -- argv[0] = "" (at argv + 16), argv[1] = NULL
  mem ← mem.writeBytes P.argv (C1.Memory.le 8 (P.argv + 16))
  let mut env : Env := { mem }
  let mut done : Std.HashSet Nat := {}
  for (x, ty, init) in P.statics do
    if done.contains x then continue
    let (some a, some e) := (P.gaddr[x]?, init) | continue
    done := done.insert x
    -- objects of types outside the fragment are left zero (`check` rejects their uses)
    if !P.obj ty then continue
    env ← initAt P fuel C1.topFrame a ty e env
  return env

/-- **The C4 interpreter.** Run `main` with `fuel`. -/
def run (fuel : Nat) (p : TypedProgram) : Result :=
  let P := prepare p
  let r : Except Stop (Val × Env) := do
    let env ← initMemory P fuel
    let some ms := p.1 | .error (.unsupported "no main")
    let some fd := P.funcs[ms.number]? | .error (.unsupported "main is not defined")
    let args : List Arg := fd.params.zipIdx.map fun ((_, ty), i) =>
      ⟨ty, .scalar (if i == 0 then 1 else if i == 1 then (P.argv : Int) else 0)⟩
    callFn P (fuel + 1) ms args env
  match r with
  | .ok (v, env) => .done ⟨env.out.toList, C0.toStatus v.int⟩
  | .error (.exit c out) => .done ⟨out.toList, C0.toStatus c⟩
  | .error (.abort out) => .done ⟨out.toList, .signal 6⟩
  | .error (.undefined why) => .undefined why
  | .error .outOfFuel => .outOfFuel
  | .error (.unsupported why) => .unsupported why

/-! ## Behaviours and the language -/

/-- The behaviours of a program under C4, as for C0 (`C0.beh`). -/
def beh (p : TypedProgram) : Set Obs := {o |
  (∃ n, run n p = .done o) ∨ (∃ n why, run n p = .undefined why) ∨
    (o = ⟨[], .diverges⟩ ∧ ∀ n, run n p = .outOfFuel)}

/-- C4 as a semantics of C. -/
def sem : Semantics := beh

/-- C4 as a language of the zoo. -/
def lang : Language.{0} := cSyntax.lang sem

theorem beh_of_done {p : TypedProgram} {n : Nat} {o : Obs} (h : run n p = .done o) :
    o ∈ beh p := .inl ⟨n, h⟩

/-- Undefined behaviour allows every behaviour. -/
theorem beh_of_undefined {p : TypedProgram} {n : Nat} {why : String}
    (h : run n p = .undefined why) : beh p = Set.univ :=
  Set.eq_univ_of_forall fun _ => .inr (.inl ⟨n, why, h⟩)

/-! ## The fragment -/

/-- Is `t` the type of a scalar value of C4 (or `void`)? -/
def Prog.valueType (P : Prog) : CType → Bool
  | .int .. | .bool | .void | .float _ => true
  | .ptr t => C4.pointee P.layout depth t
  | _ => false

/-- Is `t` a struct or union type of C4? -/
def Prog.aggType (P : Prog) (t : CType) : Bool :=
  match aggOf t with
  | some ty => P.obj ty
  | none => false

/-- The member `m` of the struct or union type `ty`, for the checker. -/
def Prog.memberS (P : Prog) (ty : Ctype) (m : Identifier) : Except String (Nat × Ctype) :=
  match P.member ty m with
  | .ok r => .ok r
  | .error _ => .error s!"no member {m.name} in a struct or union of C4"

/-- Does `t` have a layout in C4 (for `sizeof` and `_Alignof`)? -/
def Prog.sized (P : Prog) (ty : Ctype) : Except String Unit :=
  match P.sizeAlign ty with
  | .ok _ => pure ()
  | .error _ => throw "sizeof of a type outside C4"

/-- Is a floating constant in C4 (not `long double`, and well formed)? -/
def checkFloat (fc : FloatingConstant) : Except String Unit :=
  match floatConst fc with
  | .ok _ => pure ()
  | .error _ => throw "a floating constant outside C4"

/-- Calls use the static prototype; direct external calls additionally check C3's
library boundary. Address-taking checks also prevent indirect unsupported externals. -/
def checkCallShape (P : Prog) (f : TypedExpression) (args : List TypedExpression) :
    Except String Unit := do
  match callTypes f with
  | .error _ => throw "call of a non-function"
  | .ok _ => pure ()
  match f.node with
  | .functionDecay ⟨_, _, _, .ident g⟩ =>
    if !P.funcs.contains g.number then C3.checkCall P.toC3 f args
  | _ => pure ()

mutual
/-- Check a function designator, including the targets whose addresses escape. -/
def checkF (P : Prog) : TypedExpression → Except String Unit
  | .mk _ _ _ node => do
  match node with
  | .ident g =>
    if !P.symbols.contains g.number then throw "an undeclared function designator"
    if !P.funcs.contains g.number && !(externals.contains (P.name g)) &&
        (C3.F.libm (P.name g)).isNone then throw s!"address of the external function {P.name g}"
  | .unary .indirection p => checkE P p
  | .annot _ a => checkF P a
  | _ => throw "a function designator outside C4"

/-- Check that an rvalue is in the fragment. -/
def checkE (P : Prog) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue .. => throw "an lvalue in value position"
    | .rvalue g =>
      let t := ofGenType g
      if P.aggType t then checkA P node
      else
        if !P.valueType t then throw "an expression of a type outside C4"
        checkN P node
/-- Check an expression of a struct or union type. -/
def checkA (P : Prog) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a => checkLv P a
  | .vaArg ap _ => checkE P ap
  | .assign l r => do checkLv P l; checkE P r
  | .call f args => do checkCallShape P f args; checkE P f; checkL P args
  | .cond c (some a) b => do checkE P c; checkE P a; checkE P b
  | .binary a .comma b => do checkE P a; checkE P b
  | .annot _ a => checkE P a
  | _ => throw "an aggregate expression outside C4"
def checkN (P : Prog) : ExpressionNode GenTypeCategory → Except String Unit
  | .rvalue a | .arrayDecay a => checkLv P a
  | .functionDecay a => checkF P a
  | .vaStart _ _ => pure ()
  | .vaArg a _ | .vaEnd a => checkE P a
  | .vaCopy _ b => checkE P b
  | .const c =>
    match c with
    | .integer _ | .character _ | .predefined _ | .null => pure ()
    | .floating fc => checkFloat fc
    | _ => throw "a constant outside C4"
  | .annot _ a | .cast _ _ a | .assert a => checkE P a
  | .unary op a =>
    match op with
    | .plus | .minus | .bnot => checkE P a
    | .address => if isFunction a then checkF P a else checkLv P a
    | .postfixIncr | .postfixDecr => checkLv P a
    | .indirection => throw "an indirection outside an lvalue"
  | .binary a _ b => do checkE P a; checkE P b
  | .assign l r | .compoundAssign l _ r => do checkLv P l; checkE P r
  | .cond c a b => do
    checkE P c
    match a with
    | some a => checkE P a
    | none => pure ()
    checkE P b
  | .call f args => do checkCallShape P f args; checkE P f; checkL P args
  | .sizeof _ ty | .alignof _ ty => P.sized ty
  | .offsetof ty m => do let _ ← P.memberS ty m
  | .sizeofExpr _ => pure ()
  | .generic _ (some _) assocs => checkG P assocs
  | _ => throw "an expression outside the fragment"
/-- Check that an lvalue is in the fragment. -/
def checkLv (P : Prog) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue _ ty _ => if !P.obj ty then throw "an object of a type outside C4"
    | .rvalue _ => throw "an rvalue in lvalue position"
    match node with
    | .ident _ => pure ()
    | .unary .indirection p => checkE P p
    | .memberof a _ => checkLv P a
    | .memberofptr p _ => do
      checkE P p
      match typeOf p with
      | .ptr sty => if !P.obj sty then throw "a member of an incomplete struct or union"
      | _ => throw "a member through a non-pointer"
    | .str s => if !plainString s then throw "a wide string literal"
    | .annot _ a => checkLv P a
    | _ => throw "an lvalue outside C4"
def checkL (P : Prog) : List TypedExpression → Except String Unit
  | [] => pure ()
  | e :: es => do checkE P e; checkL P es
def checkG (P : Prog) : List (GenericAssociation GenTypeCategory) → Except String Unit
  | [] => pure ()
  | .type_ _ _ e :: gs | .default e :: gs => do checkE P e; checkG P gs
end

mutual
/-- Check an aggregate constant. -/
def checkC : Constant → Except String Unit
  | .array _ cs => checkCs cs
  | .struct _ ms => checkCm ms
  | .union _ _ c => checkC c
  | .integer _ | .character _ | .predefined _ | .null | .indeterminate _ => pure ()
  | .floating fc => checkFloat fc
def checkCs : List Constant → Except String Unit
  | [] => pure ()
  | c :: cs => do checkC c; checkCs cs
def checkCm : List (Identifier × Constant) → Except String Unit
  | [] => pure ()
  | (_, c) :: cs => do checkC c; checkCm cs
end

/-- Check an initializer of an object of type `ty` (`n` bounds the nesting). -/
def checkI (P : Prog) : Nat → Ctype → TypedExpression → Except String Unit
  | 0, _, _ => throw "an initializer nested too deeply"
  | n + 1, ty, e@(.mk _ _ _ node) =>
    match ty with
    | .mk _ (.array et _) =>
      match node with
      | .array _ _ elems => elems.forM fun
        | some x => checkI P n et x
        | none => pure ()
      | .str s => if plainString s then pure () else throw "a wide string literal"
      | .const c => checkC c
      | _ => throw "an array initializer outside C4"
    | .mk _ (.struct _) | .mk _ (.union _) =>
      match node with
      | .struct _ ms => ms.forM fun
        | (m, some x) => do checkI P n (← P.memberS ty m).2 x
        | (_, none) => pure ()
      | .union _ m (some x) => do checkI P n (← P.memberS ty m).2 x
      | .union _ _ none => pure ()
      | .const c => checkC c
      | _ => checkE P e
    | _ => do
      if !P.valueType (ofCtype ty) then throw "an initializer of an object without values in C4"
      checkE P e

/-- The locals of a statement have types of C4. -/
def checkLocals (P : Prog) (bs : Bindings) : Except String Unit := do
  for (x, (_, _, _, ty)) in bs do
    if !P.obj ty then throw s!"local {Silmaril.Compile.Forks.Csem.C.symName x} of a type outside C4"

mutual
def checkS (P : Prog) (fd : FunDef) : TypedStatement → Except String Unit
  | .mk _ _ _ node => checkSN P fd node
def checkSN (P : Prog) (fd : FunDef) : StatementNode GenTypeCategory → Except String Unit
  | .skip | .break_ | .continue_ | .returnVoid | .goto _ => pure ()
  | .expr e | .return_ e => checkE P e
  | .block bs ss => do checkLocals P bs; checkSL P fd ss
  | .if_ c a b => do checkE P c; checkS P fd a; checkS P fd b
  | .while_ c b _ | .do_ b c _ => do checkE P c; checkS P fd b
  | .switch e b => do checkE P e; checkS P fd b
  | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => checkS P fd b
  | .declaration ds => checkD P fd ds
  | _ => throw "a statement outside the fragment"
def checkSL (P : Prog) (fd : FunDef) : List TypedStatement → Except String Unit
  | [] => pure ()
  | s :: ss => do checkS P fd s; checkSL P fd ss
def checkD (P : Prog) (fd : FunDef) : List (Sym × Option TypedExpression) → Except String Unit
  | [] => pure ()
  | (x, some e) :: ds => do
    match fd.memLocals.find? (·.1 == x.number) with
    | some (_, ty) => checkI P depth ty e
    | none => checkE P e
    checkD P fd ds
  | (_, none) :: ds => checkD P fd ds
end

mutual
/-- Function references in an expression, including addresses and variadic operands. -/
def callsE : TypedExpression → List Nat
  | .mk _ _ _ node => callsN node
def callsN : ExpressionNode GenTypeCategory → List Nat
  | .ident x => [x.number]
  | .call f args =>
    (match f.node with
      | .functionDecay ⟨_, _, _, .ident g⟩ => [g.number]
      | _ => callsE f) ++ callsL args
  | .unary _ a | .annot _ a | .cast _ _ a | .assert a | .rvalue a | .sizeofExpr a
  | .functionDecay a | .arrayDecay a | .memberof a _ | .memberofptr a _
  | .vaStart a _ | .vaArg a _ | .vaEnd a => callsE a
  | .binary a _ b | .assign a b | .compoundAssign a _ b | .vaCopy a b => callsE a ++ callsE b
  | .cond c a b => callsE c ++ (match a with | some a => callsE a | none => []) ++ callsE b
  | .array _ _ es => callsO es
  | .struct _ ms => callsM ms
  | .union _ _ (some e) => callsE e
  | .generic _ _ gs => callsG gs
  | _ => []
def callsL : List TypedExpression → List Nat
  | [] => []
  | e :: es => callsE e ++ callsL es
def callsO : List (Option TypedExpression) → List Nat
  | [] => []
  | none :: es => callsO es
  | some e :: es => callsE e ++ callsO es
def callsM : List (Identifier × Option TypedExpression) → List Nat
  | [] => []
  | (_, none) :: es => callsM es
  | (_, some e) :: es => callsE e ++ callsM es
def callsG : List (GenericAssociation GenTypeCategory) → List Nat
  | [] => []
  | .type_ _ _ e :: gs | .default e :: gs => callsE e ++ callsG gs
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

/-- Is the program in the C4 fragment? The reason when it is not. Only the functions reachable
from `main` are checked, and the initializers of the objects of static storage duration whose
type is in C4 (the others are left zero, and their uses are rejected where they occur). -/
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
          throw s!"a function with a result outside C4: {Silmaril.Compile.Forks.Csem.C.symName x}"
        if ps.any fun (_, t, _) =>
            !P.obj t || !((C3.width (ofCtype t)).isSome || P.aggType (ofCtype t)) then
          throw s!"a function with a parameter outside C4: {Silmaril.Compile.Forks.Csem.C.symName x}"
    | .object .. => pure ()
  for (_, ty, init) in P.statics do
    if P.obj ty then
      if let some e := init then checkI P depth ty e
  for f in live do
    if let some fd := P.funcs[f]? then checkS P fd fd.body

/-- The C4 fragment. -/
def InFragment (p : TypedProgram) : Prop := check p = .ok ()

instance (p : TypedProgram) : Decidable (InFragment p) :=
  inferInstanceAs (Decidable (check p = .ok ()))

/-- The fragment as a set of programs. -/
def fragment : Set TypedProgram := {p | InFragment p}

end Silmaril.Compile.C.Sem.C4
