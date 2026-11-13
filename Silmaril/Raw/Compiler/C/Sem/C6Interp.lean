module

public import Silmaril.Compiler.C.Sem.C6Prepare.Defs
/-!
# The extended C6 evaluator

The fuel-recursive statement machine follows C5's evaluator, reusing its heap, library and
scalar operations by import. Added cases implement compound objects, GNU block values and
members of aggregate snapshots. `C6.run` in `C6.lean` uses this evaluator outside C5's fragment.
-/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C6

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C
open C0 (Stop ub Kont Result)
open C1 (Memory Place FunDef wrap convTo shape store base externals plainString)
open C2 (Agg Val Next aggOf lvType readAgg writeAgg depth)
open C3 (ofInt truthOf floatConst storeV layoutOf sizeAlignOf)
open C4 (Arg Cursor Prog codeAddress callTypes vaCompatible writeConst usualOf isFunction)

/-- C5's state and heap, plus the literal slots of the current activation. -/
structure Env extends toC5 : C5.Env where
  literals : Std.HashMap Nat Nat := {}

@[inline] def Env.withMem (env : Env) (f : Memory → Except Stop Memory) : Except Stop Env := do
  return { env with mem := ← f env.mem }
@[inline] def Env.setReg (env : Env) (x : Nat) (v : Int) : Env :=
  { env with regs := env.regs.insert x v }
def Env.newCursor (env : Env) (c : Cursor) : Except Stop (Int × Env) := do
  let (h, e) ← env.toC5.newCursor c
  return (h, { env with toC5 := e })
def Env.takeArg (env : Env) (h : Int) : Except Stop (Arg × Env) := do
  let (a, e) ← env.toC5.takeArg h
  return (a, { env with toC5 := e })
def Env.expire (env : Env) (activation : Nat) : Env :=
  { env with toC5 := env.toC5.expire activation }
def Env.access (env : Env) (a n : Nat) : Except Stop Unit := env.toC5.access a n

def readPlace (fd : FunDef) (env : Env) (t : CType) (pl : Place) : Except Stop Int :=
  C5.readPlace fd env.toC5 t pl
def writePlace (env : Env) (t : CType) (v : Int) (pl : Place) : Except Stop Env := do
  return { env with toC5 := ← C5.writePlace env.toC5 t v pl }
def external (name : String) (args : List Int) (env : Env) : Except Stop (Int × Env) := do
  let (v, e) ← C5.external name args env.toC5
  return (v, { env with toC5 := e })

/-- Extract an aggregate member without inventing a temporary object address. Its byte
initialisation is retained; scalar loads below detect indeterminate member bytes. -/
def memberValue (P : Prog) (a : TypedExpression) (m : Identifier) (v : Agg) : Except Stop Agg := do
  let some ty := aggOf (typeOf a) | throw (.unsupported "a member of a non-aggregate value")
  let (off, mt) ← P.member ty m
  let (size, _) ← P.sizeAlign mt
  if off + size > v.bytes.size then ub "a member outside its aggregate value"
  return ⟨v.bytes.extract off (off + size), v.init.extract off (off + size)⟩

/-- Decode a scalar snapshot with C3's scalar load (including float representation). -/
def scalarValue (t : CType) (v : Agg) : Except Stop Int :=
  C3.load { bytes := v.bytes, init := v.init, roTop := base, sp := base + v.bytes.size } t base

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
    | _ => .error (.unsupported "a function designator outside C6")

/-- The place an lvalue designates. -/
def evalL (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Place × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, e, env =>
    match e.node with
    | .compound _ ty init => do
      let .mk _ [.marker id] _ _ := e | throw (.unsupported "an unprepared compound literal")
      let (a, env) ← match env.literals[id]? with
        | some a => pure (a, env)
        | none => do
          let (size, align) ← P.sizeAlign ty
          let (a, mem) ← env.mem.alloc size align
          pure (a, { env with mem, literals := env.literals.insert id a })
      let env ← initAt P n fd a ty init env
      return (.mem a, env)
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
    | .gccStatement _ ss => do
      let (v, env) ← evalSE P n fd ss env
      match v with
      | .agg v => return (v, env)
      | .scalar _ => throw (.unsupported "a scalar statement expression in aggregate position")
    | .memberof a m => do
      let (v, env) ← evalObject P n fd a env
      return (← memberValue P a m v, env)
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
      env.access b size
      return (← readAgg env.mem b size, env)
    | .assign l r => do
      let (v, env) ← evalA P n fd r env
      let (pl, env) ← evalL P n fd l env
      let b ← pl.addr
      env.access b v.bytes.size
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
    | _ => .error (.unsupported "an aggregate expression outside C6")

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
    | .gccStatement _ ss => do
      let (v, env) ← evalSE P n fd ss env
      match v with
      | .scalar v => return (v, env)
      | .agg _ => throw (.unsupported "an aggregate statement expression in scalar position")
    | .memberof a m => do
      let (v, env) ← evalObject P n fd a env
      return (← scalarValue t (← memberValue P a m v), env)
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

/-- Read an aggregate object or use an aggregate value, as required by member selection. -/
def evalObject (P : Prog) : Nat → FunDef → TypedExpression → Env → Except Stop (Agg × Env)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, fd, a, env =>
    match a.annotation with
    | .rvalue _ => evalA P n fd a env
    | .lvalue _ ty _ => do
      let (pl, env) ← evalL P n fd a env
      let b ← pl.addr
      let (size, _) ← P.sizeAlign ty
      env.access b size
      return (← readAgg env.mem b size, env)

/-- Evaluate a GNU statement-expression block. Prefix statements run on their own
continuation; the final expression is evaluated exactly once and copied as a value. -/
def evalSE (P : Prog) : Nat → FunDef → List TypedStatement → Env → Except Stop (Val × Env)
  | 0, _, _, _ => .error .outOfFuel
  | _ + 1, _, [], env => .ok (.scalar 0, env)
  | n + 1, fd, [s], env =>
    match s.node with
    | .expr e =>
      match aggOf (typeOf e) with
      | some _ => do
        let (v, env) ← evalA P n fd e env
        return (.agg v, env)
      | none => do
        let (v, env) ← evalE P n fd e env
        return (.scalar v, env)
    | _ => do
      let (_, env) ← loop P n fd (some s) .stop env
      return (.scalar 0, env)
  | n + 1, fd, s :: ss, env => do
    let (_, env) ← loop P n fd (some s) .stop env
    evalSE P n fd ss env

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
        literals := {}
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
        literals := env.literals
        regs := env.regs
        frame := env.frame
        mem := { e.mem with sp := max sp e.heapTop }
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

/-- Run `main` with the extended C6 evaluator and `fuel`. -/
def runExtended (fuel : Nat) (p : TypedProgram) : Result :=
  let r : Except Stop (Val × Env) := do
    let P ← prepareProgram p
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


end Silmaril.Compile.C.Sem.C6
