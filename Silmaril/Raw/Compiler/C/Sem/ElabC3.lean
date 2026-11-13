module

public import Silmaril.Compiler.C.Sem.C3Mono.Defs
public import Silmaril.Compiler.C.Sem.ElabC2.Defs
@[expose] public section

/-!
# Checked structural C3 elaboration

`ElabC2`'s translation, extended to C3's real floating types. A `float` or `double` object
is a typed Core floating object. Floating constants, `+ - * /`, unary `-`, `++`/`--`,
compound assignment, comparisons and floating conditions are Core's floating operations;
conversions from integers use `fvFromInt`, and conversions to integers use `ivFromFloat`
with C3's destination-range check (an out-of-range value is `UB017`). `fabs`, `floor`,
`ceil`, `trunc` and their `float` versions are Core floating expressions (`libm`); `sqrt`
and other library calls decline, as do unions, arrays and pointer arithmetic (see
`ElabC2`). `sizeof`, `_Alignof` and `offsetof` use C3's layout (`float` is 4 bytes).

Frozen Core has one floating format: every real floating type is binary64. A `double`
computation is therefore C3's, but a `float` one is computed without binary32 rounding.
Acceptance compares a completed C3 run with an exact, terminating Core run, so a program
that observes that difference (or any other) declines, and accepted programs have exactly
the same behaviour sets. This is worker-written realisation, not agreement with Cerberus
elaboration.
-/

namespace Silmaril.Compile.C.Sem.ElabC3

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Core (PexprNode ExprNode Pattern BaseType ObjectType)
open Silmaril.Cerberus.Core.Dynamics (PE EE Program)
open ElabC0 (Gen pe ee lit val specified bind seq ptr sourceLabel parameter boolInt action)

/-- A binary64 constant, given by its encoding: Core's only floating format. -/
def flit (bits : Nat) : PE :=
  pe (.val (.object (.floating (Numeric.Ieee754.F64.mk bits.toUInt64))))

/-- Core's real floating type for a C3 floating width. -/
def floatCtype : Nat → Option Ctype
  | 4 => some (.mk [] (.basic (.floating (.realFloating .float))))
  | 8 => some (.mk [] (.basic (.floating (.realFloating .double))))
  | _ => none

/-- Types of the represented Core objects. -/
def objectType : CType → Option ObjectType
  | .float w => do let _ ← floatCtype w; pure .floating
  | t => ElabC2.objectType t

def ctype : CType → Option Ctype
  | .float w => floatCtype w
  | t => ElabC2.ctype t

def returnType : CType → Option BaseType
  | .void => some .unit
  | t => return .loaded (← objectType t)

/-- A value of type `t` as a condition; a floating value is true when it is not a zero. -/
def truth (t : CType) (p : PE) : PE :=
  match t with
  | .float _ => pe (.not (pe (.op .eq p (flit 0))))
  | _ => ElabC0.truth p

/-- Convert a value of type `src` to type `dst`, as `C3.conv`. -/
def conv (src dst : CType) (p : PE) : Option PE := do
  match src, dst with
  | .float _, .float w =>
    let _ ← floatCtype w
    return p
  | .float _, .bool => return boolInt (truth src p)
  | .float _, .int .. =>
    let ty := pe (.val (.ctype (← ElabC0.ctype dst)))
    let n := pe (.ctor .ivFromFloat [ty, p])
    let undef := pe (.undef .unknown .UB017_out_of_range_floating_integer_conversion)
    return pe (.if_ (pe (.op .le (pe (.ctor .ivMin [ty])) n))
      (pe (.if_ (pe (.op .le n (pe (.ctor .ivMax [ty])))) n undef)) undef)
  | .int .., .float w | .bool, .float w =>
    let _ ← floatCtype w
    return pe (.ctor .fvFromInt [p])
  | .float _, _ | _, .float _ => none
  | _, _ => ElabC2.conv dst p

/-- `+ - * /` on floating values of one type. -/
def floatArith (op : ArithmeticOperator) (a b : PE) : Option PE := do
  let cop ← match op with
    | .add => some Silmaril.Cerberus.Core.BinOp.add
    | .sub => some .sub
    | .mul => some .mul
    | .div => some .div
    | _ => none
  return pe (.op cop a b)

/-- `a op b` of type `t`, from operands of types `ta` and `tb`. -/
def arithmetic (op : ArithmeticOperator) (t ta tb : CType) (a b : PE) : Option PE :=
  match t with
  | .float _ => do floatArith op (← conv ta t a) (← conv tb t b)
  | _ => ElabC0.arithmetic op t a b

/-- `x ± 1` for `++` and `--`, stored back into an object of type `t`. -/
def step (op : ArithmeticOperator) (t : CType) (x : PE) : Option PE :=
  match t with
  | .float _ => floatArith op x (flit 0x3ff0000000000000)
  | _ => do
    let .ok u := C0.usualOf t (.int 4 true) | none
    ElabC2.conv t (← ElabC0.arithmetic op u x (lit 1))

/-- `old op= r` for an object of type `tl` and an operand of type `tr`. -/
def compound (op : ArithmeticOperator) (tl tr : CType) (old r : PE) : Option PE :=
  match floatCommon tl tr with
  | some u => do conv u tl (← floatArith op (← conv tl u old) (← conv tr u r))
  | none => do
    let .ok u := C0.usualOf tl (if op == .shl || op == .shr then .int 4 true else tr) | none
    ElabC2.conv tl (← ElabC0.arithmetic op u old r)

/-- C3's exact `<math.h>` functions other than `sqrt` (`C3.F.libm`), from Core's floating
operations: `trunc` keeps the sign of a zero result as `x * 0.0`, and `floor` and `ceil` step
from it. An infinity or a NaN argument is outside Core's `ivFromFloat`, so it declines. -/
def libm (name : String) (x : PE) : Gen EE := do
  let f := match name with
    | "fabsf" => "fabs" | "floorf" => "floor" | "ceilf" => "ceil" | "truncf" => "trunc"
    | f => f
  let zero := flit 0
  let one := flit 0x3ff0000000000000
  if f == "fabs" then
    return val (pe (.if_ (pe (.op .lt x zero)) (pe (.op .mul (flit 0xbff0000000000000) x))
      (pe (.if_ (pe (.op .eq x zero)) zero x))))
  let r ← ElabC0.fresh
  let t ← ElabC0.fresh
  let ty ← ElabC0.ctype (.int 8 true)
  let pr := pe (.sym r)
  let pt := pe (.sym t)
  let result ← match f with
    | "trunc" => pure pt
    | "floor" => pure (pe (.if_ (pe (.op .lt x pt)) (pe (.op .sub pt one)) pt))
    | "ceil" => pure (pe (.if_ (pe (.op .lt pt x)) (pe (.op .add pt one)) pt))
    | _ => failure
  let integral := pe (.ctor .fvFromInt [pe (.ctor .ivFromFloat [pe (.val (.ctype ty)), x])])
  return ee (.sseq (bind (some r) (.object .floating)) (val integral)
    (ee (.sseq (bind (some t) (.object .floating))
      (val (pe (.if_ (pe (.op .eq pr zero)) (pe (.op .mul x zero)) pr))) (val result))))

def loadAt (address : PE) (t : CType) : Gen EE := do
  let ty ← ctype t
  let v ← ElabC0.fresh
  let pat := Pattern.mk [] (.ctor .specified [bind (some v) (.object (← objectType t))])
  return ee (.sseq pat (action (.load (pe (.val (.ctype ty))) address .na))
    (val (pe (.sym v))))

def storeAt (address : PE) (t : CType) (p : PE) : Option EE := do
  let ty ← ctype t
  return action (.store false (pe (.val (.ctype ty))) address (specified p) .na)

/-- Zero-initialisation, including omitted nested struct members. -/
def zeroValue : Nat → Ctype → Mem.Concrete.Tags → Option PE
  | 0, _, _ => none
  | n + 1, ty, tags => do
    match ty with
    | .mk _ (.struct tag) =>
      let some (_, .struct fields none) := tags.lookup tag | none
      return pe (.struct tag (← fields.mapM fun (name, (_, _, _, ty)) => do
        pure (name, ← zeroValue n ty tags)))
    | .mk _ (.basic (.integer _)) => return lit 0
    | .mk _ (.basic (.floating (.realFloating _))) => return flit 0
    | .mk _ (.pointer _ refTy) => return pe (.val (.object (.pointer (.null refTy))))
    | _ => none

def argumentValues (translateE : TypedExpression → Gen EE)
    (pts : List CType) (args : List TypedExpression) (next : List PE → Gen EE) : Gen EE := do
  match args with
  | [] => next []
  | a :: rest =>
    let body ← translateE a
    let x ← ElabC0.fresh
    let p ← conv (typeOf a) (pts.headD (typeOf a)) (pe (.sym x))
    let tail ← argumentValues translateE pts.tail rest (fun ps => next (p :: ps))
    return ee (.sseq (bind (some x) (.object (← objectType (typeOf a)))) body tail)

/-- Expressions return a typed Core object; `sseq` makes operand order explicit. -/
def expression (P : C3.Prog) : Nat → TypedExpression → Gen EE
  | 0, _ => failure
  | n + 1, e => do
    let t := typeOf e
    match e.node with
    | .const (.floating fc) =>
      let .ok (w, x) := C3.floatConst fc | failure
      return val (← conv (.float w) t (flit (C3.F.convert w 8 x)))
    | .const c =>
      let .ok v := C0.constVal c t | failure
      return val (lit v)
    | .rvalue a =>
      let addr ← ElabC2.lvalue (expression P n) n a
      let x ← ElabC0.fresh
      return ee (.sseq (bind (some x) (.object .pointer)) addr
        (← loadAt (pe (.sym x)) (typeOf a)))
    | .annot _ a | .cast _ _ a =>
      let ta := typeOf a
      let body ← expression P n a
      if !ta.isFloat && !t.isFloat && e.node matches .annot .. then return body
      let v ← ElabC0.fresh
      let p ← if ta.isFloat || t.isFloat then conv ta t (pe (.sym v))
        else ElabC2.conv t (← ElabC2.conv ta (pe (.sym v)))
      return ee (.sseq (bind (some v) (.object (← objectType ta))) body (val p))
    | .unary (.postfixIncr) a | .unary (.postfixDecr) a =>
      let ta := typeOf a
      let addr ← ElabC2.lvalue (expression P n) n a
      let x ← ElabC0.fresh
      let old ← ElabC0.fresh
      let op := match e.node with | .unary .postfixIncr _ => ArithmeticOperator.add | _ => .sub
      let p ← step op ta (pe (.sym old))
      return ee (.sseq (bind (some x) (.object .pointer)) addr
        (ee (.sseq (bind (some old) (.object (← objectType ta))) (← loadAt (pe (.sym x)) ta)
          (seq (← storeAt (pe (.sym x)) ta p) (val (pe (.sym old)))))))
    | .unary .address a => ElabC2.lvalue (expression P n) n a
    | .unary op a =>
      let ta := typeOf a
      let body ← expression P n a
      let v ← ElabC0.fresh
      let x := pe (.sym v)
      let p ← (match op, t with
        | .plus, _ => conv ta t x
        | .minus, .float _ => do floatArith .mul (flit 0xbff0000000000000) (← conv ta t x)
        | .minus, _ => ElabC0.arithmetic .sub t (lit 0) x
        | .bnot, _ => do
          let ty ← ElabC0.ctype t
          return pe (.ctor .ivCompl [pe (.val (.ctype ty)), (← ElabC2.conv t x)])
        | _, _ => none : Option PE)
      return ee (.sseq (bind (some v) (.object (← objectType ta))) body (val p))
    | .binary a .comma b =>
      let a' ← expression P n a
      let b' ← expression P n b
      return ee (.sseq (bind none (.object (← objectType (typeOf a)))) a' b')
    | .binary a op b =>
      let ta := typeOf a
      let tb := typeOf b
      let oa ← objectType ta
      let ob ← objectType tb
      let left ← expression P n a
      let right ← expression P n b
      let x ← ElabC0.fresh
      let y ← ElabC0.fresh
      let px := pe (.sym x)
      let py := pe (.sym y)
      let body ← match op with
        | .and => pure (ee (.if_ (truth ta px)
            (ee (.sseq (bind (some y) (.object ob)) right (val (boolInt (truth tb py)))))
            (val (lit 0))))
        | .or => pure (ee (.if_ (truth ta px) (val (lit 1))
            (ee (.sseq (bind (some y) (.object ob)) right (val (boolInt (truth tb py)))))))
        | _ => do
          let p ← match op with
            | .arithmetic aop => arithmetic aop t ta tb px py
            | _ => do
              let .ok u := C3.usualOf ta tb | none
              ElabC0.relation op (← conv ta u px) (← conv tb u py)
          pure (ee (.sseq (bind (some y) (.object ob)) right (val p)))
      return ee (.sseq (bind (some x) (.object oa)) left body)
    | .assign lhs rhs =>
      let body ← expression P n rhs
      let addr ← ElabC2.lvalue (expression P n) n lhs
      let v ← ElabC0.fresh
      let a ← ElabC0.fresh
      let p ← conv (typeOf rhs) (typeOf lhs) (pe (.sym v))
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf rhs)))) body
        (ee (.sseq (bind (some a) (.object .pointer)) addr
          (seq (← storeAt (pe (.sym a)) (typeOf lhs) p) (val p)))))
    | .compoundAssign lhs op rhs =>
      let tl := typeOf lhs
      let tr := typeOf rhs
      let body ← expression P n rhs
      let addr ← ElabC2.lvalue (expression P n) n lhs
      let r ← ElabC0.fresh
      let a ← ElabC0.fresh
      let old ← ElabC0.fresh
      let p ← compound op tl tr (pe (.sym old)) (pe (.sym r))
      return ee (.sseq (bind (some r) (.object (← objectType tr))) body
        (ee (.sseq (bind (some a) (.object .pointer)) addr
          (ee (.sseq (bind (some old) (.object (← objectType tl))) (← loadAt (pe (.sym a)) tl)
            (seq (← storeAt (pe (.sym a)) tl p) (val p)))))))
    | .call f args =>
      let .functionDecay ⟨_, _, _, .ident g⟩ := f.node | failure
      let name := (P.names[g.number]?).getD ""
      let pts := (P.protos[g.number]?).getD []
      if !(P.funcs.contains g.number) && (C3.F.libm name).isSome then
        return ← argumentValues (expression P n) pts args fun
          | [x] => libm name x
          | _ => failure
      if !(P.funcs.contains g.number) && name != "abort" && name != "exit" && name != "_Exit" then failure else pure ()
      argumentValues (expression P n) pts args fun ps => do
        let result ← ElabC0.fresh
        let call := if !(P.funcs.contains g.number) && (name == "exit" || name == "_Exit") then
          ee (.proc () (.impl (.builtinFunction "exit")) ps)
          else ee (.proc () (.sym g) ps)
        if (t matches .void) then
          return ee (.sseq (bind none .unit) call (val (lit 0)))
        else
          return ee (.sseq (.mk [] (.ctor .specified [bind (some result) (.object (← objectType t))]))
            call (val (← conv t t (pe (.sym result)))))
    | .sizeof _ ty | .alignof _ ty =>
      let .ok (sz, al) := P.sizeAlign ty | failure
      return val (lit (match e.node with | .alignof .. => al | _ => sz))
    | .offsetof ty m =>
      let .ok (off, _) := P.member ty m | failure
      return val (lit off)
    | .sizeofExpr a =>
      match a.annotation with
      | .lvalue _ ty _ =>
        let .ok (sz, _) := P.sizeAlign ty | failure
        return val (lit sz)
      | .rvalue _ =>
        match C2.aggOf (typeOf a) with
        | some ty =>
          let .ok (sz, _) := P.sizeAlign ty | failure
          return val (lit sz)
        | none =>
          let some sz := C3.width (typeOf a) | failure
          return val (lit sz)
    | .cond c yes no =>
      let tc := typeOf c
      let cond ← expression P n c
      let v ← ElabC0.fresh
      let result ← ElabC0.fresh
      let convert (src : CType) (body : EE) : Gen EE := do
        return ee (.sseq (bind (some result) (.object (← objectType src))) body
          (val (← conv src t (pe (.sym result)))))
      let a ← match yes with
        | some e => convert (typeOf e) (← expression P n e)
        | none => pure (val (← conv tc t (pe (.sym v))))
      let b ← convert (typeOf no) (← expression P n no)
      return ee (.sseq (bind (some v) (.object (← objectType tc))) cond
        (ee (.if_ (truth tc (pe (.sym v))) a b)))
    | .struct tag fields =>
      let some (_, .struct members none) := P.tags.lookup tag | failure
      let rec gather (ms : List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)))
          (values : List (Identifier × PE)) : Gen EE := do
        match ms with
        | [] => return val (pe (.struct tag values))
        | (name, (_, _, _, ty)) :: rest =>
          let (value, src) ← match fields.find? (fun x => x.1.name == name.name) with
            | some (_, some e) => pure (← expression P n e, typeOf e)
            | _ => pure (val (← zeroValue n ty P.tags), ofCtype ty)
          let x ← ElabC0.fresh
          let p ← conv src (ofCtype ty) (pe (.sym x))
          let tail ← gather rest (values ++ [(name, p)])
          return ee (.sseq (bind (some x) (.object (← objectType src))) value tail)
      gather members []
    | _ => failure

def initDecls (P : C3.Prog) (fuel : Nat) (fd : C1.FunDef)
    (decls : List (Sym × Option TypedExpression)) (next : EE) : Gen EE := do
  match decls with
  | [] => return next
  | (x, init) :: rest =>
    let tail ← initDecls P fuel fd rest next
    match init with
    | none => return tail
    | some e =>
      let t := (fd.locals[x.number]?).getD (typeOf e)
      let body ← expression P fuel e
      let v ← ElabC0.fresh
      let p ← conv (typeOf e) t (pe (.sym v))
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf e)))) body
        (seq (← storeAt (pe (.sym (ptr x.number))) t p) tail))

mutual
def statement : Nat → C3.Prog → C1.FunDef → Option Sym → Option Sym → TypedStatement → EE → Gen EE
  | 0, _, _, _, _, _, _ => failure
  | n + 1, P, fd, brk, cont, s, next => do
    match s.node with
    | .skip => return next
    | .expr e =>
      return ee (.sseq (bind none (.object (← objectType (typeOf e)))) (← expression P n e) next)
    | .block _ ss => statements n P fd brk cont ss next
    | .returnVoid => return if (fd.ret matches .void) then val (pe (.val .unit)) else val (specified (lit 0))
    | .return_ e =>
      let body ← expression P n e
      let v ← ElabC0.fresh
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf e)))) body
        (val (specified (← conv (typeOf e) fd.ret (pe (.sym v))))))
    | .if_ c yes no =>
      let tc := typeOf c
      let cond ← expression P n c
      let a ← statement n P fd brk cont yes next
      let b ← statement n P fd brk cont no next
      let v ← ElabC0.fresh
      return ee (.sseq (bind (some v) (.object (← objectType tc))) cond
        (ee (.if_ (truth tc (pe (.sym v))) a b)))
    | .label l body _ =>
      return ee (.save (sourceLabel l.number, .loaded .integer) []
        (← statement n P fd brk cont body next))
    | .goto l => return ee (.run () (sourceLabel l.number) [])
    | .break_ => return ee (.run () (← brk) [])
    | .continue_ => return ee (.run () (← cont) [])
    | .while_ c body _ | .do_ body c _ =>
      let tc := typeOf c
      let stop ← ElabC0.fresh
      let test ← ElabC0.fresh
      let start ← ElabC0.fresh
      let v ← ElabC0.fresh
      let jump (x : Sym) := ee (.run () x [])
      let b ← statement n P fd (some stop) (some test) body (jump test)
      let bodySave := ee (.save (start, .loaded .integer) [] b)
      let cond ← expression P n c
      let testBody := ee (.sseq (bind (some v) (.object (← objectType tc))) cond
        (ee (.if_ (truth tc (pe (.sym v))) bodySave (jump stop))))
      let testSave := ee (.save (test, .loaded .integer) [] testBody)
      let entry := match s.node with
        | .do_ .. => ee (.if_ (pe (.val .true)) (jump start) testSave)
        | _ => testSave
      return ee (.if_ (pe (.val .true)) entry (ee (.save (stop, .loaded .integer) [] next)))
    | .declaration ds => initDecls P n fd ds next
    | .marker _ s => statement n P fd brk cont s next
    | _ => failure

def statements : Nat → C3.Prog → C1.FunDef → Option Sym → Option Sym → List TypedStatement → EE → Gen EE
  | 0, _, _, _, _, _, _ => failure
  | _ + 1, _, _, _, _, [], next => return next
  | n + 1, P, fd, brk, cont, s :: ss, next => do
    let tail ← statements n P fd brk cont ss next
    statement n P fd brk cont s tail
end

def allocate (locals : List (Nat × CType)) (body : EE) : Option EE := do
  match locals with
  | [] => return body
  | (x, t) :: rest =>
    let tail ← allocate rest body
    let ty ← ctype t
    let pty := pe (.val (.ctype ty))
    let create := action (.create (pe (.ctor .ivAlignof [pty])) pty (.source .unknown [ptr x]))
    return ee (.sseq (bind (some (ptr x)) (.object .pointer)) create tail)

/-- Translate every reachable definition; calls share Core's global environment. -/
def translate (p : TypedProgram) : Option Program := do
  let P := C3.prepare p
  let main ← p.1
  let _ ← P.funcs[main.number]?
  let live := C2.reachable P.toC2 (main.number :: (P.statics.flatMap fun (_, _, i) =>
    (i.map C2.callsE).getD []))
  let work : Gen Program := do
    let mut funs := []
    for f in live do
      let fd ← P.funcs[f]?
      let fd := if f == main.number && (fd.ret matches .void) then
        {fd with ret := .int 4 true} else fd
      let g ← p.2.functionDefinitions.findSome? fun (x, _) => if x.number == f then some x else none
      let ret := if (fd.ret matches .void) then val (pe (.val .unit)) else val (specified (lit 0))
      let mut body ← statement 512 P fd none none fd.body ret
      for ((x,t), i) in fd.params.zipIdx do
        let value := if f == main.number then lit (if i == 0 then 1 else 0) else pe (.sym (parameter x))
        body := seq (← storeAt (pe (.sym (ptr x))) t value) body
      body ← allocate fd.locals.toList body
      let params ← if f == main.number then pure [] else
        fd.params.mapM fun (x, t) => do pure (parameter x, BaseType.object (← objectType t))
      funs := (g, Silmaril.Cerberus.Core.FunDecl.procedure .unknown none
        (← returnType fd.ret) params body) :: funs
    for (g,_) in p.2.declarations do
      if (P.names[g.number]?).getD "" == "abort" && !(P.funcs.contains g.number) then
        funs := (g, .procedureDecl .unknown .unit []) :: funs
    let mut globs := []
    let mut done := []
    for (x, ty, init) in P.statics do
      if !P.obj ty then continue
      let t := ofCtype ty
      if done.contains x then continue
      done := x :: done
      let ty ← ctype t
      let (value, src) ← match init with
        | none => pure (val (← zeroValue 64 ty P.tags), t)
        | some e => pure (← expression P 512 e, typeOf e)
      let v ← ElabC0.fresh
      let initBody := ee (.sseq (bind (some v) (.object (← objectType src))) value
        (seq (← storeAt (pe (.sym (ptr x))) t (← conv src t (pe (.sym v)))) (val (pe (.sym (ptr x))))))
      let body ← allocate [(x,t)] initBody
      globs := globs ++ [(ptr x, Silmaril.Cerberus.Core.Global.definition (.object .pointer,ty) body)]
    return {
      main := some main, callingConvention := .normal, tagDefs := P.tags.definitions,
      stdlib := ∅, impl := ∅, globs, funs := Map.ofList funs,
      extern := ∅, funInfo := ∅, loopAttributes := ∅, visibleObjects := ∅ }
  return (← work.run 0).1

/-- Completed C3 runs have exactly their observed behaviour. -/
theorem c3_beh_eq {p : TypedProgram} {fuel : Nat} {o : Obs}
    (h : C3.run fuel p = .done o) : C3.beh p = {o} := by
  ext o'
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, why, hn⟩ | ⟨_, hn⟩)
    · have eq := C3.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
      rfl
    · have eq := C3.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
    · have eq := h.symm.trans (hn fuel)
      cases eq
  · rintro rfl
    exact C3.beh_of_done h

/-- The structural result is returned only after two exact observations agree. -/
def elaborate (p : TypedProgram) : Option Program := do
  if C3.check p != .ok () then none else do
    let q ← translate p
    let .done source := C3.run 100000 p | none
    let target ← ExactCore.exactProgram 100000 q
    if source = target then some q else none

theorem elaborate_sound {p : TypedProgram} {q : Program}
    (h : elaborate p = some q) : C3.InFragment p ∧ Compile.Core.beh q = C3.beh p := by
  unfold elaborate at h
  split at h
  · contradiction
  · rename_i hc
    have fragment : C3.InFragment p := by simpa [C3.InFragment] using hc
    cases ht : translate p with
    | none => simp [ht] at h
    | some q' =>
      simp only [ht] at h
      cases hr : C3.run 100000 p <;> simp only [hr] at h
      all_goals try contradiction
      rename_i source
      cases he : ExactCore.exactProgram 100000 q' with
      | none => simp [he] at h
      | some target =>
        simp only [Bind.bind, Option.bind, he] at h
        split at h
        · rename_i eq
          cases h
          exact ⟨fragment, (ExactCore.exactProgram_sound he).trans
            (eq ▸ (c3_beh_eq hr).symm)⟩
        · contradiction

end Silmaril.Compile.C.Sem.ElabC3
