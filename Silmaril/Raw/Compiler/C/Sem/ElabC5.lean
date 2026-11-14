module

public import Silmaril.Compiler.C.Sem.C5Mono.Defs
public import Silmaril.Compiler.C.Sem.ElabC4.Defs
@[expose] public section

/-!
# Checked structural C5 elaboration

Extend the C4 translation with the heap. Direct calls of the allocation functions
(`malloc`, `calloc`, `realloc`, `free`, gcc's `__builtin_` forms included) that the
program does not define translate to Core memory actions:

* `malloc(n)` is Core's `alloc` of an aligned region of `n` bytes;
* `free(p)` tests `p` against null, then statically kills the region base with an
  `unsigned char` footprint (so the block of `malloc(0)` cannot be freed);
* `calloc(k, n)` allocates `k * n` bytes, then calls a Core procedure that stores a
  zero byte at each offset;
* `realloc` translates only in programs whose every allocation records its size in a
  16-byte header below the block; it allocates the new block, copies the first
  `min old n` bytes through a Core byte-copy procedure and kills the old region.
  `realloc(NULL, n)` is `malloc(n)` and `realloc(p, 0)` frees `p` and returns null.

Conversions between `void *` and object pointers keep the Core pointer. Pointer
addition and subtraction of an integer use Core's `arrayShift`. Nothing about these
encodings is assumed: Core has no allocation-size query, `memcpy` or zero-filled
region, and its exhaustion is unsupported rather than `NULL`, its equality across
distinct allocations undecided, and its addresses not C5's. As for C0 through C4,
acceptance compares a completed C5 execution with an exact Core execution, so a
program whose heap encoding is wrong, which frees memory not from `malloc`, uses a
block after `free`, frees it twice, observes addresses or exhausts the heap
declines. C4's restrictions remain. This is worker-written realisation, not
agreement with Cerberus's elaboration.
-/

namespace Silmaril.Compile.C.Sem.ElabC5

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Core (Pattern BaseType ObjectType)
open Silmaril.Cerberus.Core.Dynamics (PE EE Program)
open ElabC0 (Gen pe ee lit val specified bind seq ptr sourceLabel parameter boolInt action)
open ElabC3 (flit floatArith arithmetic step compound libm loadAt storeAt zeroValue allocate ctype)
open ElabC4 (objectType null nullConstant returnType condition fixedE fixedS)

/-- Is `t` a (qualified) `void`? -/
def isVoid : Ctype → Bool
  | .mk _ .void => true
  | _ => false

/-- As C4, and `void *` converts to and from every object pointer. -/
def conv (src dst : CType) (p : PE) : Option PE := do
  match src, dst with
  | .ptr a, .ptr b =>
    if isVoid a || isVoid b then return p else ElabC4.conv src dst p
  | _, _ => ElabC4.conv src dst p

def convE (e : TypedExpression) (dst : CType) (p : PE) : Option PE := do
  if let .ptr ty := dst then
    if nullConstant 64 e then return null ty
  conv (typeOf e) dst p

def argumentValues (translateE : TypedExpression → Gen EE)
    (pts : List CType) (args : List TypedExpression) (next : List PE → Gen EE) : Gen EE := do
  match args with
  | [] => next []
  | a :: rest =>
    let body ← translateE a
    let x ← ElabC0.fresh
    let p ← convE a (pts.headD (typeOf a)) (pe (.sym x))
    let tail ← argumentValues translateE pts.tail rest (fun ps => next (p :: ps))
    return ee (.sseq (bind (some x) (.object (← objectType (typeOf a)))) body tail)

/-! ## The heap -/

def byteTy : Ctype := .mk [] (.basic (.integer (.unsigned .ichar)))
def sizeTy : Ctype := .mk [] (.basic (.integer (.unsigned .long)))
def voidTy : Ctype := .mk [] .void

/-- Symbols of the helper procedures and their variables (a digest no source symbol has). -/
def helper (n : Nat) (name : String) : Sym := ⟨⟨List.replicate 16 7⟩, n, .id name⟩
def zeroProc : Sym := helper 0 "csem_zero"
def copyProc : Sym := helper 1 "csem_copy"
def loopLabel : Sym := helper 2 "loop"
def argP : Sym := helper 3 "p"
def argQ : Sym := helper 4 "q"
def argN : Sym := helper 5 "n"
def argI : Sym := helper 6 "i"
def loaded : Sym := helper 7 "byte"

/-- A procedure with a byte loop `i = 0 .. n - 1` over `params`, returning `unit`. -/
def byteLoop (params : List (Sym × BaseType)) (body : PE → EE) :
    Silmaril.Cerberus.Core.FunDecl Codec.wireModel Unit Unit :=
  let i := pe (.sym argI)
  let next := ee (.run () loopLabel [pe (.op .add i (lit 1))])
  let test := ee (.if_ (pe (.op .lt i (pe (.sym argN)))) (seq (body i) next) (val (pe (.val .unit))))
  .procedure .unknown none .unit params
    (ee (.save (loopLabel, .unit) [(argI, ((.object .integer, none), lit 0))] test))

def at_ (base : Sym) (i : PE) : PE := pe (.arrayShift (pe (.sym base)) byteTy i)

/-- Store a zero byte at each of the `n` bytes from `p`. -/
def zeroDecl : Silmaril.Cerberus.Core.FunDecl Codec.wireModel Unit Unit :=
  byteLoop [(argP, .object .pointer), (argN, .object .integer)] fun i =>
    action (.store false (pe (.val (.ctype byteTy))) (at_ argP i) (specified (lit 0)) .na)

/-- Copy `n` bytes from `q` to `p`, initialisation included (a byte is loaded as is). -/
def copyDecl : Silmaril.Cerberus.Core.FunDecl Codec.wireModel Unit Unit :=
  byteLoop [(argP, .object .pointer), (argQ, .object .pointer), (argN, .object .integer)] fun i =>
    ee (.sseq (bind (some loaded) (.loaded .integer))
      (action (.load (pe (.val (.ctype byteTy))) (at_ argQ i) .na))
      (action (.store false (pe (.val (.ctype byteTy))) (at_ argP i) (pe (.sym loaded)) .na)))

/-- The bytes below a block where `realloc` programs record its size. -/
def header : Nat := 16

/-- An aligned region of `n` bytes; with `sized`, after a header that records `n`. -/
def alloc (sized : Bool) (n : PE) : Gen EE := do
  if !sized then
    return action (.alloc (lit 16) n .malloc)
  let b ← ElabC0.fresh
  return ee (.sseq (bind (some b) (.object .pointer))
    (action (.alloc (lit 16) (pe (.op .add n (lit header))) .malloc))
    (seq (action (.store false (pe (.val (.ctype sizeTy))) (pe (.sym b)) (specified n) .na))
      (val (pe (.arrayShift (pe (.sym b)) byteTy (lit header))))))

/-- The region of a block (its header, if sized). -/
def region (sized : Bool) (p : PE) : PE :=
  if sized then pe (.arrayShift p byteTy (lit (-header))) else p

/-- `free(p)`: nothing for null, else a static kill of the region base. -/
def free (sized : Bool) (p : PE) : Gen EE := do
  let b ← ElabC0.fresh
  return ee (.sseq (bind (some b) .boolean) (ee (.memop .ptrEq [p, null voidTy]))
    (ee (.if_ (pe (.sym b)) (val (pe (.val .unit)))
      (action (.kill (.static byteTy) (region sized p))))))

def calloc (sized : Bool) (k n : PE) : Gen EE := do
  let size ← ElabC0.fresh
  let b ← ElabC0.fresh
  let sz := pe (.sym size)
  return ee (.sseq (bind (some size) (.object .integer)) (val (pe (.op .mul k n)))
    (ee (.sseq (bind (some b) (.object .pointer)) (← alloc sized sz)
      (seq (ee (.proc () (.sym zeroProc) [pe (.sym b), sz])) (val (pe (.sym b)))))))

/-- `realloc(p, n)` of a sized program. -/
def realloc (p n : PE) : Gen EE := do
  let isNull ← ElabC0.fresh
  let old ← ElabC0.fresh
  let q ← ElabC0.fresh
  let zero ← ElabC0.fresh
  let loadOld := ee (.sseq (.mk [] (.ctor .specified [bind (some old) (.object .integer)]))
    (action (.load (pe (.val (.ctype sizeTy))) (region true p) .na))
    (ee (.sseq (bind (some q) (.object .pointer)) (← alloc true n)
      (seq (ee (.proc () (.sym copyProc) [pe (.sym q), p,
          pe (.if_ (pe (.op .lt (pe (.sym old)) n)) (pe (.sym old)) n)]))
        (seq (← free true p) (val (pe (.sym q))))))))
  return ee (.sseq (bind (some isNull) .boolean) (ee (.memop .ptrEq [p, null voidTy]))
    (ee (.if_ (pe (.sym isNull)) (← alloc true n)
      (ee (.sseq (bind (some zero) .boolean) (val (pe (.op .eq n (lit 0))))
        (ee (.if_ (pe (.sym zero)) (seq (← free true p) (val (null voidTy))) loadOld)))))))

/-- Direct calls of an allocation function the program does not define. -/
def heapCall (sized : Bool) (name : String) (ps : List PE) : Gen EE :=
  match name, ps with
  | "malloc", [n] => alloc sized n
  | "calloc", [k, n] => calloc sized k n
  | "free", [p] => free sized p
  | "realloc", [p, n] => if sized then realloc p n else failure
  | _, _ => failure

/-- Expressions return a typed Core object; `sseq` makes operand order explicit. -/
def expression (P : C4.Prog) (sized : Bool) : Nat → TypedExpression → Gen EE
  | 0, _ => failure
  | n + 1, e => do
    let t := typeOf e
    match e.node with
    | .ident g =>
      if !C4.isFunction e || !P.symbols.contains g.number then failure else
        return val (pe (.val (.object (.pointer (.function g)))))
    | .functionDecay a => expression P sized n a
    | .unary .indirection a =>
      if C4.isFunction e then expression P sized n a else failure
    | .const .null =>
      let .ptr ty := t | failure
      return val (null ty)
    | .const (.integer ic) =>
      if let .ptr ty := t then
        if Silmaril.Compile.Forks.Csem.C.intConstValue ic == 0 then return val (null ty) else failure
      else
        let .ok v := C0.constVal (.integer ic) t | failure
        return val (lit v)
    | .const (.floating fc) =>
      let .ok (w, x) := C3.floatConst fc | failure
      return val (← conv (.float w) t (flit (C3.F.convert w 8 x)))
    | .const c =>
      let .ok v := C0.constVal c t | failure
      return val (lit v)
    | .rvalue a =>
      let addr ← ElabC2.lvalue (expression P sized n) n a
      let x ← ElabC0.fresh
      return ee (.sseq (bind (some x) (.object .pointer)) addr
        (← loadAt (pe (.sym x)) (typeOf a)))
    | .cast _ _ a =>
      if let .ptr ty := t then
        if let .const (.integer ic) := a.node then
          if Silmaril.Compile.Forks.Csem.C.intConstValue ic == 0 then return val (null ty) else failure
      let ta := typeOf a
      let body ← expression P sized n a
      let v ← ElabC0.fresh
      let tail ← if (t matches .bool) && (ta matches .ptr _) then
          condition ta (pe (.sym v)) (val (lit 1)) (val (lit 0))
        else pure (val (← convE a t (pe (.sym v))))
      return ee (.sseq (bind (some v) (.object (← objectType ta))) body tail)
    | .annot _ a =>
      let ta := typeOf a
      let body ← expression P sized n a
      let v ← ElabC0.fresh
      let tail ← if (t matches .bool) && (ta matches .ptr _) then
          condition ta (pe (.sym v)) (val (lit 1)) (val (lit 0))
        else pure (val (← convE a t (pe (.sym v))))
      return ee (.sseq (bind (some v) (.object (← objectType ta))) body tail)
    | .unary (.postfixIncr) a | .unary (.postfixDecr) a =>
      let ta := typeOf a
      let addr ← ElabC2.lvalue (expression P sized n) n a
      let x ← ElabC0.fresh
      let old ← ElabC0.fresh
      let op := match e.node with | .unary .postfixIncr _ => ArithmeticOperator.add | _ => .sub
      let p ← match ta with
        | .ptr ty => pure (pe (.arrayShift (pe (.sym old)) ty (lit (if op matches .add then 1 else -1))))
        | _ => step op ta (pe (.sym old))
      return ee (.sseq (bind (some x) (.object .pointer)) addr
        (ee (.sseq (bind (some old) (.object (← objectType ta))) (← loadAt (pe (.sym x)) ta)
          (seq (← storeAt (pe (.sym x)) ta p) (val (pe (.sym old)))))))
    | .unary .address a =>
      if C4.isFunction a then expression P sized n a else ElabC2.lvalue (expression P sized n) n a
    | .unary op a =>
      let ta := typeOf a
      let body ← expression P sized n a
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
      let a' ← expression P sized n a
      let b' ← expression P sized n b
      return ee (.sseq (bind none (.object (← objectType (typeOf a)))) a' b')
    | .binary a op b =>
      let ta := typeOf a
      let tb := typeOf b
      let oa ← objectType ta
      let ob ← objectType tb
      let left ← expression P sized n a
      let right ← expression P sized n b
      let x ← ElabC0.fresh
      let y ← ElabC0.fresh
      let px := pe (.sym x)
      let py := pe (.sym y)
      let body ← match op with
        | .and =>
          let tail ← condition tb py (val (lit 1)) (val (lit 0))
          condition ta px (ee (.sseq (bind (some y) (.object ob)) right tail)) (val (lit 0))
        | .or =>
          let tail ← condition tb py (val (lit 1)) (val (lit 0))
          condition ta px (val (lit 1)) (ee (.sseq (bind (some y) (.object ob)) right tail))
        | .arithmetic aop =>
          match ta, tb, aop with
          | .ptr ty, .int .., .add | .ptr ty, .int .., .sub | .int .., .ptr ty, .add => do
            let (p, i) := if ta matches .ptr _ then (px, py) else (py, px)
            let i := if aop matches .sub then pe (.op .sub (lit 0) i) else i
            pure (ee (.sseq (bind (some y) (.object ob)) right (val (pe (.arrayShift p ty i)))))
          | .ptr _, _, _ | _, .ptr _, _ => failure
          | _, _, _ => do
            let p ← arithmetic aop t ta tb px py
            pure (ee (.sseq (bind (some y) (.object ob)) right (val p)))
        | _ =>
          if (ta matches .ptr _) || (tb matches .ptr _) then do
            let ty ← match ta, tb with
              | .ptr ty, _ | _, .ptr ty => pure ty
              | _, _ => failure
            let ca ← convE a (.ptr ty) px
            let cb ← convE b (.ptr ty) py
            let cmp ← match op with
              | .eq => pure Silmaril.Cerberus.MemOp.ptrEq
              | .ne => pure .ptrNe
              | _ => failure
            let result ← ElabC0.fresh
            pure (ee (.sseq (bind (some y) (.object ob)) right
              (ee (.sseq (bind (some result) .boolean) (ee (.memop cmp [ca, cb]))
                (val (boolInt (pe (.sym result))))))))
          else do
            let p ← match op with
              | .arithmetic aop => arithmetic aop t ta tb px py
              | _ => do
                let .ok u := C3.usualOf ta tb | none
                ElabC0.relation op (← conv ta u px) (← conv tb u py)
            pure (ee (.sseq (bind (some y) (.object ob)) right (val p)))
      return ee (.sseq (bind (some x) (.object oa)) left body)
    | .assign lhs rhs =>
      let body ← expression P sized n rhs
      let addr ← ElabC2.lvalue (expression P sized n) n lhs
      let v ← ElabC0.fresh
      let a ← ElabC0.fresh
      let p ← convE rhs (typeOf lhs) (pe (.sym v))
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf rhs)))) body
        (ee (.sseq (bind (some a) (.object .pointer)) addr
          (seq (← storeAt (pe (.sym a)) (typeOf lhs) p) (val p)))))
    | .compoundAssign lhs op rhs =>
      let tl := typeOf lhs
      let tr := typeOf rhs
      let body ← expression P sized n rhs
      let addr ← ElabC2.lvalue (expression P sized n) n lhs
      let r ← ElabC0.fresh
      let a ← ElabC0.fresh
      let old ← ElabC0.fresh
      let p ← match tl, tr, op with
        | .ptr ty, .int .., .add => pure (pe (.arrayShift (pe (.sym old)) ty (pe (.sym r))))
        | .ptr ty, .int .., .sub =>
          pure (pe (.arrayShift (pe (.sym old)) ty (pe (.op .sub (lit 0) (pe (.sym r))))))
        | .ptr _, _, _ | _, .ptr _, _ => failure
        | _, _, _ => compound op tl tr (pe (.sym old)) (pe (.sym r))
      return ee (.sseq (bind (some r) (.object (← objectType tr))) body
        (ee (.sseq (bind (some a) (.object .pointer)) addr
          (ee (.sseq (bind (some old) (.object (← objectType tl))) (← loadAt (pe (.sym a)) tl)
            (seq (← storeAt (pe (.sym a)) tl p) (val p)))))))
    | .call f args =>
      let .ptr fty := typeOf f | failure
      let pts ← match fty with
        | .mk _ (.function _ ps false) => pure (ps.map fun (_, ty, _) => ofCtype ty)
        | .mk _ (.functionNoParams _) => pure (args.map typeOf)
        | _ => failure
      let direct := match f.node with
        | .functionDecay ⟨_, _, _, .ident g⟩ => some g
        | _ => none
      if let some g := direct then
        let name := (P.names[g.number]?).getD ""
        if !(P.funcs.contains g.number) && (C3.F.libm name).isSome then
          return ← argumentValues (expression P sized n) pts args fun
            | [x] => libm name x
            | _ => failure
        if !(P.funcs.contains g.number) && C5.heapExternals.contains (P.name g) then
          return ← argumentValues (expression P sized n) pts args fun ps => do
            let body ← heapCall sized (P.name g) ps
            if (t matches .void) then return seq body (val (lit 0)) else return body
        if !(P.funcs.contains g.number) && (name == "exit" || name == "_Exit") then
          return ← argumentValues (expression P sized n) pts args fun ps =>
            pure (ee (.proc () (.impl (.builtinFunction "exit")) ps))
      let target ← expression P sized n f
      let callee ← ElabC0.fresh
      let body ← argumentValues (expression P sized n) pts args fun ps => do
        let result ← ElabC0.fresh
        let call := ee (.ccall () (pe (.val (.ctype fty)))
          (specified (pe (.sym callee))) ps)
        if (t matches .void) then
          return ee (.sseq (bind none .unit) call (val (lit 0)))
        else
          return ee (.sseq (.mk [] (.ctor .specified [bind (some result) (.object (← objectType t))]))
            call (val (← conv t t (pe (.sym result)))))
      return ee (.sseq (bind (some callee) (.object .pointer)) target body)
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
      let cond ← expression P sized n c
      let v ← ElabC0.fresh
      let result ← ElabC0.fresh
      let convert (e : TypedExpression) (body : EE) : Gen EE := do
        return ee (.sseq (bind (some result) (.object (← objectType (typeOf e)))) body
          (val (← convE e t (pe (.sym result)))))
      let a ← match yes with
        | some e => convert e (← expression P sized n e)
        | none => pure (val (← convE c t (pe (.sym v))))
      let b ← convert no (← expression P sized n no)
      return ee (.sseq (bind (some v) (.object (← objectType tc))) cond
        (← condition tc (pe (.sym v)) a b))
    | .struct tag fields =>
      let some (_, .struct members none) := P.tags.lookup tag | failure
      let rec gather (ms : List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)))
          (values : List (Identifier × PE)) : Gen EE := do
        match ms with
        | [] => return val (pe (.struct tag values))
        | (name, (_, _, _, ty)) :: rest =>
          let (value, src) ← match fields.find? (fun x => x.1.name == name.name) with
            | some (_, some e) => pure (← expression P sized n e, typeOf e)
            | _ => pure (val (← zeroValue n ty P.tags), ofCtype ty)
          let x ← ElabC0.fresh
          let p ← match fields.find? (fun x => x.1.name == name.name) with
            | some (_, some e) => convE e (ofCtype ty) (pe (.sym x))
            | _ => conv src (ofCtype ty) (pe (.sym x))
          let tail ← gather rest (values ++ [(name, p)])
          return ee (.sseq (bind (some x) (.object (← objectType src))) value tail)
      gather members []
    | _ => failure

def initDecls (P : C4.Prog) (sized : Bool) (fuel : Nat) (fd : C1.FunDef)
    (decls : List (Sym × Option TypedExpression)) (next : EE) : Gen EE := do
  match decls with
  | [] => return next
  | (x, init) :: rest =>
    let tail ← initDecls P sized fuel fd rest next
    match init with
    | none => return tail
    | some e =>
      let t := (fd.locals[x.number]?).getD (typeOf e)
      let body ← expression P sized fuel e
      let v ← ElabC0.fresh
      let p ← convE e t (pe (.sym v))
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf e)))) body
        (seq (← storeAt (pe (.sym (ptr x.number))) t p) tail))

mutual
def statement : Nat → C4.Prog → Bool → C1.FunDef → Option Sym → Option Sym → TypedStatement → EE → Gen EE
  | 0, _, _, _, _, _, _, _ => failure
  | n + 1, P, sized, fd, brk, cont, s, next => do
    match s.node with
    | .skip => return next
    | .expr e =>
      return ee (.sseq (bind none (.object (← objectType (typeOf e)))) (← expression P sized n e) next)
    | .block _ ss => statements n P sized fd brk cont ss next
    | .returnVoid => return if (fd.ret matches .void) then val (pe (.val .unit)) else val (specified (lit 0))
    | .return_ e =>
      let body ← expression P sized n e
      let v ← ElabC0.fresh
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf e)))) body
        (val (specified (← convE e fd.ret (pe (.sym v))))))
    | .if_ c yes no =>
      let tc := typeOf c
      let cond ← expression P sized n c
      let a ← statement n P sized fd brk cont yes next
      let b ← statement n P sized fd brk cont no next
      let v ← ElabC0.fresh
      return ee (.sseq (bind (some v) (.object (← objectType tc))) cond
        (← condition tc (pe (.sym v)) a b))
    | .label l body _ =>
      return ee (.save (sourceLabel l.number, .loaded .integer) []
        (← statement n P sized fd brk cont body next))
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
      let b ← statement n P sized fd (some stop) (some test) body (jump test)
      let bodySave := ee (.save (start, .loaded .integer) [] b)
      let cond ← expression P sized n c
      let testBody := ee (.sseq (bind (some v) (.object (← objectType tc))) cond
        (← condition tc (pe (.sym v)) bodySave (jump stop)))
      let testSave := ee (.save (test, .loaded .integer) [] testBody)
      let entry := match s.node with
        | .do_ .. => ee (.if_ (pe (.val .true)) (jump start) testSave)
        | _ => testSave
      return ee (.if_ (pe (.val .true)) entry (ee (.save (stop, .loaded .integer) [] next)))
    | .declaration ds => initDecls P sized n fd ds next
    | .marker _ s => statement n P sized fd brk cont s next
    | _ => failure

def statements : Nat → C4.Prog → Bool → C1.FunDef → Option Sym → Option Sym → List TypedStatement → EE → Gen EE
  | 0, _, _, _, _, _, _, _ => failure
  | _ + 1, _, _, _, _, _, [], next => return next
  | n + 1, P, sized, fd, brk, cont, s :: ss, next => do
    let tail ← statements n P sized fd brk cont ss next
    statement n P sized fd brk cont s tail
end

/-- Syntactic exclusion of variadic calls and va_* even in unreachable code.
A depth limit fails closed. Variadic declarations alone (e.g. headers) are fine. -/
def fixedE : Nat → TypedExpression → Bool
  | 0, _ => false
  | n + 1, e =>
    let go := fixedE n
    match e.node with
    | .vaStart .. | .vaArg .. | .vaCopy .. | .vaEnd .. => false
    | .call f args =>
      let fixed := match typeOf f with
        | .ptr (.mk _ (.function _ _ true)) => false
        | _ => true
      fixed && go f && args.all go
    | .unary _ a | .annot _ a | .cast _ _ a | .assert a | .rvalue a
    | .arrayDecay a | .functionDecay a | .memberof a _ | .memberofptr a _
    | .compound _ _ a | .sizeofExpr a => go a
    | .binary a _ b | .assign a b | .compoundAssign a _ b => go a && go b
    | .cond c a b => go c && (a.map go).getD true && go b
    | .array _ _ es => es.all (fun e => (e.map go).getD true)
    | .struct _ ms => ms.all (fun (_, e) => (e.map go).getD true)
    | .union _ _ e => (e.map go).getD true
    | .generic a _ gs => go a && gs.all (fun g => match g with
        | .type_ _ _ e | .default e => go e)
    | _ => true

def fixedS : Nat → TypedStatement → Bool
  | 0, _ => false
  | n + 1, s =>
    let go := fixedS n
    match s.node with
    | .expr e | .return_ e => fixedE n e
    | .block _ ss | .par ss => ss.all go
    | .if_ c a b => fixedE n c && go a && go b
    | .while_ c b _ | .do_ b c _ | .switch c b => fixedE n c && go b
    | .case_ _ b | .caseRangeGnu _ _ b | .default b | .label _ b _ | .marker _ b => go b
    | .declaration ds => ds.all (fun (_, e) => (e.map (fixedE n)).getD true)
    | _ => true

/-- Translate every reachable definition; calls share Core's global environment. -/
def translate (p : TypedProgram) : Option Program := do
  let P := C4.prepare p
  if !p.2.functionDefinitions.all (fun (_, fd) => fixedS 512 fd.body) ||
      !p.2.objectDefinitions.all (fun (_, e) => fixedE 512 e) then none else pure ()
  -- Reject every variadic definition, including unreachable definitions.
  if p.2.functionDefinitions.any (fun (g, _) => P.variadics.contains g.number) then none else pure ()
  let main ← p.1
  let _ ← P.funcs[main.number]?
  let live := C4.reachable P (main.number :: (P.statics.flatMap fun (_, _, i) =>
    (i.map C4.callsE).getD []))
  -- Programs that reach `realloc` record every block's size in a header.
  let sized := (live.flatMap fun f => ((P.funcs[f]?).map (C4.callsS ·.body)).getD []).any fun g =>
    ["realloc", "__builtin_realloc"].contains ((P.names[g]?).getD "")
  let work : Gen Program := do
    let mut funs := [(zeroProc, zeroDecl), (copyProc, copyDecl)]
    for f in live do
      let fd ← P.funcs[f]?
      let fd := if f == main.number && (fd.ret matches .void) then
        {fd with ret := .int 4 true} else fd
      let g ← p.2.functionDefinitions.findSome? fun (x, _) => if x.number == f then some x else none
      let ret := if (fd.ret matches .void) then val (pe (.val .unit)) else val (specified (lit 0))
      let mut body ← statement 512 P sized fd none none fd.body ret
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
        | some e => pure (← expression P sized 512 e, typeOf e)
      let v ← ElabC0.fresh
      let converted ← match init with
        | some e => convE e t (pe (.sym v))
        | none => conv src t (pe (.sym v))
      let initBody := ee (.sseq (bind (some v) (.object (← objectType src))) value
        (seq (← storeAt (pe (.sym (ptr x))) t converted) (val (pe (.sym (ptr x))))))
      let body ← allocate [(x,t)] initBody
      globs := globs ++ [(ptr x, Silmaril.Cerberus.Core.Global.definition (.object .pointer,ty) body)]
    return {
      main := some main, callingConvention := .normal, tagDefs := P.tags.definitions,
      stdlib := ∅, impl := ∅, globs, funs := Map.ofList funs,
      extern := ∅, funInfo := ∅, loopAttributes := ∅, visibleObjects := ∅ }
  return (← work.run 0).1

/-- Completed C5 runs have exactly their observed behaviour. -/
theorem c5_beh_eq {p : TypedProgram} {fuel : Nat} {o : Obs}
    (h : C5.run fuel p = .done o) : C5.beh p = {o} := by
  ext o'
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, why, hn⟩ | ⟨_, hn⟩)
    · have eq := C5.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
      rfl
    · have eq := C5.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
    · have eq := h.symm.trans (hn fuel)
      cases eq
  · rintro rfl
    exact C5.beh_of_done h

/-- The structural result is returned only after two exact observations agree. -/
def elaborate (p : TypedProgram) : Option Program := do
  if C5.check p != .ok () then none else do
    let q ← translate p
    let .done source := C5.run 100000 p | none
    let target ← ExactCore.exactProgram 100000 q
    if source = target then some q else none

theorem elaborate_sound {p : TypedProgram} {q : Program}
    (h : elaborate p = some q) : C5.InFragment p ∧ Compile.Core.beh q = C5.beh p := by
  unfold elaborate at h
  split at h
  · contradiction
  · rename_i hc
    have fragment : C5.InFragment p := by simpa [C5.InFragment] using hc
    cases ht : translate p with
    | none => simp [ht] at h
    | some q' =>
      simp only [ht] at h
      cases hr : C5.run 100000 p <;> simp only [hr] at h
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
            (eq ▸ (c5_beh_eq hr).symm)⟩
        · contradiction

end Silmaril.Compile.C.Sem.ElabC5
