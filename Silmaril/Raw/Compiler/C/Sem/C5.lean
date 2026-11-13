module

public import Silmaril.Compiler.C.Sem.C4.Defs
@[expose] public section

/-!
# C5: the heap (`malloc`, `calloc`, `realloc`, `free`)

C5 extends C4 with the allocation functions of `<stdlib.h>` (STD §7.22.3), gcc's
`__builtin_malloc` and friends included. Everything else is C4's.

## The heap

A heap block is a C1 allocation of the requested size, aligned to 16 (as glibc's and ccomp's
runtime `malloc`), placed on top of the current stack after a gap of 16 bytes (where ccomp's
runtime keeps its block header); the stack then never shrinks below the last block, so a
block outlives the activation that allocated it. Blocks are never reused, so
a pointer to a freed block can never come to designate a new one. C5 records every block (its
address, its size, whether it is still allocated) in address order, and reports undefined
behaviour, besides C4's, for

* an access to a freed block (STD §7.22.3#1: the lifetime of the object has ended),
* an access that starts in a block and runs past its end, or that touches the gap before a
  block (an overrun of the block or of the object below it; in particular every access to the
  block of `malloc(0)`),
* `free` or `realloc` of a pointer that is neither `NULL` nor the address of an allocated
  block (STD §7.22.3.3#2, §7.22.3.5#3), and so a double `free`,
* through C1, a read of a byte not yet written (`malloc` and `realloc` beyond the old size
  give uninitialised bytes; C leaves them indeterminate, so C5 claims less than C there, as C1
  does for its other objects).

These accesses are checked for scalar and aggregate reads and writes, and for the memory and
string arguments of C1's library (`memcpy`, `memmove`, `memset`, `memcmp`, the bytes
`strncpy` writes, the strings of `strlen`, `strcmp`, `strcpy`, `strcat`, `strchr`,
`strrchr`, `puts`, the format of `printf`, `sprintf`, `snprintf` and the first byte they
write). A `%s` argument of `printf` and the bytes `sprintf` writes past the first are not
checked against the block bounds; a freed block is also marked uninitialised, so reading it
there is still undefined. Frames of returned activations below the last block stay
addressable: as in C1, a dangling stack pointer there is not detected (C5 is more defined
than C).

## Choices

* Every allocation succeeds, except a request of `2⁶³` bytes or more (above `PTRDIFF_MAX`),
  or a `calloc` whose product is, which returns `NULL` as glibc's does. A run whose memory
  exceeds C1's 256 MiB leaves the fragment (it is not modelled as a `NULL` result). C allows
  any allocation to fail, so these are choices among C's behaviours. ccomp's runtime libc
  returns `NULL` when its fixed heap is exhausted; its programs that use less agree with C5.
* `malloc(0)` and `calloc` with a zero product return a unique non-null pointer to a block of
  size 0 (glibc's choice; STD §7.22.3#1 allows `NULL` or such a pointer).
* `calloc` zeroes its block; `realloc(p, n)` allocates a new block, copies the first
  `min (size p) n` bytes (with their initialisation) and frees `p`; `realloc(NULL, n)` is
  `malloc(n)`; `realloc(p, 0)` frees `p` and returns `NULL` (glibc's choice; implementation
  defined in C17). Block addresses are implementation choices, observable only through
  comparisons and conversions C leaves unspecified.

## Statement: C5 extends C4 on C4's fragment

The intended ladder law is `C4.sem ⊑[C4.fragment] C5.sem`. A C4 program calls no allocation
function, so its heap stays empty: every access check passes at once, and a returning
activation restores the stack pointer exactly as C4 does (`max sp 0 = sp`). The evaluator is
otherwise C4's, step by step. The law is stated, not proved; the driver tries C1 → C2 → C3 →
C4 before C5, so C5 runs only the programs C4 rejects.
-/

namespace Silmaril.Compile.C.Sem.C5

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C Silmaril.Compile.Category
open C0 (Stop ub Kont Result)
open C1 (Memory Place FunDef wrap convTo shape store base externals plainString)
open C2 (Layout Agg Val Next aggOf lvType readAgg writeAgg depth)
open C3 (ofInt truthOf floatConst storeV layoutOf sizeAlignOf)
open C4 (Arg Cursor Prog prepare codeAddress callTypes vaCompatible writeConst usualOf isFunction
  checkFloat checkC callsE reachable)

/-- A heap block: its address, its size, and whether it is still allocated. -/
structure Block where
  addr : Nat
  size : Nat
  live : Bool := true
deriving Inhabited

/-- C4's store, plus the heap blocks. -/
structure Env extends toC4 : C4.Env where
  /-- Every block allocated so far, by increasing address. -/
  heap : Array Block := #[]
  /-- The end of the last block: the stack never shrinks below it. -/
  heapTop : Nat := 0

@[inline] def Env.withMem (env : Env) (f : Memory → Except Stop Memory) : Except Stop Env := do
  return { env with mem := ← f env.mem }

@[inline] def Env.setReg (env : Env) (x : Nat) (v : Int) : Env :=
  { env with regs := env.regs.insert x v }

def Env.newCursor (env : Env) (c : Cursor) : Except Stop (Int × Env) := do
  let (h, e) ← env.toC4.newCursor c
  return (h, { env with toC4 := e })

def Env.takeArg (env : Env) (h : Int) : Except Stop (Arg × Env) := do
  let (a, e) ← env.toC4.takeArg h
  return (a, { env with toC4 := e })

def Env.expire (env : Env) (activation : Nat) : Env :=
  { env with toC4 := env.toC4.expire activation }

/-- The bytes left unallocated before each block. -/
def gap : Nat := 16

/-- The index of the last block at or below `a`, if any (binary search). -/
def Env.blockAt (env : Env) (a : Nat) : Option Nat := Id.run do
  let h := env.heap
  let mut lo := 0
  let mut hi := h.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if h[mid]!.addr ≤ a then lo := mid + 1 else hi := mid
  return if lo = 0 then none else some (lo - 1)

/-- An access to `[a, a + n)` that touches a heap block lies inside one allocated block. -/
def Env.access (env : Env) (a n : Nat) : Except Stop Unit := do
  if env.heap.isEmpty || n = 0 || a ≥ env.heapTop then return
  let i? := env.blockAt a
  if let some i := i? then
    let b := env.heap[i]!
    if a < b.addr + max b.size 1 then
      if !b.live then ub "an access to freed memory"
      if a + n > b.addr + b.size then ub "an access past the end of a heap block"
      return
  if let some b := env.heap[(i?.map (· + 1)).getD 0]? then
    if b.addr < a + n + gap then ub "an access past the end of an object into a heap block"

/-- Allocate a block of `n` bytes after the gap (zeroed for `calloc`); `NULL` from `2⁶³` bytes
on. -/
def Env.malloc (env : Env) (n : Nat) (zero : Bool) : Except Stop (Int × Env) := do
  if n ≥ 2^63 then return (0, env)
  let (a, mem) ← env.mem.alloc (gap + n) 16
  let a := a + gap
  let mem ← if zero then mem.writeBytes a (Array.replicate n 0) else pure mem
  return (a, { env with mem, heap := env.heap.push ⟨a, n, true⟩, heapTop := mem.sp })

/-- The allocated block at `p`, by index, or undefined behaviour (`what` names the caller). -/
def Env.liveBlock (env : Env) (what : String) (p : Nat) : Except Stop (Nat × Block) := do
  let some i := env.blockAt p | ub s!"{what} of a pointer not returned by malloc"
  let b := env.heap[i]!
  if b.addr != p then ub s!"{what} of a pointer not returned by malloc"
  if !b.live then ub (if what == "free" then "a double free" else s!"{what} of a freed pointer")
  return (i, b)

/-- Free the block at `p` (`NULL`: nothing); its bytes become uninitialised. -/
def Env.free (env : Env) (p : Nat) : Except Stop Env := do
  if p = 0 then return env
  let (i, b) ← env.liveBlock "free" p
  return { env with mem := env.mem.clear p b.size, heap := env.heap.set! i { b with live := false } }

/-- `realloc(p, n)`: a new block with the old contents, then free the old one. -/
def Env.realloc (env : Env) (p n : Nat) : Except Stop (Int × Env) := do
  if p = 0 then return ← env.malloc n false
  let (_, b) ← env.liveBlock "realloc" p
  if n = 0 then return (0, ← env.free p)
  let (q, env') ← env.malloc n false
  if q = 0 then return (0, env)
  let env' ← env'.withMem (·.copy q.toNat p (min b.size n))
  return (q, ← env'.free p)

/-- The memory C1's library functions read and write lies in allocated blocks. -/
def Env.checkLib (env : Env) (name : String) (args : List Int) : Except Stop Unit := do
  if env.heap.isEmpty then return
  let str (p : Int) : Except Stop Nat := do
    let n := (← env.mem.cstr p.toNat).size + 1
    env.access p.toNat n
    return n
  match name, args with
  | "memcpy", [d, s, n] | "memmove", [d, s, n] | "memcmp", [d, s, n] => do
    env.access d.toNat n.toNat
    env.access s.toNat n.toNat
  | "memset", [d, _, n] | "strncpy", [d, _, n] => env.access d.toNat n.toNat
  | "strlen", [s] | "puts", [s] | "strchr", [s, _] | "strrchr", [s, _] | "printf", s :: _ =>
    discard <| str s
  | "strcmp", [a, b] => do discard <| str a; discard <| str b
  | "strcpy", [d, s] => do env.access d.toNat (← str s)
  | "strcat", [d, s] => do
    let l ← str d
    env.access d.toNat (l - 1 + (← str s))
  | "sprintf", d :: f :: _ | "snprintf", d :: _ :: f :: _ => do
    discard <| str f
    env.access d.toNat 1
  | _, _ => pure ()

/-- The allocation functions of the fragment, by name (C1's `externals` are the others). -/
def heapExternals : List String := ["malloc", "calloc", "realloc", "free"]

/-- Reuse C3's scalar memory and local-value operations, with the heap checks. -/
def readPlace (fd : FunDef) (env : Env) (t : CType) (pl : Place) : Except Stop Int := do
  if let .mem a := pl then env.access a ((C3.width t).getD 1)
  C3.readPlace fd env.toC1 t pl

def writePlace (env : Env) (t : CType) (v : Int) : Place → Except Stop Env
  | .reg x => .ok (env.setReg x v)
  | .mem a => do
    env.access a ((C3.width t).getD 1)
    env.withMem (storeV · t a v)

/-- The allocation functions, then C1's externals. -/
def external (name : String) (args : List Int) (env : Env) : Except Stop (Int × Env) := do
  match name, args with
  | "malloc", [n] => env.malloc n.toNat false
  | "calloc", [k, n] =>
    if k.toNat * n.toNat ≥ 2^63 then return (0, env) else env.malloc (k.toNat * n.toNat) true
  | "realloc", [p, n] => env.realloc p.toNat n.toNat
  | "free", [p] => return (0, ← env.free p.toNat)
  | _, _ =>
    env.checkLib name args
    let (v, e) ← C1.external name args env.toC1
    return (v, { env with toC1 := e })

/-! ## Evaluation -/

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
    | _ => .error (.unsupported "a function designator outside C5")

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
    | _ => .error (.unsupported "an aggregate expression outside C5")

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

/-- **The C5 interpreter.** Run `main` with `fuel`. -/
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

/-- The behaviours of a program under C5, as for C0 (`C0.beh`). -/
def beh (p : TypedProgram) : Set Obs := {o |
  (∃ n, run n p = .done o) ∨ (∃ n why, run n p = .undefined why) ∨
    (o = ⟨[], .diverges⟩ ∧ ∀ n, run n p = .outOfFuel)}

/-- C5 as a semantics of C. -/
def sem : Semantics := beh

/-- C5 as a language of the zoo. -/
def lang : Language.{0} := cSyntax.lang sem

theorem beh_of_done {p : TypedProgram} {n : Nat} {o : Obs} (h : run n p = .done o) :
    o ∈ beh p := .inl ⟨n, h⟩

/-- Undefined behaviour allows every behaviour. -/
theorem beh_of_undefined {p : TypedProgram} {n : Nat} {why : String}
    (h : run n p = .undefined why) : beh p = Set.univ :=
  Set.eq_univ_of_forall fun _ => .inr (.inl ⟨n, why, h⟩)


/-! ## The fragment -/


/-- The parameter types of an allocation function (`size_t` is `unsigned long`). -/
def heapParams : String → Option (List CType)
  | "malloc" => some [.int 8 false]
  | "calloc" => some [.int 8 false, .int 8 false]
  | "realloc" => some [.ptr (.mk [] .void), .int 8 false]
  | "free" => some [.ptr (.mk [] .void)]
  | _ => none

/-- Does a prototype match an allocation function's parameters (pointers of any type)? -/
def heapProto (want got : List CType) : Bool :=
  want.length == got.length && (want.zip got).all fun
    | (.ptr _, .ptr _) => true
    | (.int w s, .int w' s') => w == w' && s == s'
    | _ => false

/-- Calls use the static prototype; direct external calls additionally check C3's
library boundary, or that an allocation function has its prototype. Address-taking checks
also prevent indirect unsupported externals. -/
def checkCallShape (P : Prog) (f : TypedExpression) (args : List TypedExpression) :
    Except String Unit := do
  match callTypes f with
  | .error _ => throw "call of a non-function"
  | .ok _ => pure ()
  match f.node with
  | .functionDecay ⟨_, _, _, .ident g⟩ =>
    if !P.funcs.contains g.number then
      match heapParams (P.name g) with
      | some want =>
        if !heapProto want ((P.protos[g.number]?).getD []) || want.length != args.length then
          throw s!"{P.name g} without its prototype"
      | none => C3.checkCall P.toC3 f args
  | _ => pure ()

mutual
/-- Check a function designator, including the targets whose addresses escape. -/
def checkF (P : Prog) : TypedExpression → Except String Unit
  | .mk _ _ _ node => do
  match node with
  | .ident g =>
    if !P.symbols.contains g.number then throw "an undeclared function designator"
    if !P.funcs.contains g.number && !(externals.contains (P.name g)) &&
        !(heapExternals.contains (P.name g)) && (C3.F.libm (P.name g)).isNone then throw s!"address of the external function {P.name g}"
  | .unary .indirection p => checkE P p
  | .annot _ a => checkF P a
  | _ => throw "a function designator outside C5"

/-- Check that an rvalue is in the fragment. -/
def checkE (P : Prog) : TypedExpression → Except String Unit
  | .mk ann _ _ node => do
    match ann with
    | .lvalue .. => throw "an lvalue in value position"
    | .rvalue g =>
      let t := ofGenType g
      if P.aggType t then checkA P node
      else
        if !P.valueType t then throw "an expression of a type outside C5"
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
  | _ => throw "an aggregate expression outside C5"
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
    | _ => throw "a constant outside C5"
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
    | .lvalue _ ty _ => if !P.obj ty then throw "an object of a type outside C5"
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
    | _ => throw "an lvalue outside C5"
def checkL (P : Prog) : List TypedExpression → Except String Unit
  | [] => pure ()
  | e :: es => do checkE P e; checkL P es
def checkG (P : Prog) : List (GenericAssociation GenTypeCategory) → Except String Unit
  | [] => pure ()
  | .type_ _ _ e :: gs | .default e :: gs => do checkE P e; checkG P gs
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
      | _ => throw "an array initializer outside C5"
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
      if !P.valueType (ofCtype ty) then throw "an initializer of an object without values in C5"
      checkE P e

/-- The locals of a statement have types of C5. -/
def checkLocals (P : Prog) (bs : Bindings) : Except String Unit := do
  for (x, (_, _, _, ty)) in bs do
    if !P.obj ty then throw s!"local {Silmaril.Compile.Forks.Csem.C.symName x} of a type outside C5"

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

/-- Is the program in the C5 fragment? The reason when it is not. Only the functions reachable
from `main` are checked, and the initializers of the objects of static storage duration whose
type is in C5 (the others are left zero, and their uses are rejected where they occur). -/
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
          throw s!"a function with a result outside C5: {Silmaril.Compile.Forks.Csem.C.symName x}"
        if ps.any fun (_, t, _) =>
            !P.obj t || !((C3.width (ofCtype t)).isSome || P.aggType (ofCtype t)) then
          throw s!"a function with a parameter outside C5: {Silmaril.Compile.Forks.Csem.C.symName x}"
    | .object .. => pure ()
  for (_, ty, init) in P.statics do
    if P.obj ty then
      if let some e := init then checkI P depth ty e
  for f in live do
    if let some fd := P.funcs[f]? then checkS P fd fd.body

/-- The C5 fragment. -/
def InFragment (p : TypedProgram) : Prop := check p = .ok ()

instance (p : TypedProgram) : Decidable (InFragment p) :=
  inferInstanceAs (Decidable (check p = .ok ()))

/-- The fragment as a set of programs. -/
def fragment : Set TypedProgram := {p | InFragment p}

end Silmaril.Compile.C.Sem.C5
