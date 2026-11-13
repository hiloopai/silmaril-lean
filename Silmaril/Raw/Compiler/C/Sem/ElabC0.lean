module

public import Silmaril.Compiler.C.Sem.C0Mono.Defs
public import Silmaril.Compiler.C.Sem.ExactCore.Defs
@[expose] public section

/-!
# A checked structural elaboration of C0 into Core

`translate` builds Core syntax from Ail, without running the source program.
Integer locals become Core allocations, reads and writes become load/store,
and expressions and conditionals keep their structure and sequencing.
Static integers, direct defined calls, while/do loops (including break and continue),
compound updates and sizeof retain their structure. Calls to exit and abort are emitted;
singleton scheduling requests are checked, while abnormal exits still decline.
Labels and jumps are preserved; switch statements decline. Unsupported syntax is never erased.
As in C0, non-integer static objects are ignored, and unused non-integer locals
need no allocation. In particular, the unreadable `argv` parameter stays unset.

`elaborate` checks both complete executions and compares observations. The Core
check covers **all** transitions, not just a selected schedule. It rejects UB,
divergence and genuine choices, so equality follows from two singleton behaviour
sets. Fuel exhaustion declines; it never justifies a semantic conclusion.
-/

namespace Silmaril.Compile.C.Sem.ElabC0

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Core (PexprNode ExprNode Pattern BaseType)
open Silmaril.Cerberus.Core.Dynamics (PE EE Program)

abbrev Gen := StateT Nat Option

def pe (node : PexprNode Codec.wireModel Unit Sym) : PE := .mk [] () node
def ee (node : ExprNode Codec.wireModel Unit Unit Sym) : EE := .mk [] node
def lit (n : Int) : PE := pe (.val (.object (.integer n)))
def val (p : PE) : EE := ee (.pure p)
def specified (p : PE) : PE := pe (.ctor .specified [p])
def bind (x : Option Sym) (ty : BaseType) : Pattern Sym := .mk [] (.base (x, ty))
def seq (a b : EE) : EE := ee (.sseq (bind none .unit) a b)
/-- Keep the continuation's saved labels visible to Core's syntactic label collector,
even when normal execution transfers control before reaching that continuation. -/
def retainLabels (body next : EE) : EE := ee (.if_ (pe (.val .true)) body next)
def ptr (n : Nat) : Sym := ⟨⟨List.replicate 16 0⟩, n, .id "local"⟩
def sourceLabel (n : Nat) : Sym := ⟨⟨List.replicate 16 3⟩, n, .id "label"⟩
def parameter (n : Nat) : Sym := ⟨⟨List.replicate 16 2⟩, n, .id "parameter"⟩
def fresh : Gen Sym := do
  let n ← get
  set (n + 1)
  return ⟨⟨List.replicate 16 1⟩, n, .id "temporary"⟩

def intTy : CType → Option IntegerType
  | .bool => some .bool
  | .int 1 true => some (.signed .ichar)
  | .int 1 false => some (.unsigned .ichar)
  | .int 2 true => some (.signed .short)
  | .int 2 false => some (.unsigned .short)
  | .int 4 true => some (.signed .int)
  | .int 4 false => some (.unsigned .int)
  | .int 8 true => some (.signed .long)
  | .int 8 false => some (.unsigned .long)
  | _ => none

def ctype (t : CType) : Option Ctype := do
  return .mk [] (.basic (.integer (← intTy t)))

def conv (t : CType) (p : PE) : Option PE := do
  return pe (.convInt (← intTy t) p)

def truth (p : PE) : PE := pe (.not (pe (.op .eq p (lit 0))))
def boolInt (p : PE) : PE := pe (.if_ p (lit 1) (lit 0))
def action (node : Silmaril.Cerberus.Core.ActionNode Codec.wireModel Unit Sym) : EE :=
  ee (.action (.mk .pos (.mk .unknown () node)))

def load (x : Nat) (t : CType) : Gen EE := do
  let ty ← ctype t
  let v ← fresh
  let p := Pattern.mk [] (.ctor .specified [bind (some v) (.object .integer)])
  return ee (.sseq p (action (.load (pe (.val (.ctype ty))) (pe (.sym (ptr x))) .na))
    (val (pe (.sym v))))

def store (x : Nat) (t : CType) (p : PE) : Option EE := do
  let ty ← ctype t
  return action (.store false (pe (.val (.ctype ty))) (pe (.sym (ptr x)))
    (specified p) .na)

def arithmetic (op : ArithmeticOperator) (t : CType) (a b : PE) : Option PE := do
  let ity ← intTy t
  let ca ← conv t a
  let cb ← if op == .shl || op == .shr then some b else conv t b
  let basic (op : Silmaril.Cerberus.Core.IntOp) :=
    match t with
    | .int _ true => pe (.catchExceptionalCondition ity op ca cb)
    | _ => pe (.wrapI ity op ca cb)
  match op with
  | .add => return basic .add
  | .sub => return basic .sub
  | .mul => return basic .mul
  | .div => return basic .div
  | .mod => return basic .remT
  | .shl =>
    let scale := pe (.op .exp (lit 2) cb)
    return match t with
      | .int _ true => pe (.catchExceptionalCondition ity .mul ca scale)
      | _ => pe (.wrapI ity .mul ca scale)
  | .shr =>
    let scale := pe (.op .exp (lit 2) cb)
    -- Core's division truncates. Subtracting the floor remainder gives C0's
    -- arithmetic right shift also for negative operands.
    return pe (.op .div (pe (.op .sub ca (pe (.op .remF ca scale)))) scale)
  | .band | .bor | .bxor =>
    let ctor := match op with | .band => Silmaril.Cerberus.Core.Ctor.ivAnd | .bor => .ivOr | _ => .ivXor
    let ty ← ctype t
    return pe (.ctor ctor [pe (.val (.ctype ty)), ca, cb])

def relation (op : BinaryOperator) (a b : PE) : Option PE := do
  let cop ← match op with
    | .eq | .ne => some Silmaril.Cerberus.Core.BinOp.eq
    | .lt => some .lt
    | .le => some .le
    | .gt => some .gt
    | .ge => some .ge
    | _ => none
  let p := pe (.op cop a b)
  return boolInt (if op == .ne then pe (.not p) else p)

def argumentValues (P : C0.Prog) (translateE : TypedExpression → Gen EE)
    (pts : List CType) (args : List TypedExpression) (next : List PE → Gen EE) : Gen EE := do
  match args with
  | [] => next []
  | a :: rest =>
    let body ← translateE a
    let x ← fresh
    let t := pts.headD (typeOf a)
    let p ← conv t (pe (.sym x))
    let tail ← argumentValues P translateE pts.tail rest (fun ps => next (p :: ps))
    return ee (.sseq (bind (some x) (.object .integer)) body tail)

/-- Expressions return an integer object; `sseq` makes operand order explicit. -/
def expression (P : C0.Prog) : Nat → TypedExpression → Gen EE
  | 0, _ => failure
  | n + 1, e => do
    let t := typeOf e
    match e.node with
    | .const c =>
      let .ok v := C0.constVal c t | failure
      return val (lit v)
    | .rvalue a =>
      let .ok x := C0.lvalSym a | failure
      load x.number (typeOf a)
    | .cast _ _ a | .annot _ a =>
      let body ← expression P n a
      let v ← fresh
      let p0 ← conv (typeOf a) (pe (.sym v))
      let p ← conv t p0
      return ee (.sseq (bind (some v) (.object .integer)) body (val p))
    | .unary (.postfixIncr) a | .unary (.postfixDecr) a =>
      let .ok x := C0.lvalSym a | failure
      let ta := typeOf a
      let .ok u := C0.usualOf ta (.int 4 true) | failure
      let old ← fresh
      let op := match e.node with | .unary .postfixIncr _ => ArithmeticOperator.add | _ => .sub
      let p ← conv ta (← arithmetic op u (pe (.sym old)) (lit 1))
      return ee (.sseq (bind (some old) (.object .integer)) (← load x.number ta)
        (seq (← store x.number ta p) (val (pe (.sym old)))))
    | .unary op a =>
      let body ← expression P n a
      let v ← fresh
      let x := pe (.sym v)
      let p ← (match op with
        | .plus => conv t x
        | .minus => arithmetic .sub t (lit 0) x
        | .bnot => do
          let ty ← ctype t
          return pe (.ctor .ivCompl [pe (.val (.ctype ty)), (← conv t x)])
        | _ => none : Option PE)
      return ee (.sseq (bind (some v) (.object .integer)) body (val p))
    | .binary a op b =>
      let left ← expression P n a
      let right ← expression P n b
      let x ← fresh
      let y ← fresh
      let px := pe (.sym x)
      let py := pe (.sym y)
      let body ← match op with
        | .and => pure (ee (.if_ (truth px)
            (ee (.sseq (bind (some y) (.object .integer)) right (val (boolInt (truth py)))))
            (val (lit 0))))
        | .or => pure (ee (.if_ (truth px) (val (lit 1))
            (ee (.sseq (bind (some y) (.object .integer)) right (val (boolInt (truth py)))))))
        | _ => do
          let p ← match op with
            | .arithmetic aop => arithmetic aop t px py
            | .comma => conv t py
            | _ => do
              let .ok u := C0.usualOf (typeOf a) (typeOf b) | none
              relation op (← conv u px) (← conv u py)
          pure (ee (.sseq (bind (some y) (.object .integer)) right (val p)))
      return ee (.sseq (bind (some x) (.object .integer)) left body)
    | .assign lhs rhs =>
      let .ok x := C0.lvalSym lhs | failure
      let body ← expression P n rhs
      let v ← fresh
      let p ← conv (typeOf lhs) (pe (.sym v))
      return ee (.sseq (bind (some v) (.object .integer)) body
        (seq (← store x.number (typeOf lhs) p) (val p)))
    | .compoundAssign lhs op rhs =>
      let .ok x := C0.lvalSym lhs | failure
      let tl := typeOf lhs
      let .ok u := C0.usualOf tl (if op == .shl || op == .shr then .int 4 true else typeOf rhs) | failure
      let r ← fresh
      let old ← fresh
      let p ← conv tl (← arithmetic op u (pe (.sym old)) (pe (.sym r)))
      return ee (.sseq (bind (some r) (.object .integer)) (← expression P n rhs)
        (ee (.sseq (bind (some old) (.object .integer)) (← load x.number tl)
          (seq (← store x.number tl p) (val p)))))
    | .call f args =>
      let .functionDecay ⟨_, _, _, .ident g⟩ := f.node | failure
      let name := (P.names[g.number]?).getD ""
      if !(P.funcs.contains g.number) && name != "abort" && name != "exit" && name != "_Exit" then failure else pure ()
      argumentValues P (expression P n) ((P.protos[g.number]?).getD []) args fun ps => do
        let result ← fresh
        let call := if !(P.funcs.contains g.number) && (name == "exit" || name == "_Exit") then
          ee (.proc () (.impl (.builtinFunction "exit")) ps)
          else ee (.proc () (.sym g) ps)
        if (t matches .void) then
          return ee (.sseq (bind none .unit) call (val (lit 0)))
        else
          return ee (.sseq (.mk [] (.ctor .specified [bind (some result) (.object .integer)]))
            call (val (← conv t (pe (.sym result)))))
    | .sizeof _ ty | .alignof _ ty =>
      let .ok (sz, al) := Silmaril.Compile.C.sizeAlign P.tags ty | failure
      return val (lit (match e.node with | .alignof .. => al | _ => sz))
    | .sizeofExpr a =>
      match a.annotation with
      | .lvalue _ ty _ =>
        let .ok (sz, _) := Silmaril.Compile.C.sizeAlign P.tags ty | failure
        return val (lit sz)
      | .rvalue _ =>
        let .ok (sz, _) := C0.shape (typeOf a) | failure
        return val (lit sz)
    | .cond c yes no =>
      let cond ← expression P n c
      let v ← fresh
      let result ← fresh
      let convert (body : EE) : Gen EE := do
        return ee (.sseq (bind (some result) (.object .integer)) body
          (val (← conv t (pe (.sym result)))))
      let a ← match yes with
        | some e => convert (← expression P n e)
        | none => pure (val (← conv t (pe (.sym v))))
      let b ← convert (← expression P n no)
      return ee (.sseq (bind (some v) (.object .integer)) cond (ee (.if_ (truth (pe (.sym v))) a b)))
    | _ => failure

def initDecls (P : C0.Prog) (fuel : Nat) (fd : C0.FunDef)
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
      let v ← fresh
      let p ← conv t (pe (.sym v))
      return ee (.sseq (bind (some v) (.object .integer)) body
        (seq (← store x.number t p) tail))

mutual
def statement : Nat → C0.Prog → C0.FunDef → Option Sym → Option Sym → TypedStatement → EE → Gen EE
  | 0, _, _, _, _, _, _ => failure
  | n + 1, P, fd, brk, cont, s, next => do
    match s.node with
    | .skip => return next
    | .expr e =>
      return ee (.sseq (bind none (.object .integer)) (← expression P n e) next)
    | .block _ ss => statements n P fd brk cont ss next
    | .returnVoid =>
      let result := if (fd.ret matches .void) then val (pe (.val .unit)) else val (specified (lit 0))
      return retainLabels result next
    | .return_ e =>
      let body ← expression P n e
      let v ← fresh
      let p ← conv fd.ret (pe (.sym v))
      return retainLabels (ee (.sseq (bind (some v) (.object .integer)) body
        (val (specified p)))) next
    | .if_ c yes no =>
      let cond ← expression P n c
      -- A shared saved continuation avoids exponential syntax (and label collection)
      -- for a sequence of conditionals whose branches both fall through.
      let join ← fresh
      let jump := ee (.run () join [])
      let a ← statement n P fd brk cont yes jump
      let b ← statement n P fd brk cont no jump
      let v ← fresh
      return retainLabels (ee (.sseq (bind (some v) (.object .integer)) cond
        (ee (.if_ (truth (pe (.sym v))) a b))))
        (ee (.save (join, .loaded .integer) [] next))
    | .label l body _ =>
      return ee (.save (sourceLabel l.number, .loaded .integer) []
        (← statement n P fd brk cont body next))
    | .goto l => return retainLabels (ee (.run () (sourceLabel l.number) [])) next
    | .break_ => return retainLabels (ee (.run () (← brk) [])) next
    | .continue_ => return retainLabels (ee (.run () (← cont) [])) next
    | .while_ c body _ | .do_ body c _ =>
      let stop ← fresh
      let test ← fresh
      let start ← fresh
      let v ← fresh
      let jump (x : Sym) := ee (.run () x [])
      let b ← statement n P fd (some stop) (some test) body (jump test)
      let bodySave := ee (.save (start, .loaded .integer) [] b)
      let cond ← expression P n c
      let testBody := ee (.sseq (bind (some v) (.object .integer)) cond
        (ee (.if_ (truth (pe (.sym v))) bodySave (jump stop))))
      let testSave := ee (.save (test, .loaded .integer) [] testBody)
      let entry := match s.node with
        | .do_ .. => ee (.if_ (pe (.val .true)) (jump start) testSave)
        | _ => testSave
      return ee (.if_ (pe (.val .true)) entry (ee (.save (stop, .loaded .integer) [] next)))
    | .declaration ds => initDecls P n fd ds next
    | .marker _ s => statement n P fd brk cont s next
    | _ => failure

def statements : Nat → C0.Prog → C0.FunDef → Option Sym → Option Sym → List TypedStatement → EE → Gen EE
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
  let P := C0.prepare p
  let main ← p.1
  let _ ← P.funcs[main.number]?
  let live := C0.reachable P (main.number :: (P.globals.flatMap fun (_, _, i) =>
    (i.map C0.callsE).getD []))
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
        -- C0 initializes only main's first integer parameter; argv is unreadable.
        if f == main.number && (i != 0 || !(t matches .int ..)) then continue
        let value := if f == main.number then lit 1 else pe (.sym (parameter x))
        body := seq (← store x t value) body
      body ← allocate (fd.locals.toList.filter fun (_, t) => C0.intType t) body
      let params := if f == main.number then [] else
        fd.params.map fun (x, _) => (parameter x, BaseType.object .integer)
      funs := (g, Silmaril.Cerberus.Core.FunDecl.procedure .unknown none
        (if (fd.ret matches .void) then .unit else .loaded .integer) params body) :: funs
    for (g,_) in p.2.declarations do
      if (P.names[g.number]?).getD "" == "abort" && !(P.funcs.contains g.number) then
        funs := (g, .procedureDecl .unknown .unit []) :: funs
    let mut globs := []
    let mut done := []
    for (x, t, init) in P.globals do
      -- C0.initGlobals likewise skips objects outside its scalar integer model.
      if !C0.intType t then continue
      if done.contains x then continue
      done := x :: done
      let ty ← ctype t
      let value ← match init with | none => pure (val (lit 0)) | some e => expression P 512 e
      let v ← fresh
      let initBody := ee (.sseq (bind (some v) (.object .integer)) value
        (seq (← store x t (← conv t (pe (.sym v)))) (val (pe (.sym (ptr x))))))
      let body ← allocate [(x,t)] initBody
      globs := globs ++ [(ptr x, Silmaril.Cerberus.Core.Global.definition (.object .pointer,ty) body)]
    return {
      main := some main, callingConvention := .normal, tagDefs := ∅,
      stdlib := ∅, impl := ∅, globs, funs := Map.ofList funs,
      extern := ∅, funInfo := ∅, loopAttributes := ∅, visibleObjects := ∅ }
  return (← work.run 0).1

/-- Completed C0 runs have exactly their observed behaviour. -/
theorem c0_beh_eq {p : TypedProgram} {fuel : Nat} {o : Obs}
    (h : C0.run fuel p = .done o) : C0.beh p = {o} := by
  ext o'
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, why, hn⟩ | ⟨_, hn⟩)
    · have eq := C0.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
      rfl
    · have eq := C0.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
    · have eq := h.symm.trans (hn fuel)
      cases eq
  · rintro rfl
    exact C0.beh_of_done h

/-- The structural result is returned only after two exact observations agree. -/
def elaborate (p : TypedProgram) : Option Program := do
  if C0.check p != .ok () then none else do
    let q ← translate p
    let .done source := C0.run 100000 p | none
    let target ← ExactCore.exactProgram 100000 q
    if source = target then some q else none

theorem elaborate_sound {p : TypedProgram} {q : Program}
    (h : elaborate p = some q) : C0.InFragment p ∧ Compile.Core.beh q = C0.beh p := by
  unfold elaborate at h
  split at h
  · contradiction
  · rename_i hc
    have fragment : C0.InFragment p := by simpa [C0.InFragment] using hc
    cases ht : translate p with
    | none => simp [ht] at h
    | some q' =>
      simp only [ht] at h
      cases hr : C0.run 100000 p <;> simp only [hr] at h
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
            (eq ▸ (c0_beh_eq hr).symm)⟩
        · contradiction

end Silmaril.Compile.C.Sem.ElabC0
