module

public import Silmaril.Compiler.C.Sem.C2Mono.Defs
public import Silmaril.Compiler.C.Sem.ElabC0.Defs
@[expose] public section

/-!
# Checked structural C2 elaboration

Structs remain typed Core objects: allocations carry their C types and tags,
member lvalues use `memberShift`, and aggregate assignment uses typed loads and
stores. Expressions, initializers and direct calls are translated from syntax,
without source execution results. Unions decline because the frozen Core
memory conversion and member-pointer operations do not support them. Arrays,
pointer arithmetic and unsupported library calls also decline in this slice.

Acceptance requires C2 fragment membership, a completed C2 execution, and an
exact, terminating Core execution with the same observation. Thus accepted
programs have exactly the same behaviour sets; finite fuel never justifies a
claim about an unfinished execution. This is worker-written realisation, not
agreement with Cerberus elaboration.
-/

namespace Silmaril.Compile.C.Sem.ElabC2

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Core (PexprNode ExprNode Pattern BaseType ObjectType)
open Silmaril.Cerberus.Core.Dynamics (PE EE Program)
open ElabC0 (Gen pe ee lit val specified bind seq ptr sourceLabel parameter fresh
  intTy truth boolInt action arithmetic relation)

/-- Types of the represented Core objects. Unions deliberately decline. -/
def objectType : CType → Option ObjectType
  | .void => some .integer
  | .ptr _ => some .pointer
  | .agg (.mk _ (.struct tag)) => some (.struct tag)
  | t => do let _ ← intTy t; pure .integer

def ctype : CType → Option Ctype
  | .ptr t => some (.mk [] (.pointer ⟨false, false, false⟩ t))
  | .agg ty@(.mk _ (.struct _)) => some ty
  | t => ElabC0.ctype t

def conv (t : CType) (p : PE) : Option PE := do
  let _ ← objectType t
  match t with
  | .ptr _ | .agg _ => return p
  | _ => ElabC0.conv t p

def returnType : CType → Option BaseType
  | .void => some .unit
  | t => return .loaded (← objectType t)

def loadAt (address : PE) (t : CType) : Gen EE := do
  let ty ← ctype t
  let v ← ElabC0.fresh
  let pat := Pattern.mk [] (.ctor .specified [bind (some v) (.object (← objectType t))])
  return ee (.sseq pat (action (.load (pe (.val (.ctype ty))) address .na))
    (val (pe (.sym v))))

def storeAt (address : PE) (t : CType) (p : PE) : Option EE := do
  let ty ← ctype t
  return action (.store false (pe (.val (.ctype ty))) address (specified p) .na)

/-- Member addresses preserve Core's object provenance. -/
def lvalue (eval : TypedExpression → Gen EE) : Nat → TypedExpression → Gen EE
  | 0, _ => failure
  | n + 1, e => do
    match e.node with
    | .ident x => return val (pe (.sym (ptr x.number)))
    | .annot _ a => lvalue eval n a
    | .memberof a m =>
      let .mk _ (.struct tag) := C2.lvType a | failure
      let addr ← lvalue eval n a
      let x ← ElabC0.fresh
      return ee (.sseq (bind (some x) (.object .pointer)) addr
        (val (pe (.memberShift (pe (.sym x)) tag m))))
    | .unary .indirection p => eval p
    | .memberofptr p m =>
      let .ptr (.mk _ (.struct tag)) := typeOf p | failure
      let addr ← eval p
      let x ← ElabC0.fresh
      return ee (.sseq (bind (some x) (.object .pointer)) addr
        (val (pe (.memberShift (pe (.sym x)) tag m))))
    | _ => failure

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
    | .mk _ (.pointer _ refTy) => return pe (.val (.object (.pointer (.null refTy))))
    | _ => none

def argumentValues (P : C2.Prog) (translateE : TypedExpression → Gen EE)
    (pts : List CType) (args : List TypedExpression) (next : List PE → Gen EE) : Gen EE := do
  match args with
  | [] => next []
  | a :: rest =>
    let body ← translateE a
    let x ← ElabC0.fresh
    let t := pts.headD (typeOf a)
    let p ← conv t (pe (.sym x))
    let tail ← argumentValues P translateE pts.tail rest (fun ps => next (p :: ps))
    return ee (.sseq (bind (some x) (.object (← objectType (typeOf a)))) body tail)

/-- Expressions return a typed Core object; `sseq` makes operand order explicit. -/
def expression (P : C2.Prog) : Nat → TypedExpression → Gen EE
  | 0, _ => failure
  | n + 1, e => do
    let t := typeOf e
    match e.node with
    | .const c =>
      let .ok v := C0.constVal c t | failure
      return val (lit v)
    | .rvalue a =>
      let addr ← lvalue (expression P n) n a
      let x ← ElabC0.fresh
      return ee (.sseq (bind (some x) (.object .pointer)) addr
        (← loadAt (pe (.sym x)) (typeOf a)))
    | .annot _ a => expression P n a
    | .cast _ _ a =>
      let body ← expression P n a
      let v ← ElabC0.fresh
      let p0 ← conv (typeOf a) (pe (.sym v))
      let p ← conv t p0
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf a)))) body (val p))
    | .unary (.postfixIncr) a | .unary (.postfixDecr) a =>
      let .ok x := C0.lvalSym a | failure
      let ta := typeOf a
      let .ok u := C0.usualOf ta (.int 4 true) | failure
      let old ← ElabC0.fresh
      let op := match e.node with | .unary .postfixIncr _ => ArithmeticOperator.add | _ => .sub
      let p ← conv ta (← arithmetic op u (pe (.sym old)) (lit 1))
      return ee (.sseq (bind (some old) (.object .integer)) (← loadAt (pe (.sym (ptr x.number))) ta)
        (seq (← storeAt (pe (.sym (ptr x.number))) ta p) (val (pe (.sym old)))))
    | .unary .address a => lvalue (expression P n) n a
    | .unary op a =>
      let body ← expression P n a
      let v ← ElabC0.fresh
      let x := pe (.sym v)
      let p ← (match op with
        | .plus => conv t x
        | .minus => arithmetic .sub t (lit 0) x
        | .bnot => do
          let ty ← ctype t
          return pe (.ctor .ivCompl [pe (.val (.ctype ty)), (← conv t x)])
        | _ => none : Option PE)
      return ee (.sseq (bind (some v) (.object .integer)) body (val p))
    | .binary a .comma b =>
      let a' ← expression P n a
      let b' ← expression P n b
      return ee (.sseq (bind none (.object (← objectType (typeOf a)))) a' b')
    | .binary a op b =>
      let left ← expression P n a
      let right ← expression P n b
      let x ← ElabC0.fresh
      let y ← ElabC0.fresh
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
      let body ← expression P n rhs
      let addr ← lvalue (expression P n) n lhs
      let v ← ElabC0.fresh
      let a ← ElabC0.fresh
      let p ← conv (typeOf lhs) (pe (.sym v))
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf rhs)))) body
        (ee (.sseq (bind (some a) (.object .pointer)) addr
          (seq (← storeAt (pe (.sym a)) (typeOf lhs) p) (val p)))))
    | .compoundAssign lhs op rhs =>
      let .ok x := C0.lvalSym lhs | failure
      let tl := typeOf lhs
      let .ok u := C0.usualOf tl (if op == .shl || op == .shr then .int 4 true else typeOf rhs) | failure
      let r ← ElabC0.fresh
      let old ← ElabC0.fresh
      let p ← conv tl (← arithmetic op u (pe (.sym old)) (pe (.sym r)))
      return ee (.sseq (bind (some r) (.object .integer)) (← expression P n rhs)
        (ee (.sseq (bind (some old) (.object .integer)) (← loadAt (pe (.sym (ptr x.number))) tl)
          (seq (← storeAt (pe (.sym (ptr x.number))) tl p) (val p)))))
    | .call f args =>
      let .functionDecay ⟨_, _, _, .ident g⟩ := f.node | failure
      let name := (P.names[g.number]?).getD ""
      if !(P.funcs.contains g.number) && name != "abort" && name != "exit" && name != "_Exit" then failure else pure ()
      argumentValues P (expression P n) ((P.protos[g.number]?).getD []) args fun ps => do
        let result ← ElabC0.fresh
        let call := if !(P.funcs.contains g.number) && (name == "exit" || name == "_Exit") then
          ee (.proc () (.impl (.builtinFunction "exit")) ps)
          else ee (.proc () (.sym g) ps)
        if (t matches .void) then
          return ee (.sseq (bind none .unit) call (val (lit 0)))
        else
          return ee (.sseq (.mk [] (.ctor .specified [bind (some result) (.object (← objectType t))]))
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
      let v ← ElabC0.fresh
      let result ← ElabC0.fresh
      let convert (body : EE) : Gen EE := do
        return ee (.sseq (bind (some result) (.object (← objectType t))) body
          (val (← conv t (pe (.sym result)))))
      let a ← match yes with
        | some e => convert (← expression P n e)
        | none => pure (val (← conv t (pe (.sym v))))
      let b ← convert (← expression P n no)
      return ee (.sseq (bind (some v) (.object .integer)) cond (ee (.if_ (truth (pe (.sym v))) a b)))
    | .struct tag fields =>
      let some (_, .struct members none) := P.tags.lookup tag | failure
      let rec gather (ms : List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)))
          (values : List (Identifier × PE)) : Gen EE := do
        match ms with
        | [] => return val (pe (.struct tag values))
        | (name, (_, _, _, ty)) :: rest =>
          let value ← match fields.find? (fun x => x.1.name == name.name) with
            | some (_, some e) => expression P n e
            | _ => pure (val (← zeroValue n ty P.tags))
          let x ← ElabC0.fresh
          let tail ← gather rest (values ++ [(name, pe (.sym x))])
          return ee (.sseq (bind (some x) (.object (← objectType (ofCtype ty)))) value tail)
      gather members []
    | _ => failure

def initDecls (P : C2.Prog) (fuel : Nat) (fd : C1.FunDef)
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
      let p ← conv t (pe (.sym v))
      return ee (.sseq (bind (some v) (.object (← objectType (typeOf e)))) body
        (seq (← storeAt (pe (.sym (ptr x.number))) t p) tail))

mutual
def statement : Nat → C2.Prog → C1.FunDef → Option Sym → Option Sym → TypedStatement → EE → Gen EE
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
        (val (specified (← conv fd.ret (pe (.sym v))))))
    | .if_ c yes no =>
      let cond ← expression P n c
      let a ← statement n P fd brk cont yes next
      let b ← statement n P fd brk cont no next
      let v ← ElabC0.fresh
      return ee (.sseq (bind (some v) (.object .integer)) cond
        (ee (.if_ (truth (pe (.sym v))) a b)))
    | .label l body _ =>
      return ee (.save (sourceLabel l.number, .loaded .integer) []
        (← statement n P fd brk cont body next))
    | .goto l => return ee (.run () (sourceLabel l.number) [])
    | .break_ => return ee (.run () (← brk) [])
    | .continue_ => return ee (.run () (← cont) [])
    | .while_ c body _ | .do_ body c _ =>
      let stop ← ElabC0.fresh
      let test ← ElabC0.fresh
      let start ← ElabC0.fresh
      let v ← ElabC0.fresh
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

def statements : Nat → C2.Prog → C1.FunDef → Option Sym → Option Sym → List TypedStatement → EE → Gen EE
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
  let P := C2.prepare p
  let main ← p.1
  let _ ← P.funcs[main.number]?
  let live := C2.reachable P (main.number :: (P.statics.flatMap fun (_, _, i) =>
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
      let value ← match init with | none => pure (val (← zeroValue 64 ty P.tags)) | some e => expression P 512 e
      let v ← ElabC0.fresh
      let initBody := ee (.sseq (bind (some v) (.object (← objectType t))) value
        (seq (← storeAt (pe (.sym (ptr x))) t (← conv t (pe (.sym v)))) (val (pe (.sym (ptr x))))))
      let body ← allocate [(x,t)] initBody
      globs := globs ++ [(ptr x, Silmaril.Cerberus.Core.Global.definition (.object .pointer,ty) body)]
    return {
      main := some main, callingConvention := .normal, tagDefs := P.tags.definitions,
      stdlib := ∅, impl := ∅, globs, funs := Map.ofList funs,
      extern := ∅, funInfo := ∅, loopAttributes := ∅, visibleObjects := ∅ }
  return (← work.run 0).1

/-- Completed C2 runs have exactly their observed behaviour. -/
theorem c2_beh_eq {p : TypedProgram} {fuel : Nat} {o : Obs}
    (h : C2.run fuel p = .done o) : C2.beh p = {o} := by
  ext o'
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, why, hn⟩ | ⟨_, hn⟩)
    · have eq := C2.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
      rfl
    · have eq := C2.run_agree hn h (by intro h; cases h) (by intro h; cases h)
      cases eq
    · have eq := h.symm.trans (hn fuel)
      cases eq
  · rintro rfl
    exact C2.beh_of_done h

/-- The structural result is returned only after two exact observations agree. -/
def elaborate (p : TypedProgram) : Option Program := do
  if C2.check p != .ok () then none else do
    let q ← translate p
    let .done source := C2.run 100000 p | none
    let target ← ExactCore.exactProgram 100000 q
    if source = target then some q else none

theorem elaborate_sound {p : TypedProgram} {q : Program}
    (h : elaborate p = some q) : C2.InFragment p ∧ Compile.Core.beh q = C2.beh p := by
  unfold elaborate at h
  split at h
  · contradiction
  · rename_i hc
    have fragment : C2.InFragment p := by simpa [C2.InFragment] using hc
    cases ht : translate p with
    | none => simp [ht] at h
    | some q' =>
      simp only [ht] at h
      cases hr : C2.run 100000 p <;> simp only [hr] at h
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
            (eq ▸ (c2_beh_eq hr).symm)⟩
        · contradiction

end Silmaril.Compile.C.Sem.ElabC2
