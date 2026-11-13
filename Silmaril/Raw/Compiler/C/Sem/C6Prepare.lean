module

public import Silmaril.Compiler.C.Sem.C5.Defs
/-!
# Preparing C6 activations

C4's preparation extended to traverse GNU statement-expression bodies. Locals, strings and
address-taking are collected in the same visit that numbers compound-literal occurrences.
Numbers belong to the prepared function, so equal source locations do not merge objects.
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

/-! Preparation visits expression bodies as well as ordinary statement blocks. Each compound
literal receives a fresh marker, independent of source locations (which can be identical).
The marker is private to the prepared copy; the input program is never modified. -/
structure Walk where
  next : Nat := 0
  locals : List (Nat × Ctype) := []
  strings : List (List UInt8) := []
  taken : List Nat := []
  exhausted : Bool := false

def collectBindings (bs : Bindings) : StateM Walk Unit :=
  modify fun w => { w with locals := w.locals ++ bs.filterMap fun (x, ((_, dur, _), _, _, ty)) =>
    if dur == .automatic then some (x.number, ty) else none }

mutual
/-- Number literal occurrences and collect the objects nested in an expression. -/
def numberE : Nat → TypedExpression → StateM Walk TypedExpression
  | 0, e => do modify fun w => { w with exhausted := true }; return e
  | n + 1, .mk a anns loc node => do
    let node' ← numberN n node
    match node with
    | .compound .. =>
      let w ← get
      set { w with next := w.next + 1 }
      return .mk a [.marker w.next] loc node'
    | _ => return .mk a anns loc node'
def numberN : Nat → ExpressionNode GenTypeCategory → StateM Walk (ExpressionNode GenTypeCategory)
  | 0, node => do modify fun w => { w with exhausted := true }; return node
  | n + 1, node => do
    match node with
    | .unary op a =>
      if op == .address then
        if let .ident x := a.node then modify fun w => { w with taken := x.number :: w.taken }
      return .unary op (← numberE n a)
    | .binary a op b => return .binary (← numberE n a) op (← numberE n b)
    | .assign a b => return .assign (← numberE n a) (← numberE n b)
    | .compoundAssign a op b => return .compoundAssign (← numberE n a) op (← numberE n b)
    | .cond c a b => return .cond (← numberE n c) (← a.mapM (numberE n)) (← numberE n b)
    | .cast q t a => return .cast q t (← numberE n a)
    | .call f args => return .call (← numberE n f) (← args.mapM (numberE n))
    | .assert a => return .assert (← numberE n a)
    | .generic a i gs => return .generic (← numberE n a) i (← gs.mapM (numberG n))
    | .array b t es => return .array b t (← es.mapM fun e => e.mapM (numberE n))
    | .struct t ms => return .struct t (← ms.mapM fun (m, e) => do return (m, ← e.mapM (numberE n)))
    | .union t m e => return .union t m (← e.mapM (numberE n))
    | .compound q t a => return .compound q t (← numberE n a)
    | .memberof a m => return .memberof (← numberE n a) m
    | .memberofptr a m => return .memberofptr (← numberE n a) m
    | .str s =>
      modify fun w => { w with strings := (Silmaril.Compile.Forks.Csem.C.stringBytes s).toList :: w.strings }
      return node
    | .sizeofExpr a => return .sizeofExpr (← numberE n a)
    | .annot t a => return .annot t (← numberE n a)
    | .vaStart a x => return .vaStart (← numberE n a) x
    | .vaArg a t => return .vaArg (← numberE n a) t
    | .vaCopy a b => return .vaCopy (← numberE n a) (← numberE n b)
    | .vaEnd a => return .vaEnd (← numberE n a)
    | .rvalue a => return .rvalue (← numberE n a)
    | .arrayDecay a => return .arrayDecay (← numberE n a)
    | .functionDecay a => return .functionDecay (← numberE n a)
    | .gccStatement bs ss =>
      collectBindings bs
      return .gccStatement bs (← ss.mapM (numberS n))
    | _ => return node
def numberG : Nat → GenericAssociation GenTypeCategory → StateM Walk (GenericAssociation GenTypeCategory)
  | 0, g => do modify fun w => { w with exhausted := true }; return g
  | n + 1, .type_ q t a => return .type_ q t (← numberE n a)
  | n + 1, .default a => return .default (← numberE n a)
/-- Collect ordinary and statement-expression block bindings in the same activation. -/
def numberS : Nat → TypedStatement → StateM Walk TypedStatement
  | 0, s => do modify fun w => { w with exhausted := true }; return s
  | n + 1, .mk loc di attrs node => do
    return .mk loc di attrs (← numberSN n node)
def numberSN : Nat → StatementNode GenTypeCategory → StateM Walk (StatementNode GenTypeCategory)
  | 0, node => do modify fun w => { w with exhausted := true }; return node
  | n + 1, node => do
    match node with
    | .expr e => return .expr (← numberE n e)
    | .return_ e => return .return_ (← numberE n e)
    | .block bs ss =>
      collectBindings bs
      return .block bs (← ss.mapM (numberS n))
    | .if_ c a b => return .if_ (← numberE n c) (← numberS n a) (← numberS n b)
    | .while_ c b i => return .while_ (← numberE n c) (← numberS n b) i
    | .do_ b c i => return .do_ (← numberS n b) (← numberE n c) i
    | .switch c b => return .switch (← numberE n c) (← numberS n b)
    | .case_ v b => return .case_ v (← numberS n b)
    | .caseRangeGnu a z b => return .caseRangeGnu a z (← numberS n b)
    | .default b => return .default (← numberS n b)
    | .label l b a => return .label l (← numberS n b) a
    | .marker i b => return .marker i (← numberS n b)
    | .declaration ds => return .declaration (← ds.mapM fun (x, e) => do return (x, ← e.mapM (numberE n)))
    | .par ss => return .par (← ss.mapM (numberS n))
    | _ => return node
end

/-- C4's preparation, extended through all C6 expressions. The depth bound declines rather
than silently preparing an incomplete body. -/
def prepareProgram (p : TypedProgram) : Except Stop Prog := do
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
    lits := lits ++ (C4.scanE e).1
  let mut funcs : Std.HashMap Nat FunDef := {}
  for (x, fd) in σ.functionDefinitions do
    let pts := (protos[x.number]?).getD []
    let pcs := (pctys[x.number]?).getD []
    let params := fd.params.zipIdx.map fun (y, i) => (y.number, (pts[i]?).getD (.int 4 true))
    let (body, w) := (numberS 4096 fd.body).run {}
    if w.exhausted then throw (.unsupported "a C6 body nested too deeply")
    let blockLocals := w.locals
    let locals := blockLocals.foldl (fun m (n, t) => m.insert n (ofCtype t))
      (params.foldl (fun m (n, t) => m.insert n t) {})
    let (ls, taken) := (w.strings.reverse, w.taken)
    lits := lits ++ ls
    let all := fd.params.zipIdx.map (fun (y, i) => (y.number, (pcs[i]?).getD (.mk [] .void)))
      ++ blockLocals
    let memLocals := all.filter fun (n, t) =>
      taken.contains n || (C3.width (ofCtype t)).isNone
    funcs := funcs.insert x.number
      { params, ret := (rets[x.number]?).getD (.int 4 true), body := body, locals,
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


end Silmaril.Compile.C.Sem.C6
