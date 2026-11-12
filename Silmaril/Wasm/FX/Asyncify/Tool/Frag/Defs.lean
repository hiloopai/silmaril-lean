module

public import Silmaril.Wasm.FX.Asyncify.Tool.Machine.Defs
public import Silmaril.Wasm.Modules
public import Silmaril.Wasm.Binaryen.Exe.Fold

/-!
# The source fragment of the asyncify tool: statement form

A source program of the first asyncify strategy is a Core 3.0 module whose function imports are
**suspending**: a call to an import stops the machine (`Res.ask`) and the host answers later. Its
defined functions are in *statement form*: the body is a list of statements followed by a tail,

* `Stmt.pure is`: non-empty pure code (`pureIns`) that starts and ends on an empty operand stack
  (`depthAfter is 0 = some 0`);
* `Stmt.call f as rs`: `local.get a₁ … local.get aₙ; call f; local.set rₘ … local.set r₁`
  (arguments from locals, results to locals), for an import or a defined function `f`;
* the tail: pure code leaving the results (`depthAfter tail 0 = some nres`).

`FnSrc.body` is the flat Core code, so the source is executed by the machine of
`Silmaril.Wasm.FX.Asyncify.Tool.Machine` on the unchanged instructions; the statement structure only
guides the transformation. `Prog.WF` collects the conditions; `recognize` reads a
`Silmaril.Wasm.Module` (`envOf`), splits every body (`split`) and keeps the result only when the
checks pass and the flattened program is exactly the module's (`recognize_sound`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- A statement. -/
inductive Stmt where
  | pure (is : List Instr)
  | call (f : FuncIdx) (args rets : List LocalIdx)
  deriving Repr

/-- `local.get` of each argument. -/
def getsCode (as : List LocalIdx) : List Instr := as.map .localGet

/-- `local.set` of each result, the last result (top of the stack) first. -/
def setsCode (rs : List LocalIdx) : List Instr := rs.reverse.map .localSet

/-- The flat code of a statement. -/
def Stmt.code : Stmt → List Instr
  | .pure is => is
  | .call f as rs => getsCode as ++ [.call f] ++ setsCode rs

/-- The flat code of statements. -/
def flatS : List Stmt → List Instr
  | [] => []
  | s :: r => s.code ++ flatS r

/-- A source function in statement form. -/
structure FnSrc where
  nparams : Nat
  nlocals : Nat
  nres : Nat
  stmts : List Stmt
  tail : List Instr
  deriving Repr

/-- The flat body. -/
def FnSrc.body (fn : FnSrc) : List Instr := flatS fn.stmts ++ fn.tail

/-- The number of locals (parameters included). -/
def FnSrc.nloc (fn : FnSrc) : Nat := fn.nparams + fn.nlocals

/-- A source program: imports (arity, result count), then defined functions. -/
structure Prog where
  imps : List (Nat × Nat)
  fns : List FnSrc
  deriving Repr

/-- The machine program of the source. -/
def Prog.env (P : Prog) : Env :=
  ⟨P.imps, P.fns.map fun fn => ⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩⟩

/-! ## Static checks -/

/-- Pure instructions of the fragment, with local indices below `S`. -/
def pureIns (S : Nat) : Instr → Bool
  | .nop | .drop | .intConst .i32 _ | .intUnOp .i32 _ | .intBinOp .i32 _ | .intTestOp .i32 _
  | .intRelOp .i32 _ => true
  | .localGet i | .localSet i | .localTee i => decide (i.value.val < S)
  | _ => false

/-- Operands popped and pushed by a pure instruction. -/
def eff : Instr → Nat × Nat
  | .nop => (0, 0)
  | .drop => (1, 0)
  | .localGet _ => (0, 1)
  | .localSet _ => (1, 0)
  | .localTee _ => (1, 1)
  | .intConst _ _ => (0, 1)
  | .intUnOp _ _ => (1, 1)
  | .intBinOp _ _ => (2, 1)
  | .intTestOp _ _ => (1, 1)
  | .intRelOp _ _ => (2, 1)
  | _ => (0, 0)

/-- The stack depth after pure code, from depth `d`; `none` on an underflow. -/
def depthAfter : List Instr → Nat → Option Nat
  | [], d => some d
  | i :: is, d => if (eff i).1 ≤ d then depthAfter is (d - (eff i).1 + (eff i).2) else none

/-- Arity and result count of function index `f`. -/
def Prog.sig (P : Prog) (f : Nat) : Option (Nat × Nat) :=
  if h : f < P.imps.length then some P.imps[f]
  else (P.fns[f - P.imps.length]?).map fun fn => (fn.nparams, fn.nres)

/-- Checks of one statement of a function with `S` locals. -/
def Stmt.wf (P : Prog) (S : Nat) : Stmt → Bool
  | .pure is => !is.isEmpty && is.all (pureIns S) && depthAfter is 0 == some 0
  | .call f as rs =>
    P.sig f.value.val == some (as.length, rs.length) &&
      as.all (fun a => decide (a.value.val < S)) && rs.all (fun r => decide (r.value.val < S))

/-- The frame size of the asyncified program in words: the most locals of a function, plus one
for the resume index. -/
def Prog.frameWords (P : Prog) : Nat := (P.fns.map FnSrc.nloc).foldr max 0 + 1

/-- The request area in words: an import index and the arguments, or the results. -/
def Prog.reqWords (P : Prog) : Nat := (P.imps.map fun x => max (x.1 + 1) x.2).foldr max 1

/-- Checks of one function. -/
def FnSrc.wf (P : Prog) (fn : FnSrc) : Bool :=
  fn.stmts.all (Stmt.wf P fn.nloc) && fn.tail.all (pureIns fn.nloc) &&
    depthAfter fn.tail 0 == some fn.nres && decide (fn.stmts.length < 2 ^ 31)

/-- Checks of a program. The bounds keep every constant of the generated code below `2 ^ 32`. -/
def Prog.wf (P : Prog) : Bool :=
  P.fns.all (FnSrc.wf P) && decide (P.imps.length + P.fns.length < 2 ^ 31) &&
    decide (4 * P.frameWords + 4 * P.reqWords < 2 ^ 24)

/-- The well-formedness of a source program. -/
def Prog.WF (P : Prog) : Prop := P.wf = true

/-! ## Reading a Core module -/

/-- The function type at a type index, if all its parameters and results are `i32`. -/
def i32Sig (m : Module) (t : TypeIdx) : Option (Nat × Nat) :=
  match m.typeDefinitions[t.value.val]? with
  | some ⟨_, _, .func ft⟩ =>
    if ft.params.all (· == .i32) && ft.results.all (· == .i32) then
      some (ft.params.length, ft.results.length)
    else none
  | _ => none

/-- The arity and result count of a function import (`none` for other imports). -/
def impSig (m : Module) (im : Import) : Option (Nat × Nat) :=
  match im.type with
  | .func t => i32Sig m t
  | _ => none

/-- The machine function of a defined function with `i32` locals. -/
def fnDefOf (m : Module) (f : Func) : Option FnDef :=
  match i32Sig m f.type with
  | some (n, r) => if f.locals.all (· == .i32) then some ⟨n, f.locals.length, r, f.body⟩ else none
  | none => none

/-- The module has nothing but types, function imports, functions and exports. -/
def plainModule (m : Module) : Bool :=
  m.globals.isEmpty && m.memories.isEmpty && m.tables.isEmpty && m.tags.isEmpty &&
    m.data.isEmpty && m.elems.isEmpty && m.start.isNone

/-- The machine program of a module of the fragment: function imports only (all `i32`), no
globals, memories, tables, tags, segments or start function; defined functions with `i32`
locals, read with their bodies unchanged. -/
def envOf (m : Module) : Option Env :=
  if plainModule m then
    match m.imports.mapM (impSig m), m.funcs.mapM (fnDefOf m) with
    | some imps, some fns => some ⟨imps, fns⟩
    | _, _ => none
  else none

/-- Split a body into statements and a tail (`sig` gives arity and result count of a function
index). The first applicable rule is used: a call statement, else the shortest non-empty pure
prefix returning to depth 0; whatever is left is the tail. -/
def split (sig : Nat → Option (Nat × Nat)) : Nat → List Instr → List Stmt × List Instr
  | 0, is => ([], is)
  | fuel + 1, is =>
    let as := is.takeWhile (fun | .localGet _ => true | _ => false)
    let r := is.drop as.length
    let asI : List LocalIdx := as.filterMap fun | .localGet a => some a | _ => none
    let callStmt : Option (Stmt × List Instr) :=
      match r with
      | .call f :: r' =>
        match sig f.value.val with
        | some (n, k) =>
          if n = asI.length then
            let ss := r'.take k
            let rsRev : List LocalIdx := ss.filterMap fun | .localSet x => some x | _ => none
            if rsRev.length = k then some (.call f asI rsRev.reverse, r'.drop k) else none
          else none
        | none => none
      | _ => none
    match callStmt with
    | some (s, rest) =>
      let (ss, tl) := split sig fuel rest
      (s :: ss, tl)
    | none =>
      match (List.range is.length).find? (fun j => depthAfter (is.take (j + 1)) 0 == some 0 &&
          (is.take (j + 1)).all fun | .call _ => false | _ => true) with
      | some j =>
        let (ss, tl) := split sig fuel (is.drop (j + 1))
        (.pure (is.take (j + 1)) :: ss, tl)
      | none => ([], is)

/-- Executable equality of machine programs (`instrsEqb` on bodies). -/
def fnDefEqb (a b : FnDef) : Bool :=
  a.nparams == b.nparams && a.nlocals == b.nlocals && a.nres == b.nres &&
    Silmaril.Wasm.Binaryen.Exe.instrsEqb a.body b.body

/-- Executable equality of lists of machine functions. -/
def fnDefsEqb : List FnDef → List FnDef → Bool
  | [], [] => true
  | a :: as, b :: bs => fnDefEqb a b && fnDefsEqb as bs
  | _, _ => false

/-- Executable equality of machine programs. -/
def envEqb (a b : Env) : Bool := a.imps == b.imps && fnDefsEqb a.fns b.fns

/-- The source program read off a machine program by splitting every body. -/
def progOf (E : Env) : Prog :=
  let sig : Nat → Option (Nat × Nat) := fun f =>
    if h : f < E.imps.length then some E.imps[f]
    else (E.fns[f - E.imps.length]?).map fun fn => (fn.nparams, fn.nres)
  ⟨E.imps, E.fns.map fun fn =>
    let (ss, tl) := split sig (fn.body.length + 1) fn.body
    ⟨fn.nparams, fn.nlocals, fn.nres, ss, tl⟩⟩

/-- Recognise a module of the fragment in statement form. -/
def recognize (m : Module) : Except String Prog :=
  match envOf m with
  | none => .error "not in the fragment: only i32 function imports and i32 functions, no globals, memories, tables, tags, segments or start"
  | some E =>
    if envEqb (progOf E).env E then
      if (progOf E).wf then .ok (progOf E)
      else .error "not in statement form: pure statements must be balanced, calls must read their arguments from locals and write their results to locals"
    else .error "internal: the statement split does not flatten to the body"

end Silmaril.Wasm.FX.Asyncify.Tool
