module

public import Silmaril.Compiler.Core.Verified.LoopIteration.Defs
public import Silmaril.Compiler.Core.Verified.LoopLink.Defs
public import Silmaril.Compiler.Core.Verified.State.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # `main` with one `while` loop over `int` locals: recogniser and code

`recognize doc = some P`: `main` is a procedure without parameters, the file has no global
definitions, and `main`'s body is a block whose `int` locals are created first (as in
`State`), followed by

* straight statements `int x;`, `int x = e;`, `x = e;` (`Pre`);
* one loop, Cerberus's elaboration of `while (c) body`: a saved label `l` whose only
  parameter is a local `x` (default `x`), whose body is the test `c` (`LoopCondition`) selecting
  `body; run l(x)` (`LoopFallthrough`: assignments, `continue` saves, sequencing) or `unit`,
  then the fall-through statements after the label (the `break` save);
* `return e;`.

Each read is of a local defined before (`covered`, `Pre.after`, `stmtAfter`), and the labels of
the body have pairwise distinct keys (`labelKeys`), so a `run` finds its own save.

The code (`blocks`) is a Lir control-flow graph over registers, one per local (`regOf`): block
0 runs the straight statements, block 1 the test (Cerberus's `z ≠ 1` conversion,
`LoopBlocks.coreTest`), block 2 the body and the back edge to 1, block 3 the statements after
the loop and the return. Every value is computed at run time from the current registers
(`StateExprLir`); nothing of the program is evaluated by the compiler.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopMain

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics (EE)
open Silmaril.Machine
open StateExpr (Key Term term)
open StateStmt (assignStmt initStmt uninitStmt retStmt isLocal isFresh)
open ReturnLit (Eff)

/-! ## Labels -/

mutual
/-- The keys of the labels saved in an expression, in the order of `Dynamics.saves`. -/
def labelKeys : EE → List Key
  | .mk _ (.sseq _ a b) => labelKeys a ++ labelKeys b
  | .mk _ (.wseq _ a b) => labelKeys a ++ labelKeys b
  | .mk _ (.save (s, _) _ body) => s.key :: labelKeys body
  | .mk _ (.let_ _ _ body) => labelKeys body
  | .mk _ (.if_ _ a b) => labelKeys a ++ labelKeys b
  | .mk _ (.case_ _ bs) => labelKeysCases bs
  | .mk _ (.unseq es) => labelKeysList es
  | _ => []

def labelKeysList : List EE → List Key
  | [] => []
  | e :: es => labelKeys e ++ labelKeysList es

def labelKeysCases : List (Pattern Sym × EE) → List Key
  | [] => []
  | (_, e) :: es => labelKeys e ++ labelKeysCases es
end

/-! ## Statements -/

/-- The straight statements before the loop. -/
inductive Pre where
  | assign (x : Sym) (t : Term)
  | init (x : Sym) (t : Term)
  | uninit (x : Sym)

/-- Which straight statement `s` is. -/
def classifyPre (file : File Codec.wireModel Unit Unit) (s : Eff) : Option Pre :=
  match assignStmt file s with
  | some (x, t) => some (.assign x t)
  | none => match initStmt file s with
    | some (x, t) => some (.init x t)
    | none => (uninitStmt s).map .uninit

/-- Every local `t` reads is in `dk`. -/
def covered (dk : List Key) (t : Term) : Bool := t.vars.all fun q => dk.contains q

/-- The defined locals after a straight statement, when its local is one of `xs` and its reads
are defined. -/
def Pre.after (xs : List Sym) (dk : List Key) : Pre → Option (List Key)
  | .assign x t | .init x t =>
    if isLocal xs x = true ∧ covered dk t = true then some (x.key :: dk) else none
  | .uninit x => if isLocal xs x = true then some (dk.filter (· != x.key)) else none

/-- The defined locals after a fall-through statement, when its locals are among `xs` and its
reads are defined. -/
def stmtAfter (xs : List Sym) : List Key → LoopFallthrough.Stmt → Option (List Key)
  | dk, .skip => some dk
  | dk, .assign x t => if isLocal xs x = true ∧ covered dk t = true then some (x.key :: dk) else none
  | dk, .seq a b => (stmtAfter xs dk a).bind fun d => stmtAfter xs d b
  | dk, .save x b => if isLocal xs x = true then stmtAfter xs dk b else none

/-- `pure(unit)`. -/
def isUnit : Eff → Bool
  | .mk _ (.pure (.mk _ () (.val .unit))) => true
  | _ => false

/-- The loop statement: `save l(x := x) in (test; if then (body; run l(x)) else unit)`, then
the statements after the label. -/
def loopStmt (file : File Codec.wireModel Unit Unit) (xs : List Sym) :
    Eff → Option (Term × LoopFallthrough.Stmt × LoopFallthrough.Stmt)
  | .mk _ (.sseq (.mk _ (.base (none, _)))
      (.mk _ (.save (label, _) [(x, (_, .mk _ () (.sym x')))] cond)) brk) =>
    if x' = x ∧ isLocal xs x = true then
      match LoopCondition.recognize file xs cond with
      | some (t, .mk _ (.sseq (.mk _ (.base (none, _))) body
          (.mk _ (.run () label' [.mk _ () (.sym x'')]))), no) =>
        if label' = label ∧ x'' = x ∧ isUnit no = true then
          match LoopFallthrough.recognize file body, LoopFallthrough.recognize file brk with
          | some sb, some sk => some (t, sb, sk)
          | _, _ => none
        else none
      | _ => none
    else none
  | _ => none

/-- A recognised `main`: its locals, the straight statements, the loop's test, body and
statements after the label, and the returned expression. -/
structure Plan where
  xs : List Sym
  pre : List Pre
  test : Term
  body : LoopFallthrough.Stmt
  brk : LoopFallthrough.Stmt
  ret : Term

/-- The statements of the block with the locals `xs`, `dk` defined: straight statements, the
loop, the return. -/
def stmts (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) :
    List Key → Eff →
      Option (List Pre × Term × LoopFallthrough.Stmt × LoopFallthrough.Stmt × Term)
  | dk, .mk _ (.sseq (.mk _ (.base (none, _))) s rest) =>
    match classifyPre file s with
    | some st => match st.after xs dk with
      | some dk' => (stmts file ret xs dk' rest).map fun (ps, r) => (st :: ps, r)
      | none => none
    | none => match loopStmt file xs s, rest with
      | some (t, sb, sk), .mk _ (.sseq (.mk _ (.base (none, _))) r _) =>
        match stmtAfter xs dk sb, stmtAfter xs dk sk, retStmt file ret xs r with
        | some _, some dk', some tr =>
          if covered dk t = true ∧ covered dk' tr = true then some ([], t, sb, sk, tr) else none
        | _, _, _ => none
      | _, _ => none
  | _, _ => none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The creations of the block's locals, then the rest of the block. -/
def creates : List Sym → Eff → Option (List Sym × Eff)
  | xs, .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    if Locals.createInt cr = true ∧ isFresh xs x = true ∧ xs.length < 1024 then
      creates (xs ++ [x]) rest
    else none
  | xs, e => some (xs, e)
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The body of `main`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (body : Eff) : Option Plan :=
  match body with
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
    if r'.key = r.key ∧ (labelKeys body).Nodup then
      match creates [] a with
      | some (xs, e) =>
        if (xs.map (·.key)).Nodup then
          (stmts file ret xs [] e).map fun (ps, t, sb, sk, tr) => ⟨xs, ps, t, sb, sk, tr⟩
        else none
      | none => none
    else none
  | _ => none

/-- `main` is a block of `int` locals with one loop. -/
def recognize (doc : Codec.Document) : Option Plan := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-! ## Code -/

/-- The register of a local: its position among the locals' keys. -/
def regOf : List Key → Key → Nat
  | [], _ => 0
  | k :: ks, q => if k = q then 0 else regOf ks q + 1

/-- The register operations of a straight statement. -/
def Pre.ops (regs : Key → Mir.Reg) (d : Nat) : Pre → List (Lir.Op Mir.Reg)
  | .assign x t | .init x t => StateExprLir.assignOps regs d x.key t
  | .uninit _ => []

/-- The blocks of `__ccomp_start`: straight statements, test, body, exit. -/
def blocks (P : Plan) : List (Lir.Block Mir.Reg) :=
  let regs := regOf (P.xs.map (·.key))
  let d := P.xs.length
  [⟨(P.pre.flatMap (Pre.ops regs d)).map .op, .jump 1⟩,
   LoopBlocks.testBlock regs d (LoopBlocks.coreTest P.test) 2 3,
   LoopIteration.bodyBlock regs d P.body 1,
   ⟨(P.brk.ops regs d ++ StateExprLir.ops regs d P.ret).map .op, .ret [.reg d]⟩]

end Silmaril.Compile.Core.Verified.LoopMain
